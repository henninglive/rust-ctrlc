// Copyright (c) 2015 CtrlC developers
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>,
// at your option. All files in the project carrying such
// notice may not be copied, modified, or distributed except
// according to those terms.

#![warn(missing_docs)]

//! A simple easy to use wrapper around Ctrl-C.
//! # Example
//! ```rust,no_run
//! extern crate ctrlc;
//! use std::sync::atomic::{AtomicBool, Ordering};
//! use std::sync::Arc;
//!
//! fn main() {
//!     let running = Arc::new(AtomicBool::new(true));
//!     let r = running.clone();
//!     ctrlc::set_handler(move || {
//!         r.store(false, Ordering::SeqCst);
//!     }).expect("Error setting Ctrl-C handler");
//!     println!("Waiting for Ctrl-C...");
//!     while running.load(Ordering::SeqCst) {}
//!     println!("Got it! Exiting...");
//! }
//! ```

use std::sync::atomic::{AtomicBool, Ordering, ATOMIC_BOOL_INIT};
use std::time::Duration;
use std::fmt;

static INIT: AtomicBool = ATOMIC_BOOL_INIT;

/// Ctrl-C error.
#[derive(Debug)]
pub enum Error {
    /// Ctrl-C signal handler already registered.
    MultipleHandlers,
    /// Wait timed out.
    Timeout,
    /// Unexpected system error.
    System(std::io::Error),
}

/// Ctrl-C guard
pub struct Guard(std::marker::PhantomData<*const usize>);

unsafe impl Send for Guard {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use std::error::Error;
        write!(f, "Ctrl-C error: {}", self.description())
    }
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        match *self {
            Error::MultipleHandlers => "Ctrl-C signal handler already registered",
            Error::Timeout => "Wait timed out",
            Error::System(_) => "Unexpected system error",
        }
    }

    fn cause(&self) -> Option<&std::error::Error> {
        match *self {
            Error::System(ref e) => Some(e),
            _ => None,
        }
    }
}

#[cfg(unix)]
mod platform {
    extern crate nix;

    use super::Error;
    use self::nix::unistd;
    use self::nix::sys::signal;
    use std::os::unix::io::RawFd;
    use std::io;

    static mut PIPE: (RawFd, RawFd) = (-1, -1);

    extern fn os_handler(_: nix::c_int) {
        // Assuming this always succeeds. Can't really handle errors in any meaningful way.
        unsafe {
            unistd::write(PIPE.1, &[0u8]).is_ok();
        }
    }

    /// Register os signal handler.
    ///
    /// Must be called before calling [`block_ctrl_c()`](fn.block_ctrl_c.html)
    /// and should only be called once.
    ///
    /// # Errors
    /// Will return an error if a recoverable system error occur. An error should leave
    /// the system in a constant state, where trying again might succeed.
    ///
    /// # Panics
    /// Will panic if a non recoverable system error occur.
    ///
    #[inline]
    pub unsafe fn register() -> Result<(), Error> {
        // Should only fail if invalid parameters, FD limit or out of memory.
        PIPE = unistd::pipe2(nix::fcntl::O_CLOEXEC).map_err(|e| Error::System(e.into()))?;

        let handler = signal::SigHandler::Handler(os_handler);
        let new_action = signal::SigAction::new(handler,
            signal::SA_RESTART,
            signal::SigSet::empty()
        );

        // Should only fail if invalid parameters,
        signal::sigaction(signal::Signal::SIGINT, &new_action).unwrap();

        #[cfg(feature = "termination")]
        signal::sigaction(signal::Signal::SIGTERM, &new_action).unwrap();

        // TODO: Maybe throw an error if old action is not SigDfl.
        // Inspecting a SigAction is currently not possible with nix.

        Ok(())
    }

    pub unsafe fn unregister() -> Result<(), Error> {
        Ok(())
    }

    /// Blocks until a Ctrl-C signal is received.
    ///
    /// Must be called after calling [`init_os_handler()`](fn.init_os_handler.html).
    ///
    /// # Errors
    /// Will return an error if a system error occurs.
    ///
    #[inline]
    pub unsafe fn block() -> Result<(), Error> {
        let mut buf = [0u8];

        loop {
            // TODO: Can we safely convert the pipe fd into a std::io::Read reader
            // with std::os::unix::io::FromRawFd, this would handle EINTR
            // and everything for us.
            match unistd::read(PIPE.0, &mut buf[..]) {
                Ok(1) => break,
                Ok(_) => return Err(Error::System(io::ErrorKind::UnexpectedEof.into()).into()),
                Err(nix::Error::Sys(nix::Errno::EINTR)) => {},
                Err(e) => return Err(Error::System(e.into())),
            }
        }

        Ok(())
    }
}

#[cfg(windows)]
mod platform {
    extern crate winapi;
    extern crate kernel32;

    use super::Error;
    use self::winapi::{HANDLE, BOOL, DWORD, TRUE, FALSE, c_long};
    use std::ptr;
    use std::io;
    use std::time::Duration;

    const MAX_SEM_COUNT: c_long = 255;
    static mut SEMAPHORE: HANDLE = 0 as HANDLE;

    unsafe extern "system" fn os_handler(_: DWORD) -> BOOL {
        // Assuming this always succeeds. Can't really handle errors in any meaningful way.
        self::kernel32::ReleaseSemaphore(SEMAPHORE, 1, ptr::null_mut());
        TRUE
    }

    /// Register os signal handler.
    ///
    /// Must be called before calling [`block_ctrl_c()`](fn.block_ctrl_c.html)
    /// and should only be called once.
    ///
    /// # Errors
    /// Will return an error if a recoverable system error occur. An error should leave
    /// the system in a constant state, where trying again might succeed.
    ///
    /// # Panics
    /// Will panic if a non recoverable system error occur.
    ///
    #[inline]
    pub unsafe fn register() -> Result<(), Error> {
        SEMAPHORE = self::kernel32::CreateSemaphoreA(ptr::null_mut(), 0, MAX_SEM_COUNT, ptr::null());
        if SEMAPHORE.is_null() {
            return Err(Error::System(io::Error::last_os_error()));
        }

        if self::kernel32::SetConsoleCtrlHandler(Some(os_handler), TRUE) == FALSE {
            let e = io::Error::last_os_error();
            self::kernel32::CloseHandle(SEMAPHORE);
            SEMAPHORE = 0 as HANDLE;
            return Err(Error::System(e));
        }

        Ok(())
    }

    pub unsafe fn unregister() -> Result<(), Error> {
        if self::kernel32::SetConsoleCtrlHandler(Some(os_handler), FALSE) == FALSE {
            Err(Error::System(io::Error::last_os_error()))
        } else {
            // There might be race here.
            self::kernel32::CloseHandle(SEMAPHORE);
            SEMAPHORE = 0 as HANDLE;
            Ok(())
        }
    }

    /// Blocks until a Ctrl-C signal is received.
    ///
    /// Must be called after calling [`init_os_handler()`](fn.init_os_handler.html).
    ///
    /// # Errors
    /// Will return an error if a system error occurs.
    ///
    #[inline]
    pub unsafe fn block(timeout: Option<Duration>) -> Result<(), Error> {
        use self::winapi::{INFINITE, WAIT_OBJECT_0, WAIT_FAILED, WAIT_TIMEOUT};

        let time = if let Some(dur) = timeout {
            let ms_sec = dur.as_secs().overflowing_mul(1000).0;
            let ms_nano = dur.subsec_nanos() / 1000;
            (ms_sec as DWORD) + (ms_nano as DWORD)
        } else {
            INFINITE
        };

        match self::kernel32::WaitForSingleObject(SEMAPHORE, time) {
            WAIT_OBJECT_0 => Ok(()),
            WAIT_FAILED => Err(Error::System(io::Error::last_os_error())),
            WAIT_TIMEOUT => Err(Error::Timeout),
            ret => Err(Error::System(io::Error::new(
                io::ErrorKind::Other,
                format!("WaitForSingleObject(), unexpected return value \"{:x}\"", ret),
            ))),
        }
    }
}

impl Guard {
    /// Register new Ctrl-C guard
    pub fn register() -> Result<Guard, Error> {
        if INIT.compare_and_swap(false, true, Ordering::SeqCst) {
            return Err(Error::MultipleHandlers);
        }

        unsafe {
            match platform::register() {
                Ok(_) => Ok(Guard(std::marker::PhantomData)),
                Err(e) => {
                    INIT.store(false, Ordering::SeqCst);
                    Err(e)
                },
            }
        }
    }

    /// Blocks until a Ctrl-C signal is received.
    pub fn block(&mut self) -> Result<(), Error> {
        unsafe {
            platform::block(None)
        }
    }

    /// Blocks until a Ctrl-C signal is received or timeout.
    pub fn block_timeout(&mut self, timeout: Duration) -> Result<(), Error> {
        unsafe {
            platform::block(Some(timeout))
        }
    }

    /// Unregister Ctrl-C guard
    pub fn unregister(self) -> Result<(), Error> {
        assert!(INIT.load(Ordering::SeqCst));
        unsafe {
            let res = platform::unregister();
            INIT.store(false, Ordering::SeqCst);
            res
        }
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        if INIT.load(Ordering::SeqCst) {
            unsafe {
                platform::unregister().is_ok();
                INIT.store(false, Ordering::SeqCst);
            }
        }
    }
}

/// Sets up the signal handler for Ctrl-C.
///
/// # Example
/// ```rust,no_run
/// ctrlc::set_handler(|| println!("Hello world!")).expect("Error setting Ctrl-C handler");
/// ```
///
/// # Warning
/// On Unix, any existing SIGINT, SIGTERM(if termination feature is enabled) or SA_SIGINFO posix
/// signal handlers will be overwritten. On Windows, multiple CTRL+C handlers are allowed, but only
/// the first one will be executed.
///
/// # Errors
/// Will return an error if another `ctrlc::set_handler()` handler exists or if a recoverable
/// system error occur while setting the handler. An error should leave the system in a
/// constant state, where trying again might succeed.
///
/// # Panics
/// Will panic if a non recoverable system error occur while setting the handler.
/// The handler runs on its own thread, any panics in handler or other system errors
/// on this thread will not be caught, leading to thread being brought down.
///
pub fn set_handler<F>(user_handler: F) -> Result<(), Error>
    where F: Fn() -> () + 'static + Send
{
    let mut guard = Guard::register()?;
    std::thread::spawn(move || {
        loop {
            guard.block().expect("Critical system error while waiting for Ctrl-C");
            user_handler();
        }
    });

    Ok(())
}
