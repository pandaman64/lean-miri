#![no_std]
#![no_main]
extern crate core as std;
mod duplicate_prefix;

#[inline(never)]
fn outer(shared: &[u8], raw: *mut [u8], count: usize) -> bool {
    // This unsafe caller bypasses the borrow checker and creates a competing
    // mutable slice while the function argument still protects the shared one.
    let mutable = unsafe { &mut *raw };
    let succeeded = duplicate_prefix::duplicate_prefix(mutable, count);
    succeeded && shared.len() == 2
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut bytes = [1u8, 2];
    let raw: *mut [u8] = &raw mut bytes;
    let shared = unsafe { &*raw };
    if outer(shared, raw, if cfg!(positive) { 1 } else { 0 }) { 0 } else { 1 }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
