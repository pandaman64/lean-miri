#![no_std]
#![no_main]

#[path = "empty_function.rs"]
mod fixture;

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    fixture::empty_function();
    0
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
