#![no_std]
#![no_main]
#[path = "control.rs"]
mod control;

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if control::count_up(1, 3, true) == 3 && control::count_up(1, 3, false) == 1 { 0 } else { 101 }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
