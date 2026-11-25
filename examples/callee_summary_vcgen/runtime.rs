#![no_std]
#![no_main]

#[inline(never)]
fn update(slot: &mut u8) -> u8 {
    *slot = 42;
    7
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut slot = 1;
    let returned = update(&mut slot);
    if returned != 7 { return 1; }
    if slot != 42 { return 2; }
    slot = 99;
    if slot != 99 { return 3; }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { loop {} }
