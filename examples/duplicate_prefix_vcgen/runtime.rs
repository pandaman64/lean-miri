#![no_std]
#![no_main]

extern crate core as std;
mod duplicate_prefix;

use duplicate_prefix::duplicate_prefix;

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut bytes = [1, 2, 3, 4, 5, 6, 7, 8];
    if !duplicate_prefix(&mut bytes, 0) { return 101; }
    if !matches!(bytes, [1, 2, 3, 4, 5, 6, 7, 8]) { return 102; }
    if !duplicate_prefix(&mut bytes, 2) { return 103; }
    if !matches!(bytes, [1, 2, 1, 2, 5, 6, 7, 8]) { return 104; }
    if !duplicate_prefix(&mut bytes, 4) { return 105; }
    if !matches!(bytes, [1, 2, 1, 2, 1, 2, 1, 2]) { return 106; }
    if duplicate_prefix(&mut bytes, 5) { return 107; }
    if !matches!(bytes, [1, 2, 1, 2, 1, 2, 1, 2]) { return 108; }
    if duplicate_prefix(&mut bytes, usize::MAX) { return 109; }
    if !matches!(bytes, [1, 2, 1, 2, 1, 2, 1, 2]) { return 110; }
    let mut empty = [];
    if !duplicate_prefix(&mut empty, 0) { return 111; }
    if duplicate_prefix(&mut empty, 1) { return 112; }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
