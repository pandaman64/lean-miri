#![no_std]
#![no_main]

#[path = "runtime-loop.rs"]
mod novel;

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    if cfg!(negative) {
        return novel::vc_audit(3, 15, 9) as isize;
    }
    if novel::vc_audit(0, 15, 0) != 15 { return 101; }
    if novel::vc_audit(3, 15, 0) != 13 { return 102; }
    if novel::vc_audit(4, 15, 0) != 15 { return 103; }
    0
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
