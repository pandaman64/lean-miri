#![no_std]
#![no_main]
#![feature(core_intrinsics)]
#![allow(internal_features)]

#[inline(never)]
pub unsafe fn copy_then_load(source: *const u8, destination: *mut u8, observe: *const u8) -> u8 {
    unsafe {
        core::intrinsics::copy_nonoverlapping(source, destination, 1);
        *observe
    }
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let mut bytes = [73u8, 13];
    let raw = (&raw mut bytes).cast::<u8>();
    unsafe {
        let destination = raw.add(1);
        let observe = if cfg!(rejected) {
            // The parent write invalidates this unprotected child.
            let child = &mut *destination;
            child as *mut u8 as *const u8
        } else {
            destination as *const u8
        };
        if copy_then_load(raw, destination, observe) == 73 {
            0
        } else {
            1
        }
    }
}

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
