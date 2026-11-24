#[inline(never)]
fn adjust(n: u32, odd: bool) -> u32 {
    if odd { n ^ 7 } else { n ^ 2 }
}

#[unsafe(no_mangle)]
pub extern "C" fn vc_audit(mut remaining: u32, mut value: u32, mode: u32) -> u32 {
    if mode == 7 {
        loop {}
    }
    while remaining > 0 {
        value = adjust(value, remaining & 1 == 1);
        remaining -= 1;
    }
    if mode == 9 {
        unsafe { *(0 as *const u32) }
    } else {
        value
    }
}
