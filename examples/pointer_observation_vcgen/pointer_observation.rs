#![no_std]

pub unsafe fn shared_read(source: *const u8) -> u8 {
    let reference = unsafe { &*source };
    *reference
}

pub unsafe fn mutable_write(source: *mut u8) {
    let reference = unsafe { &mut *source };
    *reference = 73;
}

pub unsafe fn raw_write(source: *mut u8) {
    let pointer = &raw mut *source;
    unsafe { *pointer = 73 };
}
