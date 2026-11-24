#[inline(never)]
fn increment(x: u8) -> u8 {
    x.wrapping_add(1)
}

pub fn count_up(mut x: u8, stop: u8, run: bool) -> u8 {
    if run {
        while x < stop {
            x = increment(x);
        }
    }
    x
}
