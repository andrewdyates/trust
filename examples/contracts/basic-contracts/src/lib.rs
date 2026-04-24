#![allow(dead_code)]

/// Tier 2 public contract corpus: a crate-first example using `trust-spec`.

#[trust::requires(denominator != 0)]
#[trust::ensures(result * denominator == numerator)]
pub fn divide_exact(numerator: i32, denominator: i32) -> i32 {
    numerator / denominator
}

#[trust::ensures(result >= 0)]
pub fn abs_total(x: i32) -> i32 {
    if x == i32::MIN {
        i32::MAX
    } else if x < 0 {
        -x
    } else {
        x
    }
}

#[trust::requires(index < values.len())]
#[trust::ensures(result == values[index])]
pub fn get_at(values: &[i32], index: usize) -> i32 {
    values[index]
}

pub fn running_total(values: &[u32]) -> u64 {
    let mut total = 0_u64;
    for value in values {
        total += u64::from(*value);
    }
    total
}

pub fn midpoint_checked(low: usize, high: usize) -> Option<usize> {
    if low > high {
        return None;
    }
    Some(low + (high - low) / 2)
}
