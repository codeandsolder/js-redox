pub use jsvm_safe_core::{exact_i64, exact_u64};

/// JavaScript ToInt32 for values that are already proven exact signed integers.
#[must_use]
pub const fn js_int32_from_i64(value: i64) -> i32 {
    let bytes = value.to_le_bytes();
    i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

/// JavaScript ToUint32 for values that are already proven exact signed integers.
#[must_use]
pub const fn js_uint32_from_i64(value: i64) -> u32 {
    let bytes = value.to_le_bytes();
    u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])
}

/// Evaluate the JavaScript bitwise operators for exact integer inputs.
///
/// JavaScript first coerces both operands to 32 bits and masks shift counts to
/// five bits. Unsigned right shift returns the resulting Uint32 value as a
/// non-negative integer.
#[must_use]
pub fn eval_js_bitwise_i64(op: &str, lhs: i64, rhs: i64) -> Option<i64> {
    let shift = js_uint32_from_i64(rhs) & 31;
    match op {
        "&" => Some(i64::from(js_int32_from_i64(lhs) & js_int32_from_i64(rhs))),
        "|" => Some(i64::from(js_int32_from_i64(lhs) | js_int32_from_i64(rhs))),
        "^" => Some(i64::from(js_int32_from_i64(lhs) ^ js_int32_from_i64(rhs))),
        "<<" => Some(i64::from(js_int32_from_i64(lhs).wrapping_shl(shift))),
        ">>" => Some(i64::from(js_int32_from_i64(lhs) >> shift)),
        ">>>" => Some(i64::from(js_uint32_from_i64(lhs) >> shift)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::{eval_js_bitwise_i64, js_int32_from_i64, js_uint32_from_i64};

    #[test]
    fn integer_to_int32_matches_javascript_modulo_semantics() {
        assert_eq!(js_int32_from_i64(0x8000_0000), i32::MIN);
        assert_eq!(js_int32_from_i64(0xffff_ffff), -1);
        assert_eq!(js_uint32_from_i64(-1), u32::MAX);
    }

    #[test]
    fn bitwise_operators_match_javascript_32_bit_semantics() {
        assert_eq!(eval_js_bitwise_i64(">>>", -1, 0), Some(4_294_967_295));
        assert_eq!(
            eval_js_bitwise_i64(">>", 0x8000_0000, 0),
            Some(-2_147_483_648)
        );
        assert_eq!(eval_js_bitwise_i64("<<", 1, 33), Some(2));
        assert_eq!(
            eval_js_bitwise_i64("&", 0xffff_ffff, 0x8000_0000),
            Some(-2_147_483_648)
        );
    }
}
