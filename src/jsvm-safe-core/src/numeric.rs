/// ECMAScript strict numeric equality without approximate float comparisons.
///
/// Equal finite or infinite IEEE-754 encodings compare equal, either signed
/// zero compares equal to the other, and NaN never compares equal (even when
/// its payload bits happen to match). This is *not* SameValue/Object.is.
#[must_use = "Use the comparison result with ECMAScript number equality semantics"]
pub const fn js_number_equal(left: f64, right: f64) -> bool {
    const ABS_MASK: u64 = 0x7fff_ffff_ffff_ffff;
    if left.is_nan() || right.is_nan() {
        return false;
    }
    let left_bits = left.to_bits();
    let right_bits = right.to_bits();
    left_bits == right_bits || ((left_bits & ABS_MASK) == 0 && (right_bits & ABS_MASK) == 0)
}

/// The engine-independent cases of ECMAScript `Number::exponentiate`.
///
/// ECMA-262 6.1.6.1.3 specifies exact exceptional results but leaves
/// ordinary finite nonzero powers implementation-approximated. An exact
/// mathematical answer, even when representable, is not a proof that every
/// JavaScript implementation returns that particular IEEE-754 encoding.
///
/// Return `None` rather than importing the host libm approximation into a
/// portable JavaScript rewrite.
#[must_use = "Use the result only when exponentiation has engine-independent semantics"]
pub fn js_number_exponentiate(base: f64, exponent: f64) -> Option<f64> {
    if exponent.is_nan() {
        return Some(f64::NAN);
    }
    if exponent == 0.0 {
        return Some(1.0);
    }
    if base.is_nan() {
        return Some(f64::NAN);
    }
    if base == 0.0 || base.is_infinite() {
        let odd = js_number_equal(exponent % 2.0, 1.0) || js_number_equal(exponent % 2.0, -1.0);
        let magnitude = if base.is_infinite() == (exponent > 0.0) {
            f64::INFINITY
        } else {
            0.0
        };
        return Some(if base.is_sign_negative() && odd {
            -magnitude
        } else {
            magnitude
        });
    }
    if exponent.is_infinite() {
        if js_number_equal(base.abs(), 1.0) {
            return Some(f64::NAN);
        }
        return Some(if (base.abs() > 1.0) == exponent.is_sign_positive() {
            f64::INFINITY
        } else {
            0.0
        });
    }
    if base < 0.0 && exponent.fract() != 0.0 {
        return Some(f64::NAN);
    }
    None
}

#[must_use = "Use the integer only when conversion is exact"]
pub fn exact_u64(value: f64) -> Option<u64> {
    if !value.is_finite() || value < 0.0 {
        return None;
    }
    if value == 0.0 {
        return Some(0);
    }

    let bits = value.to_bits();
    let exponent_bits = u16::try_from((bits >> 52) & 0x07ff).ok()?;
    let exponent = i32::from(exponent_bits) - 1023;
    if !(0..=63).contains(&exponent) {
        return None;
    }

    let significand = (bits & ((1_u64 << 52) - 1)) | (1_u64 << 52);
    if exponent >= 52 {
        significand.checked_shl(u32::try_from(exponent - 52).ok()?)
    } else {
        let shift = u32::try_from(52 - exponent).ok()?;
        let fractional_mask = (1_u64 << shift) - 1;
        (significand & fractional_mask == 0).then_some(significand >> shift)
    }
}

#[must_use = "Use the integer only when conversion is exact"]
pub fn exact_i64(value: f64) -> Option<i64> {
    if value == 0.0 {
        return Some(0);
    }
    let negative = value.is_sign_negative();
    let magnitude = exact_u64(value.abs())?;
    if negative {
        if magnitude == 1_u64 << 63 {
            Some(i64::MIN)
        } else {
            i64::try_from(magnitude).ok()?.checked_neg()
        }
    } else {
        i64::try_from(magnitude).ok()
    }
}

#[must_use = "Use the integer only when conversion is exact"]
pub fn exact_u32(value: f64) -> Option<u32> {
    u32::try_from(exact_u64(value)?).ok()
}

#[must_use = "Use the integer only when conversion is exact"]
pub fn exact_usize(value: f64) -> Option<usize> {
    usize::try_from(exact_u64(value)?).ok()
}

#[cfg(test)]
mod tests {
    use super::{
        exact_i64, exact_u32, exact_u64, exact_usize, js_number_equal, js_number_exponentiate,
    };

    #[test]
    fn js_number_equality_preserves_signed_zero_and_nan_rules() {
        assert!(js_number_equal(-0.0, 0.0));
        assert!(js_number_equal(f64::INFINITY, f64::INFINITY));
        assert!(!js_number_equal(f64::INFINITY, f64::NEG_INFINITY));
        assert!(!js_number_equal(f64::NAN, f64::NAN));
        assert!(!js_number_equal(
            f64::from_bits(0x7ff8_0000_0000_0001),
            f64::from_bits(0x7ff8_0000_0000_0001)
        ));
        assert!(js_number_equal(42.0, 42.0));
        assert!(!js_number_equal(42.0, 42.000_000_000_000_01));
    }

    #[test]
    fn exponentiation_preserves_ecmascript_exceptional_values() {
        let cases = [
            (1.0, f64::NAN, f64::NAN),
            (-1.0, f64::INFINITY, f64::NAN),
            (1.0, f64::NEG_INFINITY, f64::NAN),
            (0.0, f64::NAN, f64::NAN),
            (f64::NAN, -0.0, 1.0),
            (f64::NAN, 2.0, f64::NAN),
            (-0.0, 3.0, -0.0),
            (-0.0, -3.0, f64::NEG_INFINITY),
            (-0.0, 2.0, 0.0),
            (-0.0, -2.0, f64::INFINITY),
            (-0.0, f64::NEG_INFINITY, f64::INFINITY),
            (0.0, -0.5, f64::INFINITY),
            (f64::NEG_INFINITY, 3.0, f64::NEG_INFINITY),
            (f64::NEG_INFINITY, -3.0, -0.0),
            (f64::NEG_INFINITY, 2.0, f64::INFINITY),
            (f64::NEG_INFINITY, -2.0, 0.0),
            (f64::NEG_INFINITY, f64::INFINITY, f64::INFINITY),
            (f64::INFINITY, -0.5, 0.0),
            (-0.0, 9_007_199_254_740_991.0, -0.0),
            (-0.0, 9_007_199_254_740_992.0, 0.0),
            (2.0, f64::INFINITY, f64::INFINITY),
            (2.0, f64::NEG_INFINITY, 0.0),
            (0.5, f64::INFINITY, 0.0),
            (0.5, f64::NEG_INFINITY, f64::INFINITY),
            (-2.0, 0.5, f64::NAN),
        ];
        for (base, exponent, expected) in cases {
            assert!(
                js_number_exponentiate(base, exponent).is_some_and(|actual| {
                    if expected.is_nan() {
                        actual.is_nan()
                    } else {
                        actual.to_bits() == expected.to_bits()
                    }
                }),
                "{base:?} ** {exponent:?} must yield {expected:?}"
            );
        }
    }

    #[test]
    fn exponentiation_does_not_guess_implementation_approximated_values() {
        for (base, exponent) in [(2.0, 1.5), (-2.0, 3.0), (1.0, 2.0), (2.0, 1.0), (0.5, -2.0)] {
            assert!(js_number_exponentiate(base, exponent).is_none());
        }
    }

    #[test]
    fn exact_unsigned_conversions_reject_fractional_and_out_of_range_values() {
        assert_eq!(exact_u64(42.0), Some(42));
        assert_eq!(exact_u64(42.5), None);
        assert_eq!(exact_u64(-1.0), None);
        assert_eq!(exact_u64(18_446_744_073_709_551_616.0), None);
        assert_eq!(exact_u32(4_294_967_295.0), Some(u32::MAX));
        assert_eq!(exact_u32(4_294_967_296.0), None);
        assert_eq!(exact_usize(7.0), Some(7));
    }

    #[test]
    fn exact_signed_conversion_handles_i64_min_without_saturation() {
        assert_eq!(exact_i64(-9_223_372_036_854_775_808.0), Some(i64::MIN));
        assert_eq!(exact_i64(9_223_372_036_854_775_808.0), None);
        assert_eq!(exact_i64(-42.0), Some(-42));
        assert_eq!(exact_i64(-42.5), None);
        assert_eq!(exact_i64(f64::NAN), None);
    }
}
