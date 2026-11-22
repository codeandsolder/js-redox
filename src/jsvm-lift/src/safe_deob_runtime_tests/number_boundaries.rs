//! IEEE-754 boundary and deterministic primitive numerical observations.

use super::{compare_sources, PRIMITIVE_RESULTS};
use anyhow::Result;
use std::{collections::BTreeSet, fmt::Write as _};

const BOUNDARY_BITS: [u64; 26] = [
    0,
    1,
    2,
    3,
    0x000f_ffff_ffff_fffe,
    0x000f_ffff_ffff_ffff,
    0x0010_0000_0000_0000,
    0x0010_0000_0000_0001,
    0x3ca0_0000_0000_0000,
    0x3cb0_0000_0000_0000,
    0x3fdf_ffff_ffff_ffff,
    0x3fe0_0000_0000_0000,
    0x3fef_ffff_ffff_ffff,
    0x3ff0_0000_0000_0000,
    0x3ff0_0000_0000_0001,
    0x3fff_ffff_ffff_ffff,
    0x4000_0000_0000_0000,
    0x4000_0000_0000_0001,
    0x4330_0000_0000_0000,
    0x433f_ffff_ffff_ffff,
    0x4340_0000_0000_0000,
    0x4340_0000_0000_0001,
    0x7fef_ffff_ffff_fffe,
    0x7fef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0x7ff8_0000_0000_0000,
];

struct Seed(u64);

impl Seed {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
}

fn number_source(bits: u64) -> String {
    let value = f64::from_bits(bits);
    if value.is_nan() {
        "(0/0)".into()
    } else if value.is_infinite() {
        if value.is_sign_negative() {
            "(-1/0)".into()
        } else {
            "(1/0)".into()
        }
    } else if value == 0.0 {
        if value.is_sign_negative() {
            "-0".into()
        } else {
            "0".into()
        }
    } else {
        // Use independent Rust decimal formatting for round-trip input
        // generation, not the ECMAScript formatter being exercised.
        format!("{value:e}")
    }
}

fn numbers(seed: &mut Seed) -> Vec<String> {
    let mut values = Vec::new();
    for bits in BOUNDARY_BITS {
        for sign in [0, 1 << 63] {
            let source = number_source(bits | sign);
            if !values.contains(&source) {
                values.push(source);
            }
        }
    }
    values.extend((0..64).map(|_| number_source(seed.next())));
    assert_eq!(values.len(), 115);
    values
}

fn primitive_batch(expressions: impl IntoIterator<Item = String>) -> Result<String> {
    let mut source = String::from("const cases = [\n");
    for expression in expressions {
        writeln!(source, "()=>({expression}),")?;
    }
    source.push_str("];\n");
    source.push_str(PRIMITIVE_RESULTS);
    Ok(source)
}

fn arithmetic_sources(values: &[String], seed: &mut Seed) -> Result<Vec<String>> {
    let operators = [
        "+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>", ">>>", "===", "!==", "==", "!=", "<",
        "<=", ">", ">=",
    ];
    let count = values.len();
    let modulo = u64::try_from(count)?;
    let mut sources = Vec::with_capacity(operators.len());
    for operator in operators {
        let mut expressions = Vec::with_capacity(count * 8);
        for (index, left) in values.iter().enumerate() {
            let sampled = usize::try_from(seed.next() % modulo)?;
            for right in [
                left.as_str(),
                &values[(index + 1) % count],
                &values[(index + count - 1) % count],
                &values[sampled],
                "1",
                "-1",
                "0",
                "-0",
            ] {
                expressions.push(format!("({left}){operator}({right})"));
            }
        }
        assert_eq!(expressions.len(), 920);
        sources.push(primitive_batch(expressions)?);
    }
    Ok(sources)
}

// Construct 2^power + k*2^(power-53) + delta, with |delta| <= 1.
// Work in exact binary strings so the test is independent of floating-point
// evaluation and covers radix conversion well beyond the integer type widths.
fn boundary_integer(power: usize, midpoint: u64, offset: i8) -> String {
    let shift = power - 53;
    let coefficient = (1_u64 << 53) + midpoint;
    if shift == 0 {
        return match offset {
            -1 => format!("{:b}", coefficient - 1),
            1 => format!("{:b}", coefficient + 1),
            _ => format!("{coefficient:b}"),
        };
    }
    match offset {
        -1 => format!("{:b}{}", coefficient - 1, "1".repeat(shift)),
        1 => format!("{coefficient:b}{}1", "0".repeat(shift - 1)),
        _ => format!("{coefficient:b}{}", "0".repeat(shift)),
    }
}

fn radix_digits(binary: &str, group: usize) -> String {
    let mut result = String::new();
    let padding = (group - binary.len() % group) % group;
    let mut digit = 0_usize;
    let mut width = padding;
    for byte in binary.bytes() {
        digit = (digit << 1) | usize::from(byte == b'1');
        width += 1;
        if width == group {
            result.push(char::from(b"0123456789abcdef"[digit]));
            digit = 0;
            width = 0;
        }
    }
    result
}

fn coercion_inputs(values: &[String]) -> BTreeSet<String> {
    let mut inputs = [
        "",
        " ",
        "\t\n\r\u{2028}\u{2029}\u{feff}",
        "-0",
        "+0",
        "-0e999",
        "+Infinity",
        "-Infinity",
        "Infinity",
        "infinity",
        "INF",
        "nan",
        "NaN",
        "-NaN",
        "0x+1",
        "0x-1",
        "+0x1",
        "0b2",
        "0o8",
        "0x",
        "0b",
        "0o",
        "1_0",
        "1\u{0085}",
        "1\u{200b}",
        "1\u{180e}",
        "\u{00a0}-0\u{feff}",
        "1.",
        "+.5",
        "-.5",
        "1e",
        "1e+2",
        "4.9406564584124654e-324",
        "2.4703282292062327e-324",
        "2.4703282292062328e-324",
        "2.2250738585072011e-308",
        "2.2250738585072012e-308",
        "2.2250738585072014e-308",
        "1.7976931348623157e308",
        "1.7976931348623158e308",
        "1.7976931348623159e308",
        "1e1000000",
        "-1e-1000000",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect::<BTreeSet<_>>();
    inputs.extend(values.iter().cloned());
    for power in [
        53, 54, 55, 63, 64, 65, 100, 127, 128, 255, 511, 1022, 1023, 1024, 1100,
    ] {
        for (midpoint, offset) in [(0, 0), (1, -1), (1, 0), (1, 1), (3, -1), (3, 0), (3, 1)] {
            let binary = boundary_integer(power, midpoint, offset);
            for (prefix, group) in [("0b", 1), ("0o", 3), ("0x", 4), ("0X", 4)] {
                let digits = radix_digits(&binary, group);
                inputs.insert(format!("{prefix}{digits}"));
                inputs.insert(format!("{prefix}00000{digits}"));
                inputs.insert(format!("{prefix}{digits}g"));
            }
        }
    }
    inputs
}

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_number_boundary_matrix() -> Result<()> {
    let mut seed = Seed(0x864a_5fa1_ce95_27ef);
    let values = numbers(&mut seed);
    let mut sources = arithmetic_sources(&values, &mut seed)?;
    sources.push(primitive_batch(values.iter().flat_map(|value| {
        [
            format!("''+({value})"),
            format!("`${{({value})}}`"),
            format!("+( ' '+({value}))"),
        ]
    }))?);
    // Smaller batches retain useful diagnostics for the particularly long
    // binary/octal/hexadecimal inputs at and above the overflow boundary.
    let inputs = coercion_inputs(&values);
    assert!(inputs.len() > 1300);
    let mut expressions = Vec::with_capacity(inputs.len() * 4);
    for input in inputs {
        let text = serde_json::to_string(&input)?;
        expressions.extend([
            format!("+({text})"),
            format!("-({text})"),
            format!("~({text})"),
            format!("({text})-0"),
        ]);
    }
    for batch in expressions.chunks(512) {
        sources.push(primitive_batch(batch.iter().cloned())?);
    }
    compare_sources("number-boundary-matrix", sources)
}
