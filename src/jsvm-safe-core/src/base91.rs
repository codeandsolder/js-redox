use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) struct Base91Alphabet {
    indices: HashMap<char, u16>,
}

impl Base91Alphabet {
    pub(crate) fn parse(alphabet: &str) -> Option<Self> {
        let mut indices = HashMap::with_capacity(91);
        for (index, character) in alphabet.chars().enumerate() {
            let index = u16::try_from(index).ok()?;
            if indices.insert(character, index).is_some() {
                return None;
            }
        }
        (indices.len() == 91).then_some(Self { indices })
    }

    pub(crate) fn decode_ascii(&self, encoded: &str) -> Option<String> {
        let mut accumulator = 0u32;
        let mut bits = 0u32;
        let mut pending = None;
        let mut decoded = Vec::with_capacity(encoded.len());

        for character in encoded.chars() {
            let Some(index) = self.indices.get(&character).copied() else {
                continue;
            };
            let index = u32::from(index);
            let Some(first) = pending.take() else {
                pending = Some(index);
                continue;
            };

            let value = first.checked_add(index.checked_mul(91)?)?;
            accumulator |= value.checked_shl(bits)?;
            bits += if value & 8191 > 88 { 13 } else { 14 };
            while bits > 7 {
                let byte = u8::try_from(accumulator & 0xff).ok()?;
                if !byte.is_ascii() {
                    return None;
                }
                decoded.push(byte);
                accumulator >>= 8;
                bits -= 8;
            }
        }

        if let Some(value) = pending {
            let byte = u8::try_from((accumulator | value.checked_shl(bits)?) & 0xff).ok()?;
            if !byte.is_ascii() {
                return None;
            }
            decoded.push(byte);
        }

        String::from_utf8(decoded).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::Base91Alphabet;

    #[test]
    fn decodes_generated_base91_vector() {
        let alphabet = ")uADqi*XyhHO5~&+N1KIzoP!:c@dLatEvJw.`/R9Wp|^Q;(Bl7FYVbkmTC_MS{3#j?20G,s%ng\"}r8ZUx6[>4=<]fe$";
        let parsed = Base91Alphabet::parse(alphabet);
        assert!(parsed.is_some());
        let parsed = parsed.unwrap_or_else(|| unreachable!());
        assert_eq!(
            parsed.decode_ascii(r#"y.;E1,Dc~ML1GM194&BLD":y!z"8,SJ`v5yt:MJ,q"#),
            Some("yLfabsdPOLOuoNeDEix1sRwfmgdDVETTL".to_string())
        );
    }

    #[test]
    fn rejects_invalid_alphabets_and_skips_unknown_characters() {
        assert!(Base91Alphabet::parse("short").is_none());
        let duplicated = "a".repeat(91);
        assert!(Base91Alphabet::parse(&duplicated).is_none());

        let alphabet: String = (33u8..=123).map(char::from).collect();
        let parsed = Base91Alphabet::parse(&alphabet);
        assert!(parsed.is_some());
        let parsed = parsed.unwrap_or_else(|| unreachable!());
        assert_eq!(parsed.decode_ascii("!!"), parsed.decode_ascii("!\n!"));
    }
}
