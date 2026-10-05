pub fn preview(source: &str, start: u32, end: u32, cap: usize) -> String {
    let start = start as usize;
    let end = (end as usize).min(source.len());
    let raw = source.get(start..end).unwrap_or_default();
    let mut out = String::with_capacity(cap.min(raw.len()));
    for c in raw.chars() {
        if out.len() >= cap {
            break;
        }
        out.push(if c.is_whitespace() { ' ' } else { c });
    }
    out
}
