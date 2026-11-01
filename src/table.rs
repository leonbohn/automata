//! Minimal plain-text tables for `Debug` and `Display` output.

/// Renders `rows` as a table with left-aligned, space-padded columns separated by ` | `.
/// The first row is separated from the others by a line of dashes.
pub(crate) fn render(rows: &[Vec<String>]) -> String {
    let columns = rows.iter().map(Vec::len).max().unwrap_or(0);
    let widths: Vec<usize> = (0..columns)
        .map(|c| {
            rows.iter()
                .filter_map(|row| row.get(c))
                .map(|cell| cell.chars().count())
                .max()
                .unwrap_or(0)
        })
        .collect();
    let line = |row: &Vec<String>| {
        let cells: Vec<String> = widths
            .iter()
            .enumerate()
            .map(|(c, w)| {
                let cell = row.get(c).map_or("", String::as_str);
                format!("{cell}{}", " ".repeat(w - cell.chars().count()))
            })
            .collect();
        cells.join(" | ").trim_end().to_string()
    };
    let mut out = Vec::with_capacity(rows.len() + 1);
    for (i, row) in rows.iter().enumerate() {
        out.push(line(row));
        if i == 0 {
            out.push(
                widths
                    .iter()
                    .map(|w| "-".repeat(*w))
                    .collect::<Vec<_>>()
                    .join("-+-"),
            );
        }
    }
    out.join("\n")
}

#[cfg(test)]
mod tests {
    use super::render;

    #[test]
    fn columns_are_padded() {
        let rows = vec![
            vec!["State".to_string(), "a".to_string()],
            vec!["0".to_string(), "10".to_string()],
        ];
        assert_eq!(render(&rows), "State | a\n------+---\n0     | 10");
    }
}
