//! Charts as inline SVG, generated on the server so that the page needs no scripts for them.
//!
//! Every chart has one point per commit of `main`, oldest on the left, and a tooltip with the
//! commit and the value. Points link to the run they come from.

use crate::db::Point;
use crate::model::fmt_short;
use std::collections::BTreeMap;
use std::fmt::Write;

const W: f64 = 300.0;
const H: f64 = 100.0;
const PAD: f64 = 4.0;

pub fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

pub fn day(t: i64) -> String {
    // seconds since the epoch to `YYYY-MM-DD`, without a date library
    let days = t.div_euclid(86_400) + 719_468;
    let era = days.div_euclid(146_097);
    let doe = days.rem_euclid(146_097);
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}-{m:02}-{d:02}")
}

/// A line chart of one benchmark. Points whose value differs from the previous commit by more
/// than `threshold` percent are marked.
pub fn line(points: &[Point], threshold: f64) -> String {
    if points.is_empty() {
        return String::new();
    }
    let n = points.len().saturating_sub(1).max(1) as f64;
    let (lo, hi) = points.iter().fold((u64::MAX, 0), |(lo, hi), p| {
        (lo.min(p.value), hi.max(p.value))
    });
    // Counts are exact, so noise does not exist, but a tiny step should not look like a cliff
    // either: the axis shows at least +-2 % around the middle (twice the usual threshold), a
    // change below the threshold stays flat and one above it is visible. Series that vary a lot
    // start at zero.
    let (lo, hi) = if (hi - lo) as f64 > hi as f64 * 0.2 {
        (0.0, hi as f64)
    } else {
        let middle = (lo + hi) as f64 / 2.0;
        let half = ((hi - lo) as f64 / 2.0 * 1.2).max(middle * 0.02).max(1.0);
        (middle - half, middle + half)
    };
    let span = (hi - lo).max(1.0);
    let x = |i: usize| PAD + i as f64 / n * (W - 2.0 * PAD);
    let y = |v: u64| H - PAD - (v as f64 - lo) / span * (H - 2.0 * PAD);
    let mut path = String::new();
    for (i, p) in points.iter().enumerate() {
        let _ = write!(
            path,
            "{}{:.1},{:.1}",
            if i == 0 { "M" } else { "L" },
            x(i),
            y(p.value)
        );
    }
    let mut dots = String::new();
    for (i, p) in points.iter().enumerate() {
        let change = i
            .checked_sub(1)
            .map(|j| crate::compare::relative_change(points[j].value, p.value));
        let class = match change {
            Some(c) if c > threshold => "bad",
            Some(c) if c < -threshold => "good",
            _ => "",
        };
        let delta = change
            .filter(|c| c.is_finite() && *c != 0.0)
            .map(|c| format!(" ({c:+.2} %)"))
            .unwrap_or_default();
        let _ = write!(
            dots,
            r#"<a href="/run/{}"><circle class="{class}" cx="{:.1}" cy="{:.1}" r="3"><title>{} · {} · {}{}</title></circle></a>"#,
            p.run,
            x(i),
            y(p.value),
            esc(&p.sha[..p.sha.len().min(8)]),
            day(p.time),
            fmt_short(p.value),
            delta,
        );
    }
    format!(
        r#"<svg viewBox="0 0 {W} {H}" preserveAspectRatio="none"><path class="line" d="{path}"/>{dots}</svg>"#
    )
}

/// The color of the `k`-th band of a stacked chart, also used by its legend.
pub fn hue(k: usize) -> usize {
    (k * 47) % 360
}

/// One stacked band: a name and its value at every commit.
pub struct Band {
    pub name: String,
    pub values: Vec<u64>,
}

/// A stacked area chart: at each commit the bands are piled up, so the outline is the total.
/// `commits` gives the run and the label for each x position.
pub fn stacked(commits: &[Point], bands: &[Band]) -> String {
    if commits.is_empty() || bands.is_empty() {
        return String::new();
    }
    let (w, h, pad) = (900.0, 260.0, 6.0);
    let n = commits.len().saturating_sub(1).max(1) as f64;
    let totals: Vec<u64> = (0..commits.len())
        .map(|i| bands.iter().map(|b| b.values[i]).sum())
        .collect();
    let max = totals.iter().copied().max().unwrap_or(1).max(1) as f64;
    let x = |i: usize| pad + i as f64 / n * (w - 2.0 * pad);
    let y = |v: f64| h - pad - v / max * (h - 2.0 * pad);

    let mut out =
        format!(r#"<svg class="stacked" viewBox="0 0 {w} {h}" preserveAspectRatio="none">"#);
    let mut below = vec![0.0f64; commits.len()];
    for (k, band) in bands.iter().enumerate() {
        let above: Vec<f64> = below
            .iter()
            .zip(&band.values)
            .map(|(b, v)| b + *v as f64)
            .collect();
        let mut d = String::new();
        for (i, v) in above.iter().enumerate() {
            let _ = write!(
                d,
                "{}{:.1},{:.1}",
                if i == 0 { "M" } else { "L" },
                x(i),
                y(*v)
            );
        }
        for (i, v) in below.iter().enumerate().rev() {
            let _ = write!(d, "L{:.1},{:.1}", x(i), y(*v));
        }
        let hue = hue(k);
        let _ = write!(
            out,
            r#"<path d="{d}Z" fill="hsl({hue} 55% 55%)" stroke="hsl({hue} 55% 35%)" stroke-width=".5"><title>{}</title></path>"#,
            esc(&band.name)
        );
        below = above;
    }
    for (i, p) in commits.iter().enumerate() {
        let _ = write!(
            out,
            r#"<a href="/run/{}"><circle cx="{:.1}" cy="{:.1}" r="3"><title>{} · {} · total {}</title></circle></a>"#,
            p.run,
            x(i),
            y(totals[i] as f64),
            esc(&p.sha[..p.sha.len().min(8)]),
            day(p.time),
            fmt_short(totals[i]),
        );
    }
    out.push_str("</svg>");
    out
}

/// Aligns the histories of benchmarks to the list of all commits. A benchmark that did not exist
/// at a commit contributes nothing there.
pub fn align(
    commits: &[Point],
    benches: &BTreeMap<String, Vec<Point>>,
    name_of: impl Fn(&str) -> String,
) -> Vec<Band> {
    let mut grouped: BTreeMap<String, Vec<u64>> = BTreeMap::new();
    for (bench, points) in benches {
        let values = grouped
            .entry(name_of(bench))
            .or_insert_with(|| vec![0; commits.len()]);
        for p in points {
            if let Some(i) = commits.iter().position(|c| c.run == p.run) {
                values[i] += p.value;
            }
        }
    }
    grouped
        .into_iter()
        .map(|(name, values)| Band { name, values })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(run: i64, value: u64) -> Point {
        Point {
            run,
            sha: format!("{run:040}"),
            time: 1_700_000_000,
            value,
        }
    }

    #[test]
    fn formats_dates() {
        assert_eq!(day(0), "1970-01-01");
        assert_eq!(day(1_700_000_000), "2023-11-14");
    }

    #[test]
    fn marks_changes_above_the_threshold() {
        let svg = line(&[p(1, 1000), p(2, 1000), p(3, 1100), p(4, 900)], 1.0);
        assert!(svg.contains(r#"class="bad""#));
        assert!(svg.contains(r#"class="good""#));
        assert_eq!(svg.matches("<circle").count(), 4);
        assert!(line(&[], 1.0).is_empty());
    }

    #[test]
    fn single_point_does_not_divide_by_zero() {
        assert!(line(&[p(1, 5)], 1.0).contains("<circle"));
    }

    #[test]
    fn stacks_bands_per_group() {
        let commits = [p(1, 0), p(2, 0)];
        let benches = BTreeMap::from([
            ("a::x::1".to_string(), vec![p(1, 10), p(2, 20)]),
            ("a::x::2".to_string(), vec![p(2, 5)]),
            ("b::y::1".to_string(), vec![p(1, 1), p(2, 1)]),
        ]);
        let bands = align(&commits, &benches, |b| {
            b.split("::").next().unwrap().to_string()
        });
        assert_eq!(bands.len(), 2);
        assert_eq!(bands[0].values, vec![10, 25]);
        let svg = stacked(&commits, &bands);
        assert_eq!(svg.matches("<path").count(), 2);
    }
}
