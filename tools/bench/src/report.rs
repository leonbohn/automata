//! The Markdown comment posted on pull requests.

use crate::compare::{self, Row};
use crate::github::MARKER;
use crate::model::EnvInfo;

fn short(sha: &str) -> &str {
    &sha[..sha.len().min(8)]
}

pub fn comment(
    rows: &[Row],
    head: &str,
    base: &str,
    env: &EnvInfo,
    threshold: f64,
    dashboard: &str,
) -> String {
    let mut out = format!(
        "{MARKER}\n## Benchmarks\n\n`{}` against merge base `{}`: **{}**.\n\n",
        short(head),
        short(base),
        compare::summary(rows)
    );
    let interesting: Vec<Row> = rows
        .iter()
        .filter(|r| !matches!(r.verdict, compare::Verdict::Unchanged))
        .cloned()
        .collect();
    if !interesting.is_empty() {
        out += &compare::table(&interesting);
        out.push('\n');
    }
    out += &format!(
        "<details><summary>All {} benchmarks</summary>\n\n{}\n</details>\n\n",
        rows.len(),
        compare::table(rows)
    );
    out += &format!(
        "<sub>Instruction counts under valgrind on {} ({}), {}, one execution per revision. \
         A change counts if it is above {threshold} %. Wall-clock times are on the \
         [dashboard]({dashboard}).</sub>\n",
        env.host, env.cpu, env.rustc
    );
    out
}

pub fn failure(head: &str, error: &str, dashboard: &str) -> String {
    format!(
        "{MARKER}\n## Benchmarks\n\nThe run for `{}` failed. [Details]({dashboard})\n\n```\n{}\n```\n",
        short(head),
        error.chars().take(3000).collect::<String>()
    )
}
