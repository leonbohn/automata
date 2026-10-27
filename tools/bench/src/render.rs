//! Renders the static dashboard: a single HTML file with the data embedded.

use crate::db::Db;
use anyhow::Result;
use std::path::Path;

const TEMPLATE: &str = include_str!("dashboard.html");

pub fn render(db: &Db, out_dir: &Path, repo: &str, threshold: f64) -> Result<()> {
    let data = db.dashboard(threshold, 200)?;
    let mut json = serde_json::to_value(&data)?;
    json["repo"] = repo.into();
    // keeps the JSON from closing the script element
    let json = serde_json::to_string(&json)?.replace("</", "<\\/");
    std::fs::create_dir_all(out_dir)?;
    let tmp = out_dir.join(".index.html.tmp");
    std::fs::write(&tmp, TEMPLATE.replacen("/*DATA*/null", &json, 1))?;
    std::fs::rename(tmp, out_dir.join("index.html"))?;
    std::fs::write(
        out_dir.join("data.json"),
        serde_json::to_string_pretty(&data)?,
    )?;
    Ok(())
}
