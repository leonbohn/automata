//! The little bit of the GitHub REST API the service needs: a status and one comment per PR.

use anyhow::{Context, Result};
use serde_json::{Value, json};

pub const MARKER: &str = "<!-- automata-bench -->";

pub struct Github {
    token: String,
    repo: String,
}

impl Github {
    pub fn new(token: String, repo: String) -> Self {
        Self { token, repo }
    }

    fn request(&self, method: &str, path: &str) -> ureq::Request {
        ureq::request(
            method,
            &format!("https://api.github.com/repos/{}/{path}", self.repo),
        )
        .set("Authorization", &format!("Bearer {}", self.token))
        .set("Accept", "application/vnd.github+json")
        .set("X-GitHub-Api-Version", "2022-11-28")
        .set("User-Agent", "automata-bench")
    }

    pub fn set_status(&self, sha: &str, state: &str, description: &str, url: &str) -> Result<()> {
        let description: String = description.chars().take(140).collect();
        self.request("POST", &format!("statuses/{sha}"))
            .send_json(json!({
                "state": state,
                "context": "benchmarks",
                "description": description,
                "target_url": url,
            }))
            .context("setting commit status")?;
        Ok(())
    }

    /// Creates the benchmark comment on the pull request, or edits it if it already exists.
    pub fn upsert_comment(&self, pr: u64, body: &str) -> Result<()> {
        let comments: Vec<Value> = self
            .request("GET", &format!("issues/{pr}/comments?per_page=100"))
            .call()
            .context("listing comments")?
            .into_json()?;
        let existing = comments
            .iter()
            .find(|c| c["body"].as_str().is_some_and(|b| b.contains(MARKER)))
            .and_then(|c| c["id"].as_u64());
        let body = json!({ "body": body });
        match existing {
            Some(id) => self
                .request("PATCH", &format!("issues/comments/{id}"))
                .send_json(body),
            None => self
                .request("POST", &format!("issues/{pr}/comments"))
                .send_json(body),
        }
        .context("writing comment")?;
        Ok(())
    }
}
