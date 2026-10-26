use super::RenderError;

/// Runs `dot -T<format>` on the given DOT source and returns its standard output.
pub(super) fn run_dot(dot: &str, format: &str) -> Result<Vec<u8>, RenderError> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    tracing::trace!("running dot -T{format} on\n{dot}");
    let mut child = Command::new("dot")
        .arg(format!("-T{format}"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| match e.kind() {
            std::io::ErrorKind::NotFound => RenderError::DotNotFound,
            _ => RenderError::Io(e),
        })?;

    if let Some(mut stdin) = child.stdin.take() {
        let dot = dot.to_owned();
        // written from a separate thread so that large inputs cannot deadlock against the output
        std::thread::spawn(move || stdin.write_all(dot.as_bytes()));
    }

    let output = child.wait_with_output()?;
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(RenderError::DotFailed {
            status: output.status,
            stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::{Dottable, RenderError};
    use crate::ts::Builder;

    fn dot_is_installed() -> bool {
        std::process::Command::new("dot").arg("-V").output().is_ok()
    }

    fn dfa() -> crate::automaton::DFA {
        Builder::without_edge_colors()
            .with_state_colors([true, false])
            .with_transitions([(0, 'a', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dfa(0)
    }

    #[test]
    fn graphviz_renders_svg_png_and_data_url() {
        if !dot_is_installed() {
            eprintln!("skipping, `dot` is not installed");
            return;
        }
        let dfa = dfa();
        assert!(dfa.try_svg_graphviz().unwrap().contains("<svg"));
        assert!(
            dfa.render_graphviz()
                .unwrap()
                .starts_with(&[0x89, b'P', b'N', b'G'])
        );
        let url = dfa.try_data_url_graphviz().unwrap();
        assert!(url.starts_with("data:image/svg+xml;base64,"), "{url}");
    }

    #[test]
    fn graphviz_reports_invalid_dot() {
        if !dot_is_installed() {
            return;
        }
        let err = super::run_dot("this is not dot", "svg").unwrap_err();
        assert!(matches!(err, RenderError::DotFailed { .. }), "{err}");
    }
}
