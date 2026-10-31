use thiserror::Error;

/// Errors that can occur while rendering a transition system as an image or while displaying it.
#[derive(Error, Debug)]
#[non_exhaustive]
pub enum RenderError {
    /// The generated SVG could not be processed (feature `render`).
    #[cfg(feature = "render")]
    #[error("encountered SVG rendering error: \"{0:?}\"")]
    SvgError(#[from] resvg::usvg::Error),
    /// The pixmap for the rendered image could not be allocated (feature `render`).
    #[cfg(feature = "render")]
    #[error("could not allocate pixmap")]
    PixmapAllocationError,
    /// The rendered image could not be encoded as a PNG (feature `render`).
    #[cfg(feature = "render")]
    #[error("could not encode PNG: {0}")]
    PngEncodingError(Box<dyn std::error::Error + Send + Sync>),
    /// The DOT representation could not be rendered to SVG (feature `render`).
    #[cfg(feature = "render")]
    #[error("could not render to SVG: {0}")]
    RenderToSvgError(Box<dyn std::error::Error + Send + Sync>),
    /// A file could not be written or a viewer could not be started.
    #[error("I/O error while rendering or displaying: \"{0}\"")]
    Io(#[from] std::io::Error),
    /// The graphviz `dot` executable could not be found in the `PATH` (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    #[error(
        "the graphviz `dot` executable was not found, install graphviz and make sure it is in the PATH"
    )]
    DotNotFound,
    /// The graphviz `dot` executable finished with a non-zero exit status (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    #[error("`dot` exited with {status}: {stderr}")]
    DotFailed {
        /// The exit status of the process.
        status: std::process::ExitStatus,
        /// What `dot` printed to its standard error.
        stderr: String,
    },
}

/// Encodes an SVG document as a `data:` URL that can be pasted into the address bar of a browser.
pub fn svg_to_data_url(svg: &str) -> String {
    format!(
        "data:image/svg+xml;base64,{}",
        base64::Engine::encode(&base64::prelude::BASE64_STANDARD, svg)
    )
}

/// Writes `contents` to a temporary file with the given extension and opens it in the viewer of
/// the system, which is `xdg-open` on Linux, `open` on macOS and `start` on Windows. Another
/// program can be chosen by setting the `IMAGE_VIEWER` environment variable, it is then called
/// with the path of the file as its only argument.
///
/// The file is not deleted, as the viewer may still be reading it when this function returns.
pub fn open_in_viewer(contents: &[u8], extension: &str) -> Result<(), RenderError> {
    let path = write_temporary_file(contents, extension)?;
    tracing::debug!("opening {} in the viewer", path.display());
    match std::env::var_os("IMAGE_VIEWER") {
        Some(viewer) => {
            let mut child = std::process::Command::new(viewer).arg(&path).spawn()?;
            std::thread::spawn(move || {
                let _ = child.wait();
            });
        }
        None => open::that_detached(&path)?,
    }
    Ok(())
}

fn write_temporary_file(
    contents: &[u8],
    extension: &str,
) -> Result<std::path::PathBuf, std::io::Error> {
    use std::io::Write;
    let mut file = tempfile::Builder::new()
        .prefix("automata-")
        .suffix(&format!(".{extension}"))
        .tempfile()?;
    file.write_all(contents)?;
    let (_, path) = file.keep().map_err(std::io::Error::from)?;
    Ok(path)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn data_url_is_decodable() {
        use base64::Engine;
        let url = svg_to_data_url("<svg/>");
        let payload = url.strip_prefix("data:image/svg+xml;base64,").unwrap();
        let decoded = base64::prelude::BASE64_STANDARD.decode(payload).unwrap();
        assert_eq!(decoded, b"<svg/>");
    }

    #[test]
    fn temporary_file_keeps_extension_and_contents() {
        let path = write_temporary_file(b"hello", "svg").unwrap();
        assert_eq!(path.extension().unwrap(), "svg");
        assert_eq!(std::fs::read(&path).unwrap(), b"hello");
        std::fs::remove_file(path).unwrap();
    }
}
