use std::fmt::{Debug, Display};
#[cfg(any(feature = "render", feature = "graphviz"))]
use thiserror::Error;

use crate::automaton::{DFA, IntoDPA, IntoMealyMachine, IntoMooreMachine};
use crate::ts::{Deterministic, IsEdge, StateColor, StateIndex};
use crate::{Color, Int, Show, alphabet::Alphabet};
use crate::{Pointed, TransitionSystem};
use itertools::Itertools;

/// Errors that can occur while rendering a transition system as an image or while displaying it.
#[cfg(any(feature = "render", feature = "graphviz"))]
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
    #[error("could not encode PNG: \"{0:?}\"")]
    PngEncodingError(String),
    /// The DOT representation could not be rendered to SVG (feature `render`).
    #[cfg(feature = "render")]
    #[error("could not render to SVG: \"{0}\"")]
    RenderToSvgError(String),
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

/// Transition systems that can be written in the [DOT](https://graphviz.org/doc/info/lang.html)
/// format. [`Self::dot_representation`] is always available; rendering to images is experimental
/// and needs the features `render` or `graphviz`.
pub trait Dottable: TransitionSystem {
    /// Renders the DOT representation to an SVG document (experimental, feature `render`).
    #[cfg(feature = "render")]
    fn try_svg(&self) -> Result<String, RenderError> {
        use layout::backends::svg::SVGWriter;
        let dot = self.dot_representation();

        tracing::trace!("produced DOT representation\n{}", dot);

        let mut parser = layout::gv::parser::DotParser::new(&dot);

        let graph = parser.process().map_err(RenderError::RenderToSvgError)?;

        let mut builder = layout::gv::GraphBuilder::new();
        builder.visit_graph(&graph);

        let mut visual_graph = builder.get();

        let mut svg = SVGWriter::new();
        visual_graph.do_it(false, false, false, &mut svg);

        Ok(svg.finalize())
    }

    /// Renders the DOT representation to an SVG and encodes it as a `data:` URL (experimental,
    /// feature `render`).
    #[cfg(feature = "render")]
    fn try_data_url(&self) -> Result<String, RenderError> {
        Ok(svg_to_data_url(&self.try_svg()?))
    }

    /// Like [`Self::try_svg`], but uses the `dot` executable of an installed
    /// [graphviz](https://graphviz.org/) (experimental, feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn try_svg_graphviz(&self) -> Result<String, RenderError> {
        let svg = run_dot(&self.dot_representation(), "svg")?;
        String::from_utf8(svg)
            .map_err(|e| RenderError::Io(std::io::Error::new(std::io::ErrorKind::InvalidData, e)))
    }

    /// Like [`Self::try_data_url`], but uses the `dot` executable of an installed
    /// [graphviz](https://graphviz.org/) (experimental, feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn try_data_url_graphviz(&self) -> Result<String, RenderError> {
        Ok(svg_to_data_url(&self.try_svg_graphviz()?))
    }

    /// Compute the graphviz representation, for more information on the DOT format,
    /// see the [graphviz documentation](https://graphviz.org/doc/info/lang.html).
    fn dot_representation(&self) -> String {
        let header = std::iter::once(format!(
            "digraph {} {{",
            self.dot_name().unwrap_or("A".to_string())
        ))
        .chain(self.dot_header_statements());

        let initial = self.dot_initial_state().into_iter().flat_map(|q| {
            [
                format!("{DOT_INITIAL_NODE} [shape=\"point\", label=\"\"]"),
                format!(
                    "{DOT_INITIAL_NODE} -> {}",
                    sanitize_dot_ident(&self.dot_state_ident(q))
                ),
            ]
        });

        let states = self.state_indices().map(|q| {
            format!(
                "{} [{}]",
                sanitize_dot_ident(&self.dot_state_ident(q)),
                self.dot_state_attributes(q)
                    .into_iter()
                    .map(|attr| attr.to_string())
                    .join(", ")
            )
        });

        let transitions = self.state_indices().flat_map(|q| {
            self.edges_from(q)
                .expect("edges_from may not return none for state that exists")
                .map(move |t| {
                    format!(
                        "{} -> {} [{}]",
                        sanitize_dot_ident(&self.dot_state_ident(q)),
                        sanitize_dot_ident(&self.dot_state_ident(t.target())),
                        self.dot_transition_attributes(t)
                            .into_iter()
                            .map(|attr| attr.to_string())
                            .join(", ")
                    )
                })
        });

        let mut lines = header
            .chain(initial)
            .chain(states)
            .chain(transitions)
            .chain(std::iter::once("}".to_string()));
        lines.join("\n")
    }

    /// Additional statements for the header of the DOT graph, none by default.
    fn dot_header_statements(&self) -> impl IntoIterator<Item = String> {
        []
    }

    /// The state that is marked as initial in the drawing by an arrow without source, none by
    /// default.
    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        None
    }

    /// The name of the graph, if any.
    fn dot_name(&self) -> Option<String>;

    /// Additional attributes of the DOT edge that represents the given edge, none by default.
    fn dot_transition_attributes<'a>(
        &'a self,
        _t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        []
    }
    /// The identifier of the DOT node that represents the state with the given index.
    fn dot_state_ident(&self, idx: Self::StateIndex) -> String;
    /// Additional attributes of the DOT node that represents the state with the given index, none
    /// by default.
    fn dot_state_attributes(
        &self,
        _idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        []
    }

    /// Renders the object visually (as PNG) and returns a vec of bytes/u8s encoding
    /// the rendered image. It does so by first producing an SVG from the DOT representation
    /// using the `render` crate. Subsequently, this SVG is rendered through the
    /// `resvg` crate, resulting in a PNG of the graph.
    #[cfg(feature = "render")]
    fn render(&self) -> Result<Vec<u8>, RenderError> {
        use resvg::usvg::{self, Transform};
        let svg = self.try_svg()?;

        let mut svg_options = usvg::Options::default();
        svg_options.fontdb_mut().load_system_fonts();
        let tree = usvg::Tree::from_str(&svg, &svg_options)?;

        let size = tree.size().to_int_size();
        let Some(mut pixmap) = resvg::tiny_skia::Pixmap::new(size.width(), size.height()) else {
            return Err(RenderError::PixmapAllocationError);
        };

        pixmap.fill(resvg::tiny_skia::Color::WHITE);
        resvg::render(&tree, Transform::identity(), &mut pixmap.as_mut());

        pixmap
            .encode_png()
            .map_err(|e| RenderError::PngEncodingError(format!("{:?}", e)))
    }

    /// Renders the object visually (as PNG) with the `dot` executable of an installed
    /// [graphviz](https://graphviz.org/) and returns the bytes of the image (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn render_graphviz(&self) -> Result<Vec<u8>, RenderError> {
        run_dot(&self.dot_representation(), "png")
    }

    /// Renders the object with `dot` and writes the result to the file with the given name.
    /// The output format is derived from the file extension (for example `svg`, `png` or `pdf`),
    /// it defaults to `png` (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn render_to_file_name(&self, filename: &str) -> Result<(), std::io::Error> {
        let format = std::path::Path::new(filename)
            .extension()
            .and_then(|e| e.to_str())
            .unwrap_or("png");
        let bytes = run_dot(&self.dot_representation(), format).map_err(|e| match e {
            RenderError::Io(e) => e,
            other => std::io::Error::other(other),
        })?;
        std::fs::write(filename, bytes)
    }

    /// Renders the object to an SVG with `dot` and opens it in the default viewer of the system,
    /// see [`open_in_viewer`] (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn display_rendered_graphviz(&self) -> Result<(), RenderError> {
        open_in_viewer(self.try_svg_graphviz()?.as_bytes(), "svg")
    }

    /// Renders the object to an SVG with the native backend and opens it in the default viewer
    /// of the system, see [`open_in_viewer`] (feature `render`).
    #[cfg(feature = "render")]
    fn display_rendered(&self) -> Result<(), RenderError> {
        open_in_viewer(self.try_svg()?.as_bytes(), "svg")
    }
}

impl<A: Alphabet> Dottable for DFA<A>
where
    StateIndex<Self>: Show,
{
    fn dot_name(&self) -> Option<String> {
        Some("DFA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{}", idx.show())
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        [DotTransitionAttribute::Label(t.expression().show())].into_iter()
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute>
    where
        (String, StateColor<Self>): Show,
    {
        let shape = if self.state_color(idx).unwrap() {
            "doublecircle"
        } else {
            "circle"
        };
        vec![
            DotStateAttribute::Shape(shape.into()),
            DotStateAttribute::Label(self.dot_state_ident(idx)),
        ]
    }
}
impl<A: Alphabet, Q: Color, C: Color> Dottable for crate::RightCongruence<A, Q, C>
where
    StateIndex<Self>: Show,
{
    fn dot_name(&self) -> Option<String> {
        Some("Congruence".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("c{}", idx.show())
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        [DotTransitionAttribute::Label(format!(
            "{:?}|{:?}",
            t.expression(),
            IsEdge::color(&t)
        ))]
        .into_iter()
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        vec![DotStateAttribute::Label(format!(
            "{}|{:?}",
            self.dot_state_ident(idx),
            self.state_color(idx).unwrap()
        ))]
    }
}

impl<M> Dottable for IntoMooreMachine<M>
where
    M: Deterministic,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        let color = self
            .state_color(idx)
            .map(|c| format!(" | {c:?}"))
            .unwrap_or("".to_string());
        vec![DotStateAttribute::Label(format!(
            "{}{color}",
            self.dot_state_ident(idx)
        ))]
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(t.expression().show())]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

impl<M> Dottable for IntoMealyMachine<M>
where
    M: Deterministic,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        if self.initial() == idx {
            vec![DotStateAttribute::Label(format!(
                "->{}",
                self.dot_state_ident(idx)
            ))]
        } else {
            vec![DotStateAttribute::Label(self.dot_state_ident(idx))]
        }
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{:?}",
            t.expression().show(),
            IsEdge::color(&t)
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

impl<D> Dottable for IntoDPA<D>
where
    D: Deterministic<EdgeColor = Int>,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute> {
        vec![DotStateAttribute::Label(self.dot_state_ident(idx))]
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute> {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{}",
            t.expression().show(),
            IsEdge::color(&t).show()
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{idx:?}")
    }
}

/// Enum that abstracts attributes in the DOT format.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum DotStateAttribute {
    /// The label of a node
    Label(String),
    /// The shape of a node
    Shape(String),
    /// The color of a node
    Color(String),
}

impl Display for DotStateAttribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                DotStateAttribute::Label(s) => format!("label=\"{}\"", s),
                DotStateAttribute::Shape(s) => format!("shape=\"{}\"", s),
                DotStateAttribute::Color(c) => format!("color=\"{}\"", c),
            }
        )
    }
}

/// An attribute of an edge in the DOT representation.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum DotTransitionAttribute {
    /// The label of the edge.
    Label(String),
}

impl Display for DotTransitionAttribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DotTransitionAttribute::Label(lbl) => write!(f, "label=\"{lbl}\""),
        }
    }
}

/// Encodes an SVG document as a `data:` URL that can be pasted into the address bar of a browser.
#[cfg(any(feature = "render", feature = "graphviz"))]
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
#[cfg(any(feature = "render", feature = "graphviz"))]
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

#[cfg(any(feature = "render", feature = "graphviz"))]
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

/// Runs `dot -T<format>` on the given DOT source and returns its standard output.
#[cfg(feature = "graphviz")]
fn run_dot(dot: &str, format: &str) -> Result<Vec<u8>, RenderError> {
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

/// The name of the node that only exists to draw the arrow into the initial state.
const DOT_INITIAL_NODE: &str = "init";

fn sanitize_dot_ident(name: &str) -> String {
    name.chars()
        .filter_map(|chr| match chr {
            c if c.is_alphanumeric() => Some(c),
            '|' => Some('_'),
            '(' => None,
            ')' => None,
            '[' => None,
            ']' => None,
            ':' => Some('_'),
            ',' => Some('_'),
            w if w.is_whitespace() => None,
            u => panic!("unexpected symbol {u} in identifier \"{name}\""),
        })
        .join("")
}

#[cfg(test)]
mod tests {
    use super::Dottable;
    use crate::ts::Builder;

    #[test]
    fn dot_representation_of_a_dfa() {
        let dfa = Builder::without_edge_colors()
            .with_state_colors([true, false])
            .with_transitions([(0, 'a', 1), (1, 'a', 0), (1, 'b', 1)])
            .into_dfa(0);

        let dot = dfa.dot_representation();
        assert!(dot.starts_with("digraph"), "{dot}");
        assert!(dot.contains(r#"q0 [shape="doublecircle""#), "{dot}");
        assert!(dot.contains(r#"q1 [shape="circle""#), "{dot}");
        assert!(dot.contains(r#"q0 -> q1 [label="a"]"#), "{dot}");
        assert!(dot.contains(r#"q1 -> q1 [label="b"]"#), "{dot}");
        assert!(dot.contains("init -> q0"), "{dot}");
    }

    #[cfg(feature = "render")]
    mod render {
        use super::super::Dottable;
        use crate::ts::Builder;

        fn dpa() -> crate::automaton::DPA {
            Builder::without_state_colors()
                .with_transitions([
                    (0, 'a', 1, 0),
                    (0, 'b', 2, 1),
                    (1, 'a', 0, 1),
                    (1, 'b', 2, 0),
                ])
                .into_dpa(0)
        }

        #[test]
        fn svg_is_rendered_without_external_tools() {
            let svg = dpa().try_svg().expect("rendering to SVG works");
            assert!(svg.contains("<svg"), "{svg}");
        }

        #[test]
        fn png_is_rendered_without_external_tools() {
            let png = dpa().render().expect("rendering to PNG works");
            assert!(png.starts_with(&[0x89, b'P', b'N', b'G']));
        }

        #[test]
        fn data_url_encodes_the_svg() {
            let url = dpa().try_data_url().expect("rendering to a data URL works");
            assert!(url.starts_with("data:image/svg+xml;base64,"), "{url}");
        }
    }

    #[cfg(any(feature = "render", feature = "graphviz"))]
    #[test]
    fn data_url_is_decodable() {
        use base64::Engine;
        let url = super::svg_to_data_url("<svg/>");
        let payload = url.strip_prefix("data:image/svg+xml;base64,").unwrap();
        let decoded = base64::prelude::BASE64_STANDARD.decode(payload).unwrap();
        assert_eq!(decoded, b"<svg/>");
    }

    #[cfg(any(feature = "render", feature = "graphviz"))]
    #[test]
    fn temporary_file_keeps_extension_and_contents() {
        let path = super::write_temporary_file(b"hello", "svg").unwrap();
        assert_eq!(path.extension().unwrap(), "svg");
        assert_eq!(std::fs::read(&path).unwrap(), b"hello");
        std::fs::remove_file(path).unwrap();
    }

    #[cfg(feature = "graphviz")]
    mod graphviz {
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
            let err = super::super::run_dot("this is not dot", "svg").unwrap_err();
            assert!(matches!(err, RenderError::DotFailed { .. }), "{err}");
        }
    }
}
