//! Writing transition systems in the [DOT](https://graphviz.org/doc/info/lang.html) format and,
//! with the experimental features `render` and `graphviz`, rendering them as images.
//!
//! [`Dottable::dot_representation`] is always available. Rendering is possible with
//! - the feature `render`, which needs no external tools (module `native`), and
//! - the feature `graphviz`, which calls the `dot` executable of an installed graphviz
//!   (module `graphviz`).
//!
//! Both can hand images to the viewer of the system (`open_in_viewer`).

use crate::ts::IsEdge;
use crate::ts::States;
use itertools::Itertools;

mod attributes;
mod impls;

#[cfg(feature = "graphviz")]
mod graphviz;
#[cfg(feature = "render")]
mod native;
#[cfg(any(feature = "render", feature = "graphviz"))]
mod render;

pub use attributes::{DotStateAttribute, DotTransitionAttribute};
#[cfg(any(feature = "render", feature = "graphviz"))]
pub use render::{RenderError, open_in_viewer, svg_to_data_url};

/// Transition systems that can be written in the [DOT](https://graphviz.org/doc/info/lang.html)
/// format. [`Self::dot_representation`] is always available; rendering to images is experimental
/// and needs the features `render` or `graphviz`.
pub trait Dottable: States {
    /// Renders the DOT representation to an SVG document (experimental, feature `render`).
    #[cfg(feature = "render")]
    fn try_svg(&self) -> Result<String, RenderError> {
        native::dot_to_svg(&self.dot_representation())
    }

    /// Renders the DOT representation to an SVG and encodes it as a `data:` URL (experimental,
    /// feature `render`).
    #[cfg(feature = "render")]
    fn try_data_url(&self) -> Result<String, RenderError> {
        Ok(render::svg_to_data_url(&self.try_svg()?))
    }

    /// Like [`Self::try_svg`], but uses the `dot` executable of an installed
    /// [graphviz](https://graphviz.org/) (experimental, feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn try_svg_graphviz(&self) -> Result<String, RenderError> {
        let svg = graphviz::run_dot(&self.dot_representation(), "svg")?;
        String::from_utf8(svg)
            .map_err(|e| RenderError::Io(std::io::Error::new(std::io::ErrorKind::InvalidData, e)))
    }

    /// Like [`Self::try_data_url`], but uses the `dot` executable of an installed
    /// [graphviz](https://graphviz.org/) (experimental, feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn try_data_url_graphviz(&self) -> Result<String, RenderError> {
        Ok(render::svg_to_data_url(&self.try_svg_graphviz()?))
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
        native::svg_to_png(&self.try_svg()?)
    }

    /// Renders the object visually (as PNG) with the `dot` executable of an installed
    /// [graphviz](https://graphviz.org/) and returns the bytes of the image (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn render_graphviz(&self) -> Result<Vec<u8>, RenderError> {
        graphviz::run_dot(&self.dot_representation(), "png")
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
        let bytes = graphviz::run_dot(&self.dot_representation(), format).map_err(|e| match e {
            RenderError::Io(e) => e,
            other => std::io::Error::other(other),
        })?;
        std::fs::write(filename, bytes)
    }

    /// Renders the object to an SVG with `dot` and opens it in the default viewer of the system,
    /// see [`open_in_viewer`] (feature `graphviz`).
    #[cfg(feature = "graphviz")]
    fn display_rendered_graphviz(&self) -> Result<(), RenderError> {
        render::open_in_viewer(self.try_svg_graphviz()?.as_bytes(), "svg")
    }

    /// Renders the object to an SVG with the native backend and opens it in the default viewer
    /// of the system, see [`open_in_viewer`] (feature `render`).
    #[cfg(feature = "render")]
    fn display_rendered(&self) -> Result<(), RenderError> {
        render::open_in_viewer(self.try_svg()?.as_bytes(), "svg")
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
}
