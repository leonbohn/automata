#![allow(missing_docs)]

use std::fmt::{Debug, Display};

use itertools::Itertools;

use crate::{automaton::IntoDPA, prelude::*, Alphabet, Color, Show, TransitionSystem};

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

pub trait Dottable: TransitionSystem {
    /// Compute the graphviz representation, for more information on the DOT format,
    /// see the [graphviz documentation](https://graphviz.org/doc/info/lang.html).
    fn dot_representation<'a>(&'a self) -> String
    where
        (String, StateColor<Self>): Show,
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
        let header = std::iter::once(format!(
            "digraph {} {{",
            self.dot_name().unwrap_or("A".to_string())
        ))
        .chain(self.dot_header_statements());

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
            .chain(states)
            .chain(transitions)
            .chain(std::iter::once("}".to_string()));
        lines.join("\n")
    }

    fn dot_header_statements(&self) -> impl IntoIterator<Item = String> {
        []
    }

    fn dot_name(&self) -> Option<String>;

    fn dot_transition_attributes<'a>(
        &'a self,
        _t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
        []
    }
    fn dot_state_ident(&self, idx: Self::StateIndex) -> String;
    fn dot_state_attributes(
        &self,
        _idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute>
    where
        (String, StateColor<Self>): Show,
    {
        []
    }
    /// Renders the object visually (as PNG) and returns a vec of bytes/u8s encoding
    /// the rendered image. This method is only available on the `graphviz` crate feature
    /// and makes use of temporary files.
    #[cfg(feature = "graphviz")]
    fn render<'a>(&'a self) -> Result<Vec<u8>, std::io::Error>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
        (String, StateColor<Self>): Show,
    {
        use std::io::{Read, Write};

        use tracing::trace;
        let dot = self.dot_representation();
        trace!("writing dot representation\n{}", dot);

        let mut child = std::process::Command::new("dot")
            .arg("-Tpng")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()?;

        if let Some(mut stdin) = child.stdin.take() {
            stdin.write_all(dot.as_bytes())?;
        }

        let mut output = Vec::new();
        if let Some(mut stdout) = child.stdout.take() {
            stdout.read_to_end(&mut output)?;
        }

        let status = child.wait()?;
        if !status.success() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                format!("dot process exited with status: {}", status),
            ));
        }

        Ok(output)
    }

    /// Attempts to render the object to a file with the given filename. This method
    /// is only available on the `graphviz` crate feature and makes use of temporary files.
    #[cfg(feature = "graphviz")]
    fn render_to_file_name<'a>(&'a self, filename: &str) -> Result<(), std::io::Error>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
        (String, StateColor<Self>): Show,
    {
        use std::io::{Read, Write};
        use tracing::trace;

        trace!("Outputting dot and rendering to png");
        let dot = self.dot_representation();
        let mut tempfile = tempfile::NamedTempFile::new()?;

        tempfile.write_all(dot.as_bytes())?;
        let tempfile_name = tempfile.path();

        let mut child = std::process::Command::new("dot")
            .arg("-Tpng")
            .arg("-o")
            .arg(filename)
            .arg(tempfile_name)
            .spawn()?;
        if !child.wait()?.success() {
            Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                child
                    .stdout
                    .map_or("Error in dot...".to_string(), |mut err| {
                        let mut buf = String::new();
                        if let Err(e) = err.read_to_string(&mut buf) {
                            buf = format!("Could not read from stdout: {e}");
                        }
                        buf
                    }),
            ))
        } else {
            Ok(())
        }
    }

    /// First creates a rendered PNG using [`Self::render()`], after which the rendered
    /// image is displayed via by using a locally installed image viewer.
    /// This method is only available on the `graphviz` crate feature.
    ///
    /// # Image viewer
    /// On Macos, the Preview app is used, while on Linux and Windows, the image viewer
    /// can be configured by setting the `IMAGE_VIEWER` environment variable. If it is not set,
    /// then the display command of ImageMagick will be used.
    #[cfg(feature = "graphviz")]
    fn display_rendered<'a>(&'a self) -> Result<(), std::io::Error>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
        (String, StateColor<Self>): Show,
    {
        display_png(self.render()?)?;
        Ok(())
    }
}

impl<A: Alphabet> Dottable for DFA<A> {
    fn dot_name(&self) -> Option<String> {
        Some("DFA".into())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{}", idx.show())
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
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
impl<A: Alphabet, Q: Color, C: Color> Dottable for crate::RightCongruence<A, Q, C> {
    fn dot_name(&self) -> Option<String> {
        Some("Congruence".into())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("c{}", idx.show())
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
        [DotTransitionAttribute::Label(
            (t.expression(), t.color()).show(),
        )]
        .into_iter()
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute>
    where
        (String, StateColor<Self>): Show,
    {
        vec![DotStateAttribute::Label(
            (self.dot_state_ident(idx), self.state_color(idx).unwrap()).show(),
        )]
    }
}

impl<M> Dottable for IntoMooreMachine<M>
where
    M: Deterministic,
    StateColor<M>: Show,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = DotStateAttribute>
    where
        (String, StateColor<Self>): Show,
    {
        let color = self
            .state_color(idx)
            .map(|c| format!(" | {}", c.show()))
            .unwrap_or("".to_string());
        vec![DotStateAttribute::Label(format!(
            "{}{color}",
            self.dot_state_ident(idx)
        ))]
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = DotTransitionAttribute>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
        vec![DotTransitionAttribute::Label(t.expression().show())]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{}", idx.show())
    }
}

impl<M> Dottable for IntoMealyMachine<M>
where
    M: Deterministic,
    EdgeColor<M>: Show,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
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
    ) -> impl IntoIterator<Item = DotTransitionAttribute>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{}",
            t.expression().show(),
            t.color().show()
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{}", idx.show())
    }
}

impl<D> Dottable for IntoDPA<D>
where
    D: Deterministic<EdgeColor = usize>,
{
    fn dot_name(&self) -> Option<String> {
        Some("DPA".into())
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
    ) -> impl IntoIterator<Item = DotTransitionAttribute>
    where
        (&'a EdgeExpression<Self>, EdgeColor<Self>): Show,
    {
        vec![DotTransitionAttribute::Label(format!(
            "{}|{}",
            t.expression().show(),
            t.color().show()
        ))]
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!("q{}", idx.show())
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

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum DotTransitionAttribute {
    Label(String),
}

impl Display for DotTransitionAttribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DotTransitionAttribute::Label(lbl) => write!(f, "label=\"{lbl}\""),
        }
    }
}

// impl<A: Alphabet, Q: Color + Debug, C: Color + Debug> ToDot for Vec<RightCongruence<A, Q, C>>
// where
//     A::Symbol: Display,
//     Q: DotStateColorize,
//     DotTransitionInfo<C, A>: DotTransition,
// {
//     fn dot_representation(&self) -> String {
//         format!("digraph A {{\n{}\n{}\n}}\n", self.header(), self.body(""),)
//     }

//     fn header(&self) -> String {
//         [
//             "compound=true".to_string(),
//             "fontname=\"Helvetica,Arial,sans-serif\"\nrankdir=LR".to_string(),
//             "init [label=\"\", shape=none]".into(),
//             "node [shape=rect]".into(),
//         ]
//         .join("\n")
//     }

//     fn body(&self, _prefix: &str) -> String {
//         self.iter()
//             .enumerate()
//             .map(|(i, cong)| {
//                 format!(
//                     "subgraph cluster_{} {{\n{}\n{}\n}}\n",
//                     i,
//                     cong.header(),
//                     cong.body(&format!("{i}"))
//                 )
//             })
//             .join("\n")
//     }
// }

// impl<A: Alphabet, Q: Color + Debug, C: Color + Debug> ToDot for FORC<A, Q, C>
// where
//     A::Symbol: Display,
//     Q: DotStateColorize,
//     DotTransitionInfo<C, A>: DotTransition,
// {
//     fn dot_representation(&self) -> String {
//         format!("digraph A {{\n{}\n{}\n}}\n", self.header(), self.body(""),)
//     }

//     fn header(&self) -> String {
//         [
//             "compund=true".to_string(),
//             "fontname=\"Helvetica,Arial,sans-serif\"\nrankdir=LR".to_string(),
//             "init [label=\"\", shape=none]".into(),
//             "node [shape=rect]".into(),
//         ]
//         .join("\n")
//     }

//     fn body(&self, _prefix: &str) -> String {
//         let mut lines = self
//             .progress
//             .iter()
//             .map(|(class, prc)| {
//                 format!(
//                     "subgraph cluster_{} {{\n{}\n{}\n}}\n",
//                     self.leading()
//                         .state_color(*class)
//                         .unwrap()
//                         .class()
//                         .mr_to_string(),
//                     prc.header(),
//                     prc.body(&class.to_string())
//                 )
//             })
//             .collect_vec();

//         lines.push("init [label=\"\", shape=none]".to_string());
//         let eps_prc = self
//             .prc(&Class::epsilon())
//             .expect("Must have at least the epsilon prc");
//         lines.push(format!(
//             "init -> \"{},init\" [style=\"solid\"]",
//             eps_prc
//                 .state_color(eps_prc.initial())
//                 .expect("State should have a color")
//         ));

//         for state in self.leading.state_indices() {
//             for sym in self.leading.alphabet().universe() {
//                 if let Some(edge) = self.leading.transition(state, sym) {
//                     let _source_prc = self
//                         .prc(
//                             self.leading
//                                 .state_color(state)
//                                 .expect("State should be colored")
//                                 .class(),
//                         )
//                         .expect("Must have a prc for every state");
//                     let _target_prc = self
//                         .prc(
//                             self.leading
//                                 .state_color(edge.target())
//                                 .expect("State should be colored")
//                                 .class(),
//                         )
//                         .expect("Must have a prc for every state");
//                     lines.push(format!(
//                         "\"{},init\" -> \"{},init\" [label = \"{}\", style=\"dashed\", ltail=\"cluster_{}\", lhead=\"cluster_{}\"]",
//                         self.leading.state_color(state).expect("State should be colored"),
//                         self.leading.state_color(edge.target()).expect("State should be colored"),
//                         sym,
//                         self.leading.state_color(state).expect("State should be colored").class().mr_to_string(),
//                         self.leading.state_color(edge.target()).expect("State should be colored").class().mr_to_string()
//                     ));
//                 }
//             }
//         }

//         lines.join("\n")
//     }
// }

/// Renders the given dot string to a png file and displays it using the default
/// image viewer on the system.
#[cfg(feature = "graphviz")]
pub fn display_dot(dot: &str) -> Result<(), std::io::Error> {
    display_png(render_dot_to_tempfile(dot)?)
}

#[cfg(feature = "graphviz")]
fn render_dot_to_tempfile(dot: &str) -> Result<Vec<u8>, std::io::Error> {
    use std::{io::Write, process::Stdio};

    let mut tempfile = tempfile::NamedTempFile::new()?;
    tempfile.write_all(dot.as_bytes())?;

    let mut child = std::process::Command::new("dot")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .arg("-Tpng")
        .spawn()?;

    let mut stdin = child.stdin.take().expect("Could not get handle to stdin");
    stdin.write_all(dot.as_bytes())?;

    match child.wait_with_output() {
        Ok(res) => {
            if res.status.success() {
                Ok(res.stdout)
            } else {
                let stderr_output =
                    String::from_utf8(res.stderr).expect("could not parse stderr of dot");
                tracing::error!("Could not render, dot reported\n{}", &stderr_output);
                Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    stderr_output,
                ))
            }
        }
        Err(e) => {
            let e = format!("Could not create dot child process\n{}", e);
            tracing::error!("{e}");
            Err(std::io::Error::other(e))
        }
    }
}

/// Displays a png given as a vector of bytes by calling an image viewer.
/// On Macos, that is the Preview app, while on Linux and Windows this can be configured by
/// setting the IMAGE_VIEWER environment variable. If it is not set, then the display command
/// of ImageMagick will be used.
#[cfg(feature = "graphviz")]
fn display_png(contents: Vec<u8>) -> std::io::Result<()> {
    use std::{io::Write, process::Stdio};

    use tracing::trace;
    let mut child = if cfg!(target_os = "linux") || cfg!(target_os = "windows") {
        let image_viewer = std::env::var("IMAGE_VIEWER").unwrap_or("display".to_string());

        std::process::Command::new(image_viewer)
            .stdin(Stdio::piped())
            .spawn()
            .unwrap()
    } else if cfg!(target_os = "macos") {
        std::process::Command::new("open")
            .arg("-a")
            .arg("Preview.app")
            .arg("-f")
            .stdin(Stdio::piped())
            .spawn()
            .unwrap()
    } else {
        unreachable!("Platform not supported!")
    };

    let mut stdin = child.stdin.take().unwrap();
    std::thread::spawn(move || {
        stdin
            .write_all(&contents)
            .expect("Could not write file to stdin");
        let output = child
            .wait_with_output()
            .expect("Error in display child process!");
        trace!("png display command exited with {}", output.status);
    });

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::{congruence::FORC, prelude::*};

    use super::Dottable;

    #[test_log::test]
    #[ignore]
    fn render_dfa() {
        let dfa = LinkedListNondeterministic::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 1),
                (1, 'a', Void, 1),
                (1, 'b', Void, 0),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);
        dfa.display_rendered().unwrap();
    }

    #[test]
    #[ignore]
    fn display_forc() {
        let cong = TSBuilder::without_colors()
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 0), (1, 'b', 1)])
            .into_right_congruence(0);

        let prc_e = TSBuilder::without_colors()
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 1),
                (1, 'b', 2),
                (2, 'a', 2),
                (2, 'b', 2),
            ])
            .into_right_congruence(0);

        let prc_a = TSBuilder::without_colors()
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 3),
                (1, 'b', 2),
                (2, 'a', 1),
                (2, 'b', 2),
                (3, 'a', 3),
                (3, 'b', 3),
            ])
            .into_right_congruence(0);

        let _forc = FORC::from_iter(cong, [(0, prc_e), (1, prc_a)].iter().cloned());
        todo!("Learn how to render FORC!")
    }

    #[test]
    #[ignore]
    fn dot_render_dpa() {
        let dpa = TSBuilder::without_state_colors()
            .with_edges([
                (0, 'a', 1, 0),
                (0, 'b', 2, 1),
                (1, 'a', 0, 1),
                (1, 'b', 2, 0),
            ])
            .into_dpa(0);
        dpa.display_rendered().unwrap();
    }
}
