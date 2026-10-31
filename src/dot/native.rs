use super::RenderError;

/// Lays out the graph described by the DOT source with `layout-rs` and writes it as SVG.
pub(super) fn dot_to_svg(dot: &str) -> Result<String, RenderError> {
    use layout::backends::svg::SVGWriter;

    tracing::trace!("rendering DOT representation\n{}", dot);

    let mut parser = layout::gv::parser::DotParser::new(dot);
    let graph = parser.process().map_err(|e| RenderError::RenderToSvgError(e.into()))?;

    let mut builder = layout::gv::GraphBuilder::new();
    builder.visit_graph(&graph);

    let mut visual_graph = builder.get();

    let mut svg = SVGWriter::new();
    visual_graph.do_it(false, false, false, &mut svg);

    Ok(svg.finalize())
}

/// Rasterizes an SVG document with `resvg` into a PNG with a white background.
pub(super) fn svg_to_png(svg: &str) -> Result<Vec<u8>, RenderError> {
    use resvg::usvg::{self, Transform};

    let mut svg_options = usvg::Options::default();
    svg_options.fontdb_mut().load_system_fonts();
    let tree = usvg::Tree::from_str(svg, &svg_options)?;

    let size = tree.size().to_int_size();
    let Some(mut pixmap) = resvg::tiny_skia::Pixmap::new(size.width(), size.height()) else {
        return Err(RenderError::PixmapAllocationError);
    };

    pixmap.fill(resvg::tiny_skia::Color::WHITE);
    resvg::render(&tree, Transform::identity(), &mut pixmap.as_mut());

    pixmap
        .encode_png()
        .map_err(|e| RenderError::PngEncodingError(Box::new(e)))
}

#[cfg(test)]
mod tests {
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
