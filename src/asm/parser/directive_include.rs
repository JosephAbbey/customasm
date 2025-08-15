use crate::*;

#[derive(Clone, Debug)]
pub struct AstDirectiveInclude {
    pub header_span: diagn::Span,
    pub filename_span: diagn::Span,
    pub filename: String,
}

pub fn parse(
    report: &mut diagn::Report,
    walker: &mut syntax::Walker,
    header_span: diagn::Span,
) -> Result<AstDirectiveInclude, ()> {
    let tk_filename = walker.expect(report, syntax::TokenKind::String)?;

    let filename = syntax::excerpt_as_string_contents(
        report,
        tk_filename.span,
        walker.get_span_excerpt(tk_filename.span),
    )?;

    walker.expect_linebreak(report)?;

    Ok(AstDirectiveInclude {
        header_span: header_span.join(tk_filename.span),
        filename_span: tk_filename.span,
        filename,
    })
}
