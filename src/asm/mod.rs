use core::num;

use crate::{diagn::Span, *};

pub mod parser;
pub use parser::{
    AstAny, AstDirectiveAddr, AstDirectiveAlign, AstDirectiveAssert, AstDirectiveBank,
    AstDirectiveBankdef, AstDirectiveBits, AstDirectiveData, AstDirectiveFn, AstDirectiveInclude,
    AstDirectiveLabelAlign, AstDirectiveNoEmit, AstDirectiveOnce, AstDirectiveRes,
    AstDirectiveRuledef, AstField, AstFields, AstFnParameter, AstInstruction, AstRule,
    AstRuleParameter, AstRuleParameterType, AstRulePatternPart, AstSymbol, AstSymbolConstant,
    AstSymbolKind, AstTopLevel,
};

pub mod decls;
pub use decls::ItemDecls;

pub mod defs;
pub use defs::{
    AddrDirective, AlignDirective, Bankdef, DataElement, Function, FunctionParameter, Instruction,
    ItemDefs, ResDirective, Rule, RuleParameter, RuleParameterType, RulePattern, RulePatternPart,
    Ruledef, RuledefMap, RuledefMapEntry, Symbol,
};

pub mod matcher;
pub use matcher::{
    InstructionArgument, InstructionArgumentKind, InstructionMatch, InstructionMatchResolution,
    InstructionMatches,
};

pub mod resolver;
pub use resolver::{ResolutionState, ResolveIterator, ResolverContext, ResolverNode};

pub mod output;

pub struct AssemblyResult {
    pub error: bool,
    pub ast: Option<asm::AstTopLevel>,
    pub decls: Option<asm::ItemDecls>,
    pub defs: Option<asm::ItemDefs>,
    pub output: Option<util::BitVec>,
    pub iterations_taken: Option<usize>,
}

pub struct AssemblyOptions {
    pub max_iterations: usize,
    pub debug_iterations: bool,
    pub optimize_statically_known: bool,
    pub optimize_instruction_matching: bool,

    pub driver_symbol_defs: Vec<DriverSymbolDef>,
}

pub struct DriverSymbolDef {
    pub name: String,
    pub value: expr::Value,
}

impl AssemblyResult {
    pub fn new() -> AssemblyResult {
        AssemblyResult {
            error: false,
            ast: None,
            decls: None,
            defs: None,
            output: None,
            iterations_taken: None,
        }
    }
}

impl AssemblyOptions {
    pub fn new() -> AssemblyOptions {
        AssemblyOptions {
            max_iterations: 10,
            debug_iterations: false,
            optimize_statically_known: true,
            optimize_instruction_matching: true,

            driver_symbol_defs: Vec::new(),
        }
    }
}

pub fn assemble<S>(
    report: &mut diagn::Report,
    opts: &AssemblyOptions,
    fileserver: &mut dyn util::FileServer,
    root_filenames: &[S],
) -> AssemblyResult
where
    S: std::borrow::Borrow<str>,
{
    let mut assembly = AssemblyResult::new();

    let mut run = || -> Result<(), ()> {
        assembly.ast = Some(parser::parse_many_and_resolve_includes(
            report,
            fileserver,
            root_filenames,
        )?);

        assembly.decls = Some(decls::init(report)?);

        assembly.defs = Some(defs::init());

        let mut prev_resolved_constants_count = 0;

        loop {
            decls::collect(
                report,
                assembly.ast.as_mut().unwrap(),
                assembly.decls.as_mut().unwrap(),
            )?;

            defs::define_symbols(
                report,
                opts,
                assembly.ast.as_mut().unwrap(),
                assembly.decls.as_ref().unwrap(),
                assembly.defs.as_mut().unwrap(),
            )?;

            let resolved_constants_count = resolver::resolve_constants_simple(
                report,
                opts,
                fileserver,
                assembly.ast.as_ref().unwrap(),
                assembly.decls.as_ref().unwrap(),
                assembly.defs.as_mut().unwrap(),
            )?;

            let resolved_ifs_count = resolver::resolve_ifs(
                report,
                opts,
                fileserver,
                assembly.ast.as_mut().unwrap(),
                assembly.decls.as_ref().unwrap(),
                assembly.defs.as_mut().unwrap(),
            )?;

            if resolved_constants_count == prev_resolved_constants_count && resolved_ifs_count == 0
            {
                break;
            }

            prev_resolved_constants_count = resolved_constants_count;
        }

        resolver::check_leftover_ifs(
            report,
            assembly.ast.as_ref().unwrap(),
            assembly.decls.as_ref().unwrap(),
            assembly.defs.as_ref().unwrap(),
        )?;

        defs::define_remaining(
            report,
            opts,
            assembly.ast.as_mut().unwrap(),
            assembly.defs.as_mut().unwrap(),
            assembly.decls.as_mut().unwrap(),
        )?;

        matcher::match_all(
            report,
            opts,
            assembly.ast.as_ref().unwrap(),
            assembly.decls.as_ref().unwrap(),
            assembly.defs.as_mut().unwrap(),
        )?;

        assembly.iterations_taken = Some(resolver::resolve_iteratively(
            report,
            opts,
            fileserver,
            assembly.ast.as_ref().unwrap(),
            assembly.decls.as_ref().unwrap(),
            assembly.defs.as_mut().unwrap(),
            opts.max_iterations,
        )?);

        output::check_bank_overlap(
            report,
            assembly.decls.as_ref().unwrap(),
            assembly.defs.as_mut().unwrap(),
        )?;

        assembly.output = Some(output::build_output(
            report,
            assembly.ast.as_ref().unwrap(),
            assembly.decls.as_ref().unwrap(),
            assembly.defs.as_ref().unwrap(),
        )?);

        check_unused_defines(report, opts, assembly.decls.as_ref().unwrap())?;

        Ok(())
    };

    match run() {
        Ok(()) => {}
        Err(()) => {
            assembly.error = true;
            assert!(report.has_errors());
        }
    }

    assembly
}

fn check_unused_defines(
    report: &mut diagn::Report,
    opts: &asm::AssemblyOptions,
    decls: &asm::ItemDecls,
) -> Result<(), ()> {
    let mut had_error = false;

    for symbol_def in &opts.driver_symbol_defs {
        let hierarchy = symbol_def.name.split(".").collect::<Vec<_>>();

        let maybe_decl =
            decls
                .symbols
                .try_get_by_name(&util::SymbolContext::new_global(), 0, &hierarchy);

        if let None = maybe_decl {
            report.error(format!("unused define `{}`", symbol_def.name));

            had_error = true;
        }
    }

    match had_error {
        false => Ok(()),
        true => Err(()),
    }
}

pub enum NumberFormat {
    Hex,
    Dec,
    Bin,
}

pub fn parse_number_format(report: &mut diagn::Report, input: &str) -> Result<NumberFormat, ()> {
    match input {
        "hex" => Ok(NumberFormat::Hex),
        "dec" => Ok(NumberFormat::Dec),
        "bin" => Ok(NumberFormat::Bin),
        _ => {
            report.error(format!("unknown number format: {}", input));
            Err(())
        }
    }
}

fn check_rule_disassembly(
    report: &mut diagn::Report,
    number_format: &asm::NumberFormat,
    ruledefs: &asm::defs::DefList<asm::defs::Ruledef>,
    rule: &asm::Rule,
    index: &mut usize,
    parameters: &mut Vec<String>,
    bitvec: &util::BitVec,
    production: &expr::Expr,
) -> Result<bool, ()> {
    match production {
        expr::Expr::Literal(_, expr::Value::Integer(value)) => {
            for i in (0usize..value.size.ok_or_else(|| ())?).rev() {
                if value.get_bit(i) != bitvec.read_bit(*index) {
                    return Ok(false);
                }
                *index += 1;
            }
            Ok(true)
        }
        expr::Expr::Literal(span, _) => {
            report.error_span("unsupported literal.", *span);
            Err(())
        }
        expr::Expr::Variable(_, hierarchy_level, ref hierarchy)
            if *hierarchy_level == 0 && hierarchy.len() == 1 =>
        {
            let p = rule
                .parameters
                .iter()
                .position(|p| p.name == hierarchy[0])
                .ok_or(())?;
            match rule.parameters[p].typ {
                asm::RuleParameterType::Integer(size)
                | asm::RuleParameterType::Signed(size)
                | asm::RuleParameterType::Unsigned(size) => {
                    parameters[p] = match number_format {
                        NumberFormat::Hex => {
                            "0x".to_string()
                                + &bitvec
                                    .slice(*index, {
                                        *index += size;
                                        *index
                                    })
                                    .format_hexstr()
                        }
                        NumberFormat::Bin => {
                            let mut a = "".to_string();
                            for _ in 0..size {
                                a += if bitvec.read_bit(*index) { "1" } else { "0" };
                                *index += 1;
                            }
                            "0b".to_string() + &a
                        }
                        NumberFormat::Dec => {
                            *index += size;
                            let mut n: u32 = 0;
                            let mut a: u32 = 1;
                            for i in 1..(size + 1) {
                                n += if bitvec.read_bit(*index - i) { a } else { 0 };
                                a *= 2;
                            }
                            n.to_string()
                        }
                    };
                    Ok(true)
                }
                asm::RuleParameterType::RuledefRef(rs) => {
                    'outer: {
                        for r in ruledefs.get(rs).rules.iter() {
                            let mut i = *index;
                            let mut ps: Vec<String> = vec!["".to_string(); r.parameters.len()];
                            if check_rule_disassembly(
                                report,
                                number_format,
                                ruledefs,
                                &r,
                                &mut i,
                                &mut ps,
                                bitvec,
                                &r.expr,
                            )? {
                                // dbg!("{} {:?}", i, parameters);
                                let mut instruction = String::new();
                                for i in &r.pattern {
                                    match i {
                                        asm::RulePatternPart::Whitespace => instruction.push(' '),
                                        asm::RulePatternPart::Exact(c) => instruction.push(*c),
                                        asm::RulePatternPart::ParameterIndex(a) => {
                                            instruction += &ps[*a]
                                        }
                                    }
                                }
                                parameters[p] = instruction;
                                *index = i;
                                break 'outer;
                            }
                        }
                        return Ok(false);
                    }
                    Ok(true)
                }
                asm::RuleParameterType::Unspecified => {
                    report.error("specify all types on variables.");
                    Err(())
                }
            }
        }
        expr::Expr::Variable(span, _, _) => {
            report.error_span("unsupported binary pattern.", *span);
            Err(())
        }
        expr::Expr::UnaryOp(span, _, _, _) => {
            report.error_span("unsupported unary operator.", *span);
            Err(())
        }
        expr::Expr::BinaryOp(_, _, expr::BinaryOp::Concat, ref lhs, ref rhs) => {
            Ok(check_rule_disassembly(
                report,
                number_format,
                ruledefs,
                rule,
                index,
                parameters,
                bitvec,
                lhs,
            )? && check_rule_disassembly(
                report,
                number_format,
                ruledefs,
                rule,
                index,
                parameters,
                bitvec,
                rhs,
            )?)
        }
        expr::Expr::BinaryOp(span, _, _, _, _) => {
            report.error_span("unsupported binary operator.", *span);
            Err(())
        }
        expr::Expr::TernaryOp(span, _, _, _) => {
            report.error_span("unsupported ternary operator.", *span);
            Err(())
        }
        //? This seems wrong
        expr::Expr::Slice(span, slice_span, leftmost, rightmost, inner) => check_rule_disassembly(
            report,
            number_format,
            ruledefs,
            rule,
            index,
            parameters,
            bitvec,
            inner,
        ),
        expr::Expr::SliceShort(span, size_span, size, inner) => check_rule_disassembly(
            report,
            number_format,
            ruledefs,
            rule,
            index,
            parameters,
            bitvec,
            inner,
        ),
        expr::Expr::Block(_, exprs) => {
            for expr in exprs {
                if !check_rule_disassembly(
                    report,
                    number_format,
                    ruledefs,
                    rule,
                    index,
                    parameters,
                    bitvec,
                    &Box::new(expr.clone()),
                )? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        expr::Expr::Call(span, func, _) => match &**func {
            expr::Expr::Variable(_, 0, ref hierarchy) if matches!(hierarchy.as_slice(), [name] if name == "assert") => {
                Ok(true)
            }
            _ => {
                report.error_span("unsupported call.", *span);
                Err(())
            }
        },
        expr::Expr::Asm(span, _) => {
            report.note_span(
                "ignoring asm rule so output may be more verbose, but still functional.",
                *span,
            );
            Ok(false)
        }
    }
}

pub struct DisassemblyOutput {
    pub assembly: String,
}

pub fn disassemble(
    report: &mut diagn::Report,
    number_format: &asm::NumberFormat,
    ruledefs: &asm::defs::DefList<asm::defs::Ruledef>,
    bitvec: &util::BitVec,
) -> Result<DisassemblyOutput, ()> {
    report.warning("Disassembly is not stable, there may be issues and many features have not yet been implemented.");

    // dbg!(self.rulesets);
    // dbg!(self.active_rulesets);
    let mut assembly = "disassembled:\n".to_string();
    let mut g_index = 0usize;

    while g_index < bitvec.len() {
        'outer: {
            for rs_option in &ruledefs.defs {
                if let Some(rs) = rs_option {
                    if rs.is_subruledef {
                        continue;
                    }
                    for rule in &rs.rules {
                        let mut index = g_index;
                        let mut parameters: Vec<String> =
                            vec!["".to_string(); rule.parameters.len()];
                        if check_rule_disassembly(
                            report,
                            number_format,
                            ruledefs,
                            &rule,
                            &mut index,
                            &mut parameters,
                            bitvec,
                            &rule.expr,
                        )? {
                            // dbg!(index, parameters);
                            let mut instruction = String::new();
                            for i in &rule.pattern {
                                match i {
                                    asm::RulePatternPart::Whitespace => instruction.push(' '),
                                    asm::RulePatternPart::Exact(c) => instruction.push(*c),
                                    asm::RulePatternPart::ParameterIndex(p) => {
                                        instruction += &parameters[*p]
                                    }
                                }
                            }
                            // dbg!(index, instruction.clone());
                            assembly += "    ";
                            assembly += &instruction;
                            assembly += "\n";
                            g_index = index;
                            break 'outer;
                        }
                    }
                }
            }
            report.error("cannot disassemble instruction");
        }
    }
    Ok(DisassemblyOutput { assembly })
}
