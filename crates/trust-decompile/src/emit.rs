// trust-decompile: Stage 1 raw emission — MIR to syntactically valid unsafe Rust
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AggregateKind, BinOp, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, Statement,
    Terminator, Ty, UnOp, VerifiableFunction,
};

use crate::error::DecompileError;

/// Convert a `Ty` to its Rust source representation.
pub(crate) fn ty_to_rust(ty: &Ty) -> String {
    match ty {
        Ty::Bool => "bool".to_string(),
        Ty::Int { width: 8, signed: true } => "i8".to_string(),
        Ty::Int { width: 8, signed: false } => "u8".to_string(),
        Ty::Int { width: 16, signed: true } => "i16".to_string(),
        Ty::Int { width: 16, signed: false } => "u16".to_string(),
        Ty::Int { width: 32, signed: true } => "i32".to_string(),
        Ty::Int { width: 32, signed: false } => "u32".to_string(),
        Ty::Int { width: 64, signed: true } => "i64".to_string(),
        Ty::Int { width: 64, signed: false } => "u64".to_string(),
        Ty::Int { width: 128, signed: true } => "i128".to_string(),
        Ty::Int { width: 128, signed: false } => "u128".to_string(),
        Ty::Int { width, signed } => {
            let prefix = if *signed { "i" } else { "u" };
            format!("{prefix}{width}")
        }
        Ty::Float { width: 32 } => "f32".to_string(),
        Ty::Float { width: 64 } => "f64".to_string(),
        Ty::Float { width } => format!("f{width}"),
        Ty::Ref { mutable: true, inner } => format!("&mut {}", ty_to_rust(inner)),
        Ty::Ref { mutable: false, inner } => format!("&{}", ty_to_rust(inner)),
        Ty::RawPtr { mutable: true, pointee } => format!("*mut {}", ty_to_rust(pointee)),
        Ty::RawPtr { mutable: false, pointee } => format!("*const {}", ty_to_rust(pointee)),
        Ty::Slice { elem } => format!("[{}]", ty_to_rust(elem)),
        Ty::Array { elem, len } => format!("[{}; {len}]", ty_to_rust(elem)),
        Ty::Tuple(elems) if elems.is_empty() => "()".to_string(),
        Ty::Tuple(elems) => {
            let inner: Vec<String> = elems.iter().map(ty_to_rust).collect();
            format!("({})", inner.join(", "))
        }
        Ty::Adt { name, .. } => name.clone(),
        Ty::Unit => "()".to_string(),
        Ty::Never => "!".to_string(),
        // Wildcard for non_exhaustive — fall back to a comment
        _ => "/* unknown type */".to_string(),
    }
}

/// Format a local variable name. `_0` is the return place.
fn local_name(decl: &LocalDecl) -> String {
    match &decl.name {
        Some(name) => name.to_string(),
        None => format!("_{}", decl.index),
    }
}

/// Format a place expression (local + projections).
pub(crate) fn place_to_rust(place: &Place, locals: &[LocalDecl]) -> String {
    let base = locals
        .get(place.local)
        .map(local_name)
        .unwrap_or_else(|| format!("_{}", place.local));

    let mut expr = base;
    for proj in &place.projections {
        match proj {
            Projection::Field(idx) => expr = format!("{expr}.{idx}"),
            Projection::Index(idx) => expr = format!("{expr}[_{idx}]"),
            Projection::Deref => expr = format!("(*{expr})"),
            Projection::Downcast(variant) => expr = format!("{expr} /* variant {variant} */"),
            Projection::ConstantIndex { offset, from_end } => {
                if *from_end {
                    expr = format!("{expr}[{expr}.len() - {offset}]");
                } else {
                    expr = format!("{expr}[{offset}]");
                }
            }
            Projection::Subslice { from, to, from_end } => {
                if *from_end {
                    expr = format!("{expr}[{from}..{expr}.len() - {to}]");
                } else {
                    expr = format!("{expr}[{from}..{to}]");
                }
            }
            // Wildcard for non_exhaustive
            _ => expr = format!("{expr} /* unknown projection */"),
        }
    }
    expr
}

/// Format an operand expression.
pub(crate) fn operand_to_rust(op: &Operand, locals: &[LocalDecl]) -> String {
    match op {
        Operand::Copy(place) | Operand::Move(place) => place_to_rust(place, locals),
        Operand::Constant(val) => const_to_rust(val),
        // Wildcard for non_exhaustive
        _ => "/* unknown operand */".to_string(),
    }
}

/// Format a constant value.
fn const_to_rust(val: &ConstValue) -> String {
    match val {
        ConstValue::Bool(b) => format!("{b}"),
        ConstValue::Int(n) => format!("{n}"),
        ConstValue::Uint(n, width) => {
            let suffix = match width {
                8 => "u8",
                16 => "u16",
                32 => "u32",
                64 => "u64",
                128 => "u128",
                _ => "",
            };
            format!("{n}{suffix}")
        }
        ConstValue::Float(f) => format!("{f:?}"),
        ConstValue::Unit => "()".to_string(),
        // Wildcard for non_exhaustive
        _ => "/* unknown const */".to_string(),
    }
}

/// Format a binary operator.
fn binop_to_rust(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Cmp => "/* cmp */",
        // Wildcard for non_exhaustive
        _ => "/* unknown op */",
    }
}

/// Format an rvalue expression.
pub(crate) fn rvalue_to_rust(rv: &Rvalue, locals: &[LocalDecl]) -> String {
    match rv {
        Rvalue::Use(op) => operand_to_rust(op, locals),
        Rvalue::BinaryOp(op, lhs, rhs) => {
            let l = operand_to_rust(lhs, locals);
            let r = operand_to_rust(rhs, locals);
            if matches!(op, BinOp::Cmp) {
                format!("{l}.cmp(&{r})")
            } else {
                format!("({l} {} {r})", binop_to_rust(op))
            }
        }
        Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
            let l = operand_to_rust(lhs, locals);
            let r = operand_to_rust(rhs, locals);
            let method = match op {
                BinOp::Add => "checked_add",
                BinOp::Sub => "checked_sub",
                BinOp::Mul => "checked_mul",
                BinOp::Shl => "checked_shl",
                BinOp::Shr => "checked_shr",
                _ => "/* checked_unknown */",
            };
            // MIR checked ops return (result, overflow_flag) tuple
            format!("{{ let r = {l}.{method}({r}); (r.unwrap_or(0), r.is_none()) }}")
        }
        Rvalue::UnaryOp(op, operand) => {
            let inner = operand_to_rust(operand, locals);
            match op {
                UnOp::Not => format!("(!{inner})"),
                UnOp::Neg => format!("(-{inner})"),
                UnOp::PtrMetadata => "/* ptr_metadata */ 0usize".to_string(),
                _ => format!("/* unknown unary */ {inner}"),
            }
        }
        Rvalue::Ref { mutable, place } => {
            let p = place_to_rust(place, locals);
            if *mutable {
                format!("&mut {p}")
            } else {
                format!("&{p}")
            }
        }
        Rvalue::Cast(op, ty) => {
            let inner = operand_to_rust(op, locals);
            let target = ty_to_rust(ty);
            format!("({inner} as {target})")
        }
        Rvalue::Aggregate(kind, operands) => {
            let fields: Vec<String> = operands.iter().map(|o| operand_to_rust(o, locals)).collect();
            match kind {
                AggregateKind::Tuple => format!("({})", fields.join(", ")),
                AggregateKind::Array => format!("[{}]", fields.join(", ")),
                AggregateKind::Adt { name, variant } => {
                    format!("{name}::variant_{variant}({})", fields.join(", "))
                }
                _ => "/* unknown aggregate */".to_string(),
            }
        }
        Rvalue::Discriminant(place) => {
            let p = place_to_rust(place, locals);
            format!("std::mem::discriminant(&{p})")
        }
        Rvalue::Len(place) => {
            let p = place_to_rust(place, locals);
            format!("{p}.len()")
        }
        Rvalue::Repeat(op, count) => {
            let inner = operand_to_rust(op, locals);
            format!("[{inner}; {count}]")
        }
        Rvalue::AddressOf(mutable, place) => {
            let p = place_to_rust(place, locals);
            if *mutable {
                format!("&raw mut {p}")
            } else {
                format!("&raw const {p}")
            }
        }
        Rvalue::CopyForDeref(place) => place_to_rust(place, locals),
        // Wildcard for non_exhaustive
        _ => "/* unknown rvalue */".to_string(),
    }
}

/// Format a statement as a Rust line.
pub(crate) fn stmt_to_rust(stmt: &Statement, locals: &[LocalDecl]) -> String {
    match stmt {
        Statement::Assign { place, rvalue, .. } => {
            let lhs = place_to_rust(place, locals);
            let rhs = rvalue_to_rust(rvalue, locals);
            format!("{lhs} = {rhs};")
        }
        Statement::Nop => "/* nop */".to_string(),
        // Wildcard for non_exhaustive
        _ => "/* unknown statement */".to_string(),
    }
}

/// Format a terminator as Rust code (may produce multiple lines).
pub(crate) fn terminator_to_rust(
    term: &Terminator,
    locals: &[LocalDecl],
    block_id: usize,
) -> Vec<String> {
    match term {
        Terminator::Goto(target) => {
            vec![format!("// goto bb{}", target.0)]
        }
        Terminator::SwitchInt { discr, targets, otherwise, .. } => {
            let d = operand_to_rust(discr, locals);
            let mut lines = vec![format!("match {d} {{")];
            for (value, target) in targets {
                lines.push(format!("    {value} => {{ /* bb{} */ }}", target.0));
            }
            lines.push(format!("    _ => {{ /* bb{} */ }}", otherwise.0));
            lines.push("}".to_string());
            lines
        }
        Terminator::Return => vec!["return _0;".to_string()],
        Terminator::Call { func, args, dest, target, .. } => {
            let arg_strs: Vec<String> = args.iter().map(|a| operand_to_rust(a, locals)).collect();
            let lhs = place_to_rust(dest, locals);
            let mut lines =
                vec![format!("{lhs} = {func}({});", arg_strs.join(", "))];
            if let Some(t) = target {
                lines.push(format!("// -> bb{}", t.0));
            }
            lines
        }
        Terminator::Assert { cond, expected, msg, target, .. } => {
            let c = operand_to_rust(cond, locals);
            let assertion = if *expected {
                format!("assert!({c});")
            } else {
                format!("assert!(!{c});")
            };
            vec![
                format!("// assert ({msg:?})"),
                assertion,
                format!("// -> bb{}", target.0),
            ]
        }
        Terminator::Drop { place, target, .. } => {
            let p = place_to_rust(place, locals);
            vec![
                format!("drop({p});"),
                format!("// -> bb{}", target.0),
            ]
        }
        Terminator::Unreachable => vec!["unreachable!();".to_string()],
        // Wildcard for non_exhaustive
        _ => vec![format!("/* unknown terminator in bb{block_id} */")],
    }
}

/// Emit a complete function as raw unsafe Rust.
///
/// This is Stage 1: produces syntactically valid Rust that may be ugly
/// but is structurally correct.
pub(crate) fn emit_raw(func: &VerifiableFunction) -> Result<String, DecompileError> {
    let body = &func.body;
    if body.blocks.is_empty() {
        return Err(DecompileError::EmptyBody);
    }

    let mut lines = Vec::new();

    // Function signature
    let ret_ty = ty_to_rust(&body.return_ty);
    let params: Vec<String> = body
        .locals
        .iter()
        .skip(1) // skip _0 (return place)
        .take(body.arg_count)
        .map(|decl| format!("{}: {}", local_name(decl), ty_to_rust(&decl.ty)))
        .collect();

    let fn_name = func.name.split("::").last().unwrap_or(&func.name);
    if ret_ty == "()" {
        lines.push(format!("unsafe fn {fn_name}({}) {{", params.join(", ")));
    } else {
        lines.push(format!(
            "unsafe fn {fn_name}({}) -> {ret_ty} {{",
            params.join(", ")
        ));
    }

    // Local variable declarations (skip _0 return place and args)
    let local_start = 1 + body.arg_count;
    for decl in body.locals.iter().skip(local_start) {
        let name = local_name(decl);
        let ty = ty_to_rust(&decl.ty);
        lines.push(format!("    let mut {name}: {ty};"));
    }

    // Return place declaration
    if ret_ty != "()" {
        lines.push(format!("    let mut _0: {ret_ty};"));
    }

    lines.push(String::new());

    // Basic blocks as labeled code sections
    for bb in &body.blocks {
        lines.push(format!("    // bb{}:", bb.id.0));

        for stmt in &bb.stmts {
            lines.push(format!("    {}", stmt_to_rust(stmt, &body.locals)));
        }

        for line in terminator_to_rust(&bb.terminator, &body.locals, bb.id.0) {
            lines.push(format!("    {line}"));
        }

        lines.push(String::new());
    }

    lines.push("}".to_string());

    Ok(lines.join("\n"))
}
