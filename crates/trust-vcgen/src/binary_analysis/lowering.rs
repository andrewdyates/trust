// trust-vcgen/binary_analysis/lowering.rs: Shared lowering utilities
//
// Internal helpers shared by the binary lifter and CFG reconstruction layers.
//
// Part of #148: Binary analysis pipeline
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_types::*;

use super::cfg_reconstruct::{CfgEdge, EdgeKind, ReconstructedCfg};
use super::lifter::{AbstractInsn, AbstractOp, AbstractRegister, AbstractValue, MemoryAccess};

#[derive(Debug, Clone)]
pub(crate) struct LoweringContext {
    register_info: BTreeMap<u16, AbstractRegister>,
    register_locals: BTreeMap<u16, usize>,
    value_formula_locals: BTreeMap<String, usize>,
    value_formula_info: BTreeMap<String, FormulaInfo>,
    address_formula_locals: BTreeMap<String, usize>,
    address_formula_info: BTreeMap<String, AddressInfo>,
    max_local: usize,
}

#[derive(Debug, Clone)]
struct FormulaInfo {
    formula: Formula,
    ty: Ty,
}

#[derive(Debug, Clone)]
struct AddressInfo {
    formula: Formula,
    size_bits: u32,
    mutable: bool,
}

#[cfg(test)]
#[must_use]
pub(crate) fn synthetic_registers(cfg: &ReconstructedCfg) -> Vec<AbstractRegister> {
    collect_register_ids(cfg)
        .into_iter()
        .map(|id| AbstractRegister { id, name: format!("r{id}"), width: 64 })
        .collect()
}

#[must_use]
pub(crate) fn collect_register_ids(cfg: &ReconstructedCfg) -> BTreeSet<u16> {
    let mut registers = BTreeSet::new();

    for node in &cfg.nodes {
        for insn in &node.instructions {
            for register in registers_in_instruction(insn) {
                registers.insert(register);
            }
        }
    }

    registers
}

#[must_use]
pub(crate) fn build_lowering_context(
    cfg: &ReconstructedCfg,
    registers: &[AbstractRegister],
) -> LoweringContext {
    let register_info = registers.iter().cloned().map(|register| (register.id, register)).collect();
    let max_register_local =
        registers.iter().map(|register| usize::from(register.id) + 1).max().unwrap_or(0);

    let register_locals =
        registers.iter().map(|register| (register.id, usize::from(register.id) + 1)).collect();

    let value_formula_info = collect_value_formulas(cfg);
    let address_formula_info = collect_address_formulas(cfg);

    let mut next_local = max_register_local + 1;
    let mut value_formula_locals = BTreeMap::new();
    for key in value_formula_info.keys() {
        value_formula_locals.insert(key.clone(), next_local);
        next_local += 1;
    }

    let mut address_formula_locals = BTreeMap::new();
    for key in address_formula_info.keys() {
        address_formula_locals.insert(key.clone(), next_local);
        next_local += 1;
    }

    LoweringContext {
        register_info,
        register_locals,
        value_formula_locals,
        value_formula_info,
        address_formula_locals,
        address_formula_info,
        max_local: next_local.saturating_sub(1),
    }
}

#[must_use]
pub(crate) fn build_locals(return_ty: Ty, context: &LoweringContext) -> Vec<LocalDecl> {
    let mut locals: Vec<LocalDecl> = (0..=context.max_local)
        .map(|index| LocalDecl { index, ty: Ty::Unit, name: None })
        .collect();

    if locals.is_empty() {
        locals.push(LocalDecl { index: 0, ty: return_ty.clone(), name: None });
    }

    locals[0] = LocalDecl { index: 0, ty: return_ty, name: None };

    for (id, register) in &context.register_info {
        let index = context.local_for_register(*id);
        locals[index] = LocalDecl {
            index,
            ty: ty_for_register_width(register.width),
            name: Some(register.name.clone()),
        };
    }

    for (ordinal, (key, info)) in context.value_formula_info.iter().enumerate() {
        let index = context.local_for_value_formula(key);
        locals[index] = LocalDecl {
            index,
            ty: info.ty.clone(),
            name: Some(symbolic_name("sym_value", &info.formula, ordinal)),
        };
    }

    for (ordinal, (key, info)) in context.address_formula_info.iter().enumerate() {
        let index = context.local_for_address_formula(key);
        locals[index] = LocalDecl {
            index,
            ty: Ty::Ref {
                mutable: info.mutable,
                inner: Box::new(Ty::Int { width: info.size_bits.max(8), signed: false }),
            },
            name: Some(symbolic_name("sym_addr", &info.formula, ordinal)),
        };
    }

    locals
}

#[must_use]
pub(crate) fn lower_cfg_to_blocks(
    cfg: &ReconstructedCfg,
    context: &LoweringContext,
) -> Vec<BasicBlock> {
    let address_to_block: BTreeMap<u64, BlockId> =
        cfg.nodes.iter().map(|node| (node.address, node.block_id)).collect();
    let edge_map = build_edge_map(&cfg.edges);

    cfg.nodes
        .iter()
        .map(|node| {
            let mut stmts = Vec::new();
            let mut terminator = None;

            for insn in &node.instructions {
                if let Some(new_terminator) =
                    lower_instruction(insn, &mut stmts, context, &address_to_block)
                {
                    terminator = Some(new_terminator);
                    break;
                }
            }

            let terminator = terminator.unwrap_or_else(|| {
                fallthrough_terminator(node.address, &edge_map, &address_to_block)
            });

            BasicBlock { id: node.block_id, stmts, terminator }
        })
        .collect()
}

impl LoweringContext {
    pub(crate) fn local_for_register(&self, id: u16) -> usize {
        self.register_locals.get(&id).copied().unwrap_or_else(|| usize::from(id) + 1)
    }

    fn local_for_value_formula(&self, key: &str) -> usize {
        self.value_formula_locals.get(key).copied().unwrap_or_default()
    }

    fn local_for_address_formula(&self, key: &str) -> usize {
        self.address_formula_locals.get(key).copied().unwrap_or_default()
    }
}

fn lower_instruction(
    insn: &AbstractInsn,
    stmts: &mut Vec<Statement>,
    context: &LoweringContext,
    address_to_block: &BTreeMap<u64, BlockId>,
) -> Option<Terminator> {
    match &insn.op {
        AbstractOp::Load { dst, access: MemoryAccess::Read { addr, .. } } => {
            stmts.push(Statement::Assign {
                place: Place::local(context.local_for_register(*dst)),
                rvalue: Rvalue::Use(Operand::Copy(address_place(addr, context))),
                span: SourceSpan::default(),
            });
            None
        }
        AbstractOp::Load { .. } => {
            stmts.push(Statement::Nop);
            None
        }
        AbstractOp::Store { access: MemoryAccess::Write { addr, value, .. } } => {
            stmts.push(Statement::Assign {
                place: address_place(addr, context),
                rvalue: Rvalue::Use(formula_to_operand(value, context)),
                span: SourceSpan::default(),
            });
            None
        }
        AbstractOp::Store { .. } => {
            stmts.push(Statement::Nop);
            None
        }
        AbstractOp::BinArith { dst, op, lhs, rhs } => {
            stmts.push(Statement::Assign {
                place: Place::local(context.local_for_register(*dst)),
                rvalue: Rvalue::BinaryOp(
                    *op,
                    abstract_value_to_operand(lhs, context),
                    abstract_value_to_operand(rhs, context),
                ),
                span: SourceSpan::default(),
            });
            None
        }
        AbstractOp::UnaryOp { dst, op, operand } => {
            stmts.push(Statement::Assign {
                place: Place::local(context.local_for_register(*dst)),
                rvalue: Rvalue::UnaryOp(*op, abstract_value_to_operand(operand, context)),
                span: SourceSpan::default(),
            });
            None
        }
        AbstractOp::Assign { dst, src } => {
            stmts.push(Statement::Assign {
                place: Place::local(context.local_for_register(*dst)),
                rvalue: Rvalue::Use(abstract_value_to_operand(src, context)),
                span: SourceSpan::default(),
            });
            None
        }
        AbstractOp::Compare { dst, op, lhs, rhs } => {
            stmts.push(Statement::Assign {
                place: Place::local(context.local_for_register(*dst)),
                rvalue: Rvalue::BinaryOp(
                    *op,
                    abstract_value_to_operand(lhs, context),
                    abstract_value_to_operand(rhs, context),
                ),
                span: SourceSpan::default(),
            });
            None
        }
        AbstractOp::IndirectBranch { .. } => {
            // Conservative: indirect branches terminate as unreachable
            Some(Terminator::Unreachable)
        }
        AbstractOp::Branch { target } => Some(
            address_to_block
                .get(target)
                .copied()
                .map(Terminator::Goto)
                .unwrap_or(Terminator::Unreachable),
        ),
        AbstractOp::CondBranch { cond, true_target, false_target } => Some(
            match (
                address_to_block.get(true_target).copied(),
                address_to_block.get(false_target).copied(),
            ) {
                (Some(true_block), Some(false_block)) => Terminator::SwitchInt {
                    discr: abstract_value_to_operand(cond, context),
                    targets: vec![(1, true_block)],
                    otherwise: false_block,
                    span: SourceSpan::default(),
                },
                _ => Terminator::Unreachable,
            },
        ),
        AbstractOp::Call { func, args, dest, next } => Some(Terminator::Call {
            func: func.clone(),
            args: args.iter().map(|arg| abstract_value_to_operand(arg, context)).collect(),
            dest: Place::local(dest.map_or(0, |register| context.local_for_register(register))),
            target: next.and_then(|address| address_to_block.get(&address).copied()),
            span: SourceSpan::default(),
            atomic: None,
        }),
        AbstractOp::Return { value } => {
            if let Some(value) = value {
                stmts.push(Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(abstract_value_to_operand(value, context)),
                    span: SourceSpan::default(),
                });
            }
            Some(Terminator::Return)
        }
        AbstractOp::Nop => {
            stmts.push(Statement::Nop);
            None
        }
    }
}

fn fallthrough_terminator(
    node_address: u64,
    edge_map: &BTreeMap<u64, Vec<&CfgEdge>>,
    address_to_block: &BTreeMap<u64, BlockId>,
) -> Terminator {
    let target = edge_map.get(&node_address).and_then(|edges| {
        edges.iter().find_map(|edge| {
            matches!(edge.kind, EdgeKind::Fallthrough)
                .then(|| address_to_block.get(&edge.to).copied())
                .flatten()
        })
    });

    target.map(Terminator::Goto).unwrap_or(Terminator::Return)
}

fn build_edge_map(edges: &[CfgEdge]) -> BTreeMap<u64, Vec<&CfgEdge>> {
    let mut edge_map: BTreeMap<u64, Vec<&CfgEdge>> = BTreeMap::new();
    for edge in edges {
        edge_map.entry(edge.from).or_default().push(edge);
    }
    edge_map
}

fn address_place(addr: &Formula, context: &LoweringContext) -> Place {
    Place {
        local: context.local_for_address_formula(&formula_key(addr)),
        projections: vec![Projection::Deref],
    }
}

fn abstract_value_to_operand(value: &AbstractValue, context: &LoweringContext) -> Operand {
    match value {
        AbstractValue::Register(id) => Operand::Copy(Place::local(context.local_for_register(*id))),
        AbstractValue::Formula(formula) => formula_to_operand(formula, context),
    }
}

fn formula_to_operand(formula: &Formula, context: &LoweringContext) -> Operand {
    formula_to_constant(formula).map_or_else(
        || Operand::Copy(Place::local(context.local_for_value_formula(&formula_key(formula)))),
        Operand::Constant,
    )
}

fn formula_to_constant(formula: &Formula) -> Option<ConstValue> {
    match formula {
        Formula::Bool(value) => Some(ConstValue::Bool(*value)),
        Formula::Int(value) => Some(ConstValue::Int(*value)),
        Formula::BitVec { value, .. } if *value >= 0 => Some(ConstValue::Uint(*value as u128, 64)),
        Formula::BitVec { value, .. } => Some(ConstValue::Int(*value)),
        _ => None,
    }
}

fn collect_value_formulas(cfg: &ReconstructedCfg) -> BTreeMap<String, FormulaInfo> {
    let mut formulas = BTreeMap::new();

    for node in &cfg.nodes {
        for insn in &node.instructions {
            match &insn.op {
                AbstractOp::BinArith { lhs, rhs, .. } | AbstractOp::Compare { lhs, rhs, .. } => {
                    collect_abstract_value_formula(lhs, &mut formulas);
                    collect_abstract_value_formula(rhs, &mut formulas);
                }
                AbstractOp::UnaryOp { operand, .. }
                | AbstractOp::CondBranch { cond: operand, .. } => {
                    collect_abstract_value_formula(operand, &mut formulas);
                }
                AbstractOp::Assign { src, .. } => {
                    collect_abstract_value_formula(src, &mut formulas);
                }
                AbstractOp::IndirectBranch { target } => {
                    collect_abstract_value_formula(target, &mut formulas);
                }
                AbstractOp::Call { args, .. } => {
                    for arg in args {
                        collect_abstract_value_formula(arg, &mut formulas);
                    }
                }
                AbstractOp::Return { value } => {
                    if let Some(value) = value {
                        collect_abstract_value_formula(value, &mut formulas);
                    }
                }
                AbstractOp::Store { access: MemoryAccess::Write { value, .. } } => {
                    let key = formula_key(value);
                    formulas.entry(key).or_insert_with(|| FormulaInfo {
                        formula: value.clone(),
                        ty: infer_formula_ty(value),
                    });
                }
                AbstractOp::Load { .. } | AbstractOp::Branch { .. } | AbstractOp::Nop => {}
                AbstractOp::Store { .. } => {}
            }
        }
    }

    formulas
}

fn collect_address_formulas(cfg: &ReconstructedCfg) -> BTreeMap<String, AddressInfo> {
    let mut formulas = BTreeMap::new();

    for node in &cfg.nodes {
        for insn in &node.instructions {
            match &insn.op {
                AbstractOp::Load { access: MemoryAccess::Read { addr, size }, .. } => {
                    merge_address_formula(&mut formulas, addr, *size, false);
                }
                AbstractOp::Store { access: MemoryAccess::Write { addr, size, .. } } => {
                    merge_address_formula(&mut formulas, addr, *size, true);
                }
                _ => {}
            }
        }
    }

    formulas
}

fn merge_address_formula(
    formulas: &mut BTreeMap<String, AddressInfo>,
    formula: &Formula,
    size: u32,
    mutable: bool,
) {
    let key = formula_key(formula);
    let size_bits = size.saturating_mul(8).max(8);

    formulas
        .entry(key)
        .and_modify(|info| {
            info.size_bits = info.size_bits.max(size_bits);
            info.mutable |= mutable;
        })
        .or_insert_with(|| AddressInfo { formula: formula.clone(), size_bits, mutable });
}

fn collect_abstract_value_formula(
    value: &AbstractValue,
    formulas: &mut BTreeMap<String, FormulaInfo>,
) {
    if let AbstractValue::Formula(formula) = value {
        let key = formula_key(formula);
        formulas.entry(key).or_insert_with(|| FormulaInfo {
            formula: formula.clone(),
            ty: infer_formula_ty(formula),
        });
    }
}

fn registers_in_instruction(insn: &AbstractInsn) -> Vec<u16> {
    let mut registers = Vec::new();

    match &insn.op {
        AbstractOp::Load { dst, .. } => registers.push(*dst),
        AbstractOp::Store { .. } | AbstractOp::Branch { .. } | AbstractOp::Nop => {}
        AbstractOp::BinArith { dst, lhs, rhs, .. } | AbstractOp::Compare { dst, lhs, rhs, .. } => {
            registers.push(*dst);
            collect_abstract_value_registers(lhs, &mut registers);
            collect_abstract_value_registers(rhs, &mut registers);
        }
        AbstractOp::UnaryOp { dst, operand, .. } => {
            registers.push(*dst);
            collect_abstract_value_registers(operand, &mut registers);
        }
        AbstractOp::Assign { dst, src } => {
            registers.push(*dst);
            collect_abstract_value_registers(src, &mut registers);
        }
        AbstractOp::CondBranch { cond, .. } => {
            collect_abstract_value_registers(cond, &mut registers);
        }
        AbstractOp::IndirectBranch { target } => {
            collect_abstract_value_registers(target, &mut registers);
        }
        AbstractOp::Call { args, dest, .. } => {
            if let Some(dest) = dest {
                registers.push(*dest);
            }
            for arg in args {
                collect_abstract_value_registers(arg, &mut registers);
            }
        }
        AbstractOp::Return { value } => {
            if let Some(value) = value {
                collect_abstract_value_registers(value, &mut registers);
            }
        }
    }

    registers
}

fn collect_abstract_value_registers(value: &AbstractValue, registers: &mut Vec<u16>) {
    if let AbstractValue::Register(id) = value {
        registers.push(*id);
    }
}

#[must_use]
pub(crate) fn infer_formula_ty(formula: &Formula) -> Ty {
    match formula {
        Formula::Bool(_)
        | Formula::Not(_)
        | Formula::And(_)
        | Formula::Or(_)
        | Formula::Implies(_, _)
        | Formula::Eq(_, _)
        | Formula::Lt(_, _)
        | Formula::Le(_, _)
        | Formula::Gt(_, _)
        | Formula::Ge(_, _)
        | Formula::BvULt(_, _, _)
        | Formula::BvULe(_, _, _)
        | Formula::BvSLt(_, _, _)
        | Formula::BvSLe(_, _, _)
        | Formula::Forall(_, _)
        | Formula::Exists(_, _) => Ty::Bool,
        Formula::Int(_)
        | Formula::UInt(_)
        | Formula::Add(_, _)
        | Formula::Sub(_, _)
        | Formula::Mul(_, _)
        | Formula::Div(_, _)
        | Formula::Rem(_, _)
        | Formula::Neg(_)
        | Formula::BvToInt(_, _, _) => Ty::isize(),
        Formula::BitVec { width, .. }
        | Formula::BvAdd(_, _, width)
        | Formula::BvSub(_, _, width)
        | Formula::BvMul(_, _, width)
        | Formula::BvUDiv(_, _, width)
        | Formula::BvSDiv(_, _, width)
        | Formula::BvURem(_, _, width)
        | Formula::BvSRem(_, _, width)
        | Formula::BvAnd(_, _, width)
        | Formula::BvOr(_, _, width)
        | Formula::BvXor(_, _, width)
        | Formula::BvNot(_, width)
        | Formula::BvShl(_, _, width)
        | Formula::BvLShr(_, _, width)
        | Formula::BvAShr(_, _, width)
        | Formula::IntToBv(_, width) => Ty::Int { width: *width, signed: false },
        Formula::BvExtract { high, low, .. } => {
            Ty::Int { width: high.saturating_sub(*low) + 1, signed: false }
        }
        Formula::BvConcat(lhs, rhs) => {
            let lhs_width = infer_formula_ty(lhs).int_width().unwrap_or(64);
            let rhs_width = infer_formula_ty(rhs).int_width().unwrap_or(64);
            Ty::Int { width: lhs_width.saturating_add(rhs_width), signed: false }
        }
        Formula::BvZeroExt(inner, extra) | Formula::BvSignExt(inner, extra) => Ty::Int {
            width: infer_formula_ty(inner).int_width().unwrap_or(64).saturating_add(*extra),
            signed: false,
        },
        Formula::Var(_, sort) => ty_for_sort(sort),
        Formula::Ite(_, then_branch, _) => infer_formula_ty(then_branch),
        Formula::Select(_, _) => Ty::isize(),
        Formula::Store(_, _, _) => {
            Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 8, signed: false }) }
        }
        _ => Ty::Unit,
    }
}

#[must_use]
pub(crate) fn ty_for_register_width(width: u32) -> Ty {
    match width {
        0 => Ty::Unit,
        1 => Ty::Bool,
        width => Ty::Int { width, signed: false },
    }
}

fn ty_for_sort(sort: &Sort) -> Ty {
    match sort {
        Sort::Bool => Ty::Bool,
        Sort::Int => Ty::isize(),
        Sort::BitVec(width) => Ty::Int { width: *width, signed: false },
        Sort::Array(_, _) => {
            Ty::Ref { mutable: true, inner: Box::new(Ty::Int { width: 8, signed: false }) }
        }
        _ => Ty::Unit,
    }
}

fn formula_key(formula: &Formula) -> String {
    serde_json::to_string(formula).unwrap_or_else(|_| format!("{formula:?}"))
}

fn symbolic_name(prefix: &str, formula: &Formula, ordinal: usize) -> String {
    let base = match formula {
        Formula::Var(name, _) => sanitize_name(name),
        _ => ordinal.to_string(),
    };
    format!("{prefix}_{base}")
}

fn sanitize_name(name: &str) -> String {
    let sanitized: String = name
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() || ch == '_' { ch } else { '_' })
        .collect();

    if sanitized.is_empty() { "sym".to_string() } else { sanitized }
}
