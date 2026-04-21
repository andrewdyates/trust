// trust-temporal/extract.rs: State machine extraction from MIR enum+match patterns
//
// Walks a VerifiableBody looking for the canonical enum-based state machine
// pattern: read discriminant -> SwitchInt -> assign new variant to same local.
// Produces a StateMachine that the checker and TLA2 backends can consume.
//
// Author: Andrew Yates <andrew@andrewdyates.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_types::*;

use crate::{State, StateId, StateMachine, StateMachineBuilder, Transition};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DiscriminantRead {
    pub discr_local: usize,
    pub place: Place,
    pub block: BlockId,
}

#[must_use]
pub(crate) fn find_discriminant_reads(body: &VerifiableBody) -> Vec<DiscriminantRead> {
    let mut reads = Vec::new();

    for block in &body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else {
                continue;
            };
            let Rvalue::Discriminant(source_place) = rvalue else {
                continue;
            };

            if place.projections.is_empty() {
                reads.push(DiscriminantRead {
                    discr_local: place.local,
                    place: source_place.clone(),
                    block: block.id,
                });
            }
        }
    }

    reads
}

#[must_use]
pub(crate) fn extract_state_machine(body: &VerifiableBody, enum_name: &str) -> Option<StateMachine> {
    let reads = find_discriminant_reads(body);
    let mut states = BTreeMap::new();
    let mut transitions = BTreeSet::new();

    states.insert(0usize, state_name(enum_name, 0));

    for block in &body.blocks {
        let Terminator::SwitchInt { discr, targets, .. } = &block.terminator else {
            continue;
        };
        let Some(discr_local) = operand_local(discr) else {
            continue;
        };

        for read in matching_reads(&reads, block.id, discr_local) {
            if enum_name_for_place(body, &read.place) != Some(enum_name) {
                continue;
            }

            for (from_variant, target_block) in targets {
                let Ok(from_variant) = usize::try_from(*from_variant) else {
                    continue;
                };
                states.entry(from_variant).or_insert_with(|| state_name(enum_name, from_variant));

                let Some(target_block) = block_by_id(body, *target_block) else {
                    continue;
                };

                for stmt in &target_block.stmts {
                    let Some((name, to_variant)) = aggregate_assignment(stmt, &read.place) else {
                        continue;
                    };
                    if name != enum_name {
                        continue;
                    }

                    states.entry(to_variant).or_insert_with(|| state_name(name, to_variant));
                    transitions.insert((from_variant, to_variant));
                }
            }
        }
    }

    if transitions.is_empty() {
        return None;
    }

    let mut builder = StateMachineBuilder::new(StateId(0));
    for (id, name) in states {
        builder.push_state(State::new(StateId(id), name));
    }
    for (from, to) in transitions {
        builder.push_transition(Transition::new(
            StateId(from),
            StateId(to),
            format!("variant_{from}_to_variant_{to}"),
        ));
    }

    Some(builder.build())
}

#[must_use]
pub(crate) fn extract_state_machines(body: &VerifiableBody) -> Vec<StateMachine> {
    let mut enum_names = Vec::new();

    for read in find_discriminant_reads(body) {
        let Some(enum_name) = enum_name_for_place(body, &read.place) else {
            continue;
        };
        if !enum_names.iter().any(|existing| existing == enum_name) {
            enum_names.push(enum_name.to_string());
        }
    }

    enum_names.into_iter().filter_map(|enum_name| extract_state_machine(body, &enum_name)).collect()
}

#[must_use]
fn enum_name_for_place<'a>(body: &'a VerifiableBody, place: &Place) -> Option<&'a str> {
    let decl = body.locals.iter().find(|decl| decl.index == place.local)?;
    match &decl.ty {
        Ty::Adt { name, .. } => Some(name.as_str()),
        _ => None,
    }
}

#[must_use]
fn matching_reads(
    reads: &[DiscriminantRead],
    switch_block: BlockId,
    discr_local: usize,
) -> Vec<&DiscriminantRead> {
    let same_block: Vec<_> = reads
        .iter()
        .filter(|read| read.discr_local == discr_local && read.block == switch_block)
        .collect();

    if !same_block.is_empty() {
        return same_block;
    }

    reads.iter().filter(|read| read.discr_local == discr_local).collect()
}

#[must_use]
fn operand_local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projections.is_empty() => {
            Some(place.local)
        }
        Operand::Copy(_) | Operand::Move(_) | Operand::Constant(_) => None,
        _ => None,
    }
}

#[must_use]
fn block_by_id(body: &VerifiableBody, id: BlockId) -> Option<&BasicBlock> {
    body.blocks.iter().find(|block| block.id == id)
}

#[must_use]
fn aggregate_assignment<'a>(stmt: &'a Statement, target_place: &Place) -> Option<(&'a str, usize)> {
    let Statement::Assign { place, rvalue, .. } = stmt else {
        return None;
    };
    if place != target_place {
        return None;
    }

    match rvalue {
        Rvalue::Aggregate(AggregateKind::Adt { name, variant }, _) => {
            Some((name.as_str(), *variant))
        }
        _ => None,
    }
}

#[must_use]
fn state_name(enum_name: &str, variant: usize) -> String {
    format!("{enum_name}::variant_{variant}")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn enum_ty(name: &str) -> Ty {
        Ty::Adt { name: name.to_string(), fields: vec![] }
    }

    fn assign(place: Place, rvalue: Rvalue) -> Statement {
        Statement::Assign { place, rvalue, span: SourceSpan::default() }
    }

    fn discr_stmt(discr_local: usize, enum_local: usize) -> Statement {
        assign(Place::local(discr_local), Rvalue::Discriminant(Place::local(enum_local)))
    }

    fn variant_stmt(enum_local: usize, enum_name: &str, variant: usize) -> Statement {
        assign(
            Place::local(enum_local),
            Rvalue::Aggregate(AggregateKind::Adt { name: enum_name.to_string(), variant }, vec![]),
        )
    }

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    fn switch(discr_local: usize, targets: &[(u128, usize)], otherwise: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(discr_local)),
            targets: targets.iter().map(|(value, block)| (*value, BlockId(*block))).collect(),
            otherwise: BlockId(otherwise),
            span: SourceSpan::default(),
        }
    }

    fn body(locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody { locals, blocks, arg_count: 0, return_ty: Ty::Unit }
    }

    #[test]
    fn test_extract_simple_enum_state_machine() {
        let body = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("TrafficLight"), name: Some("state".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2), (2, 3)], 4)),
                block(1, vec![variant_stmt(1, "TrafficLight", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "TrafficLight", 2)], Terminator::Return),
                block(3, vec![], Terminator::Return),
                block(4, vec![], Terminator::Return),
            ],
        );

        let reads = find_discriminant_reads(&body);
        assert_eq!(reads.len(), 1);
        assert_eq!(reads[0].discr_local, 2);
        assert_eq!(reads[0].place, Place::local(1));
        assert_eq!(reads[0].block, BlockId(0));

        let machine = extract_state_machine(&body, "TrafficLight").expect("state machine");
        assert_eq!(machine.initial, StateId(0));
        assert_eq!(machine.states.len(), 3);
        assert_eq!(machine.transitions.len(), 2);
        assert!(machine.states.iter().any(|state| state.name == "TrafficLight::variant_0"));
        assert!(machine.transitions.iter().any(|t| t.from == StateId(0) && t.to == StateId(1)));
        assert!(machine.transitions.iter().any(|t| t.from == StateId(1) && t.to == StateId(2)));

        let machines = extract_state_machines(&body);
        assert_eq!(machines.len(), 1);
    }

    #[test]
    fn test_extract_cyclic_state_machine() {
        let body = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Mode"), name: Some("mode".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "Mode", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Mode", 0)], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let machine = extract_state_machine(&body, "Mode").expect("cyclic state machine");
        assert_eq!(machine.transitions.len(), 2);
        assert!(machine.transitions.iter().any(|t| t.from == StateId(0) && t.to == StateId(1)));
        assert!(machine.transitions.iter().any(|t| t.from == StateId(1) && t.to == StateId(0)));
    }

    #[test]
    fn test_extract_no_state_machine_returns_none() {
        let body = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("value".into()) },
            ],
            vec![block(
                0,
                vec![assign(Place::local(1), Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 64))))],
                Terminator::Return,
            )],
        );

        assert!(find_discriminant_reads(&body).is_empty());
        assert!(extract_state_machine(&body, "Mode").is_none());
        assert!(extract_state_machines(&body).is_empty());
    }

    #[test]
    fn test_extract_multiple_arms() {
        let body = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("Protocol"), name: Some("protocol".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2), (2, 3), (3, 4)], 5)),
                block(1, vec![variant_stmt(1, "Protocol", 1)], Terminator::Return),
                block(2, vec![variant_stmt(1, "Protocol", 3)], Terminator::Return),
                block(3, vec![variant_stmt(1, "Protocol", 0)], Terminator::Return),
                block(4, vec![variant_stmt(1, "Protocol", 2)], Terminator::Return),
                block(5, vec![], Terminator::Return),
            ],
        );

        let machine = extract_state_machine(&body, "Protocol").expect("multi-arm state machine");
        assert_eq!(machine.states.len(), 4);
        assert_eq!(machine.transitions.len(), 4);
        assert!(machine.transitions.iter().any(|t| t.from == StateId(0) && t.to == StateId(1)));
        assert!(machine.transitions.iter().any(|t| t.from == StateId(1) && t.to == StateId(3)));
        assert!(machine.transitions.iter().any(|t| t.from == StateId(2) && t.to == StateId(0)));
        assert!(machine.transitions.iter().any(|t| t.from == StateId(3) && t.to == StateId(2)));
    }

    #[test]
    fn test_extract_self_transition() {
        let body = body(
            vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: enum_ty("WorkerState"), name: Some("worker".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("discr".into()) },
            ],
            vec![
                block(0, vec![discr_stmt(2, 1)], switch(2, &[(0, 1), (1, 2)], 3)),
                block(1, vec![variant_stmt(1, "WorkerState", 0)], Terminator::Return),
                block(2, vec![], Terminator::Return),
                block(3, vec![], Terminator::Return),
            ],
        );

        let machine =
            extract_state_machine(&body, "WorkerState").expect("self-transition state machine");
        assert_eq!(machine.transitions.len(), 1);
        assert!(machine.transitions.iter().any(|t| t.from == StateId(0) && t.to == StateId(0)));
    }
}
