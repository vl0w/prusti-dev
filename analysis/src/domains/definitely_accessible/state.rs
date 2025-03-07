// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    mir_utils::{is_prefix, Place},
    PointwiseState,
};
use log::info;
use prusti_rustc_interface::{
    data_structures::{fx::FxHashSet, stable_map::FxHashMap},
    middle::{mir, ty, ty::TyCtxt},
    span::source_map::SourceMap,
    target::abi::VariantIdx,
};
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::fmt;

#[derive(Clone, Default, Eq, PartialEq)]
pub struct DefinitelyAccessibleState<'tcx> {
    /// Places that are definitely not moved-out nor blocked by a *mutable* reference.
    pub(super) definitely_accessible: FxHashSet<Place<'tcx>>,
    /// Places that are definitely not moved-out nor blocked by a *mutable or shared* reference.
    /// Considering pack/unpack operations, this should always be a subset of `definitely_accessible`.
    pub(super) definitely_owned: FxHashSet<Place<'tcx>>,
}

impl<'tcx> DefinitelyAccessibleState<'tcx> {
    pub fn get_definitely_accessible(&self) -> &FxHashSet<Place<'tcx>> {
        &self.definitely_accessible
    }

    pub fn get_definitely_owned(&self) -> &FxHashSet<Place<'tcx>> {
        &self.definitely_owned
    }

    pub fn check_invariant(&self, location: impl fmt::Debug) {
        for &owned_place in self.definitely_owned.iter() {
            debug_assert!(
                self.definitely_accessible
                    .iter()
                    .any(|&place| place == owned_place || is_prefix(owned_place, place)),
                "In the state before {:?} the place {:?} is owned but not accessible",
                location,
                owned_place
            );
        }
    }
}

impl<'tcx> Serialize for DefinitelyAccessibleState<'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_map(Some(2))?;
        let mut definitely_accessible_set: Vec<_> = self.definitely_accessible.iter().collect();
        definitely_accessible_set.sort();
        let mut definitely_accessible_strings = vec![];
        for &place in definitely_accessible_set {
            definitely_accessible_strings.push(format!("{:?}", place));
        }
        seq.serialize_entry("accessible", &definitely_accessible_strings)?;
        let mut definitely_owned_set: Vec<_> = self.definitely_owned.iter().collect();
        definitely_owned_set.sort();
        let mut definitely_owned_strings = vec![];
        for &place in definitely_owned_set {
            definitely_owned_strings.push(format!("{:?}", place));
        }
        seq.serialize_entry("owned", &definitely_owned_strings)?;
        seq.end()
    }
}

impl fmt::Debug for DefinitelyAccessibleState<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", serde_json::to_string_pretty(&self).unwrap())
    }
}

impl<'mir, 'tcx: 'mir> PointwiseState<'mir, 'tcx, DefinitelyAccessibleState<'tcx>> {
    /// Make a best-effort at injecting statements to check the analysis state.
    pub fn generate_test_program(&self, tcx: TyCtxt<'tcx>, source_map: &SourceMap) -> String {
        let mir_span = self.mir.span;
        let source_file = source_map.lookup_source_file(mir_span.data().lo);
        let source_lines_num = source_file.count_lines();
        let mut result: Vec<String> = (0..source_lines_num)
            .map(|line_index| source_file.get_line(line_index).unwrap().to_string())
            .collect();
        let mut first_location_on_line: FxHashMap<usize, mir::Location> = FxHashMap::default();
        for (block, block_data) in self.mir.basic_blocks().iter_enumerated() {
            for statement_index in 0..=block_data.statements.len() {
                let location = mir::Location {
                    block,
                    statement_index,
                };
                let span = self.mir.source_info(location).span;
                if span.parent_callsite().is_some() {
                    info!("Statement {:?} is generated by a macro", location);
                    continue;
                }
                if source_map.is_multiline(span) {
                    info!("Statement {:?} is on multiple lines", location);
                    continue;
                }
                if let Ok(file_lines) = source_map.span_to_lines(span) {
                    if file_lines.lines.len() == 1 {
                        let line = file_lines.lines.first().unwrap();
                        let line_num = line.line_index + 1;
                        info!(
                            "Statement {:?} is on a single line at {}",
                            location, line_num
                        );
                        // Check that it parses as a statement
                        let line_seems_stmt =
                            syn::parse_str::<syn::Stmt>(&result[line.line_index]).is_ok();
                        if !line_seems_stmt {
                            info!("Statement {:?} doesn't parse as a statement", location);
                            continue;
                        }
                        // Keep the first span
                        let insert_or_replace =
                            if let Some(other_location) = first_location_on_line.get(&line_num) {
                                let other_span = self.mir.source_info(*other_location).span;
                                span < other_span
                            } else {
                                true
                            };
                        if insert_or_replace {
                            first_location_on_line.insert(line_num, location);
                        }
                    }
                } else {
                    info!("Statement {:?} has no lines", location);
                }
            }
        }
        let mut line_locations: Vec<_> = first_location_on_line.iter().collect();
        line_locations.sort_by(|left, right| right.0.cmp(left.0)); // From last to first
        for (&line_num, &location) in line_locations {
            info!(
                "The first single-line statement on line {} is {:?}",
                line_num, location
            );
            let before = "\t\t\t";
            let after = " // Check analysis";
            let state = self.lookup_before(location).unwrap();
            let mut check_stmts = vec![];
            for &place in state.definitely_accessible.iter() {
                if let Some(place_expr) = pretty_print_place(tcx, self.mir, place) {
                    check_stmts.push(format!("{}let _ = & {};{}", before, place_expr, after));
                }
            }
            for &place in state.definitely_owned.iter() {
                if let Some(place_expr) = pretty_print_place(tcx, self.mir, place) {
                    let local_decl = &self.mir.local_decls[place.local];
                    // &mut cannot be used on locals that are not marked as mut
                    if local_decl.mutability != mir::Mutability::Not {
                        check_stmts
                            .push(format!("{}let _ = &mut {};{}", before, place_expr, after));
                    }
                }
            }
            // Inject the checks
            result.insert(line_num - 1, check_stmts.join("\n"));
        }
        result.join("\n")
    }
}

fn pretty_print_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: Place<'tcx>,
) -> Option<String> {
    let mut pieces = vec![];

    // Open parenthesis
    for elem in place.projection.iter().rev() {
        match elem {
            mir::ProjectionElem::Deref => pieces.push("(*".to_string()),
            mir::ProjectionElem::Field(..) => pieces.push("(".to_string()),
            _ => {}
        }
    }

    // Skip compiler-generated variables
    if body.local_decls[place.local].from_compiler_desugaring() {
        return None;
    }

    // Find name of the local
    let local_name = body
        .var_debug_info
        .iter()
        .find(|var_debug_info| {
            if let mir::VarDebugInfoContents::Place(debug_place) = var_debug_info.value {
                if let Some(debug_local) = debug_place.as_local() {
                    return debug_local == place.local;
                }
            };
            false
        })
        .map(|var_debug_info| var_debug_info.name);
    if let Some(name) = local_name {
        pieces.push(format!("{}", name));
    } else {
        return None;
    }

    // Close parenthesis
    let mut prev_ty = body.local_decls[place.local].ty;
    let mut variant = None;
    for (proj_base, elem) in place.iter_projections() {
        match elem {
            mir::ProjectionElem::Deref => {
                pieces.push(")".to_string());
            }
            mir::ProjectionElem::Downcast(_, variant_index) => {
                prev_ty = proj_base.ty(body, tcx).ty;
                variant = Some(variant_index);
            }
            mir::ProjectionElem::Field(field, field_ty) => {
                let field_name = describe_field_from_ty(tcx, prev_ty, field, variant)?;
                pieces.push(format!(".{})", field_name));
                prev_ty = field_ty;
                variant = None;
            }
            mir::ProjectionElem::Index(..)
            | mir::ProjectionElem::ConstantIndex { .. }
            | mir::ProjectionElem::Subslice { .. } => {
                // It's not possible to move-out or borrow an individual element.
                unreachable!()
            }
        }
    }

    Some(pieces.join(""))
}

/// End-user visible description of the `field_index`nth field of `ty`
fn describe_field_from_ty(
    tcx: TyCtxt<'_>,
    ty: ty::Ty<'_>,
    field: mir::Field,
    variant_index: Option<VariantIdx>,
) -> Option<String> {
    if ty.is_box() {
        // If the type is a box, the field is described from the boxed type
        describe_field_from_ty(tcx, ty.boxed_ty(), field, variant_index)
    } else {
        match *ty.kind() {
            ty::TyKind::Adt(def, _) => {
                let variant = if let Some(idx) = variant_index {
                    assert!(def.is_enum());
                    &def.variants()[idx]
                } else {
                    def.non_enum_variant()
                };
                Some(variant.fields[field.index()].ident(tcx).to_string())
            }
            ty::TyKind::Tuple(_) => Some(field.index().to_string()),
            ty::TyKind::Ref(_, ty, _) | ty::TyKind::RawPtr(ty::TypeAndMut { ty, .. }) => {
                describe_field_from_ty(tcx, ty, field, variant_index)
            }
            ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
                describe_field_from_ty(tcx, ty, field, variant_index)
            }
            ty::TyKind::Closure(..) | ty::TyKind::Generator(..) => {
                // Supporting these cases is complex
                None
            }
            _ => unreachable!("Unexpected type `{:?}`", ty),
        }
    }
}
