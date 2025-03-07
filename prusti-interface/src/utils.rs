// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir::Place`.

use log::trace;
use prusti_rustc_interface::ast::ast;
use prusti_rustc_interface::data_structures::fx::FxHashSet;
use prusti_rustc_interface::hir::def_id::{DefId, LocalDefId};
use prusti_rustc_interface::middle::{
    mir,
    ty::{self, TyCtxt},
};
use analysis::mir_utils::expand_struct_place;
use prusti_utils::force_matches;

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// +   `is_prefix(x.f, x.f) == true`
/// +   `is_prefix(x.f.g, x.f) == true`
/// +   `is_prefix(x.f, x.f.g) == false`
pub fn is_prefix<'tcx>(place: mir::Place<'tcx>, potential_prefix: mir::Place<'tcx>) -> bool {
    if place.local != potential_prefix.local
        || place.projection.len() < potential_prefix.projection.len()
    {
        false
    } else {
        place
            .projection
            .iter()
            .zip(potential_prefix.projection.iter())
            .all(|(e1, e2)| e1 == e2)
    }
}

/// Expand `current_place` one level down by following the `guide_place`.
/// Returns the new `current_place` and a vector containing other places that
/// could have resulted from the expansion.
pub fn expand_one_level<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    current_place: mir::Place<'tcx>,
    guide_place: mir::Place<'tcx>,
) -> (mir::Place<'tcx>, Vec<mir::Place<'tcx>>) {
    let index = current_place.projection.len();
    match guide_place.projection[index] {
        mir::ProjectionElem::Field(projected_field, field_ty) => {
            let places =
                expand_struct_place(current_place, mir, tcx, Some(projected_field.index()));
            let new_current_place = tcx.mk_place_field(current_place, projected_field, field_ty);
            (new_current_place, places)
        }
        mir::ProjectionElem::Downcast(_symbol, variant) => {
            let kind = &current_place.ty(mir, tcx).ty.kind();
            force_matches!(kind, ty::TyKind::Adt(adt, _) =>
                (tcx.mk_place_downcast(current_place, *adt, variant), Vec::new())
            )
        }
        mir::ProjectionElem::Deref => (tcx.mk_place_deref(current_place), Vec::new()),
        mir::ProjectionElem::Index(idx) => (tcx.mk_place_index(current_place, idx), Vec::new()),
        elem => {
            unimplemented!("elem = {:?}", elem);
        }
    }
}

/// Pop the last projection from the place and return the new place with the popped element.
pub fn try_pop_one_level<'tcx>(
    tcx: TyCtxt<'tcx>,
    place: mir::Place<'tcx>,
) -> Option<(mir::PlaceElem<'tcx>, mir::Place<'tcx>)> {
    if place.projection.len() > 0 {
        let last_index = place.projection.len() - 1;
        let new_place = mir::Place {
            local: place.local,
            projection: tcx.intern_place_elems(&place.projection[..last_index]),
        };
        Some((place.projection[last_index], new_place))
    } else {
        None
    }
}

/// Pop the last element from the place if it is a dereference.
pub fn try_pop_deref<'tcx>(tcx: TyCtxt<'tcx>, place: mir::Place<'tcx>) -> Option<mir::Place<'tcx>> {
    try_pop_one_level(tcx, place).and_then(|(elem, base)| {
        if let mir::ProjectionElem::Deref = elem {
            Some(base)
        } else {
            None
        }
    })
}

/// Subtract the `subtrahend` place from the `minuend` place. The
/// subtraction is defined as set minus between `minuend` place replaced
/// with a set of places that are unrolled up to the same level as
/// `subtrahend` and the singleton `subtrahend` set. For example,
/// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
/// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
/// subtracting `{x.f.g.h}` from it, which results into `{x.g, x.h,
/// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`.
pub fn expand<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    mut minuend: mir::Place<'tcx>,
    subtrahend: mir::Place<'tcx>,
) -> Vec<mir::Place<'tcx>> {
    assert!(
        is_prefix(subtrahend, minuend),
        "The minuend must be the prefix of the subtrahend."
    );
    trace!(
        "[enter] expand minuend={:?} subtrahend={:?}",
        minuend,
        subtrahend
    );
    let mut place_set = Vec::new();
    while minuend.projection.len() < subtrahend.projection.len() {
        let (new_minuend, places) = expand_one_level(mir, tcx, minuend, subtrahend);
        minuend = new_minuend;
        place_set.extend(places);
    }
    trace!(
        "[exit] expand minuend={:?} subtrahend={:?} place_set={:?}",
        minuend,
        subtrahend,
        place_set
    );
    place_set
}

/// Try to collapse all places in `places` by following the
/// `guide_place`. This function is basically the reverse of
/// `expand_struct_place`.
pub fn collapse<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    places: &mut FxHashSet<mir::Place<'tcx>>,
    guide_place: mir::Place<'tcx>,
) {
    fn recurse<'tcx>(
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        places: &mut FxHashSet<mir::Place<'tcx>>,
        current_place: mir::Place<'tcx>,
        guide_place: mir::Place<'tcx>,
    ) {
        if current_place != guide_place {
            let (new_current_place, mut expansion) =
                expand_one_level(mir, tcx, current_place, guide_place);
            recurse(mir, tcx, places, new_current_place, guide_place);
            expansion.push(new_current_place);
            if expansion.iter().all(|place| places.contains(place)) {
                for place in expansion {
                    places.remove(&place);
                }
                places.insert(current_place);
            }
        }
    }
    recurse(mir, tcx, places, guide_place.local.into(), guide_place);
}

#[derive(Debug)]
pub struct VecPlaceComponent<'tcx> {
    place: mir::Place<'tcx>,
}

impl<'tcx> VecPlaceComponent<'tcx> {
    pub fn get_mir_place(&self) -> mir::Place<'tcx> {
        self.place
    }
}

/// A different way to represent a place that is more similar to the one
/// mentioned in the issue <https://github.com/rust-lang/rust/issues/52708>.
#[derive(Debug)]
pub struct VecPlace<'tcx> {
    components: Vec<VecPlaceComponent<'tcx>>,
}

impl<'tcx> VecPlace<'tcx> {
    pub fn new(
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        place: mir::Place<'tcx>,
    ) -> VecPlace<'tcx> {
        let mut vec_place = Self {
            components: Vec::new(),
        };
        let mut prefix: mir::Place = place.local.into();
        vec_place
            .components
            .push(VecPlaceComponent { place: prefix });
        while prefix.projection.len() < place.projection.len() {
            let (new_prefix, _) = expand_one_level(mir, tcx, prefix, place);
            prefix = new_prefix;
            vec_place
                .components
                .push(VecPlaceComponent { place: prefix });
        }
        vec_place
    }
    pub fn iter<'a>(&'a self) -> impl DoubleEndedIterator<Item = &'a VecPlaceComponent<'tcx>> {
        self.components.iter()
    }
    pub fn component_count(&self) -> usize {
        self.components.len()
    }
}

pub fn get_local_attributes(tcx: ty::TyCtxt<'_>, def_id: LocalDefId) -> &[prusti_rustc_interface::ast::ast::Attribute] {
    tcx.hir().attrs(tcx.hir().local_def_id_to_hir_id(def_id))
}

pub fn get_attributes(tcx: ty::TyCtxt<'_>, def_id: DefId) -> &[prusti_rustc_interface::ast::ast::Attribute] {
    if let Some(local_def_id) = def_id.as_local() {
        get_local_attributes(tcx, local_def_id)
    } else {
        tcx.item_attrs(def_id)
    }
}

/// Check if `prusti::<name>` is among the attributes.
/// Any arguments of the attribute are ignored.
pub fn has_prusti_attr(attrs: &[ast::Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| match &attr.kind {
        ast::AttrKind::Normal(
            ast::AttrItem {
                path:
                    ast::Path {
                        span: _,
                        segments,
                        tokens: _,
                    },
                args: _,
                tokens: _,
            },
            _,
        ) => {
            segments.len() == 2
                && segments[0].ident.as_str() == "prusti"
                && segments[1].ident.as_str() == name
        }
        _ => false,
    })
}

/// Check if `prusti::spec_only` is among the attributes.
pub fn has_spec_only_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "spec_only")
}

/// Check if `prusti::extern_spec` is among the attributes.
pub fn has_extern_spec_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "extern_spec")
}

pub fn read_extern_spec_attr(attrs: &[ast::Attribute]) -> Option<String> {
    read_prusti_attr("extern_spec", attrs)
}

pub fn has_to_model_fn_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_models_to_model_fn")
}

pub fn has_to_model_impl_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "type_models_to_model_impl")
}

pub fn has_trait_bounds_ghost_constraint(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "ghost_constraint_trait_bounds_in_where_clause")
}

pub fn has_abstract_predicate_attr(attrs: &[ast::Attribute]) -> bool {
    has_prusti_attr(attrs, "abstract_predicate")
}

/// Read the value stored in a Prusti attribute (e.g. `prusti::<attr_name>="...")`.
pub fn read_prusti_attrs(attr_name: &str, attrs: &[ast::Attribute]) -> Vec<String> {
    let mut strings = vec![];
    for attr in attrs {
        if let ast::AttrKind::Normal(
            ast::AttrItem {
                path:
                    ast::Path {
                        span: _,
                        segments,
                        tokens: _,
                    },
                args: ast::MacArgs::Eq(_, ast::MacArgsEq::Hir(ast::Lit {token, ..})),
                tokens: _,
            },
            _,
        ) = &attr.kind
        {
            // Skip attributes whose path don't match with "prusti::<attr_name>"
            if !(segments.len() == 2
                && segments[0].ident.as_str() == "prusti"
                && segments[1].ident.as_str() == attr_name)
            {
                continue;
            }
            fn extract_string(token: &prusti_rustc_interface::ast::token::Lit) -> String {
                token.symbol.as_str().replace("\\\"", "\"")
            }
            strings.push(extract_string(token));
        };
    }
    strings
}

/// Read the value stored in a single Prusti attribute (e.g. `prusti::<attr_name>="...")`.
pub fn read_prusti_attr(attr_name: &str, attrs: &[ast::Attribute]) -> Option<String> {
    read_prusti_attrs(attr_name, attrs).pop()
}
