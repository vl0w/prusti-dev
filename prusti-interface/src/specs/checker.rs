use log::{debug, info};
use rustc_hir::{
    self as hir,
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
    itemlikevisit::ItemLikeVisitor,
};
use rustc_middle::{hir::map::Map, ty::TyCtxt};
use rustc_span::{MultiSpan, Span};

use std::collections::HashMap;

use crate::{
    environment::Environment,
    utils::{has_prusti_attr, has_spec_only_attr, has_model_attr},
    PrustiError,
};

/// Checker visitor for the specifications.
/// Currently checks that:
/// * `predicate!` functions are never used from non-specification code
/// * `#[model]`s are not used in non-specification code
#[derive(Default)]
pub struct SpecChecker {
    /// Map of the `DefID`s to the `Span`s of `predicate!` functions found in the first pass.
    predicates: HashMap<DefId, Span>,

    /// Span of use and definition of predicates used outside of specifications, collected in the second pass.
    pred_usages: Vec<(Span, Span)>,

    /// Spans of usages of model functions in non-specification code
    illegal_model_usages: Vec<Span>,
}

/// First predicate checks visitor: collect all function items that originate
/// from predicates
struct CollectPredicatesVisitor<'v, 'tcx> {
    tcx: TyCtxt<'tcx>,

    predicates: &'v mut HashMap<DefId, Span>,
}

impl<'v, 'tcx> intravisit::Visitor<'tcx> for CollectPredicatesVisitor<'v, 'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.tcx.hir())
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx hir::FnDecl<'tcx>,
        b: hir::BodyId,
        s: Span,
        id: hir::HirId,
    ) {
        // collect this fn's DefId if predicate function
        let attrs = self.tcx.hir().attrs(id);
        if has_prusti_attr(attrs, "pred_spec_id_ref") {
            let def_id = self.tcx.hir().local_def_id(id).to_def_id();
            self.predicates.insert(def_id, s);
        }

        intravisit::walk_fn(self, fk, fd, b, s, id);
    }
}

/// Second predicate checks visitor: check any references to predicate functions
/// from non-specification code
struct CheckPredicatesVisitor<'v, 'tcx> {
    tcx: TyCtxt<'tcx>,

    predicates: &'v HashMap<DefId, Span>,
    pred_usages: &'v mut Vec<(Span, Span)>,
}

impl<'v, 'tcx> Visitor<'tcx> for CheckPredicatesVisitor<'v, 'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.tcx.hir())
    }

    fn visit_item(&mut self, i: &'tcx hir::Item<'tcx>) {
        // restrict to "interesting" sub-nodes to visit, i.e. anything that
        // could be or contain call (or other usage of predicate) expressions
        use hir::ItemKind::*;

        match i.kind {
            Static(_, _, _) | Fn(_, _, _) | Mod(_) | Impl { .. } => {
                intravisit::walk_item(self, i);
            }
            _ => {
                // don't recurse into e.g. struct decls, type aliases, consts etc.
            }
        }
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Path(ref path) = ex.kind {
            let def_id = ex.hir_id.owner;
            if self.tcx.is_mir_available(def_id) && !self.tcx.is_constructor(def_id.to_def_id()) {
                let res = self.tcx.typeck(def_id).qpath_res(path, ex.hir_id);
                if let hir::def::Res::Def(_, def_id) = res {
                    if let Some(pred_def_span) = self.predicates.get(&def_id) {
                        self.pred_usages.push((ex.span, *pred_def_span));
                    }
                }
            }
        }

        intravisit::walk_expr(self, ex);
    }

    fn visit_fn(
        &mut self,
        fk: intravisit::FnKind<'tcx>,
        fd: &'tcx hir::FnDecl<'tcx>,
        b: hir::BodyId,
        s: Span,
        id: hir::HirId,
    ) {
        // Stop checking inside `prusti::spec_only` functions
        let attrs = self.tcx.hir().attrs(id);
        if has_spec_only_attr(attrs) {
            return;
        }

        intravisit::walk_fn(self, fk, fd, b, s, id);
    }
}

/// Checks for the usage of models in non-specification code
struct ModelUsageVisitor<'v, 'tcx> {
    tcx: TyCtxt<'tcx>,
    model_usages_in_non_spec_code: &'v mut Vec<Span>,
}

impl<'v, 'tcx> ModelUsageVisitor<'v, 'tcx> {
    fn get_called_method(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<hir::HirId> {
        let maybe_method_def_id = self
            .tcx
            .typeck(expr.hir_id.owner)
            .type_dependent_def_id(expr.hir_id);
        if let Some(method_def_id) = maybe_method_def_id {
            let maybe_local_def_id = method_def_id.as_local();
            if let Some(local_def_id) = maybe_local_def_id {
                let decl_hir_id = self.tcx.hir().local_def_id_to_hir_id(local_def_id);
                return Some(decl_hir_id);
            }
        }
        None
    }

    fn is_embedded_in_spec(&self, hir_id: hir::HirId) -> bool {
        for (parent_local_def_id, _) in self.tcx.hir().parent_owner_iter(hir_id) {
            let parent_hir_id = self.tcx.hir().local_def_id_to_hir_id(parent_local_def_id);
            let attrs = self.tcx.hir().attrs(parent_hir_id);
            if has_spec_only_attr(attrs) {
                return true;
            }
        }

        false
    }
}

impl<'v, 'tcx> intravisit::Visitor<'tcx> for ModelUsageVisitor<'v, 'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        intravisit::NestedVisitorMap::All(self.tcx.hir())
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::MethodCall(_, call_span, _, _) = expr.kind {
            let maybe_method_decl_hir_id: Option<hir::HirId> = self.get_called_method(expr);

            if let Some(method_decl_hir_id) = maybe_method_decl_hir_id {
                let attrs = self.tcx.hir().attrs(method_decl_hir_id);

                if has_model_attr(&attrs) && !self.is_embedded_in_spec(expr.hir_id) {
                    self.model_usages_in_non_spec_code.push(call_span);
                }
            }
        }

        intravisit::walk_expr(self, expr);
    }
}

impl<'tcx> SpecChecker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn check(&mut self, tcx: TyCtxt<'tcx>) {
        self.check_predicate_usages(tcx);
        self.check_model_usages(tcx);
    }

    fn check_predicate_usages(&mut self, tcx: TyCtxt<'tcx>) {
        let mut collect = CollectPredicatesVisitor {
            tcx,
            predicates: &mut self.predicates,
        };
        tcx.hir().walk_toplevel_module(&mut collect);
        tcx.hir().walk_attributes(&mut collect);

        let mut visit = CheckPredicatesVisitor {
            tcx: collect.tcx,
            predicates: &self.predicates,
            pred_usages: &mut self.pred_usages,
        };
        tcx.hir().walk_toplevel_module(&mut visit);
        tcx.hir().walk_attributes(&mut visit);

        debug!("Predicate funcs: {:?}", self.predicates);
        debug!("Predicate usages: {:?}", self.pred_usages);
    }

    fn check_model_usages(&mut self, tcx: TyCtxt<'tcx>) {
        let mut collect = ModelUsageVisitor {
            tcx,
            model_usages_in_non_spec_code: &mut self.illegal_model_usages,
        };
        tcx.hir().walk_toplevel_module(&mut collect);
    }

    pub fn report_errors(&self, env: &Environment<'tcx>) {
        for &(usage_span, def_span) in &self.pred_usages {
            PrustiError::incorrect(
                "using predicate from non-specification code is not allowed".to_string(),
                MultiSpan::from_span(usage_span),
            )
            .add_note(
                "this is a specification-only predicate function",
                Some(def_span),
            )
            .emit(env);
        }

        for &model_span in &self.illegal_model_usages {
            PrustiError::incorrect(
                "using models in non-specification code is not allowed".to_string(),
                MultiSpan::from_span(model_span),
            )
            .emit(env);
        }
    }
}