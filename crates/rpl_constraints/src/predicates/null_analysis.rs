use mirsa_core::cfg::build_cfg;
use mirsa_core::mir::{collect_ptr_places, collect_ref_places};
use mirsa_domains::framework::forward::{PathForwardAnalysisConfig, PathForwardAnalysisResult};
use mirsa_domains::nullptr::{NullPtr, NullPtrState, analyze_nullptr, query_nullptr_before_location};
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

#[instrument(level = "debug", skip(tcx, body), fields(n = body.local_decls.len()), ret)]
pub(crate) fn analyze_null_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> PathForwardAnalysisResult<NullPtrState<'tcx>> {
    let cfg = build_cfg(body);
    let ptr_places = collect_ptr_places(tcx, body);
    let ref_places = collect_ref_places(tcx, body);
    analyze_nullptr(
        tcx,
        body,
        &cfg,
        &ptr_places,
        &ref_places,
        PathForwardAnalysisConfig {
            max_paths: 128,
            widen_after_iterations: None,
        },
    )
}

pub(crate) fn is_null_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    result: &PathForwardAnalysisResult<NullPtrState<'tcx>>,
    location: mir::Location,
    local: mir::Local,
) -> bool {
    let Some(state) = query_nullptr_before_location(tcx, body, result, location) else {
        return false;
    };
    let place = mir::Place::from(local);
    let value = state
        .refs
        .get(&place)
        .copied()
        .or_else(|| state.pointers.get(&place).copied())
        .unwrap_or(NullPtr::Bot);
    matches!(value, NullPtr::Null)
}
