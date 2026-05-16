use mirsa_core::cfg::build_cfg;
use mirsa_core::mir::collect_body_places;
use mirsa_domains::framework::forward::{PathForwardAnalysisConfig, PathForwardAnalysisResult};
use mirsa_domains::internval::{InternvalState, analyze_internval, query_internval_before_location};
use rustc_middle::mir;
use rustc_middle::ty::{TyCtxt, TyKind, TypingEnv};

use crate::Const;

#[instrument(level = "debug", skip(tcx, body), fields(n = body.local_decls.len()), ret)]
pub(crate) fn analyze_internval_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> PathForwardAnalysisResult<InternvalState<'tcx>> {
    let cfg = build_cfg(body);
    let places = collect_body_places(tcx, body);
    analyze_internval(
        tcx,
        body,
        &cfg,
        &places,
        PathForwardAnalysisConfig {
            max_paths: 64,
            widen_after_iterations: Some(10),
        },
    )
}

fn unsigned_bits_to_i128(bits: u128, bit_width: u64) -> i128 {
    if bit_width == 128 {
        if bits <= i128::MAX as u128 {
            bits as i128
        } else {
            i128::MAX
        }
    } else {
        let mask = (1u128 << bit_width) - 1;
        (bits & mask) as i128
    }
}

fn signed_bits_to_i128(bits: u128, bit_width: u64) -> i128 {
    if bit_width == 128 {
        bits as i128
    } else {
        let sign_bit = 1u128 << (bit_width - 1);
        let mask = (1u128 << bit_width) - 1;
        let x = bits & mask;
        if (x & sign_bit) != 0 {
            (x as i128) - ((1u128 << bit_width) as i128)
        } else {
            x as i128
        }
    }
}

fn const_to_i128<'tcx>(tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, konst: Const<'tcx>) -> Option<i128> {
    let scalar = konst.try_eval_scalar_int(tcx, typing_env)?;
    let ty = match konst {
        Const::MIR(konst) => konst.ty(),
        Const::Param(_) => return None,
    };
    let (bit_width, signed) = match ty.kind() {
        TyKind::Int(_) => (scalar.size().bits(), true),
        TyKind::Uint(_) => (scalar.size().bits(), false),
        TyKind::Bool => (1, false),
        TyKind::Char => (32, false),
        _ => return None,
    };
    let bits = scalar.to_bits_unchecked();
    Some(if signed {
        signed_bits_to_i128(bits, bit_width)
    } else {
        unsigned_bits_to_i128(bits, bit_width)
    })
}

pub(crate) fn eq_const_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
    result: &PathForwardAnalysisResult<InternvalState<'tcx>>,
    location: mir::Location,
    local: mir::Local,
    konst: Const<'tcx>,
) -> bool {
    let Some(expected) = const_to_i128(tcx, typing_env, konst) else {
        return false;
    };
    let Some(state) = query_internval_before_location(tcx, body, result, location) else {
        return false;
    };
    let place = mir::Place::from(local);
    let Some(interval) = state.internval.get(&place).copied() else {
        return false;
    };
    !interval.is_empty() && interval.low == expected && interval.high == expected
}

pub(crate) fn lt_const_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
    result: &PathForwardAnalysisResult<InternvalState<'tcx>>,
    location: mir::Location,
    local: mir::Local,
    konst: Const<'tcx>,
) -> bool {
    let Some(expected) = const_to_i128(tcx, typing_env, konst) else {
        return false;
    };
    let Some(state) = query_internval_before_location(tcx, body, result, location) else {
        return false;
    };
    let place = mir::Place::from(local);
    let Some(interval) = state.internval.get(&place).copied() else {
        return false;
    };
    !interval.is_empty() && interval.high < expected
}

pub(crate) fn gt_const_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    body: &mir::Body<'tcx>,
    result: &PathForwardAnalysisResult<InternvalState<'tcx>>,
    location: mir::Location,
    local: mir::Local,
    konst: Const<'tcx>,
) -> bool {
    let Some(expected) = const_to_i128(tcx, typing_env, konst) else {
        return false;
    };
    let Some(state) = query_internval_before_location(tcx, body, result, location) else {
        return false;
    };
    let place = mir::Place::from(local);
    let Some(interval) = state.internval.get(&place).copied() else {
        return false;
    };
    !interval.is_empty() && interval.low > expected
}

fn local_len<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    state: &InternvalState<'tcx>,
    local: mir::Local,
) -> Option<(i128, i128)> {
    let place = mir::Place::from(local);
    let ty = place.ty(&body.local_decls, tcx).ty;
    let len_iv = match ty.kind() {
        TyKind::Array(_, len) => len
            .try_to_target_usize(tcx)
            .map(|len| mirsa_domains::internval::Internval::new(len as i128, len as i128)),
        TyKind::Slice(_) => state.get_slice_meta(&place),
        TyKind::Ref(_, inner, _) => match inner.kind() {
            TyKind::Array(_, len) => len
                .try_to_target_usize(tcx)
                .map(|len| mirsa_domains::internval::Internval::new(len as i128, len as i128)),
            TyKind::Slice(_) => state.get_slice_meta(&place),
            _ => None,
        },
        _ => None,
    }?;
    if len_iv.is_empty() {
        return None;
    }
    Some((len_iv.low, len_iv.high))
}

pub(crate) fn index_in_bounds_mirsa<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    result: &PathForwardAnalysisResult<InternvalState<'tcx>>,
    location: mir::Location,
    arr_local: mir::Local,
    idx_local: mir::Local,
) -> bool {
    let Some(state) = query_internval_before_location(tcx, body, result, location) else {
        return false;
    };
    let idx_place = mir::Place::from(idx_local);
    let Some(idx_iv) = state.internval.get(&idx_place).copied() else {
        return false;
    };
    if idx_iv.is_empty() || idx_iv.low < 0 {
        return false;
    }
    let Some((len_low, _len_high)) = local_len(tcx, body, &state, arr_local) else {
        return false;
    };
    idx_iv.high < len_low
}
