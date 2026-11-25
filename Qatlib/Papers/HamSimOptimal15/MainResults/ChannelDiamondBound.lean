/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HamSimOptimal15.MainResults.DiamondNorm
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
public import Qatlib.Foundations.OperatorErrors.OperatorError

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# ChannelDiamondBound — the contraction form of Lemma 7 of arXiv:1501.01715v3

Paper: Berry–Childs–Kothari, *Hamiltonian simulation with nearly optimal
dependence on all parameters*, arXiv:1501.01715v3 (2015-12-07), Lemma 7 on p.9 and
its proof on pp.18–19, eq.(74)–(83).

The published `Qatlib.Papers.HamSimOptimal15.MainResults.lemma7_operator_diamond_norm_le`
handles the case where both conjugation operators are unitary.  The channel form of
Lemma 7 needs the per-input estimate (74)–(76) under the weaker hypothesis that the
first Kraus operator `V₀` of a channel is a contraction, `‖V₀‖ ≤ 1`, which is exactly
what `V₀†V₀ + ∑_j V_j†V_j = 1` provides.  This module supplies that estimate for an
arbitrary raw input matrix and arbitrary finite reference register.

## Main statements

* `traceNorm_conj_sub_le`: the contraction form of (74)–(76),
  `‖U X U† − V₀ X V₀†‖₁ ≤ 2‖U − V₀‖·‖X‖₁`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.ReferenceError.RefTraceError
open scoped Matrix.Norms.L2Operator BigOperators ENNReal

namespace Qatlib.Papers.HamSimOptimal15.MainResults

/-- **Lemma 7, contraction form (74)–(76), arXiv:1501.01715v3 p.18**: for a unitary `U`, a
contraction `V₀` (`‖V₀‖ ≤ 1`) and any raw input matrix `X` on `ℂ^D ⊗ ℂ^r`, the trace-norm
distance of the two amplified conjugations is at most `2‖U − V₀‖·‖X‖₁`.

The paper proves this for `X` a state; the displayed inequality is the linear-in-`X`
form that the diamond-norm assembly in eq.(77)–(83) needs, and it holds for every raw
matrix because no positivity of `X` enters the two-term split
`U X U† − V₀ X V₀† = U X (U† − V₀†) + (U − V₀) X V₀†`. -/
theorem traceNorm_conj_sub_le {D r : ℕ} (U V0 : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (hV0 : ‖V0‖ ≤ 1)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (TensorGate U (1 : Operator r) * X * (TensorGate U (1 : Operator r))ᴴ -
        TensorGate V0 (1 : Operator r) * X * (TensorGate V0 (1 : Operator r))ᴴ) ≤
      2 * ‖U - V0‖ * Matrix.traceNorm X := by
  have hnX : 0 ≤ Matrix.traceNorm X := Matrix.traceNorm_nonneg X
  have hUle : ‖U‖ ≤ 1 := l2_norm_unitary_le_one hU
  have hGle : ∀ M : Operator D, ‖M‖ ≤ 1 → ‖TensorGate M (1 : Operator r)‖ ≤ 1 := by
    intro M hM
    refine (l2_norm_tensorGate M (1 : Operator r)).trans_le ?_
    have h1 : ‖(1 : Operator r)‖ ≤ 1 := l2_norm_one_le
    calc ‖M‖ * ‖(1 : Operator r)‖ ≤ 1 * 1 :=
          mul_le_mul hM h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hGU : ‖TensorGate U (1 : Operator r)‖ ≤ 1 := hGle U hUle
  have hGV0 : ‖TensorGate V0 (1 : Operator r)‖ ≤ 1 := hGle V0 hV0
  have hdiff : ‖TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r)‖ ≤
      ‖U - V0‖ := by
    rw [tensorGate_sub_left]
    refine (l2_norm_tensorGate (U - V0) (1 : Operator r)).trans_le ?_
    calc ‖U - V0‖ * ‖(1 : Operator r)‖ ≤ ‖U - V0‖ * 1 :=
          mul_le_mul_of_nonneg_left l2_norm_one_le (norm_nonneg _)
      _ = ‖U - V0‖ := mul_one _
  have hconj : (TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r))ᴴ
      = (TensorGate U (1 : Operator r))ᴴ - (TensorGate V0 (1 : Operator r))ᴴ :=
    Matrix.conjTranspose_sub _ _
  have hsplit : TensorGate U (1 : Operator r) * X * (TensorGate U (1 : Operator r))ᴴ -
      TensorGate V0 (1 : Operator r) * X * (TensorGate V0 (1 : Operator r))ᴴ
      = TensorGate U (1 : Operator r) * X *
          ((TensorGate U (1 : Operator r))ᴴ - (TensorGate V0 (1 : Operator r))ᴴ) +
        (TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r)) * X *
          (TensorGate V0 (1 : Operator r))ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    noncomm_ring
  rw [hsplit]
  refine (Matrix.traceNorm_add_le _ _).trans ?_
  have h1 : (TensorGate U (1 : Operator r) * X *
      ((TensorGate U (1 : Operator r))ᴴ - (TensorGate V0 (1 : Operator r))ᴴ)).traceNorm
      ≤ ‖U - V0‖ * Matrix.traceNorm X := by
    refine (Matrix.traceNorm_mul_le_traceNorm_opNorm _ _).trans ?_
    have hinner : (TensorGate U (1 : Operator r) * X).traceNorm ≤
        ‖TensorGate U (1 : Operator r)‖ * Matrix.traceNorm X :=
      Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    calc (TensorGate U (1 : Operator r) * X).traceNorm *
          ‖(TensorGate U (1 : Operator r))ᴴ - (TensorGate V0 (1 : Operator r))ᴴ‖
        ≤ (1 * Matrix.traceNorm X) * ‖U - V0‖ := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · exact hinner.trans (mul_le_mul_of_nonneg_right hGU hnX)
          · rw [← hconj, Matrix.l2_opNorm_conjTranspose]
            exact hdiff
      _ = ‖U - V0‖ * Matrix.traceNorm X := by ring
  have h2 : ((TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r)) * X *
      (TensorGate V0 (1 : Operator r))ᴴ).traceNorm ≤ ‖U - V0‖ * Matrix.traceNorm X := by
    refine (Matrix.traceNorm_mul_le_traceNorm_opNorm _ _).trans ?_
    have hinner : ((TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r)) *
        X).traceNorm ≤ ‖U - V0‖ * Matrix.traceNorm X := by
      refine (Matrix.traceNorm_mul_le_opNorm_traceNorm _ _).trans ?_
      calc ‖TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r)‖ *
            Matrix.traceNorm X ≤ ‖U - V0‖ * Matrix.traceNorm X :=
            mul_le_mul_of_nonneg_right hdiff hnX
        _ = _ := rfl
    calc ((TensorGate U (1 : Operator r) - TensorGate V0 (1 : Operator r)) * X).traceNorm *
          ‖(TensorGate V0 (1 : Operator r))ᴴ‖
        ≤ (‖U - V0‖ * Matrix.traceNorm X) * 1 := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · exact hinner
          · rw [Matrix.l2_opNorm_conjTranspose]
            exact hGV0
      _ = ‖U - V0‖ * Matrix.traceNorm X := by ring
  calc _ ≤ ‖U - V0‖ * Matrix.traceNorm X + ‖U - V0‖ * Matrix.traceNorm X := add_le_add h1 h2
    _ = 2 * ‖U - V0‖ * Matrix.traceNorm X := by ring

end Qatlib.Papers.HamSimOptimal15.MainResults
