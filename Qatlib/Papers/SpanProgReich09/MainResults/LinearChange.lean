/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.LinearChange.Pairing
public import Qatlib.Papers.SpanProgReich09.MainResults.Definitions.SpanProgramModel

@[expose] public section


/-! # The actual change of basis in Reichardt's Lemma 4.12

The proof transports the complete feasible cost sets, so it preserves the
original signature even for real cost vectors without a sign restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SpanProgReich09.MainResults
open Qatlib.Foundations.PureStateMath.LinearChange

namespace Qatlib.Papers.SpanProgReich09.MainResults

variable {n : ℕ}

/-- Applying a matrix to every vector commutes with the actual available combination. -/
theorem comboLinear (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (x : BitString n) (w : Fin P.idx → ℂ) :
    (P.applyLin M).combo x w = M *ᵥ P.combo x w := by
  ext r
  simp only [SpanProgram.combo, SpanProgram.applyLin, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change P.piCoeff x j * w j * (M r i * P.vec j i) = _
  ring

/-- A transformed dual coordinate is the original coordinate at the adjoint image. -/
theorem dualLinear (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (u : Fin P.dim → ℂ) (i : Fin P.idx) :
    (P.applyLin M).dualCoord u i = P.dualCoord (Mᴴ *ᵥ u) i := by
  exact inner_mulVec_left_rect M (P.vec i) u

/-- An invertible change of basis preserves the exact positive-witness equation. -/
theorem comboEqIff (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (hM : M.det ≠ 0) (x : BitString n) (w : Fin P.idx → ℂ) :
    (P.applyLin M).combo x w = (P.applyLin M).target ↔ P.combo x w = P.target := by
  rw [comboLinear]
  change M *ᵥ P.combo x w = M *ᵥ P.target ↔ _
  constructor
  · intro h
    have hh := congrArg (fun v => M⁻¹ *ᵥ v) h
    simpa only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), Matrix.one_mulVec] using hh
  · intro h
    rw [h]

/-- The computed Boolean function is unchanged under invertible basis transport. -/
theorem functionEq (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (hM : M.det ≠ 0) (x : BitString n) : (P.applyLin M).fP x = P.fP x := by
  simp only [SpanProgram.fP, comboEqIff P M hM]
  rfl

/-- The whole positive-witness feasible cost set is preserved for arbitrary real costs. -/
theorem trueCostEq (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (hM : M.det ≠ 0) (s : Fin n → ℝ) (x : BitString n) :
    (P.applyLin M).trueCostSet s x = P.trueCostSet s x := by
  ext y
  simp only [SpanProgram.trueCostSet, Set.mem_ofPred_eq, comboEqIff P M hM]
  rfl

/-- The whole negative-witness feasible cost set is preserved by inverse-adjoint transport. -/
theorem falseCostEq (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (hM : M.det ≠ 0) (s : Fin n → ℝ) (x : BitString n) :
    (P.applyLin M).falseCostSet s x = P.falseCostSet s x := by
  ext y
  change (∃ u : Fin P.dim → ℂ,
    Inner (M *ᵥ P.target) u = 1 ∧
      (∀ i, P.Available x i → Inner (M *ᵥ P.vec i) u = 0) ∧
        y = ENNReal.ofReal (∑ i, P.costScale s i * ‖Inner (M *ᵥ P.vec i) u‖ ^ 2)) ↔ _
  simp_rw [inner_mulVec_left_rect]
  constructor
  · rintro ⟨u, ht, hav, hy⟩
    exact ⟨Mᴴ *ᵥ u, ht, hav, hy⟩
  · rintro ⟨u, ht, hav, hy⟩
    refine ⟨(M⁻¹)ᴴ *ᵥ u, ?_⟩
    simpa only [adjInvCancel M hM, SpanProgram.dualCoord] using And.intro ht (And.intro hav hy)

/-- The exact per-input witness size is invariant under an invertible change of basis. -/
theorem witnessSizeEq (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (hM : M.det ≠ 0) (s : Fin n → ℝ) (x : BitString n) :
    (P.applyLin M).witnessSize s x = P.witnessSize s x := by
  simp only [SpanProgram.witnessSize, functionEq P M hM,
    trueCostEq P M hM, falseCostEq P M hM]

/-- Lemma 4.12 preserves both the computed function and every actual witness cost. -/
theorem lemma412 (P : SpanProgram n) (M : Matrix (Fin P.dim) (Fin P.dim) ℂ)
    (hM : M.det ≠ 0) :
    (∀ x : BitString n, (P.applyLin M).fP x = P.fP x) ∧
      ∀ (s : Fin n → ℝ) (x : BitString n),
        (P.applyLin M).witnessSize s x = P.witnessSize s x := by
  exact ⟨functionEq P M hM, witnessSizeEq P M hM⟩

end Qatlib.Papers.SpanProgReich09.MainResults
