/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

@[expose] public section

/-!
# Right-hand-side normalization in Lemma 53

Scaling only the constraint right-hand sides in arXiv:1705.01843v4
rescales the primal feasible matrices and dual objectives. The dual
feasible vectors and their sparsity are preserved.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix
open Qatlib.Papers.QSDPsolver17.MainResults

namespace Qatlib.Papers.QSDPsolver17.MainResults

variable {n m : ℕ}

/-- Divide only the right-hand sides by `R`, as in Lemma 53. -/
noncomputable def scaleRhs (P : SdpData n m) (R : ℝ) : SdpData n m :=
  { P with b := fun j => P.b j / R }

/-- Scaling right-hand sides preserves the dual cone and nonnegativity constraints. -/
theorem scaleRhs_dualFeasible_iff (P : SdpData n m) (R : ℝ) (y : Fin m → ℝ) :
    (scaleRhs P R).dualFeasible y ↔ P.dualFeasible y :=
  Iff.rfl

/-- The dual objective rescales by `1/R` for every dual vector. -/
private theorem scaleRhs_dualObjective (P : SdpData n m) (R : ℝ) (y : Fin m → ℝ) :
    (scaleRhs P R).dualObjective y = P.dualObjective y / R := by
  simp only [SdpData.dualObjective, scaleRhs, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Optimality up to `ε/R` in the scaled instance is equivalent to
optimality up to `ε` in the original instance. -/
theorem scaleRhs_dualEpsOptimal_iff (P : SdpData n m) (R ε : ℝ) (hR : 0 < R)
    (y : Fin m → ℝ) :
    (scaleRhs P R).dualEpsOptimal y (ε / R) ↔ P.dualEpsOptimal y ε := by
  change (P.dualFeasible y ∧ ∀ z, P.dualFeasible z →
    (scaleRhs P R).dualObjective y ≤ (scaleRhs P R).dualObjective z + ε / R) ↔ _
  simp only [SdpData.dualEpsOptimal, scaleRhs_dualObjective, ← add_div, div_le_div_iff_of_pos_right hR]

/-- Multiplication by a nonnegative real scalar preserves the paper's
quadratic-form definition of positive semidefiniteness. -/
private theorem psd_smul_re (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ)
    (hc : 0 ≤ c) (hX : PSD X) : PSD ((c : ℂ) • X) := by
  refine ⟨hX.1.smul (by simp [IsSelfAdjoint]), ?_⟩
  intro x
  have hsum : (∑ i, star (x i) * (((c : ℂ) • X).mulVec x) i) =
      (c : ℂ) * ∑ i, star (x i) * (X.mulVec x) i := by
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  rw [hsum]
  simpa [Complex.mul_re] using mul_nonneg hc (hX.2 x)

/-- Lemma 53: right-hand-side scaling moves a positive primal trace bound
to one, preserves the optimal dual norm bound, and transports precision. -/
theorem lemma53_rhs_normalization (P : SdpData n m) (R r : ℝ) (hR : 0 < R)
    (htrace : P.traceBound R) (hdual : P.dualL1Bound r) :
    let P' := scaleRhs P R
    P'.traceBound 1 ∧ P'.dualL1Bound r ∧
      ∀ ε : ℝ, ∀ y : Fin m → ℝ, P'.dualEpsOptimal y (ε / R) → P.dualEpsOptimal y ε := by
  dsimp only
  refine ⟨?_, ?_, fun ε y => (scaleRhs_dualEpsOptimal_iff P R ε hR y).mp⟩
  · intro X hX
    have hscaled : P.primalFeasible ((R : ℂ) • X) := by
      refine ⟨psd_smul_re X R hR.le hX.1, fun j => ?_⟩
      have hj : (P.A j * X).trace.re ≤ P.b j / R := hX.2 j
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
      simp
      simpa [mul_comm R] using (le_div_iff₀ hR).mp hj
    have ht := htrace _ hscaled
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re] at ht
    simp at ht
    exact le_of_mul_le_mul_left (by simpa using ht) hR
  · obtain ⟨y, hy, hnorm, hopt⟩ := hdual
    refine ⟨y, hy, hnorm, fun z hz => ?_⟩
    rw [scaleRhs_dualObjective, scaleRhs_dualObjective]
    exact div_le_div_of_nonneg_right (hopt z hz) hR.le

end Qatlib.Papers.QSDPsolver17.MainResults
