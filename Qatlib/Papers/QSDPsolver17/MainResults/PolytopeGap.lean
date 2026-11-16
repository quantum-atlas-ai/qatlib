/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # Missing threshold slack in the legacy approximate-polytope contract.
The counterexample concerns the old Lean statement. The source uses the shifted
threshold c′=ctilde-(r+1)theta and assumes r≥1 in the final slack simplification.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QSDPsolver17.MainResults.PolytopeCounter
open Qatlib.Papers.QSDPsolver17.MainResults

/-- The scalar SDP with zero coefficient, objective and right-hand side. -/
def zeroSdp : SdpData 1 1 where
  A := fun _ => 0
  C := 0
  b := fun _ => 0
  herm_A := fun _ => Matrix.isHermitian_zero
  herm_C := Matrix.isHermitian_zero

/-- The one-dimensional identity is positive semidefinite in the legacy quadratic-form model. -/
theorem psd_scalar_one : PSD (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨Matrix.isHermitian_one, ?_⟩
  intro x
  simpa [Matrix.one_mulVec, Fin.sum_univ_one, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self] using Complex.normSq_nonneg (x 0)

/-- The complete old Lemma 6 contract fails when an allowed trace approximation has positive error. -/
theorem lemma6_counterexample :
    ¬ (∀ {n m : ℕ} (P : SdpData n m)
    (X : Matrix (Fin n) (Fin n) ℂ) (aTilde : Fin m → ℝ) (ctilde α R r θ : ℝ)
    (_hX : PSD X) (_hTrpos : 0 < (Matrix.trace X).re)
    (_hTr : (Matrix.trace X).re ≤ R) (_hR : 0 ≤ R) (_hr : 0 ≤ r) (_hθ : 0 ≤ θ)
    (_ha : ∀ j, |aTilde j - (Matrix.trace (P.A j * X)).re / (Matrix.trace X).re| ≤ θ)
    (_hc : |ctilde - (Matrix.trace (P.C * X)).re / (Matrix.trace X).re| ≤ θ),
    (∀ y, y ∈ Polytope P X α 0 → (∑ j, y j) ≤ r → y ∈ PTilde P aTilde ctilde α r) ∧
    (∀ y, y ∈ PTilde P aTilde ctilde α r → y ∈ Polytope P X α (4 * R * r * θ))) := by
  intro h
  have hp := h zeroSdp (1 : Matrix (Fin 1) (Fin 1) ℂ) (fun _ => 0)
    1 0 1 1 1 psd_scalar_one
    (by norm_num [Matrix.trace, Fin.sum_univ_one])
    (by norm_num [Matrix.trace, Fin.sum_univ_one])
    (by norm_num) (by norm_num) (by norm_num)
    (by intro j; norm_num [zeroSdp, Matrix.trace, Fin.sum_univ_one])
    (by norm_num [zeroSdp, Matrix.trace, Fin.sum_univ_one])
  have hy : (fun _ : Fin 1 => (0 : ℝ)) ∈
      Polytope zeroSdp (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 := by
    simp [Polytope, zeroSdp]
  have ht := hp.1 (fun _ => 0) hy (by norm_num)
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [zeroSdp] using ht.2.2.1
  norm_num at hbad

end Qatlib.Papers.QSDPsolver17.MainResults.PolytopeCounter
