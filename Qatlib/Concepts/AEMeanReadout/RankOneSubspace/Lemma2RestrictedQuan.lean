/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedStat

/-!
# Good and bad components under a phase iterate

This module derives the action of `RankOneReflection.iterate` on vectors restricted to marked
and unmarked coordinates. It combines the diagonal phase action with the first-column
outer-product identity to obtain the formulas of [BrassardHoyerTapp1998Counting].

## Main statements

* `zoo_counting_good_bad_phase_action`: the iterate formulas on arbitrary good and bad
  components.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

open scoped BigOperators
open scoped Matrix

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

/-- The marked phase diagonal multiplies the good component of any vector by `ϕ`. -/
lemma zoo_counting_good_bad_phase_action_good_eigen
    {n : ℕ} (g : Fin (n + 1) → Bool) (ϕ : ℂ) (v : Fin (n + 1) → ℂ) :
    Matrix.diagonal (fun i => if g i then ϕ else 1) *ᵥ RankOneReflection.goodPart g v =
      ϕ • RankOneReflection.goodPart g v := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : g i <;>
    simp [RankOneReflection.goodPart, h, Pi.smul_apply, smul_eq_mul]

/-- The marked phase diagonal leaves the bad component of any vector unchanged. -/
lemma zoo_counting_good_bad_phase_action_bad_eigen
    {n : ℕ} (g : Fin (n + 1) → Bool) (ϕ : ℂ) (v : Fin (n + 1) → ℂ) :
    Matrix.diagonal (fun i => if g i then ϕ else 1) *ᵥ RankOneReflection.badPart g v =
      (1 : ℂ) • RankOneReflection.badPart g v := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : g i <;>
    simp [RankOneReflection.badPart, h, Pi.smul_apply, smul_eq_mul]

/-- An outer-product matrix sends `w` to its second factor's dot product with `w`, multiplied by
its first factor. -/
lemma zoo_counting_good_bad_phase_action_vecMulVec_mulVec
    {n : ℕ} (u v w : Fin (n + 1) → ℂ) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  show (∑ j, u i * v j * w j) = (∑ j, v j * w j) * u i
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- For an eigenvector of the marked phase diagonal, expands the iterate as minus its eigenvalue
times the vector plus a first-column correction. -/
lemma zoo_counting_good_bad_phase_action_of_eigen
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (φ ϕ ψ : ℂ) (w : Fin (n + 1) → ℂ) (hA : A * A.conjTranspose = 1)
    (hw : Matrix.diagonal (fun i => if g i then ϕ else 1) *ᵥ w = ψ • w) :
    RankOneReflection.iterate A g φ ϕ *ᵥ w =
      (-ψ) • w + (ψ * (1 - φ) * (∑ i, star (A i 0) * w i)) • (fun i => A i 0) := by
  have hM := zoo_counting_rankone_phase_conjugation n A φ hA
  have hvec : Matrix.vecMulVec (fun i => A i 0) (fun j => star (A j 0)) *ᵥ w =
      (∑ i, star (A i 0) * w i) • (fun i => A i 0) := by
    rw [zoo_counting_good_bad_phase_action_vecMulVec_mulVec]
    rfl
  unfold RankOneReflection.iterate
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hM, hw, Matrix.mulVec_smul,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hvec]
  funext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- When `A * A.conjTranspose = 1`, gives explicit first-column correction formulas for the
iterate on the good and bad components of any vector [Brassard et al., Lemma
2][BrassardHoyerTapp1998Counting]. -/
theorem zoo_counting_good_bad_phase_action :
    ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (φ ϕ : ℂ) (v : Fin (n + 1) → ℂ),
  A * A.conjTranspose = 1 →
  (RankOneReflection.iterate A g φ ϕ).mulVec (RankOneReflection.goodPart g v) =
    (-ϕ) • RankOneReflection.goodPart g v +
      (ϕ * (1 - φ) * (∑ i, star (A i 0) * RankOneReflection.goodPart g v i)) • (fun i => A i 0) ∧
  (RankOneReflection.iterate A g φ ϕ).mulVec (RankOneReflection.badPart g v) =
    -RankOneReflection.badPart g v +
      ((1 - φ) * (∑ i, star (A i 0) * RankOneReflection.badPart g v i)) • (fun i => A i 0) := by
  intro n A g φ ϕ v hA
  refine ⟨?_, ?_⟩
  · exact zoo_counting_good_bad_phase_action_of_eigen A g φ ϕ ϕ
      (RankOneReflection.goodPart g v) hA
      (zoo_counting_good_bad_phase_action_good_eigen g ϕ v)
  · have h := zoo_counting_good_bad_phase_action_of_eigen A g φ ϕ (1 : ℂ)
      (RankOneReflection.badPart g v) hA
      (zoo_counting_good_bad_phase_action_bad_eigen g ϕ v)
    rw [neg_one_smul, one_mul] at h
    exact h

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
