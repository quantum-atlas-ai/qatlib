/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma4RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan

/-!
# Endpoint cases of amplitude amplification

The good and bad projections are related to vanishing squared norm. `source_theorem1_zero_angle`
and `source_theorem1_full_angle` describe powers of the standard iterate at marked probability
zero and one. The mathematical context is [BrassardHoyerTapp1998Counting].

## Main statements

* `source_theorem1_zero_angle`: At zero marked probability, every power of the standard iterate
  fixes the prepared state, assuming `A * A.conjTranspose = 1`.
* `source_theorem1_full_angle`: At marked probability one, the `j`th power of the standard
  iterate multiplies the prepared state by `(-1)^j`, assuming `A * A.conjTranspose = 1`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open scoped BigOperators

/-- A finite complex vector is zero if the sum of its squared coordinate norms is zero. -/
theorem source_eq_zero_of_normSq_sum_eq_zero {n : ℕ} (v : Fin (n + 1) → ℂ)
    (h : ∑ i, Complex.normSq (v i) = 0) : v = 0 := by
  funext i
  have hzero : Complex.normSq (v i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg (v j)).mp h i
      (Finset.mem_univ i)
  simpa using Complex.normSq_eq_zero.mp hzero

/-- If the good part vanishes, the bad part equals the whole vector. -/
theorem source_badPart_eq_self {n : ℕ} (g : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℂ)
    (h : goodPart g v = 0) : badPart g v = v := by
  funext i
  have hi : goodPart g v i = 0 := by rw [h]; rfl
  by_cases hg : g i <;> simp [goodPart, badPart, hg] at hi ⊢
  exact hi.symm

/-- If the bad part vanishes, the good part equals the whole vector. -/
theorem source_goodPart_eq_self {n : ℕ} (g : Fin (n + 1) → Bool) (v : Fin (n + 1) → ℂ)
    (h : badPart g v = 0) : goodPart g v = v := by
  funext i
  have hi : badPart g v i = 0 := by rw [h]; rfl
  by_cases hg : g i <;> simp [goodPart, badPart, hg] at hi ⊢
  exact hi.symm

/-- At zero marked probability, every power of the standard iterate fixes the prepared state,
assuming `A * A.conjTranspose = 1`. See [BrassardHoyerTapp1998Counting]. -/
theorem source_theorem1_zero_angle {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1)
    (hzero : ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) = 0) (j : ℕ) :
    ((iterate A g (-1) (-1)) ^ j).mulVec (fun i => A i 0) = fun i => A i 0 := by
  have hgood : goodPart g (fun i => A i 0) = 0 :=
    source_eq_zero_of_normSq_sum_eq_zero _ hzero
  have hbad : badPart g (fun i => A i 0) = fun i => A i 0 :=
    source_badPart_eq_self g _ hgood
  obtain ⟨_, hQb, hb⟩ := zoo_counting_two_dimensional_sign_action n A g hA
  have hbsum : (∑ i, Complex.normSq (badPart g (fun i => A i 0) i)) = 1 := by
    rw [hb, hzero]; norm_num
  have hstep : (iterate A g (-1) (-1)).mulVec (fun i => A i 0) = fun i => A i 0 := by
    rw [← hbad, hQb, hgood, hbsum]
    simp
  induction j with
  | zero => rw [pow_zero, Matrix.one_mulVec]
  | succ j ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hstep]

/-- At marked probability one, the `j`th power of the standard iterate multiplies the prepared
state by `(-1)^j`, assuming `A * A.conjTranspose = 1`. See [BrassardHoyerTapp1998Counting]. -/
theorem source_theorem1_full_angle {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1)
    (hone : ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i) = 1) (j : ℕ) :
    ((iterate A g (-1) (-1)) ^ j).mulVec (fun i => A i 0) =
      ((-1 : ℂ) ^ j) • (fun i => A i 0) := by
  obtain ⟨hQa, _, hb⟩ := zoo_counting_two_dimensional_sign_action n A g hA
  have hbsum : ∑ i, Complex.normSq (badPart g (fun i => A i 0) i) = 0 := by
    rw [hb, hone]; norm_num
  have hbad : badPart g (fun i => A i 0) = 0 :=
    source_eq_zero_of_normSq_sum_eq_zero _ hbsum
  have hgood : goodPart g (fun i => A i 0) = fun i => A i 0 :=
    source_goodPart_eq_self g _ hbad
  have hstep : (iterate A g (-1) (-1)).mulVec (fun i => A i 0) =
      (-1 : ℂ) • (fun i => A i 0) := by
    rw [← hgood, hQa, hbad, hone]
    module
  induction j with
  | zero => rw [pow_zero, Matrix.one_mulVec, pow_zero, one_smul]
  | succ j ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hstep, smul_smul]
      congr 1

end Qatlib.Papers.QCounting98.MainResults
