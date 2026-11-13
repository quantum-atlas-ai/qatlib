/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence

set_option backward.isDefEq.respectTransparency false

/-!
# Influence Lower Bound for Functions Far from Juntas

This module proves Lemma 2.14: if a Boolean function `f : {0, 1}^n → Bool` is `ε`-far
from every `k`-junta, then for every subset `W ⊆ [n]` of size at most `k`, the Fourier
influence `infSet f (Finset.univ \ W)` outside `W` is at least `ε`.

## Main statements

* `lemma2_14_influence_lower_bound`: `ε ≤ infSet f (Finset.univ \ W)` whenever `W.card ≤ k`.

## References

* [Ambainis et al., 2015][AmbainisBelovsRegevDeWolf2015], Lemma 2.14, Section 2.4, p. 10.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GrpJuntaTest15.MainResults.Junta

open Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel

open Qatlib.Concepts.ShadowModels.BooleanCubeFourier
open Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence

-- The shared Fourier library uses the opposite sign on each coordinate.
private lemma char_eq_signed_cubeChar {n : ℕ} (T : Finset (Fin n))
    (x : Fin n → Bool) : char T x = (-1 : ℝ) ^ T.card * cubeChar T x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [char, cubeChar]
  | @insert i T hi ih =>
    by_cases hx : x i
    · simp [char, Finset.filter_insert, hi, hx, pow_succ, cubeChar] at ih ⊢
      nlinarith
    · simp [char, Finset.filter_insert, hi, hx, pow_succ, cubeChar] at ih ⊢
      nlinarith

private lemma fourierCoeff_sq_eq_uniform {n : ℕ} (f : BoolFun (Fin n))
    (T : Finset (Fin n)) :
    fourierCoeff f T ^ 2 = uniformFourierCoeff T (pm f) ^ 2 := by
  classical
  have hc : fourierCoeff f T = (-1 : ℝ) ^ T.card * uniformFourierCoeff T (pm f) := by
    simp only [fourierCoeff, uniformFourierCoeff, char_eq_signed_cubeChar,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat, one_div]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hc, mul_pow]
  have hs : ((-1 : ℝ) ^ T.card) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm T.card 2, pow_mul]
    norm_num
  rw [hs, one_mul]

private lemma intersects_complement_iff {n : ℕ} (T W : Finset (Fin n)) :
    (T ∩ (Finset.univ \ W)).Nonempty ↔ ¬ T ⊆ W := by
  constructor
  · rintro ⟨i, hi⟩ hsub
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).2).2
      (hsub (Finset.mem_inter.mp hi).1)
  · intro hsub
    obtain ⟨i, hi, hiW⟩ := Finset.not_subset.mp hsub
    exact ⟨i, by simp [hi, hiW]⟩

/-- **Lemma 2.14**: if `f` is `ε`-far from every `k`-junta, then
`ε ≤ infSet f (Finset.univ \ W)` for every `W : Finset (Fin n)` with `W.card ≤ k`. -/
theorem lemma2_14_influence_lower_bound {n : ℕ} (f : BoolFun (Fin n)) {ε : ℝ} {k : ℕ}
    (h : epsFarFromKJunta ε k f) :
    ∀ W : Finset (Fin n), W.card ≤ k → ε ≤ infSet f (Finset.univ \ W) := by
  classical
  intro W hW
  let a : Finset (Fin n) → ℝ := fun T => uniformFourierCoeff T (pm f)
  -- Round the Fourier projection onto the characters supported inside W.
  let p : (Fin n → Bool) → ℝ := fun x =>
    ∑ T : Finset (Fin n), if T ⊆ W then a T * cubeChar T x else 0
  let g : BoolFun (Fin n) := fun x => decide (0 ≤ p x)
  have hg : IsKJunta k g := by
    refine ⟨W, hW, ?_⟩
    intro x y hxy
    have hp : p x = p y := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hT : T ⊆ W
      · simp only [hT, ite_true]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [hxy i (hT hi)]
      · simp [hT]
    simp only [g, hp]
  have hexp (x : Fin n → Bool) : pm f x - p x =
      ∑ T : Finset (Fin n), (if T ⊆ W then 0 else a T) * cubeChar T x := by
    rw [uniform_fourier_inversion (pm f) x]
    change (∑ T, a T * cubeChar T x) -
      (∑ T, if T ⊆ W then a T * cubeChar T x else 0) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : T ⊆ W <;> simp [hT]
  have herr : (∑ x : Fin n → Bool, (pm f x - p x) ^ 2) =
      (2 : ℝ) ^ n * infSet f (Finset.univ \ W) := by
    rw [sum_sq_eq_mul_sum_sq_of_expansion
      (fun T => if T ⊆ W then 0 else a T) (fun x => pm f x - p x) hexp]
    congr 1
    unfold infSet
    apply Finset.sum_congr rfl
    intro T _
    simp only [intersects_complement_iff, fourierCoeff_sq_eq_uniform]
    by_cases hT : T ⊆ W <;> simp [hT, a]
  have hpoint (x : Fin n → Bool) :
      (if f x ≠ g x then (1 : ℝ) else 0) ≤ (pm f x - p x) ^ 2 := by
    cases hf : f x <;> by_cases hp : 0 ≤ p x <;>
      simp only [g, pm, hf, hp, decide_true, decide_false, ne_eq,
        Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
        not_true_eq_false, ite_true, ite_false] <;> nlinarith [sq_nonneg (p x)]
  have hcount : (hammingDist f g : ℝ) =
      ∑ x : Fin n → Bool, if f x ≠ g x then (1 : ℝ) else 0 := by
    simp only [hammingDist, Fintype.card_subtype]
    rw [← Finset.sum_boole]
  have hdist : SourceModel.dist f g ≤ infSet f (Finset.univ \ W) := by
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
    rw [← hcount, herr] at hsum
    unfold SourceModel.dist
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr (by
      simpa [mul_comm] using hsum)
  exact (h g hg).trans hdist

end Qatlib.Papers.GrpJuntaTest15.MainResults.Junta
