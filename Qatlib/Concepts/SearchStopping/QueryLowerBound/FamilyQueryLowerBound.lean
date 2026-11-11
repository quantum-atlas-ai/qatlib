/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.FixedQueryLowerBound

/-!
# Query lower bounds for families of marked sets

Extends the hybrid argument to families of possibly overlapping query sets. A bound on their
total projected mass yields `family_hybrid_deficit`; combining this with average success and an
overlap budget gives the quadratic lower bound `family_fixed_query_quadratic`. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `family_hybrid_deficit`: For a normalized initial state, agreement off the query sets and a
  total projected-mass bound `c` imply that the summed final projection deficit is at most `2 *
  r ^ 2 * c`.
* `family_fixed_query_quadratic`: For a nonempty family with normalized initial state, overlap
  budget `m * c ≤ Fintype.card J`, the stated agreement and mass bounds, and average success at
  least one half, `(1 - Real.sqrt 2 / 2) * m - Real.sqrt m ≤ 2 * r ^ 2`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

/-- For a normalized initial state, agreement off the query sets and a total projected-mass
bound `c` imply that the summed final projection deficit is at most `2 * r ^ 2 * c`. -/
theorem family_hybrid_deficit {C J : Type*}
    [Fintype C] [DecidableEq C] [Fintype J]
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : J → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (A : ℕ → J → Finset C) (ψ : EuclideanSpace ℂ C) (hψ : ‖ψ‖ = 1)
    (r : ℕ) (c : ℝ)
    (hagree : ∀ y n, n < r → ∀ x, x ∉ A n y →
      V y n (EuclideanSpace.single x 1) = U n (EuclideanSpace.single x 1))
    (hmass : ∀ n, n < r →
      (∑ y : J, ‖QueryProjection (A n y) (UnitaryEvolution U ψ n)‖ ^ 2) ≤ c) :
    (∑ y : J, (1 - ‖QueryProjection (A r y) (UnitaryEvolution U ψ r)‖ -
      ‖QueryProjection (A r y)ᶜ (UnitaryEvolution (V y) ψ r)‖)) ≤ 2 * (r : ℝ) ^ 2 * c := by
  let a (n : ℕ) (y : J) := ‖QueryProjection (A n y) (UnitaryEvolution U ψ n)‖
  let b (y : J) := ‖QueryProjection (A r y)ᶜ (UnitaryEvolution (V y) ψ r)‖
  have hp (y : J) : 1 - a r y - b y ≤
      2 * (r : ℝ) * ∑ n ∈ Finset.range r, a n y ^ 2 := by
    have h1 := hybrid_distance_bound U (V y) (fun n => A n y) ψ r (hagree y)
    have h2 := projection_distance_lower (A r y)
      (UnitaryEvolution U ψ r) (UnitaryEvolution (V y) ψ r)
      (by rw [unitaryEvolution_norm, hψ]) (by rw [unitaryEvolution_norm, hψ])
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range r) (f := fun n => a n y)
    simp only [Finset.card_range] at hc
    have hsq := pow_le_pow_left₀
      (norm_nonneg (UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r)) h1 2
    change 2 * (1 - a r y - b y) ≤ _ at h2
    change ‖UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r‖ ^ 2 ≤
      (2 * ∑ n ∈ Finset.range r, a n y) ^ 2 at hsq
    nlinarith
  change (∑ y : J, (1 - a r y - b y)) ≤ _
  calc
    _ ≤ ∑ y : J, 2 * (r : ℝ) * ∑ n ∈ Finset.range r, a n y ^ 2 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = 2 * (r : ℝ) * ∑ n ∈ Finset.range r, ∑ y : J, a n y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 2 * (r : ℝ) * ∑ _n ∈ Finset.range r, c := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun n hn => hmass n (Finset.mem_range.mp hn))
    _ = _ := by simp; ring

/-- For a nonempty family with normalized initial state, overlap budget `m * c ≤ Fintype.card
J`, the stated agreement and mass bounds, and average success at least one half, `(1 -
Real.sqrt 2 / 2) * m - Real.sqrt m ≤ 2 * r ^ 2`. -/
theorem family_fixed_query_quadratic {C J : Type*}
    [Fintype C] [DecidableEq C] [Fintype J] [Nonempty J]
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : J → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (A : ℕ → J → Finset C) (ψ : EuclideanSpace ℂ C) (hψ : ‖ψ‖ = 1)
    (r m : ℕ) (c : ℝ)
    (hbudget : (m : ℝ) * c ≤ Fintype.card J)
    (hagree : ∀ y n, n < r → ∀ x, x ∉ A n y →
      V y n (EuclideanSpace.single x 1) = U n (EuclideanSpace.single x 1))
    (hmass : ∀ n, n ≤ r →
      (∑ y : J, ‖QueryProjection (A n y) (UnitaryEvolution U ψ n)‖ ^ 2) ≤ c)
    (hsuccess : (Fintype.card J : ℝ) / 2 ≤
      ∑ y : J, ‖QueryProjection (A r y) (UnitaryEvolution (V y) ψ r)‖ ^ 2) :
    (1 - Real.sqrt 2 / 2) * (m : ℝ) - Real.sqrt m ≤ 2 * (r : ℝ) ^ 2 := by
  let a (y : J) := ‖QueryProjection (A r y) (UnitaryEvolution U ψ r)‖
  let b (y : J) := ‖QueryProjection (A r y)ᶜ (UnitaryEvolution (V y) ψ r)‖
  have hM0 : (0 : ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hsuma0 : 0 ≤ ∑ y : J, a y := Finset.sum_nonneg (fun y _ => norm_nonneg _)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  simp only [Finset.card_univ] at hcs
  have hcs' : (∑ y : J, a y) ^ 2 ≤ (Fintype.card J : ℝ) * c :=
    hcs.trans (mul_le_mul_of_nonneg_left (hmass r le_rfl) hM0.le)
  have hroot2 := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
  have hscaled : (Real.sqrt m * ∑ y : J, a y) ^ 2 ≤ (Fintype.card J : ℝ) ^ 2 := by
    rw [mul_pow, hroot2]
    calc
      _ ≤ (m : ℝ) * ((Fintype.card J : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hcs' (Nat.cast_nonneg m)
      _ = (Fintype.card J : ℝ) * ((m : ℝ) * c) := by ring
      _ ≤ (Fintype.card J : ℝ) * Fintype.card J := mul_le_mul_of_nonneg_left hbudget hM0.le
      _ = _ := by ring
  have hroot : Real.sqrt m * (∑ y : J, a y) ≤ Fintype.card J :=
    (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hsuma0) hM0.le).mp hscaled
  have hma : (m : ℝ) * (∑ y : J, a y) ≤ Real.sqrt m * Fintype.card J := by
    calc
      _ = Real.sqrt m * (Real.sqrt m * (∑ y : J, a y)) := by rw [← mul_assoc, ← sq, hroot2]
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
  have hb := average_failure_projection_bound (A r)
    (fun y => UnitaryEvolution (V y) ψ r)
    (fun y => by rw [unitaryEvolution_norm, hψ]) hsuccess
  have hmb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
  have hdef := family_hybrid_deficit U V A ψ hψ r c hagree
    (fun n hn => hmass n hn.le)
  have heq : (∑ y : J, (1 - a y - b y)) = (Fintype.card J : ℝ) -
      (∑ y : J, a y) - ∑ y : J, b y := by simp [Finset.sum_sub_distrib]
  change (∑ y : J, (1 - a y - b y)) ≤ _ at hdef
  rw [heq] at hdef
  have hmd := mul_le_mul_of_nonneg_left hdef (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
  have hmc := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ 2 * (r : ℝ) ^ 2 by positivity)
  change (m : ℝ) * (∑ y : J, b y) ≤ _ at hmb
  apply (mul_le_mul_iff_of_pos_right hM0).mp
  nlinarith only [hmd, hma, hmb, hmc]

end Qatlib.Concepts.SearchStopping.QueryLowerBound
