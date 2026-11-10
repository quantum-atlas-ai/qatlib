/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Lemma6Stat

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators
universe u v

theorem lemma6 : Lemma6.{u, v} := by
  intro C Y _ _ _ _ U V f ψ hψ r hagree
  let A (i : ℕ) (y : Y) := Finset.univ.filter (fun c => f i c = some y)
  let a (i : ℕ) (y : Y) := ‖QueryProjection (A i y) (UnitaryEvolution U ψ i)‖
  let b (y : Y) := ‖QueryProjection (A r y)ᶜ (UnitaryEvolution (V y) ψ r)‖
  have hnorm (W : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C) (n : ℕ) :
      ‖UnitaryEvolution W ψ n‖ = 1 := by rw [unitaryEvolution_norm, hψ]
  have hmass (i : ℕ) : (∑ y : Y, a i y ^ 2) ≤ 1 := by
    have h := query_fiber_mass (f i) (UnitaryEvolution U ψ i)
    simpa only [hnorm, one_pow] using h
  have hfirst (y : Y) : ‖UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r‖ ≤
      2 * ∑ i ∈ Finset.range r, a i y :=
    hybrid_distance_bound U (V y) (fun i => A i y) ψ r
      (fun n hn c hc => hagree y n hn c (by simpa [A] using hc))
  have hsecond (y : Y) : 2 * (1 - a r y - b y) ≤
      ‖UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r‖ ^ 2 :=
    projection_distance_lower (A r y)
      (UnitaryEvolution U ψ r) (UnitaryEvolution (V y) ψ r) (hnorm U r) (hnorm (V y) r)
  refine ⟨hfirst, hsecond, ?_⟩
  have hpoint (y : Y) : 1 - a r y - b y ≤
      2 * (r : ℝ) * ∑ i ∈ Finset.range r, a i y ^ 2 := by
    have h1 := hfirst y
    have h2 := hsecond y
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range r) (f := fun i => a i y)
    simp only [Finset.card_range] at hc
    have hs : 0 ≤ ∑ i ∈ Finset.range r, a i y :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hd := norm_nonneg (UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r)
    have hsq : ‖UnitaryEvolution (V y) ψ r - UnitaryEvolution U ψ r‖ ^ 2 ≤
        (2 * ∑ i ∈ Finset.range r, a i y) ^ 2 := pow_le_pow_left₀ hd h1 2
    change 2 * (1 - a r y - b y) ≤ _ at h2
    nlinarith
  have htotal : (∑ y : Y, (1 - a r y - b y)) ≤ 2 * (r : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ y : Y, 2 * (r : ℝ) * ∑ i ∈ Finset.range r, a i y ^ 2 :=
        Finset.sum_le_sum (fun y _ => hpoint y)
      _ = 2 * (r : ℝ) * ∑ i ∈ Finset.range r, ∑ y : Y, a i y ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 2 * (r : ℝ) * ∑ _i ∈ Finset.range r, (1 : ℝ) := by
        gcongr with i hi
        exact hmass i
      _ = 2 * (r : ℝ) ^ 2 := by simp; ring
  have hfinal : (∑ y : Y, a r y) ≤ Real.sqrt (Fintype.card Y) := by
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a r)
    simp only [Finset.card_univ] at hc
    have hm := mul_le_mul_of_nonneg_left (hmass r)
      (Nat.cast_nonneg (Fintype.card Y) : (0 : ℝ) ≤ _)
    have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card Y) : (0 : ℝ) ≤ _)
    have hpos := Real.sqrt_nonneg (Fintype.card Y : ℝ)
    nlinarith
  have heq : (∑ y : Y, (1 - a r y - b y)) = (Fintype.card Y : ℝ) -
      (∑ y : Y, a r y) - ∑ y : Y, b y := by simp [Finset.sum_sub_distrib]
  change (Fintype.card Y : ℝ) - Real.sqrt (Fintype.card Y) - ∑ y : Y, b y ≤ _
  rw [heq] at htotal
  linarith

end Qatlib.Concepts.SearchStopping.QueryLowerBound
