/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterError19.MainResults.SourceModel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

/-!
# Two-dimensional square-lattice sums

Lemma F.1, Eq. (229) of arXiv:1912.08854v3. A box of side length `L`
has `L²` sites. Each new shell of radius `r ≥ 1` has `2r + 1`
sites, and their Euclidean distances from the origin are at least `r`.
-/

set_option autoImplicit false

noncomputable section

open Asymptotics Filter MeasureTheory
open scoped BigOperators
open Qatlib.Papers.TrotterError19.MainResults

namespace Qatlib.Papers.TrotterError19.MainResults.Appendices

/-- The inverse-distance weight on the square lattice, with its origin omitted. -/
def squareLatticeWeight (α : ℝ) (i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 0 else ((i : ℝ) ^ 2 + (j : ℝ) ^ 2) ^ (-(α / 2))

/-- The actual sum over a box of side length `L`, including zero weight at the origin. -/
def squareLatticeSum (α : ℝ) (L : ℕ) : ℝ :=
  ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, squareLatticeWeight α i j

/-- The range-sum presentation is exactly the sum over the finite register of lattice sites. -/
theorem squareLatticeSum_eq_sites (α : ℝ) (L : ℕ) :
    squareLatticeSum α L =
      ∑ ij : Fin L × Fin L, squareLatticeWeight α ij.1.val ij.2.val := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∑ j ∈ Finset.range L, squareLatticeWeight α i j)]
  rfl

/-- The weight of a site whose first coordinate is nonzero is bounded by its coordinate weight. -/
private theorem weight_le_first {α : ℝ} (hα : 0 ≤ α) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    squareLatticeWeight α n j ≤ (n : ℝ) ^ (-α) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  simp only [squareLatticeWeight, hn.ne', false_and, ite_false]
  calc
    _ ≤ ((n : ℝ) ^ 2) ^ (-(α / 2)) :=
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hnR) (le_add_of_nonneg_right (sq_nonneg _))
        (by linarith)
    _ = (n : ℝ) ^ (-α) := by
      rw [← Real.rpow_natCast_mul hnR.le]
      congr 1
      norm_num
      ring

/-- Adding one layer adds two strips of length `r` and one corner. -/
private theorem squareLatticeSum_succ (α : ℝ) (r : ℕ) :
    squareLatticeSum α (r + 1) = squareLatticeSum α r +
      (∑ j ∈ Finset.range r, squareLatticeWeight α r j) +
      (∑ i ∈ Finset.range r, squareLatticeWeight α i r) +
      squareLatticeWeight α r r := by
  simp only [squareLatticeSum, Finset.sum_range_succ, Finset.sum_add_distrib]
  abel

/-- Bound the box by its actual sequence of square shells. -/
private theorem box_le_shells {α : ℝ} (hα : 0 ≤ α) {L : ℕ} (hL : 1 ≤ L) :
    squareLatticeSum α L ≤ 3 * ∑ n ∈ Finset.Ico 1 L, (n : ℝ) * (n : ℝ) ^ (-α) := by
  induction L, hL using Nat.le_induction with
  | base => simp [squareLatticeSum, squareLatticeWeight]
  | succ n hn ih =>
      have hn0 : 0 < n := hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      let r : ℝ := (n : ℝ) ^ (-α)
      have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
      have hw (i j : ℕ) : squareLatticeWeight α i j = squareLatticeWeight α j i := by
        simp [squareLatticeWeight, and_comm, add_comm]
      have hleft : (∑ j ∈ Finset.range n, squareLatticeWeight α n j) ≤ (n : ℝ) * r := by
        calc
          _ ≤ ∑ _j ∈ Finset.range n, r := Finset.sum_le_sum (fun j _ => weight_le_first hα hn0 j)
          _ = _ := by simp
      have hright : (∑ i ∈ Finset.range n, squareLatticeWeight α i n) ≤ (n : ℝ) * r := by
        simpa only [hw] using hleft
      have hlast : squareLatticeWeight α n n ≤ (n : ℝ) * r :=
        (weight_le_first hα hn0 n).trans (le_mul_of_one_le_left hr hnR)
      rw [squareLatticeSum_succ, Finset.sum_Ico_succ_top hn, mul_add]
      change squareLatticeSum α n + _ + _ + _ ≤ _ + 3 * ((n : ℝ) * r)
      linarith

/-- The one-dimensional shell-power sum is bounded by a positive-domain power integral. -/
private theorem shells_le_integral {α : ℝ} (hα : 0 ≤ α) {L : ℕ} (hL : 1 ≤ L) :
    (∑ n ∈ Finset.Ico 1 L, (n : ℝ) * (n : ℝ) ^ (-α)) ≤
      (2 : ℝ) ^ α * (∫ x in (1 : ℝ)..(L : ℝ), x ^ (1 - α)) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hzero : (0 : ℝ) ∉ Set.uIcc 1 (L : ℝ) := by
    rw [Set.uIcc_of_le hLr]
    simp
  have hf : IntervalIntegrable (fun x : ℝ => (2 : ℝ) ^ α * x ^ (1 - α)) volume 1 L :=
    (intervalIntegral.intervalIntegrable_rpow (r := 1 - α) (Or.inr hzero)).const_mul _
  have hf' : IntegrableOn (fun x : ℝ => (2 : ℝ) ^ α * x ^ (1 - α)) (Set.Ico (1 : ℝ) L) :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le hLr).mp hf
  have h := sum_Ico_le_integral_of_le (f := fun x => x * x ^ (-α)) hL (g := fun x =>
    (2 : ℝ) ^ α * x ^ (1 - α)) (fun n hn x hx => by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
      have hx0 : 0 < x := by linarith [hx.1]
      have hxin : x / 2 ≤ (n : ℝ) := by
        have hx' : x < (n : ℝ) + 1 := by exact_mod_cast hx.2
        linarith
      have hpow := Real.rpow_le_rpow_of_nonpos (half_pos hx0) hxin (neg_nonpos.mpr hα)
      calc
        (n : ℝ) * (n : ℝ) ^ (-α) ≤ x * (x / 2) ^ (-α) :=
          mul_le_mul hx.1 hpow (Real.rpow_nonneg (by positivity) _) hx0.le
        _ = _ := by
          rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
            div_inv_eq_mul, show 1 - α = 1 + (-α) by ring, Real.rpow_add hx0, Real.rpow_one]
          ring) (by simpa using hf')
  simpa only [intervalIntegral.integral_const_mul, Nat.cast_one] using h

/-- The shell comparison applies at every nonnegative inverse-distance exponent. -/
private theorem box_le_integral {α : ℝ} (hα : 0 ≤ α) {L : ℕ} (hL : 1 ≤ L) :
    squareLatticeSum α L ≤ (3 * (2 : ℝ) ^ α) * (∫ x in (1 : ℝ)..(L : ℝ), x ^ (1 - α)) := by
  rw [mul_assoc]
  exact (box_le_shells hα hL).trans
    (mul_le_mul_of_nonneg_left (shells_le_integral hα hL) (by norm_num : (0 : ℝ) ≤ 3))

/-- Every term in the box sum is nonnegative. -/
private theorem box_nonneg (α : ℝ) (L : ℕ) : 0 ≤ squareLatticeSum α L := by
  unfold squareLatticeSum
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  unfold squareLatticeWeight
  split <;> positivity

/-- A uniform upper bound for the finite two-dimensional box in the subcritical range. -/
theorem lemmaF1_subcritical_two_bound {α : ℝ} (hα : 0 ≤ α) (hsub : α < 2)
    {L : ℕ} (hL : 1 ≤ L) :
    squareLatticeSum α L ≤ (3 * (2 : ℝ) ^ α / (2 - α)) * (L : ℝ) ^ (2 - α) := by
  have h := box_le_integral hα hL
  rw [integral_rpow (Or.inl (by linarith)), show 1 - α + 1 = 2 - α by ring, Real.one_rpow] at h
  calc
    _ ≤ (3 * (2 : ℝ) ^ α) * (((L : ℝ) ^ (2 - α) - 1) / (2 - α)) := h
    _ ≤ (3 * (2 : ℝ) ^ α) * ((L : ℝ) ^ (2 - α) / (2 - α)) := by
      gcongr
      linarith
    _ = _ := by ring

/-- Lemma F.1, Eq. (229): the two-dimensional subcritical box sum is
`O(L^(2-α))`, with side length `L` and the lattice origin omitted. -/
theorem lemmaF1_subcritical_two {α : ℝ} (hα : 0 ≤ α) (hsub : α < 2) :
    BigOAtTop (squareLatticeSum α) (fun L : ℕ => (L : ℝ) ^ (2 - α)) := by
  change (squareLatticeSum α) =O[atTop] (fun L : ℕ => (L : ℝ) ^ (2 - α))
  apply IsBigO.of_bound (3 * (2 : ℝ) ^ α / (2 - α))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
  rw [Real.norm_of_nonneg (box_nonneg α L), Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact lemmaF1_subcritical_two_bound hα hsub hL

/-- The same bound in the paper's site-count convention, with `n = L²`. -/
theorem lemmaF1_subcritical_two_site_count {α : ℝ} (hα : 0 ≤ α) (hsub : α < 2) :
    BigOAtTop (fun L : ℕ => ∑ ij : Fin L × Fin L,
      squareLatticeWeight α ij.1.val ij.2.val)
      (fun L : ℕ => (Fintype.card (Fin L × Fin L) : ℝ) ^ (1 - α / 2)) := by
  have hcard (L : ℕ) : (Fintype.card (Fin L × Fin L) : ℝ) ^ (1 - α / 2) =
      (L : ℝ) ^ (2 - α) := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, ← pow_two,
      ← Real.rpow_natCast_mul (Nat.cast_nonneg L)]
    congr 1
    norm_num
    ring
  simpa only [← squareLatticeSum_eq_sites, hcard] using lemmaF1_subcritical_two hα hsub

/-- At the critical exponent, integrating the shell bound gives an explicit logarithmic bound. -/
theorem lemmaF1_critical_two_bound {L : ℕ} (hL : 1 ≤ L) :
    squareLatticeSum 2 L ≤ 12 * Real.log L := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have h := box_le_integral (α := 2) (by norm_num) hL
  simp_rw [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
    integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hLr, div_one] at h
  norm_num [Real.rpow_ofNat] at h
  exact h

/-- Above the critical exponent, the finite-box sum is uniformly bounded in its side length. -/
theorem lemmaF1_supercritical_two_bound {α : ℝ} (hα : 2 < α) {L : ℕ} (hL : 1 ≤ L) :
    squareLatticeSum α L ≤ 3 * (2 : ℝ) ^ α / (α - 2) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hzero : (0 : ℝ) ∉ Set.uIcc 1 (L : ℝ) := by
    rw [Set.uIcc_of_le hLr]
    simp
  have h := box_le_integral (α := α) (by linarith) hL
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩),
    show 1 - α + 1 = -(α - 2) by ring, Real.one_rpow, div_neg_eq_neg_div, ← neg_div,
    neg_sub, Real.rpow_neg (by positivity : (0 : ℝ) ≤ L)] at h
  calc
    _ ≤ (3 * (2 : ℝ) ^ α) * ((1 - ((L : ℝ) ^ (α - 2))⁻¹) / (α - 2)) := h
    _ ≤ (3 * (2 : ℝ) ^ α) * (1 / (α - 2)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (sub_nonneg.mpr hα.le))
        (by positivity)
    _ = _ := by ring

end Qatlib.Papers.TrotterError19.MainResults.Appendices
