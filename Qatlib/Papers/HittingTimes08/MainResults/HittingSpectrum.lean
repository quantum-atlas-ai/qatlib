/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Finite spectral hitting laws

The structure `HittingLaw` records positive spectral values and nonnegative masses without
imposing normalization. This module defines its tail, mean, quantile, and cosine survival sum
and proves tail and quantile estimates used for Theorem 2.3 of [MagniezEtAl2008].

## Main statements

* `tail_quantile_le`: shows the quantile attains the required tail bound for nonnegative error.
* `tail_le_mean_div`: proves the weighted Markov bound.
* `theorem_2_3_first`: transfers a mean comparison to a quantile bound.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators

/-- A finite family of positive real values with nonnegative real masses, without requiring the
masses to sum to one. -/
structure HittingLaw (J : Type*) [Fintype J] where
  val : J → ℝ
  mass : J → ℝ

  val_pos : ∀ j, 0 < val j
  mass_nonneg : ∀ j, 0 ≤ mass j

namespace HittingLaw

variable {J : Type*} [Fintype J]

/-- The reciprocal square root of the spectral value `L.val j`. -/
def theta (L : HittingLaw J) (j : J) : ℝ := 1 / Real.sqrt (L.val j)

/-- The sum of the masses of values strictly greater than `y`. -/
def tail (L : HittingLaw J) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => y < L.val j), L.mass j

/-- The mass-weighted sum of the spectral values. -/
def mean (L : HittingLaw J) : ℝ := ∑ j, L.mass j * L.val j

/-- The sum of all spectral masses. -/
def totalMass (L : HittingLaw J) : ℝ := ∑ j, L.mass j

/-- The unweighted sum of all positive spectral values. -/
def valueSum (L : HittingLaw J) : ℝ := ∑ j, L.val j

/-- The infimum of nonnegative thresholds whose strict upper tail has mass at most `ε`. -/
def quantile (L : HittingLaw J) (ε : ℝ) : ℝ :=
  sInf {y : ℝ | 0 ≤ y ∧ L.tail y ≤ ε}

/-- The weighted cosine-power sum `∑ j, L.mass j * cos (L.theta j) ^ k`. -/
def survival (L : HittingLaw J) (k : ℕ) : ℝ :=
  ∑ j, L.mass j * Real.cos (L.theta j) ^ k

/-- The tail mass at every real threshold is nonnegative. -/
theorem tail_nonneg (L : HittingLaw J) (y : ℝ) : 0 ≤ L.tail y :=
  Finset.sum_nonneg fun j _ => L.mass_nonneg j

/-- Tail mass is nonincreasing as the threshold increases. -/
theorem tail_antitone (L : HittingLaw J) {y y' : ℝ} (h : y ≤ y') :
    L.tail y' ≤ L.tail y := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_le_of_lt h hj
  · intro j _ _; exact L.mass_nonneg j

/-- A tail bound at `y` also holds at every larger threshold `y'`. -/
theorem tail_le_of_le (L : HittingLaw J) {y y' ε : ℝ} (h : y ≤ y')
    (hy : L.tail y ≤ ε) : L.tail y' ≤ ε :=
  (L.tail_antitone h).trans hy

/-- The tail vanishes at the threshold `L.valueSum + 1`. -/
theorem tail_valueSum_add_one (L : HittingLaw J) :
    L.tail (L.valueSum + 1) = 0 := by
  unfold tail
  refine Finset.sum_eq_zero fun j hj => ?_
  have hmem : j ∈ (Finset.univ : Finset J) := Finset.mem_univ j
  have hle : L.val j ≤ L.valueSum := by
    unfold valueSum
    exact Finset.single_le_sum (fun i _ => (L.val_pos i).le) hmem
  rw [Finset.mem_filter] at hj
  linarith [hj.2]

/-- For `ε ≥ 0`, the threshold `L.valueSum + 1` satisfies the tail bound `ε`. -/
theorem feasible_nonempty (L : HittingLaw J) {ε : ℝ} (hε : 0 ≤ ε) :
    (L.tail (L.valueSum + 1) ≤ ε) := by
  rw [L.tail_valueSum_add_one]; exact hε

/-- Every spectral quantile is nonnegative. -/
theorem quantile_nonneg (L : HittingLaw J) (ε : ℝ) : 0 ≤ L.quantile ε := by
  unfold quantile
  exact Real.sInf_nonneg fun y hy => hy.1

/-- For `ε ≥ 0`, the tail at the `ε`-quantile is at most `ε`. -/
theorem tail_quantile_le (L : HittingLaw J) {ε : ℝ} (hε : 0 ≤ ε) :
    L.tail (L.quantile ε) ≤ ε := by
  have hSne : ( {y : ℝ | 0 ≤ y ∧ L.tail y ≤ ε} ).Nonempty := by
    refine ⟨L.valueSum + 1, ?_, L.feasible_nonempty hε⟩
    have : 0 ≤ L.valueSum := by
      unfold valueSum
      exact Finset.sum_nonneg fun i _ => (L.val_pos i).le
    linarith
  have hbdd : BddBelow {y : ℝ | 0 ≤ y ∧ L.tail y ≤ ε} := ⟨0, fun y hy => hy.1⟩

  have hstep : ∀ n : ℕ, L.tail (L.quantile ε + 1 / ((n : ℝ) + 1)) ≤ ε := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : sInf {y : ℝ | 0 ≤ y ∧ L.tail y ≤ ε} <
        L.quantile ε + 1 / ((n : ℝ) + 1) := by
      unfold quantile
      linarith
    obtain ⟨y, hyS, hy⟩ := exists_lt_of_csInf_lt hSne hlt
    exact L.tail_le_of_le hy.le hyS.2
  by_cases hemp : ∃ j, L.quantile ε < L.val j
  · obtain ⟨j0, hj0⟩ := hemp
    let T : Finset J := Finset.univ.filter (fun j => L.quantile ε < L.val j)
    have hTne : T.Nonempty := ⟨j0, by simp [T, hj0]⟩
    let vals : Finset ℝ := T.image L.val
    have hvalsne : vals.Nonempty := hTne.image L.val
    let m : ℝ := vals.min' hvalsne
    have hm_mem : m ∈ vals := Finset.min'_mem vals hvalsne
    obtain ⟨jm, hjmT, hjmm⟩ := Finset.mem_image.mp hm_mem
    have hm_gt : L.quantile ε < m := by
      have : L.quantile ε < L.val jm := (Finset.mem_filter.mp hjmT).2
      simpa [hjmm] using this
    have hm_le : ∀ j, L.quantile ε < L.val j → m ≤ L.val j := by
      intro j hj
      exact Finset.min'_le vals (L.val j) (Finset.mem_image.mpr ⟨j, by simp [T, hj], rfl⟩)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hm_gt)
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hfeas := hstep n
    have hfilter :
        (Finset.univ.filter (fun j => L.quantile ε < L.val j)) =
          Finset.univ.filter (fun j => L.quantile ε + 1 / ((n : ℝ) + 1) < L.val j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hj; linarith [hm_le j hj]
      · intro hj; linarith
    unfold tail at hfeas ⊢
    rw [hfilter]
    exact hfeas
  · have hzero : L.tail (L.quantile ε) = 0 := by
      unfold tail
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter] at hj
      exact absurd ⟨j, hj.2⟩ hemp
    rw [hzero]; exact hε

/-- For a positive threshold `y`, the product of its tail mass with `y` is at most the mean. -/
theorem tail_mul_le_mean (L : HittingLaw J) {y : ℝ} (hy : 0 < y) :
    L.tail y * y ≤ L.mean := by
  unfold tail mean
  rw [Finset.sum_mul]
  calc ∑ j ∈ Finset.univ.filter (fun j => y < L.val j), L.mass j * y
      ≤ ∑ j ∈ Finset.univ.filter (fun j => y < L.val j), L.mass j * L.val j := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : y < L.val j := (Finset.mem_filter.mp hj).2
        nlinarith [L.mass_nonneg j]
    _ ≤ ∑ j, L.mass j * L.val j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro i _ _; exact mul_nonneg (L.mass_nonneg i) (L.val_pos i).le

/-- For `y > 0`, the tail mass is at most `L.mean / y`. -/
theorem tail_le_mean_div (L : HittingLaw J) {y : ℝ} (hy : 0 < y) :
    L.tail y ≤ L.mean / y :=
  (le_div_iff₀ hy).mpr (L.tail_mul_le_mean hy)

/-- If `0 < ε < 1`, `HT > 0`, and `2 * L.mean ≤ HT`, then `L.quantile ε ≤ HT / (2 * ε)`, as in
the first comparison of Theorem 2.3 in [MagniezEtAl2008]. -/
theorem theorem_2_3_first (L : HittingLaw J) (HT ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hHT0 : 0 < HT) (hbridge : 2 * L.mean ≤ HT) :
    L.quantile ε ≤ HT / (2 * ε) := by
  have hy : 0 < HT / (2 * ε) := by positivity
  have htail : L.tail (HT / (2 * ε)) ≤ ε := by
    refine (L.tail_le_mean_div hy).trans ?_
    rw [div_le_iff₀ hy]
    have hcollapse : ε * (HT / (2 * ε)) = HT / 2 := by
      field_simp
    rw [hcollapse]
    nlinarith [hbridge]
  unfold quantile
  refine csInf_le ⟨0, fun y hy => hy.1⟩ ⟨hy.le, htail⟩

/-- If `HT ≤ 4 * L.mean`, total mass is at most one, and a maximal positive value carries mass
at least one half, then `HT ≤ 4 * L.quantile ε` for `0 < ε < 1 / 2`. This is the second
comparison associated with Theorem 2.3 in [MagniezEtAl2008]. -/
theorem theorem_2_3_second (L : HittingLaw J) (HT v1 : ℝ) (j0 : J)
    (hHT : HT ≤ 4 * L.mean)
    (hv1 : 0 < v1) (hval : L.val j0 = v1)
    (hmax : ∀ j, L.val j ≤ v1) (hmass : 1 / 2 ≤ L.mass j0)
    (hTot : L.totalMass ≤ 1) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    HT ≤ 4 * L.quantile ε := by
  have hq : L.quantile ε = v1 := by
    apply le_antisymm
    · unfold quantile
      refine csInf_le ⟨0, fun y hy => hy.1⟩ ⟨hv1.le, ?_⟩
      have hz : L.tail v1 = 0 := by
        unfold tail
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [Finset.mem_filter] at hj
        linarith [hmax j, hj.2]
      rw [hz]; exact hε0.le
    · unfold quantile
      refine le_csInf ?_ ?_
      · refine ⟨L.valueSum + 1, ?_, L.feasible_nonempty hε0.le⟩
        have : 0 ≤ L.valueSum := by
          unfold valueSum
          exact Finset.sum_nonneg fun i _ => (L.val_pos i).le
        linarith
      · intro y hy
        by_contra hlt
        push_neg at hlt
        have hmem : j0 ∈ Finset.univ.filter (fun j => y < L.val j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hval]; exact hlt
        have hge : 1 / 2 ≤ L.tail y := by
          unfold tail
          exact hmass.trans (Finset.single_le_sum (fun i _ => L.mass_nonneg i) hmem)
        linarith [hy.2]
  rw [hq]
  have hmean_le : L.mean ≤ v1 := by
    unfold mean
    calc ∑ j, L.mass j * L.val j ≤ ∑ j, L.mass j * v1 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmax j) (L.mass_nonneg j)
      _ = (L.totalMass) * v1 := by rw [totalMass, Finset.sum_mul]
      _ ≤ 1 * v1 := by
          exact mul_le_mul_of_nonneg_right hTot hv1.le
      _ = v1 := one_mul v1
  nlinarith [hHT, hmean_le]

end HittingLaw

end Qatlib.Papers.HittingTimes08.MainResults
