/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.WalkSpatial08.MainResults.SearchDefs
import Qatlib.Papers.WalkSpatial08.MainResults.ControlledWalkDefs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Sqrt

/-!
# Lattice spectral sums and balanced control bounds

This module defines lattice phase and gap quantities and compares their inverse-gap sums with
harmonic sums. It proves logarithmic upper and lower growth bounds and then evaluates the
balanced control parameter to bound the model phase increment and controlled-walk step count.

The controlled spatial-search setting is described in [Tulsi2008].

## Main statements

* `akr_sum_inv_gap`: two-sided logarithmic bounds for the weighted inverse-gap sum.
* `alphaDeltaStar_lower`: lower bound for the balanced model phase increment.
* `controlledWalkTimeSteps_bound`: eventual step bound proportional to `sqrt (N * log N)`.

## References

* [Tulsi, 2008][Tulsi2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.WalkSpatial08.MainResults

/-- The real logarithm of the number of lattice sites. -/
def logLattice (n : ℕ) : ℝ := Real.log (latticeSize n : ℝ)

/-- The arccosine of the average of the two lattice Fourier cosines at indices `p` and `q`. -/
def theta (n p q : ℕ) : ℝ :=
  Real.arccos
    ((Real.cos (2 * Real.pi * (p : ℝ) / (n : ℝ)) +
        Real.cos (2 * Real.pi * (q : ℝ) / (n : ℝ))) / 2)

/-- The coefficient `1 / sqrt (2 * latticeSize n)`. -/
def aPQ (n : ℕ) : ℝ := 1 / Real.sqrt (2 * (latticeSize n : ℝ))

/-- The coefficient `1 / sqrt (latticeSize n)`. -/
def aZero (n : ℕ) : ℝ := 1 / Real.sqrt (latticeSize n : ℝ)

/-- The folded index `min p (n - p)`, measuring distance to zero around a cycle when `p < n`. -/
def dist (n p : ℕ) : ℕ := min p (n - p)

/-- For an index below `n`, its folded distance is at most `n / 2`. -/
theorem dist_le_half (n p : ℕ) (hp : p < n) : dist n p ≤ n / 2 := by
  unfold dist
  by_cases h : p ≤ n - p
  · rw [Nat.min_eq_left h]
    omega
  · rw [Nat.min_eq_right (by omega)]
    omega

/-- A valid cyclic index has folded distance in the range from zero through `n / 2`. -/
theorem dist_mem_range (n p : ℕ) (hp : p < n) :
    dist n p ∈ Finset.range (n / 2 + 1) := by
  rw [Finset.mem_range]
  have := dist_le_half n p hp
  omega

/-- At most two indices in the range below `n` have any prescribed folded distance. -/
theorem fiber_dist_card (n d : ℕ) :
    ((Finset.range n).filter (fun p => dist n p = d)).card ≤ 2 := by
  unfold dist
  have hsub : (Finset.range n).filter (fun p => min p (n - p) = d) ⊆
      ({d, n - d} : Finset ℕ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpn, hmin⟩ := hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h : p ≤ n - p
    · left
      rw [Nat.min_eq_left h] at hmin
      exact hmin
    · right
      rw [Nat.min_eq_right (by omega)] at hmin
      omega
  calc ((Finset.range n).filter (fun p => min p (n - p) = d)).card
      ≤ ({d, n - d} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

/-- For a nonnegative function, summing over folded cyclic indices is at most twice the sum over
distances through `n / 2`. -/
theorem sum_dist_le (n : ℕ) (φ : ℕ → ℝ) (hφ : ∀ d, 0 ≤ φ d) :
    (∑ p ∈ Finset.range n, φ (dist n p)) ≤
      2 * ∑ d ∈ Finset.range (n / 2 + 1), φ d := by
  unfold dist
  rw [Finset.sum_comp (fun d => φ d) (fun p => min p (n - p))]
  set K := n / 2 with hK
  have himage : Finset.image (fun p => min p (n - p)) (Finset.range n) ⊆
      Finset.range (K + 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    rw [Finset.mem_range] at hp ⊢
    have := dist_le_half n p hp
    unfold dist at this
    omega
  have hcard : ∀ d, ((Finset.range n).filter (fun p => min p (n - p) = d)).card ≤ 2 :=
    fun d => fiber_dist_card n d
  calc (∑ d ∈ Finset.image (fun p => min p (n - p)) (Finset.range n),
          ((Finset.range n).filter (fun p => min p (n - p) = d)).card • φ d)
      ≤ ∑ d ∈ Finset.image (fun p => min p (n - p)) (Finset.range n), (2 : ℕ) • φ d := by
        apply Finset.sum_le_sum
        intro d hd
        rw [nsmul_eq_mul, nsmul_eq_mul]
        have hc : (((Finset.range n).filter (fun p => min p (n - p) = d)).card : ℝ) ≤ 2 := by
          exact_mod_cast hcard d
        exact mul_le_mul_of_nonneg_right hc (hφ d)
    _ = 2 * ∑ d ∈ Finset.image (fun p => min p (n - p)) (Finset.range n), φ d := by
        rw [Finset.sum_nsmul, nsmul_eq_mul]
        ring
    _ ≤ 2 * ∑ d ∈ Finset.range (K + 1), φ d := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum_of_subset_of_nonneg himage
          (fun d _ _ => hφ d)

/-- For natural-number intervals, `Ioc a b` equals `Ico (a + 1) (b + 1)`. -/
theorem Ioc_eq_Ico_succ (a b : ℕ) : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- A finite reciprocal-square tail starting at a natural number `m ≥ 2` is at most `1 / (m -
1)`. -/
theorem sum_range_inv_sq_ge_two (m K : ℕ) (hm : 2 ≤ m) :
    (∑ e ∈ Finset.range K, 1 / (((m + e : ℕ) : ℝ)) ^ 2) ≤ 1 / (((m : ℕ) : ℝ) - 1) := by
  have hconv : (∑ e ∈ Finset.range K, 1 / (((m + e : ℕ) : ℝ)) ^ 2)
      = ∑ i ∈ Finset.Ioc (m - 1) (m + K - 1), ((i : ℝ) ^ 2)⁻¹ := by
    rw [Ioc_eq_Ico_succ,
      show m - 1 + 1 = m by omega, show m + K - 1 + 1 = m + K by omega,
      Finset.sum_Ico_eq_sum_range, show m + K - m = K by omega]
    apply Finset.sum_congr rfl
    intro e he
    have : m + e = m + e := rfl
    rw [one_div, this]
  rw [hconv]
  have hk : m - 1 ≠ 0 := by omega
  have hkn : m - 1 ≤ m + K - 1 := by omega
  have hb := sum_Ioc_inv_sq_le_sub (α := ℝ) hk hkn
  refine le_trans hb ?_
  have hmr : (2 : ℝ) ≤ (m : ℕ) := by exact_mod_cast hm
  have hcast : (((m - 1 : ℕ)) : ℝ) = (m : ℝ) - 1 := by
    have h1 : 1 ≤ m := by omega
    push_cast [h1]; ring
  have hcast2 : (0 : ℝ) ≤ (((m + K - 1 : ℕ)) : ℝ)⁻¹ := by positivity
  rw [hcast]
  have hpos : 0 < (m : ℝ) - 1 := by linarith
  rw [one_div]
  linarith

/-- A finite reciprocal-square sum starting at one is at most two. -/
theorem sum_range_inv_sq_one (K : ℕ) :
    (∑ e ∈ Finset.range K, 1 / (((1 + e : ℕ) : ℝ)) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK; simp
  · have hconv : (∑ e ∈ Finset.range K, 1 / (((1 + e : ℕ) : ℝ)) ^ 2)
        = 1 + ∑ e ∈ Finset.range (K - 1), 1 / (((2 + e : ℕ) : ℝ)) ^ 2 := by
      have hK1 : K = (K - 1) + 1 := by omega
      rw [hK1, Finset.sum_range_succ']
      have key : (∑ k ∈ Finset.range (K - 1), 1 / (((1 + (k + 1) : ℕ) : ℝ)) ^ 2)
          = ∑ k ∈ Finset.range (K - 1), 1 / (((2 + k : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        have h : (1 + (k + 1) : ℕ) = 2 + k := by omega
        rw [h]
      rw [key]
      norm_num
      ring
    rw [hconv]
    have htail := sum_range_inv_sq_ge_two 2 (K - 1) (by norm_num)
    have htail' : (∑ e ∈ Finset.range (K - 1), 1 / (((2 + e : ℕ) : ℝ)) ^ 2) ≤ 1 := by
      refine le_trans htail ?_
      norm_num
    linarith

/-- The reciprocal of `d² + e²` is at most `2 / (d + e)²` for natural `d` and `e`, using
totalized real division. -/
theorem inv_add_sq_le (d e : ℕ) :
    1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2) ≤ 2 / (((d : ℝ) + (e : ℝ)) ^ 2) := by
  have hsq : ((d : ℝ) + (e : ℝ)) ^ 2 ≤ 2 * ((d : ℝ) ^ 2 + (e : ℝ) ^ 2) := by
    nlinarith [sq_nonneg ((d : ℝ) - (e : ℝ))]
  rcases eq_or_ne ((d : ℝ) ^ 2 + (e : ℝ) ^ 2) 0 with h0 | h0
  · have hd0 : (d : ℝ) = 0 := by
      have := sq_nonneg (d : ℝ); have := sq_nonneg (e : ℝ); nlinarith
    have he0 : (e : ℝ) = 0 := by
      have := sq_nonneg (d : ℝ); have := sq_nonneg (e : ℝ); nlinarith
    rw [hd0, he0]; norm_num
  · have hpos : 0 < (d : ℝ) ^ 2 + (e : ℝ) ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have hsum0 : ((d : ℝ) + (e : ℝ)) ≠ 0 := by
      intro h
      have hd0 : (d : ℝ) = 0 := by
        have hdn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
        have hen : (0:ℝ) ≤ (e:ℝ) := Nat.cast_nonneg e
        linarith
      have he0 : (e : ℝ) = 0 := by
        have hdn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
        have hen : (0:ℝ) ≤ (e:ℝ) := Nat.cast_nonneg e
        linarith
      apply h0; rw [hd0, he0]; norm_num
    have hT : 0 < ((d : ℝ) + (e : ℝ)) ^ 2 := by
      apply pow_pos
      exact lt_of_le_of_ne (by positivity) (Ne.symm hsum0)
    rw [div_le_div_iff₀ hpos hT]
    simpa using hsq

/-- The reciprocal-square sum from zero through `K` is at most two, with the zero term
interpreted by real division. -/
theorem sum_range_inv_sq_zero (K : ℕ) :
    (∑ e ∈ Finset.range (K + 1), 1 / (((e : ℕ) : ℝ)) ^ 2) ≤ 2 := by
  rw [Finset.sum_range_succ']
  have hf0 : 1 / (((0 : ℕ) : ℝ)) ^ 2 = 0 := by norm_num
  rw [hf0, add_zero]
  have h := sum_range_inv_sq_one K
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro d hd
  have : ((1 + d : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [this]

/-- The finite reciprocal-square sum starting at natural `d` is at most `4 / (d + 1)`. -/
theorem inner_sq_le (d K : ℕ) :
    (∑ e ∈ Finset.range (K + 1), 1 / (((d + e : ℕ) : ℝ)) ^ 2) ≤ 4 / ((d : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have h0 : (∑ e ∈ Finset.range (K + 1), 1 / (((0 + e : ℕ) : ℝ)) ^ 2) ≤ 2 := by
      simpa using sum_range_inv_sq_zero K
    have : (2 : ℝ) ≤ 4 / ((0 : ℝ) + 1) := by norm_num
    linarith
  · by_cases hd1 : d = 1
    · subst hd1
      have h1 : (∑ e ∈ Finset.range (K + 1), 1 / (((1 + e : ℕ) : ℝ)) ^ 2) ≤ 2 :=
        sum_range_inv_sq_one (K + 1)
      have : (2 : ℝ) ≤ 4 / ((1 : ℝ) + 1) := by norm_num
      linarith
    · have hd2 : 2 ≤ d := by omega
      have hb := sum_range_inv_sq_ge_two d (K + 1) hd2
      refine le_trans hb ?_
      have hp : 0 < (d : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
        linarith
      have hq : 0 < (d : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ hp hq]
      have hdr : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
      nlinarith

/-- The sum of reciprocals from one through `K` equals the `K`th harmonic number cast to the
reals. -/
theorem sum_range_inv_succ_eq_harmonic (K : ℕ) :
    (∑ d ∈ Finset.range K, 1 / ((d : ℝ) + 1)) = (harmonic K : ℝ) := by
  have h1 : (harmonic K : ℝ) = ∑ i ∈ Finset.Icc 1 K, ((i : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [h1, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show K + 1 - 1 = K by omega]
  apply Finset.sum_congr rfl
  intro d hd
  rw [one_div]
  congr 2
  push_cast
  ring

/-- The double reciprocal sum over `d² + e²` for indices zero through `K` is at most eight times
the harmonic number at `K + 1`. -/
theorem sum_inv_add_sq_le (K : ℕ) :
    (∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
        1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2)) ≤ 8 * (harmonic (K + 1) : ℝ) := by
  have hstep : (∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
        1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2))
      ≤ ∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          2 / (((d : ℝ) + (e : ℝ)) ^ 2) := by
    apply Finset.sum_le_sum; intro d hd
    apply Finset.sum_le_sum; intro e he
    exact inv_add_sq_le d e
  have hfac : (∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          2 / (((d : ℝ) + (e : ℝ)) ^ 2))
      = 2 * ∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          1 / (((d : ℝ) + (e : ℝ)) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [mul_one_div]
  have hb : (∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          1 / (((d : ℝ) + (e : ℝ)) ^ 2)) ≤ 4 * (harmonic (K + 1) : ℝ) := by
    have inner : ∀ d : ℕ, (∑ e ∈ Finset.range (K + 1), 1 / (((d : ℝ) + (e : ℝ)) ^ 2))
        ≤ 4 / ((d : ℝ) + 1) := by
      intro d
      have := inner_sq_le d K
      simpa [Nat.cast_add] using this
    calc (∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
            1 / (((d : ℝ) + (e : ℝ)) ^ 2))
        ≤ ∑ d ∈ Finset.range (K + 1), 4 / ((d : ℝ) + 1) := by
          apply Finset.sum_le_sum; intro d hd; exact inner d
      _ = 4 * ∑ d ∈ Finset.range (K + 1), 1 / ((d : ℝ) + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
      _ = 4 * (harmonic (K + 1) : ℝ) := by
          rw [sum_range_inv_succ_eq_harmonic]
  calc (∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2))
      ≤ ∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          2 / (((d : ℝ) + (e : ℝ)) ^ 2) := hstep
    _ = 2 * ∑ d ∈ Finset.range (K + 1), ∑ e ∈ Finset.range (K + 1),
          1 / (((d : ℝ) + (e : ℝ)) ^ 2) := hfac
    _ ≤ 2 * (4 * (harmonic (K + 1) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 8 * (harmonic (K + 1) : ℝ) := by ring

/-- The sum of the squared lattice sines at indices `p` and `q`. -/
def gap (n p q : ℕ) : ℝ :=
  Real.sin (Real.pi * (p : ℝ) / (n : ℝ)) ^ 2 +
    Real.sin (Real.pi * (q : ℝ) / (n : ℝ)) ^ 2

/-- The real cast of the lattice size equals the product of the real side length with itself. -/
theorem latticeSize_real (n : ℕ) : ((latticeSize n : ℕ) : ℝ) = (n : ℝ) * (n : ℝ) := by
  simp [latticeSize, Nat.cast_mul]

/-- For positive side length, the lattice logarithm is twice the logarithm of the side length. -/
theorem logLattice_eq_two_log {n : ℕ} (hn : 0 < n) :
    logLattice n = 2 * Real.log (n : ℝ) := by
  unfold logLattice
  rw [latticeSize_real, show (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 by ring, Real.log_pow]
  push_cast
  ring

/-- For positive side length, the squared coefficient `aPQ n` equals `1 / (2 * n * n)` over the
reals. -/
theorem aPQ_sq {n : ℕ} (hn : 0 < n) :
    (aPQ n) ^ 2 = 1 / (2 * ((n : ℝ) * (n : ℝ))) := by
  unfold aPQ
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) * (n : ℝ)) := by
    have : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [div_pow, one_pow, latticeSize_real, Real.sq_sqrt hpos.le]

/-- For a valid cyclic index, folding its distance preserves the sine of `π * p / n`. -/
theorem sin_dist (n p : ℕ) (hn : 0 < n) (hp : p < n) :
    Real.sin (Real.pi * ((dist n p : ℕ) : ℝ) / (n : ℝ)) =
      Real.sin (Real.pi * (p : ℝ) / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold dist
  by_cases h : p ≤ n - p
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega)]
    have hcast : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
      rw [Nat.cast_sub (by omega)]
    have harg : Real.pi * ((n : ℝ) - (p : ℝ)) / (n : ℝ) =
        Real.pi - Real.pi * (p : ℝ) / (n : ℝ) := by
      field_simp
    rw [hcast, harg, Real.sin_pi_sub]

/-- On indices through `n / 2` with positive `n`, the squared lattice sine is at least `4 * p² /
n²`. -/
theorem sin_sq_ge (n p : ℕ) (hn : 0 < n) (hp : p ≤ n / 2) :
    4 * (p : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ Real.sin (Real.pi * (p : ℝ) / (n : ℝ)) ^ 2 := by
  have h2p : 2 * p ≤ n := by omega
  have h2pR : 2 * (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2p
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 ≤ Real.pi * (p : ℝ) / (n : ℝ) := by positivity
  have hxle : Real.pi * (p : ℝ) / (n : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hnR]
    nlinarith [Real.pi_pos]
  have hmul := Real.mul_le_sin hx0 hxle
  have heq : 2 / Real.pi * (Real.pi * (p : ℝ) / (n : ℝ)) = 2 * (p : ℝ) / (n : ℝ) := by
    field_simp
  rw [heq] at hmul
  have hnn : 0 ≤ 2 * (p : ℝ) / (n : ℝ) := by positivity
  have hsq := pow_le_pow_left₀ hnn hmul 2
  have heq2 : (2 * (p : ℝ) / (n : ℝ)) ^ 2 = 4 * (p : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    field_simp
    ring
  rw [heq2] at hsq
  exact hsq

/-- For valid indices and positive side length, the gap is at least four times the sum of
squared folded distances divided by `n²`. -/
theorem gap_ge (n p q : ℕ) (hn : 0 < n) (hp : p < n) (hq : q < n) :
    4 * ((((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) / (n : ℝ) ^ 2 ≤
      gap n p q := by
  have h1 := sin_sq_ge n (dist n p) hn (dist_le_half n p hp)
  have h2 := sin_sq_ge n (dist n q) hn (dist_le_half n q hq)
  unfold gap
  rw [← sin_dist n p hn hp, ← sin_dist n q hn hq]
  have : 4 * (((dist n p : ℕ) : ℝ) ^ 2) / (n : ℝ) ^ 2 +
      4 * (((dist n q : ℕ) : ℝ) ^ 2) / (n : ℝ) ^ 2 =
      4 * ((((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) / (n : ℝ) ^ 2 := by
    field_simp
  linarith [h1, h2]

/-- For valid indices and positive side length, the inverse gap is bounded by `n²` divided by
four times the sum of squared folded distances. -/
theorem inv_gap_le (n p q : ℕ) (hn : 0 < n) (hp : p < n) (hq : q < n) :
    1 / gap n p q ≤
      (n : ℝ) ^ 2 / (4 * ((((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2))) := by
  set S : ℝ := ((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2 with hSdef
  by_cases hS0 : S = 0
  · have hdp : ((dist n p : ℕ) : ℝ) = 0 := by
      have := sq_nonneg ((dist n p : ℕ) : ℝ)
      have := sq_nonneg ((dist n q : ℕ) : ℝ)
      rw [hSdef] at hS0
      nlinarith
    have hdq : ((dist n q : ℕ) : ℝ) = 0 := by
      have := sq_nonneg ((dist n p : ℕ) : ℝ)
      have := sq_nonneg ((dist n q : ℕ) : ℝ)
      rw [hSdef] at hS0
      nlinarith
    have hdp0 : dist n p = 0 := by exact_mod_cast hdp
    have hdq0 : dist n q = 0 := by exact_mod_cast hdq
    have hp0 : p = 0 := by
      rcases Nat.eq_zero_or_pos p with h | h
      · exact h
      · exfalso
        unfold dist at hdp0
        have : 0 < min p (n - p) := Nat.lt_min.mpr ⟨h, by omega⟩
        omega
    have hq0 : q = 0 := by
      rcases Nat.eq_zero_or_pos q with h | h
      · exact h
      · exfalso
        unfold dist at hdq0
        have : 0 < min q (n - q) := Nat.lt_min.mpr ⟨h, by omega⟩
        omega
    subst hp0; subst hq0
    rw [hSdef] at hS0
    have hgap0 : gap n 0 0 = 0 := by simp [gap]
    rw [hgap0]
    have : (n : ℝ) ^ 2 / (4 * (((dist n 0 : ℕ) : ℝ) ^ 2 + ((dist n 0 : ℕ) : ℝ) ^ 2)) = 0 := by
      rw [show ((dist n 0 : ℕ) : ℝ) = 0 by simp [dist]]
      norm_num
    rw [this]
    norm_num
  · have hSpos : 0 < S := lt_of_le_of_ne (by positivity) (Ne.symm hS0)
    have hge := gap_ge n p q hn hp hq
    have hc : 0 < 4 * S / (n : ℝ) ^ 2 := by
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      positivity
    have h1 := one_div_le_one_div_of_le hc hge
    have heq : 1 / (4 * S / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 / (4 * S) := by
      field_simp
    rw [heq] at h1
    exact h1

/-- For positive indices strictly below a positive side length, the lattice gap is positive. -/
theorem gap_pos (n p q : ℕ) (hn : 0 < n) (hp1 : 1 ≤ p) (hpn : p < n)
    (hq1 : 1 ≤ q) (hqn : q < n) : 0 < gap n p q := by
  unfold gap
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp1
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpp : 0 < Real.pi * (p : ℝ) / (n : ℝ) := by positivity
  have hplt : Real.pi * (p : ℝ) / (n : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hnR]
    have : (p : ℝ) < (n : ℝ) := by exact_mod_cast hpn
    nlinarith [Real.pi_pos]
  have hqq : 0 < Real.pi * (q : ℝ) / (n : ℝ) := by positivity
  have hqlt : Real.pi * (q : ℝ) / (n : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hnR]
    have : (q : ℝ) < (n : ℝ) := by exact_mod_cast hqn
    nlinarith [Real.pi_pos]
  have hsp := Real.sin_pos_of_pos_of_lt_pi hpp hplt
  have hsq := Real.sin_pos_of_pos_of_lt_pi hqq hqlt
  nlinarith [sq_pos_of_ne_zero hsp.ne', sq_pos_of_ne_zero hsq.ne']

/-- For valid indices and positive side length, the gap is at most `π² * (p² + q²) / n²`. -/
theorem gap_le_pi_sq (n p q : ℕ) (hn : 0 < n) (hp : p < n) (hq : q < n) :
    gap n p q ≤ Real.pi ^ 2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpnR : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hp
  have hqnR : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hq
  have hx0p : 0 ≤ Real.pi * (p : ℝ) / (n : ℝ) := by positivity
  have hx0q : 0 ≤ Real.pi * (q : ℝ) / (n : ℝ) := by positivity
  have hxlep : Real.pi * (p : ℝ) / (n : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hnR]; nlinarith [Real.pi_pos]
  have hxleq : Real.pi * (q : ℝ) / (n : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hnR]; nlinarith [Real.pi_pos]
  have hsp := Real.sin_le hx0p
  have hsq := Real.sin_le hx0q
  have hspnn := Real.sin_nonneg_of_nonneg_of_le_pi hx0p hxlep
  have hsqnn := Real.sin_nonneg_of_nonneg_of_le_pi hx0q hxleq
  have h2p := pow_le_pow_left₀ hspnn hsp 2
  have h2q := pow_le_pow_left₀ hsqnn hsq 2
  unfold gap
  have he : (Real.pi * (p : ℝ) / (n : ℝ)) ^ 2 + (Real.pi * (q : ℝ) / (n : ℝ)) ^ 2 =
      Real.pi ^ 2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
    field_simp
  linarith [h2p, h2q]

/-- The double sum over lattice Fourier indices of `aPQ n` squared divided by the gap, using
totalized division at zero gaps. -/
def sumInvGap (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n, (aPQ n) ^ 2 / gap n p q

/-- The real cast of a harmonic number equals the reciprocal sum over the closed interval from
one to its index. -/
theorem harmonic_real_eq_sum (K : ℕ) :
    (harmonic K : ℝ) = ∑ q ∈ Finset.Icc 1 K, ((q : ℝ))⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  ring

/-- The reciprocal sum from one through `K` is at least `log (K + 1)`. -/
theorem sum_Icc_inv_ge_log (K : ℕ) :
    Real.log ((K : ℝ) + 1) ≤ ∑ q ∈ Finset.Icc 1 K, ((q : ℝ))⁻¹ := by
  have htel : (∑ q ∈ Finset.Icc 1 K, Real.log (((q : ℝ) + 1) / (q : ℝ))) =
      Real.log ((K : ℝ) + 1) := by
    induction K with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      have hc1 : ((((k + 1 : ℕ)) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
      have hc2 : ((((k + 1 : ℕ)) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
      rw [hc1, hc2]
      have hstep : Real.log ((k : ℝ) + 1) + Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) =
          Real.log ((k : ℝ) + 2) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      exact hstep
  rw [← htel]
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.mem_Icc] at hq
  obtain ⟨hq1, -⟩ := hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  calc Real.log (((q : ℝ) + 1) / (q : ℝ))
      ≤ (((q : ℝ) + 1) / (q : ℝ)) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = ((q : ℝ))⁻¹ := by
        field_simp
        ring

/-- The double sum of `1 / (p² + q²)` over positive indices through `K` is at least half the
`K`th harmonic number. -/
theorem sum_Icc_inv_add_sq_ge (K : ℕ) :
    (1 / 2) * (harmonic K : ℝ) ≤
      ∑ p ∈ Finset.Icc 1 K, ∑ q ∈ Finset.Icc 1 K, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
  have hinner : ∀ q ∈ Finset.Icc 1 K,
      1 / (2 * (q : ℝ)) ≤ ∑ p ∈ Finset.Icc 1 K, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    obtain ⟨hq1, hqK⟩ := hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hsub : (∑ p ∈ Finset.Icc 1 q, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) ≤
        ∑ p ∈ Finset.Icc 1 K, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_Icc] at hp ⊢
        omega
      · intro p _ _
        positivity
    have hterm : ∀ p ∈ Finset.Icc 1 q, 1 / (2 * (q : ℝ) ^ 2) ≤
        1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
      intro p hp
      rw [Finset.mem_Icc] at hp
      obtain ⟨hp1, hpq⟩ := hp
      have hpR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
      have hle : (p : ℝ) ^ 2 + (q : ℝ) ^ 2 ≤ 2 * (q : ℝ) ^ 2 := by nlinarith
      have hpos : (0 : ℝ) < (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by positivity
      have hpos2 : (0 : ℝ) < 2 * (q : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hpos2 hpos]
      nlinarith
    have hcard : ((Finset.Icc 1 q).card : ℝ) = (q : ℝ) := by
      rw [Nat.card_Icc]
      push_cast
      ring
    have hsum_lb : (q : ℝ) * (1 / (2 * (q : ℝ) ^ 2)) ≤
        ∑ p ∈ Finset.Icc 1 q, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
      calc (q : ℝ) * (1 / (2 * (q : ℝ) ^ 2))
          = (Finset.Icc 1 q).card • (1 / (2 * (q : ℝ) ^ 2)) := by
              rw [nsmul_eq_mul, hcard]
        _ = ∑ p ∈ Finset.Icc 1 q, 1 / (2 * (q : ℝ) ^ 2) := by rw [Finset.sum_const]
        _ ≤ ∑ p ∈ Finset.Icc 1 q, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) :=
              Finset.sum_le_sum hterm
    have hqhalf : (q : ℝ) * (1 / (2 * (q : ℝ) ^ 2)) = 1 / (2 * (q : ℝ)) := by
      field_simp
    rw [hqhalf] at hsum_lb
    linarith [hsum_lb, hsub]
  calc (1 / 2) * (harmonic K : ℝ)
      = (1 / 2) * ∑ q ∈ Finset.Icc 1 K, ((q : ℝ))⁻¹ := by rw [harmonic_real_eq_sum]
    _ = ∑ q ∈ Finset.Icc 1 K, 1 / (2 * (q : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        field_simp
    _ ≤ ∑ q ∈ Finset.Icc 1 K, ∑ p ∈ Finset.Icc 1 K, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) :=
        Finset.sum_le_sum hinner
    _ = ∑ p ∈ Finset.Icc 1 K, ∑ q ∈ Finset.Icc 1 K, 1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) := by
        rw [Finset.sum_comm]

/-- The double reciprocal sum over folded cyclic distances is at most four times the
corresponding sum over distances through `n / 2`. -/
theorem sum_inv_dist_sum_le (n : ℕ) :
    (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
        1 / (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) ≤
      4 * ∑ d ∈ Finset.range (n / 2 + 1), ∑ e ∈ Finset.range (n / 2 + 1),
        1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2) := by
  have step1 : ∀ p : ℕ, (∑ q ∈ Finset.range n,
        1 / (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) ≤
      2 * ∑ e ∈ Finset.range (n / 2 + 1),
        1 / (((dist n p : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2) := by
    intro p
    exact sum_dist_le n (fun e => 1 / (((dist n p : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2))
      (by intro e; positivity)
  have step2 : (∑ p ∈ Finset.range n, ∑ e ∈ Finset.range (n / 2 + 1),
        1 / (((dist n p : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2)) ≤
      2 * ∑ d ∈ Finset.range (n / 2 + 1), ∑ e ∈ Finset.range (n / 2 + 1),
        1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2) := by
    exact sum_dist_le n
      (fun d => ∑ e ∈ Finset.range (n / 2 + 1), 1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2))
      (by intro d; positivity)
  calc (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
        1 / (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2))
      ≤ ∑ p ∈ Finset.range n,
          2 * ∑ e ∈ Finset.range (n / 2 + 1),
            1 / (((dist n p : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2) :=
        Finset.sum_le_sum (fun p _ => step1 p)
    _ = 2 * ∑ p ∈ Finset.range n, ∑ e ∈ Finset.range (n / 2 + 1),
          1 / (((dist n p : ℕ) : ℝ) ^ 2 + (e : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (2 * ∑ d ∈ Finset.range (n / 2 + 1), ∑ e ∈ Finset.range (n / 2 + 1),
          1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left step2 (by norm_num)
    _ = 4 * ∑ d ∈ Finset.range (n / 2 + 1), ∑ e ∈ Finset.range (n / 2 + 1),
          1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2) := by ring

/-- Every lattice gap is nonnegative. -/
theorem gap_nonneg (n p q : ℕ) : 0 ≤ gap n p q := by
  unfold gap
  positivity

/-- Every weighted inverse-gap summand `(aPQ n)² / gap n p q` is nonnegative. -/
theorem term_nonneg (n p q : ℕ) : 0 ≤ (aPQ n) ^ 2 / gap n p q := by
  rw [div_eq_mul_inv]
  exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (gap_nonneg n p q))

/-- For positive side length, the weighted inverse-gap sum is at most four times the harmonic
number at `n / 2 + 1`. -/
theorem sumInvGap_le (n : ℕ) (hn : 0 < n) :
    sumInvGap n ≤ 4 * (harmonic (n / 2 + 1) : ℝ) := by
  unfold sumInvGap
  have key : ∀ a b : ℝ, a ≠ 0 → b ≠ 0 → (1 / (2 * a)) * (a / (4 * b)) = (1 / 8) * (1 / b) := by
    intro a b ha hb
    field_simp
    ring
  have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ p ∈ Finset.range n, ∀ q ∈ Finset.range n,
      (aPQ n) ^ 2 / gap n p q ≤
        (1 / 8) * (1 / (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) := by
    intro p hp q hq
    rw [Finset.mem_range] at hp hq
    have h := inv_gap_le n p q hn hp hq
    have hh : (gap n p q)⁻¹ ≤
        (n : ℝ) ^ 2 / (4 * (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) := by
      rw [← one_div]
      exact h
    have h1 : (aPQ n) ^ 2 / gap n p q ≤
        (aPQ n) ^ 2 * ((n : ℝ) ^ 2 / (4 * (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2))) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    refine le_trans h1 ?_
    rw [aPQ_sq hn]
    by_cases hE : (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2) = 0
    · rw [hE]
      norm_num
    · rw [show (n : ℝ) ^ 2 = (n : ℝ) * (n : ℝ) by ring]
      exact le_of_eq (key ((n : ℝ) * (n : ℝ)) (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)
        (mul_ne_zero hnne hnne) hE)
  calc (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n, (aPQ n) ^ 2 / gap n p q)
      ≤ ∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
          (1 / 8) * (1 / (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact hterm p hp q hq
    _ = (1 / 8) * (∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n,
          1 / (((dist n p : ℕ) : ℝ) ^ 2 + ((dist n q : ℕ) : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
    _ ≤ (1 / 8) * (4 * (∑ d ∈ Finset.range (n / 2 + 1),
          ∑ e ∈ Finset.range (n / 2 + 1), 1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2))) := by
        apply mul_le_mul_of_nonneg_left (sum_inv_dist_sum_le n) (by norm_num)
    _ = (1 / 2) * (∑ d ∈ Finset.range (n / 2 + 1),
          ∑ e ∈ Finset.range (n / 2 + 1), 1 / ((d : ℝ) ^ 2 + (e : ℝ) ^ 2)) := by ring
    _ ≤ (1 / 2) * (8 * (harmonic (n / 2 + 1) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact sum_inv_add_sq_le (n / 2)
    _ = 4 * (harmonic (n / 2 + 1) : ℝ) := by ring

/-- For positive side length, the weighted inverse-gap sum is at least `log (n / 2 + 1) / (4 *
π²)`. -/
theorem sumInvGap_ge (n : ℕ) (hn : 0 < n) :
    (1 / (4 * Real.pi ^ 2)) * Real.log (((n / 2 : ℕ) : ℝ) + 1) ≤ sumInvGap n := by
  have hK : n / 2 < n := by omega
  have hterm : ∀ p ∈ Finset.Icc 1 (n / 2), ∀ q ∈ Finset.Icc 1 (n / 2),
      1 / (2 * Real.pi ^ 2) * (1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) ≤
        (aPQ n) ^ 2 / gap n p q := by
    intro p hp q hq
    rw [Finset.mem_Icc] at hp hq
    obtain ⟨hp1, hpn⟩ := hp
    obtain ⟨hq1, hqn⟩ := hq
    have hpn' : p < n := by omega
    have hqn' : q < n := by omega
    have hgap_pos := gap_pos n p q hn hp1 hpn' hq1 hqn'
    have hgap_le := gap_le_pi_sq n p q hn hpn' hqn'
    rw [aPQ_sq hn, div_eq_mul_inv]
    have hSpos : 0 < Real.pi ^ 2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
      have : 0 < (p : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
        have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
        positivity
      positivity
    have hinv : (Real.pi ^ 2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) / (n : ℝ) ^ 2)⁻¹ ≤
        (gap n p q)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hgap_pos hgap_le
    have hcoef : 0 ≤ 1 / (2 * ((n : ℝ) * (n : ℝ))) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hinv hcoef
    have hleft : (1 / (2 * ((n : ℝ) * (n : ℝ)))) *
        (Real.pi ^ 2 * ((p : ℝ) ^ 2 + (q : ℝ) ^ 2) / (n : ℝ) ^ 2)⁻¹ =
        1 / (2 * Real.pi ^ 2) * (1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) := by
      have hppos : (0:ℝ) < (p:ℝ) ^ 2 + (q:ℝ) ^ 2 := by
        have : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp1
        positivity
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have hpinv : (0:ℝ) < Real.pi ^ 2 * ((p:ℝ) ^ 2 + (q:ℝ) ^ 2) := by positivity
      field_simp
    rw [hleft] at hmul
    exact hmul
  have hsub2 : (∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
        (aPQ n) ^ 2 / gap n p q) ≤
      ∑ p ∈ Finset.range n, ∑ q ∈ Finset.Icc 1 (n / 2), (aPQ n) ^ 2 / gap n p q := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [Finset.mem_Icc, Finset.mem_range] at hp ⊢
      omega
    · intro p hpN hpnot
      apply Finset.sum_nonneg
      intro q hq
      exact term_nonneg n p q
  have hsub3 : (∑ p ∈ Finset.range n, ∑ q ∈ Finset.Icc 1 (n / 2), (aPQ n) ^ 2 / gap n p q)
      ≤ ∑ p ∈ Finset.range n, ∑ q ∈ Finset.range n, (aPQ n) ^ 2 / gap n p q := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      simp only [Finset.mem_Icc, Finset.mem_range] at hq ⊢
      omega
    · intro q hqN hqnot
      exact term_nonneg n p q
  have hlow : (1 / (2 * Real.pi ^ 2)) *
        (∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
          1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) ≤
      ∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
        (aPQ n) ^ 2 / gap n p q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    exact hterm p hp q hq
  have hlogH : Real.log (((n / 2 : ℕ) : ℝ) + 1) ≤ (harmonic (n / 2) : ℝ) := by
    rw [harmonic_real_eq_sum]
    exact sum_Icc_inv_ge_log (n / 2)
  have hsq := sum_Icc_inv_add_sq_ge (n / 2)
  have hchain : (1 / (4 * Real.pi ^ 2)) * Real.log (((n / 2 : ℕ) : ℝ) + 1) ≤
      sumInvGap n := by
    have e1 : (1 / (4 * Real.pi ^ 2)) * Real.log (((n / 2 : ℕ) : ℝ) + 1) ≤
        (1 / (4 * Real.pi ^ 2)) * (harmonic (n / 2) : ℝ) := by
      apply mul_le_mul_of_nonneg_left hlogH
      positivity
    have e2 : (1 / (4 * Real.pi ^ 2)) * (harmonic (n / 2) : ℝ) =
        (1 / (2 * Real.pi ^ 2)) * ((1 / 2) * (harmonic (n / 2) : ℝ)) := by ring
    have e3 : (1 / (2 * Real.pi ^ 2)) * ((1 / 2) * (harmonic (n / 2) : ℝ)) ≤
        (1 / (2 * Real.pi ^ 2)) *
          (∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
            1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left hsq
      positivity
    have e4 : (1 / (2 * Real.pi ^ 2)) *
          (∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
            1 / ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) ≤
        ∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
          (aPQ n) ^ 2 / gap n p q := hlow
    have e5 : (∑ p ∈ Finset.Icc 1 (n / 2), ∑ q ∈ Finset.Icc 1 (n / 2),
          (aPQ n) ^ 2 / gap n p q) ≤ sumInvGap n := by
      unfold sumInvGap
      exact le_trans hsub2 (le_trans hsub3 (le_refl _))
    linarith [e1, e2, e3, e4, e5]
  exact hchain

/-- For all sufficiently large side lengths, the weighted inverse-gap sum lies between positive
constant multiples of the lattice logarithm. See [Main result: O(sqrt(N log N))
two-dimensional spatial search][Tulsi2008]. -/
theorem akr_sum_inv_gap :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      c1 * logLattice n ≤ sumInvGap n ∧ sumInvGap n ≤ c2 * logLattice n := by
  refine ⟨1 / (16 * Real.pi ^ 2), 4, by positivity, by norm_num, 16, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hlogn : (2 : ℝ) ≤ Real.log (n : ℝ) := by
    have h16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog16 : Real.log (16 : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) h16
    have h16eq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have hlog2ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [hlog16, h16eq, hlog2ge]
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  constructor
  · have h := sumInvGap_ge n hn0
    rw [logLattice_eq_two_log hn0]
    have hle1 : (n : ℝ) / 2 ≤ ((n / 2 : ℕ) : ℝ) + 1 := by
      have hdiv : n ≤ 2 * (n / 2) + 2 := by omega
      have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hdiv
      linarith
    have hlogmono : Real.log ((n : ℝ) / 2) ≤ Real.log (((n / 2 : ℕ) : ℝ) + 1) :=
      Real.log_le_log (by positivity) hle1
    have hlogdiv : Real.log ((n : ℝ) / 2) = Real.log (n : ℝ) - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num)]
    have hlowerlog : (1 / 2) * Real.log (n : ℝ) ≤ Real.log (((n / 2 : ℕ) : ℝ) + 1) := by
      nlinarith [hlogmono, hlogdiv, hlog2le1, hlogn]
    have h2 : (1 / (16 * Real.pi ^ 2)) * (2 * Real.log (n : ℝ)) ≤
        (1 / (4 * Real.pi ^ 2)) * Real.log (((n / 2 : ℕ) : ℝ) + 1) := by
      have hstep : (1 / (16 * Real.pi ^ 2)) * (2 * Real.log (n : ℝ)) =
          (1 / (4 * Real.pi ^ 2)) * ((1 / 2) * Real.log (n : ℝ)) := by ring
      rw [hstep]
      exact mul_le_mul_of_nonneg_left hlowerlog (by positivity)
    linarith [h, h2]
  · have h := sumInvGap_le n hn0
    rw [logLattice_eq_two_log hn0]
    have hle2 : ((n / 2 : ℕ) + 1 : ℕ) ≤ n := by omega
    have hle2R : (((n / 2 : ℕ) : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hle2
    have hlog2 : Real.log (((n / 2 : ℕ) : ℝ) + 1) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log
      · have : (0:ℝ) < ((n / 2 : ℕ) : ℝ) + 1 := by positivity
        exact this
      · exact hle2R
    have hH : (harmonic (n / 2 + 1) : ℝ) ≤ 1 + Real.log (n : ℝ) := by
      have hb := harmonic_le_one_add_log (n / 2 + 1)
      push_cast at hb
      linarith [hb, hlog2]
    have : 4 * (harmonic (n / 2 + 1) : ℝ) ≤ 4 * (2 * Real.log (n : ℝ)) := by
      nlinarith [hH, hlogn]
    linarith [h, this]

/-- The balanced control angle `arccos (1 / sqrt (logLattice n))`. -/
def deltaStar (n : ℕ) : ℝ :=
  Real.arccos (1 / Real.sqrt (logLattice n))

/-- The model phase increment `1 / (sqrt (latticeSize n) * sqrt (logLattice n + tan δ² / 4))`. -/
def alphaDelta (n : ℕ) (δ : ℝ) : ℝ :=
  1 / (Real.sqrt (latticeSize n : ℝ) *
    Real.sqrt (logLattice n + (Real.tan δ) ^ 2 / 4))

/-- A lattice logarithm at least one is positive. -/
theorem logLattice_pos {n : ℕ} (hlog : 1 ≤ logLattice n) : 0 < logLattice n :=
  lt_of_lt_of_le zero_lt_one hlog

/-- When the lattice logarithm is at least one, its inverse square root is at most one. -/
theorem one_div_sqrt_log_le_one {n : ℕ} (hlog : 1 ≤ logLattice n) :
    1 / Real.sqrt (logLattice n) ≤ 1 := by
  have hsqrt1 : 1 ≤ Real.sqrt (logLattice n) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hlog
  have hpos : 0 < Real.sqrt (logLattice n) := lt_of_lt_of_le zero_lt_one hsqrt1
  rw [div_le_one hpos]
  exact hsqrt1

/-- When the lattice logarithm is at least one, its inverse square root is at least negative
one. -/
theorem neg_one_le_one_div_sqrt_log {n : ℕ} (hlog : 1 ≤ logLattice n) :
    -1 ≤ 1 / Real.sqrt (logLattice n) := by
  have hpos : 0 ≤ 1 / Real.sqrt (logLattice n) := by positivity
  linarith

/-- When the lattice logarithm is at least one, the cosine of the balanced angle is its inverse
square root. -/
theorem cos_deltaStar {n : ℕ} (hlog : 1 ≤ logLattice n) :
    Real.cos (deltaStar n) = 1 / Real.sqrt (logLattice n) := by
  unfold deltaStar
  exact Real.cos_arccos (neg_one_le_one_div_sqrt_log hlog) (one_div_sqrt_log_le_one hlog)

/-- When the lattice logarithm is at least one, the squared cosine of the balanced angle equals
its reciprocal. -/
theorem sq_cos_deltaStar {n : ℕ} (hlog : 1 ≤ logLattice n) :
    (Real.cos (deltaStar n)) ^ 2 = 1 / logLattice n := by
  rw [cos_deltaStar hlog, div_pow, one_pow,
    Real.sq_sqrt (logLattice_pos hlog).le]

/-- When the lattice logarithm is at least one, the squared sine of the balanced angle equals
one minus its reciprocal. -/
theorem sin_sq_deltaStar {n : ℕ} (hlog : 1 ≤ logLattice n) :
    (Real.sin (deltaStar n)) ^ 2 = 1 - 1 / logLattice n := by
  have h := Real.sin_sq_add_cos_sq (deltaStar n)
  have hc := sq_cos_deltaStar hlog
  linarith

/-- When the lattice logarithm is at least one, the squared tangent of the balanced angle equals
the lattice logarithm minus one. -/
theorem tan_sq_deltaStar {n : ℕ} (hlog : 1 ≤ logLattice n) :
    (Real.tan (deltaStar n)) ^ 2 = logLattice n - 1 := by
  have hL := logLattice_pos hlog
  have hsin := sin_sq_deltaStar hlog
  have hcos := sq_cos_deltaStar hlog
  have hLne : logLattice n ≠ 0 := hL.ne'
  rw [Real.tan_eq_sin_div_cos, div_pow, hsin, hcos]
  field_simp
  try ring

/-- For lattice logarithm at least one, `sqrt (5 * logLattice n - 1)` lies between twice and
three times `sqrt (logLattice n)`. -/
theorem sqrt_five_log_sub_one_bounds {n : ℕ} (hlog : 1 ≤ logLattice n) :
    2 * Real.sqrt (logLattice n) ≤ Real.sqrt (5 * logLattice n - 1) ∧
      Real.sqrt (5 * logLattice n - 1) ≤ 3 * Real.sqrt (logLattice n) := by
  have hL := logLattice_pos hlog
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h9 : Real.sqrt (9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  constructor
  · have h : 4 * logLattice n ≤ 5 * logLattice n - 1 := by linarith
    calc
      2 * Real.sqrt (logLattice n) = Real.sqrt (4 * logLattice n) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4]
      _ ≤ Real.sqrt (5 * logLattice n - 1) := Real.sqrt_le_sqrt h
  · have h : 5 * logLattice n - 1 ≤ 9 * logLattice n := by linarith
    calc
      Real.sqrt (5 * logLattice n - 1) ≤ Real.sqrt (9 * logLattice n) :=
        Real.sqrt_le_sqrt h
      _ = 3 * Real.sqrt (logLattice n) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9), h9]

/-- For positive side length and lattice logarithm at least one, the balanced phase increment
equals `2 / (sqrt (latticeSize n) * sqrt (5 * logLattice n - 1))`. -/
theorem alphaDeltaStar_eq {n : ℕ} (hn : 0 < n) (hlog : 1 ≤ logLattice n) :
    alphaDelta n (deltaStar n) =
      2 / (Real.sqrt (latticeSize n : ℝ) * Real.sqrt (5 * logLattice n - 1)) := by
  have hL := logLattice_pos hlog
  have hsqrtN : 0 < Real.sqrt (latticeSize n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast latticeSize_pos hn)
  have h5 : 0 < 5 * logLattice n - 1 := by linarith
  have hsqrt5 : 0 < Real.sqrt (5 * logLattice n - 1) := Real.sqrt_pos.mpr h5
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold alphaDelta
  rw [tan_sq_deltaStar hlog]
  have harg : logLattice n + (logLattice n - 1) / 4 = (5 * logLattice n - 1) / 4 := by
    ring
  rw [harg]
  have hsq : Real.sqrt ((5 * logLattice n - 1) / 4) =
      Real.sqrt (5 * logLattice n - 1) / 2 := by
    rw [Real.sqrt_div' (5 * logLattice n - 1) (by norm_num : (0 : ℝ) ≤ 4), h4]
  rw [hsq]
  field_simp
  try ring

/-- For positive side length and lattice logarithm at least one, the balanced phase increment is
at least two thirds of the inverse square root of `latticeSize n * logLattice n`. See [Main
result: O(sqrt(N log N)) two-dimensional spatial search][Tulsi2008]. -/
theorem alphaDeltaStar_lower {n : ℕ} (hn : 0 < n) (hlog : 1 ≤ logLattice n) :
    (2 / 3) * (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n)) ≤
      alphaDelta n (deltaStar n) := by
  have hL := logLattice_pos hlog
  have hNpos : 0 < (latticeSize n : ℝ) := by exact_mod_cast latticeSize_pos hn
  have hsqrtN : 0 < Real.sqrt (latticeSize n : ℝ) := Real.sqrt_pos.mpr hNpos
  have hsqrtL : 0 < Real.sqrt (logLattice n) := Real.sqrt_pos.mpr hL
  have h5 : 0 < 5 * logLattice n - 1 := by linarith
  have hsqrt5 : 0 < Real.sqrt (5 * logLattice n - 1) := Real.sqrt_pos.mpr h5
  have hkey : Real.sqrt (5 * logLattice n - 1) ≤ 3 * Real.sqrt (logLattice n) :=
    (sqrt_five_log_sub_one_bounds hlog).2
  have hNL : Real.sqrt ((latticeSize n : ℝ) * logLattice n) =
      Real.sqrt (latticeSize n : ℝ) * Real.sqrt (logLattice n) :=
    Real.sqrt_mul hNpos.le _
  rw [alphaDeltaStar_eq hn hlog, hNL]
  have hX : 0 < Real.sqrt (latticeSize n : ℝ) * (3 * Real.sqrt (logLattice n)) := by
    positivity
  have hY : 0 < Real.sqrt (latticeSize n : ℝ) * Real.sqrt (5 * logLattice n - 1) := by
    positivity
  rw [show (2 / 3) * (1 / (Real.sqrt (latticeSize n : ℝ) * Real.sqrt (logLattice n))) =
      2 / (Real.sqrt (latticeSize n : ℝ) * (3 * Real.sqrt (logLattice n))) by
    field_simp
    try ring]
  rw [div_le_div_iff₀ hX hY]
  have hmul : Real.sqrt (latticeSize n : ℝ) * Real.sqrt (5 * logLattice n - 1) ≤
      Real.sqrt (latticeSize n : ℝ) * (3 * Real.sqrt (logLattice n)) :=
    mul_le_mul_of_nonneg_left hkey hsqrtN.le
  linarith

/-- When the lattice logarithm is at least one, the reciprocal of `cos (deltaStar n) * sqrt
(logLattice n)` equals one. See [Main result: O(sqrt(N log N)) two-dimensional spatial
search][Tulsi2008]. -/
theorem controlled_walk_target_overlap
    (n : ℕ) (hlog : 1 ≤ logLattice n) :
    1 / (Real.cos (deltaStar n) * Real.sqrt (logLattice n)) = 1 := by
  have hcos := cos_deltaStar hlog
  have hsqrtL : 0 < Real.sqrt (logLattice n) := Real.sqrt_pos.mpr (logLattice_pos hlog)
  rw [hcos]
  field_simp

/-- Twice the rounded balanced iteration count plus the rounded square root of the lattice size
for setup. -/
def controlledWalkTimeSteps (n : ℕ) : ℕ :=
  2 * Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n))) +
    Nat.ceil (Real.sqrt (latticeSize n : ℝ))

/-- A lattice side length at least sixteen has lattice logarithm at least one. -/
theorem logLattice_ge_one_of_ge_16 {n : ℕ} (hn : 16 ≤ n) : 1 ≤ logLattice n := by
  have h256 : (0 : ℝ) < (latticeSize 16 : ℝ) := by norm_num [latticeSize]
  have hexp : Real.exp 1 ≤ (latticeSize 16 : ℝ) := by
    have h3 := Real.exp_one_lt_three
    have hval : (latticeSize 16 : ℝ) = 256 := by norm_num [latticeSize]
    rw [hval]
    linarith
  have h16 : 1 ≤ logLattice 16 := by
    unfold logLattice
    exact (Real.le_log_iff_exp_le h256).mpr hexp
  have hmul : latticeSize 16 ≤ latticeSize n := by
    unfold latticeSize
    exact Nat.mul_le_mul hn hn
  have h256le : (latticeSize 16 : ℝ) ≤ (latticeSize n : ℝ) := by exact_mod_cast hmul
  exact le_trans h16 (Real.log_le_log h256 h256le)

/-- For all sufficiently large side lengths, the controlled-walk step count is at most a
positive constant times `sqrtNLatticeLog n`. See [Main result: O(sqrt(N log N))
two-dimensional spatial search][Tulsi2008]. -/
theorem controlledWalkTimeSteps_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (controlledWalkTimeSteps n : ℝ) ≤ C * sqrtNLatticeLog n := by
  refine ⟨7, by norm_num, 16, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hlog : 1 ≤ logLattice n := logLattice_ge_one_of_ge_16 hn
  have hL := logLattice_pos hlog
  have hNpos : 0 < latticeSize n := latticeSize_pos hnpos
  have hNposR : (0 : ℝ) < (latticeSize n : ℝ) := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ (latticeSize n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hNpos)
  have hgpos : 0 < Real.sqrt ((latticeSize n : ℝ) * logLattice n) :=
    Real.sqrt_pos.mpr (mul_pos hNposR hL)
  have hg1 : 1 ≤ Real.sqrt ((latticeSize n : ℝ) * logLattice n) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hmul := mul_le_mul hN1 hlog (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hNposR)
    simpa using hmul
  have halpha := alphaDeltaStar_lower hnpos hlog
  have hlowpos : 0 < (2 / 3) *
      (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n)) := by
    have h1 : 0 < 1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n) :=
      one_div_pos.mpr hgpos
    nlinarith
  have halpha_pos : 0 < alphaDelta n (deltaStar n) := lt_of_lt_of_le hlowpos halpha
  have hratio : Real.pi / (4 * alphaDelta n (deltaStar n)) ≤
      (3 * Real.pi / 8) * Real.sqrt ((latticeSize n : ℝ) * logLattice n) := by
    have hdenα : 0 < 4 * alphaDelta n (deltaStar n) := by nlinarith [halpha_pos]
    have hdenl : 0 < 4 * ((2 / 3) *
        (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n))) := by nlinarith [hlowpos]
    have h4alpha : 4 * ((2 / 3) *
          (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n))) ≤
        4 * alphaDelta n (deltaStar n) := by linarith [halpha]
    have hstep : Real.pi / (4 * alphaDelta n (deltaStar n)) ≤
        Real.pi / (4 * ((2 / 3) *
          (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n)))) := by
      rw [div_le_div_iff₀ hdenα hdenl]
      have hmulpi : Real.pi * (4 * ((2 / 3) *
            (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n)))) ≤
          Real.pi * (4 * alphaDelta n (deltaStar n)) :=
        mul_le_mul_of_nonneg_left h4alpha (le_of_lt Real.pi_pos)
      linarith
    have h2 : Real.pi / (4 * ((2 / 3) *
          (1 / Real.sqrt ((latticeSize n : ℝ) * logLattice n)))) =
        (3 * Real.pi / 8) * Real.sqrt ((latticeSize n : ℝ) * logLattice n) := by
      field_simp
      try ring
    linarith
  have hceil1 : (Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n))) : ℝ) ≤
      (3 * Real.pi / 8) * Real.sqrt ((latticeSize n : ℝ) * logLattice n) + 1 := by
    have hnonneg : 0 ≤ Real.pi / (4 * alphaDelta n (deltaStar n)) :=
      le_of_lt (div_pos Real.pi_pos (by nlinarith [halpha_pos]))
    have h := Nat.ceil_lt_add_one hnonneg
    linarith
  have hceil2 : (Nat.ceil (Real.sqrt (latticeSize n : ℝ)) : ℝ) ≤
      Real.sqrt ((latticeSize n : ℝ) * logLattice n) + 1 := by
    have hnonneg : 0 ≤ Real.sqrt (latticeSize n : ℝ) := le_of_lt (Real.sqrt_pos.mpr hNposR)
    have h := Nat.ceil_lt_add_one hnonneg
    have hleN : Real.sqrt (latticeSize n : ℝ) ≤
        Real.sqrt ((latticeSize n : ℝ) * logLattice n) := by
      apply Real.sqrt_le_sqrt
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hNposR)
      simpa [mul_one] using hmul
    linarith
  have hsqrtNL : sqrtNLatticeLog n = Real.sqrt ((latticeSize n : ℝ) * logLattice n) := rfl
  unfold controlledWalkTimeSteps
  rw [hsqrtNL]
  push_cast
  have hA : (2 : ℝ) * (Nat.ceil (Real.pi / (4 * alphaDelta n (deltaStar n))) : ℝ) ≤
      2 * ((3 * Real.pi / 8) * Real.sqrt ((latticeSize n : ℝ) * logLattice n) + 1) := by
    linarith [hceil1]
  have hpi : 3 * Real.pi / 4 + 4 ≤ 7 := by
    nlinarith [Real.pi_lt_four]
  nlinarith [hA, hceil2, hpi, hg1]

/-- The scale `sqrtNLogLattice n` equals `sqrt (logLattice n)` times `sqrtNLatticeLog n`. -/
theorem sqrtNLogLattice_eq_sqrt_log_mul (n : ℕ) :
    sqrtNLogLattice n = Real.sqrt (logLattice n) * sqrtNLatticeLog n := by
  unfold sqrtNLogLattice sqrtNLatticeLog logLattice
  have hN : (0 : ℝ) ≤ (latticeSize n : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log (latticeSize n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp [latticeSize, Real.log_zero]
    · have h1 : (1 : ℝ) ≤ (latticeSize n : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (latticeSize_pos hn))
      exact Real.log_nonneg h1
  calc
    Real.sqrt (latticeSize n : ℝ) * Real.log (latticeSize n : ℝ)
        = Real.sqrt (latticeSize n : ℝ) *
            Real.sqrt ((Real.log (latticeSize n : ℝ)) ^ 2) := by
          rw [Real.sqrt_sq hl]
    _ = Real.sqrt ((latticeSize n : ℝ) * (Real.log (latticeSize n : ℝ)) ^ 2) := by
          rw [Real.sqrt_mul hN]
    _ = Real.sqrt (Real.log (latticeSize n : ℝ) *
          ((latticeSize n : ℝ) * Real.log (latticeSize n : ℝ))) := by
          congr 1
          ring
    _ = Real.sqrt (Real.log (latticeSize n : ℝ)) *
          Real.sqrt ((latticeSize n : ℝ) * Real.log (latticeSize n : ℝ)) := by
          rw [Real.sqrt_mul hl]

end Qatlib.Papers.WalkSpatial08.MainResults
