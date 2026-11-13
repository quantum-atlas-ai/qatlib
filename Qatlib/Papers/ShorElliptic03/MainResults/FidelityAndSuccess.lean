/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

/-!
# Fidelity loss and Fourier readout for elliptic-curve discrete logarithms

`badSlotFraction` and `groupShiftTotalLoss` model the losses from exceptional group additions,
while `euclidTotalIterations` supports a separate accumulated Euclidean loss bound. The Fourier
peak model `peakWeight` yields finite tail bounds and a lower-bound expression
`dlogSuccessLowerBound` that approaches one along powers of two. See [ProosZalka2003] for the
source development.

## Main statements

* `totalFidelityLoss_le`: bounds the sum of `12 * n ^ 2` losses of size at most `1 / n ^ 3` by
  `12 / n`.
* `peak_tail_bound`: bounds the two-sided finite Fourier tail by `2 / Δ`.
* `dlogSuccess_two_pow_close_to_one`: makes the gap in the modeled success lower bound
  arbitrarily small.

## References

* [Proos and Zalka, 2003][ProosZalka2003]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ShorElliptic03.MainResults.FidelityAndSuccess

/-- The real logarithm to base two used in the resource and fidelity formulas. -/
def paperLog2 (x : ℝ) : ℝ := Real.logb 2 x

/-- The modeled exceptional fraction `2 / q` for a group shift over `q` slots. -/
def badSlotFraction (q : ℕ) : ℝ := 2 / (q : ℝ)

/-- The modeled total exceptional loss from `2 * n` group shifts, each contributing
`badSlotFraction q`. -/
def groupShiftTotalLoss (n q : ℕ) : ℝ := 2 * (n : ℝ) * badSlotFraction q

/-- For positive `q`, a set of at most two exceptional slots has uniform fraction at most `2 /
q`. See [ProosZalka2003]. -/
theorem uniform_bad_fraction (q : ℕ) (bad : Finset (Fin q)) (hbad : bad.card ≤ 2)
    (hq : 0 < q) :
    (bad.card : ℝ) / (q : ℝ) ≤ 2 / (q : ℝ) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h : (bad.card : ℝ) ≤ 2 := by exact_mod_cast hbad
  exact div_le_div_of_nonneg_right h (le_of_lt hq')

/-- If every group-shift loss is at most `badSlotFraction q` and `q > 0`, their sum over `2 * n`
shifts is at most `4 * n / q`. See [ProosZalka2003]. -/
theorem groupShiftLoss_le (n q : ℕ) (hq : 0 < q) (loss : ℕ → ℝ)
    (hloss : ∀ i, loss i ≤ badSlotFraction q) :
    ∑ i ∈ Finset.range (2 * n), loss i ≤ 4 * (n : ℝ) / (q : ℝ) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq'
  calc
    ∑ i ∈ Finset.range (2 * n), loss i
        ≤ ∑ _i ∈ Finset.range (2 * n), badSlotFraction q :=
          Finset.sum_le_sum (fun i _ => hloss i)
    _ = (Finset.range (2 * n)).card • badSlotFraction q := by
          rw [Finset.sum_const]
    _ = ((2 * n : ℕ) : ℝ) * badSlotFraction q := by
          rw [Finset.card_range, nsmul_eq_mul]
    _ = (2 * (n : ℝ)) * badSlotFraction q := by
          push_cast
          ring
    _ = 4 * (n : ℝ) / (q : ℝ) := by
          unfold badSlotFraction
          field_simp
          ring

/-- For positive `q`, the modeled total group-shift loss equals `4 * n / q`. See
[ProosZalka2003]. -/
theorem groupShiftTotalLoss_eq (n q : ℕ) (hq : 0 < q) :
    groupShiftTotalLoss n q = 4 * (n : ℝ) / (q : ℝ) := by
  unfold groupShiftTotalLoss badSlotFraction
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq'
  field_simp
  ring

/-- For positive `q`, multiplying `badSlotFraction q` by twice the base-two logarithm of `q`
gives `4 * log₂ q / q`. See [ProosZalka2003]. -/
theorem groupShiftTotalLoss_log2 (q : ℕ) (hq : 0 < q) :
    2 * paperLog2 (q : ℝ) * badSlotFraction q =
      4 * paperLog2 (q : ℝ) / (q : ℝ) := by
  unfold badSlotFraction
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq'
  field_simp
  ring

/-- The real-valued iteration estimate obtained from `8 * n` Euclidean runs with `1.5 * n`
iterations each. -/
def euclidTotalIterations (n : ℕ) : ℝ := 8 * (n : ℝ) * (1.5 * (n : ℝ))

/-- The modeled Euclidean iteration count simplifies to `12 * n ^ 2`. See [ProosZalka2003]. -/
theorem euclidTotalIterations_eq (n : ℕ) :
    euclidTotalIterations n = 12 * (n : ℝ) ^ 2 := by
  unfold euclidTotalIterations
  ring

/-- For `n ≥ 1`, the sum of `12 * n ^ 2` losses, each at most `1 / n ^ 3`, is at most `12 / n`.
See [ProosZalka2003]. -/
theorem totalFidelityLoss_le (n : ℕ) (hn : 1 ≤ n) (loss : ℕ → ℝ)
    (hloss : ∀ i, loss i ≤ 1 / (n : ℝ) ^ 3) :
    ∑ i ∈ Finset.range (12 * n ^ 2), loss i ≤ 12 / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  calc
    ∑ i ∈ Finset.range (12 * n ^ 2), loss i
        ≤ ∑ _i ∈ Finset.range (12 * n ^ 2), (1 / (n : ℝ) ^ 3) :=
          Finset.sum_le_sum (fun i _ => hloss i)
    _ = ((12 * n ^ 2 : ℕ) : ℝ) * (1 / (n : ℝ) ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = 12 * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 3) := by
          push_cast
          ring
    _ = 12 / (n : ℝ) := by
          field_simp

/-- The squared sine-ratio Fourier peak weight at offset `d + δ`, with value one when that
offset vanishes. -/
def peakWeight (N : ℕ) (δ : ℝ) (d : ℤ) : ℝ :=
  if (d : ℝ) + δ = 0 then 1
  else
    (Real.sin (Real.pi * ((d : ℝ) + δ)) /
        ((N : ℝ) * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)))) ^ 2

/-- The real-valued readout window `N / (2 * q)` for register size `N` and group size `q`. -/
def readoutWindow (N q : ℕ) : ℝ := (N : ℝ) / (2 * (q : ℝ))

/-- The modeled discrete-logarithm success lower bound `1 - 8 * q / N`. -/
def dlogSuccessLowerBound (N q : ℕ) : ℝ := 1 - 8 * (q : ℝ) / (N : ℝ)

/-- For positive `N` and nonzero offset `d + δ` whose scaled angle has magnitude at most `π /
2`, the peak weight is at most `1 / (4 * (d + δ) ^ 2)`. See [ProosZalka2003]. -/
theorem peakWeight_le_inv_four_sq (N : ℕ) (δ : ℝ) (d : ℤ)
    (hN : 0 < N) (hne : (d : ℝ) + δ ≠ 0)
    (hangle : |Real.pi * ((d : ℝ) + δ) / (N : ℝ)| ≤ Real.pi / 2) :
    peakWeight N δ d ≤ 1 / (4 * ((d : ℝ) + δ) ^ 2) := by
  unfold peakWeight
  rw [ite_eq_right hne]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_pow, mul_pow]
  have hsin : (2 / Real.pi) * |Real.pi * ((d : ℝ) + δ) / (N : ℝ)|
      ≤ |Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ))| := Real.mul_abs_le_abs_sin hangle
  have hsin' : 2 * |(d : ℝ) + δ| / (N : ℝ)
      ≤ |Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ))| := by
    have heq : (2 / Real.pi) * |Real.pi * ((d : ℝ) + δ) / (N : ℝ)|
        = 2 * |(d : ℝ) + δ| / (N : ℝ) := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hNpos]
      field_simp
    rwa [heq] at hsin
  have hsq : (2 * |(d : ℝ) + δ| / (N : ℝ)) ^ 2
      ≤ Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2 := by
    have h1 : 0 ≤ 2 * |(d : ℝ) + δ| / (N : ℝ) := by positivity
    have h2 : 0 ≤ |Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ))| := abs_nonneg _
    nlinarith [hsin', h1, h2, sq_abs (Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)))]
  have hdenpos : 0 < (N : ℝ) ^ 2 * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2 := by
    have hb : 0 < Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2 := by
      have hpos : 0 < 2 * |(d : ℝ) + δ| / (N : ℝ) := by positivity
      have hlt := lt_of_lt_of_le hpos hsin'
      have habs2 : 0 < |Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ))| ^ 2 := pow_pos hlt 2
      rwa [sq_abs] at habs2
    positivity
  have hnum : Real.sin (Real.pi * ((d : ℝ) + δ)) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hstep1 : Real.sin (Real.pi * ((d : ℝ) + δ)) ^ 2
        / ((N : ℝ) ^ 2 * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2)
      ≤ 1 / ((N : ℝ) ^ 2 * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2) := by
    exact div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
  have hx2 : 0 < ((d : ℝ) + δ) ^ 2 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · nlinarith [mul_pos_of_neg_of_neg hlt hlt]
    · nlinarith [mul_pos hgt hgt]
  have hspos : 0 < 4 * ((d : ℝ) + δ) ^ 2 := by positivity
  have hle : 4 * ((d : ℝ) + δ) ^ 2
      ≤ (N : ℝ) ^ 2 * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2 := by
    have h4 : (2 * |(d : ℝ) + δ| / (N : ℝ)) ^ 2
        = 4 * ((d : ℝ) + δ) ^ 2 / (N : ℝ) ^ 2 := by
      rw [div_pow, mul_pow, sq_abs]; ring
    rw [h4, div_le_iff₀ (by positivity)] at hsq
    nlinarith [hsq]
  calc
    Real.sin (Real.pi * ((d : ℝ) + δ)) ^ 2
        / ((N : ℝ) ^ 2 * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2)
        ≤ 1 / ((N : ℝ) ^ 2 * Real.sin (Real.pi * ((d : ℝ) + δ) / (N : ℝ)) ^ 2) := hstep1
    _ ≤ 1 / (4 * ((d : ℝ) + δ) ^ 2) := one_div_le_one_div_of_le hspos hle

/-- For `a ≥ 2`, every finite sum of reciprocal squares starting at `a` is at most `1 / (a -
1)`. -/
lemma sum_range_inv_sq_le (a n : ℕ) (ha : 2 ≤ a) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / ((a : ℝ) + (i : ℝ)) ^ 2) ≤ 1 / ((a : ℝ) - 1) := by
  have ha1 : (1 : ℝ) ≤ (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hpt : ∀ i ∈ Finset.range n,
      (1 : ℝ) / ((a : ℝ) + (i : ℝ)) ^ 2
        ≤ 1 / ((a : ℝ) - 1 + (i : ℝ)) - 1 / ((a : ℝ) + (i : ℝ)) := by
    intro i _
    have hi : (0 : ℝ) ≤ (i : ℝ) := by positivity
    have hx : (0 : ℝ) < (a : ℝ) - 1 + (i : ℝ) := by linarith
    have hy : (0 : ℝ) < (a : ℝ) + (i : ℝ) := by linarith
    have hid : 1 / ((a : ℝ) - 1 + (i : ℝ)) - 1 / ((a : ℝ) + (i : ℝ))
        = 1 / (((a : ℝ) - 1 + (i : ℝ)) * ((a : ℝ) + (i : ℝ))) := by
      field_simp
      ring
    rw [hid]
    have hprod : 0 < ((a : ℝ) - 1 + (i : ℝ)) * ((a : ℝ) + (i : ℝ)) := mul_pos hx hy
    have hle : ((a : ℝ) - 1 + (i : ℝ)) * ((a : ℝ) + (i : ℝ))
        ≤ ((a : ℝ) + (i : ℝ)) ^ 2 := by nlinarith [hx, hy]
    exact one_div_le_one_div_of_le hprod hle
  have htel : ∀ n, (∑ i ∈ Finset.range n,
        ((1 : ℝ) / ((a : ℝ) - 1 + (i : ℝ)) - 1 / ((a : ℝ) - 1 + ((i : ℝ) + 1))))
      = 1 / ((a : ℝ) - 1) - 1 / ((a : ℝ) - 1 + (n : ℝ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have hconv : (∑ i ∈ Finset.range n,
        (1 / ((a : ℝ) - 1 + (i : ℝ)) - 1 / ((a : ℝ) + (i : ℝ))))
      = ∑ i ∈ Finset.range n,
        ((1 : ℝ) / ((a : ℝ) - 1 + (i : ℝ)) - 1 / ((a : ℝ) - 1 + ((i : ℝ) + 1))) := by
    apply Finset.sum_congr rfl
    intro i _
    have hd : (a : ℝ) + (i : ℝ) = (a : ℝ) - 1 + ((i : ℝ) + 1) := by ring
    rw [hd]
  calc
    ∑ i ∈ Finset.range n, (1 : ℝ) / ((a : ℝ) + (i : ℝ)) ^ 2
        ≤ ∑ i ∈ Finset.range n,
            (1 / ((a : ℝ) - 1 + (i : ℝ)) - 1 / ((a : ℝ) + (i : ℝ))) :=
          Finset.sum_le_sum hpt
    _ = 1 / ((a : ℝ) - 1) - 1 / ((a : ℝ) - 1 + (n : ℝ)) := by rw [hconv, htel n]
    _ ≤ 1 / ((a : ℝ) - 1) := by
          have hpos : 0 < ((a : ℝ) - 1 + (n : ℝ)) := by
            have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
            linarith
          have hle : 0 ≤ 1 / ((a : ℝ) - 1 + (n : ℝ)) := by positivity
          linarith

/-- For `a ≥ 1`, every finite sum of reciprocal squares starting at `a` is at most `2 / a`. -/
lemma sum_range_inv_sq_le_two (a n : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / ((a : ℝ) + (i : ℝ)) ^ 2) ≤ 2 / (a : ℝ) := by
  by_cases ha1 : a = 1
  · rw [ha1]
    cases n with
    | zero => norm_num
    | succ m =>
        rw [Finset.sum_range_succ']
        push_cast
        have hsh : (∑ i ∈ Finset.range m, (1 : ℝ) / ((1 : ℝ) + ((i : ℝ) + 1)) ^ 2)
            = ∑ i ∈ Finset.range m, (1 : ℝ) / ((2 : ℝ) + (i : ℝ)) ^ 2 := by
          apply Finset.sum_congr rfl; intro i _; ring_nf
        rw [hsh]
        have hbound := sum_range_inv_sq_le 2 m (by norm_num)
        norm_num at hbound
        have hone : (1 : ℝ) / ((1 : ℝ) + (0:ℝ)) ^ 2 = 1 := by norm_num
        rw [hone]
        norm_num
        linarith
  · have ha2' : 2 ≤ a := by omega
    have hb := sum_range_inv_sq_le a n ha2'
    have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2'
    have hle : 1 / ((a : ℝ) - 1) ≤ 2 / (a : ℝ) := by
      have h1 : (0 : ℝ) < (a : ℝ) := by linarith
      have h2 : (0 : ℝ) < (a : ℝ) - 1 := by linarith
      field_simp
      nlinarith
    linarith

/-- For `0 ≤ δ < 1`, `2 ≤ j ≤ K`, and `2 * (K + 1) ≤ N`, the positive-offset peak weight is at
most `1 / (4 * j ^ 2)`. -/
lemma peakWeight_pos_le (N K : ℕ) (δ : ℝ) (j : ℕ)
    (hN : 0 < N) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hKj : j ≤ K)
    (hKN : 2 * (K + 1) ≤ N) (hj : 2 ≤ j) :
    peakWeight N δ (j : ℤ) ≤ 1 / (4 * (j : ℝ) ^ 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hcast : ((j : ℤ) : ℝ) = (j : ℝ) := by push_cast; ring
  have hne : ((j : ℤ) : ℝ) + δ ≠ 0 := by
    intro h0
    rw [hcast] at h0
    have hpos : (0:ℝ) < (j:ℝ) + δ := by linarith
    linarith
  have hangle : |Real.pi * (((j : ℤ) : ℝ) + δ) / (N : ℝ)| ≤ Real.pi / 2 := by
    rw [hcast]
    have hKjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKj
    have hKN' : (2 : ℝ) * ((K : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hKN
    have hnum : (j : ℝ) + δ < (N : ℝ) / 2 := by linarith
    have hnum0 : 0 ≤ (j : ℝ) + δ := by linarith
    rw [abs_of_nonneg (by positivity)]
    have hratio : ((j : ℝ) + δ) / (N : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hNpos]; linarith
    have hpi := Real.pi_pos
    have hmul : Real.pi * (((j : ℝ) + δ) / (N : ℝ)) ≤ Real.pi * (1 / 2) :=
      mul_le_mul_of_nonneg_left hratio (le_of_lt hpi)
    calc Real.pi * ((j : ℝ) + δ) / (N : ℝ)
        = Real.pi * (((j : ℝ) + δ) / (N : ℝ)) := by ring
      _ ≤ Real.pi * (1 / 2) := hmul
      _ = Real.pi / 2 := by ring
  have hspos : (0 : ℝ) < 4 * (j : ℝ) ^ 2 := by
    have : (0:ℝ) < (j:ℝ) := by linarith
    positivity
  calc peakWeight N δ (j : ℤ) ≤ 1 / (4 * (((j : ℤ) : ℝ) + δ) ^ 2) :=
        peakWeight_le_inv_four_sq N δ (j : ℤ) hN hne hangle
    _ ≤ 1 / (4 * (j : ℝ) ^ 2) := by
        rw [hcast]
        apply one_div_le_one_div_of_le hspos
        nlinarith [hjR, hδ0]

/-- For `0 ≤ δ < 1`, `2 ≤ j ≤ K`, and `2 * (K + 1) ≤ N`, the negative-offset peak weight is at
most `1 / (4 * (j - 1) ^ 2)`. -/
lemma peakWeight_neg_le (N K : ℕ) (δ : ℝ) (j : ℕ)
    (hN : 0 < N) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hKj : j ≤ K)
    (hKN : 2 * (K + 1) ≤ N) (hj : 2 ≤ j) :
    peakWeight N δ (-(j : ℤ)) ≤ 1 / (4 * ((j : ℝ) - 1) ^ 2) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  let j' : ℤ := -(j : ℤ)
  have hcast : (j' : ℝ) = -(j : ℝ) := by unfold j'; push_cast; ring
  have hne : (j' : ℝ) + δ ≠ 0 := by
    rw [hcast]
    have hneg0 : (-(j:ℝ)) + δ < 0 := by linarith
    linarith
  have hangle : |Real.pi * ((j' : ℝ) + δ) / (N : ℝ)| ≤ Real.pi / 2 := by
    rw [hcast]
    have hKjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKj
    have hKN' : (2 : ℝ) * ((K : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hKN
    have hnum : -(j : ℝ) + δ < 0 := by linarith
    have habs : |Real.pi * (-(j : ℝ) + δ) / (N : ℝ)|
        = Real.pi * ((j : ℝ) - δ) / (N : ℝ) := by
      have hx : Real.pi * (-(j : ℝ) + δ) / (N : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · have := Real.pi_pos; nlinarith
        · positivity
      rw [abs_of_nonpos hx]
      have hneg : -(Real.pi * (-(j : ℝ) + δ) / (N : ℝ))
          = Real.pi * ((j : ℝ) - δ) / (N : ℝ) := by ring
      rw [hneg]
    rw [habs]
    have hle : (j : ℝ) - δ ≤ (N : ℝ) / 2 := by linarith
    have hratio : ((j : ℝ) - δ) / (N : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hNpos]; linarith
    have hnonneg : 0 ≤ Real.pi * ((j : ℝ) - δ) / (N : ℝ) := by
      have : 0 ≤ (j : ℝ) - δ := by linarith
      positivity
    have hpi := Real.pi_pos
    have hmul : Real.pi * (((j : ℝ) - δ) / (N : ℝ)) ≤ Real.pi * (1 / 2) :=
      mul_le_mul_of_nonneg_left hratio (le_of_lt hpi)
    calc Real.pi * ((j : ℝ) - δ) / (N : ℝ)
        = Real.pi * (((j : ℝ) - δ) / (N : ℝ)) := by ring
      _ ≤ Real.pi * (1 / 2) := hmul
      _ = Real.pi / 2 := by ring
  have hspos : (0 : ℝ) < 4 * ((j : ℝ) - 1) ^ 2 := by
    have : (0:ℝ) < (j:ℝ) - 1 := by linarith
    positivity
  have hmain : peakWeight N δ j' ≤ 1 / (4 * ((j : ℝ) - 1) ^ 2) := by
    calc peakWeight N δ j' ≤ 1 / (4 * ((j' : ℝ) + δ) ^ 2) :=
          peakWeight_le_inv_four_sq N δ j' hN hne hangle
      _ ≤ 1 / (4 * ((j : ℝ) - 1) ^ 2) := by
          rw [hcast]
          apply one_div_le_one_div_of_le hspos
          have hgt : (j : ℝ) - 1 < (j : ℝ) - δ := by linarith
          nlinarith [hjR]
  exact hmain

/-- For `0 ≤ δ < 1`, `1 ≤ Δ ≤ K`, and `2 * (K + 1) ≤ N`, the sum of the positive and negative
peak weights from `Δ + 1` through `K` is at most `2 / Δ`. See [ProosZalka2003]. -/
theorem peak_tail_bound (N K : ℕ) (δ : ℝ) (Δ : ℕ)
    (_hK : 1 ≤ K) (hN : 2 * (K + 1) ≤ N)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hΔ1 : 1 ≤ Δ) (hΔK : Δ ≤ K) :
    (∑ j ∈ Finset.Ico (Δ + 1) (K + 1),
        (peakWeight N δ (j : ℤ) + peakWeight N δ (-(j : ℤ)))) ≤ 2 / (Δ : ℝ) := by
  have hNpos : 0 < N := by omega
  rcases Nat.lt_or_ge Δ K with hDK | hKD
  · rw [Finset.sum_Ico_eq_sum_range]
    rw [show (K + 1) - (Δ + 1) = K - Δ by omega]
    rw [Finset.sum_add_distrib]
    have hA : (∑ i ∈ Finset.range (K - Δ), peakWeight N δ (((Δ + 1 + i : ℕ) : ℤ)))
        ≤ 1 / (4 * (Δ : ℝ)) := by
      have hstep : (∑ i ∈ Finset.range (K - Δ), peakWeight N δ (((Δ + 1 + i : ℕ) : ℤ)))
          ≤ ∑ i ∈ Finset.range (K - Δ),
              1 / (4 * (((Δ + 1 + i : ℕ) : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact peakWeight_pos_le N K δ (Δ + 1 + i) hNpos hδ0 hδ1 (by omega) hN (by omega)
      have hstep2 : (∑ i ∈ Finset.range (K - Δ),
            1 / (4 * (((Δ + 1 + i : ℕ) : ℝ)) ^ 2))
          = (1 / 4) * ∑ i ∈ Finset.range (K - Δ),
              1 / (((Δ + 1 + i : ℕ) : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      have hstep3 : (∑ i ∈ Finset.range (K - Δ),
            1 / (((Δ + 1 + i : ℕ) : ℝ)) ^ 2) ≤ 1 / (Δ : ℝ) := by
        have h := sum_range_inv_sq_le (Δ + 1) (K - Δ) (by omega)
        calc (∑ i ∈ Finset.range (K - Δ), (1:ℝ) / (((Δ + 1 + i : ℕ) : ℝ)) ^ 2)
            = ∑ i ∈ Finset.range (K - Δ),
                (1:ℝ) / (((Δ + 1 : ℕ) : ℝ) + (i : ℝ)) ^ 2 := by
              apply Finset.sum_congr rfl; intro i _; push_cast; ring
          _ ≤ 1 / (((Δ + 1 : ℕ) : ℝ) - 1) := h
          _ = 1 / (Δ : ℝ) := by push_cast; ring
      calc (∑ i ∈ Finset.range (K - Δ), peakWeight N δ (((Δ + 1 + i : ℕ) : ℤ)))
          ≤ ∑ i ∈ Finset.range (K - Δ), 1 / (4 * (((Δ + 1 + i : ℕ) : ℝ)) ^ 2) := hstep
        _ = (1 / 4) * ∑ i ∈ Finset.range (K - Δ), 1 / (((Δ + 1 + i : ℕ) : ℝ)) ^ 2 := hstep2
        _ ≤ (1 / 4) * (1 / (Δ : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hstep3 (by norm_num)
        _ = 1 / (4 * (Δ : ℝ)) := by ring
    have hB : (∑ i ∈ Finset.range (K - Δ), peakWeight N δ (-(((Δ + 1 + i : ℕ) : ℤ))))
        ≤ 1 / (2 * (Δ : ℝ)) := by
      have hstep : (∑ i ∈ Finset.range (K - Δ), peakWeight N δ (-(((Δ + 1 + i : ℕ) : ℤ))))
          ≤ ∑ i ∈ Finset.range (K - Δ),
              1 / (4 * ((((Δ + 1 + i : ℕ) : ℝ)) - 1) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact peakWeight_neg_le N K δ (Δ + 1 + i) hNpos hδ0 hδ1 (by omega) hN (by omega)
      have hstep2 : (∑ i ∈ Finset.range (K - Δ),
            1 / (4 * ((((Δ + 1 + i : ℕ) : ℝ)) - 1) ^ 2))
          = (1 / 4) * ∑ i ∈ Finset.range (K - Δ),
              1 / (((Δ + 1 + i : ℕ) : ℝ) - 1) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hxpos : (0:ℝ) < ((Δ + 1 + i : ℕ) : ℝ) - 1 := by
          have h2 : (2:ℝ) ≤ ((Δ + 1 + i : ℕ) : ℝ) := by
            have : 2 ≤ Δ + 1 + i := by omega
            exact_mod_cast this
          linarith
        field_simp
      have hstep3 : (∑ i ∈ Finset.range (K - Δ),
            1 / (((Δ + 1 + i : ℕ) : ℝ) - 1) ^ 2) ≤ 2 / (Δ : ℝ) := by
        have h := sum_range_inv_sq_le_two Δ (K - Δ) hΔ1
        calc (∑ i ∈ Finset.range (K - Δ), (1:ℝ) / (((Δ + 1 + i : ℕ) : ℝ) - 1) ^ 2)
            = ∑ i ∈ Finset.range (K - Δ), (1:ℝ) / ((Δ : ℝ) + (i : ℝ)) ^ 2 := by
              apply Finset.sum_congr rfl; intro i _; push_cast; ring
          _ ≤ 2 / (Δ : ℝ) := h
      calc (∑ i ∈ Finset.range (K - Δ), peakWeight N δ (-(((Δ + 1 + i : ℕ) : ℤ))))
          ≤ ∑ i ∈ Finset.range (K - Δ), 1 / (4 * ((((Δ + 1 + i : ℕ) : ℝ)) - 1) ^ 2) := hstep
        _ = (1 / 4) * ∑ i ∈ Finset.range (K - Δ), 1 / (((Δ + 1 + i : ℕ) : ℝ) - 1) ^ 2 := hstep2
        _ ≤ (1 / 4) * (2 / (Δ : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hstep3 (by norm_num)
        _ = 1 / (2 * (Δ : ℝ)) := by ring
    have hsum := add_le_add hA hB
    have hfinal : 1 / (4 * (Δ : ℝ)) + 1 / (2 * (Δ : ℝ)) ≤ 2 / (Δ : ℝ) := by
      have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ1
      have hr : (0 : ℝ) ≤ 1 / (Δ : ℝ) := by positivity
      have e1 : 1 / (4 * (Δ : ℝ)) = (1/4) * (1/(Δ:ℝ)) := by ring
      have e2 : 1 / (2 * (Δ : ℝ)) = (1/2) * (1/(Δ:ℝ)) := by ring
      have e3 : 2 / (Δ : ℝ) = 2 * (1/(Δ:ℝ)) := by ring
      rw [e1, e2, e3]
      nlinarith
    linarith
  · have hΔeq : Δ = K := by omega
    rw [show K = Δ from hΔeq.symm]
    have hempty : (∑ j ∈ Finset.Ico (Δ + 1) (Δ + 1),
        (peakWeight N δ (j : ℤ) + peakWeight N δ (-(j : ℤ)))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      omega
    rw [hempty]
    have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast hΔ1
    positivity

/-- For positive `N` and `q`, twice the reciprocal of the readout window equals `4 * q / N`. See
[ProosZalka2003]. -/
theorem peakTail_window (N q : ℕ) (hN : 0 < N) (hq : 0 < q) :
    2 / readoutWindow N q = 4 * (q : ℝ) / (N : ℝ) := by
  unfold readoutWindow
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  field_simp
  ring

/-- If both register tails are at most `2 / readoutWindow N q` and `N, q > 0`, then
`dlogSuccessLowerBound N q` is at most one minus their sum. See [ProosZalka2003]. -/
theorem dlog_success_of_register_tails (N q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (tailx taily : ℝ) (hx : tailx ≤ 2 / readoutWindow N q)
    (hy : taily ≤ 2 / readoutWindow N q) :
    dlogSuccessLowerBound N q ≤ 1 - (tailx + taily) := by
  rw [peakTail_window N q hN hq] at hx hy
  unfold dlogSuccessLowerBound
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN'
  have heq : 4 * (q : ℝ) / (N : ℝ) + 4 * (q : ℝ) / (N : ℝ) =
      8 * (q : ℝ) / (N : ℝ) := by
    field_simp
    ring
  have hsum : tailx + taily ≤ 8 * (q : ℝ) / (N : ℝ) := by
    calc
      tailx + taily ≤ 4 * (q : ℝ) / (N : ℝ) + 4 * (q : ℝ) / (N : ℝ) :=
        add_le_add hx hy
      _ = 8 * (q : ℝ) / (N : ℝ) := heq
  linarith

/-- For positive `q`, the gap between one and `dlogSuccessLowerBound (2 ^ n) q` can be made at
most any prescribed positive real number. See [ProosZalka2003]. -/
theorem dlogSuccess_two_pow_close_to_one (q : ℕ) (hq : 0 < q) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      1 - dlogSuccessLowerBound (2 ^ n) q ≤ ε := by
  intro ε hε
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨m, hm⟩ := exists_nat_gt (8 * (q : ℝ) / ε)
  refine ⟨m + 1, ?_⟩
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hm' : 8 * (q : ℝ) / ε < ((m + 1 : ℕ) : ℝ) := by
    have h1 : ((m : ℕ) : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    linarith
  have hpow : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m + 1)).le
  have hlt : 8 * (q : ℝ) / ε < (2 : ℝ) ^ (m + 1) := lt_of_lt_of_le hm' hpow
  have hq8 : 8 * (q : ℝ) < ε * (2 : ℝ) ^ (m + 1) := by
    have hcomm : (2 : ℝ) ^ (m + 1) * ε = ε * (2 : ℝ) ^ (m + 1) := mul_comm _ _
    rw [← hcomm]
    exact (div_lt_iff₀ hε).mp hlt
  have hfrac : 8 * (q : ℝ) / (2 : ℝ) ^ (m + 1) ≤ ε := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hcast : (((2 ^ (m + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (m + 1) := by
    push_cast
    ring
  unfold dlogSuccessLowerBound
  rw [hcast]
  linarith

end Qatlib.Papers.ShorElliptic03.MainResults.FidelityAndSuccess
