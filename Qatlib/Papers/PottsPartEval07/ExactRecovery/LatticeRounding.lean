/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Lattice rounding for exact weight recovery

This module bounds the effect of phase errors on finite sums of complex exponentials and on the
scaled Gauss-sum expression used for code weights. The lattice separation lemmas show that an
estimate within half the lattice spacing uniquely determines the exact weight [GeraciLidar2008].

## Main statements

* `gauss_weight_error_bound`: Uniform phase errors give an explicit bound on the scaled sum
  error.
* `weight_recovery`: A weight estimate within half the spacing determines its integer lattice
  index uniquely.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.ExactRecovery

open scoped BigOperators

/-- Two distinct integer multiples of a positive spacing `L` are separated by at least `L`. -/
theorem lattice_separation {L : ℝ} (hL : 0 < L) {a b : ℤ} (hab : a ≠ b) :
    L ≤ |(a : ℝ) * L - (b : ℝ) * L| := by
  have h1 : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
    have hz : (1 : ℤ) ≤ |a - b| := Int.one_le_abs (sub_ne_zero.mpr hab)
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|a - b| : ℤ) : ℝ) := by exact_mod_cast hz
    rw [Int.cast_abs, Int.cast_sub] at h2
    simpa using h2
  have hsplit : (a : ℝ) * L - (b : ℝ) * L = ((a : ℝ) - (b : ℝ)) * L := by ring
  rw [hsplit, abs_mul, abs_of_pos hL]
  calc L = 1 * L := by ring
    _ ≤ |(a : ℝ) - (b : ℝ)| * L := by gcongr

/-- An estimate cannot be strictly within `L / 2` of two distinct points of the lattice `L * ℤ`
[GeraciLidar2008]. -/
theorem nearest_lattice_unique {L : ℝ} (hL : 0 < L) {e : ℝ} {a b : ℤ}
    (ha : |e - (a : ℝ) * L| < L / 2) (hb : |e - (b : ℝ) * L| < L / 2) : a = b := by
  by_contra hab
  have hge : L ≤ |(a : ℝ) * L - (b : ℝ) * L| := lattice_separation hL hab
  have hlt : |(a : ℝ) * L - (b : ℝ) * L| < L := by
    have htri : |(a : ℝ) * L - (b : ℝ) * L|
        ≤ |(a : ℝ) * L - e| + |e - (b : ℝ) * L| := by
      have : (a : ℝ) * L - (b : ℝ) * L = ((a : ℝ) * L - e) + (e - (b : ℝ) * L) := by ring
      rw [this]
      exact abs_add_le _ _
    have h1 : |(a : ℝ) * L - e| = |e - (a : ℝ) * L| := abs_sub_comm _ _
    rw [h1] at htri
    linarith
  linarith

/-- The distance between the complex phases with angles `x` and `y` is at most `|x - y|`. -/
theorem complex_exp_lipschitz (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  have heq : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)
      = Complex.exp ((y : ℂ) * Complex.I)
          * (Complex.exp (((x - y : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    have harg : (x : ℂ) * Complex.I
        = (y : ℂ) * Complex.I + ((x - y : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [harg]
  rw [heq, norm_mul]
  have hy : ‖Complex.exp ((y : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hy, one_mul]
  simpa [mul_comm] using h

/-- A sum of `d` phase differences with coefficients of norm at most one has norm at most `d *
ε` when each angle error is at most `ε`. -/
theorem phase_sum_bound {d : ℕ} (γ γ' : Fin d → ℝ) (c : Fin d → ℂ)
    (hc : ∀ a, ‖c a‖ ≤ 1) (ε : ℝ) (hε : ∀ a, |γ a - γ' a| ≤ ε) :
    ‖∑ a, c a * (Complex.exp (((γ a : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((γ' a : ℝ) : ℂ) * Complex.I))‖ ≤ (d : ℝ) * ε := by
  calc ‖∑ a, c a * (Complex.exp (((γ a : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((γ' a : ℝ) : ℂ) * Complex.I))‖
      ≤ ∑ a, ‖c a * (Complex.exp (((γ a : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((γ' a : ℝ) : ℂ) * Complex.I))‖ := norm_sum_le _ _
    _ = ∑ a, ‖c a‖ * ‖Complex.exp (((γ a : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((γ' a : ℝ) : ℂ) * Complex.I)‖ := by
        simp only [norm_mul]
    _ ≤ ∑ _a : Fin d, 1 * ε := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul (hc a)
          (le_trans (complex_exp_lipschitz (γ a) (γ' a)) (hε a)) (norm_nonneg _) zero_le_one
    _ = (d : ℝ) * ε := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]

/-- The scaled Gauss-phase sum has error at most `(q - 1) / (q * N) * (d * ε)` under the stated
coefficient and phase-error bounds [GeraciLidar2008]. -/
theorem gauss_weight_error_bound
    {d q N : ℕ} (hq : 1 ≤ q) (hN : 0 < N)
    (γ γ' : Fin d → ℝ) (c : Fin d → ℂ) (hc : ∀ a, ‖c a‖ ≤ 1)
    (ε : ℝ) (hε : ∀ a, |γ a - γ' a| ≤ ε) :
    ‖((((q : ℝ) - 1) / ((q : ℝ) * N) : ℝ) : ℂ)
        * ∑ a, c a * (Complex.exp (((γ a : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((γ' a : ℝ) : ℂ) * Complex.I))‖
      ≤ ((q : ℝ) - 1) / ((q : ℝ) * N) * (d * ε) := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : (0 : ℝ) ≤ ((q : ℝ) - 1) / ((q : ℝ) * N) := by
    apply div_nonneg
    · linarith
    · positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hden]
  exact mul_le_mul_of_nonneg_left (phase_sum_bound γ γ' c hc ε hε) hden

/-- If `w = m * L` and `w'` is strictly within `L / 2` of `w`, every integer `m'` with `|w' - m'
* L| < L / 2` equals `m` [GeraciLidar2008]. -/
theorem weight_recovery {L : ℝ} (hL : 0 < L) {w w' : ℝ} {m : ℤ}
    (hw : w = (m : ℝ) * L) (hw' : |w' - w| < L / 2) :
    ∀ (m' : ℤ), |w' - (m' : ℝ) * L| < L / 2 → m' = m := by
  intro m' hm'
  apply nearest_lattice_unique hL (e := w') (a := m') (b := m) hm'
  rw [← hw]
  exact hw'

end Qatlib.Papers.PottsPartEval07.ExactRecovery
