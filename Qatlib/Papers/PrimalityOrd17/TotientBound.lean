/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpTransform14.TotientLimInf.TotientLimInfAmpl
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
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Basic

/-!
# An eventual lower bound for the totient ratio

The theorem `totient_ratio_gt_inv_three_loglog` gives a strict reciprocal log-log lower bound on
φ(M) / M for all sufficiently large natural numbers M. This numerical estimate supports the
success-probability analysis of order-based primality trials [DonisVelaGarciaEscartin2017].

## Main statements

* `totient_ratio_gt_inv_three_loglog`: The totient ratio eventually exceeds 1 / (3 log log M).

## References

* [Donis-Vela and Garcia-Escartin, 2017][DonisVelaGarciaEscartin2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Filter
open scoped Topology
namespace Qatlib.Papers.PrimalityOrd17.TotientBound

/-- For all sufficiently large natural numbers `M`, the ratio `totient M / M` is greater than `1
/ (3 * log (log M))` [DonisVelaGarciaEscartin2017]. -/
theorem totient_ratio_gt_inv_three_loglog :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (1 : ℝ) / (3 * Real.log (Real.log (M : ℝ))) < (Nat.totient M : ℝ) / (M : ℝ) := by
  have hlim :=
    Qatlib.Papers.AmpTransform14.TotientLimInf.AmplifiedQuantumTransforms2014.totientLimInf_answer
  change Filter.liminf
      (fun N : ℕ => (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ))
      Filter.atTop = Real.exp (-Real.eulerMascheroniConstant) at hlim
  have hbdd : IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun N : ℕ => (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ)) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop,
      (0 : ℝ) ≤ (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ)
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hn3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have ht : 1 ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
      linarith [Real.exp_one_lt_d9]
    have hln : 0 ≤ Real.log (Real.log (N : ℝ)) :=
      Real.log_nonneg (ht.trans (Real.log_le_log (by norm_num) hn3))
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hln) (Nat.cast_nonneg _)
  have hexp : (1 / 3 : ℝ) < Real.exp (-Real.eulerMascheroniConstant) := by
    have h3 : Real.exp (2 / 3 : ℝ) < 3 := by
      have hmono : Real.exp (2 / 3 : ℝ) < Real.exp 1 :=
        Real.exp_lt_exp.mpr (by norm_num)
      have he1 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      linarith
    have h23 : (1 / 3 : ℝ) < Real.exp (-(2 / 3 : ℝ)) := by
      rw [Real.exp_neg, show (1 / 3 : ℝ) = 3⁻¹ by norm_num]
      exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 3) (Real.exp_pos _)).2 h3
    have hlt : Real.exp (-(2 / 3 : ℝ)) < Real.exp (-Real.eulerMascheroniConstant) := by
      apply Real.exp_lt_exp.mpr
      have := Real.eulerMascheroniConstant_lt_two_thirds
      linarith
    linarith
  have hlt : (1 / 3 : ℝ) < Filter.liminf
      (fun N : ℕ => (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ))
      Filter.atTop := by
    rw [hlim]
    exact hexp
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 3 : ℝ) < (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ) :=
    eventually_lt_of_lt_liminf hlt hbdd
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hev
  refine ⟨max M₀ 3, ?_⟩
  intro M hM
  have hMge : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM3 : 3 ≤ M := le_trans (le_max_right _ _) hM
  have hb := hM₀ M hMge
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hexp1_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h1lt : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact hexp1_lt3
  have hM3r : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hlogM : (1 : ℝ) < Real.log (M : ℝ) :=
    lt_of_lt_of_le h1lt (Real.log_le_log (by norm_num) hM3r)
  have hLpos : 0 < Real.log (Real.log (M : ℝ)) := Real.log_pos hlogM
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * Real.log (Real.log (M : ℝ))) hMpos]
  have hb' : (1 / 3 : ℝ) * M < (Nat.totient M : ℝ) * Real.log (Real.log (M : ℝ)) := by
    rw [lt_div_iff₀ hMpos] at hb
    linarith
  nlinarith

end Qatlib.Papers.PrimalityOrd17.TotientBound
