/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationStat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Asymptotic decay of the collision-isolation error

This module bounds the geometric tail appearing in collision isolation and proves decay of
logarithmic powers divided by positive real powers. The explicit function `errorMajorant` tends
to zero, giving a threshold at which the accumulated isolation error is arbitrarily small.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `errorMajorant_tendsto`: proves decay of the explicit majorant.
* `isolationError_threshold`: supplies a natural-number threshold for the desired error and size
  bounds.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped Classical BigOperators

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open Filter
open scoped Topology
noncomputable section

/-- For positive `x`, the geometric tail `2^(-Nat.floor (log x))` is at most `2 / x^(log 2)`. -/
theorem binaryFloorLog_tail_bound (x : ℝ) (hx : 0 < x) :
    (1/2 : ℝ)^(Nat.floor (Real.log x)) ≤ 2/x^(Real.log 2) := by
  have hfloor := Nat.lt_floor_add_one (Real.log x)
  calc
    (1/2 : ℝ)^(Nat.floor (Real.log x)) =
        (2 : ℝ)^(-(Nat.floor (Real.log x) : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      simp [one_div, inv_pow]
    _ ≤ (2 : ℝ)^(1-Real.log x) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2/x^(Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hx]
      rw [show Real.log 2*(1-Real.log x) = Real.log 2-Real.log x*Real.log 2 by ring,
        Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
end
noncomputable section

/-- Every natural power of `log x` divided by `x^s` tends to zero as `x` tends to infinity when
`s` is positive. -/
theorem logPower_div_rpow_tendsto (p : ℕ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun x : ℝ => (Real.log x)^p/x^s) atTop (nhds 0) := by
  simpa only [Real.rpow_natCast] using!
    (isLittleO_log_rpow_rpow_atTop (p : ℝ) hs).tendsto_div_nhds_zero
end
noncomputable section
/-- The explicit majorant `(1 + k * log x) * (2 / x^(log 2) + 4 / x + 16 * k^2 * (log x + 1)^2 /
sqrt x)` for accumulated isolation error. -/
def errorMajorant (k : ℕ) (x : ℝ) : ℝ :=
  (1+(k : ℝ)*Real.log x)*
    (2/x^(Real.log 2)+4/x+16*(k : ℝ)^2*(Real.log x+1)^2/Real.sqrt x)
end
noncomputable section

/-- For each fixed `k`, the isolation error majorant tends to zero at infinity. -/
theorem errorMajorant_tendsto (k : ℕ) : Tendsto (errorMajorant k) atTop (nhds 0) := by
  have halpha : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0a := logPower_div_rpow_tendsto 0 (Real.log 2) halpha
  have h1a := logPower_div_rpow_tendsto 1 (Real.log 2) halpha
  have h01 := logPower_div_rpow_tendsto 0 1 (by norm_num)
  have h11 := logPower_div_rpow_tendsto 1 1 (by norm_num)
  have h0h := logPower_div_rpow_tendsto 0 (1/2) (by norm_num)
  have h1h := logPower_div_rpow_tendsto 1 (1/2) (by norm_num)
  have h2h := logPower_div_rpow_tendsto 2 (1/2) (by norm_num)
  have h3h := logPower_div_rpow_tendsto 3 (1/2) (by norm_num)
  have hlimit := (((h0a.const_mul 2).add (h1a.const_mul (2*(k : ℝ)))).add
    ((h01.const_mul 4).add (h11.const_mul (4*(k : ℝ))))).add
      ((((h3h.const_mul (k : ℝ)).add (h2h.const_mul (1+2*(k : ℝ)))).add
        ((h1h.const_mul (2+(k : ℝ))).add h0h)).const_mul (16*(k : ℝ)^2))
  convert! hlimit using 1
  · ext x
    simp only [errorMajorant, Real.sqrt_eq_rpow, Real.rpow_one, pow_zero, pow_one]
    ring
  · simp
end
noncomputable section

/-- For `k ≥ 2` and positive `ε`, all sufficiently large `N` satisfy the stated square-root and
logarithm bounds and have accumulated isolation error at most `ε`. -/
theorem isolationError_threshold (k : ℕ) (_hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (8*k*k : ℝ) ≤ Real.sqrt N ∧ 2 ≤ Real.log (N : ℝ) ∧
      (1+(k : ℝ)*Real.log (N : ℝ))*
        ((1/2 : ℝ)^(Nat.floor (Real.log (N : ℝ)))+4/(N : ℝ)+
          16*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N) ≤ ε := by
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have herror := (errorMajorant_tendsto k).comp hnat
  have hsmall : ∀ᶠ N : ℕ in atTop, errorMajorant k N < ε :=
    herror.eventually (eventually_lt_nhds hε)
  have hsqrt : ∀ᶠ N : ℕ in atTop, (8*k*k : ℝ) ≤ Real.sqrt N :=
    (Real.tendsto_sqrt_atTop.comp hnat).eventually_ge_atTop _
  have hlog : ∀ᶠ N : ℕ in atTop, 2 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp hnat).eventually_ge_atTop _
  have hpos : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have heventually : ∀ᶠ N : ℕ in atTop,
      (8*k*k : ℝ) ≤ Real.sqrt N ∧ 2 ≤ Real.log (N : ℝ) ∧
      (1+(k : ℝ)*Real.log (N : ℝ))*
        ((1/2 : ℝ)^(Nat.floor (Real.log (N : ℝ)))+4/(N : ℝ)+
          16*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N) ≤ ε := by
    filter_upwards [hsqrt, hlog, hsmall, hpos] with N hN hs he hp
    refine ⟨hN, hs, le_trans ?_ he.le⟩
    have hx : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have htail := binaryFloorLog_tail_bound (N : ℝ) hx
    have hcoeff : 0 ≤ 1+(k : ℝ)*Real.log (N : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add htail le_rfl) le_rfl) hcoeff
  exact eventually_atTop.mp heventually
end
end Qatlib.Concepts.WalkFind.SearchAlgorithm
