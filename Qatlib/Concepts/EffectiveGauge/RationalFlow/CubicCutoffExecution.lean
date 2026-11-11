/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierPeriodExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Cubic Cutoff Execution

Rational Flow constructions for Effective Gauge.
Defines `cubicCutoffSearch`, `rationalCubicCeiling`, `finitePoissonCutoff`.
Proves `cubicCutoffSearch_spec`, `rationalCubicCeiling_spec`, `finitePoissonCutoff_pos`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Bounded integer search. Its result is the same least cubic ceiling
as the prototype's binary search; this implementation has its own fuel. -/
def cubicCutoffSearch (value : ℚ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | fuel+1 => if value ≤ (n : ℚ)^3 then n else cubicCutoffSearch value (n+1) fuel

/-- Definition of rational Cubic Ceiling in the Rational Flow construction. -/
def rationalCubicCeiling (value : ℚ) : ℕ :=
  cubicCutoffSearch value 0 (Nat.ceil value+1)

/-- Definition of finite Poisson Cutoff in the Rational Flow construction. -/
def finitePoissonCutoff (C6 tolerance : ℚ) : ℕ :=
  max 1 (rationalCubicCeiling (400*C6/tolerance))

/-- Original `cubicCutoffSearch_spec` guarantee for the `CubicCutoffExecution` construction; the complete source hypotheses are retained. -/
theorem cubicCutoffSearch_spec (value : ℚ) (fuel n : ℕ)
    (hstop : value ≤ ((n+fuel : ℕ) : ℚ)^3) :
    let r := cubicCutoffSearch value n fuel
    value ≤ (r : ℚ)^3 ∧ n ≤ r ∧ r ≤ n+fuel ∧
      ∀ k, n ≤ k → k<r → (k : ℚ)^3<value := by
  induction fuel generalizing n with
  | zero =>
    dsimp only [cubicCutoffSearch]
    refine ⟨by simpa only [Nat.add_zero] using hstop,le_rfl,by omega,?_⟩
    intro k hk hkn
    omega
  | succ fuel ih =>
    dsimp only [cubicCutoffSearch]
    split_ifs with h
    · refine ⟨h,le_rfl,by omega,?_⟩
      intro k hk hkn
      omega
    · have hstop' : value ≤ ((n+1+fuel : ℕ) : ℚ)^3 := by
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hstop
      obtain ⟨hvalue,hlo,hhi,hprior⟩ := ih (n+1) hstop'
      refine ⟨hvalue,by omega,by omega,?_⟩
      intro k hk hkr
      by_cases heq : k=n
      · subst k
        exact lt_of_not_ge h
      · exact hprior k (by omega) hkr

/-- Original `rationalCubicCeiling_spec` guarantee for the `CubicCutoffExecution` construction; the complete source hypotheses are retained. -/
theorem rationalCubicCeiling_spec (value : ℚ) :
    value ≤ (rationalCubicCeiling value : ℚ)^3 ∧
      ∀ k, k<rationalCubicCeiling value → (k : ℚ)^3<value := by
  let t : ℚ := (Nat.ceil value : ℚ)+1
  have ht1 : 1 ≤ t := by
    dsimp only [t]
    linarith [(Nat.cast_nonneg (Nat.ceil value) : (0 : ℚ) ≤ Nat.ceil value)]
  have hle : value ≤ t := (Nat.le_ceil value).trans (by dsimp only [t]; linarith)
  have hcube : t ≤ t^3 := by
    have hprod : 0 ≤ t*(t-1)*(t+1) := mul_nonneg
      (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have hstop : value ≤ ((0+(Nat.ceil value+1) : ℕ) : ℚ)^3 := by
    simpa only [Nat.zero_add,Nat.cast_add,Nat.cast_one] using hle.trans hcube
  have h := cubicCutoffSearch_spec value (Nat.ceil value+1) 0 hstop
  exact ⟨h.1,fun k hk => h.2.2.2 k (Nat.zero_le _) hk⟩

/-- Original `finitePoissonCutoff_pos` guarantee for the `CubicCutoffExecution` construction; the complete source hypotheses are retained. -/
theorem finitePoissonCutoff_pos (C6 tolerance : ℚ) : 0<finitePoissonCutoff C6 tolerance :=
  lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _)

/-- Original `finitePoissonCutoff_budget` guarantee for the `CubicCutoffExecution` construction; the complete source hypotheses are retained. -/
theorem finitePoissonCutoff_budget (C6 tolerance : ℚ) (ht : 0<tolerance) :
    400*C6 ≤ tolerance*(finitePoissonCutoff C6 tolerance : ℚ)^3 := by
  have hroot := (rationalCubicCeiling_spec (400*C6/tolerance)).1
  have hpow : (rationalCubicCeiling (400*C6/tolerance) : ℚ)^3 ≤
      (finitePoissonCutoff C6 tolerance : ℚ)^3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _)
      (by exact_mod_cast le_max_right 1 (rationalCubicCeiling (400*C6/tolerance))) 3
  have h := (div_le_iff₀ ht).mp (hroot.trans hpow)
  simpa only [mul_comm] using h

end Qatlib.Concepts.EffectiveGauge.RationalFlow
