/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.ClockBridge.MachineImplementationDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis
open Qatlib.Concepts.CircuitImpl.Phi3Universal

theorem miDyadicTruncationBound (a : RatAngle) (d : ℕ) : MiDyadicTruncationBound a d := by
  unfold MiDyadicTruncationBound
  have h := Nat.div_mul_le_self (a.num * 2 ^ d) a.den
  unfold dyadicApprox
  exact h

theorem miDyadicApprox_le (a : RatAngle) (d : ℕ) :
    dyadicApprox a d * a.den ≤ a.num * 2 ^ d := miDyadicTruncationBound a d

theorem miCopyProgramLedger (inW work : ℕ) : MiCopyProgramLedger inW work := by
  refine ⟨?_, ?_⟩
  · show (copyProgram inW work).length = 4
    rfl
  · show (copyProgram inW work)
      = [.alloc work, .fixedGate (.cx inW work), .fixedGate (.cx inW work),
        .releaseClean work]
    rfl

theorem miRealQuantization_ledger (r : ℝ) (d : ℕ) : MiRealQuantizationLedger r d := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hfloor := Int.floor_le (r * (2 : ℝ) ^ d)
  have hfloor' := Int.lt_floor_add_one (r * (2 : ℝ) ^ d)
  have hcancel : (r * (2 : ℝ) ^ d) / (2 : ℝ) ^ d = r := by
    rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  constructor
  · rw [realDyadicValue]
    have h1 : (realDyadicApprox r d : ℝ) ≤ r * (2 : ℝ) ^ d := hfloor
    have h2 : (realDyadicApprox r d : ℝ) / (2 : ℝ) ^ d
        ≤ (r * (2 : ℝ) ^ d) / (2 : ℝ) ^ d :=
      div_le_div_of_nonneg_right h1 (le_of_lt hpos)
    rw [hcancel] at h2
    exact h2
  · rw [realDyadicValue, realDyadicStep, inv_eq_one_div]
    have h1 : r * (2 : ℝ) ^ d < (realDyadicApprox r d : ℝ) + 1 := hfloor'
    have h2 : (r * (2 : ℝ) ^ d) / (2 : ℝ) ^ d
        < ((realDyadicApprox r d : ℝ) + 1) / (2 : ℝ) ^ d :=
      div_lt_div_of_pos_right h1 hpos
    rw [add_div] at h2
    rw [hcancel] at h2
    exact h2

theorem miRealQuantization_error (r : ℝ) (d : ℕ) :
    |realDyadicValue r d - r| ≤ realDyadicStep d := by
  have h := miRealQuantization_ledger r d
  have h1 : realDyadicValue r d - r ≤ 0 := by linarith [h.1]
  have h2 : realDyadicValue r d - r > -(realDyadicStep d) := by
    have hlt : r - realDyadicValue r d < realDyadicStep d := by linarith [h.2]
    linarith
  have hstep : 0 ≤ realDyadicStep d := by
    rw [realDyadicStep]
    positivity
  exact (abs_le).2 ⟨le_of_lt h2, h1.trans hstep⟩

theorem miRealQuantization_step_le_one (d : ℕ) : realDyadicStep d ≤ 1 := by
  rw [realDyadicStep, inv_eq_one_div]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ d := by
    induction d with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ k * 2 := by
          calc 2 = 1 * 2 := by ring
            _ ≤ (2 : ℝ) ^ k * 2 := mul_le_mul_of_nonneg_right ih (by norm_num)
        linarith
  exact (div_le_one (by positivity)).2 h1

theorem miRealQuantization_agrees_rational (a : RatAngle) (d : ℕ) :
    realDyadicApprox a.value d = (dyadicApprox a d : ℤ) := by
  have hn : 0 < a.den := a.den_pos
  have hq : dyadicApprox a d * a.den ≤ a.num * 2 ^ d := Nat.div_mul_le_self _ _
  have hr : (a.num * 2 ^ d).mod a.den < a.den := Nat.mod_lt _ hn
  have hsplit : a.den * (dyadicApprox a d) + (a.num * 2 ^ d).mod a.den = a.num * 2 ^ d := by
    rw [dyadicApprox]
    exact Nat.div_add_mod _ _
  have hx : a.value * (2 : ℝ) ^ d = Nat.cast (a.num * 2 ^ d) / (a.den : ℝ) := by
    rw [RatAngle.value]
    field_simp
    norm_cast
  rw [realDyadicApprox, Int.floor_eq_iff]
  constructor
  · rw [hx]
    have h1 : (dyadicApprox a d : ℝ) ≤ Nat.cast (a.num * 2 ^ d) / (a.den : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hn)]
      exact_mod_cast hq
    exact h1
  · rw [hx]
    have hlt : Nat.cast (a.num * 2 ^ d)
        < (Nat.cast (dyadicApprox a d) + 1) * (a.den : ℝ) := by
      have hrem' : Nat.cast ((a.num * 2 ^ d).mod a.den) < (a.den : ℝ) := by exact_mod_cast hr
      have heq : Nat.cast (a.num * 2 ^ d)
          = Nat.cast (dyadicApprox a d) * (a.den : ℝ) + Nat.cast ((a.num * 2 ^ d).mod a.den) := by
        have h2 := hsplit
        norm_cast at h2 ⊢
        linarith
      rw [heq]
      linarith
    rw [div_lt_iff₀ (by exact_mod_cast hn)]
    exact hlt

theorem miRealPhase_error (r : ℝ) (d : ℕ) :
    ‖phaseOf r - phaseOf (realDyadicValue r d)‖ ≤ 2 * |r - realDyadicValue r d| := by
  have herr := miRealQuantization_error r d
  have hstep : realDyadicStep d ≤ 1 := miRealQuantization_step_le_one d
  have hmargin : |r - realDyadicValue r d| ≤ 1 := by
    have h1 : |realDyadicValue r d - r| ≤ 1 := le_trans herr hstep
    rw [abs_le] at h1 ⊢
    constructor <;> linarith
  exact thresholdGoal_phase_lipschitz r (realDyadicValue r d) hmargin

end Qatlib.Concepts.MixedInstrument.ClockBridge
