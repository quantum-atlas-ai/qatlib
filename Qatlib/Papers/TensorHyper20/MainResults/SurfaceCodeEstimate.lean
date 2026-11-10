/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.SurfaceCodeEstimate

def physPerLogical (d : ℕ) : ℕ := 2 * (d + 1) ^ 2

theorem physPerLogical_ratio : physPerLogical 31 = 4 * physPerLogical 15 := by
  norm_num [physPerLogical]

theorem physical_qubits_factor_four (L : ℕ) :
    physPerLogical 31 * L = 4 * (physPerLogical 15 * L) := by
  rw [physPerLogical_ratio]
  ring

theorem physical_qubits_four_million :
    physPerLogical 31 * 1953 ≤ 4000000 ∧ physPerLogical 15 * 1953 ≤ 1000000 := by
  norm_num [physPerLogical]

def innerLoops : ℕ := 483000

def toffolisPerLoop : ℕ := 13880

def totalToffolis : ℕ := innerLoops * toffolisPerLoop

def factoryRateHz : ℕ := 25000

theorem runtime_lt_four_days :
    totalToffolis ≤ 4 * (86400 * factoryRateHz) := by
  norm_num [totalToffolis, innerLoops, toffolisPerLoop, factoryRateHz]

theorem runtime_optimistic_lt_two_days :
    15 * totalToffolis ≤ 2 * (86400 * factoryRateHz) * 31 := by
  norm_num [totalToffolis, innerLoops, toffolisPerLoop, factoryRateHz]

end Qatlib.Papers.TensorHyper20.MainResults.SurfaceCodeEstimate
