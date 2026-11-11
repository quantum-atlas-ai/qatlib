/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Surface-code resource estimates

Evaluates a surface-code qubit proxy and fixed Toffoli-throughput estimates associated with
[LeeEtAl2021]. The function `physPerLogical` assigns `2 * (d + 1)^2` physical qubits per logical
qubit, and the numerical results compare distances 31 and 15.

The runtime statements bound the defined Toffoli count by four days of the stated factory
throughput and by a two-day budget after the indicated `15 / 31` rescaling.

## Main statements

* `physical_qubits_four_million`: checks the two physical-qubit budgets for 1953 logical qubits.
* `runtime_lt_four_days`: checks a four-day Toffoli-throughput budget.
* `runtime_optimistic_lt_two_days`: checks the rescaled two-day budget.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.SurfaceCodeEstimate

/-- The physical-qubit proxy `2 * (d + 1)^2` per logical qubit at code distance `d`. -/
def physPerLogical (d : ℕ) : ℕ := 2 * (d + 1) ^ 2

/-- The physical-qubit proxy at distance 31 is four times its value at distance 15. -/
theorem physPerLogical_ratio : physPerLogical 31 = 4 * physPerLogical 15 := by
  norm_num [physPerLogical]

/-- For any logical-qubit count, changing the proxy distance from 15 to 31 multiplies the total
physical-qubit count by four. -/
theorem physical_qubits_factor_four (L : ℕ) :
    physPerLogical 31 * L = 4 * (physPerLogical 15 * L) := by
  rw [physPerLogical_ratio]
  ring

/-- For 1953 logical qubits, the distance-31 proxy is at most four million physical qubits and
the distance-15 proxy is at most one million. See [LeeEtAl2021]. -/
theorem physical_qubits_four_million :
    physPerLogical 31 * 1953 ≤ 4000000 ∧ physPerLogical 15 * 1953 ≤ 1000000 := by
  norm_num [physPerLogical]

/-- The fixed phase-estimation inner-loop count of 483000. -/
def innerLoops : ℕ := 483000

/-- The fixed Toffoli count of 13880 per inner loop. -/
def toffolisPerLoop : ℕ := 13880

/-- The product of the defined inner-loop count and Toffoli count per loop. -/
def totalToffolis : ℕ := innerLoops * toffolisPerLoop

/-- The fixed factory throughput of 25000 Toffolis per second. -/
def factoryRateHz : ℕ := 25000

/-- The defined total Toffoli count fits within four days at the stated factory throughput. See
[LeeEtAl2021]. -/
theorem runtime_lt_four_days :
    totalToffolis ≤ 4 * (86400 * factoryRateHz) := by
  norm_num [totalToffolis, innerLoops, toffolisPerLoop, factoryRateHz]

/-- The total Toffoli count multiplied by 15 fits within 31 times the two-day throughput budget. -/
theorem runtime_optimistic_lt_two_days :
    15 * totalToffolis ≤ 2 * (86400 * factoryRateHz) * 31 := by
  norm_num [totalToffolis, innerLoops, toffolisPerLoop, factoryRateHz]

end Qatlib.Papers.TensorHyper20.MainResults.SurfaceCodeEstimate
