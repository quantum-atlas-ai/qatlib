/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs

/-!
# First-quantized local-operator cost models

This module records the local-operator cost models associated with [AbramsLloyd1997]. The
function `particleTermCost` assigns m^(2k) to a k-particle term, recovering m² and m⁴ for the
one- and two-particle cases.

The modeled cost of N steps is bounded by 2Nm⁴ when m ≥ 1. The module also records the
derivatives at zero of a local matrix exponential.

## Main statements

* `simulationCost_polynomial`: The defined N-step cost is at most 2Nm⁴.
* `one_two_particle_budget_arithmetic`: The one- and two-particle cost comparisons.

## References

* [Abrams and Lloyd, 1997][AbramsLloyd1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

/-- The k-particle term cost model m^(2k). -/
def particleTermCost (k m : ℕ) : ℕ := m ^ (2 * k)

/-- The k-particle term cost model equals (m²)^k. -/
theorem particleTermCost_eq (k m : ℕ) : particleTermCost k m = (m ^ 2) ^ k := by
  rw [particleTermCost, pow_mul]

/-- The one-particle term cost model is m². -/
theorem one_particle_term_cost (m : ℕ) : particleTermCost 1 m = m ^ 2 := by
  simp [particleTermCost]

/-- The two-particle term cost model is m⁴. -/
theorem two_particle_term_cost (m : ℕ) : particleTermCost 2 m = m ^ 4 := by
  simp [particleTermCost]

/-- The one-particle step cost agrees with `particleTermCost 1 m`. -/
theorem one_particle_step_cost (m : ℕ) :
    oneParticleStepCost m = particleTermCost 1 m := rfl

/-- The two-particle step cost agrees with `particleTermCost 2 m`. -/
theorem two_particle_step_cost (m : ℕ) :
    twoParticleStepCost m = particleTermCost 2 m := by
  unfold twoParticleStepCost particleTermCost
  norm_num

/-- The N-step cost model obtained by multiplying N by the sum of the one- and two-particle step
costs. -/
def simulationCost (N m : ℕ) : ℕ :=
  N * (oneParticleStepCost m + twoParticleStepCost m)

/-- For m ≥ 1, the defined N-step simulation cost is at most 2Nm⁴ [AbramsLloyd1997]. -/
theorem simulationCost_polynomial {N m : ℕ} (hm : 1 ≤ m) :
    simulationCost N m ≤ 2 * N * m ^ 4 := by
  unfold simulationCost
  calc N * (oneParticleStepCost m + twoParticleStepCost m)
      ≤ N * (2 * m ^ 4) := Nat.mul_le_mul_left N (firstQuantized_simulation_bound hm)
    _ = 2 * N * m ^ 4 := by ring

/-- For m ≥ 1, the one-particle cost is at most m⁴, the two-particle cost equals m⁴, and their
sum is at most 2m⁴. -/
theorem one_two_particle_budget_arithmetic {m : ℕ} (hm : 1 ≤ m) :
    oneParticleStepCost m ≤ m ^ 4 ∧
      twoParticleStepCost m = m ^ 4 ∧
      oneParticleStepCost m + twoParticleStepCost m ≤ 2 * m ^ 4 :=
  ⟨oneParticleStepCost_le hm, rfl, firstQuantized_simulation_bound hm⟩

/-- The kth derivative at zero of the local matrix exponential t ↦ exp(tH) equals H^k. -/
theorem local_term_evolution_jets {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => NormedSpace.exp (t • H)) 0 = H ^ k :=
  local_evolution_jets H k

end Qatlib.Papers.ManyBodyFermi97.MainResults
