/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Matrix

namespace Qatlib.Papers.ManyBodyFermi97.MainResults

def particleTermCost (k m : ℕ) : ℕ := m ^ (2 * k)

theorem particleTermCost_eq (k m : ℕ) : particleTermCost k m = (m ^ 2) ^ k := by
  rw [particleTermCost, pow_mul]

theorem one_particle_term_cost (m : ℕ) : particleTermCost 1 m = m ^ 2 := by
  simp [particleTermCost]

theorem two_particle_term_cost (m : ℕ) : particleTermCost 2 m = m ^ 4 := by
  simp [particleTermCost]

theorem one_particle_step_cost (m : ℕ) :
    oneParticleStepCost m = particleTermCost 1 m := rfl

theorem two_particle_step_cost (m : ℕ) :
    twoParticleStepCost m = particleTermCost 2 m := by
  unfold twoParticleStepCost particleTermCost
  norm_num

def simulationCost (N m : ℕ) : ℕ :=
  N * (oneParticleStepCost m + twoParticleStepCost m)

theorem simulationCost_polynomial {N m : ℕ} (hm : 1 ≤ m) :
    simulationCost N m ≤ 2 * N * m ^ 4 := by
  unfold simulationCost
  calc N * (oneParticleStepCost m + twoParticleStepCost m)
      ≤ N * (2 * m ^ 4) := Nat.mul_le_mul_left N (firstQuantized_simulation_bound hm)
    _ = 2 * N * m ^ 4 := by ring

theorem one_two_particle_budget_arithmetic {m : ℕ} (hm : 1 ≤ m) :
    oneParticleStepCost m ≤ m ^ 4 ∧
      twoParticleStepCost m = m ^ 4 ∧
      oneParticleStepCost m + twoParticleStepCost m ≤ 2 * m ^ 4 :=
  ⟨oneParticleStepCost_le hm, rfl, firstQuantized_simulation_bound hm⟩

theorem local_term_evolution_jets {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => NormedSpace.exp (t • H)) 0 = H ^ k :=
  local_evolution_jets H k

end Qatlib.Papers.ManyBodyFermi97.MainResults
