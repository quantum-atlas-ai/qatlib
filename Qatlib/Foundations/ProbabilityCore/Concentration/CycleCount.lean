/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Perm

@[expose] public section


/-! # Actual permutation cycle counts for Gaussian moment enumeration

LinearOptics10 Proposition 55 and its fourth-moment argument count fixed
points as cycles. Mathlib cycleType records only nontrivial cycles.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.ProbabilityCore.Concentration.CycleCount

/-- The actual number of nontrivial cycles, excluding fixed points. -/
def nontrivCycles {n : ℕ} (sigma : Equiv.Perm (Fin n)) : ℕ := sigma.cycleType.card

/-- The actual full cycle count adds each fixed point as a singleton cycle. -/
def allCycles {n : ℕ} (sigma : Equiv.Perm (Fin n)) : ℕ :=
  sigma.cycleType.card + (n-sigma.support.card)

/-- Identity permutations have no nontrivial cycles. -/
theorem nontrivIdentity (n : ℕ) : nontrivCycles (1 : Equiv.Perm (Fin n)) = 0 := by
  simp [nontrivCycles]

/-- Identity permutations have exactly n cycles when singleton cycles are included. -/
theorem identityCount (n : ℕ) : allCycles (1 : Equiv.Perm (Fin n)) = n := by
  simp [allCycles]

/-- Every permutation of a singleton is the actual identity. -/
theorem singletonPerm (sigma : Equiv.Perm (Fin 1)) : sigma = 1 := by
  apply Equiv.ext
  intro i
  exact Subsingleton.elim _ _

end Qatlib.Foundations.ProbabilityCore.Concentration.CycleCount
