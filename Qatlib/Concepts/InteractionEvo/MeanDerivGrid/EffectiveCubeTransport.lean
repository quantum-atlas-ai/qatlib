/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions

/-!
# Injective and collision parts of Dyson cube sums

This module partitions a repeated-index Dyson cube sum into its injective-index part and
collision part. It proves that collisions vanish in degrees zero and one, and that degree-one
cube and strict sums coincide. These finite-sum identities support the Dyson grid constructions
in the setting of [LowWiebe2018].

## Main statements

* `effectiveCubeRaw_partition`: separate injective words from collisions.
* `effectiveCubeRaw_one`: identify the degree-one cube and strict sums.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.InteractionEvo.EffCosts

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The full sorted cube sum equals its injective-index contribution plus the collision
contribution. -/
theorem effectiveCubeRaw_partition {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) :
    effectiveCubeRaw H t M k =
      (∑ v : Fin k → Fin M, if Function.Injective v then effectiveSortedWord H t M k v else 0) +
      effectiveCollisionRaw H t M k := by
  classical
  unfold effectiveCubeRaw effectiveCollisionRaw
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : Function.Injective v <;> simp [h]

/-- The collision contribution vanishes in degrees zero and one. -/
theorem effectiveCollisionRaw_zero {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M : ℕ) :
    effectiveCollisionRaw H t M 0 = 0 ∧ effectiveCollisionRaw H t M 1 = 0 := by
  have hinj (k : ℕ) [Subsingleton (Fin k)] (v : Fin k → Fin M) : Function.Injective v := by
    intro i j _
    exact Subsingleton.elim i j
  constructor
  · simp only [effectiveCollisionRaw,if_pos (hinj 0 _),Finset.sum_const_zero]
  · simp only [effectiveCollisionRaw,if_pos (hinj 1 _),Finset.sum_const_zero]

/-- The repeated-index cube sum and the strict sum coincide in degree one. -/
theorem effectiveCubeRaw_one {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M : ℕ) :
    effectiveCubeRaw H t M 1 = effectiveStrictRaw H t M 1 := by
  unfold effectiveCubeRaw effectiveStrictRaw
  apply Finset.sum_congr rfl
  intro v _
  have hv : StrictMono v := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega
  simp [effectiveSortedWord,hv,List.ofFn_succ]

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
