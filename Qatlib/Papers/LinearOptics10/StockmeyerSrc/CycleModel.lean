/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.CycleCount
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Basic.Real.Basic

@[expose] public section


/-! # Fixed points missing from the historical colored-cycle model

The old cycleCount is cycleType.card, which counts nontrivial cycles only.
The fixed source includes fixed points in cyc(sigma). The unrestricted old
Proposition55 already fails at n=1,c=2. A corrected concrete count is kept,
without asserting the full colored-permutation enumeration theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.CycleModel
open Qatlib.Foundations.ProbabilityCore.Concentration.CycleCount

/-- The complete literal historical colored-cycle formula. -/
def LegacyColored : Prop := ∀ n c : ℕ, 1 ≤ c →
  (∑ sigma : Equiv.Perm (Fin n), (c : ℝ)^nontrivCycles sigma) / (n.factorial : ℝ) =
    ((n+c-1).choose (c-1) : ℝ)

/-- The exact full old target is refuted on the valid one-point, two-color input. -/
theorem legacyRefuted : ¬LegacyColored := by
  intro h
  have hn := h 1 2 (by decide)
  have hc (sigma : Equiv.Perm (Fin 1)) : nontrivCycles sigma = 0 := by
    rw [singletonPerm sigma, nontrivIdentity]
  norm_num [hc, Fintype.card_perm] at hn

/-- The corrected singleton-cycle count gives the source value two in the same concrete input. -/
theorem correctedOne :
    (∑ sigma : Equiv.Perm (Fin 1), (2 : ℝ)^allCycles sigma) / (Nat.factorial 1 : ℝ) = 2 := by
  have hc (sigma : Equiv.Perm (Fin 1)) : allCycles sigma = 1 := by
    rw [singletonPerm sigma, identityCount]
  simp [hc]

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.CycleModel
