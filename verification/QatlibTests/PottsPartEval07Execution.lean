/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Qatlib.Papers.PottsPartEval07.ExactRecovery.MacWilliams
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.PottsReduction
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.QueryReduction

@[expose] public section

/-! # Potts phase-recovery consumer -/

namespace QatlibTests.PottsPartEval07Execution

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
open Qatlib.Papers.PottsPartEval07.ExactRecovery

example : latticeDecode 2 2 = 1 := by
  norm_num [latticeDecode]

example : batchQueries 3 4 = 9 := by
  rw [batchQueries_eq]
  norm_num

/-- The consumer invokes the certified-code Potts query reduction. -/
theorem potts_reduction_consumer
    {q : ℕ} [NeZero q] {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {classes terms classSize : ℕ} (hd : 0 < terms) (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q))
    (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (k : ℕ) (hcard : Fintype.card C = q ^ k)
    (spacing : ℕ) (hspacing : 0 < spacing) (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin classes → Fin terms → ℂ) (hc : ∀ i a, ‖coefficient i a‖ ≤ 1)
    (phase : Fin terms → ℝ)
    (hformula : ∀ i, turnWeight base scale (coefficient i) phase =
      hammingWeight (partition.representative i).val)
    (hdiv : ∀ i, spacing ∣ hammingWeight (partition.representative i).val)
    (radius : ℝ) (hr : 0 < radius)
    (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2)
    (y : ℝ) (hy : y ≠ 0) :
    3 / 4 ≤ exactMass (q := q) ends (q ^ k) classSize (sampleSize terms radius) spacing
      base scale coefficient phase y ∧
      (batchQueries terms (sampleSize terms radius) : ℝ) ≤ 3 * (terms : ℝ) ^ 2 / radius :=
  query_reduction hd ends C partition hdual k hcard spacing hspacing base scale hs
    coefficient hc phase hformula hdiv radius hr hp y hy

end QatlibTests.PottsPartEval07Execution
