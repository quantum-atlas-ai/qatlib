/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic

/-!
# Truncation and refined Monte Carlo cost records

This module defines truncated and centered expectations and additional resource records for the
analysis of [Montanaro2015]. The functions `truncatedExpectation` and `truncationThreshold` use
a dyadic cutoff, while `centeredExpectation` averages a scaled and shifted payoff.

The structures `NextCostLedger` and `PrepareLedger` record quantum and classical resource
counts. The remaining functions specify table-selection, arithmetic, and space formulas used by
the refined statements.

## Main statements

* `NextCostLedger`: Resource counts including table-selection gates and space.
* `NextCostLedger.replicate`: Componentwise repetition of resource counts.
* `prepareLedger`: One preparation and one inverse preparation with supplied auxiliary costs.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo
namespace StageBMONTECARLO

open Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic.StageBMONTECARLO
open Qatlib.Papers.MCMontanaro15.MonteCarlo.StageBMONTECARLO
open Qatlib
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The payoff expectation with all values at least 2^k replaced by zero. -/
noncomputable def truncatedExpectation {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) (k : ℕ) : ℝ :=
  p.expect (fun x => if (2 : ℝ) ^ k ≤ f x then 0 else f x)

/-- The dyadic truncation threshold 2^k. -/
noncomputable def truncationThreshold (k : ℕ) : ℝ := (2 : ℝ) ^ k

/-- The expectation of the scaled and shifted payoff f/σ − m. -/
noncomputable def centeredExpectation {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) (σ m : ℝ) : ℝ :=
  p.expect (fun x => f x / σ - m)

/-- Natural-number resource counts for copies, reflections, medians, classical bits,
table-selection gates, greatest-common-divisor gates, memory, and persistent space. -/
structure NextCostLedger where

  copies : ℕ

  reflections : ℕ

  medians : ℕ

  classicalBits : ℕ

  tableSelectGates : ℕ

  gcdGates : ℕ

  memoryBits : ℕ

  persistentSpaceBits : ℕ

/-- The refined resource ledger obtained by multiplying every component by n. -/
def NextCostLedger.replicate (c : NextCostLedger) (n : ℕ) : NextCostLedger :=
  { copies := c.copies * n
    reflections := c.reflections * n
    medians := c.medians * n
    classicalBits := c.classicalBits * n
    tableSelectGates := c.tableSelectGates * n
    gcdGates := c.gcdGates * n
    memoryBits := c.memoryBits * n
    persistentSpaceBits := c.persistentSpaceBits * n }

/-- Counts for state preparations, inverse preparations, angle gates, and classical bits. -/
structure PrepareLedger where

  statePreparations : ℕ

  inversePreparations : ℕ

  angleGates : ℕ

  classicalBits : ℕ

/-- A preparation ledger with one state preparation, one inverse preparation, and the supplied
angle-gate and classical-bit counts. -/
noncomputable def prepareLedger (angleGates classicalBits : ℕ) : PrepareLedger :=
  { statePreparations := 1
    inversePreparations := 1
    angleGates := angleGates
    classicalBits := classicalBits }

/-- The table-selection output defined by `selectedBand k m`. -/
noncomputable def tableSelectProgram (k : ℕ) (m : ℝ) : ℕ := selectedBand k m

/-- The table-selection gate count model equal to the cutoff k. -/
noncomputable def tableSelectGates (k : ℕ) : ℕ := k

/-- The greatest-common-divisor gate count model equal to the supplied bit count. -/
noncomputable def gcdGates (bits : ℕ) : ℕ := bits

/-- The memory-bit expression log₂(N maxAbs + 1) + k + 1, using the natural binary logarithm. -/
noncomputable def memoryBits (N k Q maxAbs : ℕ) : ℕ := Nat.log2 (N * maxAbs + 1) + k + 1

/-- The persistent-space expression log₂(N maxAbs + 1) + log₂ Q + log₂(k + 1), using natural
binary logarithms. -/
noncomputable def persistentSpaceBits (N k Q maxAbs : ℕ) : ℕ :=
  Nat.log2 (N * maxAbs + 1) + Nat.log2 Q + Nat.log2 (k + 1)

end StageBMONTECARLO
end Qatlib.Papers.MCMontanaro15.MonteCarlo
