/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MCMontanaro15.MonteCarlo.Basic
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

noncomputable def truncatedExpectation {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) (k : ℕ) : ℝ :=
  p.expect (fun x => if (2 : ℝ) ^ k ≤ f x then 0 else f x)

noncomputable def truncationThreshold (k : ℕ) : ℝ := (2 : ℝ) ^ k

noncomputable def centeredExpectation {X : Type} [Fintype X] (p : FinDist X)
    (f : X → ℝ) (σ m : ℝ) : ℝ :=
  p.expect (fun x => f x / σ - m)

structure NextCostLedger where

  copies : ℕ

  reflections : ℕ

  medians : ℕ

  classicalBits : ℕ

  tableSelectGates : ℕ

  gcdGates : ℕ

  memoryBits : ℕ

  persistentSpaceBits : ℕ

def NextCostLedger.replicate (c : NextCostLedger) (n : ℕ) : NextCostLedger :=
  { copies := c.copies * n
    reflections := c.reflections * n
    medians := c.medians * n
    classicalBits := c.classicalBits * n
    tableSelectGates := c.tableSelectGates * n
    gcdGates := c.gcdGates * n
    memoryBits := c.memoryBits * n
    persistentSpaceBits := c.persistentSpaceBits * n }

structure PrepareLedger where

  statePreparations : ℕ

  inversePreparations : ℕ

  angleGates : ℕ

  classicalBits : ℕ

noncomputable def prepareLedger (angleGates classicalBits : ℕ) : PrepareLedger :=
  { statePreparations := 1
    inversePreparations := 1
    angleGates := angleGates
    classicalBits := classicalBits }

noncomputable def tableSelectProgram (k : ℕ) (m : ℝ) : ℕ := selectedBand k m

noncomputable def tableSelectGates (k : ℕ) : ℕ := k

noncomputable def gcdGates (bits : ℕ) : ℕ := bits

noncomputable def memoryBits (N k Q maxAbs : ℕ) : ℕ := Nat.log2 (N * maxAbs + 1) + k + 1

noncomputable def persistentSpaceBits (N k Q maxAbs : ℕ) : ℕ :=
  Nat.log2 (N * maxAbs + 1) + Nat.log2 Q + Nat.log2 (k + 1)

end StageBMONTECARLO
end Qatlib.Papers.MCMontanaro15.MonteCarlo
