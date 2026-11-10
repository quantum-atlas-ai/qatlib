/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.LcuQsvtDefs
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsExt
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily
import Qatlib.Concepts.QspSimulation.Achievability.LcuQsvt
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open Matrix Polynomial
open Qatlib Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs

structure LcuEvalOracle where

  fn : ℝ → ℂ

  readsPerEval : ℕ

  bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖fn x‖ ≤ 1

structure LcuModulus (f : ℝ → ℂ) where

  ω : ℝ → ℝ

  readsPerQuery : ℕ

  isModulus : ModulusOfContinuity f ω

structure LcuContinuousTarget where

  oracle : LcuEvalOracle

  modulus : LcuModulus oracle.fn

noncomputable def lcuBernsteinNode (n k : ℕ) : ℝ :=
  -1 + 2 * (k : ℝ) / (n : ℝ)

noncomputable def lcuBernsteinGrid (n : ℕ) : List ℝ :=
  (Finset.range (n + 1)).toList.map (lcuBernsteinNode n)

noncomputable def lcuBernsteinPoly (n : ℕ) (f : ℝ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (((n.choose k : ℕ) : ℂ) * f (lcuBernsteinNode n k)) *
      (Polynomial.C (1 / 2 : ℂ) * (X + 1)) ^ k * (Polynomial.C (1 / 2 : ℂ) * (1 - X)) ^ (n - k)

noncomputable def lcuBernsteinWeight (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k))

structure LcuApproxPlan where

  degree : ℕ

  evalReads : ℕ

  modulusReads : ℕ

  error : ℝ

  degree_pos : 0 < degree

noncomputable def lcuBernsteinError (n : ℕ) (s : ℝ) (ω : ℝ → ℝ) : ℝ :=
  ω s + ω 2 / (n * s ^ 2)

structure LcuApplicationLedger where

  angles : List ℝ

  costs : QsvtCostLedger

structure LcuDegreeZeroWitness where

  constant : ℂ

  isUnit : Complex.normSq constant = 1

  angles : List ℝ

  length_two : angles.length = 2

structure LcuSaturationWitness where

  delta : ℝ

  degree : ℕ

  responseGap : ℝ

  printedBound : ℝ

structure LcuEq3Transport where

  head : ℂ

  gates : List ℂ

  pair : Polynomial ℂ × Polynomial ℂ

  pair_eq : pair = lqEq3Pair head gates

structure LcuSynthesizedPair where

  base : ℂ

  phases : List ℂ

  table : List ℝ

  cost : ℕ

noncomputable def lcuResponseStep (z : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (Polynomial.C z * (Polynomial.X * pq.1 + (1 - Polynomial.X ^ 2) * pq.2),
    Polynomial.C (star z) * (pq.1 - Polynomial.X * pq.2))

noncomputable def lcuEq3Step (z : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (Polynomial.C z * (Polynomial.X * pq.1 - (1 - Polynomial.X ^ 2) * pq.2),
    Polynomial.C (star z) * (pq.1 + Polynomial.X * pq.2))

noncomputable def lcuEq3Fold (pq : Polynomial ℂ × Polynomial ℂ) (z : ℂ) :
    Polynomial ℂ × Polynomial ℂ := lcuEq3Step z pq

structure LcuAdaptiveScenario where

  responses : ℕ

  callsPerBranch : ℕ

  dimension : ℕ

structure LcuJaTruncation where

  tau : ℕ

  precision : ℝ

  recovered : List ℝ

structure LcuRealParameter where

  numerator : ℤ

  denominator : ℕ

  denominator_pos : 0 < denominator

  bits : ℕ

structure LcuFrameEmbedding where

  ancillas : ℕ

  prepareCalls : ℕ

  controlledSwaps : ℕ

structure LcuMachineCost where

  integerBitTime : ℕ

  peakWorkspace : ℕ

  physicalResets : ℕ

  pauliTerms : ℕ

structure LcuMachineWord where

  base : ℕ

  ops : List DynStep

structure LcuChainData where

  nodes : List ℕ

  order : ℕ

  retries : ℕ

structure LcuSourceFrameConsumer where

  frame : List ℝ

  queries : ℕ

end Qatlib.Papers.QSingValue19.AlgorithmApps
