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

/-!
# Data for LCU approximation and resource plans

This module defines the interfaces `LcuEvalOracle` and `LcuModulus`, the Bernstein polynomial
`lcuBernsteinPoly`, and synthesis records used by the LCU applications of
[GilyenSuLowWiebe2019]. Additional records store phase transport, finite parameter descriptions,
frame resources, and dynamic machine instruction lists.

## Main statements

* `LcuContinuousTarget`: Bundles a bounded evaluation interface with a modulus of continuity.
* `lcuBernsteinPoly`: Constructs the Bernstein polynomial on [−1, 1].
* `LcuSynthesizedPair`: Stores a base phase, phase entries, angle table, and cost.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open Matrix Polynomial
open Qatlib Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs

/-- A complex valued function bounded by one on [−1, 1], together with a read count per
evaluation. -/
structure LcuEvalOracle where

  fn : ℝ → ℂ

  readsPerEval : ℕ

  bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖fn x‖ ≤ 1

/-- A modulus of continuity for a function, together with a read count per modulus query. -/
structure LcuModulus (f : ℝ → ℂ) where

  ω : ℝ → ℝ

  readsPerQuery : ℕ

  isModulus : ModulusOfContinuity f ω

/-- A bounded evaluation interface paired with a modulus of continuity for its function. -/
structure LcuContinuousTarget where

  oracle : LcuEvalOracle

  modulus : LcuModulus oracle.fn

/-- The Bernstein node −1 + 2k/n on the interval [−1, 1]. -/
noncomputable def lcuBernsteinNode (n k : ℕ) : ℝ :=
  -1 + 2 * (k : ℝ) / (n : ℝ)

/-- The list of Bernstein nodes indexed by zero through n. -/
noncomputable def lcuBernsteinGrid (n : ℕ) : List ℝ :=
  (Finset.range (n + 1)).toList.map (lcuBernsteinNode n)

/-- The complex Bernstein polynomial built from samples of f at the n + 1 grid nodes of [−1, 1]. -/
noncomputable def lcuBernsteinPoly (n : ℕ) (f : ℝ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (((n.choose k : ℕ) : ℂ) * f (lcuBernsteinNode n k)) *
      (Polynomial.C (1 / 2 : ℂ) * (X + 1)) ^ k * (Polynomial.C (1 / 2 : ℂ) * (1 - X)) ^ (n - k)

/-- The real Bernstein weight (n choose k)((x + 1)/2)^k((1 − x)/2)^(n − k). -/
noncomputable def lcuBernsteinWeight (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (((x + 1) / 2) ^ k * ((1 - x) / 2) ^ (n - k))

/-- A positive degree approximation plan storing evaluation reads, modulus reads, and a real
error value. -/
structure LcuApproxPlan where

  degree : ℕ

  evalReads : ℕ

  modulusReads : ℕ

  error : ℝ

  degree_pos : 0 < degree

/-- The scalar Bernstein error expression ω(s) + ω(2)/(ns²). -/
noncomputable def lcuBernsteinError (n : ℕ) (s : ℝ) (ω : ℝ → ℝ) : ℝ :=
  ω s + ω 2 / (n * s ^ 2)

/-- A real angle list paired with a QSVT cost ledger. -/
structure LcuApplicationLedger where

  angles : List ℝ

  costs : QsvtCostLedger

/-- A unit modulus constant paired with an angle list of length two. -/
structure LcuDegreeZeroWitness where

  constant : ℂ

  isUnit : Complex.normSq constant = 1

  angles : List ℝ

  length_two : angles.length = 2

/-- A record of perturbation size, degree, response gap, and printed bound. -/
structure LcuSaturationWitness where

  delta : ℝ

  degree : ℕ

  responseGap : ℝ

  printedBound : ℝ

/-- A head phase, phase list, and polynomial pair certified to equal their Equation 3 pair. -/
structure LcuEq3Transport where

  head : ℂ

  gates : List ℂ

  pair : Polynomial ℂ × Polynomial ℂ

  pair_eq : pair = lqEq3Pair head gates

/-- A record storing a base, complex phase list, real angle table, and natural synthesis cost. -/
structure LcuSynthesizedPair where

  base : ℂ

  phases : List ℂ

  table : List ℝ

  cost : ℕ

/-- The response recurrence step on a polynomial pair using a phase and its conjugate. -/
noncomputable def lcuResponseStep (z : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (Polynomial.C z * (Polynomial.X * pq.1 + (1 - Polynomial.X ^ 2) * pq.2),
    Polynomial.C (star z) * (pq.1 - Polynomial.X * pq.2))

/-- The Equation 3 polynomial pair recurrence with the specified signs in its two components. -/
noncomputable def lcuEq3Step (z : ℂ) (pq : Polynomial ℂ × Polynomial ℂ) :
    Polynomial ℂ × Polynomial ℂ :=
  (Polynomial.C z * (Polynomial.X * pq.1 - (1 - Polynomial.X ^ 2) * pq.2),
    Polynomial.C (star z) * (pq.1 + Polynomial.X * pq.2))

/-- The Equation 3 recurrence step with the polynomial pair supplied before the phase, for use
in a fold. -/
noncomputable def lcuEq3Fold (pq : Polynomial ℂ × Polynomial ℂ) (z : ℂ) :
    Polynomial ℂ × Polynomial ℂ := lcuEq3Step z pq

/-- A record of response count, calls per branch, and dimension for an adaptive scenario. -/
structure LcuAdaptiveScenario where

  responses : ℕ

  callsPerBranch : ℕ

  dimension : ℕ

/-- A record of a natural time parameter, precision, and recovered real values for a
Jacobi–Anger truncation. -/
structure LcuJaTruncation where

  tau : ℕ

  precision : ℝ

  recovered : List ℝ

/-- An integer numerator and positive natural denominator, together with a bit count. -/
structure LcuRealParameter where

  numerator : ℤ

  denominator : ℕ

  denominator_pos : 0 < denominator

  bits : ℕ

/-- A record of ancilla count, preparation calls, and controlled swaps for a frame embedding. -/
structure LcuFrameEmbedding where

  ancillas : ℕ

  prepareCalls : ℕ

  controlledSwaps : ℕ

/-- A record of integer bit time, peak workspace, physical reset count, and Pauli term count. -/
structure LcuMachineCost where

  integerBitTime : ℕ

  peakWorkspace : ℕ

  physicalResets : ℕ

  pauliTerms : ℕ

/-- A base register size together with a list of dynamic instructions. -/
structure LcuMachineWord where

  base : ℕ

  ops : List DynStep

/-- A list of natural nodes with an order and retry count. -/
structure LcuChainData where

  nodes : List ℕ

  order : ℕ

  retries : ℕ

/-- A list of real frame values paired with a query count. -/
structure LcuSourceFrameConsumer where

  frame : List ℝ

  queries : ℕ

end Qatlib.Papers.QSingValue19.AlgorithmApps
