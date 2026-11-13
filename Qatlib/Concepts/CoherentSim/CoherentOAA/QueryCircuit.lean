/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT

/-!
# Oracle instruction words and QSVT compilation

This module defines circuit words with fixed matrix gates and separate forward and adjoint
oracle queries. It provides matrix evaluation and independent query and fixed-gate counts,
making the resource accounting for singular value transformation explicit
[GilyenSuLowWiebe2019].

The compiler `compileQSVT` realizes the phased alternating sequence. Exchanging query directions
corresponds to replacing the oracle by its adjoint and preserves both instruction counts.

## Main statements

* `evaluate_compileQSVT`: compilation evaluates to `phasedAlternating`.
* `queryCount_compileQSVT`: one oracle query is used per phase-list entry.
* `gateCount_compileQSVT`: the fixed-gate count is the phase-list length plus one.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix

/-- An oracle circuit instruction consisting of a fixed matrix gate, a forward oracle query, or
an adjoint oracle query. -/
inductive AdjointStep (H : Type*) where
  | gate : Matrix H H ℂ → AdjointStep H
  | forward : AdjointStep H
  | backward : AdjointStep H

/-- The instruction transformation exchanging forward and backward oracle queries while
preserving fixed gates. -/
def swapQueries {H : Type*} : AdjointStep H → AdjointStep H
  | .gate V => .gate V
  | .forward => .backward
  | .backward => .forward

/-- The number of forward and backward oracle query instructions in a circuit word. -/
def adjointQueryCount {H : Type*} : List (AdjointStep H) → ℕ
  | [] => 0
  | .gate _ :: cs => adjointQueryCount cs
  | .forward :: cs => adjointQueryCount cs + 1
  | .backward :: cs => adjointQueryCount cs + 1

/-- The number of fixed matrix gate instructions in a circuit word. -/
def adjointGateCount {H : Type*} : List (AdjointStep H) → ℕ
  | [] => 0
  | .gate _ :: cs => adjointGateCount cs + 1
  | .forward :: cs => adjointGateCount cs
  | .backward :: cs => adjointGateCount cs

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The matrix of an instruction, interpreting forward queries as `U` and backward queries as
`Uᴴ`. -/
noncomputable def instructionMatrix (U : Matrix H H ℂ) : AdjointStep H → Matrix H H ℂ
  | .gate V => V
  | .forward => U
  | .backward => Uᴴ

/-- The product of the instruction matrices in list order, with the empty word evaluating to the
identity. -/
noncomputable def evaluate (U : Matrix H H ℂ) : List (AdjointStep H) → Matrix H H ℂ
  | [] => 1
  | c :: cs => instructionMatrix U c * evaluate U cs

/-- Exchanging all query directions has the same evaluation as replacing the oracle by its
conjugate transpose. -/
theorem evaluate_swapQueries (U : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate U (cs.map swapQueries) = evaluate Uᴴ cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [evaluate, instructionMatrix, swapQueries, ih]

omit [Fintype H] [DecidableEq H] in

/-- Exchanging forward and backward queries preserves the oracle query count. -/
@[simp] theorem adjointQueryCount_swapQueries (cs : List (AdjointStep H)) :
    adjointQueryCount (cs.map swapQueries) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [swapQueries, adjointQueryCount, ih]

omit [Fintype H] [DecidableEq H] in

/-- Exchanging forward and backward queries preserves the fixed-gate count. -/
@[simp] theorem adjointGateCount_swapQueries (cs : List (AdjointStep H)) :
    adjointGateCount (cs.map swapQueries) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [swapQueries, adjointGateCount, ih]

/-- The recursive oracle word implementing the phased alternating sequence, with query
directions exchanged in each recursive tail. -/
noncomputable def compileQSVT (P Q : Matrix H H ℂ) (base : ℂ) :
    List ℂ → List (AdjointStep H)
  | [] => [.gate (phaseRotation Q base)]
  | z :: zs => .gate (phaseRotation Q z) :: .forward ::
      (compileQSVT Q P base zs).map swapQueries

/-- The compiled QSVT word evaluates exactly to the phased alternating matrix sequence. -/
theorem evaluate_compileQSVT (U P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    evaluate U (compileQSVT P Q base zs) = phasedAlternating U P Q base zs := by
  induction zs generalizing U P Q with
  | nil => simp [compileQSVT, evaluate, instructionMatrix, phasedAlternating]
  | cons z zs ih =>
    simp [compileQSVT, evaluate, instructionMatrix, evaluate_swapQueries, ih,
      phasedAlternating, Matrix.mul_assoc]

omit [Fintype H] in

/-- The compiled QSVT word has one oracle query per phase-list entry. -/
theorem queryCount_compileQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointQueryCount (compileQSVT P Q base zs) = zs.length := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileQSVT, adjointQueryCount, ih]

omit [Fintype H] in

/-- The compiled QSVT word has one more fixed gate than the number of phase-list entries. -/
theorem gateCount_compileQSVT (P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    adjointGateCount (compileQSVT P Q base zs) = zs.length + 1 := by
  induction zs generalizing P Q with
  | nil => rfl
  | cons z zs ih => simp [compileQSVT, adjointGateCount, ih]

end Qatlib.Concepts.CoherentSim.CoherentOAA
