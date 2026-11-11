/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFindDefs
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution

/-!
# Exact decoding laws for general walk search

`generalFindDecoder` returns only marked vertices, and `generalFindSuccess` equals the marked
mass of a state. For `generalDetectionExecution`, this mass is exactly the sum of kernel weights
on the marked set. `GeneralMnrsFindAccount` packages these laws and setup legality, while
`generalMnrsFindResidual` records additional constructions outside this account. For background
on search via quantum walks, see [MagniezNayakRolandSantha2011].

## Main statements

* `generalFindDecoder_no_false_positive`: Every value returned by `generalFindDecoder S` belongs
  to the marked set `S`.
* `clause7_complete`: Decoder reflexivity holds and the detection execution success is the sum
  of the kernel weights on `S`.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccess
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

namespace Qatlib.Concepts.WalkSearch.MainResults
namespace GeneralMnrsFind

open Matrix
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecution
open Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFindDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false

/-- Every value returned by `generalFindDecoder S` belongs to the marked set `S`. -/
theorem generalFindDecoder_no_false_positive {V : ℕ} (S : Finset (GeneralVertex V))
    (u v : GeneralVertex V) (h : generalFindDecoder S u = some v) : v ∈ S := by
  by_cases hu : u ∈ S
  · simp [generalFindDecoder, hu] at h
    subst h
    exact hu
  · simp [generalFindDecoder, hu] at h

/-- The decoder returns `none` on a vertex exactly when that vertex is outside `S`. -/
theorem generalFindDecoder_none_iff {V : ℕ} (S : Finset (GeneralVertex V))
    (u : GeneralVertex V) : generalFindDecoder S u = none ↔ u ∉ S := by
  by_cases hu : u ∈ S
  · simp [generalFindDecoder, hu]
  · simp [generalFindDecoder, hu]

/-- The success functional `generalFindSuccess` equals `generalMarkedMass` for every state. -/
theorem generalFindSuccess_eq {V : ℕ} (S : Finset (GeneralVertex V))
    (ψ : QState (GeneralVertex V)) :
    generalFindSuccess S ψ = generalMarkedMass S ψ := rfl

/-- Equal marked sets and equal setup repetition counts give equal decoders and equal setup
words. -/
theorem generalFind_program_independent_of_mass {V : ℕ} (K : GeneralKernel V)
    (p : GeneralVertex V) (S : Finset (GeneralVertex V)) (k : ℕ)
    (S' : Finset (GeneralVertex V)) (k' : ℕ)
    (hS : S = S') (hk : k = k') :
    generalFindDecoder S = generalFindDecoder S' ∧
      generalSetupWord K p k = generalSetupWord K p k' := by
  subst hS
  subst hk
  exact ⟨rfl, rfl⟩

/-- The success functional on `generalDetectionExecution K p S` is exactly the sum of `K.weight
p u` over marked vertices `u`. -/
theorem generalFind_success_exact {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) :
    generalFindSuccess S (generalDetectionExecution K p S) = ∑ u ∈ S, (K.weight p u : ℝ) := by
  rw [generalFindSuccess_eq]
  exact generalDetectionExecution_exact K p S

/-- Descriptions of the recursion, spectral, sampling, resource, and reduction constructions not
supplied by the general find account. -/
def generalMnrsFindResidual : List String :=
  [ "the MNRS recursion schedule with a changing fresh slice is not built here",
    "the R(P) spectral output and the non-invertible branch are not built here",
    "the multi-band phase word and the fair-bit length sampling are not built here",
    "the finite-gate and bit-time ledgers of the find execution are not built here",
    "the interleaving with the relations/Johnson/triangle/element-distinctness reductions is not built here" ]

/-- A proposition bundling decoder soundness and exactness, the marked mass success law, the
exact kernel weight success formula, and setup word legality. -/
structure GeneralMnrsFindAccount (V : ℕ) (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) : Prop where

  noFalsePositive : ∀ u v, generalFindDecoder S u = some v → v ∈ S

  decoderExact : ∀ u, generalFindDecoder S u = none ↔ u ∉ S

  successLaw : ∀ ψ, generalFindSuccess S ψ = generalMarkedMass S ψ

  exactSuccess : generalFindSuccess S (generalDetectionExecution K p S)
      = ∑ u ∈ S, (K.weight p u : ℝ)

  setupLegal : WellFormedAdjointCircuit (generalSetupWord K p k)

/-- The decoder, success functional, and setup word satisfy every field of
`GeneralMnrsFindAccount`. -/
theorem clause5_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    GeneralMnrsFindAccount V K p S k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v h
    exact generalFindDecoder_no_false_positive S u v h
  · intro u
    exact generalFindDecoder_none_iff S u
  · intro ψ
    exact generalFindSuccess_eq S ψ
  · exact generalFind_success_exact K p S
  · exact generalSetupWord_wellFormed K p k

/-- The decoder has no false positives and the detection execution satisfies the exact kernel
weight success formula, together with decoder reflexivity. -/
theorem clause6_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    (∀ u v, generalFindDecoder S u = some v → v ∈ S) ∧
      generalFindSuccess S (generalDetectionExecution K p S)
        = ∑ u ∈ S, (K.weight p u : ℝ) ∧
      generalFindDecoder S = generalFindDecoder S := by
  exact ⟨fun u v h => generalFindDecoder_no_false_positive S u v h,
    generalFind_success_exact K p S, rfl⟩

/-- Decoder reflexivity holds and the detection execution success is the sum of the kernel
weights on `S`. -/
theorem clause7_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    (generalFindDecoder S = generalFindDecoder S) ∧
      generalFindSuccess S (generalDetectionExecution K p S)
        = ∑ u ∈ S, (K.weight p u : ℝ) := by
  exact ⟨rfl, generalFind_success_exact K p S⟩

end GeneralMnrsFind
end Qatlib.Concepts.WalkSearch.MainResults
