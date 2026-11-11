/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalGraphCompilationQuan

/-!
# Compiling reflection circuits to graph measurement patterns

Legal reflection-gate words compile to legal measurement networks. The logical
matrix agrees with the circuit matrix up to the specified scalar, and every
measurement history has the stated scalar-weighted action even in the presence
of an untouched reference register.

The one-way model is introduced in [RaussendorfBriegel2001]; compositional
measurement-pattern semantics are developed in
[Danos, Kashefi & Panangaden, *The measurement calculus*][DanosKashefiPanangaden2007].
-/
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ClusterPatterns.ClusterCompile

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile

open Matrix Qatlib

/-- Every legal list of single-qubit and CNOT gates has a measurement-based graph compilation
satisfying `UniversalLocalGraphCompilation`; see [RaussendorfBriegel2000]. -/
theorem measurement_scheme_universal : UniversalLocalGraphCompilation :=
  universalLocalGraphCompilation_answer

/-- A legal reflection circuit has a legal graph-pattern compilation with the
specified logical and reference-system action. Compare
[Raussendorf & Briegel, one-way computation][RaussendorfBriegel2001]. -/
theorem universality_per_circuit (n : ℕ) (gs : List (ReflectionGate n))
    (hgs : reflectionLegal gs) :
    let G := mbqcGraphWord gs
    let a := (mbqcLocalCounts gs).1
    let b := (mbqcLocalCounts gs).2
    networkLegal (List.ofFn G) ∧
      networkLogicalMatrix (List.ofFn G) = mbqcLocalScalar gs • mbqcLogicalMatrix gs ∧
      (∀ (R : ℕ) (h : GraphHistory G)
        (X : Matrix (Fin (2 ^ n) × Fin R) (Fin (2 ^ n) × Fin R) ℂ),
        graphActualReference true G h R X = (1 / 2 : ℂ) ^ (4 * a + 2 * b) •
          (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R) * X *
            (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R))ᴴ)) := by
  (try dsimp only)
  obtain ⟨_, _, hlegal, _, _, hmat, href, _, _⟩ :=
    universalLocalGraphCompilation_answer n gs hgs
  exact ⟨hlegal, hmat, href⟩

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
