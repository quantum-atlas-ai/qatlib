/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalGraphCompilationQuan
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

theorem measurement_scheme_universal : UniversalLocalGraphCompilation :=
  universalLocalGraphCompilation_answer

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
