/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.UniversalLocalGraphCompilationQuan

/-!
# Conditioning on measurement-pattern histories

This module defines `referenceOutput` for a compiled local gate list and derives formulas for
sums over selected measurement histories. For legal lists, each subset contributes its
cardinality times the common branch weight, and rescaling any nonempty subset recovers the same
logical output with the reference unchanged. These are instrument-level consequences of the
one-way computation framework of [RaussendorfBriegel2000].

## Main statements

* `frontier1`: Constructs the branch instrument and gives subset probability and joint-output
  formulas.
* `conditional_reference`: Normalizing any nonempty subset of histories gives `referenceOutput`.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Concepts.ClusterPatterns.PauliNetwork
open Qatlib.Concepts.ClusterPatterns.Preentangled

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile

open Qatlib  Matrix
open scoped Classical BigOperators

/-- The joint operator obtained by conjugating the system by `mbqcLogicalMatrix gs` while
leaving the finite reference unchanged. -/
def referenceOutput {n : ℕ} (gs : List (ReflectionGate n)) (R : ℕ)
    (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :=
  TensorGate (mbqcLogicalMatrix gs) (1 : Operator R) * X *
    (TensorGate (mbqcLogicalMatrix gs) (1 : Operator R))ᴴ

/-- A legal local gate list yields an instrument realizing its graph branches, with subset
probabilities proportional to subset cardinality. The corresponding subset sum on any joint
operator is the same scalar times `referenceOutput`. -/
theorem frontier1 {n : ℕ} (gs : List (ReflectionGate n)) (hgs : reflectionLegal gs) :
    let G := mbqcGraphWord gs
    let m := 4*(mbqcLocalCounts gs).1 + 2*(mbqcLocalCounts gs).2
    ∃ I : Instrument (GraphHistory G) (2^n) (2^n),
      (∀ h ρ, I.branch h ρ = graphActualBranch true G h ρ) ∧
      (∀ (ρ : Operator (2^n)), IsDensityOperator ρ → ∀ S : Finset (GraphHistory G),
        (∑ h ∈ S, instrumentProb I ρ h) = (S.card : ℝ) * (1/2 : ℝ)^m) ∧
      (∀ (S : Finset (GraphHistory G)) (R : ℕ)
        (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ),
        (∑ h ∈ S, graphActualReference true G h R X) =
          ((S.card : ℂ) * (1/2 : ℂ)^m) • referenceOutput gs R X) := by
  (try dsimp only)
  obtain ⟨_, _, _, _, _, _, href, ⟨I, hbr, hprob, _⟩, _⟩ :=
    universalLocalGraphCompilation_answer n gs hgs
  refine ⟨I, hbr, ?_, ?_⟩
  · intro ρ hρ S
    simp only [hprob ρ hρ, Finset.sum_const, nsmul_eq_mul]
  · intro S R X
    simp only [href R, ← Finset.sum_smul, Finset.sum_const, nsmul_eq_mul, referenceOutput]

/-- Rescaling the branch sum over any nonempty set of histories by its uniform weight recovers
`referenceOutput`. -/
theorem conditional_reference {n : ℕ} (gs : List (ReflectionGate n)) (hgs : reflectionLegal gs)
    (S : Finset (GraphHistory (mbqcGraphWord gs))) (hS : S.Nonempty) (R : ℕ)
    (X : Matrix (Fin (2^n) × Fin R) (Fin (2^n) × Fin R) ℂ) :
    (((S.card : ℂ) * (1/2 : ℂ)^(4*(mbqcLocalCounts gs).1+2*(mbqcLocalCounts gs).2))⁻¹) •
      (∑ h ∈ S, graphActualReference true (mbqcGraphWord gs) h R X) = referenceOutput gs R X := by
  obtain ⟨_, _, _, href⟩ := frontier1 gs hgs
  rw [href S R X, smul_smul]
  have hc : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  have hw : (S.card : ℂ) * (1/2 : ℂ)^(4*(mbqcLocalCounts gs).1+2*(mbqcLocalCounts gs).2) ≠ 0 :=
    mul_ne_zero hc (pow_ne_zero _ (by norm_num))
  rw [inv_mul_cancel₀ hw, one_smul]

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
