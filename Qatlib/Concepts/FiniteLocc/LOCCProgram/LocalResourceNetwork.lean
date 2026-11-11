/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs

/-!
# EPR inventories and interactive resource bounds

This module collects guarantees for finite EPR inventories and their local use. It proves
normalization and positivity, independent updates at distinct slots, preservation of reference
marginals by complete local operations, and the factory's preparation and gate charges. The EPR
resource setting is motivated by teleportation [BennettEtAl1993Teleportation].

The interactive-message results give the transcript strategy equations, equality under equal
inputs, a depth-based integer Kraft bound, prefix freeness, and the length and exponential
identities for repeated encodings.

## Main statements

* `clause6_complete`: collect EPR inventory, local-channel, and factory guarantees.
* `clause7_kraft`: bound message-tree Kraft mass and prove prefix freeness.
* `clause7_complete`: collect transcript and encoding resource identities.

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs

namespace Qatlib.Concepts.FiniteLocc.LOCCProgram
namespace LocalResourceNetwork

open Matrix
open Qatlib.Concepts.FiniteLocc.LOCCProgram.LocalResourceNetworkDefs
open scoped Classical BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The EPR factor is positive semidefinite, has trace one, and equals one half of the projector
formed from its unnormalized equal-bit vector. -/
theorem clause6_epr_factor :
    eprFactor.PosSemidef ∧ Matrix.trace eprFactor = 1 ∧
    eprFactor = (1 / 2 : ℂ) • outerProduct (fun ij => if ij.1 = ij.2 then 1 else 0) :=
  ⟨eprFactor_psd, eprFactor_trace, eprFactor_canonical⟩

/-- Every finite tensor inventory of EPR factors is positive semidefinite and has trace one. -/
theorem clause6_inventory (m : ℕ) :
    (eprInventory m).PosSemidef ∧ Matrix.trace (eprInventory m) = 1 :=
  ⟨eprInventory_psd m, eprInventory_trace m⟩

/-- Actions on two distinct EPR slots update exactly those tensor factors by their respective
conjugations. -/
theorem clause6_exclusive_consumption (m : ℕ) (j₁ j₂ : Fin m) (hne : j₁ ≠ j₂)
    (A₁ A₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    slotAction m j₂ A₂ * (slotAction m j₁ A₁ * eprInventory m * (slotAction m j₁ A₁)ᴴ)
        * (slotAction m j₂ A₂)ᴴ
      = productMatrix (fun j' =>
          if j' = j₁ then A₁ * eprFactor * A₁ᴴ else if j' = j₂ then A₂ * eprFactor * A₂ᴴ
          else eprFactor) :=
  two_slot_consumption m j₁ j₂ hne A₁ A₂

/-- A complete local Kraus channel preserves the reference marginal. -/
theorem clause6_locality {D R s : ℕ} (K : Fin s → Operator D)
    (hK : ∑ k, (K k)ᴴ * (K k) = 1) (ρ : LocalJoint D R) :
    partialTraceFirst (localChannel K ρ) = partialTraceFirst ρ :=
  localChannel_reference_preserved K hK ρ

/-- The sum of a complete local instrument's branches preserves the reference marginal. -/
theorem clause6_record_feedback_instrument {D R s : ℕ} (K : Fin s → Operator D)
    (hK : ∑ k, (K k)ᴴ * (K k) = 1) (ρ : LocalJoint D R) :
    partialTraceFirst (∑ k, localConj (K k) ρ) = partialTraceFirst ρ :=
  localInstrument_reference_preserved K hK ρ

/-- A local unitary regarded as a single-outcome channel preserves the reference marginal. -/
theorem clause6_conditional_unitary {D R : ℕ} (U : Operator D)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) (ρ : LocalJoint D R) :
    partialTraceFirst (localChannel (fun _ : Fin 1 => U) ρ) = partialTraceFirst ρ :=
  localUnitary_reference_preserved U hU ρ

/-- The factory prepares the EPR factor from `e00`, and both its inventory charge and its
gate-list length are twice the number of slots. -/
theorem clause6_supply :
    outerProduct (eprFactoryUnitary *ᵥ e00) = eprFactor ∧
    (∀ (inv : EPRInventory), inv.gateCost = 2 * inv.slots) ∧
    (∀ m : ℕ, (eprFactoryGates m).length = 2 * m) :=
  ⟨eprFactoryOutput_eq, EPRInventory.gateCost_eq, eprFactoryGates_length⟩

/-- The EPR factor and its inventories are normalized positive operators, distinct slots update
independently, and complete local channels and instruments preserve the reference marginal.
This also records the factory output and the two-gates-per-slot charge, in the teleportation
setting of [BennettEtAl1993Teleportation]. -/
theorem clause6_complete :
    eprFactor.PosSemidef ∧ Matrix.trace eprFactor = 1 ∧
    (∀ m : ℕ, (eprInventory m).PosSemidef ∧ Matrix.trace (eprInventory m) = 1) ∧
    (∀ m : ℕ, ∀ j₁ j₂ : Fin m, j₁ ≠ j₂ →
      ∀ A₁ A₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
        slotAction m j₂ A₂ * (slotAction m j₁ A₁ * eprInventory m * (slotAction m j₁ A₁)ᴴ)
            * (slotAction m j₂ A₂)ᴴ
          = productMatrix (fun j' =>
              if j' = j₁ then A₁ * eprFactor * A₁ᴴ else if j' = j₂ then A₂ * eprFactor * A₂ᴴ
              else eprFactor)) ∧
    (∀ (D R s : ℕ) (K : Fin s → Operator D), (∑ k, (K k)ᴴ * (K k) = 1) →
      ∀ ρ : LocalJoint D R, partialTraceFirst (localChannel K ρ) = partialTraceFirst ρ) ∧
    (∀ (D R s : ℕ) (K : Fin s → Operator D), (∑ k, (K k)ᴴ * (K k) = 1) →
      ∀ ρ : LocalJoint D R,
        partialTraceFirst (∑ k, localConj (K k) ρ) = partialTraceFirst ρ) ∧
    outerProduct (eprFactoryUnitary *ᵥ e00) = eprFactor ∧
    (∀ (inv : EPRInventory), inv.gateCost = 2 * inv.slots) := by
  refine ⟨eprFactor_psd, eprFactor_trace, ?_, ?_, ?_, ?_, eprFactoryOutput_eq,
    EPRInventory.gateCost_eq⟩
  · intro m
    exact ⟨eprInventory_psd m, eprInventory_trace m⟩
  · intro m j₁ j₂ hne A₁ A₂
    exact two_slot_consumption m j₁ j₂ hne A₁ A₂
  · intro D R s K hK ρ
    exact localChannel_reference_preserved K hK ρ
  · intro D R s K hK ρ
    exact localInstrument_reference_preserved K hK ρ

/-- Each party's transcript message is its strategy applied to the other party's messages from
earlier rounds. -/
theorem clause7_interactive {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x : X) (j : Fin rounds) :
    (P.transcript x).1 j = P.alice x j (before (P.transcript x).2 j) ∧
    (P.transcript x).2 j = P.bob j (before (P.transcript x).1 j) := by
  refine ⟨P.transcript_alice x j, P.transcript_bob x j⟩

/-- Equal inputs give equal transcripts for a fixed interactive guessing protocol. -/
theorem clause7_deterministic {X : Type} [Fintype X] {rounds : ℕ}
    (P : InteractiveGuess X rounds) (x y : X) (h : x = y) :
    P.transcript x = P.transcript y :=
  P.transcript_deterministic x y h

/-- A binary message tree of depth at most `C` has integer Kraft mass at most `2 ^ C`, and
distinct leaf paths have prefix-incomparable encodings. -/
theorem clause7_kraft :
    (∀ (C : ℕ) (T : BinaryMessageTree), T.depth ≤ C → treeKraftMass T C ≤ 2 ^ C) ∧
    (∀ (T : BinaryMessageTree) (p q : T.Path), p ≠ q →
      ¬ List.IsPrefix (T.encode p) (T.encode q)) :=
  ⟨tree_kraft_le_one, tree_leaves_prefix_free⟩

/-- Repeating a length-`C` message `r` times gives length `r * C`, with the corresponding
exponential expression equal to `((2 : ℝ) ^ C) ^ r`. -/
theorem clause7_redundancy :
    (∀ (r C : ℕ) (w : List Bool), w.length = C → (redundantEncode r w).length = r * C) ∧
    (∀ (r C : ℕ), (2 : ℝ) ^ (C * r) = ((2 : ℝ) ^ C) ^ r) :=
  ⟨redundant_budget, redundant_bound_degrades⟩

/-- The interactive transcripts satisfy both strategy equations and respect equality of inputs.
Binary message trees satisfy the depth-based Kraft bound and prefix freeness, while repeated
encodings satisfy the stated length and exponential identities. -/
theorem clause7_complete :
    (∀ (X : Type) [Fintype X] (rounds : ℕ) (P : InteractiveGuess X rounds) (x : X)
      (j : Fin rounds),
      (P.transcript x).1 j = P.alice x j (before (P.transcript x).2 j) ∧
      (P.transcript x).2 j = P.bob j (before (P.transcript x).1 j)) ∧
    (∀ (X : Type) [Fintype X] (rounds : ℕ) (P : InteractiveGuess X rounds) (x y : X),
      x = y → P.transcript x = P.transcript y) ∧
    (∀ (C : ℕ) (T : BinaryMessageTree), T.depth ≤ C → treeKraftMass T C ≤ 2 ^ C) ∧
    (∀ (T : BinaryMessageTree) (p q : T.Path), p ≠ q →
      ¬ List.IsPrefix (T.encode p) (T.encode q)) ∧
    (∀ (r C : ℕ) (w : List Bool), w.length = C → (redundantEncode r w).length = r * C) ∧
    (∀ (r C : ℕ), (2 : ℝ) ^ (C * r) = ((2 : ℝ) ^ C) ^ r) := by
  refine ⟨?_, ?_, tree_kraft_le_one, tree_leaves_prefix_free, redundant_budget,
    redundant_bound_degrades⟩
  · intro X _ rounds P x j
    exact ⟨P.transcript_alice x j, P.transcript_bob x j⟩
  · intro X _ rounds P x y h
    exact P.transcript_deterministic x y h

/-- The interactive transcripts satisfy both strategy equations, and depth-bounded binary
message trees satisfy the integer Kraft bound. -/
theorem clause7_residual :
    (∀ (X : Type) [Fintype X] (rounds : ℕ) (P : InteractiveGuess X rounds) (x : X)
      (j : Fin rounds),
      (P.transcript x).1 j = P.alice x j (before (P.transcript x).2 j) ∧
      (P.transcript x).2 j = P.bob j (before (P.transcript x).1 j)) ∧
    (∀ (C : ℕ) (T : BinaryMessageTree), T.depth ≤ C → treeKraftMass T C ≤ 2 ^ C) := by
  refine ⟨?_, tree_kraft_le_one⟩
  intro X _ rounds P x j
  exact ⟨P.transcript_alice x j, P.transcript_bob x j⟩

end LocalResourceNetwork
