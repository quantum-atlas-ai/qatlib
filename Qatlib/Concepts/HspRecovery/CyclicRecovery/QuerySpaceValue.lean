/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardCoordinates
import Mathlib.Tactic.NormNum
set_option warningAsError false
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.CyclicRecovery

open Qatlib Matrix
open scoped Classical
set_option linter.unusedSectionVars false

theorem relabel_permMatrix_of_intertwining
    {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (s : A → A) (t : B → B)
    (hst : ∀ a, e (s a) = t (e a)) :
    relabelGate e (permMatrix s) = permMatrix t := by
  ext i j
  change (if e.symm i = s (e.symm j) then (1 : ℂ) else 0) =
    (if i = t j then (1 : ℂ) else 0)
  have heq : e.symm i = s (e.symm j) ↔ i = t j := by
    constructor
    · intro hij
      calc i = e (e.symm i) := (e.apply_symm_apply i).symm
        _ = e (s (e.symm j)) := congrArg e hij
        _ = t (e (e.symm j)) := hst (e.symm j)
        _ = t j := congrArg t (e.apply_symm_apply j)
    · intro hij
      apply e.injective
      calc e (e.symm i) = i := e.apply_symm_apply i
        _ = t j := hij
        _ = t (e (e.symm j)) := congrArg t (e.apply_symm_apply j).symm
        _ = e (s (e.symm j)) := (hst (e.symm j)).symm
  simp only [heq]

theorem relabel_tensor_right
    {A B W : Type} (e : A ≃ B) (M : Matrix A A ℂ) (N : Matrix W W ℂ) :
    relabelGate (e.prodCongr (Equiv.refl W)) (TensorGate M N) =
      TensorGate (relabelGate e M) N := by
  ext p q
  rcases p with ⟨i, w⟩
  rcases q with ⟨j, v⟩
  rfl

theorem boolValue_xor (a b : Bool) :
    boolZModEquiv (a ^^ b) = boolZModEquiv a + boolZModEquiv b := by
  have h11 : (1 : ZMod 2) + 1 = 0 :=
    eq_neg_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two (1 : ZMod 2)).symm
  cases a <;> cases b <;> simp [Bool.xor, h11]

def bitValueEquiv (I : Type) : (I × Bool) ≃ (I × ZMod 2) :=
  (Equiv.refl I).prodCongr boolZModEquiv

def workspaceValueEquiv (I W : Type) : ((I × Bool) × W) ≃ ((I × ZMod 2) × W) :=
  (bitValueEquiv I).prodCongr (Equiv.refl W)

def boolValue {I : Type} (f : I → Bool) (x : I) : ZMod 2 := boolZModEquiv (f x)

theorem bitValueEquiv_intertwining {I : Type} (f : I → Bool) (a : I × Bool) :
    bitValueEquiv I (BitFlip f a) = addOracleEquiv (boolValue f) (bitValueEquiv I a) := by
  rcases a with ⟨x, b⟩
  apply Prod.ext
  · rfl
  · change boolZModEquiv (b ^^ f x) = boolZModEquiv b + boolZModEquiv (f x)
    exact boolValue_xor b (f x)

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

theorem bit_value_matrix (f : I → Bool) :
    relabelGate (bitValueEquiv I) (BitOracleOn f) = AddOracle (boolValue f) := by
  rw [BitOracleOn, addOracle_eq_permMatrix]
  exact relabel_permMatrix_of_intertwining (bitValueEquiv I) (BitFlip f)
    (addOracleEquiv (boolValue f)) (bitValueEquiv_intertwining f)

theorem workspace_bit_value_matrix (f : I → Bool) :
    relabelGate (workspaceValueEquiv I W) (workspaceBitOracle (W := W) f) =
      TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ) := by
  change relabelGate ((bitValueEquiv I).prodCongr (Equiv.refl W))
      (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) = _
  rw [relabel_tensor_right, bit_value_matrix]

theorem workspace_value_bit_matrix (f : I → Bool) :
    relabelGate (workspaceValueEquiv I W).symm
      (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) =
      workspaceBitOracle (W := W) f := by
  rw [← workspace_bit_value_matrix (W := W) f]
  exact relabelGate_symm (workspaceValueEquiv I W) (workspaceBitOracle (W := W) f)

theorem coherent_forward (f : I → Bool) (ψ : QState ((I × Bool) × W)) :
    ApplyGate (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ))
      (relabelState (workspaceValueEquiv I W) ψ) =
    relabelState (workspaceValueEquiv I W) (ApplyGate (workspaceBitOracle f) ψ) := by
  have h := applyGate_relabelGate (workspaceValueEquiv I W) (workspaceBitOracle f) ψ
  rw [workspace_bit_value_matrix] at h
  exact h

theorem coherent_backward (f : I → Bool) (φ : QState ((I × ZMod 2) × W)) :
    ApplyGate (workspaceBitOracle f) (relabelState (workspaceValueEquiv I W).symm φ) =
    relabelState (workspaceValueEquiv I W).symm
      (ApplyGate (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) φ) := by
  have h := applyGate_relabelGate (workspaceValueEquiv I W).symm
    (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) φ
  rw [workspace_value_bit_matrix] at h
  exact h

theorem whole_circuit_forward (f : I → Bool)
    (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
    (S : Finset ((I × Bool) × W)) :
    Run (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ))
      (relabelCircuit (workspaceValueEquiv I W) C)
      (relabelState (workspaceValueEquiv I W) ψ) =
        relabelState (workspaceValueEquiv I W) (Run (workspaceBitOracle f) C ψ) ∧
    MeasureProb (Run (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ))
      (relabelCircuit (workspaceValueEquiv I W) C)
      (relabelState (workspaceValueEquiv I W) ψ))
      (S.map (workspaceValueEquiv I W).toEmbedding) =
        MeasureProb (Run (workspaceBitOracle f) C ψ) S := by
  have h := run_relabelCircuit_readout (workspaceValueEquiv I W)
    (workspaceBitOracle f) C ψ S
  rw [workspace_bit_value_matrix] at h
  exact h

theorem whole_circuit_backward (f : I → Bool)
    (C : Circuit ((I × ZMod 2) × W)) (φ : QState ((I × ZMod 2) × W))
    (S : Finset ((I × ZMod 2) × W)) :
    Run (workspaceBitOracle f) (relabelCircuit (workspaceValueEquiv I W).symm C)
      (relabelState (workspaceValueEquiv I W).symm φ) =
    relabelState (workspaceValueEquiv I W).symm
      (Run (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) C φ) ∧
    MeasureProb (Run (workspaceBitOracle f)
      (relabelCircuit (workspaceValueEquiv I W).symm C)
      (relabelState (workspaceValueEquiv I W).symm φ))
      (S.map (workspaceValueEquiv I W).symm.toEmbedding) =
    MeasureProb (Run (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) C φ) S := by
  have h := run_relabelCircuit_readout (workspaceValueEquiv I W).symm
    (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) C φ S
  rw [workspace_value_bit_matrix] at h
  exact h

theorem forward_resources (C : Circuit ((I × Bool) × W)) :
    (IsUnitaryCircuit (relabelCircuit (workspaceValueEquiv I W) C) ↔ IsUnitaryCircuit C) ∧
    QueryCount (relabelCircuit (workspaceValueEquiv I W) C) = QueryCount C ∧
    GateCount (relabelCircuit (workspaceValueEquiv I W) C) = GateCount C ∧
    Size (relabelCircuit (workspaceValueEquiv I W) C) = Size C :=
  relabelCircuit_legality_resources (workspaceValueEquiv I W) C

theorem backward_resources (C : Circuit ((I × ZMod 2) × W)) :
    (IsUnitaryCircuit (relabelCircuit (workspaceValueEquiv I W).symm C) ↔ IsUnitaryCircuit C) ∧
    QueryCount (relabelCircuit (workspaceValueEquiv I W).symm C) = QueryCount C ∧
    GateCount (relabelCircuit (workspaceValueEquiv I W).symm C) = GateCount C ∧
    Size (relabelCircuit (workspaceValueEquiv I W).symm C) = Size C :=
  relabelCircuit_legality_resources (workspaceValueEquiv I W).symm C

theorem roundtrip (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    relabelCircuit (workspaceValueEquiv I W).symm
      (relabelCircuit (workspaceValueEquiv I W) C) = C ∧
    relabelState (workspaceValueEquiv I W).symm
      (relabelState (workspaceValueEquiv I W) ψ) = ψ :=
  ⟨(relabelCircuit_equivalence_laws (workspaceValueEquiv I W)
      (workspaceValueEquiv I W).symm C).2.2,
    relabelState_relabelState (workspaceValueEquiv I W) ψ⟩

end Qatlib.Concepts.HspRecovery.CyclicRecovery
