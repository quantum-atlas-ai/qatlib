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

/-!
# Equivalence of bit and additive value queries

Relabels Boolean answer registers as `ZMod 2` answer registers, with optional workspace. The
equivalences `bitValueEquiv` and `workspaceValueEquiv` turn bit-flip queries into additive value
queries.

Proves compatibility at the matrix, state, and whole-circuit levels, including preservation of
measurement probabilities, unitarity, and circuit resource counts. This formalizes the
relationship between standard query encodings described in [NielsenChuang2010].

## Main statements

* `workspace_bit_value_matrix`: identifies the relabeled workspace oracle.
* `whole_circuit_forward`: transports circuit execution and measurement events.
* `forward_resources`: preserves unitarity and resource counts.
* `roundtrip`: recovers circuits and states after forward and inverse relabeling.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- An equivalence intertwining two index maps relabels the permutation matrix of the first map
to that of the second. -/
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

/-- Relabeling the first factor of a tensor gate relabels that factor's matrix and leaves the
second factor's matrix unchanged. -/
theorem relabel_tensor_right
    {A B W : Type} (e : A ≃ B) (M : Matrix A A ℂ) (N : Matrix W W ℂ) :
    relabelGate (e.prodCongr (Equiv.refl W)) (TensorGate M N) =
      TensorGate (relabelGate e M) N := by
  ext p q
  rcases p with ⟨i, w⟩
  rcases q with ⟨j, v⟩
  rfl

/-- The Boolean-to-`ZMod 2` equivalence sends exclusive-or to addition. -/
theorem boolValue_xor (a b : Bool) :
    boolZModEquiv (a ^^ b) = boolZModEquiv a + boolZModEquiv b := by
  have h11 : (1 : ZMod 2) + 1 = 0 :=
    eq_neg_iff_add_eq_zero.mp (ZMod.neg_eq_self_mod_two (1 : ZMod 2)).symm
  cases a <;> cases b <;> simp [Bool.xor, h11]

/-- The equivalence replacing a Boolean answer coordinate by its value in `ZMod 2` while
preserving the query index. -/
def bitValueEquiv (I : Type) : (I × Bool) ≃ (I × ZMod 2) :=
  (Equiv.refl I).prodCongr boolZModEquiv

/-- The bit-to-value register equivalence extended by the identity on a workspace. -/
def workspaceValueEquiv (I W : Type) : ((I × Bool) × W) ≃ ((I × ZMod 2) × W) :=
  (bitValueEquiv I).prodCongr (Equiv.refl W)

/-- The `ZMod 2`-valued encoding of a Boolean oracle function. -/
def boolValue {I : Type} (f : I → Bool) (x : I) : ZMod 2 := boolZModEquiv (f x)

/-- The bit-to-value equivalence intertwines a bit-flip query with the additive oracle
permutation for `boolValue f`. -/
theorem bitValueEquiv_intertwining {I : Type} (f : I → Bool) (a : I × Bool) :
    bitValueEquiv I (BitFlip f a) = addOracleEquiv (boolValue f) (bitValueEquiv I a) := by
  rcases a with ⟨x, b⟩
  apply Prod.ext
  · rfl
  · change boolZModEquiv (b ^^ f x) = boolZModEquiv b + boolZModEquiv (f x)
    exact boolValue_xor b (f x)

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

omit [Fintype I] in

/-- Relabeling the bit oracle matrix by `bitValueEquiv` gives the additive oracle matrix for
`boolValue f`. -/
theorem bit_value_matrix (f : I → Bool) :
    relabelGate (bitValueEquiv I) (BitOracleOn f) = AddOracle (boolValue f) := by
  rw [BitOracleOn, addOracle_eq_permMatrix]
  exact relabel_permMatrix_of_intertwining (bitValueEquiv I) (BitFlip f)
    (addOracleEquiv (boolValue f)) (bitValueEquiv_intertwining f)

omit [Fintype W] in

/-- Relabeling a workspace bit oracle gives the tensor product of the additive value oracle with
the workspace identity. -/
theorem workspace_bit_value_matrix (f : I → Bool) :
    relabelGate (workspaceValueEquiv I W) (workspaceBitOracle (W := W) f) =
      TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ) := by
  change relabelGate ((bitValueEquiv I).prodCongr (Equiv.refl W))
      (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) = _
  rw [relabel_tensor_right, bit_value_matrix]

/-- Relabeling the workspace additive value oracle by the inverse equivalence recovers the
workspace bit oracle. -/
theorem workspace_value_bit_matrix (f : I → Bool) :
    relabelGate (workspaceValueEquiv I W).symm
      (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) =
      workspaceBitOracle (W := W) f := by
  rw [← workspace_bit_value_matrix (W := W) f]
  exact relabelGate_symm (workspaceValueEquiv I W) (workspaceBitOracle (W := W) f)

/-- Applying the additive value oracle to a relabeled state equals relabeling the state obtained
by applying the workspace bit oracle. -/
theorem coherent_forward (f : I → Bool) (ψ : QState ((I × Bool) × W)) :
    ApplyGate (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ))
      (relabelState (workspaceValueEquiv I W) ψ) =
    relabelState (workspaceValueEquiv I W) (ApplyGate (workspaceBitOracle f) ψ) := by
  have h := applyGate_relabelGate (workspaceValueEquiv I W) (workspaceBitOracle f) ψ
  rw [workspace_bit_value_matrix] at h
  exact h

/-- Applying the workspace bit oracle to an inversely relabeled state equals inversely
relabeling the additive value oracle output. -/
theorem coherent_backward (f : I → Bool) (φ : QState ((I × ZMod 2) × W)) :
    ApplyGate (workspaceBitOracle f) (relabelState (workspaceValueEquiv I W).symm φ) =
    relabelState (workspaceValueEquiv I W).symm
      (ApplyGate (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) φ) := by
  have h := applyGate_relabelGate (workspaceValueEquiv I W).symm
    (TensorGate (AddOracle (boolValue f)) (1 : Matrix W W ℂ)) φ
  rw [workspace_value_bit_matrix] at h
  exact h

/-- Forward register relabeling intertwines execution of a workspace bit-query circuit with its
additive value-query circuit and preserves probabilities of correspondingly relabeled
events. -/
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

/-- Inverse register relabeling intertwines execution of a workspace additive value-query
circuit with its bit-query circuit and preserves probabilities of correspondingly relabeled
events. -/
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

/-- Forward register relabeling preserves the unitary-circuit property, query count, gate count,
and circuit size. -/
theorem forward_resources (C : Circuit ((I × Bool) × W)) :
    (IsUnitaryCircuit (relabelCircuit (workspaceValueEquiv I W) C) ↔ IsUnitaryCircuit C) ∧
    QueryCount (relabelCircuit (workspaceValueEquiv I W) C) = QueryCount C ∧
    GateCount (relabelCircuit (workspaceValueEquiv I W) C) = GateCount C ∧
    Size (relabelCircuit (workspaceValueEquiv I W) C) = Size C :=
  relabelCircuit_legality_resources (workspaceValueEquiv I W) C

/-- Inverse register relabeling preserves the unitary-circuit property, query count, gate count,
and circuit size. -/
theorem backward_resources (C : Circuit ((I × ZMod 2) × W)) :
    (IsUnitaryCircuit (relabelCircuit (workspaceValueEquiv I W).symm C) ↔ IsUnitaryCircuit C) ∧
    QueryCount (relabelCircuit (workspaceValueEquiv I W).symm C) = QueryCount C ∧
    GateCount (relabelCircuit (workspaceValueEquiv I W).symm C) = GateCount C ∧
    Size (relabelCircuit (workspaceValueEquiv I W).symm C) = Size C :=
  relabelCircuit_legality_resources (workspaceValueEquiv I W).symm C

/-- Forward relabeling followed by inverse relabeling recovers both the original circuit and the
original state. -/
theorem roundtrip (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    relabelCircuit (workspaceValueEquiv I W).symm
      (relabelCircuit (workspaceValueEquiv I W) C) = C ∧
    relabelState (workspaceValueEquiv I W).symm
      (relabelState (workspaceValueEquiv I W) ψ) = ψ :=
  ⟨(relabelCircuit_equivalence_laws (workspaceValueEquiv I W)
      (workspaceValueEquiv I W).symm C).2.2,
    relabelState_relabelState (workspaceValueEquiv I W) ψ⟩

end Qatlib.Concepts.HspRecovery.CyclicRecovery
