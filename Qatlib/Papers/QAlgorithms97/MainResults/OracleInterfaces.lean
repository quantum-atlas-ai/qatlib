/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAlgorithms97.MainResults.OracleInterfaces
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

theorem bitFlip_involutive {I : Type} (f : I → Bool) : Function.Involutive (BitFlip f) := by
  rintro ⟨x,b⟩
  cases h : f x <;> cases b <;> simp [BitFlip, h]

theorem bitOracle_unitary {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) :
    BitOracleOn f ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
  permMatrix_unitary (bitFlip_involutive f)

theorem phaseOracle_unitary {I : Type} [Fintype I] [DecidableEq I] (f : I → Bool) :
    PhaseOracle f ∈ Matrix.unitaryGroup I ℂ := by
  apply diagonal_mem_unitaryGroup
  intro x
  cases f x <;> simp

theorem phaseOracle_apply {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bool) (ψ : QState I) (x : I) :
    ApplyGate (PhaseOracle f) ψ x = (if f x then (-1 : ℂ) else 1) * ψ x :=
  congrFun (applyGate_diagonal _ ψ) x

theorem bitOracle_minus {I : Type} [Fintype I] [DecidableEq I]
    (f : I → Bool) (ψ : QState I) :
    ApplyGate (BitOracleOn f) (TensorState ψ Minus) =
      TensorState (ApplyGate (PhaseOracle f) ψ) Minus := by
  funext p
  rcases p with ⟨x,b⟩
  rw [show BitOracleOn f = permMatrix (BitFlip f) from rfl,
    applyGate_permMatrix (bitFlip_involutive f)]
  simp only [TensorState, BitFlip, Minus, phaseOracle_apply]
  cases f x <;> cases b <;> simp [Hadamard]

def outputXor {I : Type} {m : ℕ} (f : I → Reg m) (p : I × Reg m) : I × Reg m :=
  (p.1, fun j => p.2 j ^^ f p.1 j)

theorem outputXor_involutive {I : Type} {m : ℕ} (f : I → Reg m) :
    Function.Involutive (outputXor f) := by
  rintro ⟨x,y⟩
  change (x, fun j => (y j ^^ f x j) ^^ f x j) = (x,y)
  simp

def outputOracle {I : Type} [DecidableEq I] {m : ℕ} (f : I → Reg m) :
    Matrix (I × Reg m) (I × Reg m) ℂ := permMatrix (outputXor f)

theorem outputOracle_unitary {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (f : I → Reg m) :
    outputOracle f ∈ Matrix.unitaryGroup (I × Reg m) ℂ :=
  permMatrix_unitary (outputXor_involutive f)

def binaryCharacter {m : ℕ} (c y : Reg m) : ℂ :=
  ∏ j, if c j && y j then (-1 : ℂ) else 1

def outputAnswer {m : ℕ} (c : Reg m) : QState (Reg m) :=
  ApplyGate (HadamardN m) (Ket c)

theorem outputAnswer_apply {m : ℕ} (c y : Reg m) :
    outputAnswer c y = ((Real.sqrt 2 : ℂ)⁻¹) ^ m * binaryCharacter c y := by
  rw [outputAnswer, applyGate_eq_mulVec_ket, hadamardN_apply]
  simp only [binaryCharacter, Bool.and_comm]

theorem outputAnswer_normalized {m : ℕ} (c : Reg m) : Normalized (outputAnswer c) :=
  normalized_applyGate (hadamardN_unitary m) (normalized_ket c)

theorem outputAnswer_xor {m : ℕ} (c y v : Reg m) :
    outputAnswer c (fun j => y j ^^ v j) = binaryCharacter c v * outputAnswer c y := by
  simp only [outputAnswer_apply, binaryCharacter]
  have hp : ∀ j, (if c j && (y j ^^ v j) then (-1 : ℂ) else 1) =
      (if c j && v j then (-1 : ℂ) else 1) * (if c j && y j then (-1 : ℂ) else 1) := by
    intro j
    cases c j <;> cases y j <;> cases v j <;> norm_num
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  ring

theorem outputOracle_kickback {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (f : I → Reg m) (c : Reg m) (ψ : QState I) :
    Run (outputOracle f) [Step.query] (TensorState ψ (outputAnswer c)) =
      TensorState (fun x => binaryCharacter c (f x) * ψ x) (outputAnswer c) := by
  funext p
  rcases p with ⟨x,y⟩
  change ApplyGate (permMatrix (outputXor f)) _ (x,y) = _
  rw [applyGate_permMatrix (outputXor_involutive f)]
  simp only [TensorState, outputXor, outputAnswer_xor]
  ring

end Qatlib.Papers.QAlgorithms97.MainResults.OracleInterfaces
