/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl

/-!
# A seven-gate relative Toffoli word

`sourceRelativeToffoliSteps` implements a relative Toffoli using four single-qubit rotations and
three CNOTs. Its target-fibre and basis-state formulas make the additional conditional sign
explicit, supplying the relative-phase building block used in the multi-control constructions of
[BarencoEtAl1995].

## Main statements

* `sourceRelativeToffoliSteps_fibre`: Conditional `PauliX`, `PauliZ`, or identity action on the
  target.
* `sourceRelativeToffoliSteps_ket`: Basis action with the explicit sign.
* `sourceRelativeToffoliSteps_counts`: Seven gates in total, including four single-qubit gates.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl
open Matrix
open scoped Classical BigOperators

/-- Multiplying `PauliX` on both sides by the same qubit Euler rotation leaves `PauliX`
unchanged. -/
private theorem rotation_x_rotation (θ : ℝ) :
    qubitEulerRotation θ * PauliX * qubitEulerRotation θ = PauliX := by
  calc
    _ = qubitEulerRotation θ * (PauliX * qubitEulerRotation θ * PauliX) * PauliX := by
      simp only [Matrix.mul_assoc, pauliX_mul_self, Matrix.mul_one]
    _ = PauliX := by
      rw [pauliX_mul_qubitEulerRotation, qubitEulerRotation_mul,
        add_neg_cancel, qubitEulerRotation_zero, Matrix.one_mul]

/-- Evaluates the alternating rotation and Boolean-controlled `PauliX` product as `PauliX` when
both bits are true, `qubitEulerRotation (-4 * θ) * PauliX` when only the first is true, and
the identity otherwise. -/
private theorem relative_factor (θ : ℝ) (a b : Bool) :
    (qubitEulerRotation θ)ᴴ * (if b then PauliX else 1) *
      (qubitEulerRotation θ)ᴴ * (if a then PauliX else 1) *
      qubitEulerRotation θ * (if b then PauliX else 1) * qubitEulerRotation θ =
    if a && b then PauliX else if a then qubitEulerRotation (-4*θ)*PauliX else 1 := by
  rw [qubitEulerRotation_conjTranspose]
  cases a <;> cases b <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true,
    if_true, if_false, Matrix.mul_one, Matrix.one_mul]
  · rw [qubitEulerRotation_mul, qubitEulerRotation_mul, qubitEulerRotation_mul,
      show -θ+-θ+θ+θ=0 from by ring, qubitEulerRotation_zero]
  · rw [rotation_x_rotation, pauliX_mul_qubitEulerRotation,
      qubitEulerRotation_mul, neg_add_cancel, qubitEulerRotation_zero]
  · have hXR : PauliX * qubitEulerRotation (θ+θ) =
        qubitEulerRotation (-(θ+θ)) * PauliX := by
      calc
        _ = (PauliX * qubitEulerRotation (θ+θ) * PauliX) * PauliX := by
          rw [Matrix.mul_assoc, pauliX_mul_self, Matrix.mul_one]
        _ = _ := by rw [pauliX_mul_qubitEulerRotation]
    calc
      _ = (qubitEulerRotation (-θ)*qubitEulerRotation (-θ))*PauliX*
          (qubitEulerRotation θ*qubitEulerRotation θ) := by simp only [Matrix.mul_assoc]
      _ = qubitEulerRotation (-4*θ)*PauliX := by
        rw [qubitEulerRotation_mul, qubitEulerRotation_mul, Matrix.mul_assoc, hXR,
          ← Matrix.mul_assoc, qubitEulerRotation_mul]
        congr 2
        ring
  · rw [rotation_x_rotation, pauliX_mul_self, Matrix.one_mul, rotation_x_rotation]

/-- The seven-gate relative Toffoli word formed from four target rotations and three CNOTs. -/
def sourceRelativeToffoliSteps {N : ℕ} (a b t : Fin N) : List (ReflectionGate N) :=
  let A := qubitEulerRotation (-Real.pi/4);
  [.inl (t,A), .inr (b,t), .inl (t,A), .inr (a,t),
    .inl (t,Aᴴ), .inr (b,t), .inl (t,Aᴴ)]

/-- The relative Toffoli gate word equals its syntactic adjoint. -/
theorem sourceRelativeToffoliSteps_adjoint {N : ℕ} (a b t : Fin N) :
    reflectionAdjoint (sourceRelativeToffoliSteps a b t) = sourceRelativeToffoliSteps a b t := by
  simp [sourceRelativeToffoliSteps, reflectionAdjoint, reflectionGateAdjoint]

/-- The relative Toffoli word is legal when both controls differ from its target. -/
theorem sourceRelativeToffoliSteps_legal {N : ℕ} (a b t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) : reflectionLegal (sourceRelativeToffoliSteps a b t) := by
  intro g hg
  simp only [sourceRelativeToffoliSteps, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact qubitEulerRotation_unitary _
  · exact hbt
  · exact qubitEulerRotation_unitary _
  · exact hat
  · rw [qubitEulerRotation_conjTranspose]; exact qubitEulerRotation_unitary _
  · exact hbt
  · rw [qubitEulerRotation_conjTranspose]; exact qubitEulerRotation_unitary _

/-- On a target fibre, the relative Toffoli word applies `PauliX` when both controls are true,
`PauliZ` when only the first is true, and the identity otherwise. -/
theorem sourceRelativeToffoliSteps_fibre {N : ℕ} (a b t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) (x : Reg N) (φ : QState Bool) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourceRelativeToffoliSteps a b t))
      (multiWireState t x φ) = multiWireState t x
        (ApplyGate (if x a && x b then PauliX else if x a then PauliZ else 1) φ) := by
  have hZ : qubitEulerRotation Real.pi * PauliX = PauliZ := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_bool, qubitEulerRotation_apply, PauliX,
        PauliZ, permMatrix, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [sourceRelativeToffoliSteps, reflectionCompile, List.map_cons, List.map_nil,
    run_gate, run_nil, reflectionGateMatrix, multiWireState_single,
    multiWireState_cnot a t hat, multiWireState_cnot b t hbt, ← applyGate_mul]
  simp only [← Matrix.mul_assoc]
  rw [relative_factor, show -4*(-Real.pi/4)=Real.pi from by ring, hZ]

/-- A target fibre containing the basis vector `Ket b` is the register basis vector with the
target bit set to `b`. -/
private theorem fibre_basis {N : ℕ} (t : Fin N) (x : Reg N) (b : Bool) :
    multiWireState t x (Qatlib.Foundations.PureStateMath.Ket b) = Qatlib.Foundations.PureStateMath.Ket (Function.update x t b) := by
  cases b <;> simp [multiWireState, Qatlib.Foundations.PureStateMath.Ket]

/-- The action of `PauliZ` on `Ket b` multiplies it by minus one for `b = true` and by one
otherwise. -/
private theorem z_basis (b : Bool) :
    ApplyGate PauliZ (Qatlib.Foundations.PureStateMath.Ket b) = (if b then (-1:ℂ) else 1) • Qatlib.Foundations.PureStateMath.Ket b := by
  ext q
  cases b <;> cases q <;> simp [ApplyGate, Matrix.mulVec, dotProduct, PauliZ,
      Qatlib.Foundations.PureStateMath.Ket]

/-- On a register basis vector, the relative Toffoli word toggles the target by the conjunction
of its controls, with sign minus one exactly when the first control and original target are
true and the second control is false. -/
theorem sourceRelativeToffoliSteps_ket {N : ℕ} (a b t : Fin N)
    (hat : a ≠ t) (hbt : b ≠ t) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (reflectionCompile (sourceRelativeToffoliSteps a b t))
      (Qatlib.Foundations.PureStateMath.Ket x) = (if x a && !x b && x t then (-1:ℂ) else 1) •
      Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ (x a && x b))) := by
  have h :=
      sourceRelativeToffoliSteps_fibre a b t hat hbt x
      (Qatlib.Foundations.PureStateMath.Ket (x t))
  rw [multiWireState_ket] at h
  rw [h]
  cases ha : x a <;> cases hb : x b <;>
    simp only [ha, hb, Bool.false_and, Bool.true_and, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_true, if_false, applyGate_one,
      applyGate_pauliX_ket, z_basis, multiWireState_smul, fibre_basis,
      Bool.xor_false, Bool.xor_true, Function.update_eq_self, one_smul]

/-- The relative Toffoli word has seven gates, of which four are single-qubit gates. -/
theorem sourceRelativeToffoliSteps_counts {N : ℕ} (a b t : Fin N) :
    (sourceRelativeToffoliSteps a b t).length = 7 ∧
    ((sourceRelativeToffoliSteps a b t).filter Sum.isLeft).length = 4 := by
  exact ⟨rfl,rfl⟩

end Qatlib.Concepts.CircuitImpl.MultiControl
