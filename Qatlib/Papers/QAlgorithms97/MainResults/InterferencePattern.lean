/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Controlled addition and phase interference

Controlled gates transfer eigenphases from a common target eigenstate to the control amplitudes.
This module realizes that mechanism using cyclic addition and a normalized Fourier kernel state,
giving the exact prescribed phase pattern for `conditionalAddWord` in the setting of
[CleveEtAl1998].

## Main statements

* `conditional_pattern`: phase transfer for a family with a common eigenstate.
* `conditional_add_kicks_back`: the Fourier kernel is an eigenstate of cyclic addition.
* `conditionalAddWord_run`: the exact controlled-addition output state.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.QAlgorithms97.MainResults.InterferencePattern

/-- The block-diagonal gate applying `U x` to the target register when the control has value
`x`. -/
def conditionalGate {I J : Type*} [DecidableEq I] (U : I → Matrix J J ℂ) :
    Matrix (I × J) (I × J) ℂ :=
  fun p q => if p.1 = q.1 then U p.1 p.2 q.2 else 0

/-- If the target state is a common eigenstate of the controlled gates with phases determined by
`φ`, the controlled gate multiplies each control amplitude by its corresponding eigenphase
[CleveEtAl1998]. -/
theorem conditional_pattern {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : I → Matrix J J ℂ)
    (φ : I → ℝ) (Ψ : QState J)
    (hΨ : ∀ x : I,
      ApplyGate (U x) Ψ =
        fun y => Complex.exp (2 * Real.pi * φ x * Complex.I) * Ψ y)
    (α : QState I) :
    ApplyGate (conditionalGate U) (fun p : I × J => α p.1 * Ψ p.2) =
      fun p => (Complex.exp (2 * Real.pi * φ p.1 * Complex.I) * α p.1) * Ψ p.2 := by
  funext p
  rcases p with ⟨x, y⟩
  have h := congrFun (hΨ x) y
  change (∑ z, U x y z * Ψ z) = _ at h
  change (∑ q : I × J,
    (if x = q.1 then U x y q.2 else 0) * (α q.1 * Ψ q.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  simp_rw [show ∀ z, U x y z * (α x * Ψ z) = α x * (U x y z * Ψ z) by
    intro z; ring]
  rw [← Finset.mul_sum, h]
  ring

/-- A controlled family of unitary target gates defines a unitary gate on the product register. -/
theorem conditionalGate_unitary {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : I → Matrix J J ℂ)
    (hU : ∀ x, U x ∈ Matrix.unitaryGroup J ℂ) :
    conditionalGate U ∈ Matrix.unitaryGroup (I × J) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext ⟨x,y⟩ ⟨z,w⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, conditionalGate]
  rw [Fintype.sum_prod_type]
  by_cases h : x = z
  · subst z
    have hu := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp (hU x)) y) w
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at hu
    simpa [Matrix.one_apply, apply_ite, eq_comm] using! hu
  · simp [apply_ite, h, eq_comm]

/-- Addition of a fixed offset modulo `2 ^ m` on the finite cyclic register. -/
def cyclicAdd {m : ℕ} (a : Fin (2 ^ m)) (y : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨(y.val + a.val) % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩

/-- The permutation matrix implementing addition of `a` modulo `2 ^ m`. -/
def cyclicAddGate {m : ℕ} (a : Fin (2 ^ m)) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun y z => if y = cyclicAdd a z then 1 else 0

/-- The explicit modular definition of `cyclicAdd` equals addition in `Fin (2 ^ m)`. -/
theorem cyclicAdd_eq_add {m : ℕ} (a y : Fin (2 ^ m)) : cyclicAdd a y = y + a := rfl

/-- Applying cyclic addition by `a` evaluates the input amplitude at the output label minus `a`. -/
theorem cyclicAddGate_apply {m : ℕ} (a : Fin (2 ^ m)) (ψ : QState (Fin (2 ^ m)))
    (y : Fin (2 ^ m)) : ApplyGate (cyclicAddGate a) ψ y = ψ (y - a) := by
  change (∑ z, (if y = cyclicAdd a z then (1 : ℂ) else 0) * ψ z) = _
  simp only [cyclicAdd_eq_add, show ∀ z, y = z + a ↔ z = y - a by
    intro z; simp [eq_sub_iff_add_eq, eq_comm], ite_mul, one_mul, zero_mul]
  simp

/-- The cyclic-addition permutation matrix is unitary. -/
theorem cyclicAddGate_unitary {m : ℕ} (a : Fin (2 ^ m)) :
    cyclicAddGate a ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
  have heq : cyclicAddGate a = Equiv.Perm.permMatrix ℂ (Equiv.addRight a).symm := by
    ext y z
    simp [cyclicAddGate, cyclicAdd_eq_add, Equiv.toPEquiv_apply,
      ← sub_eq_add_neg, eq_sub_iff_add_eq, eq_comm]
  have hp (σ : Equiv.Perm (Fin (2 ^ m))) :
      Equiv.Perm.permMatrix ℂ σ ∈ Matrix.unitaryGroup (Fin (2 ^ m)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  rw [heq]
  exact hp _

/-- The finite cyclic equivalence sends a label to the residue class of its natural-number
value. -/
theorem cyclic_label {N : ℕ} [NeZero N] (y : Fin N) :
    ZMod.finEquiv N y = (y.val : ZMod N) := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change y.val = y.val % (n + 1)
    exact (Nat.mod_eq_of_lt y.isLt).symm

/-- The standard additive character on a register of size `2 ^ m` is the complex exponential
with angle `2πy / 2 ^ m`. -/
theorem cyclic_character_exp (m : ℕ) (y : Fin (2 ^ m)) :
    ZMod.stdAddChar (ZMod.finEquiv (2 ^ m) y) =
      Complex.exp (2 * Real.pi * (y.val : ℝ) / (2 : ℝ) ^ m * Complex.I) := by
  rw [cyclic_label]
  have h := ZMod.stdAddChar_coe (N := 2 ^ m) (y.val : ℤ)
  simp only [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [h]
  congr 1
  push_cast
  ring

/-- The normalized negative-frequency Fourier kernel state on a cyclic register of size `2 ^ m`. -/
def fourierKernelState (m : ℕ) : QState (Fin (2 ^ m)) :=
  fun y => ((Real.sqrt ((2 : ℝ) ^ m) : ℝ) : ℂ)⁻¹ *
    Complex.exp (-(2 * Real.pi * (y.val : ℝ) / (2 : ℝ) ^ m) * Complex.I)

/-- The Fourier kernel amplitude is the inverse square root of the register size times the
standard additive character of the negative label. -/
theorem fourierKernelState_character (m : ℕ) (y : Fin (2 ^ m)) :
    fourierKernelState m y = (Real.sqrt ((2 : ℝ) ^ m) : ℂ)⁻¹ *
      ZMod.stdAddChar (-ZMod.finEquiv (2 ^ m) y) := by
  rw [AddChar.map_neg_eq_inv, cyclic_character_exp, ← Complex.exp_neg]
  unfold fourierKernelState
  congr 2
  ring

/-- Cyclic addition by `a` multiplies the Fourier kernel state by the phase `exp (2πi a / 2 ^
m)`. -/
theorem conditional_add_kicks_back (m : ℕ) (a : Fin (2 ^ m)) :
    ApplyGate (cyclicAddGate a) (fourierKernelState m) =
      fun y => Complex.exp (2 * Real.pi * (a.val : ℝ) / (2 : ℝ) ^ m * Complex.I) *
        fourierKernelState m y := by
  funext y
  rw [cyclicAddGate_apply, fourierKernelState_character, fourierKernelState_character,
    ← cyclic_character_exp]
  simp only [map_sub]
  rw [neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

/-- The Fourier kernel state has total Born weight one. -/
theorem normalized_fourierKernelState (m : ℕ) : Normalized (fourierKernelState m) := by
  have hn := Qatlib.Concepts.QuditTeleport.TeleportCore.normalized_charState
    (-1 : ZMod (2 ^ m))
  unfold Normalized at hn ⊢
  calc
    _ = ∑ y : ZMod (2 ^ m),
        ‖Qatlib.Concepts.QuditTeleport.TeleportCore.charState (-1) y‖ ^ 2 := by
      apply Fintype.sum_equiv (ZMod.finEquiv (2 ^ m)).toEquiv
      intro y
      rw [fourierKernelState_character,
        Qatlib.Concepts.QuditTeleport.TeleportCore.charState_apply, neg_one_mul]
      simp only [Nat.cast_pow, Nat.cast_ofNat, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
    _ = 1 := hn

/-- The single-gate circuit applying cyclic addition by the control-dependent offset `a x`. -/
def conditionalAddWord {I : Type*} [DecidableEq I] (m : ℕ) (a : I → Fin (2 ^ m)) :
    Circuit (I × Fin (2 ^ m)) :=
  [Step.gate (conditionalGate (fun x => cyclicAddGate (a x)))]

/-- The controlled cyclic-addition word is a unitary circuit. -/
theorem conditionalAddWord_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : I → Fin (2 ^ m)) : IsUnitaryCircuit (conditionalAddWord m a) := by
  simp only [conditionalAddWord, isUnitaryCircuit_gate, isUnitaryCircuit_nil, and_true]
  exact conditionalGate_unitary _ (fun _ => cyclicAddGate_unitary _)

/-- Running the controlled-addition word with the Fourier kernel target multiplies each control
amplitude by its offset-dependent phase and leaves the target state unchanged
[CleveEtAl1998]. -/
theorem conditionalAddWord_run {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : I → Fin (2 ^ m)) (α : QState I)
    (oracle : Matrix (I × Fin (2 ^ m)) (I × Fin (2 ^ m)) ℂ) :
    Run oracle (conditionalAddWord m a) (TensorState α (fourierKernelState m)) =
      TensorState (fun x =>
        Complex.exp (2 * Real.pi * ((a x).val : ℝ) / (2 : ℝ) ^ m * Complex.I) * α x)
        (fourierKernelState m) := by
  change ApplyGate (conditionalGate (fun x => cyclicAddGate (a x)))
    (TensorState α (fourierKernelState m)) = _
  simpa only [TensorState, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
    mul_div_assoc] using! conditional_pattern _ (fun x => ((a x).val : ℝ) / (2 : ℝ) ^ m)
    (fourierKernelState m) (by
      intro x
      convert! conditional_add_kicks_back m (a x) using 1
      funext y
      congr 1
      congr 1
      push_cast
      ring) α

/-- A normalized control state tensored with the Fourier kernel remains normalized after the
controlled-addition word. -/
theorem conditionalAddWord_normalized {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) (a : I → Fin (2 ^ m)) {α : QState I} (hα : Normalized α)
    (oracle : Matrix (I × Fin (2 ^ m)) (I × Fin (2 ^ m)) ℂ) :
    Normalized (Run oracle (conditionalAddWord m a) (TensorState α (fourierKernelState m))) := by
  change Normalized (ApplyGate (conditionalGate (fun x => cyclicAddGate (a x))) _)
  exact normalized_applyGate (conditionalGate_unitary _ (fun _ => cyclicAddGate_unitary _))
    (normalized_tensorState hα (normalized_fourierKernelState m))

end Qatlib.Papers.QAlgorithms97.MainResults.InterferencePattern
