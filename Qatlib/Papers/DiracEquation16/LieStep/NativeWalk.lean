/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryShift
import Qatlib.Concepts.TensorRegisters.RegisterModel.RootChars
import Qatlib.Papers.DiracEquation16.SpinGates.NativeSpin
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.DiracEquation16.LieStep
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.MatrixAlgebra
open Qatlib.Papers.DiracEquation16.SpinGates Qatlib.Papers.DiracEquation16.SpinGates.FourD

def side (s : Fin 4) : Bool := decide (2 ≤ s.val)

def axis {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (a : Fin 3) (l : G) : Matrix (Fin 4 × G) (Fin 4 × G) ℂ :=
  BinaryShift.spinLift (SpinGates.S a) * BinaryShift.stream side l * BinaryShift.spinLift (SpinGates.S a)

theorem axis_unitary {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G] (a : Fin 3) (l : G) :
    axis a l ∈ Matrix.unitaryGroup (Fin 4 × G) ℂ := by
  exact (Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
      (BinaryShift.spinLift_unitary _ (SpinGates.S_unitary a)) (BinaryShift.stream_unitary side l))
    (BinaryShift.spinLift_unitary _ (SpinGates.S_unitary a))

theorem axis_mode {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (a : Fin 3) (l : G) (χ : AddChar G ℂ) (v : Fin 4 → ℂ) :
    axis a l *ᵥ BinaryShift.mode χ v =
      BinaryShift.mode χ ((SpinGates.S a * BinaryShift.bloch side χ l * SpinGates.S a) *ᵥ v) := by
  unfold axis
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    BinaryShift.spinLift_mode, BinaryShift.stream_mode, BinaryShift.spinLift_mode]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem beta_rotation_diagonal (θ : ℝ) :
    CliffordWalk.rotation beta4 θ = Matrix.diagonal (fun s : Fin 4 =>
      if side s then Complex.exp (Complex.I * (θ : ℂ)) else Complex.exp (-Complex.I * (θ : ℂ))) := by
  have hp (x : ℝ) : Complex.exp (Complex.I * (x : ℂ)) =
      (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_ofReal_mul_I]
  have hn : Complex.exp (-(Complex.I * (θ : ℂ))) =
      (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show -(Complex.I * (θ : ℂ)) = Complex.I * ((-θ : ℝ) : ℂ) by push_cast; ring, hp]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  rw [CliffordWalk.rotation_euler_complex beta4 beta4_sq θ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [side, beta4, Matrix.smul_apply, hp, hn] <;> ring

theorem S_rotation_conj (a : Fin 3) (θ : ℝ) :
    SpinGates.S a * CliffordWalk.rotation beta4 θ * SpinGates.S a =
      CliffordWalk.rotation (SpinGates.alpha a) θ := by
  rw [CliffordWalk.rotation_euler_complex beta4 beta4_sq θ,
    CliffordWalk.rotation_euler_complex (SpinGates.alpha a) (SpinGates.alpha_sq a) θ]
  simp only [mul_add, Matrix.mul_smul, add_mul, Matrix.smul_mul, Matrix.mul_one,
    SpinGates.S_sq, SpinGates.S_beta_conj]

theorem vector_generator_hermitian (Ax Ay Az : ℝ) :
    (Ax • alphaX4 + Ay • alphaY4 + Az • alphaZ4)ᴴ = Ax • alphaX4 + Ay • alphaY4 + Az • alphaZ4 := by
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial,
    alphaX4_hermitian, alphaY4_hermitian, alphaZ4_hermitian]

def mass {G : Type*} [DecidableEq G] (m c dt : ℝ) : Matrix (Fin 4 × G) (Fin 4 × G) ℂ :=
  BinaryShift.spinLift (CliffordWalk.rotation beta4 (m * c ^ 2 * dt))

def vectorGate {G : Type*} [DecidableEq G] (e dt Ax Ay Az : ℝ) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℂ :=
  BinaryShift.spinLift (CliffordWalk.rotation (Ax • alphaX4 + Ay • alphaY4 + Az • alphaZ4) (-e * dt))

def scalarGate {G : Type*} [Fintype G] [DecidableEq G] (V : G → ℝ) (e dt : ℝ) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℂ :=
  CliffordWalk.rotation (Matrix.diagonal (fun x : Fin 4 × G => (V x.2 : ℂ))) (e * dt)

theorem mass_unitary {G : Type*} [Fintype G] [DecidableEq G] (m c dt : ℝ) :
    mass (G := G) m c dt ∈ Matrix.unitaryGroup (Fin 4 × G) ℂ :=
  BinaryShift.spinLift_unitary _ (CliffordWalk.rotation_unitary beta4 beta4_hermitian _)

theorem vectorGate_unitary {G : Type*} [Fintype G] [DecidableEq G] (e dt Ax Ay Az : ℝ) :
    vectorGate (G := G) e dt Ax Ay Az ∈ Matrix.unitaryGroup (Fin 4 × G) ℂ :=
  BinaryShift.spinLift_unitary _ (CliffordWalk.rotation_unitary _ (vector_generator_hermitian Ax Ay Az) _)

theorem scalarGate_unitary {G : Type*} [Fintype G] [DecidableEq G] (V : G → ℝ) (e dt : ℝ) :
    scalarGate V e dt ∈ Matrix.unitaryGroup (Fin 4 × G) ℂ := by
  apply CliffordWalk.rotation_unitary
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

def finiteStep {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (lx ly lz : G) (V : G → ℝ) (m c e dt Ax Ay Az : ℝ) :
    Matrix (Fin 4 × G) (Fin 4 × G) ℂ :=
  vectorGate e dt Ax Ay Az * scalarGate V e dt * mass m c dt * axis 2 lz * axis 1 ly * axis 0 lx

theorem finiteStep_unitary {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (lx ly lz : G) (V : G → ℝ) (m c e dt Ax Ay Az : ℝ) :
    finiteStep lx ly lz V m c e dt Ax Ay Az ∈ Matrix.unitaryGroup (Fin 4 × G) ℂ := by
  exact (Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
        ((Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
          ((Matrix.unitaryGroup (Fin 4 × G) ℂ).mul_mem
            (vectorGate_unitary e dt Ax Ay Az) (scalarGate_unitary V e dt)) (mass_unitary m c dt))
        (axis_unitary 2 lz)) (axis_unitary 1 ly)) (axis_unitary 0 lx)

theorem binary_bloch_phase (n : ℕ) (k : ℤ) :
    BinaryShift.bloch side (RootChars.plane (2 ^ n) k) (1 : ZMod (2 ^ n)) =
      CliffordWalk.rotation beta4 (RootChars.angle (2 ^ n) k) := by
  rw [beta_rotation_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [BinaryShift.bloch, side, RootChars.plane_one, RootChars.plane_neg_one]

theorem axis_binary_mode (n : ℕ) (a : Fin 3) (k : ℤ) (v : Fin 4 → ℂ) :
    axis a (1 : ZMod (2 ^ n)) *ᵥ BinaryShift.mode (RootChars.plane (2 ^ n) k) v =
      BinaryShift.mode (RootChars.plane (2 ^ n) k)
        (CliffordWalk.rotation (SpinGates.alpha a) (RootChars.angle (2 ^ n) k) *ᵥ v) := by
  rw [axis_mode, binary_bloch_phase, S_rotation_conj]
