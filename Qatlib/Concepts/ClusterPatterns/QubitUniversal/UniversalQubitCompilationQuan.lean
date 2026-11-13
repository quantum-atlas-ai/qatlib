/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.QubitUniversal.UniversalQubitCompilationStat

/-!
# Proof of universal qubit cluster compilation

The module proves `UniversalQubitCompilation` by relating phase and Euler-rotation matrices to
products of `Rz` and Hadamard gates. The resulting four-step cluster word realizes any one-qubit
unitary up to a unit-modulus scalar, as in the measurement-based construction of
[RaussendorfBriegel2000].

## Main statements

* `universalQubitCompilation_answer`: four-step cluster compilation for every one-qubit unitary.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.ClusterPatterns.Preentangled

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ClusterPatterns.QubitUniversal
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder Kronecker

/-- The Z rotation `Rz s` equals `qubitEulerPhase (-s)` multiplied by the scalar `exp(i s / 2)`. -/
private theorem rz_phase (s : ℝ) :
    Rz s = Complex.exp (((s/2 : ℝ) : ℂ)*Complex.I) • qubitEulerPhase (-s) := by
  ext i j
  rcases i <;> rcases j <;>
    simp only [Rz, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      qubitEulerPhase_ff, qubitEulerPhase_ft, qubitEulerPhase_tf, qubitEulerPhase_tt,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, mul_zero]
  · rw [← Complex.exp_add]
    convert! Complex.exp_zero.symm using 2
    push_cast
    ring
  · rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The displayed Z-rotation and Hadamard product equals `qubitEulerRotation θ` multiplied by
`exp(i θ / 2)`. -/
private theorem rotation_middle (θ : ℝ) :
    Rz (-Real.pi/2) * Hadamard * Rz θ * Hadamard * Rz (Real.pi/2) =
      Complex.exp (((θ/2 : ℝ) : ℂ)*Complex.I) • qubitEulerRotation θ := by
  have hp : Complex.exp (((Real.pi/2 : ℝ) : ℂ)*Complex.I) = Complex.I := by
    rw [Complex.exp_mul_I]
    simp
  have hn : Complex.exp (((-Real.pi/2 : ℝ) : ℂ)*Complex.I) = -Complex.I := by
    rw [show -Real.pi/2 = -(Real.pi/2) from by ring]
    simp only [Complex.ofReal_neg, neg_mul, Complex.exp_neg, hp, Complex.inv_I]
  have hc2 : Real.cos θ = 2*Real.cos (θ/2)^2-1 := by
    convert! Real.cos_two_mul (θ/2) using 1
    congr 1
    ring
  have hs2 : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
    convert! Real.sin_two_mul (θ/2) using 1
    congr 1
    ring
  have hcos : 1 + Complex.exp ((θ : ℂ)*Complex.I) =
      2*Complex.exp (((θ/2 : ℝ) : ℂ)*Complex.I)*(Real.cos (θ/2) : ℂ) := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,hc2,hs2]
    push_cast
    ring
  have hsin : Complex.I*(1-Complex.exp ((θ : ℂ)*Complex.I)) =
      2*Complex.exp (((θ/2 : ℝ) : ℂ)*Complex.I)*(Real.sin (θ/2) : ℂ) := by
    rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,hc2,hs2]
    have ht : (Real.sin (θ/2) : ℂ)^2+(Real.cos (θ/2) : ℂ)^2=1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq (θ/2)
    push_cast at ht ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring))
      -(2*Complex.I)*ht
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_ofNat, div_eq_mul_inv,
    mul_comm, mul_assoc] at hcos hsin
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹)^2=(1/2 : ℂ) := by
    simpa [pow_two] using! Qatlib.Concepts.QuditTeleport.TeleportCore.sqrt2_inv_sq
  ext i j
  rcases i <;> rcases j <;>
    simp [Rz, Hadamard, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      qubitEulerRotation_apply, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    simp only [div_eq_mul_inv,mul_comm,mul_left_comm] <;>
    generalize Complex.exp _ = e at hcos hsin ⊢ <;>
    generalize Complex.exp _ = z at hcos hsin ⊢ <;>
    solve
    | linear_combination (norm := (ring_nf; simp only [hsq,Complex.I_sq]; ring)) (1/2 : ℂ)*hcos
    | linear_combination (norm := (ring_nf; simp only [hsq]; ring)) (1/2 : ℂ)*hsin
    | linear_combination (norm := (ring_nf; simp only [hsq]; ring)) -(1/2 : ℂ)*hsin

/-- Z rotations turn addition of angles into matrix multiplication. -/
private theorem rz_add (s t : ℝ) : Rz (s+t)=Rz s*Rz t := by
  ext i j
  rcases i <;> rcases j <;> simp [Rz,Matrix.mul_apply,← Complex.exp_add]
  congr 1
  ring

/-- The displayed Z-Hadamard Euler product equals `knownQubitUnitary p` times the explicitly
stated phase. -/
private theorem euler_zxz (p : KnownQubitAngles) :
    Rz (-p.alpha-Real.pi/2)*Hadamard*Rz p.theta*Hadamard*
      Rz (-p.beta+Real.pi/2) =
    Complex.exp ((((p.theta-p.alpha-p.beta)/2-p.delta : ℝ) : ℂ)*Complex.I) •
      knownQubitUnitary p := by
  have hleft : Rz (-p.alpha-Real.pi/2) = Rz (-p.alpha)*Rz (-Real.pi/2) := by
    rw [← rz_add]
    congr 1
    ring
  have hright : Rz (-p.beta+Real.pi/2) = Rz (Real.pi/2)*Rz (-p.beta) := by
    rw [← rz_add]
    congr 1
    ring
  rw [hleft,hright]
  have hassoc : Rz (-p.alpha)*Rz (-Real.pi/2)*Hadamard*Rz p.theta*Hadamard*
      (Rz (Real.pi/2)*Rz (-p.beta)) =
      Rz (-p.alpha)*(Rz (-Real.pi/2)*Hadamard*Rz p.theta*Hadamard*
        Rz (Real.pi/2))*Rz (-p.beta) := by simp only [Matrix.mul_assoc]
  rw [hassoc, rotation_middle, rz_phase (-p.alpha), rz_phase (-p.beta)]
  simp only [neg_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul, knownQubitUnitary]
  congr 1
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every one-qubit unitary is compiled by its four-step cluster word with unit-modulus
parameters and a unit-modulus overall scalar. See [RaussendorfBriegel2000]. -/
theorem universalQubitCompilation_answer : UniversalQubitCompilation := by
  intro U hU
  let p := knownQubitAnglesOfUnitary U
  have h := cluster_euler_four_measurement_actual_consumer
    (-p.alpha-Real.pi/2) p.theta (-p.beta+Real.pi/2)
  refine ⟨h.1,h.2.1,?_,?_⟩
  · exact Complex.norm_exp_ofReal_mul_I _
  · change clusterSequenceUnitary (clusterEulerWord _ _ _) = _
    rw [h.2.2.1,clusterEulerRotation,euler_zxz,
      (knownQubitEuler_explicit_angles_cover_unitaries U hU).1,graphRelabel_smul]
    rfl

end Qatlib.Concepts.ClusterPatterns.QubitUniversal
