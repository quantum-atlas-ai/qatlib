/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.FiniteBitCost.FiniteQSPOperator
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2

@[expose] public section
open Qatlib.Concepts.NativeNumerics.NlfftPipeline Qatlib.Concepts.LaurentPolys.FiniteBitCost Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

set_option autoImplicit false
namespace Qatlib.Concepts.LaurentPolys.FiniteBitCost
open Polynomial Matrix
open scoped Matrix.Norms.L2Operator

/-- Squaring the complex exponential of an imaginary angle doubles that angle. -/
theorem rhw_qsp_bridge_exp_square (θ : ℝ) :
    Complex.exp ((θ:ℂ)*Complex.I)^2=Complex.exp (((2*θ:ℝ):ℂ)*Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The QSP phase gates are unitary, the signal gates are unitary on the unit interval, and
Hadamard conjugation of the diagonal phase gives the cosine signal gate. -/
theorem rhw_qsp_bridge_gate_certificate : (∀ φ : ℝ, rhwQSPBridgePhase φ∈Matrix.unitaryGroup Bool ℂ) ∧
  (∀ x : ℝ, 0≤x → x≤1 → rhwQSPBridgeSignal x∈Matrix.unitaryGroup Bool ℂ) ∧
  (∀ θ : ℝ, θ∈Set.Icc (0:ℝ) (Real.pi/2) →
    Hadamard*rhwQSPBridgeDiagonal (Complex.exp ((θ:ℂ)*Complex.I))*Hadamard=
      rhwQSPBridgeSignal (Real.cos θ)) := by
  exact ⟨rhw_qsp_bridge_phase_unitary,rhw_qsp_bridge_signal_unitary,rhw_qsp_bridge_had_signal⟩

/-- For angles strictly between minus and plus one half of pi, the bridge coefficient
normalization is cosine and its factor becomes the phase gate under Hadamard conjugation. -/
theorem rhw_qsp_bridge_factor_certificate : ∀ φ : ℝ, φ∈Set.Ioo (-(Real.pi/2)) (Real.pi/2) →
  (Real.sqrt (1+Complex.normSq (rhwQSPBridgeCoefficient φ)))⁻¹=Real.cos φ ∧
  rhwQSPBridgeFactor (rhwQSPBridgeCoefficient φ)=
    rhwQSPBridgeMatrix (Real.cos φ:ℂ) (Complex.I*(Real.sin φ:ℂ))
      (Complex.I*(Real.sin φ:ℂ)) (Real.cos φ:ℂ) ∧
  Hadamard*rhwQSPBridgeFactor (rhwQSPBridgeCoefficient φ)*Hadamard=rhwQSPBridgePhase φ := by
  intro φ hφ
  have hn : Complex.normSq (rhwQSPBridgeCoefficient φ)=Real.tan φ^2 := by
    simp only [rhwQSPBridgeCoefficient,Complex.normSq_mul,Complex.normSq_I,one_mul,
      Complex.normSq_ofReal,pow_two]
  exact ⟨by rw [hn]; exact Real.inv_sqrt_one_add_tan_sq (Real.cos_pos_of_mem_Ioo hφ),
    rhw_qsp_bridge_elem_angle φ hφ,rhw_qsp_bridge_had_elem φ hφ⟩

/-- For unit modulus signals, the bridge pair, word, and centered forms satisfy the stated
diagonal transfer identities. -/
theorem rhw_qsp_bridge_transfer_certificate : ∀ (gs : List ℂ) (w : ℂ), ‖w‖=1 →
  rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^gs.length=
    rhwQSPBridgeWord w gs*rhwQSPBridgeDiagonal w ∧
  (gs≠[] → rhwQSPBridgeWord w gs=
    rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^(gs.length-1)) ∧
  (∀ d : ℕ, (rhwQSPBridgeDiagonal w)^d*rhwQSPBridgeCentered d gs (w^2)*
    (rhwQSPBridgeDiagonal w)^d=rhwQSPBridgePair gs (w^2)*(rhwQSPBridgeDiagonal w)^(2*d)) := by
  intro gs w hw
  exact ⟨rhw_qsp_bridge_pair_word gs w hw,
    fun hgs => rhw_qsp_bridge_word_pair_nonempty gs hgs w hw,
    fun d => rhw_qsp_bridge_centered_sandwich d gs w hw⟩

/-- For the stated angle ranges, the symmetric bridge list has the prescribed length and
centered coefficients and realizes the QSP operator through the centered sandwich. -/
theorem rhw_qsp_bridge_operator_certificate : ∀ (ψ : ℕ → ℝ) (d : ℕ) (θ : ℝ),
  θ∈Set.Icc (0:ℝ) (Real.pi/2) →
  (∀ k≤d,ψ k∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) →
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  (rhwQSPBridgeGammas ψ d).length=2*d+1 ∧
  (∀ k≤d, (rhwQSPBridgeGammas ψ d).getD (d-k) 0=rhwQSPBridgeCoefficient (ψ k) ∧
    (rhwQSPBridgeGammas ψ d).getD (d+k) 0=rhwQSPBridgeCoefficient (ψ k)) ∧
  rhwQSPBridgeOperator ψ (Real.cos θ) d=
    Hadamard*(rhwQSPBridgeDiagonal w)^d*
      rhwQSPBridgeCentered d (rhwQSPBridgeGammas ψ d) (w^2)*(rhwQSPBridgeDiagonal w)^d*Hadamard := by
  intro ψ d θ hθ hψ
  exact ⟨rhw_qsp_bridge_sym_length ψ d,rhw_qsp_bridge_sym_get_center ψ d,
    rhw_qsp_bridge_eq27 ψ d θ hθ hψ⟩

/-- For the stated angle ranges, the QSP operator is symmetric and its imaginary diagonal
observable equals the scaled second nonlinear Fourier polynomial. -/
theorem rhw_qsp_bridge_observable_certificate : ∀ (ψ : ℕ → ℝ) (d : ℕ) (θ : ℝ),
  θ∈Set.Icc (0:ℝ) (Real.pi/2) →
  (∀ k≤d,ψ k∈Set.Ioo (-(Real.pi/2)) (Real.pi/2)) →
  let z := Complex.exp (((2*θ:ℝ):ℂ)*Complex.I)
  (rhwQSPBridgeOperator ψ (Real.cos θ) d).transpose=rhwQSPBridgeOperator ψ (Real.cos θ) d ∧
  Complex.I*((rhwQSPBridgeOperator ψ (Real.cos θ) d) false false).im=
    (z^d)⁻¹*(nlftSU2 (rhwQSPBridgeGammas ψ d)).2.eval z := by
  intro ψ d θ hθ hψ
  have h := rhw_qsp_bridge_eq28 ψ d θ hθ hψ
  dsimp only at h ⊢
  rw [rhw_qsp_bridge_exp_square] at h
  exact ⟨rhw_qsp_bridge_qsp_symmetric ψ (Real.cos θ) d,h⟩

end Qatlib.Concepts.LaurentPolys.FiniteBitCost
