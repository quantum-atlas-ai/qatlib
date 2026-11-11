/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities

/-!
# Fourier amplitudes of arbitrary marked sets

This module computes Fourier amplitudes for an arbitrary finite marked set in the amplified
transform and in phase-oracle and Boolean-output baselines. The formulas express
nonzero-frequency amplitudes through the marked-set phase sum, in the amplified-transform
setting of [Cornwell2014].

For the amplified state, the marked cardinality is positive and at most half the ambient
dimension. The baseline zero-frequency probabilities are computed separately, and
`aq_marked_three_probabilities` packages the three nonzero-frequency measurement formulas.

## Main statements

* `aq_marked_nonzero_amplitude`: express the amplified amplitude as a scaled phase sum.
* `aq_marked_phase_zero_amplitude`: compute the phase baseline's zero-frequency probability.
* `aq_marked_three_probabilities`: compare the amplified, phase, and Boolean-output
  probabilities.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open Matrix
open scoped Classical BigOperators Kronecker

/-- For a marked set of positive cardinality `T` with `2 * T ≤ N`, the amplified amplitude at
nonzero frequency is its phase sum multiplied by `tan(aqAngle N T) * sin(2 * aqRounds N T *
aqAngle N T) / T`. -/
theorem aq_marked_nonzero_amplitude (N : ℕ) (hN : 0 < N) (T : ℕ)
    (B : Finset (Fin N)) (y : Fin N) (hT : 0 < T) (hcard : B.card=T)
    (h2T : 2*T ≤ N) (hy : y.val ≠ 0) :
    aqState N hN T B y =
      ((Real.tan (aqAngle N T)*Real.sin (2*(aqRounds N T : ℝ)*aqAngle N T)/(T : ℝ) : ℝ) : ℂ)*
        ∑ x ∈ B, aqPhase N x.val y.val := by
  let A := B
  let theta := aqAngle N T
  let k := aqRounds N T
  have ht := aq_angle_properties N T hN hT h2T
  have hp : MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A = (Real.sin theta)^2 := by
    rw [aq_prepared_mass, hcard]
    exact ht.2.2.2.1.symm
  have hr := prepared_aa_actual_rotation (QFTMatrix N) ⟨0,hN⟩ A theta k (qftMatrix_unitary hN)
    ht.1 ht.2.2.1 hp
  rw [aqState, aqCircuit, run_append, run_gate, run_nil, hr]
  simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ((Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta:ℝ):ℂ)*
      (ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) y -
        ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) y) +
    ((Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta:ℝ):ℂ)*
      ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) y = _
  rw [aq_inverse_uniform, aq_inverse_selected]
  have hy0 : y ≠ (⟨0,hN⟩ : Fin N) := by intro h; exact hy (congrArg Fin.val h)
  simp only [Ket, if_neg hy0, zero_sub]
  have hc : Real.cos theta ≠ 0 := ht.2.2.2.2.2.ne'
  have hs : Real.sin theta ≠ 0 := ht.2.2.2.2.1.ne'
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (T:ℝ) = (N:ℝ)*(Real.sin theta)^2 := by
    have h := congrArg (fun z : ℝ => z*(N:ℝ)) ht.2.2.2.1
    (try dsimp only at h)
    rw [div_mul_cancel₀ _ hNR] at h
    simpa only [mul_comm] using! h.symm
  have hdiff : Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta -
      Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta =
      Real.sin (2*(k:ℝ)*theta)/(Real.sin theta*Real.cos theta) := by
    have h := Real.sin_sub ((2*(k:ℝ)+1)*theta) theta
    have ha : (2*(k:ℝ)+1)*theta-theta = 2*(k:ℝ)*theta := by ring
    rw [ha] at h
    field_simp
    nlinarith only [h]
  have hcoeff : (Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta -
      Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta)/(N:ℝ) =
      Real.tan theta*Real.sin (2*(k:ℝ)*theta)/(T:ℝ) := by
    rw [hdiff, Real.tan_eq_sin_div_cos, hm]
    field_simp
  have hcoeffC := congrArg Complex.ofReal hcoeff
  calc
    _ = (((Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta -
        Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta)/(N:ℝ):ℝ):ℂ)*
        (∑ x ∈ B, aqPhase N x.val y.val) := by
      simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    _ = _ := congrArg (fun z : ℂ => z*(∑ x ∈ B, aqPhase N x.val y.val)) hcoeffC

/-- At every frequency, the phase-oracle baseline amplitude is the zero-frequency basis
amplitude minus `2 / N` times the marked-set phase sum. -/
theorem aq_marked_phase_all (N : ℕ) (hN : 0 < N) (B : Finset (Fin N)) (y : Fin N) :
    aqPhaseBaseline N hN B y=Ket ⟨0,hN⟩ y-
      2*(N : ℂ)⁻¹*∑ x ∈ B, aqPhase N x.val y.val := by
  have hm : ApplyGate (preparedMark B) (preparedAAState (QFTMatrix N) ⟨0,hN⟩)=
      preparedAAState (QFTMatrix N) ⟨0,hN⟩-
        (2 : ℂ) • Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B := by
    simp only [preparedMark, ApplyGate, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [aqPhaseBaseline, ← preparedAAState, hm]
  simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul]
  change ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) y-
    (2 : ℂ)*ApplyGate (QFTMatrix N)ᴴ
      (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B) y = _
  rw [aq_inverse_uniform, aq_inverse_selected]
  ring

/-- At a nonzero frequency, the phase-oracle baseline amplitude is `-2 / N` times the marked-set
phase sum. -/
theorem aq_marked_phase_amplitude (N : ℕ) (hN : 0 < N) (B : Finset (Fin N))
    (y : Fin N) (hy : y.val ≠ 0) :
    aqPhaseBaseline N hN B y=((-2/(N : ℝ) : ℝ) : ℂ)*
      ∑ x ∈ B, aqPhase N x.val y.val := by
  rw [aq_marked_phase_all]
  have hy0 : y ≠ (⟨0,hN⟩ : Fin N) := by intro he; exact hy (congrArg Fin.val he)
  simp only [Ket, if_neg hy0]
  push_cast
  ring

/-- The phase-oracle baseline's Born probability at frequency zero is `(1 - 2 * B.card / N)^2`. -/
theorem aq_marked_phase_zero_amplitude (N : ℕ) (hN : 0 < N) (B : Finset (Fin N)) :
    BornProb (aqPhaseBaseline N hN B) ⟨0,hN⟩=(1-2*(B.card : ℝ)/(N : ℝ))^2 := by
  have he : aqPhaseBaseline N hN B ⟨0,hN⟩=((1-2*(B.card : ℝ)/(N : ℝ) : ℝ) : ℂ) := by
    rw [aq_marked_phase_all]
    simp only [Ket, if_true]
    simp [aqPhase]
    ring
  rw [BornProb, he, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- When `f` marks exactly `B`, each Boolean-output slice of the baseline is the inverse Fourier
transform of the marked component or its complementary component of the prepared state. -/
theorem aq_marked_qhs_slices (N : ℕ) (hN : 0 < N) (B : Finset (Fin N))
    (f : Fin N → Bool) (hmark : ∀ x, f x=decide (x ∈ B)) (y : Fin N) (b : Bool) :
    aqQHSBaseline N hN f (y,b)=ApplyGate (QFTMatrix N)ᴴ
      (if b then Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B else
        preparedAAState (QFTMatrix N) ⟨0,hN⟩-Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B) y := by
  unfold aqQHSBaseline
  change ApplyGate (TensorGate (QFTMatrix N)ᴴ 1) _ (y,b) = _
  rw [applyGate_tensorGate_one_left_slice]
  have hslice : (fun x : Fin N => ApplyGate (BitOracleOn f)
      (TensorState (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (Ket false)) (x,b))=
      if b then Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B else
        preparedAAState (QFTMatrix N) ⟨0,hN⟩-Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B := by
    funext x
    rw [applyGate_bitOracleOn]
    have hx := hmark x
    cases b <;> by_cases h : x ∈ B <;>
      simp [TensorState, BitFlip, Ket, collapse_apply, hx, h]
  change ApplyGate (QFTMatrix N)ᴴ
    (fun x : Fin N => ApplyGate (BitOracleOn f)
      (TensorState (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (Ket false)) (x,b)) y = _
  rw [hslice]

/-- For nonzero frequency and an oracle marking exactly `B`, the true-output baseline amplitude
is the marked-set phase sum divided by `N`, and the false-output amplitude is its negative. -/
theorem aq_marked_qhs_amplitudes (N : ℕ) (hN : 0 < N) (B : Finset (Fin N))
    (f : Fin N → Bool) (hmark : ∀ x, f x=decide (x ∈ B)) (y : Fin N) (hy : y.val ≠ 0) :
    aqQHSBaseline N hN f (y,true)=(N : ℂ)⁻¹*∑ x ∈ B, aqPhase N x.val y.val ∧
    aqQHSBaseline N hN f (y,false)=-((N : ℂ)⁻¹*∑ x ∈ B, aqPhase N x.val y.val) := by
  constructor
  · rw [aq_marked_qhs_slices N hN B f hmark y true, if_pos rfl, aq_inverse_selected]
  · rw [aq_marked_qhs_slices N hN B f hmark y false, if_neg Bool.false_ne_true]
    simp only [ApplyGate, Matrix.mulVec_sub, Pi.sub_apply]
    change ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) y-
      ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B) y = _
    rw [aq_inverse_uniform, aq_inverse_selected]
    have hy0 : y ≠ (⟨0,hN⟩ : Fin N) := by intro he; exact hy (congrArg Fin.val he)
    simp [Ket, hy0]

/-- When the oracle marks exactly `B`, the Boolean-output baseline probability of frequency
zero, summed over both output bits, is `(B.card / N)^2 + (1 - B.card / N)^2`. -/
theorem aq_marked_qhs_zero_amplitude (N : ℕ) (hN : 0 < N) (B : Finset (Fin N))
    (f : Fin N → Bool) (hmark : ∀ x, f x=decide (x ∈ B)) :
    MeasureProb (aqQHSBaseline N hN f) ({⟨0,hN⟩} ×ˢ Finset.univ)=
      ((B.card : ℝ)/(N : ℝ))^2+(1-(B.card : ℝ)/(N : ℝ))^2 := by
  have ht : aqQHSBaseline N hN f (⟨0,hN⟩,true)=(((B.card : ℝ)/(N : ℝ) : ℝ) : ℂ) := by
    rw [aq_marked_qhs_slices N hN B f hmark ⟨0,hN⟩ true, if_pos rfl,
      aq_inverse_selected_zero]
    simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  have hf : aqQHSBaseline N hN f (⟨0,hN⟩,false)=((1-(B.card : ℝ)/(N : ℝ) : ℝ) : ℂ) := by
    rw [aq_marked_qhs_slices N hN B f hmark ⟨0,hN⟩ false, if_neg Bool.false_ne_true]
    simp only [ApplyGate, Matrix.mulVec_sub, Pi.sub_apply]
    change ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) ⟨0,hN⟩-
      ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) B) ⟨0,hN⟩ = _
    rw [aq_inverse_uniform, aq_inverse_selected_zero]
    simp [Ket]
  unfold MeasureProb BornProb
  rw [Finset.sum_product, Finset.sum_singleton]
  simp only [Fintype.sum_bool, ht, hf, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- For a marked set of positive cardinality `T ≤ N / 2` and its exact Boolean oracle, the three
nonzero-frequency probabilities equal the squared marked-set phase sum times their stated
amplified, phase-oracle, and Boolean-output prefactors. -/
theorem aq_marked_three_probabilities (N : ℕ) (hN : 0 < N) (T : ℕ)
    (B : Finset (Fin N)) (f : Fin N → Bool) (y : Fin N)
    (hT : 0 < T) (hcard : B.card=T) (h2T : 2*T ≤ N)
    (hmark : ∀ x, f x=decide (x ∈ B)) (hy : y.val ≠ 0) :
    BornProb (aqState N hN T B) y=(Real.tan (aqAngle N T))^2*aqGain N T*
      Complex.normSq (∑ x ∈ B, aqPhase N x.val y.val)/(T : ℝ)^2 ∧
    BornProb (aqPhaseBaseline N hN B) y=4*Complex.normSq
      (∑ x ∈ B, aqPhase N x.val y.val)/(N : ℝ)^2 ∧
    MeasureProb (aqQHSBaseline N hN f) ({y} ×ˢ Finset.univ)=2*Complex.normSq
      (∑ x ∈ B, aqPhase N x.val y.val)/(N : ℝ)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BornProb, aq_marked_nonzero_amplitude N hN T B y hT hcard h2T hy,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
    unfold aqGain
    ring
  · rw [BornProb, aq_marked_phase_amplitude N hN B y hy,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  · have hp := aq_marked_qhs_amplitudes N hN B f hmark y hy
    unfold MeasureProb BornProb
    rw [Finset.sum_product, Finset.sum_singleton]
    simp only [Fintype.sum_bool, hp.1, hp.2, norm_neg, norm_mul, norm_inv,
      Complex.norm_natCast, mul_pow]
    rw [← Complex.normSq_eq_norm_sq]
    ring

end Qatlib.Concepts.AmpTransform.ErrorStream
