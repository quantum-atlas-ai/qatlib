/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression

/-!
# Amplified Fourier probabilities and baseline ratios

This module defines phase-query and hidden-subgroup baseline states and compares their
nonzero-frequency probabilities with amplified Fourier sampling.
`amplified_progression_success_event_probability_ratios` extends the pointwise formulas to
events excluding zero, providing the success ratios analyzed in [Cornwell2014].

## Main statements

* `amplified_progression_actual_three_algorithm_probabilities`: At a nonzero frequency, gives
  exact amplified, phase-baseline, and label-marginal hidden-subgroup probabilities in terms of
  the squared progression Fourier sum; see [Cornwell2014].
* `amplified_progression_success_event_probability_ratios`: For events excluding zero, the
  amplified probability is `aqRatio N M` times the phase-baseline probability and twice that
  ratio times the hidden-subgroup event probability; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Matrix
open scoped Classical BigOperators Kronecker

/-- The state obtained by Fourier preparation, a phase oracle for A, and the inverse Fourier
transform. -/
noncomputable def aqPhaseBaseline (N : ℕ) (hN : 0< N) (A : Finset (Fin N)) : QState (Fin N) :=
  ApplyGate (QFTMatrix N)ᴴ (ApplyGate (preparedMark A) (ApplyGate (QFTMatrix N) (Ket ⟨0,hN⟩)))
/-- The two-register baseline state obtained by uniform Fourier preparation, a Boolean bit
oracle, and the inverse Fourier transform on the label register. -/
noncomputable def aqQHSBaseline (N : ℕ) (hN : 0< N) (f : Fin N→Bool) : QState (Fin N×Bool) :=
  ApplyGate ((QFTMatrix N)ᴴ⊗ₖ(1:Matrix Bool Bool ℂ))
    (ApplyGate (BitOracleOn f) (TensorState (ApplyGate (QFTMatrix N) (Ket ⟨0,hN⟩)) (Ket false)))
/-- The probability ratio N² · `aqGain N M` / (4M(N−M)), with natural subtraction in N−M. -/
noncomputable def aqRatio (N M : ℕ) : ℝ := (N:ℝ)^2*aqGain N M/(4*(M:ℝ)*(N-M:ℕ))

/-- The inverse Fourier matrix entry at y,x is the reciprocal square-root normalization times
`aqPhase N x.val y.val`. -/
theorem aq_inverse_entry (N : ℕ) (x y : Fin N) :
    ((QFTMatrix N)ᴴ) y x = (Real.sqrt (N:ℝ):ℂ)⁻¹*aqPhase N x.val y.val := by
  rw [Matrix.conjTranspose_apply, qftMatrix_apply]
  change (starRingEnd ℂ) ((Real.sqrt (N:ℝ):ℂ)⁻¹*primRoot N ^ (((x.val:ℤ)*(y.val:ℤ)))) = _
  rw [map_mul, map_inv₀,
    Complex.conj_ofReal, primRoot_conj_zpow, primRoot_zpow_eq_exp]
  congr 1
  unfold aqPhase
  congr 1
  push_cast
  ring

/-- The inverse Fourier transform of the restricted uniform prepared state has amplitude equal
to the selected phase sum divided by N. -/
theorem aq_inverse_selected (N : ℕ) (hN : 0 < N) (A : Finset (Fin N)) (y : Fin N) :
    ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) y =
      (N:ℂ)⁻¹*∑ x ∈ A, aqPhase N x.val y.val := by
  rw [preparedAAState, qftMatrix_ket_zero N hN]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, collapse_apply, aq_inverse_entry]
  have he (x : Fin N) : (Real.sqrt (N:ℝ):ℂ)⁻¹*aqPhase N x.val y.val*
      (if x ∈ A then (Real.sqrt (N:ℝ):ℂ)⁻¹ else 0) =
      if x ∈ A then (N:ℂ)⁻¹*aqPhase N x.val y.val else 0 := by
    by_cases hx : x ∈ A
    · rw [if_pos hx, if_pos hx]
      have hh : (Real.sqrt (N:ℝ):ℂ)⁻¹*aqPhase N x.val y.val*(Real.sqrt (N:ℝ):ℂ)⁻¹ =
          ((Real.sqrt (N:ℝ):ℂ)⁻¹*(Real.sqrt (N:ℝ):ℂ)⁻¹)*aqPhase N x.val y.val := by ring
      rw [hh, inv_sqrt_mul_inv_sqrt hN]
    · simp [hx]
  calc
    _ = ∑ x : Fin N, if x ∈ A then (N:ℂ)⁻¹*aqPhase N x.val y.val else 0 :=
      Finset.sum_congr rfl (fun x hx => he x)
    _ = ∑ x ∈ A, (N:ℂ)⁻¹*aqPhase N x.val y.val := Finset.sum_ite_mem_eq A _
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- For a positive-step progression contained in the domain, summing phases over its set equals
`aqProgressionFourier`. -/
theorem aq_progression_root_sum (N s M P y : ℕ) (hM : 0 < M) (hP : 0 < P)
    (hbound : s+(M-1)*P < N) :
    (∑ x ∈ aqProgressionSet N s M P, aqPhase N x.val y) = aqProgressionFourier N s M P y := by
  let e : Fin M → Fin N :=
      fun r => ⟨s+r.val*P,aqProgression_index_lt N s M P r.val hM hbound r.isLt⟩
  have he : Function.Injective e := by
    intro r t h
    exact Fin.ext (mul_right_cancel₀ hP.ne' (Nat.add_left_cancel (congrArg Fin.val h)))
  have hset : aqProgressionSet N s M P = Finset.univ.image e := by
    ext x
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨r,hr,hx⟩
      exact ⟨⟨r,Finset.mem_range.mp hr⟩, Fin.ext hx.symm⟩
    · rintro ⟨r,hx⟩
      exact ⟨r.val, Finset.mem_range.mpr r.isLt, congrArg Fin.val hx.symm⟩
  rw [hset, Finset.sum_image]
  · change (∑ r : Fin M, aqPhase N (s+r.val*P) y) = _
    exact Fin.sum_univ_eq_sum_range (fun r : ℕ => aqPhase N (s+r*P) y) M
  · intro r hr t ht h
    exact he h

/-- At nonzero frequencies, the amplified progression amplitude is its Fourier sum times tan θ ·
sin(2kθ)/M under the half-density assumptions. -/
theorem aq_actual_nonzero_amplitude (N : ℕ) (hN : 0 < N) (s M P : ℕ) (y : Fin N)
    (hM : 0 < M) (hP : 0 < P) (hbound : s+(M-1)*P < N) (hMN : 2*M ≤ N) (hy : y.val ≠ 0) :
    aqState N hN M (aqProgressionSet N s M P) y =
      ((Real.tan (aqAngle N M)*Real.sin (2*(aqRounds N M:ℝ)*aqAngle N M)/(M:ℝ):ℝ):ℂ)*
        aqProgressionFourier N s M P y.val := by
  let A := aqProgressionSet N s M P
  let theta := aqAngle N M
  let k := aqRounds N M
  have ht := aq_angle_properties N M hN hM hMN
  have hp : MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A = (Real.sin theta)^2 := by
    rw [aq_prepared_mass, aqProgression_card N s M P hM hP hbound]
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
  rw [aq_progression_root_sum N s M P y.val hM hP hbound]
  have hc : Real.cos theta ≠ 0 := ht.2.2.2.2.2.ne'
  have hs : Real.sin theta ≠ 0 := ht.2.2.2.2.1.ne'
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (M:ℝ) = (N:ℝ)*(Real.sin theta)^2 := by
    have h := congrArg (fun z : ℝ => z*(N:ℝ)) ht.2.2.2.1

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
      Real.tan theta*Real.sin (2*(k:ℝ)*theta)/(M:ℝ) := by
    rw [hdiff, Real.tan_eq_sin_div_cos, hm]
    field_simp
  have hcoeffC := congrArg Complex.ofReal hcoeff
  calc
    _ = (((Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta -
        Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta)/(N:ℝ):ℝ):ℂ)*
        aqProgressionFourier N s M P y.val := by
      simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    _ = _ := congrArg (fun z : ℂ => z*aqProgressionFourier N s M P y.val) hcoeffC

/-- At nonzero frequencies, the phase-query baseline amplitude is −2/N times the progression
Fourier sum. -/
theorem aq_phase_nonzero_amplitude (N : ℕ) (hN : 0 < N) (s M P : ℕ) (y : Fin N)
    (hM : 0 < M) (hP : 0 < P) (hbound : s+(M-1)*P < N) (hy : y.val ≠ 0) :
    aqPhaseBaseline N hN (aqProgressionSet N s M P) y =
      ((-2/(N:ℝ):ℝ):ℂ)*aqProgressionFourier N s M P y.val := by
  let A := aqProgressionSet N s M P
  have hm : ApplyGate (preparedMark A) (preparedAAState (QFTMatrix N) ⟨0,hN⟩) =
      preparedAAState (QFTMatrix N) ⟨0,hN⟩ - (2:ℂ) • Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A := by
    simp only [preparedMark, ApplyGate, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [aqPhaseBaseline, ← preparedAAState, hm]
  simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul]
  change ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) y -
    (2:ℂ)*ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) y = _
  rw [aq_inverse_uniform, aq_inverse_selected, aq_progression_root_sum N s M P y.val hM hP hbound]
  have hy0 : y ≠ (⟨0,hN⟩ : Fin N) := by intro h; exact hy (congrArg Fin.val h)
  simp only [Ket, if_neg hy0]
  push_cast
  ring

/-- The hidden-subgroup baseline's Boolean slices are inverse Fourier transforms of the marked
and complementary parts of the prepared uniform state. -/
theorem aq_qhs_slices (N : ℕ) (hN : 0 < N) (s M P : ℕ) (f : Fin N → Bool)
    (hmark : AQMarkPromise f s M P) (y : Fin N) (b : Bool) :
    aqQHSBaseline N hN f (y,b) =
      ApplyGate (QFTMatrix N)ᴴ (if b then Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩)
        (aqProgressionSet N s M P) else preparedAAState (QFTMatrix N) ⟨0,hN⟩-
          Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (aqProgressionSet N s M P)) y := by
  unfold aqQHSBaseline
  change ApplyGate (TensorGate (QFTMatrix N)ᴴ 1) _ (y,b) = _
  rw [applyGate_tensorGate_one_left_slice]
  have hslice : (fun x : Fin N => ApplyGate (BitOracleOn f)
      (TensorState (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (Ket false)) (x,b)) =
      if b then Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (aqProgressionSet N s M P)
      else preparedAAState (QFTMatrix N) ⟨0,hN⟩-
        Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (aqProgressionSet N s M P) := by
    funext x
    rw [applyGate_bitOracleOn]
    have hx := hmark x
    cases b <;> by_cases h : x ∈ aqProgressionSet N s M P <;>
      simp [TensorState, BitFlip, Ket, collapse_apply, hx, h]
  change ApplyGate (QFTMatrix N)ᴴ
    (fun x : Fin N => ApplyGate (BitOracleOn f)
      (TensorState (preparedAAState (QFTMatrix N) ⟨0,hN⟩) (Ket false)) (x,b)) y = _
  rw [hslice]

/-- At a nonzero frequency, gives exact amplified, phase-baseline, and label-marginal
hidden-subgroup probabilities in terms of the squared progression Fourier sum; see
[Cornwell2014]. -/
theorem amplified_progression_actual_three_algorithm_probabilities : ∀ (N : ℕ) (hN : 0< N) (s M P : ℕ) (f : Fin N→Bool) (y : Fin N),
  2≤ M → 0< P → s+(M-1)*P< N → 2*M≤ N → AQMarkPromise f s M P → y.val≠0 →
  let a:= aqProgressionFourier N s M P y.val;
  BornProb (aqState N hN M (aqProgressionSet N s M P)) y=
    (Real.tan (aqAngle N M))^2*aqGain N M*Complex.normSq a/(M:ℝ)^2 ∧
  BornProb (aqPhaseBaseline N hN (aqProgressionSet N s M P)) y=4*Complex.normSq a/(N:ℝ)^2 ∧
  MeasureProb (aqQHSBaseline N hN f) ({y}×ˢFinset.univ)=2*Complex.normSq a/(N:ℝ)^2

 := by
  intro N hN s M P f y hM hP hbound hMN hmark hy
  have hMpos : 0 < M := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [BornProb, aq_actual_nonzero_amplitude N hN s M P y hMpos hP hbound hMN hy]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
    unfold aqGain
    ring
  · rw [BornProb, aq_phase_nonzero_amplitude N hN s M P y hMpos hP hbound hy]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  · unfold MeasureProb BornProb
    rw [Finset.sum_product, Finset.sum_singleton]
    have hy0 : y ≠ (⟨0,hN⟩ : Fin N) := by intro h; exact hy (congrArg Fin.val h)
    have ht : aqQHSBaseline N hN f (y,true) = (N:ℂ)⁻¹*aqProgressionFourier N s M P y.val := by
      rw [aq_qhs_slices N hN s M P f hmark y true, if_pos rfl, aq_inverse_selected,
        aq_progression_root_sum N s M P y.val hMpos hP hbound]
    have hf : aqQHSBaseline N hN f (y,false) = -(N:ℂ)⁻¹*aqProgressionFourier N s M P y.val := by
      rw [aq_qhs_slices N hN s M P f hmark y false, if_neg Bool.false_ne_true]
      simp only [ApplyGate, Matrix.mulVec_sub, Pi.sub_apply]
      change ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) y-
        ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) _) y = _
      rw [aq_inverse_uniform, aq_inverse_selected,
          aq_progression_root_sum N s M P y.val hMpos hP hbound]
      simp [Ket, hy0]
    simp only [Fintype.sum_bool, ht, hf, norm_neg, norm_mul, norm_inv, Complex.norm_natCast,
      mul_pow]
    rw [← Complex.normSq_eq_norm_sq]
    ring

/-- Under positive half-density assumptions, tan²(`aqAngle N M`) equals M/(N−M), with natural
subtraction in the denominator. -/
theorem aq_tan_density (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : 2*M ≤ N) :
    (Real.tan (aqAngle N M))^2 = (M:ℝ)/(N-M:ℕ) := by
  have ht := aq_angle_properties N M hN hM hMN
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsub : ((N-M:ℕ):ℝ) = (N:ℝ)-(M:ℝ) := by rw [Nat.cast_sub (by omega : M ≤ N)]
  have hc : (Real.cos (aqAngle N M))^2 = 1-(M:ℝ)/(N:ℝ) := by
    have h := Real.sin_sq_add_cos_sq (aqAngle N M)
    rw [ht.2.2.2.1] at h
    linarith
  rw [Real.tan_eq_sin_div_cos, div_pow, ht.2.2.2.1, hc, hsub]
  field_simp

/-- At a nonzero frequency, the amplified probability equals `aqRatio N M` times the
phase-baseline probability and twice that ratio times the hidden-subgroup label probability. -/
theorem aq_actual_point_ratios (N : ℕ) (hN : 0 < N) (s M P : ℕ) (f : Fin N → Bool)
    (y : Fin N) (hM : 2 ≤ M) (hP : 0 < P) (hbound : s+(M-1)*P < N)
    (hMN : 2*M ≤ N) (hmark : AQMarkPromise f s M P) (hy : y.val ≠ 0) :
    BornProb (aqState N hN M (aqProgressionSet N s M P)) y =
      aqRatio N M*BornProb (aqPhaseBaseline N hN (aqProgressionSet N s M P)) y ∧
    BornProb (aqState N hN M (aqProgressionSet N s M P)) y =
      2*aqRatio N M*MeasureProb (aqQHSBaseline N hN f) ({y} ×ˢ Finset.univ) := by
  have hp := amplified_progression_actual_three_algorithm_probabilities N hN s M P f y
    hM hP hbound hMN hmark hy
  have ht := aq_tan_density N M hN (by omega) hMN
  have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsub : ((N-M:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show N-M ≠ 0 by omega)
  rw [hp.1, hp.2.1, hp.2.2, ht]
  unfold aqRatio
  constructor
  · field_simp
  · field_simp
    norm_num

/-- For events excluding zero, the amplified probability is `aqRatio N M` times the
phase-baseline probability and twice that ratio times the hidden-subgroup event probability;
see [Cornwell2014]. -/
theorem amplified_progression_success_event_probability_ratios : ∀ (N : ℕ) (hN : 0< N) (s M P : ℕ) (f : Fin N→Bool) (E : Finset (Fin N)),
  2≤ M → 0< P → s+(M-1)*P< N → 2*M≤ N → AQMarkPromise f s M P → (⟨0,hN⟩:Fin N)∉E →
  MeasureProb (aqState N hN M (aqProgressionSet N s M P)) E=
    aqRatio N M*MeasureProb (aqPhaseBaseline N hN (aqProgressionSet N s M P)) E ∧
  MeasureProb (aqState N hN M (aqProgressionSet N s M P)) E=
    2*aqRatio N M*MeasureProb (aqQHSBaseline N hN f) (E×ˢFinset.univ)

 := by
  intro N hN s M P f E hM hP hbound hMN hmark hzero
  have hp (y : Fin N) (hy : y ∈ E) := aq_actual_point_ratios N hN s M P f y hM hP hbound hMN hmark
    (by
      intro hv
      apply hzero
      have hy0 : y = (⟨0,hN⟩ : Fin N) := Fin.ext hv
      exact hy0 ▸ hy)
  constructor
  · change (∑ y ∈ E, BornProb (aqState N hN M (aqProgressionSet N s M P)) y) =
      aqRatio N M*∑ y ∈ E, BornProb (aqPhaseBaseline N hN (aqProgressionSet N s M P)) y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y hy => (hp y hy).1)
  · have hs : MeasureProb (aqQHSBaseline N hN f) (E ×ˢ Finset.univ) =
        ∑ y ∈ E, MeasureProb (aqQHSBaseline N hN f) ({y} ×ˢ Finset.univ) := by
      simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton]
    rw [hs, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y hy => (hp y hy).2)

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
