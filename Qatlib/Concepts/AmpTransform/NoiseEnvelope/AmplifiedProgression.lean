/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicPeriodSampling
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Amplified sampling of an arithmetic progression

This module defines progression marking, Fourier phases, the Grover angle and round schedule,
and the executable amplified Fourier circuit. It proves exact circuit counts, the zero-frequency
amplitude, and gain bounds for the progression-sampling analysis of [Cornwell2014].

## Main statements

* `amplified_progression_actual_circuit_and_counts`: The contained progression has cardinality
  M, and its amplified circuit is unitary with normalized output, k queries, and 3k+2 gates for
  k = `aqRounds N M`. See [Cornwell2014].
* `amplified_progression_zero_mode_and_corrected_floor_bounds`: Gives the zero-frequency
  amplitude, positive gain bounds, the zero-frequency probability bound 4(M/N)(1−M/N), and the
  additional gain lower bound 1−2M²/N; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Matrix
open scoped Classical BigOperators Kronecker

/-- The Grover angle arcsin √(M/N). -/
noncomputable def aqAngle (N M : ℕ) : ℝ := Real.arcsin (Real.sqrt ((M:ℝ)/(N:ℝ)))
/-- The prescribed Grover round count ⌊π/(4 · `aqAngle N M`)⌋. -/
noncomputable def aqRounds (N M : ℕ) : ℕ := Nat.floor (Real.pi/(4*aqAngle N M))
/-- The squared sine gain sin²(2kθ) for the prescribed Grover angle and round count. -/
noncomputable def aqGain (N M : ℕ) : ℝ := (Real.sin (2*(aqRounds N M:ℝ)*aqAngle N M))^2
/-- The set of labels in `Fin N` equal to s+rP for some r < M. -/
def aqProgressionSet (N s M P : ℕ) : Finset (Fin N) :=
  {x | ∃ r∈Finset.range M,x.val= s+r*P}
/-- The marking promise that f is the indicator of `aqProgressionSet N s M P`. -/
def AQMarkPromise {N : ℕ} (f : Fin N→Bool) (s M P : ℕ) : Prop :=
  ∀ x,f x= decide (x∈aqProgressionSet N s M P)
/-- The negative Fourier phase exp(−2πi · x · y/N). -/
noncomputable def aqPhase (N x y : ℕ) : ℂ :=
  Complex.exp (((-2*Real.pi*(x:ℝ)*(y:ℝ)/(N:ℝ):ℝ):ℂ)*Complex.I)
/-- The sum of negative Fourier phases over the M progression terms starting at s with step P. -/
noncomputable def aqProgressionFourier (N s M P y : ℕ) : ℂ :=
  ∑ r∈Finset.range M,aqPhase N (s+r*P) y
/-- The prepared amplitude-amplification circuit for the prescribed rounds followed by an
inverse Fourier gate. -/
noncomputable def aqCircuit (N : ℕ) (hN : 0< N) (M : ℕ) : Circuit (Fin N) :=
  preparedAACircuit (QFTMatrix N) ⟨0,hN⟩ (aqRounds N M)++[Step.gate (QFTMatrix N)ᴴ]
/-- The output state of `aqCircuit` on the zero label with the phase oracle marking A. -/
noncomputable def aqState (N : ℕ) (hN : 0< N) (M : ℕ) (A : Finset (Fin N)) : QState (Fin N) :=
  Run (preparedMark A) (aqCircuit N hN M) (Ket ⟨0,hN⟩)

/-- Every term of a nonempty progression is below N when its last term is below N. -/
theorem aqProgression_index_lt (N s M P r : ℕ) (hM : 0 < M)
    (hbound : s+(M-1)*P < N) (hr : r < M) : s+r*P < N := by
  have hm : r ≤ M-1 := by omega
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right P hm) s).trans_lt hbound

/-- A nonempty positive-step progression contained in the domain has cardinality M. -/
theorem aqProgression_card (N s M P : ℕ) (hM : 0 < M) (hP : 0 < P)
    (hbound : s+(M-1)*P < N) : (aqProgressionSet N s M P).card=M := by
  let e : Fin M → Fin N :=
      fun r => ⟨s+r.val*P,aqProgression_index_lt N s M P r.val hM hbound r.isLt⟩
  have he : Function.Injective e := by
    intro r t h
    have hval : s+r.val*P=s+t.val*P := congrArg Fin.val h
    exact Fin.ext (mul_right_cancel₀ hP.ne' (Nat.add_left_cancel hval))
  have hset : aqProgressionSet N s M P = Finset.univ.image e := by
    ext x
    simp only [aqProgressionSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨r,hr,hx⟩
      exact ⟨⟨r,Finset.mem_range.mp hr⟩, Fin.ext hx.symm⟩
    · rintro ⟨r,hx⟩
      exact ⟨r.val, Finset.mem_range.mpr r.isLt, congrArg Fin.val hx.symm⟩
  rw [hset, Finset.card_image_of_injective _ he]
  simp

/-- The contained progression has cardinality M, and its amplified circuit is unitary with
normalized output, k queries, and 3k+2 gates for k = `aqRounds N M`. See [Cornwell2014]. -/
theorem amplified_progression_actual_circuit_and_counts : ∀ (N : ℕ) (hN : 0< N) (s M P : ℕ),
  0< M → 0< P → s+(M-1)*P< N → M< N →
  (aqProgressionSet N s M P).card= M ∧
  IsUnitaryCircuit (aqCircuit N hN M) ∧
  Normalized (aqState N hN M (aqProgressionSet N s M P)) ∧
  QueryCount (aqCircuit N hN M)= aqRounds N M ∧
  GateCount (aqCircuit N hN M)=3*aqRounds N M+2

 := by
  intro N hN s M P hM hP hbound hMN
  let A := aqProgressionSet N s M P
  have hqft := qftMatrix_unitary hN
  have hAA := prepared_aa_actual_circuit (QFTMatrix N) ⟨0,hN⟩ A (aqRounds N M) hqft
  have hInv := qftMatrix_conjTranspose_unitary N hN
  have hword : IsUnitaryCircuit (aqCircuit N hN M) := by
    rw [aqCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate]
    exact ⟨hAA.1,hInv,isUnitaryCircuit_nil⟩
  refine ⟨aqProgression_card N s M P hM hP hbound, hword, ?_, ?_, ?_⟩
  · exact hword.normalized_run (prepared_aa_reflection_and_access (QFTMatrix N) ⟨0,hN⟩ A hqft).1
      (normalized_ket _)
  · rw [aqCircuit, queryCount_append, hAA.2.1]
    simp
  · rw [aqCircuit, gateCount_append, hAA.2.2.1]
    simp

/-- The squared norm of the reciprocal square-root amplitude is 1/N. -/
theorem aq_uniform_entry_mass (N : ℕ) (_hN : 0 < N) :
    ‖(Real.sqrt (N:ℝ):ℂ)⁻¹‖^2 = 1/(N:ℝ) := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  simp only [one_div]

/-- The uniform prepared state's probability on A is |A|/N. -/
theorem aq_prepared_mass (N : ℕ) (hN : 0 < N) (A : Finset (Fin N)) :
    MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A = (A.card:ℝ)/(N:ℝ) := by
  rw [preparedAAState, qftMatrix_ket_zero N hN]
  simp only [MeasureProb, BornProb, aq_uniform_entry_mass N hN, Finset.sum_const,
    nsmul_eq_mul]
  ring

/-- Under 0 < M and 2M ≤ N, the Grover angle is in (0,π/4], has positive sine and cosine, and
satisfies sin²θ = M/N. -/
theorem aq_angle_properties (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : 2*M ≤ N) :
    0 < aqAngle N M ∧ aqAngle N M ≤ Real.pi/4 ∧ aqAngle N M < Real.pi/2 ∧
      (Real.sin (aqAngle N M))^2 = (M:ℝ)/(N:ℝ) ∧
      0 < Real.sin (aqAngle N M) ∧ 0 < Real.cos (aqAngle N M) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hp0 : (0:ℝ) < (M:ℝ)/(N:ℝ) := div_pos hMR hNR
  have hp : (M:ℝ)/(N:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hNR).mpr
    have h : 2*(M:ℝ) ≤ (N:ℝ) := by exact_mod_cast hMN
    linarith
  have hs1 : Real.sqrt ((M:ℝ)/(N:ℝ)) ≤ 1 := by
    calc
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (hp.trans (by norm_num))
      _ = 1 := Real.sqrt_one
  have hs4 : (Real.sin (Real.pi/4))^2 = (1/2:ℝ) := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hsq : Real.sqrt ((M:ℝ)/(N:ℝ)) ≤ Real.sin (Real.pi/4) := by
    exact Real.sqrt_le_iff.mpr ⟨(Real.sin_pos_of_pos_of_lt_pi (by positivity)
      (by linarith [Real.pi_pos])).le, hp.trans_eq hs4.symm⟩
  have htheta : 0 < aqAngle N M := Real.arcsin_pos.mpr (Real.sqrt_pos_of_pos hp0)
  have hquarter : aqAngle N M ≤ Real.pi/4 :=
    (Real.arcsin_le_iff_le_sin ⟨by linarith [Real.sqrt_nonneg ((M:ℝ)/(N:ℝ))],hs1⟩
      ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).mpr hsq
  have hhalf : aqAngle N M < Real.pi/2 := by linarith [Real.pi_pos]
  have hsin : (Real.sin (aqAngle N M))^2 = (M:ℝ)/(N:ℝ) := by
    rw [aqAngle, Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((M:ℝ)/(N:ℝ))]) hs1,
      Real.sq_sqrt hp0.le]
  exact ⟨htheta,hquarter,hhalf,hsin,Real.sin_pos_of_pos_of_lt_pi htheta (by linarith [Real.pi_pos]),
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hhalf⟩⟩

/-- For 0 < θ ≤ π/4 and k = ⌊π/(4θ)⌋, the gain sin²(2kθ) is positive, at most one, and at least
cos²(2θ). -/
theorem aq_floor_gain (theta : ℝ) (ht : 0 < theta) (hq : theta ≤ Real.pi/4) :
    let k := Nat.floor (Real.pi/(4*theta))
    0 < (Real.sin (2*(k:ℝ)*theta))^2 ∧
      (Real.cos (2*theta))^2 ≤ (Real.sin (2*(k:ℝ)*theta))^2 ∧
      (Real.sin (2*(k:ℝ)*theta))^2 ≤ 1 := by
  intro k
  have hdiv : 0 ≤ Real.pi/(4*theta) := by positivity
  have hle : (k:ℝ) ≤ Real.pi/(4*theta) := Nat.floor_le hdiv
  have hlt : Real.pi/(4*theta) < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk1 : (k:ℝ)*(4*theta) ≤ Real.pi := (le_div_iff₀ (by positivity)).mp hle
  have hk2 : Real.pi < ((k:ℝ)+1)*(4*theta) := (div_lt_iff₀ (by positivity)).mp hlt
  let t := Real.pi/2-2*(k:ℝ)*theta
  have ht0 : 0 ≤ t := by dsimp [t]; nlinarith
  have htt : t < 2*theta := by dsimp [t]; nlinarith
  have hthalf : t < Real.pi/2 := by linarith
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hthalf⟩
  have he : Real.sin (2*(k:ℝ)*theta) = Real.cos t := by
    dsimp only [t]
    rw [Real.cos_pi_div_two_sub]
  have hc0 : 0 ≤ Real.cos (2*theta) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],by linarith⟩
  have hc : Real.cos (2*theta) ≤ Real.cos t :=
    Real.cos_le_cos_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos]) htt.le
  have hs1 := Real.sin_sq_le_one (2*(k:ℝ)*theta)
  refine ⟨?_, ?_, hs1⟩
  · rw [he]
    positivity
  · rw [he]
    exact pow_le_pow_left₀ hc0 hc 2

/-- The inverse Fourier transform maps the prepared uniform state back to the zero basis state. -/
theorem aq_inverse_uniform (N : ℕ) (hN : 0 < N) :
    ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) = Ket ⟨0,hN⟩ := by
  have hu : (QFTMatrix N)ᴴ*QFTMatrix N=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using
        qftMatrix_unitary hN
  simp only [preparedAAState, ApplyGate, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

/-- The zero-frequency amplitude of the inverse Fourier transform of the restricted uniform
prepared state is |A|/N. -/
theorem aq_inverse_selected_zero (N : ℕ) (hN : 0 < N) (A : Finset (Fin N)) :
    ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) ⟨0,hN⟩ =
      ((A.card:ℝ)/(N:ℝ):ℂ) := by
  rw [preparedAAState, qftMatrix_ket_zero N hN]
  have hrow (x : Fin N) : ((QFTMatrix N)ᴴ) ⟨0,hN⟩ x = (Real.sqrt (N:ℝ):ℂ)⁻¹ := by
    simp [Matrix.conjTranspose_apply, qftMatrix_apply]
  simp only [ApplyGate, Matrix.mulVec, dotProduct, collapse_apply]
  simp only [hrow]
  have he (x : Fin N) : (Real.sqrt (N:ℝ):ℂ)⁻¹ *
      (if x ∈ A then (Real.sqrt (N:ℝ):ℂ)⁻¹ else 0) =
      if x ∈ A then (N:ℂ)⁻¹ else 0 := by
    by_cases hx : x ∈ A <;> simp [hx, inv_sqrt_mul_inv_sqrt hN]
  calc
    _ = ∑ x : Fin N, if x ∈ A then (N:ℂ)⁻¹ else 0 := Finset.sum_congr rfl (fun x hx => he x)
    _ = ∑ x ∈ A, (N:ℂ)⁻¹ := Finset.sum_ite_mem_eq A _
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Complex.ofReal_natCast]
      ring

/-- For a marked set of cardinality M satisfying positive half-density, the amplified state's
zero-frequency amplitude is cos(2kθ). -/
theorem aq_zero_amplitude (N : ℕ) (hN : 0 < N) (M : ℕ) (A : Finset (Fin N))
    (hcard : A.card=M) (hM : 0 < M) (hMN : 2*M ≤ N) :
    aqState N hN M A ⟨0,hN⟩ = (Real.cos (2*(aqRounds N M:ℝ)*aqAngle N M):ℂ) := by
  let theta := aqAngle N M
  let k := aqRounds N M
  have ht := aq_angle_properties N M hN hM hMN
  have hp : MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A = (Real.sin theta)^2 := by
    rw [aq_prepared_mass, hcard]
    exact ht.2.2.2.1.symm
  have hr := prepared_aa_actual_rotation (QFTMatrix N) ⟨0,hN⟩ A theta k (qftMatrix_unitary hN)
    ht.1 ht.2.2.1 hp
  have hc : Real.cos theta ≠ 0 := ht.2.2.2.2.2.ne'
  have hs : Real.sin theta ≠ 0 := ht.2.2.2.2.1.ne'
  rw [aqState, aqCircuit, run_append, run_gate, run_nil, hr]
  simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ((Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta:ℝ):ℂ)*
      (ApplyGate (QFTMatrix N)ᴴ (preparedAAState (QFTMatrix N) ⟨0,hN⟩) ⟨0,hN⟩ -
        ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) ⟨0,hN⟩) +
    ((Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta:ℝ):ℂ)*
      ApplyGate (QFTMatrix N)ᴴ (Collapse (preparedAAState (QFTMatrix N) ⟨0,hN⟩) A) ⟨0,hN⟩ = _
  rw [aq_inverse_uniform, aq_inverse_selected_zero, hcard]
  simp only [Ket, if_true]
  have hcos : (Real.cos theta)^2 = 1-(M:ℝ)/(N:ℝ) := by
    have ht1 := Real.sin_sq_add_cos_sq theta
    rw [ht.2.2.2.1] at ht1
    linarith
  have hsin : (Real.sin theta)^2 = (M:ℝ)/(N:ℝ) := ht.2.2.2.1
  have he : Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta*(1-(M:ℝ)/(N:ℝ)) +
      Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta*((M:ℝ)/(N:ℝ)) = Real.cos (2*(k:ℝ)*theta) := by
    rw [← hcos, ← hsin]
    have hbad : Real.cos ((2*(k:ℝ)+1)*theta)/Real.cos theta*(Real.cos theta)^2 =
        Real.cos ((2*(k:ℝ)+1)*theta)*Real.cos theta := by field_simp
    have hgood : Real.sin ((2*(k:ℝ)+1)*theta)/Real.sin theta*(Real.sin theta)^2 =
        Real.sin ((2*(k:ℝ)+1)*theta)*Real.sin theta := by field_simp
    rw [hbad, hgood, ← Real.cos_sub]
    congr 1
    ring
  exact_mod_cast he

/-- Gives the zero-frequency amplitude, positive gain bounds, the zero-frequency probability
bound 4(M/N)(1−M/N), and the additional gain lower bound 1−2M²/N; see [Cornwell2014]. -/
theorem amplified_progression_zero_mode_and_corrected_floor_bounds : ∀ (N : ℕ) (hN : 0< N) (s M P : ℕ),
  2≤ M → 0< P → s+(M-1)*P< N → 2*M≤ N →
  aqState N hN M (aqProgressionSet N s M P) ⟨0,hN⟩=
    (Real.cos (2*(aqRounds N M:ℝ)*aqAngle N M):ℂ) ∧
  0< aqGain N M ∧ (1-2*(M:ℝ)/(N:ℝ))^2≤ aqGain N M ∧ aqGain N M≤1 ∧
  BornProb (aqState N hN M (aqProgressionSet N s M P)) ⟨0,hN⟩≤
    4*(M:ℝ)/(N:ℝ)*(1-(M:ℝ)/(N:ℝ)) ∧
  1-2*(M:ℝ)^2/(N:ℝ)≤ aqGain N M

 := by
  intro N hN s M P hM hP hbound hMN
  have hMpos : 0 < M := by omega
  have ht := aq_angle_properties N M hN hMpos hMN
  have hg := aq_floor_gain (aqAngle N M) ht.1 ht.2.1
  have hcard := aqProgression_card N s M P hMpos hP hbound
  have hz := aq_zero_amplitude N hN M (aqProgressionSet N s M P) hcard hMpos hMN
  have hgain0 : 0 < aqGain N M := hg.1
  have hgain1 : aqGain N M ≤ 1 := hg.2.2
  have hc : Real.cos (2*aqAngle N M) = 1-2*(M:ℝ)/(N:ℝ) := by
    rw [Real.cos_two_mul]
    have h := Real.sin_sq_add_cos_sq (aqAngle N M)
    rw [ht.2.2.2.1] at h
    simp only [mul_div_assoc]
    linarith
  have hlower : (1-2*(M:ℝ)/(N:ℝ))^2 ≤ aqGain N M := by
    rw [← hc]
    exact hg.2.1
  have hzero : BornProb (aqState N hN M (aqProgressionSet N s M P)) ⟨0,hN⟩ ≤
      4*(M:ℝ)/(N:ℝ)*(1-(M:ℝ)/(N:ℝ)) := by
    rw [BornProb, hz, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h := Real.sin_sq_add_cos_sq (2*(aqRounds N M:ℝ)*aqAngle N M)
    change (1-2*(M:ℝ)/(N:ℝ))^2 ≤
      (Real.sin (2*(aqRounds N M:ℝ)*aqAngle N M))^2 at hlower
    simp only [mul_div_assoc] at hlower ⊢
    nlinarith
  have hloose : 1-2*(M:ℝ)^2/(N:ℝ) ≤ aqGain N M := by
    have hm : (2:ℝ) ≤ M := by exact_mod_cast hM
    have hp : 0 ≤ (M:ℝ)/(N:ℝ) := by positivity
    have hprod := mul_nonneg (show 0 ≤ (M:ℝ)-2 by linarith) hp
    have he : (M:ℝ)^2/(N:ℝ) = (M:ℝ)*((M:ℝ)/(N:ℝ)) := by ring
    rw [mul_div_assoc, he]
    simp only [mul_div_assoc] at hlower
    nlinarith
  exact ⟨hz,hgain0,hlower,hgain1,hzero,hloose⟩

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
