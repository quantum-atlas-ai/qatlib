/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliZeroModeTransportStat

/-!
# Zero-mode transport for Bernoulli error streams

This module proves the zero-frequency counterpart of Bernoulli Fourier-case transport. The QFT
of the prepared uniform state and its marked restriction yields the exact Born probability `cos
(2 * k * θ) ^ 2` for `conditionalAmplifiedQFTCircuit` under the marked-density angle condition.

`bernoulliErrorStreamZeroModeTransport` combines this identity with progression cardinalities,
conditional noise means, binomial layer mixing, and the full disjoint-noise transport formula.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `bernoulliErrorStreamZeroModeTransport`: exact zero-mode probabilities and Bernoulli
  transport.

## References

* [Cornwell, 2014][Cornwell2014]
-/

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QuditTeleport.TeleportCore

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open Matrix
open scoped Classical BigOperators

/-- Every entry of the QFT-prepared state from `Ket 0` equals the inverse square root of `N`. -/
private theorem uniform_entry (N : ℕ) [NeZero N] (x : ZMod N) :
    preparedAAState (zmodQFTGate (N := N)) 0 x = (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by
  simp [preparedAAState, ApplyGate, Matrix.mulVec, dotProduct, Ket, zmodQFTGate_apply]

/-- The QFT-prepared uniform state assigns mass `S.card / N` to a finite set `S`. -/
private theorem uniform_mass (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    MeasureProb (preparedAAState (zmodQFTGate (N := N)) 0) S = (S.card : ℝ)/N := by
  simp only [MeasureProb, BornProb, uniform_entry, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), Finset.sum_const, nsmul_eq_mul]
  ring

/-- The QFT of the unnormalized restriction of the uniform state to `S` has amplitude `N⁻¹ *
distinctNoiseFourier S y` at `y`. -/
private theorem qft_selected (N : ℕ) [NeZero N]
    (S : Finset (ZMod N)) (y : ZMod N) :
    ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) S) y =
      (N : ℂ)⁻¹ * distinctNoiseFourier S y := by
  have hs : (Real.sqrt (N : ℝ) : ℂ)⁻¹ * (Real.sqrt (N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← pow_two, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  simp only [ApplyGate, Matrix.mulVec, dotProduct, zmodQFTGate_apply,
    collapse_apply, uniform_entry]
  have he (x : ZMod N) : (Real.sqrt (N : ℝ) : ℂ)⁻¹ * ZMod.stdAddChar (y*x) *
      (if x ∈ S then (Real.sqrt (N : ℝ) : ℂ)⁻¹ else 0) =
      if x ∈ S then (N : ℂ)⁻¹ * ZMod.stdAddChar (x*y) else 0 := by
    by_cases hx : x ∈ S
    · simp only [if_pos hx]
      rw [mul_right_comm, hs, mul_comm y x]
    · simp [hx]
  simp_rw [he]
  rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rfl

/-- At zero frequency, the QFT of the unnormalized uniform-state restriction to `S` has
amplitude `S.card / N`. -/
private theorem qft_selected_zero (N : ℕ) [NeZero N] (S : Finset (ZMod N)) :
    ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) S) 0 =
      (((S.card : ℝ)/N : ℝ) : ℂ) := by
  rw [qft_selected]
  simp only [distinctNoiseFourier, mul_zero, AddChar.map_zero_eq_one,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- Applying the QFT to the QFT-prepared uniform state gives amplitude one at zero frequency. -/
private theorem qft_uniform_zero (N : ℕ) [NeZero N] :
    ApplyGate zmodQFTGate (preparedAAState (zmodQFTGate (N := N)) 0) 0 = 1 := by
  have hc : Collapse (preparedAAState (zmodQFTGate (N := N)) 0) Finset.univ =
      preparedAAState (zmodQFTGate (N := N)) 0 := by
    ext x
    simp [collapse_apply]
  rw [← hc, qft_selected_zero]
  simp [ZMod.card, (NeZero.ne N)]

/-- For an angle in `(0, π / 2)` whose sine squared equals the marked density, the actual
amplified-QFT zero-mode Born probability is `cos (2 * k * θ) ^ 2`. -/
private theorem amplified_zero_born (N k : ℕ) [NeZero N]
    (B : Finset (ZMod N)) (θ : ℝ) (hθ : 0 < θ) (hθp : θ < Real.pi/2)
    (hm : (Real.sin θ)^2 = (B.card : ℝ)/N) :
    BornProb (Run (preparedMark B) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0 =
      (Real.cos (2*(k : ℝ)*θ))^2 := by
  have hr := prepared_aa_actual_rotation (zmodQFTGate (N := N)) 0 B θ k
    (zmodQFTGate_unitary (NeZero.pos N)) hθ hθp ((uniform_mass N B).trans hm.symm)
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩).ne'
  have hs : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have hcos : (Real.cos θ)^2 = 1 - (B.card : ℝ)/N := by
    have ht := Real.sin_sq_add_cos_sq θ
    rw [hm] at ht
    linarith
  have he : Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ*(1-(B.card : ℝ)/N) +
      Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ*((B.card : ℝ)/N) = Real.cos (2*(k : ℝ)*θ) := by
    rw [← hcos, ← hm]
    have hbad : Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ*(Real.cos θ)^2 =
        Real.cos ((2*(k : ℝ)+1)*θ)*Real.cos θ := by field_simp
    have hgood : Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ*(Real.sin θ)^2 =
        Real.sin ((2*(k : ℝ)+1)*θ)*Real.sin θ := by field_simp
    rw [hbad, hgood, ← Real.cos_sub]
    congr 1
    ring
  have ha : Run (preparedMark B) (conditionalAmplifiedQFTCircuit N k) (Ket 0) 0 =
      (Real.cos (2*(k : ℝ)*θ) : ℂ) := by
    rw [conditionalAmplifiedQFTCircuit, run_append, run_gate, run_nil, hr]
    simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    change ((Real.cos ((2*(k : ℝ)+1)*θ)/Real.cos θ : ℝ) : ℂ) *
        (ApplyGate zmodQFTGate (preparedAAState (zmodQFTGate (N := N)) 0) 0 -
          ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) B) 0) +
      ((Real.sin ((2*(k : ℝ)+1)*θ)/Real.sin θ : ℝ) : ℂ) *
        ApplyGate zmodQFTGate (Collapse (preparedAAState (zmodQFTGate (N := N)) 0) B) 0 = _
    rw [qft_uniform_zero, qft_selected_zero]
    exact_mod_cast he
  rw [BornProb, ha, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A positive-step progression with its last site below `N` has exactly `M` elements in `ZMod
N`. -/
private theorem progression_card (N s M P : ℕ) [NeZero N] (hP : 0 < P)
    (hbound : s+(M-1)*P < N) :
    ((Finset.range M).image (fun r : ℕ => (s+r*P : ZMod N))).card = M := by
  have hlabel (r : ℕ) (hr : r ∈ Finset.range M) : s+r*P < N := by
    have hr' : r ≤ M-1 := by have := Finset.mem_range.mp hr; omega
    exact (Nat.add_le_add_left (Nat.mul_le_mul_right P hr') s).trans_lt hbound
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro r hr t ht heq
  have h := congrArg ZMod.val heq
  simp only [← Nat.cast_add, ← Nat.cast_mul] at h
  rw [ZMod.val_natCast_of_lt (hlabel r hr), ZMod.val_natCast_of_lt (hlabel t ht)] at h
  exact mul_right_cancel₀ hP.ne' (Nat.add_left_cancel h)

/-- Establish the actual zero-mode Born identity, conditional layer means, circuit costs, and
Bernoulli complement transport in `BernoulliErrorStreamZeroModeTransport`; see [Cornwell,
Section 3.4.4][Cornwell2014]. -/
theorem bernoulliErrorStreamZeroModeTransport : BernoulliErrorStreamZeroModeTransport := by
  intro N k _ p _hp _hp1 d hd s M P θ _hM hP hbound _hMN hθ
  (try dsimp only)
  let A : Finset (ZMod N) := (Finset.range M).image (fun r : ℕ => (s+r*P : ZMod N))
  let C := Finset.univ \ A
  have hA : A.card = M := progression_card N s M P hP hbound
  have hcard : C.card+A.card = N := by
    simpa only [Finset.card_univ, ZMod.card] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hC : C.card = N-M := by omega
  have hU := zmodQFTGate_unitary (N := N) (NeZero.pos N)
  have hw := prepared_aa_actual_circuit (zmodQFTGate (N := N)) 0 A k hU
  have hsets : ∀ L : ℕ, L ≤ C.card → ∀ S ∈ C.powersetCard L,
      Disjoint A S ∧ (A ∪ S).card = M+L := by
    intro L _hL S hS
    simpa only [hA] using conditional_noise_record A S L hS
  have hrecord : ∀ L : ℕ, L < C.card → ∀ S ∈ C.powersetCard L,
      BornProb (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0 =
        (Real.cos (2*(k : ℝ)*θ L))^2 := by
    intro L hL S hS
    have ht := hθ L (by omega)
    apply amplified_zero_born N k (A ∪ S) (θ L) ht.1 ht.2.1
    rw [(hsets L hL.le S hS).2]
    exact ht.2.2
  have hmean (L : ℕ) (hL : L < C.card) :
      conditionalNoiseMean C L (fun S => BornProb
        (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0) =
        (Real.cos (2*(k : ℝ)*θ L))^2 := by
    rw [← conditionalNoiseMean_const C L hL.le ((Real.cos (2*(k : ℝ)*θ L))^2)]
    unfold conditionalNoiseMean
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    exact hrecord L hL S hS
  refine ⟨hA, hC, ?_, ?_, ?_, hsets, hrecord, hmean, ?_, ?_⟩
  · simp only [conditionalAmplifiedQFTCircuit, isUnitaryCircuit_append, isUnitaryCircuit_gate,
      isUnitaryCircuit_nil, and_true]
    exact ⟨hw.1, hU⟩
  · simp [conditionalAmplifiedQFTCircuit, queryCount_append, hw.2.1]
  · simp [conditionalAmplifiedQFTCircuit, gateCount_append, hw.2.2.1]
  · apply Finset.sum_congr rfl
    intro L hL
    exact congrArg ((C.card.choose L : ℝ)*p^L*(1-p)^(C.card-L) * ·)
      (hmean L (Finset.mem_range.mp hL))
  · simpa only [hA] using bernoulli_complement_transport N p d hd A
      (fun S => BornProb (Run (preparedMark (A ∪ S)) (conditionalAmplifiedQFTCircuit N k) (Ket 0)) 0)

end Qatlib.Concepts.AmpTransform.ErrorStream
