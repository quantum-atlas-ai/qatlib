/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.BernoulliFourCaseTransportStat
import Mathlib.Algebra.Field.GeomSum

/-!
# Fourier-case transport for Bernoulli error streams

This module proves `BernoulliErrorStreamFourCaseTransport` by evaluating the Fourier sum of a
nonwrapping planted progression as a geometric series. The result specializes actual conditional
amplified-QFT means to resonant, off-resonant, and vanishing-signal cases at nonzero frequency.

The theorem includes circuit costs, fixed-cardinality noise records, and the corresponding
Bernoulli mixture and disjoint-noise transport identities.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `bernoulliErrorStreamFourCaseTransport`: the full nonzero-frequency transport statement.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.QuditTeleport.TeleportCore

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.AmpTransform.ErrorStream

/-- A positive-step progression whose last site lies below `N` maps its index range injectively
into `ZMod N`. -/
private theorem progression_injective (N s M P : ℕ) [NeZero N]
    (hP : 0 < P) (hwrap : s + (M - 1) * P < N) :
    Set.InjOn (fun r : ℕ => (s + r * P : ZMod N)) (Finset.range M) := by
  intro r hr t ht heq
  have hrM := Finset.mem_range.mp hr
  have htM := Finset.mem_range.mp ht
  have hrN : s + r * P < N := lt_of_le_of_lt
    (Nat.add_le_add_left (Nat.mul_le_mul_right P (by omega)) s) hwrap
  have htN : s + t * P < N := lt_of_le_of_lt
    (Nat.add_le_add_left (Nat.mul_le_mul_right P (by omega)) s) hwrap
  have heq' : ((s + r * P : ℕ) : ZMod N) = ((s + t * P : ℕ) : ZMod N) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using heq
  have hh := congrArg ZMod.val heq'
  rw [ZMod.val_natCast_of_lt hrN, ZMod.val_natCast_of_lt htN] at hh
  exact Nat.eq_of_mul_eq_mul_right hP (Nat.add_left_cancel hh)

/-- The Fourier sum of a nonwrapping positive-step progression is its initial additive-character
phase times the geometric sum of the step character. -/
private theorem progression_fourier_sum (N s M P : ℕ) [NeZero N]
    (hP : 0 < P) (hwrap : s + (M - 1) * P < N) (y : ZMod N) :
    distinctNoiseFourier ((Finset.range M).image (fun r : ℕ => (s + r * P : ZMod N))) y =
      ZMod.stdAddChar ((s : ZMod N) * y) *
        ∑ r ∈ Finset.range M, (ZMod.stdAddChar ((P : ZMod N) * y)) ^ r := by
  unfold distinctNoiseFourier
  rw [Finset.sum_image (progression_injective N s M P hP hwrap), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [show (s + r * P : ZMod N) * y = (s : ZMod N) * y + r • ((P : ZMod N) * y) by
    simp only [nsmul_eq_mul]; ring]
  rw [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]

/-- The standard additive character on `ZMod N` equals one exactly at zero. -/
private theorem character_eq_one_iff (N : ℕ) [NeZero N] (z : ZMod N) :
    ZMod.stdAddChar z = 1 ↔ z = 0 := by
  rw [← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]

/-- A natural power of the standard additive character equals its value at the corresponding
natural multiple. -/
private theorem character_power (N : ℕ) [NeZero N] (z : ZMod N) (M : ℕ) :
    (ZMod.stdAddChar z) ^ M = ZMod.stdAddChar ((M : ZMod N) * z) := by
  simpa only [nsmul_eq_mul] using ((ZMod.stdAddChar (N := N)).map_nsmul_eq_pow M z).symm

/-- For `q ≠ 1`, the first `M` powers sum to `(1 - q ^ M) / (1 - q)`. -/
private theorem geometric_signal (q : ℂ) (hq : q ≠ 1) (M : ℕ) :
    (∑ r ∈ Finset.range M, q ^ r) = (1 - q ^ M) / (1 - q) := by
  rw [geom_sum_eq hq]
  simpa only [neg_sub] using (neg_div_neg_eq (q ^ M - 1) (q - 1)).symm

/-- Establish the nonzero-frequency conditional Born formulas, resonant and geometric branches,
vanishing-signal branch, and Bernoulli layer transport in
`BernoulliErrorStreamFourCaseTransport`; see [Cornwell, Section 3.4.4][Cornwell2014]. -/
theorem bernoulliErrorStreamFourCaseTransport : BernoulliErrorStreamFourCaseTransport := by
  intro N k _ p hp hp1 d hd s M P y θ hM hP hwrap hMN hy hθ A C w a p₂ g q mean
  have hinj := progression_injective N s M P hP hwrap
  have hA : A.card = M := by
    exact (Finset.card_image_of_injOn hinj).trans (Finset.card_range M)
  have hC : C.card = N - M := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simp only [Finset.card_univ, ZMod.card] at hh
    change C.card + A.card = N at hh
    omega
  have hθ' : ∀ L : ℕ, L < C.card → 0 < θ L ∧ θ L < Real.pi / 2 ∧
      (Real.sin (θ L)) ^ 2 = ((A.card + L : ℕ) : ℝ) / (N : ℝ) := by
    simpa only [hA, hC] using hθ
  have hCge : 2 ≤ C.card := by rw [hC]; omega
  have hApos : 0 < A.card := by omega
  have hexisting := bernoulli_noise_actual_amplified_qft N k p hp hp1 d hd A y θ
    hCge hApos hy hθ'
  rcases hexisting with ⟨hunit, hquery, hgate, hrecords, hlayer, _hmix, hraw⟩

  have hcross : (a * star (-a)).re = -Complex.normSq a := by
    rw [star_neg, mul_neg, Complex.star_def, Complex.mul_conj]
    simp
  have hmean (L : ℕ) (hL : L < C.card) :
      mean L = (g L) ^ 2 / (N : ℝ) ^ 2 *
        ((1 - 2 * (L : ℝ) / (C.card : ℝ) + p₂ L) * Complex.normSq a +
          L - p₂ L * (C.card : ℝ)) := by
    have hh := hlayer L hL
    rw [conditional_complement_fourier N A y hy] at hh
    change mean L = (conditionalAmplifiedGain k (θ L)) ^ 2 / (N : ℝ) ^ 2 *
      (‖a‖ ^ 2 + 2 * (L : ℝ) / C.card * (a * star (-a)).re + L +
        p₂ L * (‖-a‖ ^ 2 - (C.card : ℝ))) at hh
    simp only [norm_neg, ← Complex.normSq_eq_norm_sq, hcross] at hh
    rw [hh]
    dsimp only [g, conditionalAmplifiedGain]
    ring
  have hsignal : a = ZMod.stdAddChar ((s : ZMod N) * y) *
      ∑ r ∈ Finset.range M, q ^ r := progression_fourier_sum N s M P hP hwrap y
  have hnorm : Complex.normSq a = Complex.normSq (∑ r ∈ Finset.range M, q ^ r) := by
    rw [hsignal, Complex.normSq_eq_norm_sq, norm_mul, norm_stdAddChar, one_mul,
      Complex.normSq_eq_norm_sq]
  refine ⟨hA, hC, hunit, hquery, hgate, ?_, hmean, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hA] using hrecords
  · intro L hL hres
    have hq : q = 1 := by simp only [q, hres, AddChar.map_zero_eq_one]
    have hn : Complex.normSq a = (M : ℝ) ^ 2 := by
      rw [hnorm, hq]
      simp [Complex.normSq_eq_norm_sq]
    rw [hmean L hL, hn]
  · intro L hL hnon
    have hq : q ≠ 1 := by
      intro he
      have hz := (character_eq_one_iff N _).mp he
      exact hnon (by rw [hz, mul_zero])
    have hn : Complex.normSq a = Complex.normSq ((1 - q ^ M) / (1 - q)) := by
      rw [hnorm, geometric_signal q hq M]
    rw [hmean L hL, hn]
  · intro L hL hnon hann
    have hq : q ≠ 1 := fun he => hnon ((character_eq_one_iff N _).mp he)
    have hpow : q ^ M = 1 := by
      rw [character_power N _ M, hann, AddChar.map_zero_eq_one]
    have hn : Complex.normSq a = 0 := by
      rw [hnorm, geometric_signal q hq M, hpow]
      simp
    rw [hmean L hL, hn]
    ring
  · apply Finset.sum_congr rfl
    intro L hL
    rw [hmean L (Finset.mem_range.mp hL)]
  · simpa only [hA] using hraw

end Qatlib.Concepts.AmpTransform.ErrorStream
