/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AbelianDecoders.FourierSupport.SparseFourierSupport
public import Qatlib.Concepts.AmpTransform.ErrorStream.ConditionalAmplifiedNoiseConsumers
public import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedProgression

@[expose] public section

/-!
# Support transport for the amplified Fourier state

Chapter 4 of [Cornwell2014], Lemma 22 and Theorem 23, printed pp. 103-108, applies the
Donoho-Stark uncertainty principle to the marked indicator: if `A` is the marked set then the
support of the Fourier transform of its indicator has size at least `N / |A|`, so the number `Ny`
of retained frequencies times `|A|` is at least `N`.

This module transports that statement to the actual amplified circuit
`Qatlib.Concepts.AmpTransform.ErrorStream.conditionalAmplifiedQFTCircuit`: the indicator state of
`A` has support `A` and Fourier transform `(sqrt N)⁻¹` times
`Qatlib.Concepts.AmpTransform.ErrorStream.distinctNoiseFourier`, so
`Qatlib.Concepts.AbelianDecoders.FourierSupport.sparse_fourier_support_product` gives
`|A| * Ny >= N` for the number of nonzero Fourier coefficients; and at every nonzero frequency the
amplified amplitude vanishes exactly when the Fourier coefficient does, which identifies the
retained nonzero frequencies with the Fourier support. The zero frequency must be retained by
hand, and the round count must have a nonvanishing gain: at `k = 0` the circuit is a single
Fourier transform, whose nonzero-frequency amplitudes all vanish, so the literal inequality fails
without those guards. The printed `M * Ny >= N` application including its zero-mode bookkeeping is
therefore only proved here in the guarded form.

## Main statements

* `sparseFourierSupport_markedIndicator`: the support of the marked indicator is the marked set.
* `zmodQFT_markedIndicator`: its Fourier transform is `(sqrt N)⁻¹` times the marked Fourier sum.
* `marked_set_fourier_support_uncertainty`: `|A| * Ny >= N` for the number of nonzero Fourier
  coefficients of the marked indicator.
* `amplified_amplitude_ne_zero_iff`: at a nonzero frequency the amplified amplitude is nonzero
  exactly when the marked Fourier sum is.
* `support_lift_of_amplified_qft`: the guarded `|A| * Ny >= N` lift to the actual amplified state.

## References

* [Cornwell, 2014][Cornwell2014], Chapter 4, Lemma 22 and Theorem 23, printed pp. 103-108,
  [arXiv:1406.0190](https://arxiv.org/abs/1406.0190)
-/

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.SupportLift

open Qatlib.Concepts.AbelianDecoders.FourierSupport
open Qatlib.Concepts.AmpTransform.ErrorStream
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open scoped Classical BigOperators

attribute [local instance] Classical.propDecidable

/-- The indicator state of a marked set: amplitude one on `A` and zero elsewhere. -/
noncomputable def markedIndicator {N : ℕ} (A : Finset (ZMod N)) : QState (ZMod N) :=
  fun x => if x ∈ A then 1 else 0

/-- The marked indicator is nonzero exactly on the marked set. -/
theorem markedIndicator_ne_zero {N : ℕ} (A : Finset (ZMod N)) (x : ZMod N) :
    markedIndicator A x ≠ 0 ↔ x ∈ A := by
  unfold markedIndicator
  by_cases h : x ∈ A <;> simp [h]

/-- The support of the marked indicator is the marked set. -/
theorem sparseFourierSupport_markedIndicator {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    sparseFourierSupport (markedIndicator A) = A := by
  ext x
  rw [mem_sparseFourierSupport, markedIndicator_ne_zero]

/-- The nonnegative-size cast of a positive cardinality. -/
theorem card_cast_pos {N : ℕ} {A : Finset (ZMod N)} (hA : 0 < A.card) : (0 : ℝ) < (A.card : ℝ) := by
  exact_mod_cast hA

/-- The marked indicator is a nonzero state when the marked set is nonempty. -/
theorem markedIndicator_ne_zero_state {N : ℕ} {A : Finset (ZMod N)} (hA : A.Nonempty) :
    markedIndicator A ≠ 0 := by
  obtain ⟨x, hx⟩ := hA
  intro h
  have hx0 : markedIndicator A x = 0 := by rw [h]; rfl
  exact ((markedIndicator_ne_zero A x).mpr hx) hx0

/-- The Fourier transform of the marked indicator is the normalized marked Fourier sum. -/
theorem zmodQFT_markedIndicator {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (y : ZMod N) :
    zmodQFT (markedIndicator A) y =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ * distinctNoiseFourier A y := by
  rw [zmodQFT_apply, distinctNoiseFourier]
  have hterm : ∀ j : ZMod N, ZMod.stdAddChar (j * y) * markedIndicator A j =
      if j ∈ A then ZMod.stdAddChar (j * y) else 0 := by
    intro j
    unfold markedIndicator
    by_cases hj : j ∈ A <;> simp [hj]
  simp only [hterm, Finset.sum_ite_mem_eq]

/-- The marked Fourier sum at the zero frequency is the marked cardinality. -/
theorem distinctNoiseFourier_zero {N : ℕ} [NeZero N] (A : Finset (ZMod N)) :
    distinctNoiseFourier A 0 = (A.card : ℂ) := by
  rw [distinctNoiseFourier]
  simp only [mul_zero, AddChar.map_zero_eq_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Donoho-Stark for the marked set: the marked cardinality times the number of nonzero Fourier
coefficients is at least `N`. See [Cornwell2014], Chapter 4, Lemma 22. -/
theorem marked_set_fourier_support_uncertainty {N : ℕ} [NeZero N] (A : Finset (ZMod N))
    (hA : A.Nonempty) :
    A.card * (Finset.univ.filter (fun y : ZMod N => distinctNoiseFourier A y ≠ 0)).card ≥ N := by
  have hprod := sparse_fourier_support_product (markedIndicator A) (markedIndicator_ne_zero_state hA)
  rw [sparseFourierSupport_markedIndicator] at hprod
  have hsup : sparseFourierSupport (zmodQFT (markedIndicator A)) =
      Finset.univ.filter (fun y : ZMod N => distinctNoiseFourier A y ≠ 0) := by
    ext y
    rw [mem_sparseFourierSupport, zmodQFT_markedIndicator, mul_ne_zero_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hFne⟩ hy
      exact hFne hy
    · intro hFne
      refine ⟨?_, hFne⟩
      intro h0
      have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
      have hpos : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN
      have hz : ((Real.sqrt (N : ℝ) : ℂ)) = 0 := by simpa using h0
      exact absurd hz (Complex.ofReal_ne_zero.mpr hpos.ne')
  rw [hsup] at hprod
  exact hprod

/-- The conditional gain is nonzero exactly when the round count has a nonzero sine gain. -/
theorem conditionalAmplifiedGain_ne_zero_iff {k : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (hθp : θ < Real.pi / 2) :
    conditionalAmplifiedGain k θ ≠ 0 ↔ Real.sin (2 * (k : ℝ) * θ) ≠ 0 := by
  have hc : Real.cos θ ≠ 0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθp⟩).ne'
  have hs : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])).ne'
  have key : conditionalAmplifiedGain k θ
      = Real.sin (2 * (k : ℝ) * θ) / (Real.sin θ * Real.cos θ) := by
    have h := Real.sin_sub ((2 * (k : ℝ) + 1) * θ) θ
    have ha : (2 * (k : ℝ) + 1) * θ - θ = 2 * (k : ℝ) * θ := by ring
    rw [ha] at h
    unfold conditionalAmplifiedGain
    field_simp
    nlinarith only [h]
  rw [key, div_ne_zero_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, mul_ne_zero hs hc⟩⟩

/-- At a nonzero frequency the amplified amplitude is nonzero exactly when the marked Fourier sum
is nonzero, provided the round count has a nonvanishing gain. -/
theorem amplified_amplitude_ne_zero_iff {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (k : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθp : θ < Real.pi / 2)
    (hm : (Real.sin θ) ^ 2 = (A.card : ℝ) / N) (hgain : conditionalAmplifiedGain k θ ≠ 0)
    {y : ZMod N} (hy : y ≠ 0) :
    Run (preparedMark A) (conditionalAmplifiedQFTCircuit N k) (Ket 0) y ≠ 0 ↔
      distinctNoiseFourier A y ≠ 0 := by
  have hborn := conditional_amplified_qft_born N k A y θ hy hθ hθp hm
  have hkey : ‖Run (preparedMark A) (conditionalAmplifiedQFTCircuit N k) (Ket 0) y‖ ^ 2 =
      (conditionalAmplifiedGain k θ) ^ 2 / (N : ℝ) ^ 2 * ‖distinctNoiseFourier A y‖ ^ 2 := hborn
  have hcoef : (conditionalAmplifiedGain k θ) ^ 2 / (N : ℝ) ^ 2 ≠ 0 := by
    have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
    exact div_ne_zero (pow_ne_zero 2 hgain) (pow_ne_zero 2 hN.ne')
  constructor
  · intro hrun hF
    apply hrun
    have hzero : (conditionalAmplifiedGain k θ) ^ 2 / (N : ℝ) ^ 2
        * ‖distinctNoiseFourier A y‖ ^ 2 = 0 := by
      rw [hF]
      simp
    rw [← hkey] at hzero
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hzero)
  · intro hF hrun
    apply hF
    have hpos : 0 < ‖distinctNoiseFourier A y‖ ^ 2 := by
      have hne : ‖distinctNoiseFourier A y‖ ≠ 0 := norm_ne_zero_iff.mpr hF
      positivity
    have hcoefpos : 0 < (conditionalAmplifiedGain k θ) ^ 2 / (N : ℝ) ^ 2 := by
      have hg2 : 0 < (conditionalAmplifiedGain k θ) ^ 2 := by
        rcases lt_or_gt_of_ne (Ne.symm hgain) with h | h
        · nlinarith
        · nlinarith
      have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
      exact div_pos hg2 (by positivity)
    rw [hrun] at hkey
    have hzero : (0 : ℝ) = (conditionalAmplifiedGain k θ) ^ 2 / (N : ℝ) ^ 2
        * ‖distinctNoiseFourier A y‖ ^ 2 := by
      simpa using hkey
    exact absurd hzero.symm (ne_of_gt (mul_pos hcoefpos hpos))

/-- The guarded lift of the Donoho-Stark count to the actual amplified state: if the marked set is
nonempty, the gain does not vanish and the zero frequency is retained, then the marked cardinality
times the number of nonzero output amplitudes of the amplified circuit is at least `N`. See
[Cornwell2014], Chapter 4, printed pp. 106-108. -/
theorem support_lift_of_amplified_qft {N : ℕ} [NeZero N] (A : Finset (ZMod N)) (k : ℕ) (θ : ℝ)
    (hA : 0 < A.card) (hθ : 0 < θ) (hθp : θ < Real.pi / 2)
    (hm : (Real.sin θ) ^ 2 = (A.card : ℝ) / N) (hgain : conditionalAmplifiedGain k θ ≠ 0)
    (h0 : Run (preparedMark A) (conditionalAmplifiedQFTCircuit N k) (Ket 0) 0 ≠ 0) :
    A.card * (Finset.univ.filter (fun y : ZMod N =>
      Run (preparedMark A) (conditionalAmplifiedQFTCircuit N k) (Ket 0) y ≠ 0)).card ≥ N := by
  have hne : A.Nonempty := Finset.card_pos.mp hA
  have hunc := marked_set_fourier_support_uncertainty A hne
  have hsupp : Finset.univ.filter (fun y : ZMod N =>
        Run (preparedMark A) (conditionalAmplifiedQFTCircuit N k) (Ket 0) y ≠ 0) =
      Finset.univ.filter (fun y : ZMod N => distinctNoiseFourier A y ≠ 0) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hy : y = 0
    · subst hy
      constructor
      · intro _
        rw [distinctNoiseFourier_zero]
        exact_mod_cast hA.ne'
      · intro _
        exact h0
    · exact amplified_amplitude_ne_zero_iff A k θ hθ hθp hm hgain hy
  rw [hsupp]
  exact hunc

end Qatlib.Papers.AmpTransform14.SupportLift
