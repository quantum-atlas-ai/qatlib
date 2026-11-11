/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellLowMean
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.SharedInput
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPair

set_option backward.isDefEq.respectTransparency false

/-!
# Weak Promise

The literal two weak spins have the exact original singlet probability.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The literal two weak spins have the exact original singlet probability. -/
theorem weakSpin_bell_exact (b σ τ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) :
    bellProbability (weakSpin b σ) (weakSpin b τ)=b*(1-b)*(τ-σ)^2/2 := by
  have hd : determinant (weakSpin b σ) (weakSpin b τ)=
      ((Real.sqrt (1-b)*Real.sqrt b*(τ-σ) : ℝ) : ℂ) := by
    simp only [determinant,weakSpin,Bool.false_eq_true,ite_false,ite_true]
    push_cast
    ring
  rw [bellProbability,hd,Complex.normSq_ofReal]
  rw [←pow_two,mul_pow,mul_pow,Real.sq_sqrt hb0,Real.sq_sqrt (by linarith : 0≤1-b)]
  ring

/-- Every actual fixed weak-sign pair obeys the original pointwise public Bell bound. -/
theorem weakSpin_bell_le (b σ τ : ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (hσ : σ^2=1) (hτ : τ^2=1) : bellProbability (weakSpin b σ) (weakSpin b τ)≤2*b := by
  rw [weakSpin_bell_exact b σ τ hb0 hb1]
  have hdiff : (τ-σ)^2≤4 := by nlinarith [sq_nonneg (τ+σ)]
  have h := mul_le_mul_of_nonneg_left hdiff (mul_nonneg hb0 (by linarith : 0≤1-b))
  nlinarith [sq_nonneg b]

/-- Arbitrary hidden local phases preserve the complete actual Bell probability. -/
theorem bell_local_phases (u v : Bool → ℂ) (z w : ℂ)
    (hz : Complex.normSq z=1) (hw : Complex.normSq w=1) :
    bellProbability (fun s => z*u s) (fun s => w*v s)=bellProbability u v := by
  have hd : determinant (fun s => z*u s) (fun s => w*v s)=z*w*determinant u v := by
    simp only [determinant]
    ring
  rw [bellProbability,hd,Complex.normSq_mul,Complex.normSq_mul,hz,hw,one_mul,one_mul]
  rfl

/-- Every weak shared-phase field obeys the public Bell bound on every known address map. -/
theorem original_weak_phase_bell_bound {A : Type} [Fintype A] [Nonempty A]
    (N Q : ℕ) (hN : 256≤N) (σ : A → ℝ) (hσ : ∀ a,(σ a)^2=1)
    (ω : A → Fin (Q+1)) (τ : A → A) :
    bellMean (real0 (sharedPhaseField (fun a => weakSpin (128/((N : ℝ)^2)) (σ a)) Q ω))
      (imag0 (sharedPhaseField (fun a => weakSpin (128/((N : ℝ)^2)) (σ a)) Q ω))
      (real1 (sharedPhaseField (fun a => weakSpin (128/((N : ℝ)^2)) (σ a)) Q ω))
      (imag1 (sharedPhaseField (fun a => weakSpin (128/((N : ℝ)^2)) (σ a)) Q ω)) τ≤256/((N : ℝ)^2) := by
  have hb := original_weak_excitation N hN
  have hr (k : Fin (Q+1)) : Complex.normSq (rootPhase Q k)=1 := by
    rw [Complex.normSq_eq_norm_sq,rootPhase_norm]
    norm_num
  unfold bellMean
  simp_rw [complexSpinor_parts]
  have hp (a : A) :
      bellProbability (sharedPhaseField (fun a => weakSpin (128/((N : ℝ)^2)) (σ a)) Q ω a)
        (sharedPhaseField (fun a => weakSpin (128/((N : ℝ)^2)) (σ a)) Q ω (τ a))≤
          256/((N : ℝ)^2) := by
    change bellProbability (fun s => rootPhase Q (ω a)*weakSpin (128/((N : ℝ)^2)) (σ a) s)
      (fun s => rootPhase Q (ω (τ a))*weakSpin (128/((N : ℝ)^2)) (σ (τ a)) s)≤256/((N : ℝ)^2)
    rw [bell_local_phases _ _ _ _ (hr _) (hr _)]
    have h := weakSpin_bell_le (128/((N : ℝ)^2)) (σ a) (σ (τ a)) hb.1 (by linarith) (hσ a) (hσ (τ a))
    convert h using 1
    ring
  unfold populationMean
  apply (div_le_iff₀ (by exact_mod_cast Fintype.card_pos : 0<(Fintype.card A : ℝ))).2
  calc _ ≤ ∑ _ : A,256/((N : ℝ)^2) := Finset.sum_le_sum (fun a _ => hp a)
       _ = _ := by simp [mul_comm]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence
