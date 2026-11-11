/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PairedPrior
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.WeakPromise

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Dense Overlap

The actual weak-spin overlap, before normalization by the original grid size.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Model.ConfidenceWeakSpin
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- The actual weak-spin overlap, before normalization by the original grid size. -/
theorem weak_spin_inner (b σ : ℝ) (hb0 : 0≤b) (hb1 : b≤1) :
    Inner (weakSpin b 1) (weakSpin b σ)=((1-b+b*σ : ℝ) : ℂ) := by
  rw [inner_apply]
  simp [weakSpin,←Complex.ofReal_mul,
    Real.mul_self_sqrt (by linarith : 0≤1-b)]
  push_cast
  have hs : ((Real.sqrt b : ℝ) : ℂ)^2=(b : ℂ) := by exact_mod_cast Real.sq_sqrt hb0
  linear_combination (σ : ℂ)*hs

/-- The literal normalized original supplied vectors have overlap one minus b for every balanced real sign field. -/
theorem supplied_inner {A : Type*} [Fintype A] [Nonempty A] (b : ℝ) (σ : A → ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (hσ : ∑ a,σ a=0) :
    Inner (fun z : A × Bool => suppliedSpinState (real0 (fun _ : A => weakSpin b 1))
      (imag0 (fun _ : A => weakSpin b 1)) (real1 (fun _ : A => weakSpin b 1))
      (imag1 (fun _ : A => weakSpin b 1)) z.2 z.1)
      (fun z : A × Bool => suppliedSpinState (real0 (fun a => weakSpin b (σ a)))
      (imag0 (fun a => weakSpin b (σ a))) (real1 (fun a => weakSpin b (σ a)))
      (imag1 (fun a => weakSpin b (σ a))) z.2 z.1)=((1-b : ℝ) : ℂ) := by
  let κ : ℂ := Real.sqrt (Fintype.card A : ℝ)
  have hκs : star κ=κ := by simp [κ]
  have hκsq : κ*κ=(Fintype.card A : ℂ) := by
    dsimp only [κ]
    rw [←Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp only [Complex.ofReal_natCast]
  have hm : (Fintype.card A : ℂ)≠0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card A≠0)
  rw [inner_apply,Fintype.sum_prod_type]
  simp only [suppliedSpinState,complexSpinor_parts]
  change (∑ a,∑ s,(starRingEnd ℂ) (weakSpin b 1 s/κ)*(weakSpin b (σ a) s/κ))=_
  have ht (a : A) (s : Bool) :
      (starRingEnd ℂ) (weakSpin b 1 s/κ)*(weakSpin b (σ a) s/κ)=
        ((starRingEnd ℂ) (weakSpin b 1 s)*weakSpin b (σ a) s)/(Fintype.card A : ℂ) := by
    change star (weakSpin b 1 s/κ)*(weakSpin b (σ a) s/κ)=_
    rw [star_div₀,hκs,div_mul_div_comm,hκsq]
    simp only [Complex.star_def]
  simp_rw [ht]
  simp_rw [←Finset.sum_div]
  have hi (a : A) : (∑ s,(starRingEnd ℂ) (weakSpin b 1 s)*weakSpin b (σ a) s)=
      ((1-b+b*σ a : ℝ) : ℂ) := weak_spin_inner b (σ a) hb0 hb1
  simp_rw [hi]
  push_cast
  rw [Finset.sum_add_distrib,Finset.sum_const,←Finset.mul_sum]
  have hz : (∑ a : A,(σ a : ℂ))=0 := by exact_mod_cast hσ
  rw [hz,mul_zero,add_zero]
  simp only [Finset.card_univ,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hm

/-- A shared zero local phase is literally the original pure input, with no measured or discarded registers. -/
theorem copies_zero {A : Type*} [Fintype A] (ψ : A → Bool → ℂ) (Q : ℕ)
    (x : Fin Q → A × Bool) :
    originalSuppliedCopies ψ Q (fun _ => 0) x=
      ∏ j,suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) (x j).2 (x j).1 := by
  simp only [originalSuppliedCopies,original_supplied_phase_factor,rootPhase]
  simp

/-- The full original Q-copy overlap is the Q-th power of the original single-copy overlap, including Q zero. -/
theorem original_copies_inner {A : Type*} [Fintype A] (ψ φ : A → Bool → ℂ) (Q : ℕ) :
    Inner (originalSuppliedCopies ψ Q (fun _ => 0)) (originalSuppliedCopies φ Q (fun _ => 0))=
      (Inner (fun z : A × Bool => suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) z.2 z.1)
        (fun z : A × Bool => suppliedSpinState (real0 φ) (imag0 φ) (real1 φ) (imag1 φ) z.2 z.1))^Q := by
  simp only [inner_apply,copies_zero,map_prod,←Finset.prod_mul_distrib]
  calc
    _ = ∏ _j : Fin Q,∑ z : A × Bool,
        (starRingEnd ℂ) (suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) z.2 z.1)*
          suppliedSpinState (real0 φ) (imag0 φ) (real1 φ) (imag1 φ) z.2 z.1 :=
      (Fintype.prod_sum (fun (_j : Fin Q) (z : A × Bool) =>
        (starRingEnd ℂ) (suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) z.2 z.1)*
          suppliedSpinState (real0 φ) (imag0 φ) (real1 φ) (imag1 φ) z.2 z.1)).symm
    _ = _ := by simp only [Fin.prod_const]

/-- The dense pair has exactly the source's complete Q-copy overlap on the original supplied input. -/
theorem dense_copies_inner {A : Type*} [Fintype A] [Nonempty A] (b : ℝ) (σ : A → ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (hσ : ∑ a,σ a=0) (Q : ℕ) :
    Inner (originalSuppliedCopies (fun _ : A => weakSpin b 1) Q (fun _ => 0))
      (originalSuppliedCopies (fun a => weakSpin b (σ a)) Q (fun _ => 0))=
        (((1-b)^Q : ℝ) : ℂ) := by
  rw [original_copies_inner,supplied_inner b σ hb0 hb1 hσ,Complex.ofReal_pow]


/-- The complete supplied-copy vector in a known finite basis, retaining every original input register. -/
def encodedCopies {A : Type*} [Fintype A] (ψ : A → Bool → ℂ) (Q : ℕ) :
    QState (Fin (Fintype.card (Fin Q → A × Bool))) :=
  fun i => originalSuppliedCopies ψ Q (fun _ => 0) ((Fintype.equivFin (Fin Q → A × Bool)).symm i)

/-- Known complete-basis relabeling preserves original Q-copy normalization. -/
theorem encodedCopies_normalized {A : Type*} [Fintype A] [Nonempty A]
    (ψ : A → Bool → ℂ) (hψ : ∀ a,qubitMass (ψ a)=1) (Q : ℕ) :
    Normalized (encodedCopies ψ Q) := by
  have h := originalSuppliedCopies_normalized ψ hψ Q (fun _ => 0)
  change (∑ i,‖originalSuppliedCopies ψ Q (fun _ => 0)
    ((Fintype.equivFin (Fin Q → A × Bool)).symm i)‖^2)=1
  exact (Equiv.sum_comp (Fintype.equivFin (Fin Q → A × Bool)).symm
    (fun x => ‖originalSuppliedCopies ψ Q (fun _ => 0) x‖^2)).trans h

/-- The complete known basis relabeling preserves the literal original inner product. -/
theorem encodedCopies_inner {A : Type*} [Fintype A] (ψ φ : A → Bool → ℂ) (Q : ℕ) :
    Inner (encodedCopies ψ Q) (encodedCopies φ Q)=
      Inner (originalSuppliedCopies ψ Q (fun _ => 0)) (originalSuppliedCopies φ Q (fun _ => 0)) := by
  simp only [inner_apply,encodedCopies]
  exact Equiv.sum_comp (Fintype.equivFin (Fin Q → A × Bool)).symm
    (fun x => (starRingEnd ℂ) (originalSuppliedCopies ψ Q (fun _ => 0) x)*
      originalSuppliedCopies φ Q (fun _ => 0) x)

/-- The actual weak sign fields have unit qubit mass, with no global Bloch constraint. -/
theorem weak_qubit_mass {A : Type*} (b : ℝ) (σ : A → ℝ) (hb0 : 0≤b) (hb1 : b≤1)
    (hσ : ∀ a,(σ a)^2=1) (a : A) : qubitMass (weakSpin b (σ a))=1 := by
  have h := weakSpin_normalized b (σ a) hb0 hb1 (hσ a)
  simp only [Normalized,Fintype.sum_bool,Complex.sq_norm] at h
  simpa only [qubitMass,Complex.normSq_apply,pow_two,add_assoc,add_comm,add_left_comm] using h

/-- The exact dense pure-state squared fidelity is proved for the actual complete original input at every maximum copy count. -/
theorem dense_full_fidelity {A : Type} [Fintype A] [Nonempty A] (b : ℝ) (σ : A → ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (hσ : ∀ a,(σ a)^2=1) (hmean : ∑ a,σ a=0) (Q : ℕ) :
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot
      (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (encodedCopies (fun _ : A => weakSpin b 1) Q))
      (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (encodedCopies (fun a => weakSpin b (σ a)) Q)))^2=
        (1-b)^(2*Q) := by
  let ψ := encodedCopies (fun _ : A => weakSpin b 1) Q
  let φ := encodedCopies (fun a => weakSpin b (σ a)) Q
  have hp : Normalized ψ := encodedCopies_normalized _ (weak_qubit_mass b (fun _ : A => 1) hb0 hb1 (by intro; norm_num)) Q
  have hq : Normalized φ := encodedCopies_normalized _ (weak_qubit_mass b σ hb0 hb1 hσ) Q
  have h := (Qatlib.Concepts.MixedFidelity.FidelityMetric.g1 _ _ _
    (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density hp)
    (Qatlib.Foundations.PureStateMath.BornBridge.outerProduct_density hq)).2.2.2.2.1 ψ φ hp hq
  change (Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot
    (Qatlib.Foundations.PureStateMath.Reflection.outerProduct ψ)
    (Qatlib.Foundations.PureStateMath.Reflection.outerProduct φ))^2=_
  rw [h]
  change ‖Inner (encodedCopies (fun _ : A => weakSpin b 1) Q)
    (encodedCopies (fun a => weakSpin b (σ a)) Q)‖^2=_
  rw [encodedCopies_inner,dense_copies_inner b σ hb0 hb1 hmean Q]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (by linarith : 0≤1-b) Q)]
  rw [←pow_mul]
  congr 1
  omega


end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
