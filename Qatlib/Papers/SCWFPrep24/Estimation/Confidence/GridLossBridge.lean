/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.FullLossNuisance
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap

set_option backward.isDefEq.respectTransparency false

/-!
# Grid Loss Bridge

The literal original physical field retains one sampled sign field and one sampled phase field.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridLossBridge
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.MatchingEnergy
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.DenseOverlap
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The literal original physical field retains one sampled sign field and one sampled phase field. -/
def physicalField {A E : Type*} (e : A ≃ E × Bool) (b : ℝ) (κ : E → Fin 4)
    (Q : ℕ) (ω : A → Fin (Q+1)) : A → Bool → ℂ :=
  sharedPhaseField (fun a => pairedWeakSpin b κ (e a)) Q ω

/-- Every member of the actual original phase/sign prior has the original pointwise four-coordinate normalization. -/
theorem physicalField_coordinate_mass {A E : Type*} (e : A ≃ E × Bool) (b : ℝ)
    (hb0 : 0≤b) (hb1 : b≤1) (κ : E → Fin 4) (Q : ℕ) (ω : A → Fin (Q+1)) (a : A) :
    (real0 (physicalField e b κ Q ω) a)^2+(imag0 (physicalField e b κ Q ω) a)^2+
      (real1 (physicalField e b κ Q ω) a)^2+(imag1 (physicalField e b κ Q ω) a)^2=1 := by
  have hp : qubitMass (pairedWeakSpin b κ (e a))=1 :=
    weak_qubit_mass b (siteSign κ) hb0 hb1 (siteSign_unit κ) (e a)
  have hr : Complex.normSq (rootPhase Q (ω a))=1 := by
    rw [Complex.normSq_eq_norm_sq,rootPhase_norm,one_pow]
  have hm : qubitMass (physicalField e b κ Q ω a)=1 := by
    simp only [qubitMass,physicalField,sharedPhaseField,Complex.normSq_mul,hr,one_mul]
    exact hp
  simpa only [qubitMass,real0,imag0,real1,imag1,Complex.normSq_apply,pow_two,add_assoc] using hm

/-- The complete actual Bell spin statistic is transported through a known full coordinate bijection; all physical phases cancel only inside Bell probabilities. -/
theorem physicalField_spin_energy {A E : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype E] [DecidableEq E] [Nonempty E] {d : ℕ}
    (e : A ≃ E × Bool) (u : Fin d → Equiv.Perm A) (τ : Fin d → Equiv.Perm (E × Bool))
    (hτ : ∀ j a,e (u j (u j a))=τ j (e a))
    (b G : ℝ) (κ : E → Fin 4) (Q : ℕ) (ω : A → Fin (Q+1)) :
    G*(∑ j : Fin d,bellMean (real0 (physicalField e b κ Q ω)) (imag0 (physicalField e b κ Q ω))
      (real1 (physicalField e b κ Q ω)) (imag1 (physicalField e b κ Q ω)) ((u j).trans (u j)))=
        spinEnergy b G τ κ := by
  have hr (a : A) : Complex.normSq (rootPhase Q (ω a))=1 := by
    rw [Complex.normSq_eq_norm_sq,rootPhase_norm,one_pow]
  have hj (j : Fin d) :
      bellMean (real0 (physicalField e b κ Q ω)) (imag0 (physicalField e b κ Q ω))
        (real1 (physicalField e b κ Q ω)) (imag1 (physicalField e b κ Q ω)) ((u j).trans (u j))=
          (∑ z : E × Bool,edgeBell b κ z (τ j z))/(Fintype.card (E × Bool) : ℝ) := by
    simp only [bellMean,populationMean,complexSpinor_parts,Fintype.card_congr e]
    congr 1
    calc
      _ = ∑ a : A,edgeBell b κ (e a) (τ j (e a)) := by
        apply Finset.sum_congr rfl
        intro a _
        change bellProbability (fun s => rootPhase Q (ω a)*pairedWeakSpin b κ (e a) s)
          (fun s => rootPhase Q (ω (u j (u j a)))*pairedWeakSpin b κ (e (u j (u j a))) s)=_
        rw [bell_local_phases _ _ _ _ (hr a) (hr (u j (u j a))),hτ]
        rfl
      _ = _ := Equiv.sum_comp e (fun z => edgeBell b κ z (τ j z))
  simp_rw [hj]
  rw [←Finset.sum_div]
  unfold spinEnergy
  ring

/-- Every actual phase/sign input has the full original loss within the original deterministic velocity nuisance of its same actual graph spin energy. -/
theorem physicalField_full_loss {A E : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    [Fintype E] [DecidableEq E] [Nonempty E] {d : ℕ}
    (e : A ≃ E × Bool) (u : Fin d → Equiv.Perm A) (τ : Fin d → Equiv.Perm (E × Bool))
    (hτ : ∀ j a,e (u j (u j a))=τ j (e a))
    (b : ℝ) (hb0 : 0≤b) (hb1 : b≤1) (κ : E → Fin 4) (Q : ℕ) (ω : A → Fin (Q+1))
    (h lam : ℝ) (hh : h≠0) :
    0≤ spinorDiscreteLoss (real0 (physicalField e b κ Q ω)) (imag0 (physicalField e b κ Q ω))
      (real1 (physicalField e b κ Q ω)) (imag1 (physicalField e b κ Q ω)) (fun _ _ => 0) u h 1 lam-
        spinEnergy b (2*lam^2/h^2) τ κ ∧
    spinorDiscreteLoss (real0 (physicalField e b κ Q ω)) (imag0 (physicalField e b κ Q ω))
      (real1 (physicalField e b κ Q ω)) (imag1 (physicalField e b κ Q ω)) (fun _ _ => 0) u h 1 lam-
        spinEnergy b (2*lam^2/h^2) τ κ≤(d : ℝ)/h^2 := by
  have hn := original_full_loss_velocity_nuisance
    (real0 (physicalField e b κ Q ω)) (imag0 (physicalField e b κ Q ω))
    (real1 (physicalField e b κ Q ω)) (imag1 (physicalField e b κ Q ω))
    (physicalField_coordinate_mass e b hb0 hb1 κ Q ω) u h lam hh
  rwa [physicalField_spin_energy e u τ hτ b (2*lam^2/h^2) κ Q ω] at hn

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridLossBridge
