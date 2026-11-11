/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressTrainedOriginal

set_option backward.isDefEq.respectTransparency false

/-!
Thin sequential control for the SCWF fresh-pilot/selected-word instrument.
Only past history and fresh pilot are independent. Main words may depend on
both. Updating a finite history preserves earlier coordinates; uniform
per-history endpoint bounds integrate without independent matchings.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.Schedule
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open RetainedSpin FiniteAxisWord UniformMatching
variable {H P E : Type} [Fintype H] [Fintype P] [Fintype E] [DecidableEq E] [Nonempty E]

/-- Only fresh pilot data is independent of past classical history. -/
def samples (p : FinDist H) (pilot : FinDist P) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : H → P → E → List Gate) (n : ℕ) :
    FinDist ((H × P) × (Fin n → GlobalRecord E)) :=
  TrainedMain.trainedLaw (independentPairLaw p pilot) u v hu hv (fun z => words z.1 z.2) n

/-- Complete original `samples_expect` guarantee for `PartialAddressAdaptive`; all source hypotheses and output obligations are retained. -/
theorem samples_expect (p : FinDist H) (pilot : FinDist P) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : H → P → E → List Gate) (n : ℕ)
    (f : ((H × P) × (Fin n → GlobalRecord E)) → ℝ) :
    (samples p pilot u v hu hv words n).expect f=
      p.expect (fun h => (TrainedMain.trainedLaw pilot u v hu hv (words h) n).expect
        (fun z => f ((h,z.1),z.2))) := by
  simp only [FinDist.expect,samples,TrainedMain.trainedLaw,independentPairLaw,Fintype.sum_prod_type,
    Finset.mul_sum,mul_assoc]

/-- Construction for step in the partial address adaptive model. -/
def step [DecidableEq H] (p : FinDist H) (pilot : FinDist P) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : H → P → E → List Gate) (n : ℕ)
    (update : H → P → (Fin n → GlobalRecord E) → H) : FinDist H :=
  PilotProjection.pushLaw (samples p pilot u v hu hv words n) (fun z => update z.1.1 z.1.2 z.2)

/-- Complete original `step_keep` guarantee for `PartialAddressAdaptive`; all source hypotheses and output obligations are retained. -/
theorem step_keep [DecidableEq H] (p : FinDist H) (pilot : FinDist P) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : H → P → E → List Gate) (n : ℕ)
    (update : H → P → (Fin n → GlobalRecord E) → H) (f : H → ℝ)
    (hkeep : ∀ h Ω ω,f (update h Ω ω)=f h) :
    (step p pilot u v hu hv words n update).expect f=p.expect f := by
  rw [step,PilotProjection.push_expect]
  have he : (samples p pilot u v hu hv words n).expect (fun z => f (update z.1.1 z.1.2 z.2))=
      (samples p pilot u v hu hv words n).expect (fun z => f z.1.1) := by
    apply congrArg (samples p pilot u v hu hv words n).expect
    funext z
    exact hkeep _ _ _
  rw [he,samples_expect]
  apply congrArg p.expect
  funext h
  unfold FinDist.expect
  dsimp only
  rw [← Finset.sum_mul,FinDist.sum_one,one_mul]

/-- Complete original `step_bound` guarantee for `PartialAddressAdaptive`; all source hypotheses and output obligations are retained. -/
theorem step_bound [DecidableEq H] (p : FinDist H) (pilot : FinDist P) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : H → P → E → List Gate) (n : ℕ)
    (update : H → P → (Fin n → GlobalRecord E) → H)
    (f : H → ℝ) (current : P × (Fin n → GlobalRecord E) → ℝ) (b : ℝ)
    (hcurrent : ∀ h Ω ω,f (update h Ω ω)=current (Ω,ω))
    (hbound : ∀ h,(TrainedMain.trainedLaw pilot u v hu hv (words h) n).expect current≤b) :
    (step p pilot u v hu hv words n update).expect f≤b := by
  rw [step,PilotProjection.push_expect,samples_expect]
  calc
    _ = p.expect (fun h => (TrainedMain.trainedLaw pilot u v hu hv (words h) n).expect current) := by
      apply congrArg p.expect
      funext h
      apply congrArg (TrainedMain.trainedLaw pilot u v hu hv (words h) n).expect
      funext z
      exact hcurrent _ _ _
    _ ≤ p.expect (fun _ => b) := finite_expect_mono p _ _ hbound
    _ = b := by
      unfold FinDist.expect
      rw [← Finset.sum_mul,p.sum_one,one_mul]

/-- Complete original `empty_words_expect` guarantee for `PartialAddressAdaptive`; all source hypotheses and output obligations are retained. -/
theorem empty_words_expect (pilot : FinDist P) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (n : ℕ) (f : (Fin n → GlobalRecord E) → ℝ) :
    (TrainedMain.trainedLaw pilot u v hu hv (fun _ _ => []) n).expect (fun z => f z.2)=
      ∑ ω : Fin n → GlobalRecord E,(UniformMatching.law u v hu hv).probOf ω*f ω := by
  simp only [FinDist.expect,TrainedMain.trainedLaw,Fintype.sum_prod_type,mul_assoc,
    ← Finset.mul_sum,TrainedMain.mainLaw]
  rw [← Finset.sum_mul,pilot.sum_one,one_mul]
  rfl

section Chain
variable {I X : Type} [Fintype X]

/-- Construction for run in the partial address adaptive model. -/
def run (transition : I → FinDist X → FinDist X) : List I → FinDist X → FinDist X
  | [],p => p
  | i::is,p => run transition is (transition i p)

/-- Complete original `run_preserves` guarantee for `PartialAddressAdaptive`; all source hypotheses and output obligations are retained. -/
theorem run_preserves (transition : I → FinDist X → FinDist X) (f : X → ℝ)
    (order : List I) (hkeep : ∀ i∈order,∀ p,(transition i p).expect f=p.expect f) (p : FinDist X) :
    (run transition order p).expect f=p.expect f := by
  induction order generalizing p with
  | nil => rfl
  | cons a rest ih =>
    rw [run,ih (by intro i hi; exact hkeep i (by simp [hi]))]
    exact hkeep a (by simp) p

/-- Complete original `run_bound` guarantee for `PartialAddressAdaptive`; all source hypotheses and output obligations are retained. -/
theorem run_bound [DecidableEq I] (transition : I → FinDist X → FinDist X)
    (f : I → X → ℝ) (b : I → ℝ)
    (hkeep : ∀ i j,i≠j → ∀ p,(transition j p).expect (f i)=p.expect (f i))
    (hnew : ∀ i p,(transition i p).expect (f i)≤b i)
    (order : List I) (i : I) (hi : i∈order) (p : FinDist X) :
    (run transition order p).expect (f i)≤b i := by
  induction order generalizing p with
  | nil => simp at hi
  | cons a rest ih =>
    rw [run]
    by_cases hrest : i∈rest
    · exact ih hrest (transition a p)
    · have hia : i=a := (List.mem_cons.mp hi).resolve_right hrest
      subst a
      rw [run_preserves transition (f i) rest (by
        intro j hj
        apply hkeep i j
        intro h
        subst j
        exact hrest hj)]
      exact hnew i p
end Chain

#print axioms samples
#print axioms samples_expect
#print axioms step
#print axioms step_keep
#print axioms step_bound
#print axioms empty_words_expect
#print axioms run
#print axioms run_preserves
#print axioms run_bound
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.Schedule
