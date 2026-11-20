/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressAxisCertificate
public import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressCountMap

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
Selected finite spin words, actual main Born records, and a two-stage law.
Each training record (including any fixed earlier classical history) fixes
its words before fresh main preparations. The main law is proved from the
actual selected word, spin projection, and endpoint program on supplied
slices. The same sparse rational output keeps its Bell matching target.
No independence of word selection and pilot data is assumed. Connection to
the original grid/pilot and elimination of minority inputs is in TrainedOriginal.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TrainedMain
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open RetainedSpin FiniteAxisWord UniformMatching

/-- A common complex scalar on both input amplitudes factors through a single spin gate. -/
theorem spin_step_scale (g : Gate) (c : ℂ) (u : Bool → ℂ) :
    spinStep g (fun b => c*u b)=fun b => c*spinStep g u b := by
  funext b
  cases g <;> cases b <;> simp [spinStep] <;> ring

/-- Executing a finite spin word on a scaled input gives the scaled output of the word on the
original spinor. -/
theorem run_spin_scale (gs : List Gate) (c : ℂ) (u : Bool → ℂ) :
    runSpin gs (fun b => c*u b)=fun b => c*runSpin gs u b := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih => rw [runSpin,spin_step_scale,ih]; rfl

variable {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]

/-- Construction for rotated in the partial address trained main model. -/
def rotated (u : E → Bool → ℂ) (words : E → List Gate) : E → Bool → ℂ :=
  fun e => runSpin (words e) (u e)

omit [Fintype E] [DecidableEq E] [Nonempty E] in
/-- If the input spinor has unit mass at every edge, it remains unit mass at every edge after
its selected word. -/
theorem rotated_mass (u : E → Bool → ℂ) (words : E → List Gate)
    (hu : ∀ e,qubitMass (u e)=1) : ∀ e,qubitMass (rotated u words e)=1 := by
  intro e
  rw [rotated,run_spin_mass,hu]

-- Full supplied slice, then actual selected spin word, spin projection and
/-- actual endpoint program. No conditional-record law is supplied as an input. -/
def wordNativeProb (u v : E → Bool → ℂ) (words : E → List Gate)
    (z : GlobalRecord E) : ℝ :=
  BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (endpointProgram z.2.2.1)
    (spinProjection z.2.1
      (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) (program (words z.1))
        (fun x => supplied u v (z.1,x))))) (pairReg z.2.2.2 z.2.1)/3

omit [DecidableEq E] [Nonempty E] in
/-- The native record weight of executing the edge word before the spin projection and endpoint
measurement equals the native weight formed directly from the word-rotated endpoint spinors. -/
theorem word_native_prob (u v : E → Bool → ℂ) (words : E → List Gate)
    (z : GlobalRecord E) :
    wordNativeProb u v words z=nativeProb (rotated u words) (rotated v words) z := by
  unfold wordNativeProb
  rw [supplied_slice,program_edge_run,run_spin_scale,run_spin_scale,← edge_spin_filter]
  change actualProb (fun b => edgeScale (E:=E)*runSpin (words z.1) (u z.1) b)
    (fun b => edgeScale (E:=E)*runSpin (words z.1) (v z.1) b) z.2.1 z.2.2.1 z.2.2.2=_
  rw [actual_prob_scale,edge_scale_norm,native_prob_uniform]
  simp only [rotated]
  ring

/-- Construction for main Law in the partial address trained main model. -/
def mainLaw (u v : E → Bool → ℂ) (hu : ∀ e,qubitMass (u e)=1)
    (hv : ∀ e,qubitMass (v e)=1) (words : E → List Gate) : FinDist (GlobalRecord E) :=
  law (rotated u words) (rotated v words) (rotated_mass u words hu) (rotated_mass v words hv)

omit [DecidableEq E] in
/-- For unit endpoint spinors, every record probability under the main law equals the Born
weight of the native circuit with the selected edge word. -/
theorem main_law_native (u v : E → Bool → ℂ) (hu : ∀ e,qubitMass (u e)=1)
    (hv : ∀ e,qubitMass (v e)=1) (words : E → List Gate) (z : GlobalRecord E) :
    (mainLaw u v hu hv words).prob z=wordNativeProb u v words z := by
  rw [mainLaw,law_prob_native,word_native_prob]

omit [DecidableEq E] [Nonempty E] in
/-- Because both endpoints of each edge receive the same word, the average Bell target is
unchanged by edge-dependent spin rotations. -/
theorem main_target (u v : E → Bool → ℂ) (words : E → List Gate) :
    average (fun e => bellProbability (rotated u words e) (rotated v words e))=
      average (fun e => bellProbability (u e) (v e)) := by
  simp only [rotated,run_spin_bell]

variable {T : Type} [Fintype T]

-- Actual training records T determine every word before main preparations.
/-- The product below is conditional on that single fixed training record. -/
def trainedLaw (p : FinDist T) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : T → E → List Gate) (n : ℕ) : FinDist (T × (Fin n → GlobalRecord E)) where
  prob z := p.prob z.1*(mainLaw u v hu hv (words z.1)).probOf z.2
  nonneg z := mul_nonneg (p.nonneg _) (Finset.prod_nonneg fun i _ =>
    (mainLaw u v hu hv (words z.1)).nonneg (z.2 i))
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,FinDist.sum_probOf,mul_one]
    exact p.sum_one

omit [Fintype E] [DecidableEq E] [Nonempty E] [Fintype T] in
/-- A specified pilot and main cohort have joint probability equal to the pilot probability
times the product of native main record weights with the words fixed by that pilot. -/
theorem trained_law_native {E : Type} [_inst0 : Fintype E] [_inst1 : DecidableEq E]
    [_inst2 : Nonempty E] {T : Type} [_inst3 : Fintype T]
    (p : FinDist T) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : T → E → List Gate) (n : ℕ) (z : T × (Fin n → GlobalRecord E)) :
    (trainedLaw p u v hu hv words n).prob z=
      p.prob z.1*∏ i,wordNativeProb u v (words z.1) (z.2 i) := by
  simp only [trainedLaw,FinDist.probOf,main_law_native]

/-- For at least two main records, the sparse count estimator averaged over the pilot and the
conditional main cohort is unbiased for the original average edge Bell probability. -/
theorem trained_sparse_unbiased (p : FinDist T) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : T → E → List Gate) (n : ℕ) (hn : 2≤n) :
    (∑ z : T × (Fin n → GlobalRecord E),(trainedLaw p u v hu hv words n).prob z*
      (CountMap.sparseCountValueQ z.2 : ℝ))=
      average (fun e => bellProbability (u e) (v e)) := by
  rw [Fintype.sum_prod_type]
  simp only [trainedLaw,mul_assoc,← Finset.mul_sum]
  have hm (t : T) :
      (∑ ω : Fin n → GlobalRecord E,(mainLaw u v hu hv (words t)).probOf ω*
        (CountMap.sparseCountValueQ ω : ℝ))=
        average (fun e => bellProbability (u e) (v e)) := by
    simp only [CountMap.sparse_value_eq_ustatistic,mainLaw]
    rw [actual_global_unbiased _ _ _ _ hn,main_target]
  simp_rw [hm]
  rw [← Finset.sum_mul,p.sum_one,one_mul]

/-- The probability of a decidable event on `n` independent draws is the sum of the product
weights times its indicator. -/
theorem event_weighted {X : Type} [Fintype X] (p : FinDist X) (n : ℕ)
    (event : (Fin n → X) → Prop) [DecidablePred event] :
    p.probEvent event=∑ ω : Fin n → X,p.probOf ω*(if event ω then (1 : ℝ) else 0) := by
  classical
  simp only [FinDist.probEvent,Finset.sum_filter,mul_ite,mul_one,mul_zero]

/-- Every decidable event on a cohort of independent draws from a finite law has probability at
most one. -/
theorem event_le_one {X : Type} [Fintype X] (p : FinDist X) (n : ℕ)
    (event : (Fin n → X) → Prop) [DecidablePred event] : p.probEvent event≤1 := by
  classical
  rw [event_weighted]
  calc
    _ ≤ ∑ ω : Fin n → X,p.probOf ω := by
      apply Finset.sum_le_sum
      intro ω _
      have h : 0≤p.probOf ω := Finset.prod_nonneg fun i _ => p.nonneg (ω i)
      by_cases hω : event ω
      · simp [hω]
      · simpa [hω] using h
    _ = 1 := p.sum_probOf n

omit [Fintype E] [DecidableEq E] [Nonempty E] [Fintype T] in
/-- If bad pilot outcomes have probability at most `α` and each other pilot outcome gives
conditional main event probability at most a nonnegative `β`, the joint law gives the main
event probability at most `α+β`. -/
theorem trained_event_bound {E : Type} [_inst0 : Fintype E] [_inst1 : DecidableEq E]
    [_inst2 : Nonempty E] {T : Type} [_inst3 : Fintype T]
    (p : FinDist T) (u v : E → Bool → ℂ)
    (hu : ∀ e,qubitMass (u e)=1) (hv : ∀ e,qubitMass (v e)=1)
    (words : T → E → List Gate) (n : ℕ) (bad : T → Prop) [DecidablePred bad]
    (event : (Fin n → GlobalRecord E) → Prop) [DecidablePred event]
    (α β : ℝ) (hβ : 0≤β)
    (hpilot : p.expect (fun t => if bad t then (1 : ℝ) else 0)≤α)
    (hmain : ∀ t,¬bad t → (mainLaw u v hu hv (words t)).probEvent event≤β) :
    (trainedLaw p u v hu hv words n).expect
      (fun z => if event z.2 then (1 : ℝ) else 0)≤α+β := by
  classical
  have he : (trainedLaw p u v hu hv words n).expect
      (fun z => if event z.2 then (1 : ℝ) else 0)=
      p.expect (fun t => (mainLaw u v hu hv (words t)).probEvent event) := by
    simp only [FinDist.expect,trainedLaw,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum,
      event_weighted]
  rw [he]
  calc
    _ ≤ p.expect (fun t => (if bad t then (1 : ℝ) else 0)+β) := by
      apply finite_expect_mono
      intro t
      by_cases ht : bad t
      · simpa only [ite_eq_left ht] using (event_le_one (mainLaw u v hu hv (words t)) n event).trans
          (by linarith : (1 : ℝ)≤1+β)
      · simpa only [ite_eq_right ht,zero_add] using hmain t ht
    _ = p.expect (fun t => if bad t then (1 : ℝ) else 0)+β := by
      simp only [FinDist.expect,mul_add,Finset.sum_add_distrib,← Finset.sum_mul,p.sum_one,one_mul]
    _ ≤ α+β := by linarith

#print axioms spin_step_scale
#print axioms run_spin_scale
#print axioms rotated_mass
#print axioms word_native_prob
#print axioms main_law_native
#print axioms main_target
#print axioms trainedLaw
#print axioms trained_law_native
#print axioms trained_sparse_unbiased
#print axioms event_weighted
#print axioms event_le_one
#print axioms trained_event_bound
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TrainedMain
