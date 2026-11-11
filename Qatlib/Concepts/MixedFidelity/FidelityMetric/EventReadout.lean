/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.EffectTesting
import Mathlib.MeasureTheory.VectorMeasure.Basic
import Mathlib.Tactic

open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection

/-!
# Event Readout

Positive normalized measurable-event effects with finite additivity form a class containing all countably additive quantum measurements.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder MatrixOrder

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open MeasureTheory

/-- Positive normalized measurable-event effects with finite additivity form a class containing all countably additive quantum measurements. -/
structure EventPOVM (D : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The actual positive operator associated with an output event. -/
  effect : Set Ω → Operator D
  /-- Measurable events have positive operators. -/
  positive : ∀ s,MeasurableSet s → (effect s).PosSemidef
  /-- The empty event has zero operator. -/
  empty : effect ∅=0
  /-- The full outcome event has the identity operator. -/
  total : effect Set.univ=1
  /-- Disjoint measurable events have additive operators. -/
  add : ∀ s t,MeasurableSet s → MeasurableSet t → Disjoint s t → effect (s ∪ t)=effect s+effect t

/-- A genuine countably additive positive operator-valued measure on the complete finite-dimensional quantum input. -/
structure CountablePOVM (D : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The actual sigma-additive matrix-valued measure, with no finite-outcome restriction. -/
  measure : VectorMeasure Ω (Operator D)
  /-- Every measurable event has positive operator mass. -/
  positive : ∀ s,MeasurableSet s → (measure s).PosSemidef
  /-- The actual complete quantum measurement is normalized. -/
  total : measure Set.univ=1

/-- Every genuine countably additive POVM embeds into the larger event model, with finite additivity derived from its sigma-additive vector measure. -/
def CountablePOVM.toEvent {D : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : CountablePOVM D Ω) : EventPOVM D Ω where
  effect := P.measure
  positive := P.positive
  empty := P.measure.empty
  total := P.total
  add _ _ hs ht hst := P.measure.of_union hst hs ht

/-- The positive complement of any genuine measurable output event is its actual complementary-event effect. -/
theorem EventPOVM.complement {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (s : Set Ω) (hs : MeasurableSet s) :
    P.effect sᶜ=1-P.effect s := by
  have h := P.add s sᶜ hs hs.compl disjoint_compl_right
  rw [Set.union_compl_self,P.total] at h
  rw [h]
  abel

/-- Every measurable output event has both a positive effect and a positive identity complement. -/
theorem EventPOVM.event_effects {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (s : Set Ω) (hs : MeasurableSet s) :
    (P.effect s).PosSemidef ∧ (1-P.effect s).PosSemidef := by
  exact ⟨P.positive s hs,by rw [←P.complement s hs]; exact P.positive sᶜ hs.compl⟩

/-- Finite sums of actual vector measures evaluate by summing their same event operators. -/
theorem vectorSum_apply {D : ℕ} {O : Type*} [Fintype O] {Ω : Type*} [MeasurableSpace Ω]
    (v : O → VectorMeasure Ω (Operator D)) (s : Set Ω) :
    (∑ o : O,v o) s=∑ o : O,v o s := by
  simp only [FunLike.coe_sum,Finset.sum_apply]

/-- A finite canonical POVM with arbitrary output scores is a genuine sigma-additive operator-valued measure on the output space. -/
def finiteReadout {D : ℕ} {O : Type} [Fintype O] {Ω : Type*} [MeasurableSpace Ω]
    (P : FinitePOVM O D) (score : O → Ω) : CountablePOVM D Ω where
  measure := ∑ o : O,VectorMeasure.dirac (score o) (P.effect o)
  positive s hs := by
    simp only [vectorSum_apply]
    apply Matrix.posSemidef_sum
    intro o _
    by_cases h : score o∈s
    · rw [VectorMeasure.dirac_apply_of_mem hs h]
      exact P.effect_posSemidef o
    · rw [VectorMeasure.dirac_apply_of_notMem h]
      exact Matrix.PosSemidef.zero
  total := by
    rw [vectorSum_apply]
    calc
      _ = ∑ o : O,P.effect o := by
        apply Finset.sum_congr rfl
        intro o _
        exact VectorMeasure.dirac_apply_of_mem MeasurableSet.univ (Set.mem_univ (score o))
      _ = 1 := P.effect_sum

/-- The genuine countably additive finite-output embedding returns exactly the original sum of actual effects in the chosen measurable score event. -/
theorem finiteReadout_event {D : ℕ} {O : Type} [Fintype O] {Ω : Type*} [MeasurableSpace Ω]
    (P : FinitePOVM O D) (score : O → Ω) (s : Set Ω) (hs : MeasurableSet s) :
    (finiteReadout P score).measure s=∑ o ∈ Finset.univ.filter (fun o => score o∈s),P.effect o := by
  simp only [finiteReadout,vectorSum_apply,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : score o∈s
  · simp only [ite_eq_left h,VectorMeasure.dirac_apply_of_mem hs h]
  · simp only [ite_eq_right h,VectorMeasure.dirac_apply_of_notMem h]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixedFidelity.FidelityMetric.EffectTesting

/-- The actual Born probability of a measurable output event against a complete quantum input. -/
def EventPOVM.born {D : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : EventPOVM D Ω)
    (A : Operator D) (s : Set Ω) : ℝ := (Matrix.trace (P.effect s*A)).re

/-- Positive measurable-event effects give actual nonnegative Born probabilities. -/
theorem EventPOVM.born_nonneg {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (A : Operator D) (hA : IsDensityOperator A) (s : Set Ω) (hs : MeasurableSet s) :
    0≤P.born A s := by
  have hp := P.event_effects s hs
  simpa only [EventPOVM.born,binaryOfEffect,ite_true] using
    povmBorn_nonneg (binaryOfEffect (P.effect s) hp.1 hp.2) A hA true

/-- The actual complementary measurable event has exactly the complementary Born probability. -/
theorem EventPOVM.born_complement {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (A : Operator D) (hA : IsDensityOperator A) (s : Set Ω) (hs : MeasurableSet s) :
    P.born A sᶜ=1-P.born A s := by
  simp only [EventPOVM.born,P.complement s hs,Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,hA.2,
    Complex.sub_re,Complex.one_re]

/-- A true complete measurable-event Born probability is at most one. -/
theorem EventPOVM.born_le_one {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (A : Operator D) (hA : IsDensityOperator A) (s : Set Ω) (hs : MeasurableSet s) :
    P.born A s≤1 := by
  have h := P.born_nonneg A hA sᶜ hs.compl
  rw [P.born_complement A hA s hs] at h
  linarith

/-- Actual Born probabilities are monotone on measurable events, from positivity and finite additivity of their real operators. -/
theorem EventPOVM.born_mono {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (A : Operator D) (hA : IsDensityOperator A) (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s⊆t) : P.born A s≤P.born A t := by
  have he := P.add s (t\s) hs (ht.diff hs) Set.disjoint_sdiff_right
  rw [Set.union_sdiff_cancel hst] at he
  have hn := P.born_nonneg A hA (t\s) (ht.diff hs)
  simp only [EventPOVM.born,he,Matrix.add_mul,Matrix.trace_add,Complex.add_re]
  exact le_add_of_nonneg_right hn

/-- Born event probabilities of an actual finite quantum mixture equal the same weighted probabilities of its actual complete component vectors. -/
theorem EventPOVM.born_mixture {D : ℕ} {Ω Z : Type*} [MeasurableSpace Ω] [Fintype Z]
    (P : EventPOVM D Ω) (w : Z → ℝ) (ψ : Z → QState (Fin D)) (s : Set Ω) :
    P.born (∑ z,(w z : ℂ) • outerProduct (ψ z)) s=∑ z,w z*P.born (outerProduct (ψ z)) s := by
  simp only [EventPOVM.born,Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
    smul_eq_mul,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- Every measurable event of an unrestricted event-valued quantum readout obeys the whole-input fidelity testing lower bound. -/
theorem EventPOVM.error_lower {D : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM D Ω) (A B : Operator D) (hA : IsDensityOperator A) (hB : IsDensityOperator B)
    (s : Set Ω) (hs : MeasurableSet s) :
    (Froot A B)^2/2≤P.born A s+P.born B sᶜ := by
  have hp := P.event_effects s hs
  simpa only [EventPOVM.born,P.complement s hs] using binary_error_lower (P.effect s) A B hp.1 hp.2 hA hB

/-- Arbitrary common finite-dimensional quantum processing, including any retained finite memory, preserves the same complete-input event-testing lower bound. -/
theorem EventPOVM.error_after_channel {D K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : EventPOVM K Ω) (T : QuantumChannel D K) (A B : Operator D)
    (hA : IsDensityOperator A) (hB : IsDensityOperator B) (s : Set Ω) (hs : MeasurableSet s) :
    (Froot A B)^2/2≤P.born (T.map A) s+P.born (T.map B) sᶜ := by
  have hlow := P.error_lower (T.map A) (T.map B) (T.preservesDensity hA) (T.preservesDensity hB) s hs
  have hm := (g3 D A B hA hB).2 K T
  have hn := (g1 D A B hA hB).2.1.1
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hn hm.2 2) (by norm_num)).trans hlow

end Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The actual real-output estimation failure event keeps the original absolute-error guarantee. -/
def estimationFailure (loss η : ℝ) : Set ℝ := {x | η < |x-loss|}

/-- The original absolute-error failure event is Borel measurable, without discretizing the real output. -/
theorem estimationFailure_measurable (loss η : ℝ) : MeasurableSet (estimationFailure loss η) :=
  (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet

/-- Born probabilities are linear on actual finite weighted quantum densities, also after common channels produce mixed component states. -/
theorem EventPOVM.born_weighted {D : ℕ} {Ω Z : Type*} [MeasurableSpace Ω] [Fintype Z]
    (P : EventPOVM D Ω) (w : Z → ℝ) (A : Z → Operator D) (s : Set Ω) :
    P.born (∑ z,(w z : ℂ) • A z) s=∑ z,w z*P.born (A z) s := by
  simp only [EventPOVM.born,Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
    smul_eq_mul,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- A real quantum readout's actual classification error on a physical prior is at most its uniform estimation risk plus that same prior's true bad-input mass. -/
theorem EventPOVM.prior_event_upper {D : ℕ} {Ω Z : Type*} [MeasurableSpace Ω] [Fintype Z] [DecidableEq Z]
    (P : EventPOVM D Ω) (p : FinDist Z) (A : Z → Operator D) (hA : ∀ z,IsDensityOperator (A z))
    (bad : Z → Prop) (c : Set Ω) (hc : MeasurableSet c) (failure : Z → Set Ω)
    (hfailure : ∀ z,MeasurableSet (failure z)) (δ : ℝ) (hδ : 0≤δ)
    (hrisk : ∀ z,P.born (A z) (failure z)≤δ)
    (hgood : ∀ z,¬bad z → c⊆failure z) :
    P.born (∑ z,(p.prob z : ℂ) • A z) c≤δ+∑ z ∈ Finset.univ.filter bad,p.prob z := by
  have hp (z : Z) : P.born (A z) c≤δ+(if bad z then 1 else 0) := by
    by_cases hb : bad z
    · rw [ite_eq_left hb]
      have h := P.born_le_one (A z) (hA z) c hc
      linarith
    · rw [ite_eq_right hb,add_zero]
      exact (P.born_mono (A z) (hA z) c (failure z) hc (hfailure z) (hgood z hb)).trans (hrisk z)
  rw [P.born_weighted]
  calc
    _ ≤ ∑ z,p.prob z*(δ+(if bad z then 1 else 0)) :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hp z) (p.nonneg z))
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,p.sum_one,one_mul,
        mul_ite,mul_one,mul_zero,Finset.sum_filter]

end Qatlib.Concepts.MixedFidelity.FidelityMetric.EventReadout
