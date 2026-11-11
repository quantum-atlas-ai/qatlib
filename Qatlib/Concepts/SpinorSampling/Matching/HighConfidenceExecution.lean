/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.HighConfidencePlan

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# High Confidence Execution

High Confidence Execution constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib

/-- Construction for High Confidence Data in the high confidence execution model. -/
def HighConfidenceData (S : Type) (d : ℕ) (p : HighConfidencePlanQ) : Type :=
  (Fin d → VelocityData S p.current p.crossRecords p.norm) ×
    (Fin 3 × Fin d → CorrelationData S p.spinSchedule.mode
      p.spinSchedule.records p.spinSchedule.blocks)

instance {S : Type} [Fintype S] (d : ℕ) (p : HighConfidencePlanQ) :
    Fintype (HighConfidenceData S d p) := by unfold HighConfidenceData; infer_instance

instance {S : Type} [DecidableEq S] (d : ℕ) (p : HighConfidencePlanQ) :
    DecidableEq (HighConfidenceData S d p) := by unfold HighConfidenceData; infer_instance

variable {S : Type} [Fintype S] [DecidableEq S]

/-- This is the literal clipped returned loss, including the no-spin branch. -/
def highConfidenceOutputQ {d : ℕ} (p : HighConfidencePlanQ) (u : Fin d → S → ℚ)
    (e : Fin d → S → S) (α β U γ : ℚ) (z : HighConfidenceData S d p) : ℚ :=
  let V := ∑ j : Fin d, intervalClipQ 0 ((α+β*U)^2)
    (velocityRawOutputQ p.current p.crossRecords p.norm (Fintype.card S) (u j) α β (z.1 j))
  if γ=0 then V else V+intervalClipQ 0 (2*(d : ℚ)*γ)
    (γ*((d : ℚ)-∑ i : Fin 3 × Fin d, correlationOutputQ
      p.spinSchedule.mode p.spinSchedule.records p.spinSchedule.blocks (Fintype.card S)
      (e i.2) (-1) (z.2 i)))

noncomputable section
variable [Nonempty S]

/-- Construction for high Confidence Law in the high confidence execution model. -/
def highConfidenceLaw {d : ℕ} (p : HighConfidencePlanQ)
    (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (ms : Fin 3 → S → ℝ) (hms : ∀ i x, |ms i x|≤1) :
    FinDist (HighConfidenceData S d p) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => velocityRawLaw p.current p.crossRecords p.norm (mv j) (hmv j)))
    (finiteFamilyLaw (fun i : Fin 3 × Fin d => correlationLaw p.spinSchedule.mode
      p.spinSchedule.records p.spinSchedule.blocks (ms i.1) (hms i.1)))

/-- Complete original `interval_clip_q_idempotent` guarantee for `HighConfidenceExecution`; all source hypotheses and output obligations are retained. -/
private theorem interval_clip_q_idempotent (lo hi x : ℚ) (h : lo≤hi) :
    intervalClipQ lo hi (intervalClipQ lo hi x)=intervalClipQ lo hi x := by
  have hlo : lo ≤ intervalClipQ lo hi x := le_min h (le_max_left _ _)
  have hhi : intervalClipQ lo hi x ≤ hi := min_le_left _ _
  exact (congrArg (min hi) (max_eq_right hlo)).trans (min_eq_right hhi)

omit [Fintype S] [Nonempty S] in
/-- Complete original `correlation_output_reclip` guarantee for `HighConfidenceExecution`; all source hypotheses and output obligations are retained. -/
theorem correlation_output_reclip (mode : CorrelationMode) (n K M : ℕ) (τ : S → S)
    (z : CorrelationData S mode n K) :
    intervalClipQ (-1) 1 (correlationOutputQ mode n K M τ (-1) z)=
      correlationOutputQ mode n K M τ (-1) z := by
  cases mode with
  | zero => norm_num [correlationOutputQ,intervalClipQ]
  | matched => exact interval_clip_q_idempotent _ _ _ (by norm_num)
  | matchedMedian => exact interval_clip_q_idempotent _ _ _ (by norm_num)
  | ustatisticMedian => exact interval_clip_q_idempotent _ _ _ (by norm_num)

omit [Nonempty S] in
/-- Complete original `high_confidence_output_cast` guarantee for `HighConfidenceExecution`; all source hypotheses and output obligations are retained. -/
theorem high_confidence_output_cast {d : ℕ} (p : HighConfidencePlanQ)
    (u : Fin d → S → ℚ) (e : Fin d → S → S) (α β U γ : ℚ)
    (z : HighConfidenceData S d p) :
    (highConfidenceOutputQ p u e α β U γ z : ℝ)=
      combinedLoss ((α : ℝ)+(β : ℝ)*(U : ℝ)) (γ : ℝ)
        (fun j => (velocityRawOutputQ p.current p.crossRecords p.norm (Fintype.card S)
          (u j) α β (z.1 j) : ℝ))
        (fun i => (correlationOutputQ p.spinSchedule.mode p.spinSchedule.records
          p.spinSchedule.blocks (Fintype.card S) (e i.2) (-1) (z.2 i) : ℝ)) := by
  have hq : highConfidenceOutputQ p u e α β U γ z=
      combinedLossQ (α+β*U) γ
        (fun j => velocityRawOutputQ p.current p.crossRecords p.norm (Fintype.card S)
          (u j) α β (z.1 j))
        (fun i => correlationOutputQ p.spinSchedule.mode p.spinSchedule.records
          p.spinSchedule.blocks (Fintype.card S) (e i.2) (-1) (z.2 i)) := by
    simp only [highConfidenceOutputQ,combinedLossQ,correlation_output_reclip]
  rw [hq,combined_loss_cast,Rat.cast_add,Rat.cast_mul]

/-- Complete original `high_confidence_accuracy` guarantee for `HighConfidenceExecution`; all source hypotheses and output obligations are retained. -/
theorem high_confidence_accuracy {d : ℕ} (hd : 0<d)
    (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (ms : Fin 3 → S → ℝ) (hs : ∀ x, ∑ a : Fin 3, (ms a x)^2=1)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (rootM α β U γ η δ : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hα : 0<α) (hβ : 0≤β) (hU : 0≤U) (hγ : 0≤γ)
    (hu : ∀ j x, |u j x|≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1) :
    let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
    finiteBadMass (highConfidenceLaw p mv hmv ms (fun i x => unit_spin_component_bound ms hs i x))
      (fun z => (highConfidenceOutputQ p u (fun j => e j) α β U γ z : ℝ))
      (implementedResidualLoss mv (fun j x => (u j x : ℝ)) ms e
        (α : ℝ) (β : ℝ) (γ : ℝ)) ((η : ℝ)/2)≤(δ : ℝ) := by
  let p := highConfidencePlanQ d (Fintype.card S) rootM α β U γ η δ
  let ε : ℚ := η/(8*(d : ℚ))
  let ρ : ℚ := δ/(4*(d : ℚ))
  let hms := fun i x => unit_spin_component_bound ms hs i x
  let pV := fun j : Fin d => velocityRawLaw p.current p.crossRecords p.norm (mv j) (hmv j)
  let pS := fun i : Fin 3 × Fin d => correlationLaw p.spinSchedule.mode
    p.spinSchedule.records p.spinSchedule.blocks (ms i.1) (hms i.1)
  let fV := fun (j : Fin d) (z : VelocityData S p.current p.crossRecords p.norm) =>
    (velocityRawOutputQ p.current p.crossRecords p.norm (Fintype.card S) (u j) α β z : ℝ)
  let fS := fun (i : Fin 3 × Fin d) (z : CorrelationData S p.spinSchedule.mode
      p.spinSchedule.records p.spinSchedule.blocks) =>
    (correlationOutputQ p.spinSchedule.mode p.spinSchedule.records p.spinSchedule.blocks
      (Fintype.card S) (e i.2) (-1) z : ℝ)
  let V := fun j : Fin d => siteMean (fun x => ((α : ℝ)*mv j x-(β : ℝ)*(u j x : ℝ))^2)
  let C := fun i : Fin 3 × Fin d => siteMean (fun x => ms i.1 x*ms i.1 (e i.2 x))
  have hdQ : (0 : ℚ)<d := by exact_mod_cast hd
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hε : 0<ε := by dsimp [ε]; positivity
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ<1 := by
    dsimp [ρ]
    apply (div_lt_one (by positivity : (0 : ℚ)<4*(d : ℚ))).mpr
    have hd1 : (1 : ℚ)≤d := by exact_mod_cast hd
    linarith
  have hVbad (j : Fin d) : finiteBadMass (pV j) (fV j) (V j) (3*(ε : ℝ))≤3*(ρ : ℝ) := by
    have ht := planned_velocity_raw_confidence (mv j) (hmv j) (u j) α β U rootM ε ρ
      hα hβ hU (hu j) hroot hε hρ hρ1
    exact ht
  have hVrange (j : Fin d) : 0≤V j ∧ V j≤((α : ℝ)+(β : ℝ)*(U : ℝ))^2 := by
    constructor
    · exact site_mean_nonneg _ (fun _ => sq_nonneg _)
    · exact residual_mean_bound (mv j) (fun x => (u j x : ℝ)) (α : ℝ) (β : ℝ) (U : ℝ)
        (hmv j) (fun x => by
          exact_mod_cast hu j x)
        (Rat.cast_nonneg.mpr hα.le) (Rat.cast_nonneg.mpr hβ)
  have hCrange (i : Fin 3 × Fin d) : -1≤C i ∧ C i≤1 :=
    abs_le.mp (spin_component_mean_range ms hs i.1 (e i.2))
  have hγR : (0 : ℝ)≤γ := Rat.cast_nonneg.mpr hγ
  change finiteBadMass (independentPairLaw (finiteFamilyLaw pV) (finiteFamilyLaw pS))
    (fun z => (highConfidenceOutputQ p u (fun j => e j) α β U γ z : ℝ))
    ((∑ j, V j)+(γ : ℝ)*((d : ℝ)-∑ i, C i)) ((η : ℝ)/2)≤(δ : ℝ)
  simp_rw [high_confidence_output_cast]
  by_cases hγ0 : γ=0
  · have hγ0R : (γ : ℝ)=0 := by exact_mod_cast hγ0
    simp only [hγ0R,combined_loss_zero,zero_mul,add_zero]
    rw [independent_pair_bad_mass_left (finiteFamilyLaw pV) (finiteFamilyLaw pS)
      (fun v : Fin d → VelocityData S p.current p.crossRecords p.norm =>
        ∑ j : Fin d, intervalClip 0 (((α : ℝ)+(β : ℝ)*(U : ℝ))^2) (fV j (v j)))
      (∑ j, V j) ((η : ℝ)/2)]
    have ht := velocity_only_confidence pV fV V ((α : ℝ)+(β : ℝ)*(U : ℝ))
      (3*(ε : ℝ)) (3*(ρ : ℝ)) hVrange hVbad
    have he : (d : ℝ)*(3*(ε : ℝ))≤(η : ℝ)/2 := by
      dsimp [ε]
      push_cast
      have heq : (d : ℝ) * (3 * ((η : ℝ) / (8 * (d : ℝ)))) = 3*(η : ℝ)/8 := by field_simp
      rw [heq]
      have hηR : (0 : ℝ)<η := Rat.cast_pos.mpr hη
      linarith
    have hf : (d : ℝ)*(3*(ρ : ℝ))≤(δ : ℝ) := by
      dsimp [ρ]
      push_cast
      have heq : (d : ℝ) * (3 * ((δ : ℝ) / (4 * (d : ℝ)))) = 3*(δ : ℝ)/4 := by field_simp
      rw [heq]
      have hδR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
      linarith
    exact (finite_bad_mass_mono_radius _ _ _ _ _ he).trans (ht.trans hf)
  · have hγpos : 0<γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
    let εs : ℚ := η/(24*(d : ℚ)*γ)
    let ρs : ℚ := δ/(12*(d : ℚ))
    have hεs : 0<εs := by dsimp [εs]; positivity
    have hρs : 0<ρs := by dsimp [ρs]; positivity
    have hρs1 : ρs<1 := by
      dsimp [ρs]
      apply (div_lt_one (by positivity : (0 : ℚ)<12*(d : ℚ))).mpr
      have hd1 : (1 : ℚ)≤d := by exact_mod_cast hd
      linarith
    have hspin := high_plan_spin_fields d (Fintype.card S) rootM α β U γ η δ hγ0
    have hSbad (i : Fin 3 × Fin d) : finiteBadMass (pS i) (fS i) (C i) (εs : ℝ)≤(ρs : ℝ) := by
      change finiteBadMass (correlationLaw p.spinSchedule.mode p.spinSchedule.records
        p.spinSchedule.blocks (ms i.1) (hms i.1))
        (fun z => (correlationOutputQ p.spinSchedule.mode p.spinSchedule.records
          p.spinSchedule.blocks (Fintype.card S) (e i.2) (-1) z : ℝ)) (C i) (εs : ℝ)≤(ρs : ℝ)
      rw [hspin]
      exact planned_spin_correlation_confidence (e i.2) (ms i.1) (hms i.1) rootM εs ρs
        hroot hεs hρs hρs1
    have hRrange := spin_total_mean_range ms hs (fun j => e j) (γ : ℝ) hγR
    have ht := combined_loss_confidence pV pS fV fS V C ((α : ℝ)+(β : ℝ)*(U : ℝ))
      (γ : ℝ) (3*(ε : ℝ)) (εs : ℝ) (3*(ρ : ℝ)) (ρs : ℝ) hγR
      hVrange hCrange hRrange hVbad hSbad
    have he : (d : ℝ)*(3*(ε : ℝ))+3*(d : ℝ)*(γ : ℝ)*(εs : ℝ)=(η : ℝ)/2 := by
      dsimp [ε,εs]
      push_cast
      have hγRp : (γ : ℝ)≠0 := by exact_mod_cast hγ0
      field_simp
      ring
    have hf : (d : ℝ)*(3*(ρ : ℝ))+3*(d : ℝ)*(ρs : ℝ)=(δ : ℝ) := by
      dsimp [ρ,ρs]
      push_cast
      field_simp
      ring
    rw [he,hf] at ht
    exact ht

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.correlation_output_reclip
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_confidence_output_cast
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.high_confidence_accuracy
