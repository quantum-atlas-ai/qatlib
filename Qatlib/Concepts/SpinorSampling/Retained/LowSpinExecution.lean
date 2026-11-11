/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinConfidence

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Execution

Low Spin Execution constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Construction for low Spin Failure in the low spin execution model. -/
private def lowSpinFailure {d : ℕ} (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (α β U γ η : ℚ)
    (p : LowSpinPlanQ) : ℝ :=
  finiteBadMass (lowSpinLaw p mv hmv a b c k hz e)
    (fun z => (lowSpinOutputQ p u e α β U γ z : ℝ))
    (implementedResidualLoss mv (fun j x => (u j x : ℝ)) (pauliField a b c k) e
      (α : ℝ) (β : ℝ) (γ : ℝ)) ((η : ℝ)/2)

-- The schedule is the literal production schedule. Neither success events
-- nor caller-selected integer budgets are premises of this endpoint.
/-- Complete original `low_spin_accuracy` guarantee for `LowSpinExecution`; all source hypotheses and output obligations are retained. -/
theorem low_spin_accuracy {d : ℕ} (hd : 0<d) (side : ℕ)
    (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (rootM α β U γ η δ p₀ : ℚ)
    (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hα : 0<α) (hβ : 0≤β) (hU : 0≤U) (hγ : 0≤γ)
    (hu : ∀ j x, |u j x|≤U) (hη : 0<η) (hδ : 0<δ) (hδ1 : δ<1)
    (hp : 0≤p₀) (hp1 : p₀≤1/2)
    (hmean : γ≠0 → ∀ j,bellMean a b c k (e j)≤(p₀ : ℝ))
    (hidentity : side≤2 → ∀ j,e j=Equiv.refl S) :
    let p := lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀
    finiteBadMass (lowSpinLaw p mv hmv a b c k hz e)
      (fun z => (lowSpinOutputQ p u e α β U γ z : ℝ))
      (implementedResidualLoss mv (fun j x => (u j x : ℝ)) (pauliField a b c k) e
        (α : ℝ) (β : ℝ) (γ : ℝ)) ((η : ℝ)/2)≤(δ : ℝ) := by
  let pV := highConfidencePlanQ d (Fintype.card S) rootM α β U 0 η δ
  let ε : ℚ := η/(8*(d : ℚ))
  let ρ : ℚ := δ/(4*(d : ℚ))
  let lawV := fun j : Fin d => velocityRawLaw pV.current pV.crossRecords pV.norm (mv j) (hmv j)
  let fV := fun (j : Fin d) (z : VelocityData S pV.current pV.crossRecords pV.norm) =>
    (velocityRawOutputQ pV.current pV.crossRecords pV.norm (Fintype.card S) (u j) α β z : ℝ)
  let V := fun j : Fin d => siteMean (fun x => ((α : ℝ)*mv j x-(β : ℝ)*(u j x : ℝ))^2)
  have hdQ : (0 : ℚ)<d := by exact_mod_cast hd
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hηR : (0 : ℝ)<η := Rat.cast_pos.mpr hη
  have hδR : (0 : ℝ)<δ := Rat.cast_pos.mpr hδ
  have hε : 0<ε := by dsimp [ε]; positivity
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ<1 := by
    dsimp [ρ]
    apply (div_lt_one (by positivity : (0 : ℚ)<4*(d : ℚ))).mpr
    have hd1 : (1 : ℚ)≤d := by exact_mod_cast hd
    linarith
  have hVbad (j : Fin d) : finiteBadMass (lawV j) (fV j) (V j) (3*(ε : ℝ))≤3*(ρ : ℝ) :=
    planned_velocity_raw_confidence (mv j) (hmv j) (u j) α β U rootM ε ρ
      hα hβ hU (hu j) hroot hε hρ hρ1
  have hVrange (j : Fin d) : 0≤V j ∧ V j≤((α : ℝ)+(β : ℝ)*(U : ℝ))^2 := by
    constructor
    · exact site_mean_nonneg _ (fun _ => sq_nonneg _)
    · exact residual_mean_bound (mv j) (fun x => (u j x : ℝ)) (α : ℝ) (β : ℝ) (U : ℝ)
        (hmv j) (fun x => by
          exact_mod_cast hu j x)
        (Rat.cast_nonneg.mpr hα.le) (Rat.cast_nonneg.mpr hβ)
  change lowSpinFailure mv hmv a b c k hz u e α β U γ η
    (lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀)≤(δ : ℝ)
  by_cases hγ0 : γ=0
  · have hplan : lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀=
        ⟨pV,none,pV.copies,pV.targetQueries⟩ := by
      simp only [lowSpinPlanQ,ite_eq_left hγ0,add_zero]
      rfl
    rw [hplan]
    unfold lowSpinFailure
    simp_rw [low_spin_output_cast_none]
    rw [implemented_loss_bell_form mv (fun j x => (u j x : ℝ)) a b c k hz e]
    have hγ0R : (γ : ℝ)=0 := by exact_mod_cast hγ0
    simp only [hγ0R,zero_mul,mul_zero,add_zero]
    change finiteBadMass (independentPairLaw (finiteFamilyLaw lawV)
      (lowSpinBellLaw a b c k hz e none))
      (fun z => ∑ j : Fin d,intervalClip 0 (((α : ℝ)+(β : ℝ)*(U : ℝ))^2) (fV j (z.1 j)))
      (∑ j,V j) ((η : ℝ)/2)≤(δ : ℝ)
    rw [independent_pair_bad_mass_left (finiteFamilyLaw lawV) (lowSpinBellLaw a b c k hz e none)
      (fun z => ∑ j : Fin d,intervalClip 0 (((α : ℝ)+(β : ℝ)*(U : ℝ))^2) (fV j (z j)))
      (∑ j,V j) ((η : ℝ)/2)]
    have ht := velocity_only_confidence lawV fV V ((α : ℝ)+(β : ℝ)*(U : ℝ))
      (3*(ε : ℝ)) (3*(ρ : ℝ)) hVrange hVbad
    have he : (d : ℝ)*(3*(ε : ℝ))≤(η : ℝ)/2 := by
      dsimp [ε]
      push_cast
      have heq : (d : ℝ)*(3*((η : ℝ)/(8*(d : ℝ))))=3*(η : ℝ)/8 := by field_simp
      rw [heq]
      linarith
    have hf : (d : ℝ)*(3*(ρ : ℝ))≤(δ : ℝ) := by
      dsimp [ρ]
      push_cast
      have heq : (d : ℝ)*(3*((δ : ℝ)/(4*(d : ℝ))))=3*(δ : ℝ)/4 := by field_simp
      rw [heq]
      linarith
    exact (finite_bad_mass_mono_radius _ _ _ _ _ he).trans (ht.trans hf)
  · have hγpos : 0<γ := lt_of_le_of_ne hγ (Ne.symm hγ0)
    let εb : ℚ := η/(32*(d : ℚ)*γ)
    let q := bellPlanQ side (Fintype.card S) p₀ εb ρ
    have hεb : 0<εb := by dsimp [εb]; positivity
    have hplan : lowSpinPlanQ side d (Fintype.card S) rootM α β U γ η δ p₀=
        ⟨pV,some q,pV.copies+d*q.copies,pV.targetQueries⟩ := by
      simp only [lowSpinPlanQ,ite_eq_right hγ0]
      rfl
    rw [hplan]
    unfold lowSpinFailure
    have hBbad (j : Fin d) : finiteBadMass
        (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz (e j) q.blocks)
        (fun ω => ((executePlannedBellQ q (e j) ω).value : ℝ))
        (bellMean a b c k (e j)) (εb : ℝ)≤(ρ : ℝ) := by
      rw [← finite_bad_indicator_mean]
      exact bell_plan_confidence side a b c k hz (e j) p₀ εb ρ hp hp1 hεb hρ hρ1
        (hmean hγ0 j) (fun hside => hidentity hside j)
    have ht := low_spin_some_confidence pV q (pV.copies+d*q.copies) pV.targetQueries
      mv hmv a b c k hz u e α β U γ (3*(ε : ℝ)) (εb : ℝ) (3*(ρ : ℝ)) (ρ : ℝ)
      (Rat.cast_nonneg.mpr hγ) hVrange hVbad hBbad
    have he : (d : ℝ)*(3*(ε : ℝ))+4*(γ : ℝ)*(d : ℝ)*(εb : ℝ)=(η : ℝ)/2 := by
      dsimp [ε,εb]
      push_cast
      have hγR : (γ : ℝ)≠0 := by exact_mod_cast hγ0
      field_simp
      ring
    have hf : (d : ℝ)*(3*(ρ : ℝ))+(d : ℝ)*(ρ : ℝ)=(δ : ℝ) := by
      dsimp [ρ]
      push_cast
      field_simp
      ring
    rw [he,hf] at ht
    exact ht

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_accuracy
