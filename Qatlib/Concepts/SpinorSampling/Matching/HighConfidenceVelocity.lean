/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.CorrelationExecution
import Qatlib.Concepts.SpinorSampling.Matching.LinearTargetExecution

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# High Confidence Velocity

High Confidence Velocity constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib
open Qatlib.Concepts.SpinorSampling.FiniteExecution.SplitResidual

/-- Construction for Velocity Data in the high confidence velocity model. -/
def VelocityData (S : Type) (current : CorrelationPlanQ) (cross : ℕ) (norm : TargetNormPlanQ) : Type :=
  CorrelationData S current.mode current.records current.blocks ×
    ((Fin cross → S × Bool) × TargetNormData S norm.mode norm.records norm.blocks)

instance {S : Type} [Fintype S] (current : CorrelationPlanQ) (cross : ℕ) (norm : TargetNormPlanQ) :
    Fintype (VelocityData S current cross norm) := by
  unfold VelocityData
  infer_instance

instance {S : Type} [DecidableEq S] (current : CorrelationPlanQ) (cross : ℕ) (norm : TargetNormPlanQ) :
    DecidableEq (VelocityData S current cross norm) := by
  unfold VelocityData
  infer_instance

variable {S : Type} [DecidableEq S]

/-- Construction for velocity Raw Output Q in the high confidence velocity model. -/
def velocityRawOutputQ [Fintype S] (current : CorrelationPlanQ) (cross : ℕ) (norm : TargetNormPlanQ)
    (M : ℕ) (u : S → ℚ) (α β : ℚ) (ω : VelocityData S current cross norm) : ℚ :=
  α^2*correlationOutputQ current.mode current.records current.blocks M id 0 ω.1+
    crossTargetOutputQ u α β ω.2.1+
    targetNormOutputQ norm.mode norm.records norm.blocks (fun x => (β*u x)^2) ω.2.2

noncomputable section
variable [Fintype S] [Nonempty S]

-- Fintype is required only by exact norm output and actual probability laws.
/-- The data still contains all three fresh groups even when an output skips. -/
def velocityRawLaw (current : CorrelationPlanQ) (cross : ℕ) (norm : TargetNormPlanQ)
    (m : S → ℝ) (hm : ∀ x, |m x|≤1) : FinDist (VelocityData S current cross norm) :=
  independentPairLaw (correlationLaw current.mode current.records current.blocks m hm)
    (independentPairLaw (cohortLaw (signedRecordLaw m hm) cross)
      (targetNormLaw norm.mode norm.records norm.blocks))

/-- Complete original `finite_bad_mass_positive_scale` guarantee for `HighConfidenceVelocity`; all source hypotheses and output obligations are retained. -/
theorem finite_bad_mass_positive_scale {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (f : X → ℝ) (c A ε : ℝ) (hA : 0<A) :
    finiteBadMass p (fun x => A*f x) (A*c) ε=finiteBadMass p f c (ε/A) := by
  unfold finiteBadMass
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← mul_sub,abs_mul,abs_of_pos hA,div_lt_iff₀ hA,mul_comm (|f x-c|) A]


-- Prove the finite union step over abstract record types. Keeping plan
-- constructors opaque here avoids normalizing their dependent data instances.
/-- Complete original `finite_three_sum_confidence` guarantee for `HighConfidenceVelocity`; all source hypotheses and output obligations are retained. -/
theorem finite_three_sum_confidence {X Y Z : Type}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (pC : FinDist X) (pL : FinDist Y) (pN : FinDist Z)
    (fC : X → ℝ) (fL : Y → ℝ) (fN : Z → ℝ) (cC cL cN ε ρ : ℝ)
    (hCB : finiteBadMass pC fC cC ε≤ρ) (hLB : finiteBadMass pL fL cL ε≤ρ)
    (hNB : finiteBadMass pN fN cN ε≤ρ) :
    finiteBadMass (independentPairLaw pC (independentPairLaw pL pN))
      (fun z => fC z.1+fL z.2.1+fN z.2.2) (cC+cL+cN) (3*ε)≤3*ρ := by
  let p := independentPairLaw pC (independentPairLaw pL pN)
  let f : Fin 3 → X × (Y × Z) → ℝ :=
    ![fun z => fC z.1, fun z => fL z.2.1, fun z => fN z.2.2]
  let centers : Fin 3 → ℝ := ![cC,cL,cN]
  have hpoint (z : X × (Y × Z))
      (h : ∀ i, |f i z-centers i|≤ε) :
      |fC z.1+fL z.2.1+fN z.2.2-(cC+cL+cN)|≤3*ε := by
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    change |fC z.1-cC|≤ε at h0
    change |fL z.2.1-cL|≤ε at h1
    change |fN z.2.2-cN|≤ε at h2
    calc
      _ = |((fC z.1-cC)+(fL z.2.1-cL))+(fN z.2.2-cN)| := by congr 1; ring
      _ ≤ |fC z.1-cC|+|fL z.2.1-cL|+|fN z.2.2-cN| :=
        (abs_add_le _ _).trans (by linarith [abs_add_le (fC z.1-cC) (fL z.2.1-cL)])
      _ ≤ _ := by linarith
  have hunion := finite_bad_mass_from_components p f centers (fun _ => ε)
    (fun z => fC z.1+fL z.2.1+fN z.2.2) (cC+cL+cN) (3*ε) hpoint
  have hm0 : finiteBadMass p (f 0) (centers 0) ε=finiteBadMass pC fC cC ε :=
    independent_pair_bad_mass_left _ _ _ _ _
  have hm1 : finiteBadMass p (f 1) (centers 1) ε=finiteBadMass pL fL cL ε := by
    change finiteBadMass (independentPairLaw pC (independentPairLaw pL pN))
      (fun z => fL z.2.1) cL ε=_
    rw [independent_pair_bad_mass_right pC (independentPairLaw pL pN)
      (fun z : Y × Z => fL z.1) cL ε,independent_pair_bad_mass_left pL pN fL cL ε]
  have hm2 : finiteBadMass p (f 2) (centers 2) ε=finiteBadMass pN fN cN ε := by
    change finiteBadMass (independentPairLaw pC (independentPairLaw pL pN))
      (fun z => fN z.2.2) cN ε=_
    rw [independent_pair_bad_mass_right pC (independentPairLaw pL pN)
      (fun z : Y × Z => fN z.2) cN ε,independent_pair_bad_mass_right pL pN fN cN ε]
  have hsum : (∑ i : Fin 3, finiteBadMass p (f i) (centers i) ε)≤3*ρ := by
    rw [Fin.sum_univ_three,hm0,hm1,hm2]
    linarith
  exact hunion.trans hsum


omit [DecidableEq S] [Nonempty S] in
/-- Complete original `split_velocity_center` guarantee for `HighConfidenceVelocity`; all source hypotheses and output obligations are retained. -/
theorem split_velocity_center (m : S → ℝ) (u : S → ℚ) (α β : ℚ) :
    (α : ℝ)^2*siteMean (fun x => (m x)^2)-
      2*(α : ℝ)*(β : ℝ)*siteMean (fun x => m x*(u x : ℝ))+
      targetSquare (β : ℝ) (fun x => (u x : ℝ))=
      siteMean (fun x => ((α : ℝ)*m x-(β : ℝ)*(u x : ℝ))^2) := by
  unfold siteMean targetSquare
  rw [← mul_div_assoc,← mul_div_assoc,div_sub_div_same,← add_div]
  congr 1
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Complete original `planned_velocity_raw_confidence` guarantee for `HighConfidenceVelocity`; all source hypotheses and output obligations are retained. -/
theorem planned_velocity_raw_confidence (m : S → ℝ) (hm : ∀ x, |m x|≤1)
    (u : S → ℚ) (α β U rootM ε ρ : ℚ) (hα : 0<α) (hβ : 0≤β) (hU : 0≤U)
    (hu : ∀ x, |u x|≤U) (hroot : Real.sqrt (Fintype.card S : ℝ)≤(rootM : ℝ))
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) :
    let current := correlationPlanQ (Fintype.card S) rootM (ε/α^2) ρ
    let cross := linearCountQ (2*α*β*U) ε ρ
    let norm := targetNormPlanQ (Fintype.card S) (β*U) ε ρ
    finiteBadMass (velocityRawLaw current cross norm m hm)
      (fun ω => (velocityRawOutputQ current cross norm (Fintype.card S) u α β ω : ℝ))
      (siteMean (fun x => ((α : ℝ)*m x-(β : ℝ)*(u x : ℝ))^2)) (3*(ε : ℝ))≤3*(ρ : ℝ) := by
  let current := correlationPlanQ (Fintype.card S) rootM (ε/α^2) ρ
  let cross := linearCountQ (2*α*β*U) ε ρ
  let norm := targetNormPlanQ (Fintype.card S) (β*U) ε ρ
  let pC := correlationLaw current.mode current.records current.blocks m hm
  let pL := cohortLaw (signedRecordLaw m hm) cross
  let pN : FinDist (TargetNormData S norm.mode norm.records norm.blocks) :=
    targetNormLaw norm.mode norm.records norm.blocks
  let p := independentPairLaw pC (independentPairLaw pL pN)
  let fC := fun z : CorrelationData S current.mode current.records current.blocks => (α : ℝ)^2*
    (correlationOutputQ current.mode current.records current.blocks (Fintype.card S) id 0 z : ℝ)
  let fL := fun z : Fin cross → S × Bool => (crossTargetOutputQ u α β z : ℝ)
  let fN := fun z : TargetNormData S norm.mode norm.records norm.blocks =>
    (targetNormOutputQ norm.mode norm.records norm.blocks (fun x => (β*u x)^2) z : ℝ)
  let cC := (α : ℝ)^2*siteMean (fun x => (m x)^2)
  let cL := -2*(α : ℝ)*(β : ℝ)*siteMean (fun x => m x*(u x : ℝ))
  let cN := targetSquare (β : ℝ) (fun x => (u x : ℝ))
  have hαR : (0 : ℝ)<α := Rat.cast_pos.mpr hα
  have hCB : finiteBadMass pC fC cC (ε : ℝ)≤(ρ : ℝ) := by
    rw [finite_bad_mass_positive_scale pC _ _ _ _ (sq_pos_of_pos hαR)]
    have ht := planned_current_correlation_confidence m hm rootM (ε/α^2) ρ hroot
      (by positivity) hρ hρ1
    simpa only [Rat.cast_div,Rat.cast_pow] using ht
  have hLB : finiteBadMass pL fL cL (ε : ℝ)≤(ρ : ℝ) :=
    planned_cross_target_confidence u α β U ε ρ m hm hα.le hβ hU hu hε hρ
  have hNB : finiteBadMass pN fN cN (ε : ℝ)≤(ρ : ℝ) :=
    planned_squared_target_norm_confidence u β U ε ρ hβ hu hε hρ
  have ht := finite_three_sum_confidence pC pL pN fC fL fN cC cL cN
    (ε : ℝ) (ρ : ℝ) hCB hLB hNB
  change finiteBadMass p
    (fun z => (velocityRawOutputQ current cross norm (Fintype.card S) u α β z : ℝ))
    (siteMean (fun x => ((α : ℝ)*m x-(β : ℝ)*(u x : ℝ))^2)) (3*(ε : ℝ))≤3*(ρ : ℝ)
  have hcenter : cC+cL+cN=siteMean (fun x => ((α : ℝ)*m x-(β : ℝ)*(u x : ℝ))^2) := by
    dsimp [cC,cL,cN]
    convert split_velocity_center m u α β using 1
    ring
  rw [hcenter] at ht
  simpa only [velocityRawOutputQ,Rat.cast_add,Rat.cast_mul,Rat.cast_pow] using ht

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finite_bad_mass_positive_scale
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.split_velocity_center
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_velocity_raw_confidence

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.finite_three_sum_confidence
