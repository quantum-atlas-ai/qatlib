/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinProbability
import Qatlib.Concepts.SpinorSampling.Retained.LowSpinComposition

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Confidence

Low Spin Confidence constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ}

-- Union bound on the actual joint data. The Bell marginal uses a dependent
-- product: its matching carrier differs with the direction.
/-- Complete original `low_spin_some_confidence` guarantee for `LowSpinConfidence`; all source hypotheses and output obligations are retained. -/
theorem low_spin_some_confidence (pV : HighConfidencePlanQ) (q : BellPlanQ)
    (copies queries : ℕ) (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x|≤1)
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → S → ℚ) (e : Fin d → Equiv.Perm S) (α β U γ : ℚ)
    (εv εb ρv ρb : ℝ) (hγ : 0≤(γ : ℝ))
    (hVrange : ∀ j,0 ≤ siteMean (fun x => ((α : ℝ)*mv j x-(β : ℝ)*(u j x : ℝ))^2) ∧
      siteMean (fun x => ((α : ℝ)*mv j x-(β : ℝ)*(u j x : ℝ))^2)≤
        ((α : ℝ)+(β : ℝ)*(U : ℝ))^2)
    (hVbad : ∀ j,finiteBadMass (velocityRawLaw pV.current pV.crossRecords pV.norm (mv j) (hmv j))
      (fun z => (velocityRawOutputQ pV.current pV.crossRecords pV.norm
        (Fintype.card S) (u j) α β z : ℝ))
      (siteMean (fun x => ((α : ℝ)*mv j x-(β : ℝ)*(u j x : ℝ))^2)) εv≤ρv)
    (hBbad : ∀ j,finiteBadMass
      (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz (e j) q.blocks)
      (fun ω => ((executePlannedBellQ q (e j) ω).value : ℝ)) (bellMean a b c k (e j)) εb≤ρb) :
    let p : LowSpinPlanQ := ⟨pV,some q,copies,queries⟩
    finiteBadMass (lowSpinLaw p mv hmv a b c k hz e)
      (fun z => (lowSpinOutputQ p u e α β U γ z : ℝ))
      (implementedResidualLoss mv (fun j x => (u j x : ℝ)) (pauliField a b c k) e
        (α : ℝ) (β : ℝ) (γ : ℝ))
      ((d : ℝ)*εv+4*(γ : ℝ)*(d : ℝ)*εb)≤(d : ℝ)*ρv+(d : ℝ)*ρb := by
  let p : LowSpinPlanQ := ⟨pV,some q,copies,queries⟩
  let lawV := fun j : Fin d => velocityRawLaw pV.current pV.crossRecords pV.norm (mv j) (hmv j)
  let lawB := bellAxisLaw a b c k hz e q
  let law := lowSpinLaw p mv hmv a b c k hz e
  let fV := fun (j : Fin d) (z : VelocityData S pV.current pV.crossRecords pV.norm) =>
    (velocityRawOutputQ pV.current pV.crossRecords pV.norm (Fintype.card S) (u j) α β z : ℝ)
  let fB := fun (j : Fin d) (ω : Fin q.blocks → CohortObservation q.records q.records (e j)) =>
    ((executePlannedBellQ q (e j) ω).value : ℝ)
  let V := fun j : Fin d => siteMean (fun x => ((α : ℝ)*mv j x-(β : ℝ)*(u j x : ℝ))^2)
  let μ := fun j : Fin d => bellMean a b c k (e j)
  let f : (Fin d ⊕ Fin d) → LowSpinData S d e p → ℝ :=
    Sum.elim (fun j z => fV j (z.1 j)) (fun j z => fB j (z.2 j))
  let centers : (Fin d ⊕ Fin d) → ℝ := Sum.elim V μ
  let radii : (Fin d ⊕ Fin d) → ℝ := Sum.elim (fun _ => εv) (fun _ => εb)
  have hpoint (z : LowSpinData S d e p) (h : ∀ i, |f i z-centers i|≤radii i) :
      |(lowSpinOutputQ p u e α β U γ z : ℝ)-
        ((∑ j,V j)+4*(γ : ℝ)*(∑ j,μ j))|≤(d : ℝ)*εv+4*(γ : ℝ)*(d : ℝ)*εb := by
    rw [low_spin_output_cast_some]
    exact bell_velocity_loss_error _ _ εv εb _ V _ μ hγ hVrange
      (bell_spin_term_range a b c k hz (fun j => e j) (γ : ℝ) hγ)
      (fun j => h (.inl j)) (fun j => h (.inr j))
  have hVm (j : Fin d) : finiteBadMass law (fun z => fV j (z.1 j)) (V j) εv=
      finiteBadMass (lawV j) (fV j) (V j) εv := by
    change finiteBadMass (independentPairLaw (finiteFamilyLaw lawV) lawB)
      (fun z => fV j (z.1 j)) (V j) εv=_
    rw [independent_pair_bad_mass_left (finiteFamilyLaw lawV) lawB
      (fun w => fV j (w j)) (V j) εv,finite_family_bad_mass_coord lawV j (fV j) (V j) εv]
  have hBm (j : Fin d) : finiteBadMass law (fun z => fB j (z.2 j)) (μ j) εb=
      finiteBadMass (freshObservationBlocks a b c k hz (e j) q.blocks) (fB j) (μ j) εb := by
    change finiteBadMass (independentPairLaw (finiteFamilyLaw lawV) lawB)
      (fun z => fB j (z.2 j)) (μ j) εb=_
    rw [independent_pair_bad_mass_right (finiteFamilyLaw lawV) lawB
      (fun w => fB j (w j)) (μ j) εb,bell_axis_bad_mass_coord a b c k hz e q j (fB j) (μ j) εb]
  have hunion := finite_bad_mass_from_components law f centers radii
    (fun z => (lowSpinOutputQ p u e α β U γ z : ℝ))
    ((∑ j,V j)+4*(γ : ℝ)*(∑ j,μ j)) ((d : ℝ)*εv+4*(γ : ℝ)*(d : ℝ)*εb) hpoint
  rw [implemented_loss_bell_form mv (fun j x => (u j x : ℝ)) a b c k hz e]
  calc
    _ ≤ (∑ j : Fin d,finiteBadMass law (fun z => fV j (z.1 j)) (V j) εv)+
        (∑ j : Fin d,finiteBadMass law (fun z => fB j (z.2 j)) (μ j) εb) := by
      simpa only [Fintype.sum_sum_type,f,centers,radii,Sum.elim_inl,Sum.elim_inr] using hunion
    _ = (∑ j : Fin d,finiteBadMass (lawV j) (fV j) (V j) εv)+
        (∑ j : Fin d,finiteBadMass
          (freshObservationBlocks a b c k hz (e j) q.blocks) (fB j) (μ j) εb) := by
      simp_rw [hVm,hBm]
    _ ≤ (∑ _j : Fin d,ρv)+(∑ _j : Fin d,ρb) :=
      add_le_add (Finset.sum_le_sum fun j _ => hVbad j) (Finset.sum_le_sum fun j _ => hBbad j)
    _ = _ := by simp [nsmul_eq_mul]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_some_confidence
