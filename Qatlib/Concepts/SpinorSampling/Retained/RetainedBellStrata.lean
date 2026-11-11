/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellPGF

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Strata

Retained Bell Strata constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n m : ℕ}

-- No positivity of this particular event is needed, including empty fibers.
/-- Complete original `matched_fiber_mass_formula` guarantee for `RetainedBellStrata`; all source hypotheses and output obligations are retained. -/
theorem matched_fiber_mass_formula (τ : Equiv.Perm S) (A : Finset S) :
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => matchedSites z.1 z.2 τ=A),pairAddressMass z)=
      matchedCardEventMass τ n m A.card / (Fintype.card S).choose A.card := by
  let c := ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
    (fun z => matchedSites z.1 z.2 τ=A),pairAddressMass z
  have hc : ∀ B ∈ (Finset.univ : Finset S).powersetCard A.card,
      (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ=B),pairAddressMass z)=c := by
    intro B hB
    have hAB : A.card=B.card := (Finset.mem_powersetCard.mp hB).2.symm
    obtain ⟨σ,hσ⟩ := exists_perm_map_finset A B hAB
    exact (matched_fiber_filter_mass_equal σ τ A B hσ).symm.trans rfl
  have hf : (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ).card=A.card)=
      (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ∈(Finset.univ : Finset S).powersetCard A.card) := by
    ext z
    simp [Finset.mem_powersetCard]
  have hD : matchedCardEventMass τ n m A.card=
      ((Fintype.card S).choose A.card : ℝ)*c := by
    unfold matchedCardEventMass
    rw [hf]
    exact matched_card_event_mass_const τ c hc
  have hchoose : ((Fintype.card S).choose A.card : ℝ)≠0 := by
    exact_mod_cast (Nat.choose_pos A.card_le_univ).ne'
  change c=_
  rw [hD]
  field_simp

/-- Complete original `matched_stratum_weighted` guarantee for `RetainedBellStrata`; all source hypotheses and output obligations are retained. -/
theorem matched_stratum_weighted (τ : Equiv.Perm S) (r : ℕ) (F : Finset S → ℝ) :
    (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ).card=r),pairAddressMass z*F (matchedSites z.1 z.2 τ))=
      (matchedCardEventMass τ n m r / (Fintype.card S).choose r)*
        ∑ A ∈ (Finset.univ : Finset S).powersetCard r,F A := by
  have hf : (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
      (fun z => (matchedSites z.1 z.2 τ).card=r)=
      (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
        (fun z => matchedSites z.1 z.2 τ∈(Finset.univ : Finset S).powersetCard r) := by
    ext z
    simp [Finset.mem_powersetCard]
  calc
    _ = ∑ A ∈ (Finset.univ : Finset S).powersetCard r,
        ∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
          (fun z => matchedSites z.1 z.2 τ=A),pairAddressMass z*F (matchedSites z.1 z.2 τ) := by
      rw [hf]
      simpa only [Finset.sum_filter] using
        (Finset.sum_fiberwise_eq_sum_filter
          (s := (Finset.univ : Finset ((Fin n → S) × (Fin m → S))))
          (t := (Finset.univ : Finset S).powersetCard r)
          (g := fun z => matchedSites z.1 z.2 τ)
          (f := fun z => pairAddressMass z*F (matchedSites z.1 z.2 τ))).symm
    _ = ∑ A ∈ (Finset.univ : Finset S).powersetCard r,
        (∑ z ∈ (Finset.univ : Finset ((Fin n → S) × (Fin m → S))).filter
          (fun z => matchedSites z.1 z.2 τ=A),pairAddressMass z)*F A := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      have hAr := (Finset.mem_powersetCard.mp hA).2
      rw [matched_fiber_mass_formula τ A,hAr]

/-- Complete original `observation_stratum_pgf` guarantee for `RetainedBellStrata`; all source hypotheses and output obligations are retained. -/
theorem observation_stratum_pgf (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (τ : Equiv.Perm S) (r : ℕ) (u : ℝ) :
    observationStratumPGF (n:=n) (m:=m) a b c k hz τ r u=
      (matchedCardEventMass τ n m r / (Fintype.card S).choose r)*
        ∑ A ∈ (Finset.univ : Finset S).powersetCard r,
          ∏ x ∈ A,(1+bellProbability (complexSpinor a b c k x)
            (complexSpinor a b c k (τ x))*(u-1)) := by
  rw [observation_stratum_address_pgf]
  exact matched_stratum_weighted (n:=n) (m:=m) τ r (fun A =>
    ∏ x ∈ A,(1+bellProbability (complexSpinor a b c k x)
      (complexSpinor a b c k (τ x))*(u-1)))

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.matched_fiber_mass_formula
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.matched_stratum_weighted
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.observation_stratum_pgf
