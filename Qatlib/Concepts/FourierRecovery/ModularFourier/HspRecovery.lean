/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.HspRecoveryDefs

/-!
# Stabilizer recovery endpoints and compact records

This module proves the record, controlled powers, and dyadic localisation specifications used
for Abelian stabilizer recovery [Kitaev1995]. It computes the total localisation cost and
verifies normalization and event probabilities for the next independent product record law.

The compact index map is proved injective and surjective, with full range cardinality and a
sufficient binary width. The endpoint theorems collect these results together with the existing
mixture and correct oracle bisection guarantees.

## Main statements

* `aspLocalisationCost_eq`: total localisation cost is `2^l - 1`.
* `clause14_endpoint_holds`: mixture, controlled powers, and conditional bisection guarantees.
* `clause16_endpoint_holds`: independent record probabilities and compact width.
* `clause17_endpoint_holds`: compact indexing and cardinality properties.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.FourierRecovery.ModularFourier.HspRecoveryDefs
open Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Concepts.StabilizerAlg.NearUniformGen.AspRecordKernel

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open scoped Classical BigOperators ENNReal

/-- The total localisation cost for `l` levels is `2^l - 1`. -/
theorem aspLocalisationCost_eq (l : ℕ) : aspLocalisationCost l = 2 ^ l - 1 := by
  have hmain : ∀ l : ℕ, (Finset.range l).sum aspLocalisationGateCost = 2 ^ l - 1 := by
    intro l
    induction l with
    | zero =>
        simp
    | succ l ih =>
        rw [Finset.sum_range_succ, ih, aspLocalisationGateCost, pow_succ]
        have h1 : (1 : ℕ) ≤ 2 ^ l := by
          have h2 : (0 : ℕ) < 2 ^ l := by positivity
          omega
        omega
  exact hmain l

/-- The compact index map on a finite type is injective. -/
theorem aspCompactIndex_injective {X : Type} [Fintype X] :
    Function.Injective (aspCompactIndex (X := X)) := by
  intro x y hxy
  exact Equiv.injective (Fintype.equivFin X) hxy

/-- Every index below the cardinality of a finite type is the compact index of some element. -/
theorem aspCompactIndex_surjective {X : Type} [Fintype X] :
    Function.Surjective (aspCompactIndex (X := X)) := by
  intro z
  refine ⟨(Fintype.equivFin X).symm z, ?_⟩
  simp [aspCompactIndex]

/-- For nonzero `m`, the compact width provides at least `m` binary labels. -/
theorem aspCompactWidth_bound (m : ℕ) (hm : m ≠ 0) : m ≤ 2 ^ aspCompactWidth m := by
  exact compactRecordWidth_bound m hm

/-- The range of the compact index map has cardinality equal to that of its domain. -/
theorem aspCompactIndex_range_card {X : Type} [Fintype X] :
    (Set.range (aspCompactIndex (X := X))).ncard = Fintype.card X := by
  simp [Set.ncard_range_of_injective (aspCompactIndex_injective (X := X))]

/-- The next product record law has total probability one. -/
theorem aqNext_product_record_law_is_distribution {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) :
    (∑ ω : Fin l → G, (aqNextProductRecordLaw μ l).prob ω) = 1 :=
  (aqNextProductRecordLaw μ l).sum_one

/-- The next product record law assigns each record its independent sample probability
`μ.probOf`. -/
theorem aqNext_product_record_mass_eq {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) (ω : Fin l → G) :
    (aqNextProductRecordLaw μ l).prob ω = μ.probOf ω := rfl

/-- Summing the next product record law over an event equals its independent sample event
probability. -/
theorem aqNext_product_record_event_eq {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) (E : (Fin l → G) → Prop) [DecidablePred E] :
    (∑ ω ∈ Finset.univ.filter E, (aqNextProductRecordLaw μ l).prob ω)
      = FinDist.probEvent (L := l) μ E := by
  unfold FinDist.probEvent aqNextProductRecordLaw
  rfl

/-- Packages mixture normalization, uniform character branches, controlled powers, and bisection
guarantees conditional on oracle correctness, associated with [Kitaev, Lemma
10][Kitaev1995]. -/
theorem clause14_endpoint_holds : clause14_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω G _ _ _ k
    exact AspRecordKernel.marginal_total_mass k
  · intro G _ _ _ χ
    exact aspOrbitBranchLaw_uniform G χ
  · intro I _ _ U l
    exact asp_gate_is_paper_U_pow U l
  · intro l j hj
    exact asp_gate_provides_localisation_powers l j hj
  · intro l o
    refine ⟨aspBisectionRun_queries l o, aspBisectionRun_level l o, ?_⟩
    rw [aspBisectionRun_width]
    rfl
  · intro l o φ hφ hcorrect
    exact aspBisection_contains l o φ hφ hcorrect

/-- Establishes the controlled powers and localisation specification, including exponent ranges
and the exact cost `2^l - 1`. -/
theorem walkGoal_endpoint_holds : walkGoal_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro I _ _ U l
    exact asp_gate_is_paper_U_pow U l
  · intro l x
    exact asp_gate_exponent_range l x
  · intro l j hj
    exact ⟨asp_gate_provides_localisation_powers l j hj, asp_gate_localisation_block l j hj⟩
  · intro l
    exact aspLocalisationCost_eq l
  · intro l
    rw [aspLocalisationCost_eq]
    have : (1 : ℕ) ≤ 2 ^ l := by
      have h2 : (0 : ℕ) < 2 ^ l := by positivity
      omega
    omega

/-- Establishes the product record specification, including normalization, independent record
masses, event probabilities, and the compact width bound. -/
theorem clause16_endpoint_holds : clause16_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G _ _ μ l
    exact asp_product_record_law_is_distribution μ l
  · intro G _ _ μ l ω
    exact asp_product_record_mass_eq μ l ω
  · intro m hm
    exact aspCompactWidth_bound m hm
  · intro G _ _ μ l
    exact aqNext_product_record_law_is_distribution μ l
  · intro G _ _ μ l ω
    exact aqNext_product_record_mass_eq μ l ω
  · intro G _ _ μ l E
    exact aqNext_product_record_event_eq μ l E

/-- Establishes the compact indexing specification: injectivity, surjectivity, sufficient binary
width, and preservation of cardinality. -/
theorem clause17_endpoint_holds : clause17_endpoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X _ a₁ a₂ h
    exact aspCompactIndex_injective (X := X) h
  · intro X _ z
    exact aspCompactIndex_surjective (X := X) z
  · intro m hm
    exact aspCompactWidth_bound m hm
  · intro X
    exact aspCompactIndex_range_card (X := X)

end Qatlib.Concepts.FourierRecovery.ModularFourier
