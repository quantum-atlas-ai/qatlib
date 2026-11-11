/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StabilizerAlg.NearUniformGen.CompositeMeasurementNearUniformStat
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Near uniformity of composite measurements

`compositeMeasurementNearUniformSubgoal` proves that uniformly mixing conditional laws which
return their subgroup label with error at most δ gives subset probabilities within δ of the
uniform subgroup law. The proof bounds the conditional mass of a subset separately for labels
inside and outside it. For background, see [Kitaev1995].

## Main statements

* `compositeMeasurementNearUniformSubgoal`: proves the subsetwise deviation bound for the
  composite measurement mixture.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen
open scoped Classical BigOperators
open Qatlib

/-- The sum of a real constant over a finite set is its cardinality times the constant. -/
private lemma sum_const_card {α : Type} [Fintype α] (s : Finset α) (c : ℝ) :
    (∑ _i ∈ s, c) = (s.card : ℝ) * c := by
  simp [Finset.sum_const, nsmul_eq_mul]

/-- The real-valued cardinality of a finite-set complement is the ambient cardinality minus the
set cardinality. -/
private lemma card_compl {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) :
    (sᶜ : Finset α).card = (Fintype.card α : ℝ) - (s.card : ℝ) := by
  have hle := Finset.card_le_univ s
  rw [Finset.card_compl, Nat.cast_sub hle]

/-- The mass assigned by a finite distribution to a finite set of distinct subgroup elements is
at most one. -/
private lemma subset_mass_le_one {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H : AddSubgroup G} (d : FinDist G) (s : Finset (↥H)) :
    (∑ g ∈ s, d.prob (g : G)) ≤ 1 := by
  have hinj : Set.InjOn Subtype.val (s : Set (↥H)) :=
    Set.injOn_of_injective fun a b h => Subtype.ext h
  have hsub : (∑ g ∈ s, d.prob (g : G)) ≤ ∑ x : G, d.prob x := by
    calc
      ∑ g ∈ s, d.prob (g : G) = ∑ x ∈ s.image Subtype.val, d.prob x := by
        symm
        exact Finset.sum_image hinj
      _ ≤ ∑ x : G, d.prob x :=
        Finset.sum_le_sum_of_subset_of_nonneg (s := s.image Subtype.val)
          (t := Finset.univ) (Finset.subset_univ _) (fun x _ _ => d.nonneg x)
  rw [d.sum_one] at hsub
  exact hsub

/-- A uniform mixture over subgroup labels, each conditionally returned with probability at
least `1 - δ`, differs from the uniform subgroup law by at most δ on every finite subgroup
subset. -/
theorem compositeMeasurementNearUniformSubgoal :
    CompositeMeasurementNearUniformSubgoal := by
  intro G _ _ _ H μ cond δ hδ hmix hacc L
  have hq0 : (0 : ℝ) < (Fintype.card ↥H : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hq : (Fintype.card ↥H : ℝ) ≠ 0 := ne_of_gt hq0
  have hmc : (L.card : ℝ) ≤ (Fintype.card ↥H : ℝ) := by
    exact_mod_cast Finset.card_le_univ L

  set m : ↥H → ℝ := fun h' => ∑ g ∈ L, (cond h').prob (g : G) with hmdef
  have hm_nonneg (h' : ↥H) : 0 ≤ m h' := by
    dsimp [m]
    exact Finset.sum_nonneg fun g _ => (cond h').nonneg (g : G)
  have hm_le_one (h' : ↥H) : m h' ≤ 1 :=
    subset_mass_le_one (cond h') L
  have hm_ge (h' : ↥H) (hh' : h' ∈ L) : 1 - δ ≤ m h' := by
    have hone := hacc h'
    have hsingle : (cond h').prob (h' : G) ≤ ∑ g ∈ L, (cond h').prob (g : G) :=
      Finset.single_le_sum (s := L) (fun g _ => (cond h').nonneg (g : G)) hh'
    dsimp [m]
    linarith
  have hm_le (h' : ↥H) (hh' : h' ∉ L) : m h' ≤ δ := by
    have hone := hacc h'
    have hcompl : (cond h').prob (h' : G) ≤ ∑ g ∈ (L : Finset (↥H))ᶜ, (cond h').prob (g : G) :=
      Finset.single_le_sum (s := Lᶜ) (fun g _ => (cond h').nonneg (g : G))
        (Finset.mem_compl.2 hh')
    have ht := Finset.sum_add_sum_compl L (fun g : ↥H => (cond h').prob (g : G))
    have hone2 : (∑ g : ↥H, (cond h').prob (g : G)) ≤ 1 :=
      subset_mass_le_one (cond h') Finset.univ
    dsimp [m]
    linarith

  have hexch : (∑ g ∈ L, μ.prob (g : G))
      = (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, m h' := by
    have h1 : (∑ g ∈ L, μ.prob (g : G))
        = ∑ g ∈ L, (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob (g : G) := by
      refine Finset.sum_congr rfl fun g _ => ?_
      exact hmix (g : G)
    rw [h1, ← Finset.mul_sum, Finset.sum_comm]

  have hsum_low : (L.card : ℝ) * (1 - δ) ≤ ∑ h' : ↥H, m h' := by
    have h1 : (L.card : ℝ) * (1 - δ) ≤ ∑ h' ∈ L, m h' := by
      have hcard : ∑ h' ∈ L, (1 - δ) = (L.card : ℝ) * (1 - δ) := sum_const_card L _
      rw [← hcard]
      exact Finset.sum_le_sum (s := L) fun h' hh' => hm_ge h' hh'
    exact le_trans h1 (Finset.sum_le_sum_of_subset_of_nonneg (s := L)
      (t := Finset.univ) (Finset.subset_univ _) fun h' _ _ => hm_nonneg h')
  have hcompl_card : (Lᶜ : Finset (↥H)).card = (Fintype.card ↥H : ℝ) - (L.card : ℝ) :=
    card_compl L
  have hsum_up :
      (∑ h' : ↥H, m h') ≤ (L.card : ℝ) + ((Fintype.card ↥H : ℝ) - (L.card : ℝ)) * δ := by
    have hsplit : (∑ h' : ↥H, m h') = (∑ h' ∈ L, m h') + ∑ h' ∈ Lᶜ, m h' :=
      (Finset.sum_add_sum_compl L fun h' => m h').symm
    have h1 : (∑ h' ∈ L, m h') ≤ (L.card : ℝ) := by
      have hcard : ∑ h' ∈ L, (1 : ℝ) = (L.card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      rw [← hcard]
      exact Finset.sum_le_sum (s := L) fun h' _ => hm_le_one h'
    have h2 : (∑ h' ∈ Lᶜ, m h')
        ≤ ((Lᶜ : Finset (↥H)).card : ℝ) * δ := by
      have hcard : ∑ h' ∈ Lᶜ, δ = ((Lᶜ : Finset (↥H)).card : ℝ) * δ :=
        sum_const_card Lᶜ _
      rw [← hcard]
      exact Finset.sum_le_sum (s := Lᶜ) fun h' hh' => hm_le h' (Finset.mem_compl.mp hh')
    calc
      ∑ h' : ↥H, m h' = (∑ h' ∈ L, m h') + ∑ h' ∈ Lᶜ, m h' := hsplit
      _ ≤ (L.card : ℝ) + ((Lᶜ : Finset (↥H)).card : ℝ) * δ := add_le_add h1 h2
      _ = _ := by rw [hcompl_card]

  have hdev : |(∑ h' : ↥H, m h') - (L.card : ℝ)| ≤ (Fintype.card ↥H : ℝ) * δ := by
    rw [abs_le]
    constructor
    · have hmul := mul_le_mul_of_nonneg_right hmc hδ
      linarith
    · have hmc0 : 0 ≤ (L.card : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
      linarith
  rw [hexch]
  have hone : (Fintype.card ↥H : ℝ)⁻¹ * (∑ h' : ↥H, m h') - (L.card : ℝ) /
        (Fintype.card ↥H : ℝ)
      = ((∑ h' : ↥H, m h') - (L.card : ℝ)) / (Fintype.card ↥H : ℝ) := by
    field_simp [hq]
  rw [hone]
  calc
    |((∑ h' : ↥H, m h') - (L.card : ℝ)) / (Fintype.card ↥H : ℝ)|
        = |(∑ h' : ↥H, m h') - (L.card : ℝ)| / (Fintype.card ↥H : ℝ) := by
          rw [abs_div, abs_of_pos hq0]
    _ ≤ ((Fintype.card ↥H : ℝ) * δ) / (Fintype.card ↥H : ℝ) := by
          gcongr
    _ = δ := by field_simp [hq]

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
