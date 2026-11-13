/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

/-!
# Difference-model partition functions and consistent labels

Defines the edge-difference map `edgeDiff`, the Boltzmann product `deltaWeight`, and the sum
`consistentDeltaSum` over labelings induced by vertex configurations. Global shifts preserve
edge differences, and under the stated connectivity condition each nonempty fiber consists
precisely of the global shifts of one configuration.

The theorem `lemma5_6_difference_model_partition` proves the factorization from Lemma 5.6 of
[AradLandau2010]: the difference-model partition function is the color cardinality times the
consistent-label sum.

## Main statements

* `fiber_eq_image`: describes a fiber of the edge-difference map by global shifts.
* `lemma5_6_difference_model_partition`: factors the partition function through consistent
  labels.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

namespace Qatlib.Papers.TensorNetwork08.MainResults.Lemma56

open Classical
open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

/-- The sum of Boltzmann edge-weight products over edge labelings induced by vertex differences,
with zero contribution from other labelings. -/
noncomputable def consistentDeltaSum [DecidableEq C] [AddCommGroup C]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ) : ℂ :=
  ∑ δ : E → C,
    if IsConsistentLabeling src dst δ then
      ∏ e : E, Complex.exp (-(β * h e (δ e)))
    else 0

/-- The edge labeling obtained by subtracting the destination vertex label from the source
vertex label. -/
def edgeDiff [Sub C] (src dst : E → V) (σ : V → C) : E → C :=
  fun e => σ (src e) - σ (dst e)

/-- The product of the Boltzmann factors `exp (-β * h e (δ e))` over all edges. -/
noncomputable def deltaWeight (h : E → C → ℂ) (β : ℂ) (δ : E → C) : ℂ :=
  ∏ e : E, Complex.exp (-(β * h e (δ e)))

/-- Adding a constant to every vertex label leaves all edge differences unchanged. -/
theorem edgeDiff_shift [AddCommGroup C] (src dst : E → V) (σ : V → C) (κ : C) :
    edgeDiff src dst (σ + fun _ => κ) = edgeDiff src dst σ := by
  classical
  funext e
  simp only [edgeDiff, Pi.add_apply]
  abel

/-- On a nonempty vertex type, distinct constant shifts of a fixed configuration give distinct
configurations. -/
theorem shift_injective [AddCommGroup C] [Nonempty V] (σ₀ : V → C) :
    Function.Injective (fun κ : C => σ₀ + fun _ => κ) := by
  classical
  intro κ₁ κ₂ h
  have hv := congrFun h (Classical.arbitrary V)
  simpa only [Pi.add_apply] using add_left_cancel hv

/-- Under the stated connectivity condition, the fiber of `edgeDiff` containing `σ₀` is exactly
the image of all constant shifts of `σ₀`. See [AradLandau2010]. -/
theorem fiber_eq_image [AddCommGroup C] [DecidableEq C] [Nonempty V]
    (src dst : E → V) (hconn : ∀ σ τ : V → C,
      (∀ e : E, σ (src e) - σ (dst e) = τ (src e) - τ (dst e)) →
        ∃ κ : C, ∀ v : V, τ v = σ v + κ)
    (σ₀ : V → C) (δ : E → C) (hσ₀ : edgeDiff src dst σ₀ = δ) :
    (Finset.univ.filter (fun σ : V → C => edgeDiff src dst σ = δ))
      = Finset.univ.image (fun κ : C => σ₀ + fun _ => κ) := by
  classical
  ext σ
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hσ
    have hsame : ∀ e : E, σ₀ (src e) - σ₀ (dst e) = σ (src e) - σ (dst e) := by
      intro e
      have h1 : edgeDiff src dst σ₀ e = δ e := by rw [hσ₀]
      have h2 : edgeDiff src dst σ e = δ e := by rw [hσ]
      exact h1.trans h2.symm
    obtain ⟨κ, hκ⟩ := hconn σ₀ σ hsame
    exact ⟨κ, by funext v; simpa using (hκ v).symm⟩
  · rintro ⟨κ, rfl⟩
    rw [edgeDiff_shift, hσ₀]

/-- For a nonempty vertex type and the stated connectivity condition, the difference-model
partition function equals the color cardinality times the sum over consistent edge
labelings. See [AradLandau2010]. -/
theorem lemma5_6_difference_model_partition
    [AddCommGroup C] [DecidableEq C] [Nonempty V]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ)
    (hconn : ∀ σ τ : V → C,
      (∀ e : E, σ (src e) - σ (dst e) = τ (src e) - τ (dst e)) →
        ∃ κ : C, ∀ v : V, τ v = σ v + κ) :
    differencePartitionFunction src dst h β
      = (Fintype.card C : ℂ) * consistentDeltaSum src dst h β := by
  classical

  have hfiber : ∀ δ : E → C,
      (∑ σ : V → C, if edgeDiff src dst σ = δ then (1 : ℂ) else 0)
        = if IsConsistentLabeling src dst δ then (Fintype.card C : ℂ) else 0 := by
    intro δ
    by_cases hc : ∃ σ : V → C, edgeDiff src dst σ = δ
    · obtain ⟨σ₀, hσ₀⟩ := hc
      have hcons : IsConsistentLabeling src dst δ :=
        ⟨σ₀, fun e => by have := congrFun hσ₀ e; simpa [edgeDiff] using this.symm⟩
      rw [if_pos hcons, sum_ite_one, fiber_eq_image src dst hconn σ₀ δ hσ₀]
      rw [Finset.card_image_of_injOn
        (fun a _ b _ hab => shift_injective σ₀ hab), Finset.card_univ]
    · have hnc : ¬ IsConsistentLabeling src dst δ := by
        intro hcon
        obtain ⟨σ, hσ⟩ := hcon
        exact hc ⟨σ, by funext e; simpa [edgeDiff] using (hσ e).symm⟩
      rw [if_neg hnc]
      refine Finset.sum_eq_zero fun σ _ => ?_
      by_cases heq : edgeDiff src dst σ = δ
      · exact absurd ⟨σ, heq⟩ hc
      · simp [heq]

  have hL : differencePartitionFunction src dst h β
      = ∑ σ : V → C, deltaWeight h β (edgeDiff src dst σ) := by
    simp only [differencePartitionFunction, deltaWeight, edgeDiff]
  rw [hL]
  calc ∑ σ : V → C, deltaWeight h β (edgeDiff src dst σ)
      = ∑ σ : V → C, ∑ δ : E → C,
          (if edgeDiff src dst σ = δ then (1 : ℂ) else 0) * deltaWeight h β δ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_eq_single (edgeDiff src dst σ)]
        · simp
        · intro δ _ hδ; rw [if_neg (fun h => hδ h.symm), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    _ = ∑ δ : E → C, ∑ σ : V → C,
          (if edgeDiff src dst σ = δ then (1 : ℂ) else 0) * deltaWeight h β δ :=
        Finset.sum_comm
    _ = ∑ δ : E → C,
          (∑ σ : V → C, if edgeDiff src dst σ = δ then (1 : ℂ) else 0) * deltaWeight h β δ := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ δ : E → C,
          (if IsConsistentLabeling src dst δ then (Fintype.card C : ℂ) else 0)
            * deltaWeight h β δ := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [hfiber δ]
    _ = (Fintype.card C : ℂ) * ∑ δ : E → C,
          if IsConsistentLabeling src dst δ then deltaWeight h β δ else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ _ => ?_
        by_cases hδ : IsConsistentLabeling src dst δ <;> simp [hδ]
    _ = (Fintype.card C : ℂ) * consistentDeltaSum src dst h β := by
        simp only [consistentDeltaSum, deltaWeight]

end Qatlib.Papers.TensorNetwork08.MainResults.Lemma56
