/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

/-!
# Tensor-network evaluation of a general partition function

Defines the vertex-consistency tensors `vertexTensor` and Boltzmann tensors `energyTensor` for
the general-model network of Theorem 5.2 in [AradLandau2010]. Vertex configurations induce
labels on both ends of each edge through `induced`.

The consistency identities identify contributing edge-end labelings with induced vertex
labelings. When every vertex is incident to an edge, the induced-labeling map is injective and
`theorem5_2_network_evaluates_partition` identifies the network value with the partition
function.

## Main statements

* `prod_vertexTensor_eq_indicator`: characterizes the product of vertex-consistency tensors.
* `induced_injective`: proves injectivity when every vertex is incident to an edge.
* `theorem5_2_network_evaluates_partition`: identifies the network contraction with the
  partition function.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

namespace Qatlib.Papers.TensorNetwork08.MainResults.Theorem52

open Classical
open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

/-- The zero-one tensor testing whether all edge-end labels incident to a vertex equal some
common color. -/
noncomputable def vertexTensor (src dst : E → V) (v : V) (l : E × Bool → C) : ℂ :=
  if ∃ c : C,
      (∀ e : E, src e = v → l (e, true) = c) ∧
        (∀ e : E, dst e = v → l (e, false) = c)
    then 1 else 0

/-- The complex Boltzmann weight for the two endpoint labels of edge `e`. -/
noncomputable def energyTensor (h : E → C → C → ℂ) (β : ℂ) (e : E)
    (l : E × Bool → C) : ℂ :=
  Complex.exp (-(β * h e (l (e, true)) (l (e, false))))

/-- The sum over all edge-end labelings of the product of vertex-consistency tensors and edge
Boltzmann tensors. -/
noncomputable def generalModelNetworkValue (src dst : E → V) (h : E → C → C → ℂ)
    (β : ℂ) : ℂ :=
  ∑ l : E × Bool → C,
    (∏ v : V, vertexTensor src dst v l) * ∏ e : E, energyTensor h β e l

/-- The edge-end labeling obtained from a vertex configuration, using the source for true and
the destination for false. -/
def induced (src dst : E → V) (σ : V → C) : E × Bool → C :=
  fun p => if p.2 then σ (src p.1) else σ (dst p.1)

/-- At the true endpoint of an edge, the induced label is the source vertex label. -/
@[simp] theorem induced_true (src dst : E → V) (σ : V → C) (e : E) :
    induced src dst σ (e, true) = σ (src e) := by simp [induced]

/-- At the false endpoint of an edge, the induced label is the destination vertex label. -/
@[simp] theorem induced_false (src dst : E → V) (σ : V → C) (e : E) :
    induced src dst σ (e, false) = σ (dst e) := by simp [induced]

/-- Local existence of a common incident color at every vertex is equivalent to a vertex
configuration matching all edge-end labels. -/
theorem forall_exists_iff (src dst : E → V) (l : E × Bool → C) :
    (∀ v : V, ∃ c : C,
        (∀ e : E, src e = v → l (e, true) = c) ∧
          (∀ e : E, dst e = v → l (e, false) = c))
      ↔ ∃ σ : V → C, ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e) := by
  constructor
  · intro h
    choose σ hσ using h
    exact ⟨σ, fun e => ⟨(hσ (src e)).1 e rfl, (hσ (dst e)).2 e rfl⟩⟩
  · rintro ⟨σ, hσ⟩ v
    refine ⟨σ v, ?_, ?_⟩
    · intro e he
      rw [(hσ e).1, he]
    · intro e he
      rw [(hσ e).2, he]

/-- The product of the vertex tensors is one exactly when the edge-end labels match some vertex
configuration, and zero otherwise. See [AradLandau2010]. -/
theorem prod_vertexTensor_eq_indicator (src dst : E → V) (l : E × Bool → C) :
    (∏ v : V, vertexTensor src dst v l)
      = if (∃ σ : V → C,
            ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e))
        then 1 else 0 := by
  classical
  have hiff : (∀ v : V, ∃ c : C,
        (∀ e : E, src e = v → l (e, true) = c) ∧
          (∀ e : E, dst e = v → l (e, false) = c))
      ↔ ∃ σ : V → C, ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e) :=
    forall_exists_iff src dst l
  have hprod : (∏ v : V, vertexTensor src dst v l)
      = if (∀ v : V, ∃ c : C,
            (∀ e : E, src e = v → l (e, true) = c) ∧
              (∀ e : E, dst e = v → l (e, false) = c)) then 1 else 0 := by
    have h1 : (∏ v : V, vertexTensor src dst v l)
        = ∏ v : V, (if (∃ c : C,
            (∀ e : E, src e = v → l (e, true) = c) ∧
              (∀ e : E, dst e = v → l (e, false) = c)) then (1 : ℂ) else 0) :=
      Finset.prod_congr rfl fun v _ => by simp [vertexTensor]
    rw [h1, prod_ite_one_zero]
    simp
  rw [hprod]
  by_cases h : ∃ σ : V → C, ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]

/-- An edge-end labeling matches a vertex configuration exactly when it equals the labeling
induced by some configuration. -/
theorem exists_iff_exists_induced (src dst : E → V) (l : E × Bool → C) :
    (∃ σ : V → C, ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e))
      ↔ ∃ σ : V → C, l = induced src dst σ := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, by
      funext p
      rcases p with ⟨e, b⟩
      cases b
      · simpa using (hσ e).2
      · simpa using (hσ e).1⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨σ, fun e => ⟨by simp, by simp⟩⟩

/-- If every vertex is a source or destination of some edge, then distinct vertex configurations
induce distinct edge-end labelings. See [AradLandau2010]. -/
theorem induced_injective (src dst : E → V)
    (hcover : ∀ v : V, ∃ e : E, src e = v ∨ dst e = v) :
    Function.Injective (induced (C := C) src dst) := by
  intro σ τ h
  funext v
  obtain ⟨e, he | he⟩ := hcover v
  · have hv := congrFun h (e, true)
    simpa [he] using hv
  · have hv := congrFun h (e, false)
    simpa [he] using hv

/-- If every vertex is incident to an edge, the general-model tensor-network value equals the
partition function with the same interactions and inverse temperature. See [AradLandau2010]. -/
theorem theorem5_2_network_evaluates_partition
    (src dst : E → V) (h : E → C → C → ℂ) (β : ℂ)
    (hcover : ∀ v : V, ∃ e : E, src e = v ∨ dst e = v) :
    generalModelNetworkValue src dst h β = partitionFunction src dst h β := by
  classical

  have hval : generalModelNetworkValue src dst h β
      = ∑ l : E × Bool → C,
          (if ∃ σ : V → C, l = induced src dst σ then (1 : ℂ) else 0)
            * ∏ e : E, energyTensor h β e l := by
    simp only [generalModelNetworkValue]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [prod_vertexTensor_eq_indicator]
    by_cases h : ∃ σ : V → C, l = induced src dst σ
    · have hcons : ∃ σ : V → C,
          ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e) :=
        (exists_iff_exists_induced src dst l).mpr h
      rw [if_pos hcons, if_pos h]
    · have hcons : ¬ ∃ σ : V → C,
          ∀ e : E, l (e, true) = σ (src e) ∧ l (e, false) = σ (dst e) :=
        fun hc => h ((exists_iff_exists_induced src dst l).mp hc)
      rw [if_neg hcons, if_neg h]
  set img : Finset (E × Bool → C) := Finset.univ.image (induced src dst) with himg
  have hmem : ∀ l : E × Bool → C, l ∈ img ↔ ∃ σ : V → C, l = induced src dst σ := by
    intro l
    rw [himg, Finset.mem_image]
    constructor
    · rintro ⟨σ, -, hσ⟩
      exact ⟨σ, hσ.symm⟩
    · rintro ⟨σ, hσ⟩
      exact ⟨σ, Finset.mem_univ _, hσ.symm⟩
  calc generalModelNetworkValue src dst h β
      = ∑ l : E × Bool → C,
          (if l ∈ img then (1 : ℂ) else 0) * ∏ e : E, energyTensor h β e l := by
        rw [hval]
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases h : ∃ σ : V → C, l = induced src dst σ
        · rw [if_pos h, if_pos ((hmem l).mpr h)]
        · rw [if_neg h, if_neg (fun hh => h ((hmem l).mp hh))]
    _ = ∑ l : E × Bool → C,
          (if l ∈ img then ∏ e : E, energyTensor h β e l else 0) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        by_cases hl : l ∈ img <;> simp [hl]
    _ = ∑ l ∈ img, ∏ e : E, energyTensor h β e l := by
        have hsub : (∑ l : E × Bool → C,
              (if l ∈ img then ∏ e : E, energyTensor h β e l else 0))
            = ∑ l ∈ img,
              (if l ∈ img then ∏ e : E, energyTensor h β e l else 0) :=
          (Finset.sum_subset (fun x _ => Finset.mem_univ x) (fun x _ hx => by simp [hx])).symm
        rw [hsub]
        exact Finset.sum_congr rfl fun l hl => by rw [if_pos hl]
    _ = ∑ σ : V → C, ∏ e : E, energyTensor h β e (induced src dst σ) := by
        rw [himg, Finset.sum_image (fun x _ y _ hxy => induced_injective src dst hcover hxy)]
    _ = partitionFunction src dst h β := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        refine Finset.prod_congr rfl fun e _ => ?_
        simp [energyTensor]

end Qatlib.Papers.TensorNetwork08.MainResults.Theorem52
