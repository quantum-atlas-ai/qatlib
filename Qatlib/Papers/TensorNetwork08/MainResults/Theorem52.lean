/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
set_option warningAsError false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Theorem52

open Classical
open scoped BigOperators
open Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

noncomputable def vertexTensor (src dst : E → V) (v : V) (l : E × Bool → C) : ℂ :=
  if ∃ c : C,
      (∀ e : E, src e = v → l (e, true) = c) ∧
        (∀ e : E, dst e = v → l (e, false) = c)
    then 1 else 0

noncomputable def energyTensor (h : E → C → C → ℂ) (β : ℂ) (e : E)
    (l : E × Bool → C) : ℂ :=
  Complex.exp (-(β * h e (l (e, true)) (l (e, false))))

noncomputable def generalModelNetworkValue (src dst : E → V) (h : E → C → C → ℂ)
    (β : ℂ) : ℂ :=
  ∑ l : E × Bool → C,
    (∏ v : V, vertexTensor src dst v l) * ∏ e : E, energyTensor h β e l

def induced (src dst : E → V) (σ : V → C) : E × Bool → C :=
  fun p => if p.2 then σ (src p.1) else σ (dst p.1)

@[simp] theorem induced_true (src dst : E → V) (σ : V → C) (e : E) :
    induced src dst σ (e, true) = σ (src e) := by simp [induced]

@[simp] theorem induced_false (src dst : E → V) (σ : V → C) (e : E) :
    induced src dst σ (e, false) = σ (dst e) := by simp [induced]

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
