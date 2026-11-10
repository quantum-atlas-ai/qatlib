/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.OrderedKernel

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.QcaDynamics.ScalarNoGo
namespace Qatlib.Concepts.QcaDynamics.PeriodicNoGo

def neighborhoodDiffs {V : Type*} [Sub V] [DecidableEq V] (E : Finset V) : Finset V :=
  (E ×ˢ E).image fun p => p.1 - p.2

theorem sub_mem_neighborhoodDiffs {V : Type*} [Sub V] [DecidableEq V]
    {E : Finset V} {e f : V} (he : e ∈ E) (hf : f ∈ E) :
    e - f ∈ neighborhoodDiffs E :=
  Finset.mem_image.mpr ⟨(e,f), Finset.mem_product.mpr ⟨he,hf⟩, rfl⟩

def KernelNonalias {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq V] (q : V →+ W) (E : Finset V) : Prop :=
  Set.InjOn q (neighborhoodDiffs E : Set V)

theorem kernelNonalias_injOn {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq V] (q : V →+ W) (E : Finset V) (hq : KernelNonalias q E) :
    Set.InjOn q (E : Set V) := by
  intro e he f hf hef
  have hmap : q (e - f) = q (e - e) := by simp [map_sub, hef]
  have h := hq (sub_mem_neighborhoodDiffs he hf) (sub_mem_neighborhoodDiffs he he) hmap
  have hzero : e - f = 0 := by simpa using h
  exact sub_eq_zero.mp hzero

def quotientWeights {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq W] (q : V →+ W) (A : Weights V) : Weights W where
  neighborhood := A.neighborhood.image q
  weight y := ∑ e ∈ A.neighborhood, if q e = y then A.weight e else 0
  support y hy := by
    by_contra hn
    apply hy
    apply Finset.sum_eq_zero
    intro e he
    have hne : q e ≠ y := by
      intro h
      exact hn (Finset.mem_image.mpr ⟨e,he,h⟩)
    simp [hne]

theorem quotient_weight_mem {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq V] [DecidableEq W] (q : V →+ W) (A : Weights V)
    (hq : Set.InjOn q (A.neighborhood : Set V)) (e : V) (he : e ∈ A.neighborhood) :
    (quotientWeights q A).weight (q e) = A.weight e := by
  unfold quotientWeights
  dsimp only
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    have hn : q f ≠ q e := by intro h; exact hfe (hq hf he h)
    simp [hn]
  · exact fun h => False.elim (h he)

theorem quotient_weight_difference {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq V] [DecidableEq W] (q : V →+ W) (A : Weights V)
    (hq : KernelNonalias q A.neighborhood) (e d : V)
    (he : e ∈ A.neighborhood) (hd : d ∈ neighborhoodDiffs A.neighborhood) :
    (quotientWeights q A).weight (q (e - d)) = A.weight (e - d) := by
  by_cases hm : e - d ∈ A.neighborhood
  · exact quotient_weight_mem q A (kernelNonalias_injOn q _ hq) _ hm
  · have hz : A.weight (e - d) = 0 := by
      by_contra h
      exact hm (A.support _ h)
    rw [hz]
    change (∑ f ∈ A.neighborhood, if q f = q (e - d) then A.weight f else 0) = 0
    apply Finset.sum_eq_zero
    intro f hf
    have hn : q f ≠ q (e - d) := by
      intro h
      have hmap : q (e - f) = q d := by
        rw [map_sub, h, map_sub]
        abel
      have hef := hq (sub_mem_neighborhoodDiffs he hf) hd hmap
      have hf' : f = e - d := by rw [← hef]; abel
      exact hm (hf' ▸ hf)
    simp only [if_neg hn]

theorem unitary_of_quotient {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq V] [DecidableEq W] (q : V →+ W) (A : Weights V)
    (hq : KernelNonalias q A.neighborhood) (hU : Unitary (quotientWeights q A)) :
    Unitary A := by
  have hinj := kernelNonalias_injOn q A.neighborhood hq
  have hdiag : (∑ y ∈ (quotientWeights q A).neighborhood,
      (quotientWeights q A).weight y * star ((quotientWeights q A).weight y)) =
      ∑ e ∈ A.neighborhood, A.weight e * star (A.weight e) := by
    change (∑ y ∈ A.neighborhood.image q, _) = _
    rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    apply Finset.sum_congr rfl
    intro e he
    rw [quotient_weight_mem q A hinj e he]
  refine ⟨hdiag.symm.trans hU.1, ?_⟩
  intro d hd
  by_cases hmem : d ∈ neighborhoodDiffs A.neighborhood
  · obtain ⟨p,hp,_⟩ := Finset.mem_image.mp hmem
    have he : p.1 ∈ A.neighborhood := (Finset.mem_product.mp hp).1
    have hzero : (0 : V) ∈ neighborhoodDiffs A.neighborhood := by
      simpa using sub_mem_neighborhoodDiffs he he
    have hqd : q d ≠ 0 := by
      intro h
      apply hd
      exact hq hmem hzero (by simpa using h)
    have hcorr : (∑ y ∈ (quotientWeights q A).neighborhood,
        (quotientWeights q A).weight y * star ((quotientWeights q A).weight (y - q d))) =
        ∑ e ∈ A.neighborhood, A.weight e * star (A.weight (e - d)) := by
      change (∑ y ∈ A.neighborhood.image q, _) = _
      rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
      apply Finset.sum_congr rfl
      intro e he
      rw [quotient_weight_mem q A hinj e he, ← map_sub,
        quotient_weight_difference q A hq e d he hmem]
    exact hcorr.symm.trans (hU.2 (q d) hqd)
  · apply Finset.sum_eq_zero
    intro e he
    by_cases hz : A.weight (e - d) = 0
    · simp [hz]
    · have hem := A.support (e - d) hz
      have hdmem : d ∈ neighborhoodDiffs A.neighborhood := by
        have h := sub_mem_neighborhoodDiffs he hem
        have hdiff : e - (e - d) = d := by abel
        rwa [hdiff] at h
      exact False.elim (hmem hdmem)

theorem quotient_step {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [DecidableEq W] (q : V →+ W) (A : Weights V) (φ : W → ℂ) (x : W) :
    step (quotientWeights q A) φ x =
      ∑ e ∈ A.neighborhood, A.weight e * φ (x + q e) := by
  unfold step quotientWeights
  dsimp only
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_eq_single (q e)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hn
    exact False.elim (hn (Finset.mem_image.mpr ⟨e,he,rfl⟩))

theorem quotient_noGo {V W : Type*} [AddCommGroup V] [LinearOrder V]
    [IsOrderedAddMonoid V] [AddCommGroup W] [DecidableEq V] [DecidableEq W]
    (q : V →+ W) (A : Weights V) (hq : KernelNonalias q A.neighborhood)
    (hU : Unitary (quotientWeights q A)) :
    ∃ (e₀ : V) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      ∀ (φ : W → ℂ) (x : W), step (quotientWeights q A) φ x = c * φ (x + q e₀) := by
  obtain ⟨e₀,hne,honly,hnorm⟩ := noGo_weights A (unitary_of_quotient q A hq hU)
  refine ⟨e₀,A.weight e₀,rfl,hnorm,?_⟩
  intro φ x
  rw [quotient_step]
  rw [Finset.sum_eq_single e₀]
  · intro e _ he
    have hz : A.weight e = 0 := by
      by_contra h
      exact he (honly e h)
    simp [hz]
  · intro hn
    exact False.elim (hn (A.support e₀ hne))

end Qatlib.Concepts.QcaDynamics.PeriodicNoGo
