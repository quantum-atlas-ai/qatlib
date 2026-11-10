/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.CoordinateFibre
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.FullCarrier
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

theorem sum_indicator_subtype {A K : Type*} [Fintype A] [AddCommMonoid K] (p : A → Prop)
    (g : A → K) : (∑ a : A,if p a then g a else 0)=∑ a : {a // p a},g a := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (F := inferInstance) (Finset.univ.filter p) (by simp) g
omit [Fintype I] [Fintype L] in

theorem update_injective_iff (i : I) (u : InjectiveTuple I L) (a : L) :
    Function.Injective (Function.update (u : I → L) i a) ↔ a ∉ Set.range (eraseTuple i u) := by
  constructor
  · intro h ⟨j,hj⟩
    have he : Function.update (u : I → L) i a j=Function.update (u : I → L) i a i := by
      rw [Function.update_of_ne j.2,Function.update_self]
      exact hj
    exact j.2 (h he)
  · intro h
    exact (completeCoordinate i u ⟨a,h⟩).injective

theorem coordinateGram_apply (i : I) (u : InjectiveTuple I L) (v : InjectiveTuple I L → ℂ) :
    (coordinateGram (L := L) i*ᵥ v) u=∑ a : L,extend v (Function.update (u : I → L) i a) := by
  change (∑ z : InjectiveTuple I L,(if eraseTuple i u=eraseTuple i z then (1 : ℂ) else 0)*v z)=_
  simp_rw [ite_mul,one_mul,zero_mul]
  have hs (z : InjectiveTuple I L) : (if eraseTuple i u=eraseTuple i z then v z else 0)=
      if eraseTuple i z=eraseTuple i u then v z else 0 := by simp [eq_comm]
  simp_rw [hs]
  trans ∑ z : {z : InjectiveTuple I L // eraseTuple i z=eraseTuple i u},v z.1
  · convert sum_indicator_subtype (fun z : InjectiveTuple I L => eraseTuple i z=eraseTuple i u) v using 1
    · apply Finset.sum_congr (by ext; simp)
      intro z hz
      by_cases h : eraseTuple i z=eraseTuple i u <;> simp [h]
    · apply Finset.sum_congr (by ext; simp)
      intro z hz
      rfl
  · have he := Fintype.sum_equiv (coordinateFibreEquiv i u)
      (fun z : {z : InjectiveTuple I L // eraseTuple i z=eraseTuple i u} => v z.1)
      (fun a : Available i u => v (completeCoordinate i u a))
      (fun z => by
        have hh := (coordinateFibreEquiv i u).left_inv z
        exact congrArg
            (fun z : {z : InjectiveTuple I L // eraseTuple i z=eraseTuple i u} => v z.1) hh.symm)
    rw [he]
    symm
    have hz : (∑ a : L,extend v (Function.update (u : I → L) i a))=
        ∑ a : Available i u,extend v (Function.update (u : I → L) i a.1) := by
      trans ∑ a : L,if a ∉ Set.range (eraseTuple i u) then extend v (Function.update (u : I → L) i a) else 0
      · apply Finset.sum_congr rfl
        intro a ha
        by_cases h : a ∉ Set.range (eraseTuple i u)
        · rw [if_pos h]
        · rw [if_neg h]
          have hn := not_iff_not.mpr (update_injective_iff i u a)
          have hni : ¬ Function.Injective (Function.update (u : I → L) i a) := hn.mpr h
          simp [extend,hni]
      · convert sum_indicator_subtype (fun a : L => a ∉ Set.range (eraseTuple i u))
          (fun a => extend v (Function.update (u : I → L) i a)) using 1
        · apply Finset.sum_congr (by ext; simp)
          intro a ha
          by_cases h : a ∉ Set.range (eraseTuple i u) <;> simp [h]
        · apply Finset.sum_congr (by ext; simp)
          intro a ha
          rfl
    rw [hz]
    apply Finset.sum_congr rfl
    intro a ha
    exact extend_injective v (completeCoordinate i u a)

end Qatlib.Foundations.MatrixGeometry.TupleDeletion
