/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressMatchedGrid
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressBoxPoincare
import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellLowMean

set_option backward.isDefEq.respectTransparency false

/-!
Transport open edges of translated product boxes to the original +2 grid.
Every internal edge maps to the original directed edge at the inverse address;
the address equivalence prevents duplicate counting, and discarded boundary
edges are nonnegative. Uniform geometry is unrelated to independence of pilot
box counts. The actual normalized spinors identify periodic Pauli energy with
8 times the Bell-11 mean. All directional public promises yield the actual
average box defect bound d*ell^2*p0 for ell=2*m. This is a classical geometry
and spin-energy bridge, not a free routing or trained-main circuit theorem.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.BoxGridEnergy

/-- Complete original `inside_step` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem inside_step (C ell y : ℕ) (hell : 0<ell) (hy : y<C*ell) (hi : y%ell+1<ell) :
    y+1<C*ell ∧ (y+1)/ell=y/ell ∧ (y+1)%ell=y%ell+1 := by
  have hq : y/ell<C := Nat.div_lt_of_lt_mul (show y<ell*C by simpa only [Nat.mul_comm] using hy)
  have hid := Nat.mod_add_div y ell
  have hend : y+1<C*ell := by
    calc
      _ = ell*(y/ell)+(y%ell+1) := by omega
      _ < ell*(y/ell)+ell := Nat.add_lt_add_left hi _
      _ = ell*(y/ell+1) := by ring
      _ ≤ ell*C := Nat.mul_le_mul_left ell (by omega)
      _ = _ := Nat.mul_comm _ _
  refine ⟨hend,?_,?_⟩
  · calc
      _ = ((y%ell+1)+ell*(y/ell))/ell := by congr 1; omega
      _ = (y%ell+1)/ell+y/ell := Nat.add_mul_div_left _ _ hell
      _ = _ := by rw [Nat.div_eq_of_lt hi]; omega
  · rw [← Nat.mod_add_mod y ell 1,Nat.mod_eq_of_lt hi]

/-- Complete original `internal_right_image` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem internal_right_image (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (offset : Fin d → Fin (C*ell))
    (x : Fin d → Fin (2^r)) (j : Fin d) (hell : 0<ell)
    (hi : ((GridPatch.nativeGridEquiv C ell d r hN offset x).2 j).val+1<ell) :
    GridPatch.nativeGridEquiv C ell d r hN offset (MatchedGrid.right d r j x)=
      ((GridPatch.nativeGridEquiv C ell d r hN offset x).1,
        Function.update (GridPatch.nativeGridEquiv C ell d r hN offset x).2 j
          ⟨((GridPatch.nativeGridEquiv C ell d r hN offset x).2 j).val+1,hi⟩) := by
  have hL : 0<C*ell := Nat.pos_of_ne_zero (NeZero.ne _)
  let y := ((C*ell-(offset j).val)+(x j).val/2)%(C*ell)
  have hy : y<C*ell := Nat.mod_lt _ hL
  have hilocal : y%ell+1<ell := hi
  have hs := inside_step C ell y hell hy hilocal
  have hv : (MatchedGrid.right d r j x j).val=((x j).val+2)%(C*ell*2) := by
    simp only [MatchedGrid.right,Function.update_self,Fin.val_add,
      Fin.coe_ofNat_eq_mod,Nat.add_mod_mod,hN]
  apply Prod.ext
  · funext i
    by_cases hij : i=j
    · subst i
      apply Prod.ext <;> apply Fin.ext
      · change (MatchedGrid.right d r j x j).val%2=(x j).val%2
        rw [hv]
        exact MatchedGrid.native_parity_same (C*ell) (x j).val
      · change (((C*ell-(offset j).val)+(MatchedGrid.right d r j x j).val/2)%(C*ell))/ell=
          (((C*ell-(offset j).val)+(x j).val/2)%(C*ell))/ell
        rw [hv,MatchedGrid.translated_right,Nat.mod_eq_of_lt hs.1]
        exact hs.2.1
    · change (GridPatch.coordinateEquiv C ell (offset i) (Fin.cast hN (MatchedGrid.right d r j x i))).1=
        (GridPatch.coordinateEquiv C ell (offset i) (Fin.cast hN (x i))).1
      simp only [MatchedGrid.right,Function.update_of_ne hij]
  · dsimp only
    funext i
    by_cases hij : i=j
    · subst i
      rw [Function.update_self]
      apply Fin.ext
      change (((C*ell-(offset j).val)+(MatchedGrid.right d r j x j).val/2)%(C*ell))%ell=
        (((C*ell-(offset j).val)+(x j).val/2)%(C*ell))%ell+1
      rw [hv,MatchedGrid.translated_right,Nat.mod_eq_of_lt hs.1]
      exact hs.2.2
    · rw [Function.update_of_ne hij]
      change (GridPatch.coordinateEquiv C ell (offset i) (Fin.cast hN (MatchedGrid.right d r j x i))).2=
        (GridPatch.coordinateEquiv C ell (offset i) (Fin.cast hN (x i))).2
      simp only [MatchedGrid.right,Function.update_of_ne hij]

/-- Complete original `internal_right_inverse` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem internal_right_inverse (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (offset : Fin d → Fin (C*ell))
    (box : Fin d → Fin 2 × Fin C) (a : Fin d → Fin ell) (j : Fin d) (hell : 0<ell)
    (hi : (a j).val+1<ell) :
    (GridPatch.nativeGridEquiv C ell d r hN offset).symm
      (box,Function.update a j ⟨(a j).val+1,hi⟩)=
      MatchedGrid.right d r j ((GridPatch.nativeGridEquiv C ell d r hN offset).symm (box,a)) := by
  let e := GridPatch.nativeGridEquiv C ell d r hN offset
  apply (GridPatch.nativeGridEquiv C ell d r hN offset).injective
  rw [Equiv.apply_symm_apply]
  have hi' : ((e (e.symm (box,a))).2 j).val+1<ell := by simpa only [e.apply_symm_apply] using hi
  have h := internal_right_image C ell d r hN offset (e.symm (box,a)) j hell hi'
  dsimp only [e] at h
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Construction for periodic Energy in the partial address box grid energy model. -/
def periodicEnergy (d r : ℕ) (f : (Fin d → Fin (2^r)) → ℝ) : ℝ :=
  ∑ x,∑ j : Fin d,(f (MatchedGrid.right d r j x)-f x)^2

/-- Complete original `scalar_energy_transport` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem scalar_energy_transport (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (offset : Fin d → Fin (C*ell)) (hell : 0<ell)
    (f : (Fin d → Fin (2^r)) → ℝ) :
    (∑ box : Fin d → Fin 2 × Fin C,BoxTensor.gridEnergy
      (fun a => f ((GridPatch.nativeGridEquiv C ell d r hN offset).symm (box,a)))) ≤
      periodicEnergy d r f := by
  let e := GridPatch.nativeGridEquiv C ell d r hN offset
  have he (box : Fin d → Fin 2 × Fin C) (a : Fin d → Fin ell) (j : Fin d) :
      BoxTensor.edgeAt (fun v => f (e.symm (box,v))) j a ≤
        (f (MatchedGrid.right d r j (e.symm (box,a)))-f (e.symm (box,a)))^2 := by
    unfold BoxTensor.edgeAt
    split_ifs with hi
    · change (f (e.symm (box,Function.update a j ⟨(a j).val+1,hi⟩))-f (e.symm (box,a)))^2 ≤ _
      rw [show e.symm (box,Function.update a j ⟨(a j).val+1,hi⟩)=_ from
        internal_right_inverse C ell d r hN offset box a j hell hi]
    · exact sq_nonneg _
  calc
    _ ≤ ∑ box : Fin d → Fin 2 × Fin C,∑ a : Fin d → Fin ell,∑ j : Fin d,
        (f (MatchedGrid.right d r j (e.symm (box,a)))-f (e.symm (box,a)))^2 := by
      apply Finset.sum_le_sum
      intro box _
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum fun j _ => he box a j
    _ = _ := by
      rw [← Fintype.sum_prod_type (fun z => ∑ j : Fin d,
        (f (MatchedGrid.right d r j (e.symm z))-f (e.symm z))^2)]
      exact e.symm.sum_comp (fun x => ∑ j : Fin d,(f (MatchedGrid.right d r j x)-f x)^2)

/-- Complete original `fin_equiv_two` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem fin_equiv_two (N : ℕ) [NeZero N] : (ZMod.finEquiv N) (2 : Fin N)=2 := by
  cases N with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ N => rfl

/-- Complete original `right_eq_periodic` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem right_eq_periodic (d r : ℕ) (j : Fin d) (x : Fin d → Fin (2^r)) :
    MatchedGrid.right d r j x=periodicDoubleShift d (2^r) j x := by
  funext i
  apply (ZMod.finEquiv (2^r)).injective
  rw [periodic_double_shift_coordinates]
  by_cases hi : i=j
  · subst i
    simp only [MatchedGrid.right,Function.update_self,ite_true,map_add]
    congr 1
    exact fin_equiv_two (2^r)
  · simp only [MatchedGrid.right,Function.update_of_ne hi,ite_eq_right hi,add_zero]

/-- Complete original `pauli_edge_bell` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem pauli_edge_bell {S : Type*} (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (x y : S) :
    (∑ h : Fin 3,(pauliField a b c k h y-pauliField a b c k h x)^2)=
      8*RetainedSpin.bellProbability (complexSpinor a b c k y)
        (complexSpinor a b c k x) := by
  have h := RetainedSpin.bell_probability_eq_bloch_distance
    (complexSpinor a b c k y) (complexSpinor a b c k x)
    (RetainedSpin.complex_spinor_mass a b c k hz y) (RetainedSpin.complex_spinor_mass a b c k hz x)
  rw [RetainedSpin.complex_spinor_bloch,RetainedSpin.complex_spinor_bloch] at h
  linarith

/-- Construction for directional Bell Mean in the partial address box grid energy model. -/
noncomputable def directionalBellMean {d r : ℕ} (a b c k : (Fin d → Fin (2^r)) → ℝ) (j : Fin d) : ℝ :=
  (∑ x,RetainedSpin.bellProbability
    (complexSpinor a b c k (periodicDoubleShift d (2^r) j x))
    (complexSpinor a b c k x))/((2^r : ℕ) : ℝ)^d

/-- Complete original `directional_bell_mean_eq` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem directional_bell_mean_eq {d r : ℕ}
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (j : Fin d) :
    directionalBellMean a b c k j=
      RetainedSpin.bellMean a b c k (periodicDoubleShift d (2^r) j) := by
  unfold directionalBellMean RetainedSpin.bellMean RetainedSpin.populationMean
  simp only [periodic_grid_card,Nat.cast_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  unfold RetainedSpin.bellProbability
  have h (u v : Bool → ℂ) : RetainedSpin.determinant u v= -RetainedSpin.determinant v u := by
    unfold RetainedSpin.determinant
    ring
  rw [h,Complex.normSq_neg]

/-- Complete original `pauli_periodic_energy` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem pauli_periodic_energy {d r : ℕ} (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) :
    (∑ h : Fin 3,periodicEnergy d r (pauliField a b c k h))=
      8*((2^r : ℕ) : ℝ)^d*∑ j : Fin d,directionalBellMean a b c k j := by
  unfold periodicEnergy
  rw [Finset.sum_comm]
  have hpoint (x : Fin d → Fin (2^r)) :
      (∑ h : Fin 3,∑ j : Fin d,
        (pauliField a b c k h (MatchedGrid.right d r j x)-pauliField a b c k h x)^2)=
      ∑ j : Fin d,8*RetainedSpin.bellProbability
        (complexSpinor a b c k (periodicDoubleShift d (2^r) j x)) (complexSpinor a b c k x) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [pauli_edge_bell a b c k hz,right_eq_periodic]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp only [directionalBellMean,← Finset.mul_sum,← Finset.sum_div]
  have hM : ((2^r : ℕ) : ℝ)^d ≠ 0 := by positivity
  field_simp

/-- Complete original `native_average_defect_energy` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem native_average_defect_energy (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m)))
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) :
    PilotVector.averageDefect (NativePilot.actualFields
      (GridPatch.nativeGridEquiv C (2*m) d r hN offset) a b c k) ≤
      (((2*m : ℕ) : ℝ)^2/(8*((2^r : ℕ) : ℝ)^d))*
        ∑ h : Fin 3,periodicEnergy d r (pauliField a b c k h) := by
  let e := GridPatch.nativeGridEquiv C (2*m) d r hN offset
  let nb : ℝ := Fintype.card (Fin d → Fin 2 × Fin C)
  have hnb : 0<nb := by dsimp only [nb]; exact_mod_cast Fintype.card_pos
  have hA : ((2*m : ℕ) : ℝ)^d ≠ 0 := by exact_mod_cast pow_ne_zero d (NeZero.ne (2*m))
  have hcard : nb*((2*m : ℕ) : ℝ)^d=((2^r : ℕ) : ℝ)^d := by
    have hc := Fintype.card_congr e
    simp only [Fintype.card_prod,Fintype.card_pi,Fintype.card_fin,Finset.prod_const,
      Finset.card_univ] at hc
    have hr : ((2^r)^d : ℝ)=((2*C)^d : ℝ)*((2*m)^d : ℝ) := by exact_mod_cast hc
    simpa only [nb,Fintype.card_pi,Fintype.card_prod,Fintype.card_fin,Finset.prod_const,
      Finset.card_univ,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat] using hr.symm
  have hsum := Finset.sum_le_sum (fun box (_ : box ∈ (Finset.univ : Finset (Fin d → Fin 2 × Fin C))) =>
    BoxTensor.native_box_defect_bound e a b c k hz box)
  have hE : (∑ box : Fin d → Fin 2 × Fin C,∑ h : Fin 3,
      BoxTensor.gridEnergy (fun v => pauliField a b c k h (e.symm (box,v)))) ≤
      ∑ h : Fin 3,periodicEnergy d r (pauliField a b c k h) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro h _
    exact scalar_energy_transport C (2*m) d r hN offset (Nat.pos_of_ne_zero (NeZero.ne (2*m))) (pauliField a b c k h)
  have hcoef : 0 ≤ (((2*m : ℕ) : ℝ)^2/(8*((2*m : ℕ) : ℝ)^d)) := by positivity
  calc
    _ ≤ (∑ box : Fin d → Fin 2 × Fin C,
        (((2*m : ℕ) : ℝ)^2/(8*((2*m : ℕ) : ℝ)^d))*
          ∑ h : Fin 3,BoxTensor.gridEnergy (fun v => pauliField a b c k h (e.symm (box,v))))/nb :=
      div_le_div_of_nonneg_right hsum hnb.le
    _ = ((((2*m : ℕ) : ℝ)^2/(8*((2*m : ℕ) : ℝ)^d))*
        (∑ box : Fin d → Fin 2 × Fin C,∑ h : Fin 3,
          BoxTensor.gridEnergy (fun v => pauliField a b c k h (e.symm (box,v)))))/nb := by
      rw [Finset.mul_sum]
    _ ≤ ((((2*m : ℕ) : ℝ)^2/(8*((2*m : ℕ) : ℝ)^d))*
        (∑ h : Fin 3,periodicEnergy d r (pauliField a b c k h)))/nb :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE hcoef) hnb.le
    _ = _ := by rw [← hcard]; field_simp

/-- Complete original `native_average_defect_bell` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem native_average_defect_bell (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m)))
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) :
    PilotVector.averageDefect (NativePilot.actualFields
      (GridPatch.nativeGridEquiv C (2*m) d r hN offset) a b c k) ≤
      ((2*m : ℕ) : ℝ)^2*∑ j : Fin d,directionalBellMean a b c k j := by
  have h := native_average_defect_energy C m d r hN offset a b c k hz
  rw [pauli_periodic_energy a b c k hz] at h
  have heq : ((((2*m : ℕ) : ℝ)^2/(8*((2^r : ℕ) : ℝ)^d))*
      (8*((2^r : ℕ) : ℝ)^d*∑ j : Fin d,directionalBellMean a b c k j))=
      ((2*m : ℕ) : ℝ)^2*∑ j : Fin d,directionalBellMean a b c k j := by
    field_simp
  rwa [heq] at h

/-- Complete original `native_average_defect_promise` guarantee for `PartialAddressBoxGridEnergy`; all source hypotheses and output obligations are retained. -/
theorem native_average_defect_promise (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m)))
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (p0 : ℝ) (hp : ∀ j : Fin d,
      RetainedSpin.bellMean a b c k (periodicDoubleShift d (2^r) j) ≤ p0) :
    PilotVector.averageDefect (NativePilot.actualFields
      (GridPatch.nativeGridEquiv C (2*m) d r hN offset) a b c k) ≤
      (d : ℝ)*((2*m : ℕ) : ℝ)^2*p0 := by
  calc
    _ ≤ _ := native_average_defect_bell C m d r hN offset a b c k hz
    _ ≤ ((2*m : ℕ) : ℝ)^2*∑ _ : Fin d,p0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => by rw [directional_bell_mean_eq]; exact hp j)) (sq_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

#print axioms inside_step
#print axioms internal_right_image
#print axioms internal_right_inverse
#print axioms scalar_energy_transport
#print axioms fin_equiv_two
#print axioms right_eq_periodic
#print axioms pauli_edge_bell
#print axioms directional_bell_mean_eq
#print axioms pauli_periodic_energy
#print axioms native_average_defect_energy
#print axioms native_average_defect_bell
#print axioms native_average_defect_promise
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.BoxGridEnergy
