/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressBoxGridEnergy
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressAxisCertificate
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressCountMap
import Mathlib.Logic.Equiv.Prod

set_option backward.isDefEq.respectTransparency false

/-!
Original dyadic-grid matching geometry and the actual trained minority mean.
The edge/endpoint bijection preserves the complete supplied amplitudes and
has twice its edge cardinality equal to the original grid cardinality.
For production matchingOffset the endpoint bit is the translated bit 1.
The minority identity uses the full matching coverage and actual box fields.
These are state/label identities, not a native address-permutation circuit;
physical translation/readout and their gate accounting remain separate.
-/

open Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TrainedGrid
noncomputable section
open scoped BigOperators
open RetainedSpin FiniteAxisWord UniformMatching

/-- Abbreviation for Other in the partial address trained grid model. -/
abbrev Other (m d : ℕ) (axis : Fin d) := {j : Fin d // j≠axis} → Fin (2*m)
/-- Abbreviation for Local Edge in the partial address trained grid model. -/
abbrev LocalEdge (m d : ℕ) (axis : Fin d) := Fin m × Other m d axis
/-- Abbreviation for Box in the partial address trained grid model. -/
abbrev Box (C d : ℕ) := Fin d → Fin 2 × Fin C
/-- Abbreviation for Edge in the partial address trained grid model. -/
abbrev Edge (C m d : ℕ) (axis : Fin d) := Box C d × LocalEdge m d axis

/-- Construction for local Equiv in the partial address trained grid model. -/
def localEquiv (m d : ℕ) (axis : Fin d) :
    (Fin d → Fin (2*m)) ≃ LocalEdge m d axis × Bool where
  toFun x := ((((finProdFinEquiv (m:=m) (n:=2)).symm (Fin.cast (Nat.mul_comm 2 m) (x axis))).1,
    fun j => x j),
    finTwoEquiv ((finProdFinEquiv (m:=m) (n:=2)).symm (Fin.cast (Nat.mul_comm 2 m) (x axis))).2)
  invFun y := fun j => if h : j=axis then
    Fin.cast (Nat.mul_comm m 2) (finProdFinEquiv (y.1.1,finTwoEquiv.symm y.2)) else y.1.2 ⟨j,h⟩
  left_inv x := by
    funext j
    by_cases h : j=axis
    · subst j
      simp only [dite_true,Equiv.symm_apply_apply]
      change Fin.cast (Nat.mul_comm m 2)
        (finProdFinEquiv ((finProdFinEquiv (m:=m) (n:=2)).symm
          (Fin.cast (Nat.mul_comm 2 m) (x axis))))=x axis
      rw [Equiv.apply_symm_apply]
      rfl
    · simp [h]
  right_inv y := by
    rcases y with ⟨⟨q,rest⟩,bit⟩
    apply Prod.ext
    · apply Prod.ext
      · simp
      · funext j
        simp [j.property]
    · simp

/-- Complete original `local_left_axis` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem local_left_axis (m d : ℕ) (axis : Fin d) (e : LocalEdge m d axis) :
    ((localEquiv m d axis).symm (e,false) axis).val=2*e.1.val := by
  simp [localEquiv,finProdFinEquiv,finTwoEquiv]

/-- Complete original `local_right_axis` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem local_right_axis (m d : ℕ) (axis : Fin d) (e : LocalEdge m d axis) :
    ((localEquiv m d axis).symm (e,true) axis).val=2*e.1.val+1 := by
  simp [localEquiv,finProdFinEquiv,finTwoEquiv]
  omega

/-- Complete original `local_right_update` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem local_right_update (m d : ℕ) (axis : Fin d) (e : LocalEdge m d axis) :
    (localEquiv m d axis).symm (e,true)=
      Function.update ((localEquiv m d axis).symm (e,false)) axis
        ⟨((localEquiv m d axis).symm (e,false) axis).val+1,by
          rw [local_left_axis]
          have := e.1.isLt
          omega⟩ := by
  funext j
  by_cases h : j=axis
  · subst j
    apply Fin.ext
    simp only [Function.update_self,local_left_axis,local_right_axis]
  · simp [localEquiv,h]

/-- Construction for matching Equiv in the partial address trained grid model. -/
def matchingEquiv (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d) :
    (Fin d → Fin (2^r)) ≃ Edge C m d axis × Bool :=
  (GridPatch.nativeGridEquiv C (2*m) d r hN offset).trans
    ((Equiv.prodCongr (Equiv.refl (Box C d)) (localEquiv m d axis)).trans
      (Equiv.prodAssoc (Box C d) (LocalEdge m d axis) Bool).symm)

/-- Complete original `matching_inverse` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_inverse (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (e : Edge C m d axis) (bit : Bool) :
    (matchingEquiv C m d r hN offset axis).symm (e,bit)=
      (GridPatch.nativeGridEquiv C (2*m) d r hN offset).symm
        (e.1,(localEquiv m d axis).symm (e.2,bit)) := rfl

/-- Complete original `matching_same_box` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_same_box (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (e : Edge C m d axis) (bit : Bool) :
    (GridPatch.nativeGridEquiv C (2*m) d r hN offset
      ((matchingEquiv C m d r hN offset axis).symm (e,bit))).1=e.1 := by
  rw [matching_inverse,Equiv.apply_symm_apply]

/-- Complete original `matching_right` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_right (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (e : Edge C m d axis) :
    (matchingEquiv C m d r hN offset axis).symm (e,true)=
      MatchedGrid.right d r axis ((matchingEquiv C m d r hN offset axis).symm (e,false)) := by
  rw [matching_inverse,matching_inverse,local_right_update]
  apply BoxGridEnergy.internal_right_inverse
  · have := e.2.1.isLt
    omega

/-- Complete original `matching_card` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_card (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d) :
    2*Fintype.card (Edge C m d axis)=(2^r)^d := by
  have h := Fintype.card_congr (matchingEquiv C m d r hN offset axis)
  have hs : Fintype.card (Fin d → Fin (2^r))=(2^r)^d := by simp
  have ht : Fintype.card (Edge C m d axis × Bool)=Fintype.card (Edge C m d axis)*2 := by
    rw [Fintype.card_prod,Fintype.card_bool]
  rw [hs,ht] at h
  omega

-- Exact complete matching coverage; no independence or sampling law assumption.
/-- Complete original `pair_mean` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem pair_mean {S E : Type} [Fintype S] [Fintype E] [Nonempty E]
    (g : S ≃ E × Bool) (f : S → ℝ) :
    (∑ e : E,(f (g.symm (e,false))+f (g.symm (e,true)))/2)/(Fintype.card E : ℝ)=
      (∑ x : S,f x)/(Fintype.card S : ℝ) := by
  classical
  have hc : (Fintype.card S : ℝ)=2*(Fintype.card E : ℝ) := by
    have h := Fintype.card_congr g
    rw [Fintype.card_prod,Fintype.card_bool] at h
    exact_mod_cast h.trans (Nat.mul_comm _ _)
  have hs : (∑ x : S,f x)=∑ e : E,(f (g.symm (e,false))+f (g.symm (e,true))) := by
    rw [← g.symm.sum_comp f,Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hc,hs,← Finset.sum_div]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Complete original `box_minor_mean` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem box_minor_mean {B A : Type} [Fintype A] [Nonempty A]
    (fields : Fin 3 → B × A → ℝ) (axes : B → Fin 3 → ℝ) (box : B) :
    (∑ a : A,(1-AxisRisk.dot (fun h => fields h (box,a)) (axes box))/2)/
      (Fintype.card A : ℝ)=
      (1-AxisRisk.dot (PilotVector.boxVector fields box) (axes box))/2 := by
  classical
  have hA : (Fintype.card A : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : AxisRisk.dot (PilotVector.boxVector fields box) (axes box)=
      (∑ a : A,AxisRisk.dot (fun h => fields h (box,a)) (axes box))/(Fintype.card A : ℝ) := by
    unfold AxisRisk.dot PilotVector.boxVector PilotProjection.boxMean
    simp only [div_mul_eq_mul_div,Finset.sum_mul,← Finset.sum_div]
    rw [Finset.sum_comm]
  rw [hd,← Finset.sum_div,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  field_simp

/-- Complete original `supplied_amplitude` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem supplied_amplitude (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (e : Edge C m d axis) (bit spin : Bool) :
    supplied
      (fun e => complexSpinor a b c k ((matchingEquiv C m d r hN offset axis).symm (e,false)))
      (fun e => complexSpinor a b c k ((matchingEquiv C m d r hN offset axis).symm (e,true)))
      (e,pairReg bit spin)=
      suppliedSpinState a b c k spin ((matchingEquiv C m d r hN offset axis).symm (e,bit)) := by
  have hp : C≠0 ∧ 2*m≠0 := Nat.mul_ne_zero_iff.mp (NeZero.ne (C*(2*m)))
  let : NeZero C := ⟨hp.1⟩
  let : NeZero m := ⟨(Nat.mul_ne_zero_iff.mp hp.2).2⟩
  let : NeZero (2*m) := ⟨hp.2⟩
  rw [UniformMatching.supplied_amplitude]
  have hc : (2 : ℝ)*(Fintype.card (Edge C m d axis) : ℝ)=
      (Fintype.card (Fin d → Fin (2^r)) : ℝ) := by
    have hs : Fintype.card (Fin d → Fin (2^r))=(2^r)^d := by simp
    rw [hs]
    exact_mod_cast matching_card C m d r hN offset axis
  cases bit <;> simp only [Bool.false_eq_true,ite_false,ite_true,suppliedSpinState,hc]

/-- Complete original `box_average` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem box_average {S B A : Type} [Fintype S] [Fintype B] [Fintype A]
    (g : S ≃ B × A) (f : S → ℝ) :
    (∑ x : S,f x)/(Fintype.card S : ℝ)=
      (∑ b : B,(∑ a : A,f (g.symm (b,a)))/(Fintype.card A : ℝ))/(Fintype.card B : ℝ) := by
  classical
  have hc : (Fintype.card S : ℝ)=(Fintype.card B : ℝ)*(Fintype.card A : ℝ) := by
    exact_mod_cast (Fintype.card_congr g).trans (Fintype.card_prod B A)
  rw [← g.symm.sum_comp f,Fintype.sum_prod_type,hc,← Finset.sum_div,div_div]
  congr 1
  ring

/-- Complete original `grid_minority` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem grid_minority {S B A : Type} [Fintype S] [Fintype B] [Fintype A] [Nonempty A]
    (g : S ≃ B × A) (ψ : S → Bool → ℂ) (hu : ∀ x,qubitMass (ψ x)=1)
    (words : B → List Gate) :
    (∑ x : S,Complex.normSq (runSpin (words (g x).1) (ψ x) true))/(Fintype.card S : ℝ)=
      PilotVector.averageMinority (fun h y => qubitBloch (ψ (g.symm y)) h)
        (fun b => wordAxis (words b)) := by
  rw [box_average g]
  unfold PilotVector.averageMinority
  congr 1
  apply Finset.sum_congr rfl
  intro box _
  simp only [Equiv.apply_symm_apply]
  simp_rw [minority_probability _ _ (hu _)]
  exact box_minor_mean (fun h y => qubitBloch (ψ (g.symm y)) h) (fun b => wordAxis (words b)) box

/-- Complete original `actual_matching_minority` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem actual_matching_minority (C m d r : ℕ) [NeZero C] [NeZero m]
    [NeZero (2*m)] [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (words : Box C d → List Gate) :
    UniformMatching.average (fun e : Edge C m d axis => sectorMass
      (runSpin (words e.1) (complexSpinor a b c k
        ((matchingEquiv C m d r hN offset axis).symm (e,false))))
      (runSpin (words e.1) (complexSpinor a b c k
        ((matchingEquiv C m d r hN offset axis).symm (e,true)))) true)=
      PilotVector.averageMinority
        (NativePilot.actualFields (GridPatch.nativeGridEquiv C (2*m) d r hN offset) a b c k)
        (fun box => wordAxis (words box)) := by
  let g := matchingEquiv C m d r hN offset axis
  let ge := GridPatch.nativeGridEquiv C (2*m) d r hN offset
  let f := fun x => Complex.normSq (runSpin (words (ge x).1) (complexSpinor a b c k x) true)
  have hf (e : Edge C m d axis) (bit : Bool) :
      f (g.symm (e,bit))=Complex.normSq
        (runSpin (words e.1) (complexSpinor a b c k (g.symm (e,bit))) true) := by
    dsimp only [f,g,ge]
    rw [matching_same_box]
  calc
    _ = (∑ e : Edge C m d axis,(f (g.symm (e,false))+f (g.symm (e,true)))/2)/
        (Fintype.card (Edge C m d axis) : ℝ) := by
      simp only [hf,UniformMatching.average,sectorMass]
      rfl
    _ = (∑ x : Fin d → Fin (2^r),f x)/(Fintype.card (Fin d → Fin (2^r)) : ℝ) := pair_mean g f
    _ = _ := by
      have h := grid_minority ge (complexSpinor a b c k)
        (complex_spinor_mass a b c k hz) words
      simp only [complex_spinor_bloch] at h
      exact h

/-- Complete original `local_endpoint_value` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem local_endpoint_value (m d : ℕ) (axis : Fin d) (x : Fin d → Fin (2*m)) :
    (finTwoEquiv.symm ((localEquiv m d axis x).2)).val=(x axis).val%2 := by
  change (finTwoEquiv.symm (finTwoEquiv
    ((finProdFinEquiv (m:=m) (n:=2)).symm (Fin.cast (Nat.mul_comm 2 m) (x axis))).2)).val=_
  rw [Equiv.symm_apply_apply]
  rfl

/-- Complete original `matching_endpoint_value` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_endpoint_value (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (x : Fin d → Fin (2^r)) :
    (finTwoEquiv.symm ((matchingEquiv C m d r hN offset axis x).2)).val=
      (((C*(2*m)-(offset axis).val)+(x axis).val/2)%(C*(2*m)))%2 := by
  change (finTwoEquiv.symm ((localEquiv m d axis
    (GridPatch.nativeGridEquiv C (2*m) d r hN offset x).2).2)).val=_
  rw [local_endpoint_value]
  change (((((C*(2*m)-(offset axis).val)+(x axis).val/2)%(C*(2*m)))%(2*m))%2)=_
  exact Nat.mod_mod_of_dvd _ ⟨m,rfl⟩

/-- Complete original `matching_color_bit` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_color_bit (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (axis : Fin d) (color : Fin 2)
    (x : Fin d → Fin (2^r)) :
    (finTwoEquiv.symm ((matchingEquiv C m d r hN
      (MatchedGrid.matchingOffset C (2*m) d axis color (by omega)) axis x).2)).val=
      ((x axis).val/2+color.val)%2 := by
  rw [matching_endpoint_value,MatchedGrid.matching_offset_value]
  simp only [ite_true,mul_one]
  have hd : 2 ∣ C*(2*m) := ⟨C*m,by ring⟩
  rw [Nat.mod_mod_of_dvd _ hd]
  have hm : (C*(2*m))%2=0 := Nat.mod_eq_zero_of_dvd hd
  have hp : 0<C*(2*m) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hc := color.isLt
  omega

/-- Construction for basis Equiv in the partial address trained grid model. -/
def basisEquiv (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d) :
    ((Fin d → Fin (2^r)) × Bool) ≃ (Edge C m d axis × (Fin 2 → Bool)) :=
  ((matchingEquiv C m d r hN offset axis).prodCongr (Equiv.refl Bool)).trans
    ((Equiv.prodAssoc (Edge C m d axis) Bool Bool).trans
      ((Equiv.refl (Edge C m d axis)).prodCongr pairEquiv))

/-- Complete original `basis_amplitude` guarantee for `PartialAddressTrainedGrid`; all source hypotheses and output obligations are retained. -/
theorem basis_amplitude (C m d r : ℕ) [NeZero (C*(2*m))]
    (hN : 2^r=C*(2*m)*2) (offset : Fin d → Fin (C*(2*m))) (axis : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (x : (Fin d → Fin (2^r)) × Bool) :
    supplied
      (fun e => complexSpinor a b c k ((matchingEquiv C m d r hN offset axis).symm (e,false)))
      (fun e => complexSpinor a b c k ((matchingEquiv C m d r hN offset axis).symm (e,true)))
      (basisEquiv C m d r hN offset axis x)=suppliedSpinState a b c k x.2 x.1 := by
  change supplied _ _ ((matchingEquiv C m d r hN offset axis x.1).1,
    pairReg (matchingEquiv C m d r hN offset axis x.1).2 x.2)=_
  have h := supplied_amplitude C m d r hN offset axis a b c k
    (matchingEquiv C m d r hN offset axis x.1).1
    (matchingEquiv C m d r hN offset axis x.1).2 x.2
  simpa only [Prod.mk.eta,Equiv.symm_apply_apply] using h

#print axioms localEquiv
#print axioms local_left_axis
#print axioms local_right_axis
#print axioms local_right_update
#print axioms matchingEquiv
#print axioms matching_inverse
#print axioms matching_same_box
#print axioms matching_right
#print axioms matching_card
#print axioms pair_mean
#print axioms box_minor_mean
#print axioms supplied_amplitude
#print axioms box_average
#print axioms grid_minority
#print axioms actual_matching_minority
#print axioms local_endpoint_value
#print axioms matching_endpoint_value
#print axioms matching_color_bit
#print axioms basisEquiv
#print axioms basis_amplitude
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.TrainedGrid
