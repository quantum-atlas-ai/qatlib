/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressNativePilot

set_option backward.isDefEq.respectTransparency false

/-!
Canonical color matching: clear address bit 1 and translate by twice the
known color, then prove both endpoints lie in the same translated box for
even ell. The input labels are in the frame after the known -2*color
translation; they are not raw pre-translation supplied-state addresses.
The bit-clear arithmetic is tied to the original little-endian
address decoder. These are classical label identities, not a free quantum
routing/decomposition or a proof of the full main measurement law.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.MatchedGrid

/-- Complete original `pair_local_lt` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem pair_local_lt (ell y : ℕ) (hell : 0<ell) (heven : ell%2=0) (hy : y%2=0) :
    y%ell+1<ell := by
  have hd : 2 ∣ ell := Nat.dvd_of_mod_eq_zero heven
  have hm : (y%ell)%2=0 := by rw [Nat.mod_mod_of_dvd y hd]; exact hy
  have hl := Nat.mod_lt y hell
  omega

/-- Complete original `pair_box_step` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem pair_box_step (C ell y : ℕ) (hell : 0<ell) (heven : ell%2=0)
    (hy : y<C*ell) (hpar : y%2=0) : y+1<C*ell ∧ (y+1)/ell=y/ell := by
  have hend : (C*ell)%2=0 := by simp only [Nat.mul_mod,heven,mul_zero,Nat.zero_mod]
  have hnext := pair_local_lt ell y hell heven hpar
  constructor
  · omega
  · calc
      _ = ((y%ell+1)+ell*(y/ell))/ell := by
        congr 1
        have h := Nat.mod_add_div y ell
        omega
      _ = (y%ell+1)/ell+y/ell := Nat.add_mul_div_left _ _ hell
      _ = _ := by rw [Nat.div_eq_of_lt hnext]; omega

/-- Complete original `coarse_right` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem coarse_right (L x : ℕ) : ((x+2)%(L*2))/2=(x/2+1)%L := by
  rw [Nat.mod_mul_left_div_self]
  congr 1
  omega

/-- Complete original `translated_right` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem translated_right (L c x : ℕ) :
    ((L-c)+((x+2)%(L*2))/2)%L=(((L-c)+x/2)%L+1)%L := by
  rw [coarse_right,Nat.add_mod_mod,Nat.mod_add_mod]
  congr 1

#print axioms pair_local_lt
#print axioms pair_box_step
#print axioms coarse_right
#print axioms translated_right
/-- Complete original `native_box_same` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem native_box_same (C ell c x : ℕ) (hell : 0<ell) (heven : ell%2=0)
    (hL : 0<C*ell) (hpar : (((C*ell-c)+x/2)%(C*ell))%2=0) :
    (((C*ell-c)+((x+2)%(C*ell*2))/2)%(C*ell))/ell=
      (((C*ell-c)+x/2)%(C*ell))/ell := by
  have h := pair_box_step C ell (((C*ell-c)+x/2)%(C*ell)) hell heven
    (Nat.mod_lt _ hL) hpar
  rw [translated_right,Nat.mod_eq_of_lt h.1,h.2]

/-- Complete original `native_parity_same` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem native_parity_same (L x : ℕ) : ((x+2)%(L*2))%2=x%2 := by
  rw [Nat.mod_mul_left_mod]
  omega

#print axioms native_box_same
#print axioms native_parity_same
/-- Construction for right in the partial address matched grid model. -/
def right (d r : ℕ) (axis : Fin d) (x : Fin d → Fin (2^r)) : Fin d → Fin (2^r) :=
  Function.update x axis (x axis+2)

/-- Complete original `matching_key_same` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_key_same (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (offset : Fin d → Fin (C*ell))
    (axis : Fin d) (x : Fin d → Fin (2^r))
    (hell : 0<ell) (heven : ell%2=0)
    (hpar : (((C*ell-(offset axis).val)+(x axis).val/2)%(C*ell))%2=0) :
    (GridPatch.nativeGridEquiv C ell d r hN offset (right d r axis x)).1=
      (GridPatch.nativeGridEquiv C ell d r hN offset x).1 := by
  funext i
  by_cases hi : i=axis
  · subst i
    have hL : 0<C*ell := Nat.pos_of_ne_zero (NeZero.ne _)
    have hv : (right d r axis x axis).val=((x axis).val+2)%(C*ell*2) := by
      simp only [right,Function.update_self,Fin.val_add,Fin.coe_ofNat_eq_mod,Nat.add_mod_mod,hN]
    apply Prod.ext <;> apply Fin.ext
    · change (right d r axis x axis).val%2=(x axis).val%2
      rw [hv]
      exact native_parity_same (C*ell) (x axis).val
    · change (((C*ell-(offset axis).val)+(right d r axis x axis).val/2)%(C*ell))/ell=
        (((C*ell-(offset axis).val)+(x axis).val/2)%(C*ell))/ell
      rw [hv]
      exact native_box_same C ell (offset axis).val (x axis).val hell heven hL hpar
  · change (GridPatch.coordinateEquiv C ell (offset i) (Fin.cast hN (right d r axis x i))).1=
      (GridPatch.coordinateEquiv C ell (offset i) (Fin.cast hN (x i))).1
    simp only [right,Function.update_of_ne hi]

#print axioms matching_key_same
/-- Complete original `cleared_left_parity` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem cleared_left_parity (L c x : ℕ) (hL : 0<L) (heven : L%2=0) (hc : c<2) :
    ((L-c+(x%2+4*(x/4)+2*c)%(L*2)/2)%L)%2=0 := by
  have hcle : c ≤ L := by omega
  have hd : 2 ∣ L := Nat.dvd_of_mod_eq_zero heven
  have hcoarse : (x%2+4*(x/4)+2*c)%(L*2)/2=(2*(x/4)+c)%L := by
    rw [Nat.mod_mul_left_div_self]
    congr 1
    omega
  rw [hcoarse,Nat.add_mod_mod]
  have he : L-c+(2*(x/4)+c)=L+2*(x/4) := by omega
  rw [he,Nat.add_mod_left,Nat.mod_mod_of_dvd _ hd]
  omega

/-- Construction for canonical Left in the partial address matched grid model. -/
def canonicalLeft (d r : ℕ) (axis : Fin d) (color : Fin 2)
    (x : Fin d → Fin (2^r)) : Fin d → Fin (2^r) :=
  Function.update x axis
    ⟨((x axis).val%2+4*((x axis).val/4)+2*color.val)%(2^r),
      Nat.mod_lt _ (by positivity)⟩

/-- Construction for color Offset in the partial address matched grid model. -/
def colorOffset (L d : ℕ) (axis : Fin d) (color : Fin 2) (hL : 2 ≤ L) : Fin d → Fin L :=
  fun j => if j=axis then ⟨color.val,by omega⟩ else ⟨0,by omega⟩

/-- Complete original `canonical_left_parity` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem canonical_left_parity (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (axis : Fin d) (color : Fin 2) (x : Fin d → Fin (2^r))
    (heven : ell%2=0) (hL : 2 ≤ C*ell) :
    (((C*ell-(colorOffset (C*ell) d axis color hL axis).val)+
      (canonicalLeft d r axis color x axis).val/2)%(C*ell))%2=0 := by
  have hp : 0<C*ell := Nat.pos_of_ne_zero (NeZero.ne _)
  have he : (C*ell)%2=0 := by simp only [Nat.mul_mod,heven,mul_zero,Nat.zero_mod]
  simpa only [colorOffset,ite_eq_left rfl,ite_true,canonicalLeft,Function.update_self,hN] using
    cleared_left_parity (C*ell) color.val (x axis).val hp he color.isLt

/-- Complete original `canonical_matching_same_box` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem canonical_matching_same_box (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (axis : Fin d) (color : Fin 2) (x : Fin d → Fin (2^r))
    (hell : 0<ell) (heven : ell%2=0) (hL : 2 ≤ C*ell) :
    let offset := colorOffset (C*ell) d axis color hL
    let left := canonicalLeft d r axis color x
    (GridPatch.nativeGridEquiv C ell d r hN offset (right d r axis left)).1=
      (GridPatch.nativeGridEquiv C ell d r hN offset left).1 := by
  dsimp only
  exact matching_key_same C ell d r hN _ axis _ hell heven
    (canonical_left_parity C ell d r hN axis color x heven hL)

#print axioms cleared_left_parity
#print axioms canonical_left_parity
#print axioms canonical_matching_same_box
/-- Complete original `half_grid_two` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem half_grid_two (C ell : ℕ) [NeZero (C*ell)] (heven : ell%2=0) :
    2 ≤ C*ell := by
  have hp : 0<C*ell := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm : (C*ell)%2=0 := by simp only [Nat.mul_mod,heven,mul_zero,Nat.zero_mod]
  omega

/-- Construction for matching Offset in the partial address matched grid model. -/
def matchingOffset (C ell : ℕ) [NeZero (C*ell)] (d : ℕ)
    (axis : Fin d) (color : Fin 2) (heven : ell%2=0) : Fin d → Fin (C*ell) :=
  colorOffset (C*ell) d axis color (half_grid_two C ell heven)

/-- Complete original `selected_matching_same_box` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem selected_matching_same_box (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (axis : Fin d) (color : Fin 2) (x : Fin d → Fin (2^r))
    (hell : 0<ell) (heven : ell%2=0) :
    let offset := matchingOffset C ell d axis color heven
    let left := canonicalLeft d r axis color x
    (GridPatch.nativeGridEquiv C ell d r hN offset (right d r axis left)).1=
      (GridPatch.nativeGridEquiv C ell d r hN offset left).1 := by
  exact canonical_matching_same_box C ell d r hN axis color x hell heven
    (half_grid_two C ell heven)

#print axioms half_grid_two
#print axioms selected_matching_same_box
open Qatlib ShiftCircuit

/-- Complete original `axis_clear_second` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem axis_clear_second (lo hi : Bool) (tail : List Bool) :
    axisValue (lo::false::tail)=
      axisValue (lo::hi::tail)%2+4*(axisValue (lo::hi::tail)/4) := by
  cases lo <;> cases hi <;> simp only [axisValue,Bool.toNat_false,Bool.toNat_true] <;> omega

/-- Complete original `clear_bit_one_address` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem clear_bit_one_address (r : ℕ) (bits : Fin (r+2) → Bool) :
    (littleAddress (r+2) (Function.update bits ⟨1,by omega⟩ false)).val=
      (littleAddress (r+2) bits).val%2+4*((littleAddress (r+2) bits).val/4) := by
  have hlist : List.ofFn (Function.update bits ⟨1,by omega⟩ false)=
      bits 0::false::List.ofFn (fun i : Fin r => bits i.succ.succ) := by
    rw [List.ofFn_succ,List.ofFn_succ]
    apply congrArg₂ List.cons
    · apply Function.update_of_ne
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    · apply congrArg₂ List.cons
      · exact Function.update_self _ _ _
      · apply congrArg List.ofFn
        funext i
        apply Function.update_of_ne
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ] at hv
        omega
  change axisValue (List.ofFn (Function.update bits ⟨1,by omega⟩ false))=_
  rw [hlist]
  have horig : List.ofFn bits=bits 0::bits ⟨1,by omega⟩::List.ofFn (fun i : Fin r => bits i.succ.succ) := by
    rw [List.ofFn_succ,List.ofFn_succ]
    rfl
  change _=axisValue (List.ofFn bits)%2+4*(axisValue (List.ofFn bits)/4)
  rw [horig]
  exact axis_clear_second _ _ _

#print axioms axis_clear_second
#print axioms clear_bit_one_address
/-- Complete original `canonical_left_readout` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem canonical_left_readout (d r : ℕ) (axis : Fin d) (color : Fin 2)
    (bits : Fin d → Fin (r+2) → Bool) :
    (canonicalLeft d (r+2) axis color (fun j => littleAddress (r+2) (bits j)) axis).val=
      ((littleAddress (r+2) (Function.update (bits axis) ⟨1,by omega⟩ false)).val+
        2*color.val)%(2^(r+2)) := by
  simp only [canonicalLeft,Function.update_self,clear_bit_one_address]

#print axioms canonical_left_readout
/-- Complete original `matching_offset_value` guarantee for `PartialAddressMatchedGrid`; all source hypotheses and output obligations are retained. -/
theorem matching_offset_value (C ell : ℕ) [NeZero (C*ell)] (d : ℕ)
    (axis : Fin d) (color : Fin 2) (heven : ell%2=0) (j : Fin d) :
    (matchingOffset C ell d axis color heven j).val=color.val*(if j=axis then 1 else 0) := by
  by_cases h : j=axis <;> simp only [matchingOffset,colorOffset,h,ite_true,ite_false,mul_one,mul_zero]

#print axioms matching_offset_value
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.MatchedGrid
