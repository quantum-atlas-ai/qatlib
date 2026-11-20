/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressNativePilot

@[expose] public section

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

/-- For positive even `ell` and even `y`, the local remainder of `y` can be incremented by one
while staying below `ell`. -/
theorem pair_local_lt (ell y : ℕ) (hell : 0<ell) (heven : ell%2=0) (hy : y%2=0) :
    y%ell+1<ell := by
  have hd : 2 ∣ ell := Nat.dvd_of_mod_eq_zero heven
  have hm : (y%ell)%2=0 := by rw [Nat.mod_mod_of_dvd y hd]; exact hy
  have hl := Nat.mod_lt y hell
  omega

/-- In a grid split into blocks of positive even length, an even in-range index and its
successor both lie in range and have the same block quotient. -/
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

/-- Adding two modulo `2L` before dropping the parity bit gives the same half-index as
incrementing `x/2` modulo `L`. -/
theorem coarse_right (L x : ℕ) : ((x+2)%(L*2))/2=(x/2+1)%L := by
  rw [Nat.mod_mul_left_div_self]
  congr 1
  omega

/-- After subtracting the offset cyclically, the half-index of the two-site shift is the
successor modulo `L` of the original translated half-index. -/
theorem translated_right (L c x : ℕ) :
    ((L-c)+((x+2)%(L*2))/2)%L=(((L-c)+x/2)%L+1)%L := by
  rw [coarse_right,Nat.add_mod_mod,Nat.mod_add_mod]
  congr 1

#print axioms pair_local_lt
#print axioms pair_box_step
#print axioms coarse_right
#print axioms translated_right
/-- For positive even block length and positive half-grid size, a modular two-site shift from
an even translated half-index preserves its block quotient. -/
theorem native_box_same (C ell c x : ℕ) (hell : 0<ell) (heven : ell%2=0)
    (hL : 0<C*ell) (hpar : (((C*ell-c)+x/2)%(C*ell))%2=0) :
    (((C*ell-c)+((x+2)%(C*ell*2))/2)%(C*ell))/ell=
      (((C*ell-c)+x/2)%(C*ell))/ell := by
  have h := pair_box_step C ell (((C*ell-c)+x/2)%(C*ell)) hell heven
    (Nat.mod_lt _ hL) hpar
  rw [translated_right,Nat.mod_eq_of_lt h.1,h.2]

/-- Adding two and reducing modulo the even side length preserves the original parity bit. -/
theorem native_parity_same (L x : ℕ) : ((x+2)%(L*2))%2=x%2 := by
  rw [Nat.mod_mul_left_mod]
  omega

#print axioms native_box_same
#print axioms native_parity_same
/-- Construction for right in the partial address matched grid model. -/
def right (d r : ℕ) (axis : Fin d) (x : Fin d → Fin (2^r)) : Fin d → Fin (2^r) :=
  Function.update x axis (x axis+2)

/-- On a native grid of side `2^r = 2 * C * ell`, assume positive even box side `ell` and an
even translated half-index on the matching axis. The native point and its periodic two-site
right neighbor then have the same box key. -/
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
/-- For a positive even half-grid size and `c < 2`, putting `c` in the second-lowest bit of the
native index makes the translated half-index even after subtracting `c` modulo the half-grid
size. -/
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

/-- With even box side and half-grid size at least two, the canonical left endpoint has even
translated half-index along the chosen axis at the color offset. -/
theorem canonical_left_parity (C ell : ℕ) [NeZero (C*ell)] (d r : ℕ)
    (hN : 2^r=C*ell*2) (axis : Fin d) (color : Fin 2) (x : Fin d → Fin (2^r))
    (heven : ell%2=0) (hL : 2 ≤ C*ell) :
    (((C*ell-(colorOffset (C*ell) d axis color hL axis).val)+
      (canonicalLeft d r axis color x axis).val/2)%(C*ell))%2=0 := by
  have hp : 0<C*ell := Nat.pos_of_ne_zero (NeZero.ne _)
  have he : (C*ell)%2=0 := by simp only [Nat.mul_mod,heven,mul_zero,Nat.zero_mod]
  simpa only [colorOffset,ite_eq_left rfl,ite_true,canonicalLeft,Function.update_self,hN] using
    cleared_left_parity (C*ell) color.val (x axis).val hp he color.isLt

/-- On a native grid of side `2^r = 2 * C * ell`, assume a positive even box side and
`2 ≤ C * ell`. At the corresponding color offset, a canonical left endpoint and its periodic
two-site right neighbor map to the same box. -/
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
/-- A nonzero half-grid size `C*ell` with even `ell` is at least two, so both color offsets
fit. -/
theorem half_grid_two (C ell : ℕ) [NeZero (C*ell)] (heven : ell%2=0) :
    2 ≤ C*ell := by
  have hp : 0<C*ell := Nat.pos_of_ne_zero (NeZero.ne _)
  have hm : (C*ell)%2=0 := by simp only [Nat.mul_mod,heven,mul_zero,Nat.zero_mod]
  omega

/-- Construction for matching Offset in the partial address matched grid model. -/
def matchingOffset (C ell : ℕ) [NeZero (C*ell)] (d : ℕ)
    (axis : Fin d) (color : Fin 2) (heven : ell%2=0) : Fin d → Fin (C*ell) :=
  colorOffset (C*ell) d axis color (half_grid_two C ell heven)

/-- For a grid of side `2^r = 2 * C * ell` and positive even box side `ell`, the selected
matching offset sends the canonical left endpoint and its periodic two-site right neighbor
to the same box. -/
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

/-- Clearing the second little-endian bit preserves the low bit and all bits at positions two
and above, yielding `x % 2 + 4*(x/4)` for the original value `x`. -/
theorem axis_clear_second (lo hi : Bool) (tail : List Bool) :
    axisValue (lo::false::tail)=
      axisValue (lo::hi::tail)%2+4*(axisValue (lo::hi::tail)/4) := by
  cases lo <;> cases hi <;> simp only [axisValue,Bool.toNat_false,Bool.toNat_true] <;> omega

/-- Updating bit one of a little-endian address to false reduces its value to the low bit plus
four times the original quotient by four. -/
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
/-- On the chosen axis, the canonical left coordinate is the address with bit one cleared, plus
twice the color, reduced modulo the native side length. -/
theorem canonical_left_readout (d r : ℕ) (axis : Fin d) (color : Fin 2)
    (bits : Fin d → Fin (r+2) → Bool) :
    (canonicalLeft d (r+2) axis color (fun j => littleAddress (r+2) (bits j)) axis).val=
      ((littleAddress (r+2) (Function.update (bits axis) ⟨1,by omega⟩ false)).val+
        2*color.val)%(2^(r+2)) := by
  simp only [canonicalLeft,Function.update_self,clear_bit_one_address]

#print axioms canonical_left_readout
/-- The matching offset has the color value on the matching axis and zero on every other axis. -/
theorem matching_offset_value (C ell : ℕ) [NeZero (C*ell)] (d : ℕ)
    (axis : Fin d) (color : Fin 2) (heven : ell%2=0) (j : Fin d) :
    (matchingOffset C ell d axis color heven j).val=color.val*(if j=axis then 1 else 0) := by
  by_cases h : j=axis <;> simp only [matchingOffset,colorOffset,h,ite_true,ite_false,mul_one,mul_zero]

#print axioms matching_offset_value
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.MatchedGrid
