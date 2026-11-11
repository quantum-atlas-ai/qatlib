/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
Explicit translated boxes for the original dyadic grid. The bijection splits
coordinate parity, translates the half-grid by the known color offset, then
splits box/local coordinates. This relabels classical address outcomes; it is
not an uncharged physical permutation. Matching-edge closure and its spatial
Poincare bound are separate from this pilot-address partition.
-/
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.GridPatch
variable (C ell : ℕ) [NeZero (C*ell)]

/-- Construction for coordinate Equiv in the partial address grid patch model. -/
def coordinateEquiv (c : Fin (C*ell)) :
    Fin (C*ell*2) ≃ (Fin 2 × Fin C) × Fin ell where
  toFun x :=
    let coarseParity := (finProdFinEquiv (m:=C*ell) (n:=2)).symm x
    let boxLocal := (finProdFinEquiv (m:=C) (n:=ell)).symm (coarseParity.1-c)
    ((coarseParity.2,boxLocal.1),boxLocal.2)
  invFun y := finProdFinEquiv (finProdFinEquiv (y.1.2,y.2)+c,y.1.1)
  left_inv x := by
    simp only [Equiv.apply_symm_apply,sub_add_cancel,Prod.mk.eta]
  right_inv y := by
    simp only [Equiv.symm_apply_apply,add_sub_cancel_right,Prod.mk.eta]

/-- Complete original `coordinate_parity` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem coordinate_parity (c : Fin (C*ell)) (x : Fin (C*ell*2)) :
    ((coordinateEquiv C ell c x).1.1 : ℕ)=x.val%2 := rfl

/-- Complete original `coordinate_box` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem coordinate_box (c : Fin (C*ell)) (x : Fin (C*ell*2)) :
    ((coordinateEquiv C ell c x).1.2 : ℕ)=
      (((C*ell-c.val)+x.val/2)%(C*ell))/ell := rfl

/-- Complete original `coordinate_local` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem coordinate_local (c : Fin (C*ell)) (x : Fin (C*ell*2)) :
    ((coordinateEquiv C ell c x).2 : ℕ)=
      (((C*ell-c.val)+x.val/2)%(C*ell))%ell := rfl

#print axioms coordinateEquiv
/-- Construction for grid Equiv in the partial address grid patch model. -/
def gridEquiv (d : ℕ) (offset : Fin d → Fin (C*ell)) :
    (Fin d → Fin (C*ell*2)) ≃ ((Fin d → Fin 2 × Fin C) × (Fin d → Fin ell)) where
  toFun x := (fun j => (coordinateEquiv C ell (offset j) (x j)).1,
    fun j => (coordinateEquiv C ell (offset j) (x j)).2)
  invFun y := fun j => (coordinateEquiv C ell (offset j)).symm (y.1 j,y.2 j)
  left_inv x := by
    funext j
    exact (coordinateEquiv C ell (offset j)).symm_apply_apply (x j)
  right_inv y := by
    apply Prod.ext <;> funext j
    · exact congrArg Prod.fst ((coordinateEquiv C ell (offset j)).apply_symm_apply (y.1 j,y.2 j))
    · exact congrArg Prod.snd ((coordinateEquiv C ell (offset j)).apply_symm_apply (y.1 j,y.2 j))

/-- Complete original `grid_key_formula` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem grid_key_formula (d : ℕ) (offset : Fin d → Fin (C*ell))
    (x : Fin d → Fin (C*ell*2)) (j : Fin d) :
    (((gridEquiv C ell d offset x).1 j).1.val,
      ((gridEquiv C ell d offset x).1 j).2.val)=
      ((x j).val%2,(((C*ell-(offset j).val)+(x j).val/2)%(C*ell))/ell) := rfl

omit [NeZero (C*ell)] in
/-- Complete original `box_card` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem box_card (d : ℕ) : Fintype.card (Fin d → Fin 2 × Fin C)=(2*C)^d := by simp

omit [NeZero (C*ell)] in
/-- Complete original `local_card` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem local_card (d : ℕ) : Fintype.card (Fin d → Fin ell)=ell^d := by simp

#print axioms gridEquiv
#print axioms grid_key_formula
#print axioms box_card
#print axioms local_card
omit [NeZero (C*ell)] in
/-- Complete original `dyadic_side` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem dyadic_side (s t : ℕ) : (2^t*2^s)*2=2^(s+t+1) := by
  simp only [pow_add,pow_one]
  ring

/-- Construction for native Grid Equiv in the partial address grid patch model. -/
def nativeGridEquiv (d r : ℕ) (hN : 2^r=C*ell*2) (offset : Fin d → Fin (C*ell)) :
    (Fin d → Fin (2^r)) ≃ ((Fin d → Fin 2 × Fin C) × (Fin d → Fin ell)) :=
  (Equiv.piCongrRight (fun _ : Fin d => finCongr hN)).trans (gridEquiv C ell d offset)

/-- Complete original `native_key_formula` guarantee for `PartialAddressGridPatch`; all source hypotheses and output obligations are retained. -/
theorem native_key_formula (d r : ℕ) (hN : 2^r=C*ell*2)
    (offset : Fin d → Fin (C*ell)) (x : Fin d → Fin (2^r)) (j : Fin d) :
    (((nativeGridEquiv C ell d r hN offset x).1 j).1.val,
      ((nativeGridEquiv C ell d r hN offset x).1 j).2.val)=
      ((x j).val%2,(((C*ell-(offset j).val)+(x j).val/2)%(C*ell))/ell) := rfl

#print axioms coordinate_parity
#print axioms coordinate_box
#print axioms coordinate_local
#print axioms dyadic_side
#print axioms nativeGridEquiv
#print axioms native_key_formula
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.GridPatch
