/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.ElementaryRelations
import Mathlib.GroupTheory.OrderOfElement
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition7

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

variable {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)

local notation "u" => canonicalUnit p r hp hr

local notation "hu" => canonicalUnit_pow_eq_one p r hp hp2 hr

theorem canonicalX_eq_px : canonicalX p r hp hp2 hr = px p r u hu 1 := rfl

theorem canonicalY_eq_py : canonicalY p r hp hp2 hr = py p r u hu 1 := rfl

theorem proposition7_x_order : orderOf (canonicalX p r hp hp2 hr) = p ^ r := by
  rw [canonicalX_eq_px, px]
  rw [orderOf_injective (SemidirectProduct.inl : Cyc (p ^ r) →*
      Ppr p r u hu) SemidirectProduct.inl_injective]
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem proposition7_y_order : orderOf (canonicalY p r hp hp2 hr) = p := by
  rw [canonicalY_eq_py, py]
  rw [orderOf_injective (SemidirectProduct.inr : Cyc p →*
      Ppr p r u hu) SemidirectProduct.inr_injective]
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem zpowers_ofAdd_one_top (hp : p.Prime) :
    Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod (p ^ r))) = ⊤ := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(Multiplicative.toAdd x).val, ?_⟩
  rw [zpow_natCast]
  rw [show (Multiplicative.ofAdd (1 : ZMod (p^r)) : Cyc (p^r)) ^
      (Multiplicative.toAdd x).val
      = Multiplicative.ofAdd ((Multiplicative.toAdd x).val • (1 : ZMod (p^r)))
      from rfl]
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem px_eq_x_pow (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (a : ZMod (p ^ r)) :
    px p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr) a
      = (canonicalX p r hp hp2 hr) ^ a.val := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  conv_lhs => rw [show a = ((a.val : ℕ) : ZMod (p ^ r)) from (ZMod.natCast_zmod_val a).symm]
  rw [show ((a.val : ℕ) : ZMod (p ^ r)) = a.val * (1 : ZMod (p ^ r))
      from (mul_one _).symm]
  rw [← px_pow, ← canonicalX_eq_px]

theorem py_eq_y_pow (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r) (b : ZMod p) :
    py p r (canonicalUnit p r hp hr) (canonicalUnit_pow_eq_one p r hp hp2 hr) b
      = (canonicalY p r hp hp2 hr) ^ b.val := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  conv_lhs => rw [show b = ((b.val : ℕ) : ZMod p) from (ZMod.natCast_zmod_val b).symm]
  rw [show ((b.val : ℕ) : ZMod p) = b.val * (1 : ZMod p) from (mul_one _).symm]
  rw [← py_pow, ← canonicalY_eq_py]

theorem proposition7_cyclic_eq_ker :
    Subgroup.zpowers (canonicalX p r hp hp2 hr)
      = (SemidirectProduct.rightHom : Ppr p r u hu →* Cyc p).ker := by
  have hmap := MonoidHom.map_zpowers (SemidirectProduct.inl : Cyc (p ^ r) →* Ppr p r u hu)
    (Multiplicative.ofAdd (1 : ZMod (p ^ r)))
  rw [canonicalX_eq_px, px, ← hmap]
  rw [zpowers_ofAdd_one_top hp, ← MonoidHom.range_eq_map]
  exact SemidirectProduct.range_inl_eq_ker_rightHom

theorem proposition7_cyclic_normal :
    (Subgroup.zpowers (canonicalX p r hp hp2 hr)).Normal := by
  rw [proposition7_cyclic_eq_ker hp hp2 hr]
  infer_instance

theorem proposition7_cyclic_commutative (a b : Ppr p r u hu)
    (ha : a ∈ Subgroup.zpowers (canonicalX p r hp hp2 hr))
    (hb : b ∈ Subgroup.zpowers (canonicalX p r hp hp2 hr)) : a * b = b * a := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  rw [← zpow_add, ← zpow_add]
  congr 1
  omega

theorem proposition7_generates :
    Subgroup.closure ({canonicalX p r hp hp2 hr, canonicalY p r hp hp2 hr} : Set
      (Ppr p r u hu)) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hxmem : canonicalX p r hp hp2 hr ∈
      Subgroup.closure ({canonicalX p r hp hp2 hr, canonicalY p r hp hp2 hr} : Set
        (Ppr p r u hu)) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hymem : canonicalY p r hp hp2 hr ∈
      Subgroup.closure ({canonicalX p r hp hp2 hr, canonicalY p r hp hp2 hr} : Set
        (Ppr p r u hu)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hnf : g = px p r u hu g.left.toAdd * py p r u hu g.right.toAdd :=
    normal_form u hu g
  rw [hnf]
  apply Subgroup.mul_mem
  · rw [px_eq_x_pow hp hp2 hr]
    exact Subgroup.pow_mem _ hxmem _
  · rw [py_eq_y_pow hp hp2 hr]
    exact Subgroup.pow_mem _ hymem _

theorem proposition7_cyclic_subgroup_generator
    (L : Subgroup (Ppr p r u hu))
    (hL : L ≤ Subgroup.zpowers (canonicalX p r hp hp2 hr)) :
    ∃ n : ℕ, L = Subgroup.zpowers ((canonicalX p r hp hp2 hr) ^ n) :=
  (Subgroup.le_zpowers_iff (canonicalX p r hp hp2 hr) L).mp hL

end Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition7
