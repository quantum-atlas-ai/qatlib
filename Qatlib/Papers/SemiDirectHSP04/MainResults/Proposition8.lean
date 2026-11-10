/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition7
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition8

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model
open Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition7

variable {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 2 ≤ r)

local notation "u" => canonicalUnit p r hp hr
local notation "hu" => canonicalUnit_pow_eq_one p r hp hp2 hr

theorem px_injective :
    Function.Injective (px p r (canonicalUnit p r hp hr)
      (canonicalUnit_pow_eq_one p r hp hp2 hr)) := by
  intro a b h
  have h2 : Multiplicative.ofAdd a = Multiplicative.ofAdd b := by
    have := congrArg (fun g : Ppr p r u hu => g.left) h
    simpa [px] using this
  exact Multiplicative.ofAdd.injective h2

theorem canonicalUnit_coe_ne_one :
    ((canonicalUnit p r hp hr : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) ≠ 1 := by
  rw [canonicalUnit_coe p r hp hr]
  intro h
  have hz : ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) = 0 := by
    have h' : 1 + ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) - 1 = 1 - 1 := by rw [h]
    simpa using h'
  rw [ZMod.natCast_eq_zero_iff] at hz
  have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
  have hlt : p ^ (r - 1) < p ^ r :=
    pow_lt_pow_right₀ hp.one_lt (by omega)
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hz

theorem proposition8_nonabelian :
    canonicalX p r hp hp2 hr * canonicalY p r hp hp2 hr
      ≠ canonicalY p r hp hp2 hr * canonicalX p r hp hp2 hr := by
  intro h
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.pos.ne'⟩

  have hleft := congrArg (fun g : Ppr p r u hu => g.left) h

  have hxy : (canonicalX p r hp hp2 hr * canonicalY p r hp hp2 hr).left
      = Multiplicative.ofAdd (1 : ZMod (p ^ r)) := by
    simp [canonicalX_eq_px, canonicalY_eq_py, px, py,
      SemidirectProduct.mul_left]

  have hyx : (canonicalY p r hp hp2 hr * canonicalX p r hp hp2 hr).left
      = Multiplicative.ofAdd ((canonicalUnit p r hp hr : ZMod (p ^ r))) := by
    rw [canonicalY_eq_py, canonicalX_eq_px, py_mul_px]
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    simp [px, py, ZMod.val_one]
  have hone : (1 : ZMod (p ^ r))
      = (canonicalUnit p r hp hr : ZMod (p ^ r)) := by
    apply Multiplicative.ofAdd.injective
    rw [← hxy, ← hyx]
    exact hleft
  exact canonicalUnit_coe_ne_one hp hr hone.symm

theorem proposition8_cyclic_subgroup_abelian
    (K : Subgroup (Ppr p r u hu))
    (hK : K ≤ Subgroup.zpowers (canonicalX p r hp hp2 hr)) :
    ∀ a b : K, a * b = b * a := by
  intro a b
  apply Subtype.ext
  exact proposition7_cyclic_commutative hp hp2 hr (a : Ppr p r u hu) (b : Ppr p r u hu)
    (hK a.property) (hK b.property)

end Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition8
