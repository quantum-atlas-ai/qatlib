/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Mathlib.Algebra.Group.Equiv.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Model

def diagMulAut (m n : ℕ) (u : (ZMod n)ˣ) : MulAut (Fin m → Cyc n) :=
  MulEquiv.piCongrRight (fun _ => unitMulAut n u)

@[simp]
theorem diagMulAut_apply (m n : ℕ) (u : (ZMod n)ˣ) (f : Fin m → Cyc n) (i : Fin m) :
    diagMulAut m n u f i = unitMulAut n u (f i) := rfl

def diagonalAction (m q n : ℕ) (u : (ZMod n)ˣ) (hu : u ^ q = 1) :
    Cyc q →* MulAut (Fin m → Cyc n) :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift q
      ⟨zmultiplesHom (Additive (MulAut (Fin m → Cyc n)))
          (Additive.ofMul (diagMulAut m n u)), by
        have hpowu : (unitMulAut n u) ^ q = 1 := by
          change (unitMulAutHom n u) ^ q = 1
          rw [← map_pow, hu, map_one]
        have hiter : ∀ k,
            (MulEquiv.piCongrRight (fun _ : Fin m => unitMulAut n u)) ^ k
              = MulEquiv.piCongrRight (fun _ : Fin m => (unitMulAut n u) ^ k) := by
          intro k; induction k with
          | zero =>
            show (1 : MulAut (Fin m → Cyc n)) = MulEquiv.piCongrRight (fun _ => 1)
            rw [show (fun _ : Fin m => (1 : MulAut (Cyc n)))
                  = (fun _ => MulEquiv.refl (Cyc n)) from rfl,
              MulEquiv.piCongrRight_refl, MulAut.one_def]
          | succ k ih =>
            rw [pow_succ, ih]
            ext x i
            simp [MulAut.mul_apply, MulEquiv.piCongrRight_apply, pow_succ]
        have hpow : (diagMulAut m n u) ^ q = 1 := by
          unfold diagMulAut
          rw [hiter, hpowu]
          show MulEquiv.piCongrRight (fun _ : Fin m => (1 : MulAut (Cyc n))) = 1
          rw [show (fun _ : Fin m => (1 : MulAut (Cyc n)))
                = (fun _ => MulEquiv.refl (Cyc n)) from rfl,
            MulEquiv.piCongrRight_refl, MulAut.one_def]
        rw [zmultiplesHom_apply, ← ofMul_zpow, zpow_natCast, hpow, ofMul_one]⟩)

abbrev PprM (m p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) : Type :=
  (Fin m → Cyc (p ^ r)) ⋊[diagonalAction m p (p ^ r) u hu] Cyc p

def zGen (m p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (i : Fin m) :
    PprM m p r u hu :=
  SemidirectProduct.inl (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (p ^ r))))

def wGen (m p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) :
    PprM m p r u hu :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod p))

end Qatlib.Papers.SemiDirectHSP04.MainResults.Model
