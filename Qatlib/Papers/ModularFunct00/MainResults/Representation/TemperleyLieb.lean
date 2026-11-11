/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Representation.JonesSpectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Algebra.Basic

/-!
# Temperley-Lieb relations for Jones generators

This module derives the braid relation for `jonesGen` from idempotence and the stated
Temperley-Lieb relations. It also proves the inverse formula for reciprocal scalar parameters.

For self-adjoint idempotents and unit-modulus parameters, the generator and its adjoint multiply
to the identity in either order, giving the algebraic unitarity calculation used in
[FreedmanLarsenWang2000].

## Main statements

* `jonesGen_braid_pair`: Temperley-Lieb relations imply the generator braid relation.
* `jonesGen_star`: Conjugating the parameter gives the adjoint generator.
* `jonesGen_mul_star`: A generator times its adjoint is the identity under the stated
  hypotheses.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Module
open Module.End

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- For idempotent `e` and reciprocal parameters `r * q = 1`, the product `jonesGen q e *
jonesGen r e` is the identity; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_mul_jonesGen (q r : ℂ) (e : Module.End ℂ V) (he : e * e = e)
    (hrq : r * q = 1) :
    jonesGen q e * jonesGen r e = 1 := by
  have hee : ∀ x : V, e (e x) = e x := fun x => by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f x) he
  have hcoef : r * (1 + q) + (1 + r) * q - (1 + r) * (1 + q) = 0 := by
    linear_combination hrq
  ext x
  simp only [Module.End.mul_apply, jonesGen_apply, map_sub, map_smul, hee]
  rw [show r • (q • x - (1 + q) • e x) - (1 + r) • (q • e x - (1 + q) • e x)
      = (r * q) • x
        - (r * (1 + q) + (1 + r) * q - (1 + r) * (1 + q)) • e x by module]
  rw [hrq, hcoef]
  simp

/-- Two idempotents satisfying the stated Temperley-Lieb and scalar relations yield Jones
generators satisfying the braid relation; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_braid_pair (q β γ : ℂ) (a b : Module.End ℂ V)
    (ha : a * a = a) (hb : b * b = b)
    (haba : a * b * a = γ • a) (hbab : b * a * b = γ • b)
    (hβ : (1 + q) ^ 2 = q * β) (hγ : γ * β = 1) :
    jonesGen q a * jonesGen q b * jonesGen q a =
      jonesGen q b * jonesGen q a * jonesGen q b := by
  have haa : ∀ x : V, a (a x) = a x := fun x => by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f x) ha
  have hbb : ∀ x : V, b (b x) = b x := fun x => by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f x) hb
  have haba' : ∀ x : V, a (b (a x)) = γ • a x := fun x => by
    have h := congrArg (fun f : Module.End ℂ V => f x) haba
    simpa [Module.End.mul_apply] using h
  have hbab' : ∀ x : V, b (a (b x)) = γ • b x := fun x => by
    have h := congrArg (fun f : Module.End ℂ V => f x) hbab
    simpa [Module.End.mul_apply] using h
  have hβγ : β * γ = 1 := by rw [mul_comm]; exact hγ

  have hc3 : (1 + q) * ((1 + q) * ((1 + q) * γ)) = q * (1 + q) := by
    calc (1 + q) * ((1 + q) * ((1 + q) * γ))
        = ((1 + q) * (1 + q) * (1 + q)) * γ := by ring
      _ = ((1 + q) ^ 2 * (1 + q)) * γ := by ring
      _ = ((q * β) * (1 + q)) * γ := by rw [hβ]
      _ = q * (1 + q) * (β * γ) := by ring
      _ = q * (1 + q) := by rw [hβγ]; ring
  ext x
  simp only [Module.End.mul_apply, jonesGen_apply, map_sub, map_smul,
    haa, hbb, haba', hbab']
  simp only [smul_sub, smul_smul, hc3]
  module

end Algebra

section Star

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- For self-adjoint `e`, the adjoint of `jonesGen q e` is `jonesGen (star q) e`; see
[FreedmanLarsenWang2000]. -/
theorem jonesGen_star (q : ℂ) (e : Module.End ℂ V) (hstar : star e = e) :
    star (jonesGen q e) = jonesGen (star q) e := by
  have hstar_add : star (1 + q : ℂ) = 1 + star q := by simp
  rw [jonesGen, jonesGen, star_sub, star_smul, star_smul, hstar_add, star_one, hstar]

/-- For self-adjoint idempotent `e` and `star q * q = 1`, the product of `jonesGen q e` with its
adjoint is the identity; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_mul_star (q : ℂ) (e : Module.End ℂ V) (he : e * e = e)
    (hstar : star e = e) (hq : star q * q = 1) :
    jonesGen q e * star (jonesGen q e) = 1 := by
  rw [jonesGen_star q e hstar]
  exact jonesGen_mul_jonesGen q (star q) e he hq

/-- For self-adjoint idempotent `e` and `star q * q = 1`, the product of the adjoint of
`jonesGen q e` with the generator is the identity; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_star_mul (q : ℂ) (e : Module.End ℂ V) (he : e * e = e)
    (hstar : star e = e) (hq : star q * q = 1) :
    star (jonesGen q e) * jonesGen q e = 1 := by
  rw [jonesGen_star q e hstar]
  exact jonesGen_mul_jonesGen (star q) q e he (by
    rw [mul_comm]; exact hq)

end Star

end Qatlib.Papers.ModularFunct00.MainResults.Representation
