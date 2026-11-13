/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Trace coordinates over finite fields

The trace pairing against a basis over the prime field defines a bijective coordinate map. The
module proves its reversibility and records a polynomial bound for the cubic linear solve cost
used in the trace Fourier construction. See [VanDamHallgren2000].

## Main statements

* `lemma2_traceFourier_bijective`: The trace coordinate map associated with a basis of `F` over
  its prime field is bijective.
* `lemma2_traceFourier_reversible`: The trace coordinate map associated with `hb` possesses a
  left inverse.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

/-- The map sending `x` to the trace coordinates `Tr(x * hb i)` is injective over the finite
field `F`. See [VanDamHallgren2000]. -/
theorem lemma2_traceFourier_injective
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod (ringChar F)) F]
    (hb : Module.Basis (Fin (Module.finrank (ZMod (ringChar F)) F))
        (ZMod (ringChar F)) F) :
    Function.Injective
      (fun x : F =>
        fun i : Fin (Module.finrank (ZMod (ringChar F)) F) =>
          Algebra.trace (ZMod (ringChar F)) F (x * hb i)) := by
  intro x y hxy

  have hzero : ∀ i, Algebra.trace (ZMod (ringChar F)) F ((x - y) * hb i) = 0 := by
    intro i
    rw [sub_mul, map_sub, sub_eq_zero]
    exact congrFun hxy i
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨z, hz⟩ := FiniteField.trace_to_zmod_nondegenerate F hsub

  rw [← hb.sum_repr z] at hz
  have hz0 : Algebra.trace (ZMod (ringChar F)) F
      ((x - y) * ∑ i, hb.repr z i • hb i) = 0 := by
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Algebra.mul_smul_comm, map_smul, hzero i, smul_zero]
  exact hz hz0

/-- The trace coordinate map associated with a basis of `F` over its prime field is bijective.
See [VanDamHallgren2000]. -/
theorem lemma2_traceFourier_bijective
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod (ringChar F)) F]
    (hb : Module.Basis (Fin (Module.finrank (ZMod (ringChar F)) F))
        (ZMod (ringChar F)) F) :
    Function.Bijective
      (fun x : F =>
        fun i : Fin (Module.finrank (ZMod (ringChar F)) F) =>
          Algebra.trace (ZMod (ringChar F)) F (x * hb i)) := by
  haveI : NeZero (ringChar F) := ⟨CharP.ringChar_ne_zero_of_finite F⟩
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨lemma2_traceFourier_injective F hb, ?_⟩
  rw [Module.card_eq_pow_finrank (K := ZMod (ringChar F)) (V := F),
    Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- The trace coordinate map associated with `hb` possesses a left inverse. See
[VanDamHallgren2000]. -/
theorem lemma2_traceFourier_reversible
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod (ringChar F)) F]
    (hb : Module.Basis (Fin (Module.finrank (ZMod (ringChar F)) F))
        (ZMod (ringChar F)) F) :
    ∃ g : (Fin (Module.finrank (ZMod (ringChar F)) F) →
        ZMod (ringChar F)) → F,
      Function.LeftInverse g
        (fun x : F =>
          fun i : Fin (Module.finrank (ZMod (ringChar F)) F) =>
            Algebra.trace (ZMod (ringChar F)) F (x * hb i)) :=
  (lemma2_traceFourier_injective F hb).hasLeftInverse

/-- The function `r ↦ (r + 1) ^ 3` is polynomially bounded. See [VanDamHallgren2000]. -/
theorem lemma2_traceFourier_linearSolveCost :
    PolynomiallyBounded (fun r => (r + 1) ^ 3) :=
  ⟨1, 3, fun n => by simp⟩

end Qatlib.Papers.QuadChar00.MainResults
