/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Defs
import Mathlib.LinearAlgebra.Basis.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

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

theorem lemma2_traceFourier_linearSolveCost :
    PolynomiallyBounded (fun r => (r + 1) ^ 3) :=
  ⟨1, 3, fun n => by simp⟩

end Qatlib.Papers.QuadChar00.MainResults
