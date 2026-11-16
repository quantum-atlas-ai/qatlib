/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.QuditQubitTranslation
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.TraceMap

open Qatlib.Papers.MagicDistill24.Triorthogonal

/-- Squaring preserves the trace from the field of 1024 elements to its prime field. -/
theorem trace_square (x : F1024) : f1024Trace (x ^ 2) = f1024Trace x := by
  simpa only [f1024Trace, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
    using Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F1024) x

/-- The trace functional onto the two-element field is surjective. -/
theorem trace_surjective : Function.Surjective f1024Trace := by
  have hnonzero : ∃ x : F1024, f1024Trace x ≠ 0 := by
    by_contra h
    push Not at h
    have heq := f1024TracePair_nondegenerate 1 (by simpa using h)
    exact one_ne_zero heq
  obtain ⟨x, hx⟩ := hnonzero
  have hcases (b : ZMod 2) : b = 0 ∨ b = 1 := by
    have hb : b.val < 2 := b.isLt
    have hv : b.val = 0 ∨ b.val = 1 := by omega
    rcases hv with hv | hv
    · left; exact ZMod.val_injective 2 (by rw [ZMod.val_zero]; exact hv)
    · right; exact ZMod.val_injective 2 (by rw [ZMod.val_one]; exact hv)
  have hxone : f1024Trace x = 1 := (hcases _).resolve_left hx
  intro b
  rcases hcases b with rfl | rfl
  · exact ⟨0, map_zero (Algebra.trace (ZMod 2) F1024)⟩
  · exact ⟨x, hxone⟩

/-- Exactly half the elements of the field of 1024 elements have trace zero. -/
theorem trace_zero_half :
    (Finset.univ.filter (fun x : F1024 => f1024Trace x = 0)).card =
      Fintype.card F1024 / 2 := by
  classical
  let tr := (Algebra.trace (ZMod 2) F1024).toAddMonoidHom
  have hsur : Function.Surjective tr := trace_surjective
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective hsur
  have heq : Nat.card tr.ker =
      (Finset.univ.filter (fun x : F1024 => f1024Trace x = 0)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [heq, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card] at hcard
  omega

/-- Proposition 2.1.1: prime-field linearity, equal trace fibers, and Frobenius invariance. -/
theorem source_proposition_2_1_1 :
    (∀ (a : ZMod 2) (x : F1024),
      f1024Trace (algebraMap (ZMod 2) F1024 a * x) = a * f1024Trace x) ∧
    (∀ x y : F1024, f1024Trace (x + y) = f1024Trace x + f1024Trace y) ∧
    ((Finset.univ.filter (fun x : F1024 => f1024Trace x = 0)).card =
      Fintype.card F1024 / 2) ∧
    (∀ x : F1024, f1024Trace (x ^ 2) = f1024Trace x) := by
  refine ⟨?_, ?_, trace_zero_half, trace_square⟩
  · intro a x
    rw [← Algebra.smul_def]
    exact (map_smul (Algebra.trace (ZMod 2) F1024) a x).trans (smul_eq_mul a _)
  · exact fun x y => map_add (Algebra.trace (ZMod 2) F1024) x y

end Qatlib.Papers.MagicDistill24.MainResults.TraceMap
