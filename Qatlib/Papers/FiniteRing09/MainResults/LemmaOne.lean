/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Module.Submodule.Lattice

set_option autoImplicit false

namespace Qatlib.Papers.FiniteRing09.MainResults.LemmaOne

variable {R : Type*} [Ring R]

theorem source_lemma_one
    (gen base : Set R) (I : Ideal R)
    (hI : I = Submodule.span R gen)
    (hgen_sub : gen ⊆ base) (hbase_sub : base ⊆ (I : Set R)) :
    (AddSubgroup.closure base : Set R) = (I : Set R) ↔
      ∀ r : R, ∀ b ∈ base, r * b ∈ AddSubgroup.closure base := by
  constructor
  · intro hEq r b hb
    have hbI : b ∈ I := hbase_sub hb
    have hrb : r * b ∈ I := Ideal.mul_mem_left I r hbI
    have hrb' : r * b ∈ (I : Set R) := hrb
    rw [← hEq] at hrb'
    exact hrb'
  · intro hclos

    let B : Ideal R :=
      { carrier := (AddSubgroup.closure base : Set R)
        zero_mem' := AddSubgroup.zero_mem _
        add_mem' := fun hx hy => AddSubgroup.add_mem _ hx hy
        smul_mem' := fun r x hx => by
          refine AddSubgroup.closure_induction
            (p := fun y (_ : y ∈ AddSubgroup.closure base) =>
              r * y ∈ AddSubgroup.closure base) ?_ ?_ ?_ ?_ hx
          · intro y hy
            exact hclos r y hy
          · simpa using AddSubgroup.zero_mem (AddSubgroup.closure base)
          · intro u v _ _ hu hv
            rw [mul_add]
            exact AddSubgroup.add_mem _ hu hv
          · intro u _ hu
            rw [mul_neg]
            exact AddSubgroup.neg_mem _ hu }
    have hbaseB : base ⊆ (B : Set R) := fun b hb => AddSubgroup.subset_closure hb
    have hgenB : gen ⊆ (B : Set R) := fun x hx => hbaseB (hgen_sub hx)
    have hspan_le : Submodule.span R gen ≤ B := Submodule.span_le.mpr hgenB
    have hI_le : I ≤ B := by
      rw [hI]
      exact hspan_le
    have hB_le : B ≤ I := by
      intro x hx
      exact (AddSubgroup.closure_le (K := I.toAddSubgroup)).mpr hbase_sub hx
    ext x
    exact ⟨fun hx => hB_le hx, fun hx => hI_le hx⟩

theorem source_lemma_one_generators
    (gen base : Set R) (I : Ideal R)
    (hI : I = Submodule.span R gen)
    (hgen_sub : gen ⊆ base) (hbase_sub : base ⊆ (I : Set R))
    (hspan_top : Subring.closure gen = ⊤) :
    (AddSubgroup.closure base : Set R) = (I : Set R) ↔
      ∀ r ∈ gen, ∀ b ∈ base, r * b ∈ AddSubgroup.closure base := by
  constructor
  · intro hEq r _ b hb
    have hbI : b ∈ I := hbase_sub hb
    have hrb : r * b ∈ I := Ideal.mul_mem_left I r hbI
    have hrb' : r * b ∈ (I : Set R) := hrb
    rw [← hEq] at hrb'
    exact hrb'
  · intro hclos

    have hall : ∀ r ∈ Subring.closure gen,
        ∀ b ∈ AddSubgroup.closure base, r * b ∈ AddSubgroup.closure base := by
      intro r hr
      refine Subring.closure_induction
        (p := fun x (_ : x ∈ Subring.closure gen) =>
          ∀ b ∈ AddSubgroup.closure base, x * b ∈ AddSubgroup.closure base)
        ?_ ?_ ?_ ?_ ?_ ?_ hr
      · intro x hx b hb
        refine AddSubgroup.closure_induction
          (p := fun y (_ : y ∈ AddSubgroup.closure base) =>
            x * y ∈ AddSubgroup.closure base) ?_ ?_ ?_ ?_ hb
        · intro y hy
          exact hclos x hx y hy
        · simp
        · intro u v _ _ hu hv
          rw [mul_add]
          exact AddSubgroup.add_mem _ hu hv
        · intro u _ hu
          rw [mul_neg]
          exact AddSubgroup.neg_mem _ hu
      · intro b _
        simp
      · intro b hb
        simpa using hb
      · intro x y _ _ hx hy b hb
        rw [add_mul]
        exact AddSubgroup.add_mem _ (hx b hb) (hy b hb)
      · intro x _ hx b hb
        rw [neg_mul]
        exact AddSubgroup.neg_mem _ (hx b hb)
      · intro x y _ _ hx hy b hb
        rw [mul_assoc]
        exact hx (y * b) (hy b hb)
    apply (source_lemma_one gen base I hI hgen_sub hbase_sub).mpr
    intro r b hb
    exact hall r (by rw [hspan_top]; trivial) b (AddSubgroup.subset_closure hb)

end Qatlib.Papers.FiniteRing09.MainResults.LemmaOne
