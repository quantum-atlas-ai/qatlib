/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Finite.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Notation
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.CodeStructure

open scoped BigOperators

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod (ringChar F)) F]

theorem trace_mul_eq_zero_iff (x : F) :
    (∀ y : F, Algebra.trace (ZMod (ringChar F)) F (x * y) = 0) ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F hx
    exact hb (h b)
  · rintro rfl y
    simp

theorem trace_mul_eq_zero_imp_eq_zero {x : F}
    (h : ∀ y : F, Algebra.trace (ZMod (ringChar F)) F (x * y) = 0) : x = 0 :=
  (trace_mul_eq_zero_iff x).mp h

noncomputable def traceWord {ι : Type*} (g : ι → F) (x : F) : ι → ZMod (ringChar F) :=
  fun i => Algebra.trace (ZMod (ringChar F)) F (x * g i)

theorem traceWord_injective {ι : Type*} (g : ι → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤) :
    Function.Injective (traceWord (F := F) g) := by
  intro x x' hxx'

  have hzero : ∀ i, Algebra.trace (ZMod (ringChar F)) F ((x - x') * g i) = 0 := by
    intro i
    have h := congrFun hxx' i
    simp only [traceWord] at h
    rw [sub_mul, map_sub, h, sub_self]

  have hall : ∀ y : F, Algebra.trace (ZMod (ringChar F)) F ((x - x') * y) = 0 := by
    intro y
    let T : Submodule (ZMod (ringChar F)) F :=
      { carrier := {y : F | Algebra.trace (ZMod (ringChar F)) F ((x - x') * y) = 0}
        zero_mem' := by simp
        add_mem' := by
          intro a b ha hb
          change Algebra.trace (ZMod (ringChar F)) F ((x - x') * (a + b)) = 0
          rw [mul_add, map_add, ha, hb, add_zero]
        smul_mem' := by
          intro c y hy
          change Algebra.trace (ZMod (ringChar F)) F ((x - x') * (c • y)) = 0
          have h1 : ((x - x') * (c • y)) = c • ((x - x') * y) := by
            rw [Algebra.smul_def, Algebra.smul_def]
            ring
          rw [h1, map_smul, hy, smul_zero] }
    have hmem : y ∈ Submodule.span (ZMod (ringChar F)) (Set.range g) := by
      rw [hspan]
      exact Submodule.mem_top
    have hle : Submodule.span (ZMod (ringChar F)) (Set.range g) ≤ T := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      exact hzero i
    exact hle hmem
  exact sub_eq_zero.mp ((trace_mul_eq_zero_iff (x - x')).mp hall)

noncomputable def traceWordLinear {ι : Type*} (g : ι → F) :
    F →ₗ[ZMod (ringChar F)] (ι → ZMod (ringChar F)) where
  toFun := traceWord g
  map_add' := by
    intro x x'
    funext i
    show Algebra.trace (ZMod (ringChar F)) F ((x + x') * g i)
      = Algebra.trace (ZMod (ringChar F)) F (x * g i)
        + Algebra.trace (ZMod (ringChar F)) F (x' * g i)
    rw [add_mul, map_add]
  map_smul' := by
    intro c x
    funext i
    show Algebra.trace (ZMod (ringChar F)) F ((c • x) * g i)
      = c • Algebra.trace (ZMod (ringChar F)) F (x * g i)
    have h1 : (c • x) * g i = c • (x * g i) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]
    rw [h1, (Algebra.trace (ZMod (ringChar F)) F).map_smul]

theorem traceWordLinear_injective {ι : Type*} (g : ι → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤) :
    Function.Injective (traceWordLinear (F := F) g) :=
  traceWord_injective g hspan

noncomputable def traceCode {ι : Type*} (g : ι → F) :
    Submodule (ZMod (ringChar F)) (ι → ZMod (ringChar F)) :=
  LinearMap.range (traceWordLinear g)

theorem mem_traceCode_iff {ι : Type*} (g : ι → F) (v : ι → ZMod (ringChar F)) :
    v ∈ traceCode g ↔ ∃ x : F, traceWord g x = v := Iff.rfl

noncomputable def traceWordEquiv {ι : Type*} (g : ι → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤) :
    F ≃ₗ[ZMod (ringChar F)] traceCode g :=
  LinearEquiv.ofInjective (traceWordLinear g) (traceWordLinear_injective g hspan)

@[simp]
theorem traceWordEquiv_apply {ι : Type*} (g : ι → F)
    (hspan : Submodule.span (ZMod (ringChar F)) (Set.range g) = ⊤) (x : F) :
    ((traceWordEquiv g hspan) x : ι → ZMod (ringChar F)) = traceWord g x := rfl

omit [Finite F] in

theorem traceWord_mul_eq_comp {ι : Type*} (g : ι → F) (s : ι → ι) (γN : F)
    (hs : ∀ i, g (s i) = g i * γN) (x : F) :
    traceWord g (x * γN) = fun i => traceWord g x (s i) := by
  funext i
  simp only [traceWord, hs i]
  congr 1
  ring

end Qatlib.Papers.PottsPartEval07.CodeStructure
