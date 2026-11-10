/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

namespace Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

open scoped Classical BigOperators

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

noncomputable def tensorNetworkValue {W : Type*} [Fintype W]
    (tensor : W → (E → C) → ℂ) : ℂ :=
  ∑ l : E → C, ∏ w : W, tensor w l

noncomputable def partitionFunction (src dst : E → V) (h : E → C → C → ℂ) (β : ℂ) : ℂ :=
  ∑ σ : V → C, ∏ e : E, Complex.exp (-(β * h e (σ (src e)) (σ (dst e))))

noncomputable def differencePartitionFunction [AddCommGroup C]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ) : ℂ :=
  ∑ σ : V → C, ∏ e : E, Complex.exp (-(β * h e (σ (src e) - σ (dst e))))

noncomputable def approximationScale (norm : V → ℝ) : ℝ := ∏ v : V, norm v

def IsConsistentLabeling [AddCommGroup C] (src dst : E → V) (δ : E → C) : Prop :=
  ∃ σ : V → C, ∀ e : E, δ e = σ (src e) - σ (dst e)

noncomputable def pottsEdgeWeight (β J : ℝ) {C : Type*} [Zero C] [DecidableEq C]
    (δ : C) : ℝ := if δ = 0 then Real.exp (β * J) else 1

theorem prod_ite_one_zero {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∏ x ∈ s, (if p x then (1 : ℂ) else 0)) = if (∀ x ∈ s, p x) then 1 else 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih]
      by_cases hpa : p a <;> by_cases hall : ∀ x ∈ s, p x <;> simp [hpa, hall]

theorem sum_ite_one {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∑ x ∈ s, if p x then (1 : ℂ) else 0) = ((s.filter p).card : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih, Finset.filter_insert]
      by_cases hp : p a
      · simp [hp, ha]
        ring
      · simp [hp]

end Qatlib.Papers.TensorNetwork08.MainResults.StatDefs
