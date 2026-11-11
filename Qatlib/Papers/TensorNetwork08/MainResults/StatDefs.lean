/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Tensor-network and statistical-model definitions

Defines finite tensor-network contractions, general and difference-model partition functions,
and the product scale `approximationScale` used in [AradLandau2010]. The predicate
`IsConsistentLabeling` records whether edge labels arise as differences of vertex labels.

The module also defines the homogeneous Potts edge weight and provides finite product and sum
identities for zero-one indicators.

## Main statements

* `tensorNetworkValue`: sums products of tensors over all edge labelings.
* `differencePartitionFunction`: defines the partition function for difference-dependent
  interactions.
* `IsConsistentLabeling`: expresses compatibility with vertex differences.
* `prod_ite_one_zero`: converts a product of indicators into a single indicator.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

namespace Qatlib.Papers.TensorNetwork08.MainResults.StatDefs

open scoped Classical BigOperators

variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]

/-- The finite contraction obtained by summing, over all edge labelings, the product of the
supplied tensors. -/
noncomputable def tensorNetworkValue {W : Type*} [Fintype W]
    (tensor : W → (E → C) → ℂ) : ℂ :=
  ∑ l : E → C, ∏ w : W, tensor w l

/-- The sum over vertex configurations of products of complex Boltzmann weights for the edge
interaction `h`. -/
noncomputable def partitionFunction (src dst : E → V) (h : E → C → C → ℂ) (β : ℂ) : ℂ :=
  ∑ σ : V → C, ∏ e : E, Complex.exp (-(β * h e (σ (src e)) (σ (dst e))))

/-- The partition function whose edge interaction depends on the source label minus the
destination label. -/
noncomputable def differencePartitionFunction [AddCommGroup C]
    (src dst : E → V) (h : E → C → ℂ) (β : ℂ) : ℂ :=
  ∑ σ : V → C, ∏ e : E, Complex.exp (-(β * h e (σ (src e) - σ (dst e))))

/-- The product of the supplied real norm factors over all vertices. See [AradLandau2010]. -/
noncomputable def approximationScale (norm : V → ℝ) : ℝ := ∏ v : V, norm v

/-- The condition that every edge label is the difference of source and destination labels for
some vertex configuration. -/
def IsConsistentLabeling [AddCommGroup C] (src dst : E → V) (δ : E → C) : Prop :=
  ∃ σ : V → C, ∀ e : E, δ e = σ (src e) - σ (dst e)

/-- The homogeneous Potts weight, equal to `exp (β * J)` for zero difference and one otherwise.
See [AradLandau2010]. -/
noncomputable def pottsEdgeWeight (β J : ℝ) {C : Type*} [Zero C] [DecidableEq C]
    (δ : C) : ℝ := if δ = 0 then Real.exp (β * J) else 1

/-- A finite product of complex zero-one indicators is one exactly when every indexed predicate
holds, and zero otherwise. -/
theorem prod_ite_one_zero {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (∏ x ∈ s, (if p x then (1 : ℂ) else 0)) = if (∀ x ∈ s, p x) then 1 else 0 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih]
      by_cases hpa : p a <;> by_cases hall : ∀ x ∈ s, p x <;> simp [hpa, hall]

/-- A finite sum of complex zero-one indicators equals the complex cast of the number of indices
satisfying the predicate. -/
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
