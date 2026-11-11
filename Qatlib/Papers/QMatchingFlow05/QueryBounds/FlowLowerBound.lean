/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMatchingFlow05.SearchTools.Defs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction

/-!
# Majority reductions for flow query bounds

This module represents the layered flow value by the Boolean Hamming weight `middleWeight`, so
its midpoint threshold is exactly majority. This is the scalar reduction used for the flow
query-bound discussion of [AmbainisSpalek2006].

Exact majority computation on `2 * k + 1` bits yields the lower bound `k + 1`. The bounded-error
quadratic estimate for the parameter `2 * p + 2` is conditional on the proposition
`MajorityBoundedLower`.

## Main statements

* `layeredThreshold_eq_majority`: the threshold of the defined flow value is majority.
* `theorem7_exact_queryLower`: the exact threshold requires at least `k + 1` queries.
* `theorem7_flow_queryLower`: the bounded-error estimate follows from a majority lower-bound
  hypothesis.

## References

* [Ambainis and Špalek, 2006][AmbainisSpalek2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction

namespace Qatlib.Papers.QMatchingFlow05.QueryBounds

open Qatlib.Papers.QMatchingFlow05.SearchTools

/-- The number of true coordinates in the Boolean input. -/
def middleWeight {N : ℕ} (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j = true).card

/-- The number `middleWeight x` equals the imported majority count `MajorityCount x`. -/
theorem middleWeight_eq_majorityCount {N : ℕ} (x : Fin N → Bool) :
    middleWeight x = MajorityCount x := rfl

/-- The layered-flow value represented by the input Hamming weight `middleWeight x`. -/
def layeredMaxFlow {N : ℕ} (x : Fin N → Bool) : ℕ := middleWeight x

/-- The vertex-count parameter `2 * p + 2` for the layered construction. -/
def layeredVertexCount (p : ℕ) : ℕ := 2 * p + 2

/-- The capacity parameter defined to equal `layeredVertexCount p`. -/
def layeredCapacity (p : ℕ) : ℕ := layeredVertexCount p

/-- Testing whether `layeredMaxFlow x` exceeds `N / 2` gives exactly `MajorityBit x`. See
[AmbainisSpalek2006]. -/
theorem layeredThreshold_eq_majority {N : ℕ} :
    (fun x : Fin N → Bool => decide (N / 2 < layeredMaxFlow x)) = @MajorityBit N := by
  funext x
  rfl

/-- Any exact query program computing the layered-flow midpoint threshold on `2 * k + 1` bits
uses at least `k + 1` queries. See [AmbainisSpalek2006]. -/
theorem theorem7_exact_queryLower (k : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (P : Program (k + k + 1) W)
    (h : Exact P (fun x => decide ((k + k + 1) / 2 < layeredMaxFlow x))) :
    k + 1 ≤ QueryCount P.circuit :=
  majority_exact_lower k P h

/-- The proposition that a positive uniform constant gives a linear query lower bound for every
bounded-error majority program. -/
def MajorityBoundedLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (W : Type) [Fintype W] [DecidableEq W]
      (P : Program N W),
    Bounded P (@MajorityBit N) →
    c * (N : ℝ) ≤ (QueryCount P.circuit : ℝ)

/-- Any exact program computing majority on `2 * k + 1` bits uses at least `k + 1` queries. See
[AmbainisSpalek2006]. -/
theorem exact_implies_majorityBound (k : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (P : Program (k + k + 1) W) (h : Exact P MajorityBit) :
    k + 1 ≤ QueryCount P.circuit :=
  majority_exact_lower k P h

/-- Assuming `MajorityBoundedLower` and `p ≥ 1`, bounded-error programs for the defined
threshold on `p * p` bits satisfy a positive-constant lower bound proportional to `(2 * p +
2) ^ 2`. See [AmbainisSpalek2006]. -/
theorem theorem7_flow_queryLower (hmaj : MajorityBoundedLower)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ (W : Type) [Fintype W] [DecidableEq W],
      ∃ c : ℝ, 0 < c ∧ ∀ (P : Program (p * p) W),
        Bounded P (fun x => decide ((p * p) / 2 < layeredMaxFlow x)) →
        c * ((2 * (p : ℝ) + 2) ^ 2) ≤ (QueryCount P.circuit : ℝ) := by
  intro W _ _
  obtain ⟨c, hc, hbound⟩ := hmaj
  refine ⟨c / 32, by linarith, ?_⟩
  intro P hP
  have hb : c * ((p * p : ℕ) : ℝ) ≤ (QueryCount P.circuit : ℝ) :=
    hbound (p * p) W P hP
  have hpq : ((p * p : ℕ) : ℝ) = (p : ℝ) * (p : ℝ) := by push_cast; ring
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hcast : (2 * (p : ℝ) + 2) ^ 2 ≤ 32 * ((p : ℝ) * (p : ℝ)) := by
    nlinarith [hp1, sq_nonneg ((p : ℝ) - 1), sq_nonneg ((p : ℝ) - 2)]
  calc (c / 32) * ((2 * (p : ℝ) + 2) ^ 2)
      ≤ (c / 32) * (32 * ((p : ℝ) * (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hcast (by positivity)
    _ = c * ((p : ℝ) * (p : ℝ)) := by ring
    _ = c * ((p * p : ℕ) : ℝ) := by rw [hpq]
    _ ≤ (QueryCount P.circuit : ℝ) := hb

end Qatlib.Papers.QMatchingFlow05.QueryBounds

end
