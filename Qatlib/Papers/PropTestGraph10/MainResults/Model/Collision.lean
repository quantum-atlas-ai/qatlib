/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: the collision-counting problem of Lemma 12

Fixed source: arXiv:1012.3174v3. This module transcribes the collision problem
behind Lemma 12 (p. 15, Algorithm 4).  The input is a function `f : Fin X → Fin Y`
(represented by the list of its `|X|` values); a *collision* is a pair of distinct
inputs with the same image.  `collisions f` counts such (unordered) pairs, which
is the quantity the algorithm is promised to test against a threshold `M`.

A `CollisionAlgorithm` models the algorithm by a finite output set `I` with an
output distribution `out f : I → ℝ` and a set `accepting f` of outputs that decode
to "true"; `probTrue` is the total accepted mass.  `timeCost` is the running
time.  Correctness is: accepted mass `≥ 2/3` when there are at least `M`
collisions, and no accepted mass at all when there are fewer than `M` collisions
(one-sided error).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

open scoped BigOperators

/-- Number of colliding pairs of distinct inputs of `f : Fin X → Fin Y`, i.e.
pairs `x < x'` with `f x = f x'`. This is the "number of collisions" counted by
Algorithm 4 (p. 15). -/
def collisions {X Y : ℕ} (f : Fin X → Fin Y) : ℕ :=
  (by classical
    exact (Finset.univ.filter
      fun p : Fin X × Fin X => p.1 < p.2 ∧ f p.1 = f p.2).card)

/-- A collision-counting algorithm in the sense of Algorithm 4 (p. 15): a finite
randomised output distribution together with an accepting set of outputs and the
accounted running time. -/
structure CollisionAlgorithm (X Y : ℕ) where
  /-- Finite output alphabet. -/
  I : Type
  [fintypeI : Fintype I]
  [decEqI : DecidableEq I]
  /-- Probability mass of each output. -/
  out : (Fin X → Fin Y) → I → ℝ
  out_nonneg : ∀ f i, 0 ≤ out f i
  /-- Outputs that decode to "true". -/
  accepting : (Fin X → Fin Y) → Finset I
  /-- Accounted running time. -/
  timeCost : ℕ

/-- Probability that the collision algorithm outputs "true" on input `f`. -/
def CollisionAlgorithm.probTrue {X Y : ℕ} (A : CollisionAlgorithm X Y)
    (f : Fin X → Fin Y) : ℝ :=
  letI := A.fintypeI
  letI := A.decEqI
  ∑ i ∈ A.accepting f, A.out f i

end Qatlib.Papers.PropTestGraph10.MainResults.Model
