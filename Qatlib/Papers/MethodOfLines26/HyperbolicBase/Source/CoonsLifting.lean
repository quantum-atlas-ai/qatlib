/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Qatlib.Papers.MethodOfLines26.ParabolicBase.Source.CoonsLifting

set_option backward.isDefEq.respectTransparency false

/-!
# Coons Boundary Lifting for Hyperbolic PDEs

This module formalizes Theorem 13 (Coons boundary lifting for second-order hyperbolic
PDEs), combining the second-order source-transfer identity with the inclusion-exclusion
face-trace cancellation from `ParabolicBase.Source.CoonsLifting`.

## Main statements

* `coons_source_transfer_second_order`: second-order time-derivative source transfer for `u + S`.
* `theorem13_hyperbolic_boundary_lifting`: combined hyperbolic source transfer and face cancellation.

## References

* [Liang and Liu, 2026][LiangLiu2026], Theorem 13, Section 5.1, p. 35.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source

open scoped BigOperators
open Qatlib.Papers.MethodOfLines26.ParabolicBase.Source

/-- **Theorem 13 (operator/source half)**: if `u` solves `u_tt = L u + f` with first
time derivative `u'` and `S` has first and second time derivatives `S'` and `d2S`, then
`u + S` has second time derivative `L (u + S) + (f + d2S - L S)`. -/
theorem coons_source_transfer_second_order
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] V) (u S u' S' : ℝ → V) (f d2S : ℝ → V)
    (hu1 : ∀ t, HasDerivAt u (u' t) t)
    (hu2 : ∀ t, HasDerivAt u' (L (u t) + f t) t)
    (hS1 : ∀ t, HasDerivAt S (S' t) t)
    (hS2 : ∀ t, HasDerivAt S' (d2S t) t) :
    (∀ t, HasDerivAt (fun t => u t + S t) (u' t + S' t) t) ∧
    (∀ t, HasDerivAt (fun t => u' t + S' t)
      (L (u t + S t) + (f t + d2S t - L (S t))) t) := by
  refine ⟨fun t => (hu1 t).add (hS1 t), fun t => ?_⟩
  have h := (hu2 t).add (hS2 t)
  convert h using 1
  rw [ContinuousLinearMap.map_add]
  abel

/-- **Theorem 13 (hyperbolic Coons lifting)**: combines the second-order operator source
transfer with the homogeneous-boundary alternating cancellation on each face. -/
theorem theorem13_hyperbolic_boundary_lifting
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] V) (u S u' S' : ℝ → V) (f d2S : ℝ → V)
    (hu1 : ∀ t, HasDerivAt u (u' t) t)
    (hu2 : ∀ t, HasDerivAt u' (L (u t) + f t) t)
    (hS1 : ∀ t, HasDerivAt S (S' t) t)
    (hS2 : ∀ t, HasDerivAt S' (d2S t) t) :
    (∀ t, HasDerivAt (fun t => u t + S t) (u' t + S' t) t) ∧
    (∀ t, HasDerivAt (fun t => u' t + S' t)
      (L (u t + S t) + (f t + d2S t - L (S t))) t) ∧
    (∀ {ι : Type*} [DecidableEq ι] (Sset : Finset ι) (l : ι), l ∈ Sset →
      ∀ (τ : Finset ι → V), (∀ A, A ⊆ Sset → l ∉ A → τ (insert l A) = τ A) →
      (∑ A ∈ Sset.powerset.filter (fun A => A.Nonempty),
        ((-1 : ℤ) ^ A.card) • τ A) = - τ {l}) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (coons_source_transfer_second_order L u S u' S' f d2S
      hu1 hu2 hS1 hS2).1
  · exact (coons_source_transfer_second_order L u S u' S' f d2S
      hu1 hu2 hS1 hS2).2
  · intro ι _ Sset l hl τ hpair
    exact alternating_coons_cancellation Sset l hl τ hpair

end Qatlib.Papers.MethodOfLines26.HyperbolicBase.Source
