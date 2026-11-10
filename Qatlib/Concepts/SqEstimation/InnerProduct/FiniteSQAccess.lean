/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
open scoped Classical BigOperators
namespace Qatlib.Concepts.SqEstimation.InnerProduct

noncomputable def sqSquaredNorm {X : Type} [Fintype X] (v : X → ℂ) : ℝ := ∑ i, Complex.normSq (v i)
structure FiniteSQInput (X : Type) [Fintype X] where
  target : X → ℂ
  envelope : X → ℂ
  samples : FinDist X
  cachedEnvelopeSquaredNorm : ℝ
  norm_spec : cachedEnvelopeSquaredNorm = sqSquaredNorm envelope
  envelope_pos : 0 < sqSquaredNorm envelope
  domination : ∀ i, Complex.normSq (target i) ≤ Complex.normSq (envelope i)
  sample_spec : ∀ i, samples.prob i = Complex.normSq (envelope i)/sqSquaredNorm envelope

theorem sqSquaredNorm_nonneg {X : Type} [Fintype X] (v : X → ℂ) :
    0 ≤ sqSquaredNorm v := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem finite_sq_access_support_and_norm (X : Type) [Fintype X] (a : FiniteSQInput X) :
    sqSquaredNorm a.target ≤ sqSquaredNorm a.envelope ∧
    (∀ i, a.samples.prob i = 0 ↔ a.envelope i = 0) ∧
    (∀ i, a.envelope i = 0 → a.target i = 0) := by
  refine ⟨Finset.sum_le_sum (fun i _ => a.domination i), ?_, ?_⟩
  · intro i
    rw [a.sample_spec, div_eq_zero_iff]
    simp [a.envelope_pos.ne']
  · intro i hi
    have h := a.domination i
    rw [hi, Complex.normSq_zero] at h
    exact Complex.normSq_eq_zero.mp (le_antisymm h (Complex.normSq_nonneg _))

end Qatlib.Concepts.SqEstimation.InnerProduct
