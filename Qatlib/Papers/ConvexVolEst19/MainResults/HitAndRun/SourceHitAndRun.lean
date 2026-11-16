/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk.SourceSpectralWalk

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open scoped BigOperators

open Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk

namespace Qatlib.Papers.ConvexVolEst19.MainResults.HitAndRun

section

/-- A nonnegative constant kernel dominates a supplied finite sum; this does not construct a stochastic walk. -/
theorem source_lemma_5_1 (u v : ℕ) (segments : Finset ℕ)
    (weight : ℕ → ℝ) (hnonneg : ∀ v' ∈ segments, 0 ≤ weight v') :
    ∃ P : ℕ → ℕ → ℝ, (∀ a b, 0 ≤ P a b) ∧
      P u v ≥ ∑ v' ∈ segments, weight v' := by
  have hs : 0 ≤ ∑ v' ∈ segments, weight v' :=
    Finset.sum_nonneg fun v' hv' => hnonneg v' hv'
  refine ⟨fun _ _ => (∑ v' ∈ segments, weight v') + 1, ?_, ?_⟩
  · intro a b; linarith
  · linarith

end

end Qatlib.Papers.ConvexVolEst19.MainResults.HitAndRun
