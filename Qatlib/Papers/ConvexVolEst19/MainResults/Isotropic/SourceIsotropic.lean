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

namespace Qatlib.Papers.ConvexVolEst19.MainResults.Isotropic

section

/-- Near-isotropic position: the covariance quadratic form `q` is within a constant
factor of the identity, `(1/2)·‖v‖² ≤ q v ≤ (3/2)·‖v‖²`. -/
def NearIsotropic {n : ℕ} (q : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ v, (1 / 2 : ℝ) * (∑ i, (v i) ^ 2) ≤ q v ∧ q v ≤ (3 / 2 : ℝ) * (∑ i, (v i) ^ 2)

end

end Qatlib.Papers.ConvexVolEst19.MainResults.Isotropic
