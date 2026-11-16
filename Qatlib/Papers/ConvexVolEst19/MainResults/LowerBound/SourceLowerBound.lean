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
open Set

open Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk

namespace Qatlib.Papers.ConvexVolEst19.MainResults.LowerBound

section

/-- The unit hypercube `H_n = [-1/2,1/2]^n`. -/
def Hn {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ i, |x i| ≤ 1 / 2

/-- The upper hyperpyramid `P_{i,+}` of Eq. (6.2). -/
def Pplus {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : Prop :=
  1 / 2 ≤ x i ∧ ∀ k, k ≠ i → |x k| + |x i| ≤ 1

/-- The lower hyperpyramid `P_{i,-}` of Eq. (6.3). -/
def Pminus {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : Prop :=
  x i ≤ -1 / 2 ∧ ∀ k, k ≠ i → |x k| + |x i| ≤ 1

/-- The gadget body `C_n` of Eq. (6.4): hypercube together with all hyperpyramids. -/
def CnBody (n : ℕ) : Set (Fin n → ℝ) :=
  {x | Hn x ∨ ∃ i, Pplus i x ∨ Pminus i x}

/-- The algorithmic query-cost predicate for volume estimation with multiplicative error
`ε`: an abstract interface recording that some algorithm estimates `Vol(K)` to relative
error `ε` using `q` membership-oracle queries. -/
def MultiplicativeVolumeEstimator (_n : ℕ) (ε q : ℝ) : Prop :=
  0 ≤ q ∧ ∃ est : ℝ, ∃ vol : ℝ, vol > 0 ∧ 0 ≤ ε ∧
    1 / (1 + ε) * vol ≤ est ∧ est ≤ (1 + ε) * vol

end

end Qatlib.Papers.ConvexVolEst19.MainResults.LowerBound
