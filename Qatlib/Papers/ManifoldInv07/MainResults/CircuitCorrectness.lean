/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManifoldInv07.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.ManifoldInv07.MainResults.CircuitCorrectness

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ManifoldInv07.MainResults.Defs

theorem source_equation_39 {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P]
    (k : ℕ) (S0 : Matrix J J ℂ) (U : J → Matrix P P ℂ)
    (μ : J → ℝ) (Jpoly : J → ℂ) (σ : ℤ) (p0 : P)
    (hμ : ∀ j, 0 ≤ μ j)
    (hS0u : S0 ∈ Matrix.unitaryGroup J ℂ)
    (hS0 : ApplyGate S0 (psiFromWeights μ) = psiFromWeights μ)
    (hKaul : ∀ j, Inner (Ket p0) (ApplyGate (U j) (Ket p0)) = Jpoly j) :
    muxExpectation S0 U μ p0
      = sourceInvariant (sourceAlpha k) σ μ Jpoly * sourceAlpha k ^ σ := by
  rw [muxExpectation_eq S0 U μ p0 hμ hS0u hS0]
  rw [invariant_mul_alpha_zpow (sourceAlpha k) (sourceAlpha_ne_zero k) σ μ Jpoly]
  apply Finset.sum_congr rfl
  intro j _
  rw [hKaul j]

end Qatlib.Papers.ManifoldInv07.MainResults.CircuitCorrectness
