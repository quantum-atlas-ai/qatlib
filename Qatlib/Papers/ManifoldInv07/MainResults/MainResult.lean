/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManifoldInv07.MainResults.CircuitCorrectness

/-!
# Exact and approximate source-invariant recognizers

This module packages the matrix data for the invariant expectation of
[GarneroneMarzuoliRasetti2007] in `CompiledRecognizer`. Its value is the multiplexed expectation
of the supplied matrices and weight vector.

The exact existence theorem retains the unitary fixed-vector and block matrix-element
hypotheses. The approximate theorem uses normalized nonnegative weights and uniform
return-amplitude accuracy to bound the recognizer value's distance from the phase-adjusted
source invariant.

## Main statements

* `source_expectation_exact`: A recognizer realizes the prescribed invariant expectation under
  the supplied identities.
* `source_expectation_approximate`: Uniform block approximation yields an ε-accurate recognizer
  value.

## References

* [Garnerone et al., 2007][GarneroneMarzuoliRasetti2007]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.ManifoldInv07.MainResults.MainResult

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.ManifoldInv07.MainResults.Defs
open Qatlib.Papers.ManifoldInv07.MainResults.CircuitCorrectness

/-- Matrix data consisting of a color-register matrix, controlled blocks, a distinguished basis
label, a level, an integer signature, and color-indexed polynomial values. -/
structure CompiledRecognizer (J P : Type*) [Fintype J] [Fintype P]
    [DecidableEq J] where
  S0 : Matrix J J ℂ
  U : J → Matrix P P ℂ
  p0 : P
  level : ℕ
  sigma : ℤ
  coloredPoly : J → ℂ

/-- The multiplexed expectation of a compiled recognizer with the supplied real weights. -/
noncomputable def CompiledRecognizer.value {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P] (C : CompiledRecognizer J P) (μ : J → ℝ) : ℂ :=
  muxExpectation C.S0 C.U μ C.p0

/-- The source phase has complex norm one at every natural level. -/
theorem sourceAlpha_norm (k : ℕ) : ‖sourceAlpha k‖ = 1 := by
  unfold sourceAlpha
  exact Complex.norm_exp_ofReal_mul_I _

/-- Given nonnegative weights, a unitary `S0` fixing their square-root state, and the supplied
block matrix-element identities, there exists a recognizer whose value is the phase-adjusted
source invariant [GarneroneMarzuoliRasetti2007]. -/
theorem source_expectation_exact {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P]
    (k : ℕ) (S0 : Matrix J J ℂ) (U : J → Matrix P P ℂ)
    (μ : J → ℝ) (Jpoly : J → ℂ) (σ : ℤ) (p0 : P)
    (hμ : ∀ j, 0 ≤ μ j)
    (hS0u : S0 ∈ Matrix.unitaryGroup J ℂ)
    (hS0 : ApplyGate S0 (psiFromWeights μ) = psiFromWeights μ)
    (hKaul : ∀ j, Inner (Ket p0) (ApplyGate (U j) (Ket p0)) = Jpoly j) :
    ∃ C : CompiledRecognizer J P,
      C.value μ = sourceInvariant (sourceAlpha k) σ μ Jpoly * sourceAlpha k ^ σ := by
  refine ⟨⟨S0, U, p0, k, σ, Jpoly⟩, ?_⟩
  show muxExpectation S0 U μ p0 = _
  exact source_equation_39 k S0 U μ Jpoly σ p0 hμ hS0u hS0 hKaul

/-- For normalized nonnegative weights and the supplied unitary fixed-vector and exact block
identities, block return-amplitude errors at most ε/2 give a recognizer value within ε of
the phase-adjusted invariant when ε ≥ 0 [GarneroneMarzuoliRasetti2007]. -/
theorem source_expectation_approximate {J P : Type*} [Fintype J] [Fintype P]
    [DecidableEq J] [DecidableEq P]
    (k : ℕ) (S0 : Matrix J J ℂ) (U U' : J → Matrix P P ℂ)
    (μ : J → ℝ) (Jpoly : J → ℂ) (σ : ℤ) (p0 : P)
    (hμ : ∀ j, 0 ≤ μ j) (hμsum : ∑ j, μ j = 1)
    (hS0u : S0 ∈ Matrix.unitaryGroup J ℂ)
    (hS0 : ApplyGate S0 (psiFromWeights μ) = psiFromWeights μ)
    (hKaul : ∀ j, Inner (Ket p0) (ApplyGate (U j) (Ket p0)) = Jpoly j)
    (ε : ℝ) (hε : 0 ≤ ε)
    (happrox : ∀ j, ‖(ApplyGate (U' j) (Ket p0)) p0
      - (ApplyGate (U j) (Ket p0)) p0‖ ≤ ε / 2) :
    ∃ C : CompiledRecognizer J P,
      ‖C.value μ - sourceInvariant (sourceAlpha k) σ μ Jpoly * sourceAlpha k ^ σ‖ ≤ ε := by
  refine ⟨⟨S0, U', p0, k, σ, Jpoly⟩, ?_⟩
  change ‖muxExpectation S0 U' μ p0
    - sourceInvariant (sourceAlpha k) σ μ Jpoly * sourceAlpha k ^ σ‖ ≤ ε
  have hexact : muxExpectation S0 U μ p0
      = sourceInvariant (sourceAlpha k) σ μ Jpoly * sourceAlpha k ^ σ :=
    source_equation_39 k S0 U μ Jpoly σ p0 hμ hS0u hS0 hKaul
  rw [← hexact]
  have hmain : ‖muxExpectation S0 U' μ p0 - muxExpectation S0 U μ p0‖ ≤ ε / 2 :=
    muxExpectation_norm_sub_le S0 U U' μ p0 hμ hμsum hS0u hS0 (ε / 2) happrox
  exact hmain.trans (by linarith)

end Qatlib.Papers.ManifoldInv07.MainResults.MainResult
