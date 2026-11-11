/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.LinearAlgebra.Matrix.PosDef
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

set_option backward.isDefEq.respectTransparency false

/-!
# DynamicProg24 — shared source model

Source: arXiv:2403.09187 (Quantum Dynamic Programming).  Fixed text read from
`assets/2403.09187.txt` / `.pdf`; the qatlas markdown endpoint returned 503.

This module fixes the notation shared by the per-result modules of the
`MainResults` block: the paper's hyperbolic-secant recursion profile (Eq. (S76)),
the trace distance `δ(ρ,σ) = ½‖ρ-σ‖₁`, the density-operator predicate, the
fast-spectral-convergence hypothesis (Definition 8), the DME channel (Eq. (S27)),
the partial-reflection channel (Eq. (S73)) and the elementary cost model used for
the `O(·)` circuit-depth statements.

The model is deliberately basis-explicit: states are matrices `Matrix (Fin d) (Fin d) ℂ`.
This matches the paper, which works with finite-dimensional density matrices.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.DynamicProg24.MainResults

/-- The paper's hyperbolic secant `sech x = 1 / cosh x` (Eq. (S76)). -/
def sech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

/-- The paper's inverse hyperbolic secant `arcsech x = arcosh (x⁻¹)`
(used in Eq. (S76); the paper recalls `arcsech(x) = arcosh(x⁻¹)` before Eq. (S77)). -/
def arcsech (x : ℝ) : ℝ := Real.arcosh (x⁻¹)

/-- Trace distance `δ(ρ,σ) = ½‖ρ-σ‖₁`.  This is the paper's `½‖·-·‖₁` (Eq. (S31)). -/
def traceDistance {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (1 / 2) * (ρ - σ).traceNorm

/-- A finite-dimensional density operator: positive semidefinite with unit trace. -/
def IsDensity {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/-- The paper's iteration profile `h(x) = sech ((2L+1) arcsech x)` (Eq. (S128)). -/
def hProfile (L : ℕ) (x : ℝ) : ℝ := sech ((2 * (L : ℝ) + 1) * arcsech x)

/-- Definition 8 (fast spectral convergence), in the quantitative form actually used
in the proof of Theorem 9: `τ` is a fixed point of the recursion channel `U`, and the
one-step distance obeys `δ_{U(ρ)} ≤ h(δ_ρ)` with `h` strictly contracting
(`h(x) < x`) and `h(x+ε) ≤ h(x) + r ε` for some `0 ≤ r < 1` (Eq. (S32)). -/
structure FastSpectralConvergence {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
    (τ : Matrix (Fin d) (Fin d) ℂ) (h : ℝ → ℝ) (r : ℝ) : Prop where
  /-- `τ` is a fixed point of the recursion. -/
  fixed : U τ = τ
  /-- One-step distance contraction (Eq. (S30)). -/
  step_le : ∀ ρ, traceDistance (U ρ) τ ≤ h (traceDistance ρ τ)
  /-- Strict contraction along the profile. -/
  lt : ∀ x, 0 < x → h x < x
  /-- The contraction constant is nonnegative. -/
  hr0 : 0 ≤ r
  /-- The contraction constant is below one. -/
  hr1 : r < 1
  /-- The profile is `r`-Lipschitz for the accumulated-error estimate (Eq. (S32)). -/
  lipschitz : ∀ x ε : ℝ, 0 ≤ ε → h (x + ε) ≤ h x + r * ε

/-- Density-matrix exponentiation channel of Eq. (S27):
`E_s[ρ](σ) = cos²s·σ − i·sin s·cos s·[ρ,σ] + sin²s·ρ`. -/
def dmeChannel {d : ℕ} (s : ℝ) (ρ σ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (((Real.cos s) ^ 2 : ℝ) : ℂ) • σ
    - ((Complex.I * ((Real.sin s * Real.cos s : ℝ) : ℂ))) • (ρ * σ - σ * ρ)
    + ((((Real.sin s) ^ 2 : ℝ)) : ℂ) • ρ

/-- Partial reflection `Ê_s[ψ] = 1 − (1 − e^{-is})|ψ⟩⟨ψ|` (Eq. (S73)), applied as the
unitary channel `σ ↦ U σ U†`. -/
def partialReflection {d : ℕ} (s : ℝ) (ψ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  1 - ((1 - Complex.exp (-(Complex.I * (s : ℂ)))) : ℂ) • ψ

/-- The unitary channel associated with an operator `U`. -/
def unitaryChannel {d : ℕ} (U σ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  U * σ * Uᴴ

/-- Cost of one emulated recursion step at per-step channel error `η` (Eq. (S33),
following Lemma 7): the step has depth `K · η⁻¹` for a constant `K` that depends on
the polynomial but not on `ρ` or `η`. -/
def stepDepth (K η : ℝ) : ℝ := K * η⁻¹

/-- Total circuit depth of `N` emulated recursion steps at per-step error `η`. -/
def qdpDepth (K η : ℝ) (N : ℕ) : ℝ := (N : ℝ) * stepDepth K η

/-! ## Elementary facts about the trace distance -/

/-- The `traceDistance_nonneg` result for the DynamicProg24 paper model. -/
theorem traceDistance_nonneg {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ traceDistance ρ σ := by
  unfold traceDistance
  exact mul_nonneg (by norm_num) (Matrix.traceNorm_nonneg _)

/-- The `traceDistance_comm` result for the DynamicProg24 paper model. -/
theorem traceDistance_comm {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) :
    traceDistance ρ σ = traceDistance σ ρ := by
  unfold traceDistance
  rw [show ρ - σ = -(σ - ρ) by abel, Matrix.traceNorm_neg]

/-- The `traceDistance_triangle` result for the DynamicProg24 paper model. -/
theorem traceDistance_triangle {d : ℕ} (ρ σ τ : Matrix (Fin d) (Fin d) ℂ) :
    traceDistance ρ τ ≤ traceDistance ρ σ + traceDistance σ τ := by
  unfold traceDistance
  have h : ρ - τ = (ρ - σ) + (σ - τ) := by abel
  rw [h]
  have := Matrix.traceNorm_add_le (ρ - σ) (σ - τ)
  nlinarith [Matrix.traceNorm_nonneg (ρ - σ), Matrix.traceNorm_nonneg (σ - τ)]

/-! ## Hyperbolic-secant identities -/

/-- The `arcsech_sech` result for the DynamicProg24 paper model. -/
theorem arcsech_sech {y : ℝ} (hy : 0 ≤ y) : arcsech (sech y) = y := by
  unfold arcsech sech
  rw [inv_inv]
  exact Real.arcosh_cosh hy

/-- The `sech_pos` result for the DynamicProg24 paper model. -/
theorem sech_pos (y : ℝ) : 0 < sech y := by
  unfold sech
  exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh y))

/-- The `sech_le_one` result for the DynamicProg24 paper model. -/
theorem sech_le_one {y : ℝ} (hy : 0 ≤ y) : sech y ≤ 1 := by
  unfold sech
  have h2 : 0 < Real.cosh y := lt_of_lt_of_le zero_lt_one (Real.one_le_cosh y)
  have h := (div_le_one h2).2 (Real.one_le_cosh y)
  simpa [one_div] using h

/-- Eq. (S77) in the form used below: `δ_n⁻¹ = T_{2L+1}(δ_{n-1}⁻¹)`, written without
the Chebyshev polynomial on the left.  Consequence of `sech (M · arcsech x) =
1 / (T_M (x⁻¹))`, i.e. `cosh (M · arcosh (x⁻¹)) = T_M (x⁻¹)` for `0 < x ≤ 1`. -/
theorem inv_sech_profile {L : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (Polynomial.Chebyshev.T ℝ (2 * (L : ℤ) + 1)).eval (x⁻¹) =
      (sech ((2 * (L : ℝ) + 1) * arcsech x))⁻¹ := by
  have hxinv : 1 ≤ x⁻¹ := by
    have := (one_le_div (a := (1 : ℝ)) (b := x) hx0).2 hx1
    simpa [one_div] using this
  have hcosh : Real.cosh (Real.arcosh x⁻¹) = x⁻¹ := Real.cosh_arcosh hxinv
  have hrhs : (sech ((2 * (L : ℝ) + 1) * arcsech x))⁻¹ =
      Real.cosh ((2 * (L : ℝ) + 1) * Real.arcosh x⁻¹) := by
    unfold sech arcsech
    rw [inv_inv]
  have hM : (Polynomial.Chebyshev.T ℝ (2 * (L : ℤ) + 1)).eval (x⁻¹) =
      Real.cosh ((2 * (L : ℝ) + 1) * Real.arcosh x⁻¹) := by
    conv_lhs => rw [← hcosh]
    rw [Polynomial.Chebyshev.T_real_cosh]
    congr 1
    push_cast
    ring
  rw [hrhs, hM]

end Qatlib.Papers.DynamicProg24.MainResults
