/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Foundations.PureStateMath.MixedState
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import QuantumInfo.ForMathlib.Matrix

set_option backward.isDefEq.respectTransparency false

/-!
# Thermalize11.MainResults.SourceModel — finite-dimensional microcanonical vocabulary

Riera--Gogolin--Eisert, *Thermalization in Nature and on a Quantum Computer*,
fixed arXiv:1102.2389v4 (PDF SHA-256 of the prefetched copy
`prove/assets/1102.2389.pdf`, 12 Mar 2012).

This file introduces the small amount of source vocabulary needed by the three
active claims of the paper:

* `dephasedState P Ω = P / Ω` — the dephased / microcanonical state belonging to
  an energy window, where `P` is the orthogonal projector onto the window's
  support and `Ω` is the dimension of that support (paper, p. 2, around Eq. (3));
* `windowDeltaOmega`, `theorem1Bound` — the paper's `ΔΩ` and the right-hand side
  of Theorem 1, Eq. (1) on p. 2.

Two general facts about the shared `traceDistance` of
`QuantumAlgorithm.Foundations.MixedFidelity.FidelityMetric` are proved here and
reused by the claim files:

* `traceDistance_partialTrace_le` — discarding a register (the partial trace of
  `QuantumAlgorithm.Concepts.MbqcFlow.FlowDecision`) never increases the trace
  distance. This is exactly the first inequality of Eq. (3) on p. 2,
  `𝒟(ω_Π^S, ω_Π^{S(0)}) ≤ 𝒟(ω_Π, ω_Π^{(0)})`, obtained there from "monotonicity
  of the trace distance";
* `traceDistance_triangle` — the triangle inequality used for Eq. (10) on p. 4,
  `𝒟(ω_QC^S, ρ_Gibbs^S) ≤ 𝒟(ω_QC^S, ω_u^{S(0)}) + 𝒟(ω_u^{S(0)}, ρ_Gibbs^S)`.

The partial-trace contraction is proved for Hermitian matrices (the physical
case: differences of dephased projectors) by reusing the frozen library lemma
`traceRight_hermitian_trace_contraction`; the triangle inequality holds for all
complex matrices, because `traceDistance` itself is a total function.

Boundary: this module only records the metric-side vocabulary. It does not
construct spectral projectors of `H₀` or `H = H₀ + V`, it does not assert the
Bhatia sin-theta perturbation bound, and it does not model the algorithm.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Classical
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.Thermalize11.MainResults.SourceModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

variable {D E : ℕ}

/-- The dephased / microcanonical state of an energy window: the orthogonal
projector `P` onto the window support, normalized by the support dimension `Ω`.
Paper: p. 1–2 ("dephased/microcanonical states", the states `ω_u` and their
dephased versions written `ω_Π` in the extracted claim). For `Ω = 0` the
expression is the zero normalization convention `0⁻¹ • P = 0`; physically
`Ω ≥ 1`.

Stated for an arbitrary index type so that it applies to the full system-bath
space `Fin dS × Fin dB` as well as to `Operator D`. -/
def dephasedState {ι : Type*} (P : Matrix ι ι ℂ) (Ω : ℕ) : Matrix ι ι ℂ :=
  ((Ω : ℂ))⁻¹ • P

/-- Paper Eq. (1), p. 2: `ΔΩ = Ω_max − Ω_min`, the difference between the
largest and smallest support dimensions of the two dephased states. -/
def windowDeltaOmega (Ωmax Ωmin : ℝ) : ℝ := Ωmax - Ωmin

/-- Paper Theorem 1, Eq. (1), p. 2: the right-hand side
`‖V‖∞/ε + (ΔΩ + Ω_ε)/(2 Ω_max)`.

`couplingNorm` is `‖V‖∞`, `eps` is the energy window `ε`, `Ωε` is the total
number of eigenstates of `H` and `H₀` in the two `ε`-boundary windows. -/
def theorem1Bound (couplingNorm eps Ωmax Ωmin Ωε : ℝ) : ℝ :=
  couplingNorm / eps + (windowDeltaOmega Ωmax Ωmin + Ωε) / (2 * Ωmax)

/-- The partial trace of a difference is the difference of the partial traces. -/
theorem partialTrace_sub (X Y : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (X - Y) = PartialTrace X - PartialTrace Y := by
  ext i j
  simp [PartialTrace, Finset.sum_sub_distrib]

/-- The shared `PartialTrace` is the second-factor trace of Physlib. -/
theorem partialTrace_eq_traceRight (X : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace X = Matrix.traceRight X := rfl

/-- The dephased state of a Hermitian projector is Hermitian (the normalization
`Ω⁻¹` is a real scalar). Paper: p. 2, `ω_Π = P/Ω`. -/
theorem isHermitian_dephasedState {ι : Type*} {P : Matrix ι ι ℂ}
    (hP : P.IsHermitian) (Ω : ℕ) :
    (dephasedState P Ω).IsHermitian := by
  unfold dephasedState
  exact hP.smul (by simp : IsSelfAdjoint (((Ω : ℂ))⁻¹))

/-- **Partial-trace contraction of the trace norm (Hermitian case).** For a
Hermitian matrix `X` on `Fin D × Fin E`, the trace norm of the partial trace is
at most that of `X`.

Paper: Eq. (3), p. 2, first inequality, "by monotonicity of the trace distance".
This is the frozen library lemma
`QuantumAlgorithm.Foundations.ReferenceError.DensityToRaw.traceRight_hermitian_trace_contraction`,
transported across the definitional identity `PartialTrace = Matrix.traceRight`. -/
theorem traceNorm_partialTrace_le {X : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hX : X.IsHermitian) :
    Matrix.traceNorm (PartialTrace X) ≤ Matrix.traceNorm X := by
  rw [partialTrace_eq_traceRight]
  exact Qatlib.Concepts.ReferenceError.DensityToRaw.traceRight_hermitian_trace_contraction X hX

/-- A general-index trace distance `‖X − Y‖₁ / 2`; on `Operator D` it is
definitionally the shared `traceDistance`. -/
def traceDistanceGen {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℂ) : ℝ :=
  Matrix.traceNorm (X - Y) / 2

/-- On `Operator D`, `traceDistanceGen` is the shared trace distance. -/
theorem traceDistanceGen_eq_traceDistance (ρ σ : Operator D) :
    traceDistanceGen ρ σ = traceDistance ρ σ := rfl

/-- **Trace-distance monotonicity under discarding a register (full space).**
The second inequality of Eq. (3) on p. 2 is preceded by exactly this step: the
subsystem distance is bounded by the full-space distance. The Hermiticity
hypotheses are the physical density-matrix case (`ρ`, `σ` are dephased
projectors) and are what the frozen contraction lemma consumes. -/
theorem traceDistanceGen_partialTrace_le
    {ρ σ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    traceDistance (PartialTrace ρ) (PartialTrace σ) ≤ traceDistanceGen ρ σ := by
  unfold traceDistance traceDistanceGen
  rw [← partialTrace_sub]
  exact div_le_div_of_nonneg_right (traceNorm_partialTrace_le (hρ.sub hσ)) (by norm_num)

/-- **Triangle inequality for `traceDistanceGen`.** Used by the paper at
Eq. (10), p. 4. Proved from the triangle inequality of the trace norm and
`(X − Y) + (Y − Z) = X − Z`. -/
theorem traceDistanceGen_triangle {ι : Type*} [Fintype ι]
    (X Y Z : Matrix ι ι ℂ) :
    traceDistanceGen X Z ≤ traceDistanceGen X Y + traceDistanceGen Y Z := by
  unfold traceDistanceGen
  have hsum : X - Z = (X - Y) + (Y - Z) := by abel
  have h := Matrix.traceNorm_add_le (X - Y) (Y - Z)
  rw [← hsum] at h
  linarith

/-- **Triangle inequality for the shared trace distance.** Used by the paper at
Eq. (10), p. 4: `𝒟(ω_QC^S, ρ_Gibbs^S) ≤ 𝒟(ω_QC^S, ω_u^{S(0)}) +
𝒟(ω_u^{S(0)}, ρ_Gibbs^S)`. -/
theorem traceDistance_triangle (ρ σ τ : Operator D) :
    traceDistance ρ τ ≤ traceDistance ρ σ + traceDistance σ τ := by
  have := traceDistanceGen_triangle ρ σ τ
  simpa only [traceDistanceGen_eq_traceDistance] using this

/-- The paper's Theorem-1 right-hand side is nonnegative whenever `ε > 0`,
`Ω_max > 0`, `Ω_ε ≥ 0`, `Ω_max ≥ Ω_min` and `‖V‖∞ ≥ 0`. -/
theorem theorem1Bound_nonneg {couplingNorm eps Ωmax Ωmin Ωε : ℝ}
    (hV : 0 ≤ couplingNorm) (heps : 0 < eps) (hΩmax : 0 < Ωmax)
    (hΩε : 0 ≤ Ωε) (hΔ : Ωmin ≤ Ωmax) :
    0 ≤ theorem1Bound couplingNorm eps Ωmax Ωmin Ωε := by
  unfold theorem1Bound windowDeltaOmega
  have h1 : 0 ≤ couplingNorm / eps := div_nonneg hV heps.le
  have h2 : 0 ≤ (Ωmax - Ωmin + Ωε) / (2 * Ωmax) := by
    have : 0 ≤ Ωmax - Ωmin := by linarith
    positivity
  linarith

end Qatlib.Papers.Thermalize11.MainResults.SourceModel
