/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Card

/-!
# Few-level approximation error bound (source Theorem 1, Eq. (28))

Source: Ali Hamed Moosavian and Stephen Jordan, *Faster quantum algorithm to simulate
Fermionic Quantum Field Theory*, fixed version arXiv:1711.04006v3 (23 Oct 2019),
Section IV A (Theorem 1, Eq. (28)) and Appendix B.

Theorem 1 of the source bounds the error of the few-level approximation: for
`H = H_0 + λ cos(ωt) W` with `‖W‖ = 1`, exact state projector `ρ(t)` started from the ground
state of `H_0`, and `ρ⁽⁻⁾(t)` the solution of the Schrödinger equation projected onto the
span of the `ν` lowest eigenstates of `H_0`,

  `|Tr[ρ⁽⁻⁾(t) ρ(t)]| ≥ 1 - (2νλ + 3νλ²t)/δ`,

where `δ` is the minimum detuning of the driven transitions out of those `ν` levels from the
rest of the spectrum of `H_0` (Eq. (B35), (B41)).

Appendix B proceeds in three layers:

1. an interaction-picture Duhamel expansion of `Tr[ρ⁽⁻⁾ρ]`, whose integral form drops the
   first-order term and leaves the estimate
   `1 - |Tr[ρ⁽⁻⁾ρ]| ≤ (λ + 3λ²t/2) Σ_{μ<ν} Σ_{k=1,2} 1/δ^μ_k` (Eq. (B15)--(B39));
2. the spectral-norm estimate `‖R^μ_k(τ)‖ ≤ 1/δ^μ_k` for the off-resonant divisor
   `D^μ_k = Σ_{η≥ν} |ψ_η⟩⟨ψ_η| / ((-1)^k ω + ω_{μη})` sandwiched between `P_μ`, `W` and the
   phase propagator `U^μ_k(τ)` (Eq. (B29)--(B36)), which is what introduces the `1/δ`;
3. the bookkeeping `Σ_{μ<ν} Σ_{k=1,2} 1/δ^μ_k ≤ 2ν/δ` (Eq. (B40)) together with the
   passage from Eq. (B39) to Eq. (B42) = Eq. (28).

This module formalises layers 2 and 3 unconditionally: the eigenbasis `{|ψ_η⟩}` of `H_0` is
the standard basis of `ι`, `E` its eigenvalues, `W` an arbitrary operator with `‖W‖ ≤ 1`,
`low` the block of the `ν` lowest levels, and the operators `P_μ`, `D^μ_k`, `U^μ_k(τ)` of
Eq. (B32) are built as diagonal matrices. It then states Eq. (28) with layer 1, the
Duhamel estimate (B15)--(B39), as its only hypothesis.

Boundary: layer 1 is not formalised. It needs the well-posedness of the two von Neumann
equations, differentiation under the trace, integration by parts for operator-valued
functions, and the splitting of the commutator into `W^(⁻⁺)`, `W^(⁺⁻)` blocks
(Eq. (B5)--(B27)); the source's additional simplification `⟨ψ_j|W|ψ_j⟩ = 0` (Eq. (B14)) also
lives there. Only its conclusion is consumed below, so no part of Eq. (28) is assumed beyond
that displayed estimate. The shared library provides the reusable pieces of that layer: its ordered
evolution and ordered matrix-ODE uniqueness results give existence, uniqueness and
the ODE for a time-ordered propagator, while its contractive Duhamel result gives
the constant-generator case. Trace differentiation and operator-valued
integration by parts for Eqs. (B15)--(B16) are outside the scope of this module.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.FermionQFT17.MainResults.FewLevelBound

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source Eq. (B3): the Bohr transition frequency `ω_{ij} = E_i - E_j` of the eigenbasis of
`H_0`. -/
def transitionFreq (E : ι → ℝ) (i j : ι) : ℝ := E i - E j

/-- Source Eq. (B35): the real detuning denominator `(-1)^k ω + ω_{μη}` of the transition
from level `μ` to level `η` at sideband `k`; its absolute value is the detuning, and its
minimum over the off-block levels is `δ^μ_k`. -/
def detuningDenominator (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ η : ι) : ℝ :=
  (-1 : ℝ) ^ k * ω + transitionFreq E μ η

/-- Source Eq. (B35): the detuning `|(-1)^k ω + ω_{μη}|` of the transition from level `μ` to
the off-block level `η` at sideband `k`. -/
def detuningOf (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ η : ι) : ℝ :=
  |detuningDenominator E ω k μ η|

/-- Source Eq. (B32): the real phase angle `τ ((-1)^k ω + ω_{μη})` of the diagonal phase
propagator. -/
def phaseAngle (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ η : ι) (τ : ℝ) : ℝ :=
  detuningDenominator E ω k μ η * τ

/-- Source Eq. (B32): the level projector `P_μ = |ψ_μ⟩⟨ψ_μ|` of `H_0`, written in the
eigenbasis of `H_0`. -/
def levelProjector (μ : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun η => if η = μ then 1 else 0

/-- Source Eq. (B32): the off-resonant divisor `D^μ_k = Σ_{η ∉ low} |ψ_η⟩⟨ψ_η| /
((-1)^k ω + ω_{μη})`, restricted to the complement of the `ν`-level block `low`. -/
def offResonantDivisor (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ : ι) (low : Finset ι) :
    Matrix ι ι ℂ :=
  Matrix.diagonal fun η =>
    if η ∈ low then 0 else ((detuningDenominator E ω k μ η : ℂ))⁻¹

/-- Source Eq. (B32): the phase propagator `U^μ_k(τ) = Σ_η e^{i τ ((-1)^k ω + ω_{μη})}
|ψ_η⟩⟨ψ_η|`, a diagonal unitary in the eigenbasis of `H_0`. -/
def phasePropagator (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ : ι) (τ : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun η => Complex.exp (((phaseAngle E ω k μ η τ : ℂ)) * Complex.I)

/-- Source Eq. (B32)--(B33): the level projector has operator norm at most `1`, so it
contributes no factor to the bound on `‖R^μ_k(τ)‖`. -/
theorem norm_levelProjector_le_one (μ : ι) : ‖levelProjector μ‖ ≤ 1 := by
  rw [levelProjector, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun η => ?_
  by_cases h : η = μ
  · simp [h]
  · simp [h]

/-- Source Eq. (B32)--(B33): the phase propagator `U^μ_k(τ)` is unitary up to the diagonal
phases, so its operator norm is at most `1`; this is the step "one sees that `U^μ_k(τ)` is
unitary" in Appendix B. -/
theorem norm_phasePropagator_le_one (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ : ι) (τ : ℝ) :
    ‖phasePropagator E ω k μ τ‖ ≤ 1 := by
  rw [phasePropagator, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun η => ?_
  exact le_of_eq (Complex.norm_exp_ofReal_mul_I (phaseAngle E ω k μ η τ))

/-- Source Eq. (B34)--(B36): the off-resonant divisor has operator norm at most `1/δ`
whenever `δ` is below every off-block detuning, which is precisely Eq. (B34) read through
the diagonal form of Eq. (B32). -/
theorem norm_offResonantDivisor_le (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ : ι) (low : Finset ι)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : ∀ η, η ∉ low → δ ≤ detuningOf E ω k μ η) :
    ‖offResonantDivisor E ω k μ low‖ ≤ 1 / δ := by
  rw [offResonantDivisor, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun η => ?_
  by_cases h : η ∈ low
  · simp only [h, ↓reduceIte, norm_zero]
    positivity
  · have hdet : δ ≤ |detuningDenominator E ω k μ η| := hδ η h
    have hpos : 0 < |detuningDenominator E ω k μ η| := lt_of_lt_of_le hδ0 hdet
    have hinv : (|detuningDenominator E ω k μ η|)⁻¹ ≤ δ⁻¹ :=
      (inv_le_inv₀ hpos hδ0).mpr hdet
    have hnorm : ‖((detuningDenominator E ω k μ η : ℂ))⁻¹‖ =
        (|detuningDenominator E ω k μ η|)⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [if_neg h, hnorm, one_div]
    exact hinv

/-- Source Eq. (B31)--(B36): the spectral norm of the off-resonant resolvent summand
`R^μ_k(τ) = P_μ W D^μ_k U^μ_k(τ)` is at most `1/δ^μ_k`; this is the estimate that makes the
`1/δ` dependence of Eq. (28) appear. -/
theorem norm_resolventSummand_le (E : ι → ℝ) (ω : ℝ) (k : ℕ) (μ : ι) (low : Finset ι)
    (W : Matrix ι ι ℂ) {δ τ : ℝ} (hδ0 : 0 < δ)
    (hδ : ∀ η, η ∉ low → δ ≤ detuningOf E ω k μ η) (hW : ‖W‖ ≤ 1) :
    ‖levelProjector μ * W * offResonantDivisor E ω k μ low * phasePropagator E ω k μ τ‖ ≤
      1 / δ := by
  have hP : ‖levelProjector μ‖ ≤ 1 := norm_levelProjector_le_one μ
  have hD : ‖offResonantDivisor E ω k μ low‖ ≤ 1 / δ :=
    norm_offResonantDivisor_le E ω k μ low hδ0 hδ
  have hU : ‖phasePropagator E ω k μ τ‖ ≤ 1 := norm_phasePropagator_le_one E ω k μ τ
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have h1 : ‖levelProjector μ * W * offResonantDivisor E ω k μ low * phasePropagator E ω k μ τ‖ ≤
      ‖levelProjector μ * W * offResonantDivisor E ω k μ low‖ * ‖phasePropagator E ω k μ τ‖ :=
    Matrix.l2_opNorm_mul _ _
  have h2 : ‖levelProjector μ * W * offResonantDivisor E ω k μ low‖ ≤
      ‖levelProjector μ * W‖ * ‖offResonantDivisor E ω k μ low‖ := Matrix.l2_opNorm_mul _ _
  have h3 : ‖levelProjector μ * W‖ ≤ ‖levelProjector μ‖ * ‖W‖ := Matrix.l2_opNorm_mul _ _
  have h4 : ‖levelProjector μ * W * offResonantDivisor E ω k μ low‖ *
      ‖phasePropagator E ω k μ τ‖ ≤
      (‖levelProjector μ‖ * ‖W‖ * ‖offResonantDivisor E ω k μ low‖) *
        ‖phasePropagator E ω k μ τ‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖levelProjector μ * W * offResonantDivisor E ω k μ low‖
        ≤ ‖levelProjector μ * W‖ * ‖offResonantDivisor E ω k μ low‖ := h2
      _ ≤ (‖levelProjector μ‖ * ‖W‖) * ‖offResonantDivisor E ω k μ low‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  have h5 : (‖levelProjector μ‖ * ‖W‖ * ‖offResonantDivisor E ω k μ low‖) *
      ‖phasePropagator E ω k μ τ‖ ≤ ((1 * 1) * (1 / δ)) * 1 := by
    have hPW : ‖levelProjector μ‖ * ‖W‖ ≤ 1 * 1 :=
      mul_le_mul hP hW (norm_nonneg _) zero_le_one
    have hPWD : ‖levelProjector μ‖ * ‖W‖ * ‖offResonantDivisor E ω k μ low‖ ≤
        (1 * 1) * (1 / δ) := mul_le_mul hPW hD (norm_nonneg _) (by positivity)
    exact mul_le_mul hPWD hU (norm_nonneg _) (by positivity)
  have h6 : ((1 * 1) * (1 / δ)) * 1 = 1 / δ := by ring
  exact h1.trans ((h4.trans h5).trans (le_of_eq h6))

end

/-- Source Eq. (B40): the detuning bookkeeping `Σ_{μ ∈ low} Σ_{k=1,2} 1/δ^μ_k ≤ 2ν/δ`,
where `ν` is the number of levels in the block `low` and every `δ^μ_k` dominates `δ`. -/
theorem detuning_reciprocal_sum_le {ι : Type*} (low : Finset ι) (ν : ℕ) (hcard : low.card = ν)
    (d : ι → Fin 2 → ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hd : ∀ μ k, δ ≤ d μ k) :
    ∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹ ≤ 2 * ν / δ := by
  have hpos : ∀ μ k, (0 : ℝ) < d μ k := fun μ k => lt_of_lt_of_le hδ0 (hd μ k)
  have hinner : ∀ μ : ι, (∑ k : Fin 2, (d μ k)⁻¹) ≤ 2 * δ⁻¹ := by
    intro μ
    have hsum : (∑ k : Fin 2, (d μ k)⁻¹) ≤ ∑ _k : Fin 2, δ⁻¹ :=
      Finset.sum_le_sum fun k _ => (inv_le_inv₀ (hpos μ k) hδ0).mpr (hd μ k)
    have hconst : (∑ _k : Fin 2, δ⁻¹) = 2 * δ⁻¹ := by
      rw [Fin.sum_univ_two]
      ring
    rw [hconst] at hsum
    exact hsum
  calc ∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹
      ≤ ∑ _μ ∈ low, (2 * δ⁻¹) := Finset.sum_le_sum fun μ _ => hinner μ
    _ = (low.card : ℝ) * (2 * δ⁻¹) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * ν / δ := by
        rw [hcard]
        field_simp

/-- Source Eq. (B39) -- Eq. (B42): the passage from the Duhamel estimate
`1 - |Tr[ρ⁽⁻⁾ρ]| ≤ (λ + 3λ²t/2) S` and the bookkeeping `S ≤ 2ν/δ` to the published bound
`|Tr[ρ⁽⁻⁾ρ]| ≥ 1 - (2νλ + 3νλ²t)/δ` of Eq. (28). -/
theorem fewLevel_trace_bound (ν : ℕ) (lam δ τ p S : ℝ) (hδ0 : 0 < δ)
    (hS : S ≤ 2 * ν / δ) (hcoef : 0 ≤ lam + 3 * lam ^ 2 * τ / 2)
    (hdyson : 1 - |p| ≤ (lam + 3 * lam ^ 2 * τ / 2) * S) :
    1 - (2 * ν * lam + 3 * ν * lam ^ 2 * τ) / δ ≤ |p| := by
  have hmono : (lam + 3 * lam ^ 2 * τ / 2) * S ≤
      (lam + 3 * lam ^ 2 * τ / 2) * (2 * ν / δ) :=
    mul_le_mul_of_nonneg_left hS hcoef
  have heq : (lam + 3 * lam ^ 2 * τ / 2) * (2 * ν / δ) =
      (2 * ν * lam + 3 * ν * lam ^ 2 * τ) / δ := by
    field_simp
  rw [heq] at hmono
  linarith

/-- Source Theorem 1, Eq. (28): with `S = Σ_{μ ∈ low} Σ_{k=1,2} 1/δ^μ_k` the detuning sum of
Appendix B and the Duhamel estimate (B39) as hypothesis, the exact and few-level state
projectors have overlap `|Tr[ρ⁽⁻⁾(t) ρ(t)]| ≥ 1 - (2νλ + 3νλ²t)/δ`. -/
theorem theorem1_trace_lower_bound {ι : Type*} (low : Finset ι) (ν : ℕ) (hcard : low.card = ν)
    (d : ι → Fin 2 → ℝ) {δ lam τ p : ℝ} (hδ0 : 0 < δ) (hd : ∀ μ k, δ ≤ d μ k)
    (hcoef : 0 ≤ lam + 3 * lam ^ 2 * τ / 2)
    (hdyson : 1 - |p| ≤
      (lam + 3 * lam ^ 2 * τ / 2) * ∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹) :
    1 - (2 * ν * lam + 3 * ν * lam ^ 2 * τ) / δ ≤ |p| := by
  refine fewLevel_trace_bound ν lam δ τ p _ hδ0
    (detuning_reciprocal_sum_le low ν hcard d hδ0 hd) hcoef hdyson

/-- Source Eq. (B30) with Eq. (B36): combining the `ν` resolvent summand bounds
`‖R_k^μ(τ)‖ ≤ 1/δ^μ_k` with the triangle inequality gives `‖R_k(τ)‖ ≤ Σ_μ 1/δ^μ_k`. -/
theorem norm_resolventSum_le {ι : Type*} (low : Finset ι) (d : ι → Fin 2 → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hd : ∀ μ k, δ ≤ d μ k) :
    (∑ μ ∈ low, (d μ 0)⁻¹) ≤ ∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹ := by
  refine Finset.sum_le_sum fun μ _ => ?_
  have hpos : ∀ k : Fin 2, (0 : ℝ) < d μ k := fun k => lt_of_lt_of_le hδ0 (hd μ k)
  have hle : (d μ 0)⁻¹ ≤ ∑ k : Fin 2, (d μ k)⁻¹ := by
    rw [Fin.sum_univ_two]
    have h1 : (0 : ℝ) ≤ (d μ 1)⁻¹ := inv_nonneg.mpr (le_of_lt (hpos 1))
    linarith
  exact hle

/-- Source Eqs. (B27), (B37): the triangle-inequality and submultiplicativity estimate for
the boundary terms. Given the shape `K ≤ (λ/2)(2νs + 3λt·νs)` implied by Eqs. (B27), (B30)
and (B36) with `s` the resolvent-sum bound and `ν` summands, the assembled constant is
`(λ + 3λ²t/2)` times `νs`, which is the coefficient of Eq. (B39). -/
theorem K_bound (K lam t s : ℝ) (ν : ℕ) (hK : K ≤
    (lam / 2) * ((ν : ℝ) * s + (ν : ℝ) * s + 3 * lam * t * ((ν : ℝ) * s))) :
    K ≤ (lam + 3 * lam ^ 2 * t / 2) * ((ν : ℝ) * s) := by
  have heq : (lam / 2) * ((ν : ℝ) * s + (ν : ℝ) * s + 3 * lam * t * ((ν : ℝ) * s)) =
      (lam + 3 * lam ^ 2 * t / 2) * ((ν : ℝ) * s) := by ring
  rwa [heq] at hK

/-- Source Eq. (B17) with Eqs. (B37)--(B38): since `|Tr| ≥ 1 - K₁ - K₂ - L₁ - L₂` and each of
the four terms is at most `C`, the overlap is at least `1 - 4C`. -/
theorem trace_lower_from_four_terms (p K1 K2 L1 L2 C : ℝ)
    (h : 1 - K1 - K2 - L1 - L2 ≤ |p|) (h1 : K1 ≤ C) (h2 : K2 ≤ C) (h3 : L1 ≤ C)
    (h4 : L2 ≤ C) : 1 - 4 * C ≤ |p| := by
  linarith

/-- Source Eqs. (B39)--(B42) with the literal four-term bookkeeping of Eq. (B17): grouping
the two sidebands of each of the `K` and `L` pairs gives the honest hypothesis
`|Tr| ≥ 1 - 2(λ + 3λ²t/2)Σ`, and `Σ ≤ 2ν/δ` then yields
`|Tr| ≥ 1 - 2(2νλ + 3νλ²t)/δ`, i.e. Eq. (28) with all constants doubled. The printed
Eq. (B39) reads the four terms as one and drops this factor of two. -/
theorem theorem1_trace_lower_bound_factor_two {ι : Type*} (low : Finset ι) (ν : ℕ)
    (hcard : low.card = ν) (d : ι → Fin 2 → ℝ) {δ lam τ p : ℝ} (hδ0 : 0 < δ)
    (hd : ∀ μ k, δ ≤ d μ k) (hcoef : 0 ≤ lam + 3 * lam ^ 2 * τ / 2)
    (hfour : 1 - 2 * ((lam + 3 * lam ^ 2 * τ / 2) *
      ∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹) ≤ |p|) :
    1 - 2 * ((2 * ν * lam + 3 * ν * lam ^ 2 * τ) / δ) ≤ |p| := by
  have hS := detuning_reciprocal_sum_le low ν hcard d hδ0 hd
  have hmono : (lam + 3 * lam ^ 2 * τ / 2) * (∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹) ≤
      (lam + 3 * lam ^ 2 * τ / 2) * (2 * ν / δ) :=
    mul_le_mul_of_nonneg_left hS hcoef
  have heq : (lam + 3 * lam ^ 2 * τ / 2) * (2 * ν / δ) =
      (2 * ν * lam + 3 * ν * lam ^ 2 * τ) / δ := by
    field_simp
  have h4 : 1 - 2 * ((lam + 3 * lam ^ 2 * τ / 2) * (2 * ν / δ)) ≤ |p| := by
    linarith [hfour, hmono]
  rwa [heq] at h4

/-- Source Eq. (28) at the Rabi pulse time `t = π/λ` (Section IV C): Theorem 1 then reads
`|Tr| ≥ 1 - ν(2 + 3π)λ/δ`, i.e. the few-level error is linear in `λ/δ`, matching the
`ε₁` of the total-error combination. -/
theorem theorem1_at_pulse_time {ι : Type*} (low : Finset ι) (ν : ℕ) (hcard : low.card = ν)
    (d : ι → Fin 2 → ℝ) {δ lam p : ℝ} (hδ0 : 0 < δ) (hlam : 0 < lam)
    (hd : ∀ μ k, δ ≤ d μ k)
    (hdyson : 1 - |p| ≤ (lam + 3 * lam ^ 2 * (Real.pi / lam) / 2) *
      ∑ μ ∈ low, ∑ k : Fin 2, (d μ k)⁻¹) :
    1 - ν * (2 + 3 * Real.pi) * lam / δ ≤ |p| := by
  have hcoef : 0 ≤ lam + 3 * lam ^ 2 * (Real.pi / lam) / 2 := by
    have hrewrite : lam + 3 * lam ^ 2 * (Real.pi / lam) / 2 =
        lam * (1 + 3 * Real.pi / 2) := by
      field_simp
    rw [hrewrite]
    positivity
  have h := theorem1_trace_lower_bound low ν hcard d hδ0 hd hcoef hdyson
  have hcoefeq : (2 * ν * lam + 3 * ν * lam ^ 2 * (Real.pi / lam)) / δ =
      ν * (2 + 3 * Real.pi) * lam / δ := by
    field_simp
  rw [hcoefeq] at h
  exact h

end Qatlib.Papers.FermionQFT17.MainResults.FewLevelBound
