/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Local Davies entropy bounds

Claims c010 (Lemma 2.11), c013 (Lemma B.4), c014 (Lemma B.6), c015
(Lemma B.7) and c016 (Lemma B.9) of arXiv:2412.01732v1.

These are the local estimates relating the Davies conditional relative
entropy `D(ρ‖E_A(ρ))` to entropy production `EP_L(ρ)` that feed the weak MLSI
of Corollary 2.12 / Theorem B.8.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.LocalDavies

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

variable {I : Type} [Fintype I] [DecidableEq I]

/-- **Lemma 2.11**, arXiv:2412.01732v1 p.8, eq. (14). Let `A ⊆ Λ`,
`E_A := lim_{t→∞} e^{t L_A}` the conditional expectation of the local Davies
generator at inverse temperature `β`, for a local commuting `J`-bounded
Hamiltonian with growth constant `g`. Then

`D(ρ‖E_A(ρ)) ≤ e^{2gJ(1+2β|A^{∂∂}|)} (χ⁰_min)^{-1} EP_{L_{A^∂}}(ρ)`,

where `χ⁰_min > 0` is the constant of eq. (1). Here `shellCard` is
`|A^{∂∂}|`, `E` realises `E_A` and `EP` the entropy production
`EP_{L_{A^∂}}`. -/
def davies_conditional_entropy_bound (ρ : Density I) (E : Density I → Density I)
    (EP : Density I → ℝ) (g J β shellCard χ : ℝ) (hχ : 0 < χ)  : Prop :=
    relEnt ρ (E ρ) ≤ Real.exp (2 * g * J * (1 + 2 * β * shellCard)) * χ⁻¹ * EP ρ
  -- Source: arXiv:2412.01732v1, Lemma 2.11 (p.8, eq. (14)); proof in
  -- Appendix B.5 (pp.36–37), reducing β to 0 via Lemma B.6 and using the
  -- depolarising comparison of Lemma B.7.
  -- Proof route: chain
  --   D(ρ‖E^β_A(ρ)) ≤ e^{2gJβ|A^∂|} D(ρ‖E^0_A(ρ))      (Lemma B.6, (60))
  --   χ⁰_min D(ρ‖E^0_A(ρ)) ≤ EP_{L^0_{A^∂}}(ρ)          (Lemma B.7, (63))
  --   EP_{L^0_{A^∂}}(ρ) ≤ e^{2gJβ|A^∂|} EP_{L^β_{A^∂}}(ρ)  (Lemma B.6, (61))
  -- and multiply the exponential factors, using `|A^∂| ≤ |A^{∂∂}|`.
  -- Scope note: the local Davies generators `L_A`, their conditional
  -- expectations `E_A = lim e^{tL_A}`, the GNS-symmetric entropy production
  -- `EP_L`, and the constant `χ⁰_min` of eq. (1) are not formalised; they are
  -- interface parameters here. The analytic inputs (Pimsner–Popa index,
  -- [JLR22, Prop. 4.2/4.3]) are outside the imported API.
  -- Related results: `finite_temperature_comparison`,
  -- `infinite_temperature_mlsi` (this file), `Real.exp_add`,
  -- `Real.exp_mul`, `mul_le_mul_of_nonneg_left`.
  -- The conclusion follows by transitivity from the three inequalities of
  -- Lemmas B.6 and B.7.

/-- **Lemma B.4**, arXiv:2412.01732v1 p.35, eq. (51). Let `L` be the
generator of a GNS-symmetric quantum Markov semigroup with invariant state
`σ > 0` satisfying the weak MLSI with constants `c₁, c₂`, and let `ρ` be a
state with `D(ρ‖σ) ≥ c₂`. Then for `t ∈ (0, t_{c₂}(ρ))`,
`∫₀ᵗ √EP_L(ρ_s) ds ≤ 2√(c₁ D(ρ‖σ))`, where `ρ_s = e^{sL}(ρ)`.

Here `ρs : ℝ → Density I` is the trajectory `s ↦ e^{sL}(ρ)`, `EP` the
entropy production, `hwmlsi` the weak MLSI hypothesis
`EP_L(τ) ≥ c₁ (D(τ‖σ) − c₂)`, and `hc₂` the standing assumption
`D(ρ‖σ) ≥ c₂`. -/
def entropy_production_integral_bound (σ : Density I) (ρs : ℝ → Density I)
    (EP : Density I → ℝ) (c₁ c₂ t : ℝ) (hc₁ : 0 ≤ c₁) (ht : 0 ≤ t)
    (hc₂ : c₂ ≤ relEnt (ρs 0) σ)
    (hint : IntervalIntegrable (fun s => Real.sqrt (EP (ρs s))) MeasureTheory.volume 0 t)
    (hwmlsi : ∀ s ∈ Set.Icc 0 t, c₁ * (relEnt (ρs s) σ - c₂) ≤ EP (ρs s))  : Prop :=
    ∫ s in (0 : ℝ)..t, Real.sqrt (EP (ρs s)) ≤ 2 * Real.sqrt (c₁ * relEnt (ρs 0) σ)
  -- Source: arXiv:2412.01732v1, Lemma B.4 (p.35, eq. (51)); proof on p.35.
  -- Proof route: define
  --   F(t) := ∫₀ᵗ √EP_L(ρ_s) ds + 2√(c₁(D(ρ_t‖σ) − c₂))
  -- (eq. (52)) and show F is non-increasing because
  --   F'(t) = √EP_L(ρ_t) − √(c₁ EP_L(ρ_t)/√(D(ρ_t‖σ) − c₂)) ≤ 0
  -- by the weak MLSI (eq. (53)); evaluating at `t` and `0` and using
  -- `D(ρ_t‖σ) ≥ c₂` for `t < t_{c₂}(ρ)` gives the claim.
  -- Scope note: (i) `ρs` is an abstract trajectory rather than `s ↦ e^{sL}(ρ)`;
  -- (ii) the derivative computation needs the Fundamental Theorem of Calculus
  -- for the interval integral and differentiability of `s ↦ D(ρ_s‖σ)`, which
  -- are not available for the interface objects; (iii) `t_{c₂}(ρ)` is not
  -- modelled (we assume the weak MLSI on all of `[0,t]`).
  -- Related analytic results: `intervalIntegral.integral_le_of_forall_le`
  -- / `intervalIntegral.integral_mono_on`, `Real.sqrt_le_sqrt`,
  -- `Real.sq_sqrt`, `MeasureTheory.intervalIntegrable_iff`.
  -- Analytically, `F' ≤ 0` follows from differentiation of the interval
  -- integral (`intervalIntegral.integral_hasDerivAt_right`); integrating the
  -- resulting differential inequality gives the monotonicity bound.

/-- **Lemma B.6**, arXiv:2412.01732v1 p.37, eqs. (60) and (61). In the
context of Appendix A.3, for `A ⊆ Λ`, with `E^β_A`, `E^0_A` the Davies
conditional expectations at inverse temperature `β` and at infinite
temperature, and `EP^{D,0}_{L_A}` / `EP^{D,β}_{L_A}` the corresponding
entropy productions:

`D(ρ‖E^β_A(ρ)) ≤ e^{2gJβ|A^∂|} D(ρ‖E^0_A(ρ))`   (60)
and
`EP^{D,0}_{L_A}(ρ) ≤ e^{2gJ(β|A^∂|+1)} EP^{D,β}_{L_A}(ρ)`   (61). -/
def finite_temperature_comparison (ρ : Density I) (Eβ E0 : Density I → Density I)
    (EPβ EP0 : Density I → ℝ) (g J β shellCard : ℝ)  : Prop :=
    relEnt ρ (Eβ ρ) ≤ Real.exp (2 * g * J * β * shellCard) * relEnt ρ (E0 ρ) ∧
    EP0 ρ ≤ Real.exp (2 * g * J * (β * shellCard + 1)) * EPβ ρ
  -- Source: arXiv:2412.01732v1, Lemma B.6 (p.37, eqs. (60), (61)); proof on
  -- p.37.
  -- Proof route: [JLR22, Proposition 4.2] gives
  --   D(ρ‖E^β_A(ρ)) ≤ ‖E^β_A(I_Λ)‖∞ D(ρ‖E^0_A(ρ)),
  -- and `E^β_A(e^{-βH_{A^∂}}) = e^{-βH_{A^∂}}` together with
  -- `‖H_{A^∂}‖∞ ≤ gJ|A^∂|` yields `‖E^β_A(I_Λ)‖∞ ≤ e^{2βgJ|A^∂|}`. For (61),
  -- [JLR22, Proposition 4.3] gives
  --   EP^{D,0}_{L_A}(ρ) ≤ max_ω e^{|ω|/2} ‖(E^β_A(I_Λ))^{-1}‖∞ EP^{D,β}_{L_A}(ρ),
  -- with Bohr frequencies `|ω| ≤ 2gJ`; hence the exponent `2gJ(β|A^∂|+1)`.
  -- Scope note: the Bohr-frequency decomposition of the Davies generator, the
  -- E_A action on `e^{-βH_{A^∂}}`, and the operator-norm bounds are outside
  -- the formalised API; `Eβ`, `E0`, `EPβ`, `EP0` are interface data.
  -- Related operator bounds: `OperatorSpectralNorm` bounds in
  -- `Concepts.MbqcFlow.FlowDecision.MixedState`, `Matrix.norm_mul`,
  -- `norm_smul`, `Real.exp_le_exp`.
  -- The local Hamiltonian estimate `‖H_{A^∂}‖∞ ≤ gJ|A^∂|` and the two
  -- [JLR22] inequalities are the analytic inputs to this comparison.

/-- **Lemma B.7**, arXiv:2412.01732v1 p.38, eq. (63). In the context of
Appendix A.3, for `A ⊆ Λ` and `E^0_A = lim e^{t L^0_A}`:

`χ⁰_min D(ρ‖E^0_A(ρ)) ≤ EP_{L^0_{A^∂}}(ρ)`. -/
def infinite_temperature_mlsi (ρ : Density I) (E0 : Density I → Density I)
    (EP0 : Density I → ℝ) (χ : ℝ) (hχ : 0 < χ)  : Prop :=
    χ * relEnt ρ (E0 ρ) ≤ EP0 ρ
  -- Source: arXiv:2412.01732v1, Lemma B.7 (p.38, eq. (63)); proof on p.38.
  -- Proof route: by GNS symmetry of `L^0_{A^∂}`, [CM17, Theorem 5.10] writes
  -- `EP_{L^0_{A^∂}}(ρ)` as a sum of non-negative inner products with
  -- coefficients `χ⁰_{ω,k} ≥ χ⁰_min > 0`; dropping to the lower bound gives
  -- `χ⁰_min EP_{L̃}(ρ) ≤ EP_{L^0_{A^∂}}(ρ)`, and `L̃` is identified with the
  -- generator of the depolarising dynamics whose Dirichlet form is
  -- `D(ρ‖E^0_A(ρ))`.
  -- Scope note: the GNS/Dirichlet-form decomposition and the identification
  -- `L̃ = L^0_A` (via [KB16, Theorem 31]) are not formalised; `EP0`, `E0` and
  -- `χ` are interface data.
  -- Related interfaces:
  -- `EntropyProductionIneq`/`mlsi_relativeEntropy_decay` interface
  -- (GapWaveLindbladSemigroup) for the Dirichlet-form side.
  -- The relevant generator for the MLSI interface is the
  -- infinite-temperature Davies generator.

/-- **Lemma B.9**, arXiv:2412.01732v1 p.39, eq. (68). A uniform polynomial
lower bound `λ(L_A) ≥ C|A|^{-μ}` on the local gap implies the uniform lower
bound

`α_c(L_A) ≥ C / (2 log 10 + 2(2βgJ + 3 log d)|A^∂|) · |A|^{-μ}
          ≥ Ω(|A|^{-μ-1})`

on the cMLSI constant of the local generator `L_A`.

`λ` is the local gap, `αc` the cMLSI constant, `bnd A` is the boundary size
`|A^∂|` (an explicit datum, since the paper's denominator is expressed through
`|A^∂|` and only the derived `Ω(|A|^{-μ-1})` form uses `|A|`), `hgap` the
polynomial local gap assumption and `hlink` the relation
`λ(L_A) ≤ αc(L_A) · denominator` coming from `α_c(L_A) ≥ Ω(λ(L_A)/|A|)`
(eq. (15)); `hden` records the positivity of the denominator. -/
theorem poly_gap_to_cmlsi {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (C : ℝ) (μ : ℕ) (β g J d : ℝ) (_hC : 0 < C) (_hd : 0 < d) (_hβ : 0 ≤ β)
    (_hg : 0 ≤ g) (_hJ : 0 ≤ J)
    (gap αc bnd : Finset Λ → ℝ) (_hbnd : ∀ A : Finset Λ, 0 ≤ bnd A)
    (hgap : ∀ A : Finset Λ, C * (A.card : ℝ) ^ (-(μ : ℝ)) ≤ gap A)
    (hlink : ∀ A : Finset Λ,
      gap A ≤ αc A * (2 * Real.log 10 + 2 * (2 * β * g * J + 3 * Real.log d) * bnd A))
    (hden : ∀ A : Finset Λ,
      0 < 2 * Real.log 10 + 2 * (2 * β * g * J + 3 * Real.log d) * bnd A)
    (A : Finset Λ) :
    C / (2 * Real.log 10 + 2 * (2 * β * g * J + 3 * Real.log d) * bnd A)
        * (A.card : ℝ) ^ (-(μ : ℝ)) ≤ αc A := by
  have hdenA := hden A
  rw [div_mul_eq_mul_div, div_le_iff₀ hdenA]
  exact le_trans (hgap A) (hlink A)
  -- Source: arXiv:2412.01732v1, Lemma B.9 (p.39, eq. (68)); proof on p.39.
  -- Proof route: the Pimsner–Popa index bound of [GR22],
  -- `C_cb(E_A) ≤ ‖τ^{-1}‖∞ ∑_i d_{K_i}^2` with `∑_i d_{K_i} ≤ d^{|A^∂|}`
  -- and `‖τ^{-1}‖∞ ≤ d^{|A^∂|} e^{2βgJ|A^∂|}`, combined with
  -- `α_c(L_A) ≥ λ(L_A)/(2 log 10 · C_cb(E_A))` (eq. (27)), gives
  -- `α_c(L_A) ≥ λ(L_A) / (2 log 10 + 2(2βgJ + 3 log d)|A^∂|)`
  -- (the logarithm of the index contributes `2 log 10`); inserting
  -- `λ(L_A) ≥ C|A|^{-μ}` yields (68), and since `|A^∂| ≤ c|A|` the bound is
  -- `Ω(|A|^{-μ-1})`.
  -- Scope note: the Pimsner–Popa index `C_cb(E_A)`, the Davies-channel
  -- decomposition (70), and the spectral-gap/cMLSI relation (27) are not
  -- formalised; `λ` and `αc` are functions of the region supplied as
  -- interface data, with `hlink` encoding (27); `bnd` is `|A^∂|`.
  -- Related inequalities: `div_le_iff`, `div_mul_eq_mul_div`,
  -- `Real.rpow_le_rpow`, `Real.log_pos`; the
  -- `EntropyProductionIneq` interface for (27).
  -- Positivity of the denominator gives
  -- `C|A|^{-μ} / denom ≤ gap A / denom`; combining with `hlink` yields
  -- the stated bound.

end Qatlib.Papers.GibbsSampling25.MainResults.LocalDavies
