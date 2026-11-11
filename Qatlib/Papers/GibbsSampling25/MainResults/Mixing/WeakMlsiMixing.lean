/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Weak MLSI and mixing-time bounds

Claims c003 (Theorem 2.9), c004 (Corollary 2.12), c005 (Theorem 2.14) and
c011 (Corollary 2.13) of arXiv:2412.01732v1.

The semigroup is an interface datum `S : ℝ → Density I → Density I` standing
for `ρ ↦ e^{t L_Λ}(ρ)`; `mcmi` is the MCMI operator norm of Definition 2.2
(see `Model.McmiNorm`); `dist` is the lattice metric used for `dist(A,C)`.
The mixing times `tMixW1` and `tMixTrace` are interface reals standing for
`t_mix^{W1}(ε)` and `t_mix^{1}(ε)`.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Mixing

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

/-- **Theorem 2.9 (Quasi rapid Wasserstein mixing)**, arXiv:2412.01732v1 p.7,
eq. (12). For a family of Davies Lindbladians of `(κ,r)`-local, commuting,
`J`-bounded Hamiltonians with growth constant `g` and invariant Gibbs states
satisfying uniform exponential MCMI decay,

`t_mix^{W1}(ε) = quasi-poly(1/ε²) · poly log(N/ε²)` with `N = |Λ_L|`.

Formally: there are exponents `a ∈ ℝ` and `b ∈ ℕ` and a constant `C > 0` with

`t_mix^{W1}(ε) ≤ C · exp(a·(log(1/ε²)+1)^b) · (log(N/ε²)+1)^b`

for every `ε > 0` (the first factor is `quasi-poly(1/ε²)`, the second
`poly log(N/ε²)`). -/
def quasi_rapid_wasserstein_mixing {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (tMixW1 : ℝ → ℝ)
    (hUniform : ∃ K ξ : ℝ, 0 < K ∧ 0 < ξ ∧ ∀ A C Dd : Finset Λ,
      mcmi A C Dd ≤ K * (Fintype.card Λ : ℝ) * Real.exp (- setDistOf dist A C / ξ))  : Prop :=
    ∃ (a : ℝ) (b : ℕ) (C : ℝ), 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      tMixW1 ε ≤ C * Real.exp (a * (Real.log (1 / ε ^ 2) + 1) ^ b)
        * (Real.log ((Fintype.card Λ : ℝ) / ε ^ 2) + 1) ^ b
  -- Source: arXiv:2412.01732v1, Theorem 2.9 (p.7, eq. (12)); the explicit
  -- upper bound is Theorem C.1 (Appendix C.1); proof strategy on p.8.
  -- Proof route: (i) Theorem 2.10 (weak transport cost inequality) bounds the
  -- W1 distance by `√(D(ρ‖σ))` plus a constant; (ii) Corollary 2.12
  -- (quasi-poly weak MLSI) gives
  -- `D(e^{tL}ρ‖σ) ≤ e^{-α(ε)t} D(ρ‖σ) + ε` with
  -- `1/α(ε) = O(exp(poly log(N/ε)))`; (iii) combining gives
  -- `t_mix^{W1}(ε) = quasi-poly(1/ε²) · poly log(N/ε²)`.
  -- Lean gap: the Davies semigroup, the W1 distance and the weak MLSI are
  -- interface data; the constants of Theorem C.1 are not computed.
  -- Candidate reusable dependencies: `quasi_poly_weak_mlsi` (below),
  -- `weak_transport_cost_inequality`, `Real.exp_le_exp`, `Real.log_le_log`.
  -- Suggested continuation: derive the quantitative bound from Theorem C.1
  -- (which is stated with explicit constants) once the weak MLSI statement is
  -- available, using `Real.exp (poly log)` monotonicity estimates.

/-- **Corollary 2.12 (Quasi-poly weak MLSI; Theorem B.8)**,
arXiv:2412.01732v1 p.8. In the context of Theorem 2.9, for the semigroup
`S t = e^{t L_Λ}` and the Gibbs state `σ`, there is a decay-rate function
`α : ℝ → ℝ` with `α(ε) > 0` and `1/α(ε) = O(exp(poly log(N/ε)))` such that

`D(S t ρ‖σ) ≤ e^{-α(ε)t} D(ρ‖σ) + ε`

for every state `ρ`, every `ε > 0` and every `t ≥ 0`. -/
def quasi_poly_weak_mlsi {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {I : Type} [Fintype I] [DecidableEq I]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (σ : Density I)
    (S : ℝ → Density I → Density I)
    (hUniform : ∃ K ξ : ℝ, 0 < K ∧ 0 < ξ ∧ ∀ A C Dd : Finset Λ,
      mcmi A C Dd ≤ K * (Fintype.card Λ : ℝ) * Real.exp (- setDistOf dist A C / ξ))  : Prop :=
    ∃ α : ℝ → ℝ,
      (∀ ε : ℝ, 0 < ε → 0 < α ε) ∧
      (∃ (a : ℝ) (b : ℕ) (C : ℝ), 0 < C ∧ ∀ ε : ℝ, 0 < ε →
        1 / α ε ≤ C * Real.exp (a * (Real.log ((Fintype.card Λ : ℝ) / ε) + 1) ^ b)) ∧
      (∀ (ρ : Density I) (ε t : ℝ), 0 < ε → 0 ≤ t →
        relEnt (S t ρ) σ ≤ Real.exp (-(α ε) * t) * relEnt ρ σ + ε)
  -- Source: arXiv:2412.01732v1, Corollary 2.12 (p.8) and Theorem B.8
  -- (p.39, eqs. (65)–(67)).
  -- Proof route (Theorem B.8): compute
  --   D(ρ‖σ) ≤ ∑_{a,i} e^{2βgJ|C_{a,i}^∂|} e^{2βgJ|C_{a,i}^{∂∂}|} e^{2gJ} (χ⁰_min)^{-1}
  --              EP_{L_{C_{a,i}^∂}}(ρ) + D 2^D K N e^{-c/ξ}            (66)
  --           = O(exp(O((N/ε)^D log(N/ε)))) EP_{L_Λ}(ρ) + ε,          (67)
  -- choosing `c = max{ξ log(KD2^D N/ε), r}` and `ℓ = 2D(k+c)+1`; the
  -- coefficient of `EP_{L_Λ}` is the inverse weak-MLSI constant `1/α(ε)`, and
  -- Gröbwall's lemma gives the exponential decay `e^{-α(ε)t}`.
  -- Lean gap: the Davies generators, entropy production and the weak AT with
  -- constants are interface data; the Gröbwall argument (Lemma B.4) is not
  -- formalised (see `entropy_production_integral_bound`).
  -- Candidate reusable dependencies: `weak_approximate_tensorization_uniform`,
  -- `davies_conditional_entropy_bound`, `finite_temperature_comparison`,
  -- `infinite_temperature_mlsi`, `entropy_production_integral_bound`,
  -- `Real.exp_le_exp`; the Frozen `mlsi_relativeEntropy_decay`
  -- (GapWaveLindbladSemigroup) provides the Gronwall engine for a *fixed*
  -- decay rate.
  -- Suggested continuation: instantiate the Frozen
  -- `mlsi_relativeEntropy_decay` with `α := α ε` once `1/α(ε)` is bounded;
  -- `Real.exp` estimates then convert (67) into the stated shape.

/-- **Corollary 2.13 (Polylogarithmic weak MLSI)**, arXiv:2412.01732v1 p.8,
eq. (16). In the notation of Theorem 2.9, under the additional assumption of
a local gap that is at most polynomially decaying with degree `μ ∈ ℕ`,

`D(S t ρ‖σ) ≤ e^{-α(ε)t} D(ρ‖σ) + ε`

with `1/α(ε) = O((log(N/ε))^{D(1+μ)})`. -/
def polylog_weak_mlsi {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {I : Type} [Fintype I] [DecidableEq I]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (σ : Density I)
    (S : ℝ → Density I → Density I) (D : ℕ) (μ : ℕ)
    (gap : Finset Λ → ℝ) (Cgap : ℝ)
    (hUniform : ∃ K ξ : ℝ, 0 < K ∧ 0 < ξ ∧ ∀ A C Dd : Finset Λ,
      mcmi A C Dd ≤ K * (Fintype.card Λ : ℝ) * Real.exp (- setDistOf dist A C / ξ))
    (hPolyGap : 0 < Cgap ∧ ∀ A : Finset Λ, Cgap * (A.card : ℝ) ^ (-(μ : ℝ)) ≤ gap A)  : Prop :=
    ∃ α : ℝ → ℝ,
      (∀ ε : ℝ, 0 < ε → 0 < α ε) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
        1 / α ε ≤ C * (Real.log ((Fintype.card Λ : ℝ) / ε) + 1) ^ (D * (1 + μ))) ∧
      (∀ (ρ : Density I) (ε t : ℝ), 0 < ε → 0 ≤ t →
        relEnt (S t ρ) σ ≤ Real.exp (-(α ε) * t) * relEnt ρ σ + ε)
  -- Source: arXiv:2412.01732v1, Corollary 2.13 (p.8, eq. (16)); the underlying
  -- estimate is Theorem B.10 (p.39).
  -- Proof route: replace the exponential local bound of Lemma 2.11 by the
  -- polynomial cMLSI bound of Lemma B.9, `α_c(L_A) ≥ Ω(|A|^{-1-μ})`; the
  -- resulting weak MLSI coefficient scales as `(log(N/ε))^{D(1+μ)}` (the extra
  -- `D` powers come from the `D+1` levels and the `|C_{a,i}| = ℓ^D` cell-size
  -- bound with `ℓ = O(log(N/ε))`).
  -- Lean gap: as for Corollary 2.12, plus the local-gap assumption is recorded
  -- only as an interface hypothesis `hPolyGap` (see `poly_gap_to_cmlsi` for
  -- the non-vacuous formulation); the model has no spectral-gap data.
  -- Candidate reusable dependencies: `poly_gap_to_cmlsi`,
  -- `weak_approximate_tensorization_uniform`, `Real.rpow_le_rpow`,
  -- `Real.log_pos`.
  -- Suggested continuation: first replace `hPolyGap` by the concrete
  -- hypothesis of `poly_gap_to_cmlsi` (a local-gap function `λ` with the
  -- polynomial lower bound), then re-run the Theorem B.8 computation.

/-- **Theorem 2.14 (Mixing under polynomial local gap)**,
arXiv:2412.01732v1 p.9. Under a uniform polynomial local gap of degree `μ`,
and with the MCMI decay assumption of Theorem 2.9,

`t_mix^{1}(ε) = O((log(N/ε²))^{1+D(1+μ)})` and
`t_mix^{W1}(ε) = O((log log(N/ε²))^{1+D(1+μ)})`. -/
def mixing_under_poly_gap {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (tMixTrace tMixW1 : ℝ → ℝ)
    (D μ : ℕ)
    (hUniform : ∃ K ξ : ℝ, 0 < K ∧ 0 < ξ ∧ ∀ A C Dd : Finset Λ,
      mcmi A C Dd ≤ K * (Fintype.card Λ : ℝ) * Real.exp (- setDistOf dist A C / ξ))  : Prop :=
    (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      tMixTrace ε ≤ C * (Real.log ((Fintype.card Λ : ℝ) / ε ^ 2) + 1) ^ (1 + D * (1 + μ))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      tMixW1 ε ≤ C * (Real.log (Real.log ((Fintype.card Λ : ℝ) / ε ^ 2) + 2) + 1) ^ (1 + D * (1 + μ)))
  -- Source: arXiv:2412.01732v1, Theorem 2.14 (p.9); non-asymptotic forms in
  -- Theorem C.2 (Appendix C.2).
  -- Proof route: the polylogarithmic weak MLSI (Corollary 2.13) yields
  -- exponential decay `D(S t ρ‖σ) ≤ e^{-α(ε)t}D(ρ‖σ) + ε` with
  -- `1/α(ε) = O((log(N/ε))^{D(1+μ)})`; Pinsker's inequality converts the L1
  -- (trace-distance) mixing time into `O(1/α(ε))` up to log factors, and the
  -- W1 bound of Theorem 2.10 improves `log(N/ε²)` to `log log(N/ε²)`.
  -- Lean gap: the local spectral gap assumption and its conversion to a cMLSI
  -- constant (Lemma B.9 / eq. (15)) are interface hypotheses; Pinsker's
  -- inequality between relative entropy and trace distance is available in
  -- the Frozen `relative_entropy_density_bridge`/DPI interface only in
  -- qualitative form.
  -- Candidate reusable dependencies: `polylog_weak_mlsi`,
  -- `weak_transport_cost_inequality`, `Real.log_le_log`,
  -- `Real.rpow_le_rpow`, Frozen `traceDistance`.
  -- Suggested continuation: prove `mixingTime`-style bounds by instantiating
  -- the Frozen `mixingTime` with the decay rate of Corollary 2.13 and using
  -- `Real.log` monotonicity.

end Qatlib.Papers.GibbsSampling25.MainResults.Mixing
