/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QDecoding25.MainResults.FourierShift
public import Qatlib.Papers.QDecoding25.MainResults.Distinguishing
public import Qatlib.Papers.QDecoding25.MainResults.MetricDistribution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"The Quantum Decoding Problem: Tight Achievability Bounds and
Application to Regev's Reduction" (arXiv:2509.24796v2, 2025,
Blanvillain–Chailloux–Tillich).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Three cores are proved in
this block:

- `FourierShift.qdft_shift` (Lemma 3): the Fourier transform of
  the coset state `|ψ_c⟩ = Σ_e f(e)|c+e⟩` is `f̂(y)·χ_c(y)`, the
  translation–modulation duality behind the whole analysis.
- `Distinguishing.avg_success_le_card` (Lemma 9): `N` states in
  a `K`-dimensional space have average distinguishing probability at
  most `K/N`.
- `MetricDistribution.exists_unique_metric_distribution` (Lemma 14): every positive-weight metric family `r(a) = q^{-λ w a}`
  admits a unique normalising `λ > 0`.

The remaining claims are recorded as abstract statements:

- (Theorems 1, 3, 5, 6, 7, 9 and
  Prop 8): the achievability direction — rates `R` below the entropy
  threshold `H_q(|ĝ|²)` (or the typical-set entropy `H`) are decodable
  by the pretty-good measurement, with success probability tending to
  one; each needs the PGM-success second-moment machinery
  (Lemmas 4–7, 12, 13) over typical sets.
- (Theorems 2, 4, 8): the converse direction — rates
  above the threshold force failure with probability tending to one;
  each needs the Holevo bound (Prop 4) plus the Hirschman uncertainty
  principle (Prop 1).
- (Prop 1): the discrete Hirschman uncertainty principle
  `H_q(g) + H_q(ĝ) ≥ -2 log(q+1)/log q²`-type entropic lower bound;
  needs the entropy-power/Young-inequality computation on ℤ_q.
- (Lemma 1): the two-sided typical-set cardinality estimate
  `(1-δ(ε,n)) / B(ε) ≤ |T_ε(n)|`; needs the tail estimates of i.i.d.
  products of `|ĝ|²`.
- (Prop 4): the Holevo capacity lower bound `χ ≥ H_q(ĝ) - o(1)`
  for the code-state ensemble; needs the Gram-matrix eigenvalue
  analysis of `|ψ_c⟩⟨ψ_c|` over random codes.
- (Prop 5): the closed-form PGM success probability
  `P_PGM = (1/K) Σ_y |Σ_c ...|²` for the coset ensemble; needs the
  Gram-operator diagonalisation.
- (Prop 6): uniqueness of the entropy constant `H` of a nice
  family of typical sets.
- (Lemmas 4/5): pointwise probability bounds of the
  codeword Fourier weights over typical sets.
- (Lemmas 6/7) and `pgm_success_deviation_from_typical_average_statement`/`pgm_failure_upper_bound_of_entropy_gap_statement` (Lemmas 12/13): the average
  PGM success decomposition over typical/atypical parts with the gap
  `γ = H - R` and smallness parameters `α(ε), β(ε)`.
- (Lemma 8): the state-closeness `‖ψ̃_c - ψ_c‖` under truncated
  Fourier supports.
- (Lemma 10): the perturbation stability
  `p ≤ p̃ + max_i √(1 - |⟨φ_i|φ̃_i⟩|²)`; needs the optimisation
  argument over the joint measurement.
- (Lemma 11): the exponential tail sum
  `Σ_u S_u p̃(u) = O(q^{-b²ε²/2})`.
- (Prop 7): the tensor case `f = g^{⊗n}` PGM success formula.
- (Prop 9): the random-code decoupling property used for
  non-tensor functions.
- (Theorem 10): the Regev-reduction application — PGM decoding
  of LWE-type coset states from `g^{⊗n}`-states.

-/
set_option autoImplicit false

open Filter Topology

namespace Qatlib.Papers.QDecoding25.MainResults

/-! ## Shared shapes -/

/-- Success probabilities tending to one, the asymptotic success
conclusion of every achievability claim. -/
def tends_to_one (p : ℕ → ℝ) : Prop :=
  Tendsto p atTop (𝓝 1)

/-- Failure probabilities tending to one, the conclusion of every
converse claim. -/
def tends_to_one_fail (p : ℕ → ℝ) : Prop :=
  Tendsto p atTop (𝓝 1)

/-! ## Claim statements -/

/-- **(Theorem 1), achievability shape**: for a prime power `q`,
a rate `R < H_q(|ĝ|²)` (the Rényi-type entropy of the Fourier weights
of the local state `g`) and the PGM success probability `p i` at block
length `i`, the success probability tends to one. The ensemble, the
entropy functional and the PGM are abstracted away. -/
def tensor_decoding_below_fourier_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **(Theorem 2), converse shape**: for `H_q(|ĝ|²) < R`, the
decoding failure probability tends to one for any measurement. -/
def tensor_decoding_above_fourier_entropy_failure_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ tends_to_one_fail pfail

/-- **(Proposition 1), Hirschman shape**: the discrete
uncertainty principle — the sum of the position entropy of `g` and the
Fourier entropy of `ĝ` is bounded below by a `q`-dependent constant
`bound`. -/
def hirschman_entropy_sum_lower_bound_statement (Hg Hghat bound : ℝ) : Prop :=
  bound ≤ Hg + Hghat

/-- **(Theorem 3), interval achievability shape**: for
`R ∈ (0, H_q(|ĝ|²))` the PGM success probability tends to one. -/
def tensor_dual_sampling_success_below_fourier_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  0 < R ∧ R < H ∧ tends_to_one p

/-- **(Theorem 4), interval converse shape**: for
`R ∈ (H_q(|ĝ|²), 1)` the failure probability of any decoder tends to
one. -/
def decoding_failure_in_upper_rate_interval_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ R < 1 ∧ tends_to_one_fail pfail

/-- **(Lemma 1), typical-set cardinality shape**: the typical set
`T_ε(n)` of the product distribution `|ĝ|^{2n}` has cardinality at
least `(1 - δ(ε,n)) / B(ε)` where `B` is the ε-ball weight. -/
def typical_set_cardinality_lower_bound_statement (δ B : ℝ) (card : ℝ) : Prop :=
  (1 - δ) / B ≤ card

/-- **(Proposition 4), Holevo shape**: the Holevo quantity `χ` of
the code-state ensemble is at least `H_q(|ĝ|²) - ε`, the capacity
lower bound that powers every converse. -/
def holevo_capacity_lower_bound_statement (H ε χ : ℝ) : Prop :=
  H - ε ≤ χ

/-- **(Proposition 5), PGM formula shape**: the PGM success
probability on the coset ensemble equals the closed form `s / K` where
`s` is the squared-sum statistic and `K = |𝒞|`. -/
def pgm_success_eq_normalized_square_sum_statement (ppgm s K : ℝ) : Prop :=
  ppgm = s / K

/-- **(Proposition 6), uniqueness shape**: the entropy per symbol
`H` of a nice family of typical sets is unique. -/
def typical_set_entropy_uniqueness_statement (H1 H2 : ℝ) : Prop :=
  H1 = H2

/-- **(Theorem 5), sequence achievability shape**: along the
block-length sequence `n_i`, rate `R < H` implies PGM success
tending to one. -/
def typical_set_sequence_decoding_below_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **(Lemma 4), pointwise shape**: each Fourier-weight
probability `prob s` at a typical point `s` is bounded by `bound s`
uniformly. -/
def typical_fourier_weight_expectation_bound_statement {X : Type} (prob bound : X → ℝ) : Prop :=
  ∀ s, prob s ≤ bound s

/-- **(Lemma 5), pointwise shape**: the strengthened pointwise
bound on typical-set Fourier weights under the Lemma-4 assumptions. -/
def typical_fourier_weight_variance_bound_statement {X : Type} (prob bound : X → ℝ) : Prop :=
  ∀ s, prob s ≤ bound s

/-- **(Lemma 6), average success shape**: under the gap condition
`2β(ε) + α(ε) ≤ γ/2` with `γ = H - R`, the average PGM success over
the typical part is at least `q^{-n(γ-…)}`-controlled: recorded as the
lower bound `lo ≤ avg`. -/
def average_typical_pgm_success_of_entropy_gap_statement (γ α β lo avg : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → lo ≤ avg

/-- **(Lemma 7), per-state success shape**: under the same gap
condition, each individual codeword is decoded with probability at
least `lo ≤ pstate`. -/
def per_codeword_pgm_success_of_entropy_gap_statement (γ α β lo pstate : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → lo ≤ pstate

/-- **(Theorem 6), general-function achievability shape**: for
general (non-tensor) function families `f_i` with typical-set entropy
`H`, rate `R < H` implies PGM success tending to one. -/
def general_function_decoding_below_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **(Lemma 8), state closeness shape**: the truncated codeword
states `ψ̃ c` approximate the true coset states `psi c` uniformly
within `ε` in norm. -/
def truncated_coset_state_norm_error_statement {I : Type} (psi psit : I → ℂ) (ε : ℝ) : Prop :=
  ∀ c, ‖psit c - psi c‖ ≤ ε

/-- **(Lemma 10), perturbation stability shape**: the
distinguishing success `p` against true states is at most the success
`p̃` against the perturbed states plus the perturbation radius
`δ = max_i √(1 - |⟨φ_i|φ̃_i⟩|²)`. -/
def distinguishing_success_perturbation_bound_statement (p ptild δ : ℝ) : Prop :=
  p ≤ ptild + δ

/-- **(Lemma 11), exponential tail shape**: the partial tail sum
`sum` of the truncated distribution is `O(bound)` with `bound =
q^{-b²ε²/2}`: recorded as a big-O pair. -/
def rank_metric_tail_sum_upper_bound_statement (sum bound : ℝ) : Prop :=
  ∃ C > 0, sum ≤ C * bound

/-- **(Theorem 7), finite-length achievability shape**: for rates
below the typical-set threshold along sequences `(a_i)`, `(b_i)`,
`(n_i)`, the PGM success tends to one. -/
def rank_metric_decoding_below_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **(Theorem 8), finite-length converse shape**: for rates
above the threshold the failure probability tends to one. -/
def rank_metric_decoding_above_entropy_failure_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ tends_to_one_fail pfail

/-- **(Theorem 9), sequence converse shape**: the converse
companion of `typical_set_sequence_decoding_below_entropy_statement` for general function families. -/
def general_function_decoding_above_entropy_failure_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ tends_to_one_fail pfail

/-- **(Proposition 7), tensor formula shape**: for
`f = g^{⊗n}` the PGM success probability equals the closed form `s/K`
via the coset Gram diagonalisation. -/
def tensor_pgm_success_eq_normalized_square_sum_statement (ppgm s K : ℝ) : Prop :=
  ppgm = s / K

/-- **(Proposition 8), mixed-sequence achievability shape**:
along sequences `(a_i)`, `(b_i)`, `(n_i)` with `a_i + b_i ≤ n_i`,
rate below threshold implies success tending to one. -/
def rank_metric_dual_sampling_below_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **(Lemma 12), average decomposition shape**: under the gap
condition, the total PGM success is within `η` of the typical-part
average. -/
def pgm_success_deviation_from_typical_average_statement (γ α β η avg total : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → |total - avg| ≤ η

/-- **(Lemma 13), failure complement shape**: under the gap
condition, the failure probability is at most `hi`. -/
def pgm_failure_upper_bound_of_entropy_gap_statement (γ α β hi pfail : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → pfail ≤ hi

/-- **(Proposition 9), random-code shape**: a uniformly random
code `𝒞 ⊂ 𝔽_q^n` of rate `R ∈ (0,1)` satisfies the decoupling property
`prop` with probability tending to one as `n → ∞`. -/
def random_dual_code_tail_event_high_probability_statement (prop : ℕ → ℝ) : Prop :=
  tends_to_one prop

/-- **(Theorem 10), Regev application shape**: decoding the LWE
coset states built from `g^{⊗n}` succeeds with probability tending to
one at rates below the entropic threshold — the application of the
quantum decoding machinery to Regev's reduction. -/
def regev_application_success_below_entropy_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

end Qatlib.Papers.QDecoding25.MainResults
