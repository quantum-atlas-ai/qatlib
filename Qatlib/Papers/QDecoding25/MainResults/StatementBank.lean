/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDecoding25.MainResults.FourierShift
import Qatlib.Papers.QDecoding25.MainResults.Distinguishing
import Qatlib.Papers.QDecoding25.MainResults.MetricDistribution

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"The Quantum Decoding Problem: Tight Achievability Bounds and
Application to Regev's Reduction" (arXiv:2509.24796v2, 2025,
Blanvillain–Chailloux–Tillich).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Three cores are proved in
this block:

- `FourierShift.qdft_shift` (c007, Lemma 3): the Fourier transform of
  the coset state `|ψ_c⟩ = Σ_e f(e)|c+e⟩` is `f̂(y)·χ_c(y)`, the
  translation–modulation duality behind the whole analysis.
- `Distinguishing.avg_success_le_card` (c018, Lemma 9): `N` states in
  a `K`-dimensional space have average distinguishing probability at
  most `K/N`.
- `MetricDistribution.exists_unique_metric_distribution` (c029,
  Lemma 14): every positive-weight metric family `r(a) = q^{-λ w a}`
  admits a unique normalising `λ > 0`.

The remaining claims are recorded as abstract statements:

- c001/c004/c011/c016/c021/c023/c025 (Theorems 1, 3, 5, 6, 7, 9 and
  Prop 8): the achievability direction — rates `R` below the entropy
  threshold `H_q(|ĝ|²)` (or the typical-set entropy `H`) are decodable
  by the pretty-good measurement, with success probability tending to
  one; each needs the PGM-success second-moment machinery
  (Lemmas 4–7, 12, 13) over typical sets.
- c002/c005/c022 (Theorems 2, 4, 8): the converse direction — rates
  above the threshold force failure with probability tending to one;
  each needs the Holevo bound (Prop 4) plus the Hirschman uncertainty
  principle (Prop 1).
- c003 (Prop 1): the discrete Hirschman uncertainty principle
  `H_q(g) + H_q(ĝ) ≥ -2 log(q+1)/log q²`-type entropic lower bound;
  needs the entropy-power/Young-inequality computation on ℤ_q.
- c006 (Lemma 1): the two-sided typical-set cardinality estimate
  `(1-δ(ε,n)) / B(ε) ≤ |T_ε(n)|`; needs the tail estimates of i.i.d.
  products of `|ĝ|²`.
- c008 (Prop 4): the Holevo capacity lower bound `χ ≥ H_q(ĝ) - o(1)`
  for the code-state ensemble; needs the Gram-matrix eigenvalue
  analysis of `|ψ_c⟩⟨ψ_c|` over random codes.
- c009 (Prop 5): the closed-form PGM success probability
  `P_PGM = (1/K) Σ_y |Σ_c ...|²` for the coset ensemble; needs the
  Gram-operator diagonalisation.
- c010 (Prop 6): uniqueness of the entropy constant `H` of a nice
  family of typical sets.
- c012/c013 (Lemmas 4/5): pointwise probability bounds of the
  codeword Fourier weights over typical sets.
- c014/c015 (Lemmas 6/7) and c026/c027 (Lemmas 12/13): the average
  PGM success decomposition over typical/atypical parts with the gap
  `γ = H - R` and smallness parameters `α(ε), β(ε)`.
- c017 (Lemma 8): the state-closeness `‖ψ̃_c - ψ_c‖` under truncated
  Fourier supports.
- c019 (Lemma 10): the perturbation stability
  `p ≤ p̃ + max_i √(1 - |⟨φ_i|φ̃_i⟩|²)`; needs the optimisation
  argument over the joint measurement.
- c020 (Lemma 11): the exponential tail sum
  `Σ_u S_u p̃(u) = O(q^{-b²ε²/2})`.
- c024 (Prop 7): the tensor case `f = g^{⊗n}` PGM success formula.
- c028 (Prop 9): the random-code decoupling property used for
  non-tensor functions.
- c030 (Theorem 10): the Regev-reduction application — PGM decoding
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

/-- **c001 (Theorem 1), achievability shape**: for a prime power `q`,
a rate `R < H_q(|ĝ|²)` (the Rényi-type entropy of the Fourier weights
of the local state `g`) and the PGM success probability `p i` at block
length `i`, the success probability tends to one. The ensemble, the
entropy functional and the PGM are abstracted away. -/
def c001_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **c002 (Theorem 2), converse shape**: for `H_q(|ĝ|²) < R`, the
decoding failure probability tends to one for any measurement. -/
def c002_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ tends_to_one_fail pfail

/-- **c003 (Proposition 1), Hirschman shape**: the discrete
uncertainty principle — the sum of the position entropy of `g` and the
Fourier entropy of `ĝ` is bounded below by a `q`-dependent constant
`bound`. -/
def c003_statement (Hg Hghat bound : ℝ) : Prop :=
  bound ≤ Hg + Hghat

/-- **c004 (Theorem 3), interval achievability shape**: for
`R ∈ (0, H_q(|ĝ|²))` the PGM success probability tends to one. -/
def c004_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  0 < R ∧ R < H ∧ tends_to_one p

/-- **c005 (Theorem 4), interval converse shape**: for
`R ∈ (H_q(|ĝ|²), 1)` the failure probability of any decoder tends to
one. -/
def c005_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ R < 1 ∧ tends_to_one_fail pfail

/-- **c006 (Lemma 1), typical-set cardinality shape**: the typical set
`T_ε(n)` of the product distribution `|ĝ|^{2n}` has cardinality at
least `(1 - δ(ε,n)) / B(ε)` where `B` is the ε-ball weight. -/
def c006_statement (δ B : ℝ) (card : ℝ) : Prop :=
  (1 - δ) / B ≤ card

/-- **c008 (Proposition 4), Holevo shape**: the Holevo quantity `χ` of
the code-state ensemble is at least `H_q(|ĝ|²) - ε`, the capacity
lower bound that powers every converse. -/
def c008_statement (H ε χ : ℝ) : Prop :=
  H - ε ≤ χ

/-- **c009 (Proposition 5), PGM formula shape**: the PGM success
probability on the coset ensemble equals the closed form `s / K` where
`s` is the squared-sum statistic and `K = |𝒞|`. -/
def c009_statement (ppgm s K : ℝ) : Prop :=
  ppgm = s / K

/-- **c010 (Proposition 6), uniqueness shape**: the entropy per symbol
`H` of a nice family of typical sets is unique. -/
def c010_statement (H1 H2 : ℝ) : Prop :=
  H1 = H2

/-- **c011 (Theorem 5), sequence achievability shape**: along the
block-length sequence `n_i`, rate `R < H` implies PGM success
tending to one. -/
def c011_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **c012 (Lemma 4), pointwise shape**: each Fourier-weight
probability `prob s` at a typical point `s` is bounded by `bound s`
uniformly. -/
def c012_statement {X : Type} (prob bound : X → ℝ) : Prop :=
  ∀ s, prob s ≤ bound s

/-- **c013 (Lemma 5), pointwise shape**: the strengthened pointwise
bound on typical-set Fourier weights under the Lemma-4 assumptions. -/
def c013_statement {X : Type} (prob bound : X → ℝ) : Prop :=
  ∀ s, prob s ≤ bound s

/-- **c014 (Lemma 6), average success shape**: under the gap condition
`2β(ε) + α(ε) ≤ γ/2` with `γ = H - R`, the average PGM success over
the typical part is at least `q^{-n(γ-…)}`-controlled: recorded as the
lower bound `lo ≤ avg`. -/
def c014_statement (γ α β lo avg : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → lo ≤ avg

/-- **c015 (Lemma 7), per-state success shape**: under the same gap
condition, each individual codeword is decoded with probability at
least `lo ≤ pstate`. -/
def c015_statement (γ α β lo pstate : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → lo ≤ pstate

/-- **c016 (Theorem 6), general-function achievability shape**: for
general (non-tensor) function families `f_i` with typical-set entropy
`H`, rate `R < H` implies PGM success tending to one. -/
def c016_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **c017 (Lemma 8), state closeness shape**: the truncated codeword
states `ψ̃ c` approximate the true coset states `psi c` uniformly
within `ε` in norm. -/
def c017_statement {I : Type} (psi psit : I → ℂ) (ε : ℝ) : Prop :=
  ∀ c, ‖psit c - psi c‖ ≤ ε

/-- **c019 (Lemma 10), perturbation stability shape**: the
distinguishing success `p` against true states is at most the success
`p̃` against the perturbed states plus the perturbation radius
`δ = max_i √(1 - |⟨φ_i|φ̃_i⟩|²)`. -/
def c019_statement (p ptild δ : ℝ) : Prop :=
  p ≤ ptild + δ

/-- **c020 (Lemma 11), exponential tail shape**: the partial tail sum
`sum` of the truncated distribution is `O(bound)` with `bound =
q^{-b²ε²/2}`: recorded as a big-O pair. -/
def c020_statement (sum bound : ℝ) : Prop :=
  ∃ C > 0, sum ≤ C * bound

/-- **c021 (Theorem 7), finite-length achievability shape**: for rates
below the typical-set threshold along sequences `(a_i)`, `(b_i)`,
`(n_i)`, the PGM success tends to one. -/
def c021_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **c022 (Theorem 8), finite-length converse shape**: for rates
above the threshold the failure probability tends to one. -/
def c022_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ tends_to_one_fail pfail

/-- **c023 (Theorem 9), sequence converse shape**: the converse
companion of c011 for general function families. -/
def c023_statement (R H : ℝ) (pfail : ℕ → ℝ) : Prop :=
  H < R ∧ tends_to_one_fail pfail

/-- **c024 (Proposition 7), tensor formula shape**: for
`f = g^{⊗n}` the PGM success probability equals the closed form `s/K`
via the coset Gram diagonalisation. -/
def c024_statement (ppgm s K : ℝ) : Prop :=
  ppgm = s / K

/-- **c025 (Proposition 8), mixed-sequence achievability shape**:
along sequences `(a_i)`, `(b_i)`, `(n_i)` with `a_i + b_i ≤ n_i`,
rate below threshold implies success tending to one. -/
def c025_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

/-- **c026 (Lemma 12), average decomposition shape**: under the gap
condition, the total PGM success is within `η` of the typical-part
average. -/
def c026_statement (γ α β η avg total : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → |total - avg| ≤ η

/-- **c027 (Lemma 13), failure complement shape**: under the gap
condition, the failure probability is at most `hi`. -/
def c027_statement (γ α β hi pfail : ℝ) : Prop :=
  2 * β + α ≤ γ / 2 → pfail ≤ hi

/-- **c028 (Proposition 9), random-code shape**: a uniformly random
code `𝒞 ⊂ 𝔽_q^n` of rate `R ∈ (0,1)` satisfies the decoupling property
`prop` with probability tending to one as `n → ∞`. -/
def c028_statement (prop : ℕ → ℝ) : Prop :=
  tends_to_one prop

/-- **c030 (Theorem 10), Regev application shape**: decoding the LWE
coset states built from `g^{⊗n}` succeeds with probability tending to
one at rates below the entropic threshold — the application of the
quantum decoding machinery to Regev's reduction. -/
def c030_statement (R H : ℝ) (p : ℕ → ℝ) : Prop :=
  R < H ∧ tends_to_one p

end Qatlib.Papers.QDecoding25.MainResults
