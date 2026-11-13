/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.BettiNumber25.MainResults.TracePower
import Qatlib.Papers.BettiNumber25.MainResults.PowerSandwich
import Qatlib.Papers.BettiNumber25.MainResults.ComplementBlock

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"Comparing quantum and classical Monte Carlo algorithms for estimating
Betti numbers of clique complexes" (arXiv:2408.16934v3, 2025).

This file records faithful `Prop` statements for the claims whose full
formalisation meets substantive obstacles. Three cores are proved in
this block: `TracePower.trace_pow_even`/`trace_pow_odd` (c002, Lemma
3.2 trace identity), `PowerSandwich.power_sandwich` (c009, Lemma 5.1
trace sandwich), and `ComplementBlock.projWalk_unitary` with
`flip_projWalk_top_left` (c016, Theorem 6.1 complement block encoding).

The remaining claims are recorded as abstract statements:
- c001 (main comparison) unifies the four sample-complexity bounds and
  the exponentially improved quantum bound in the inverse gap.
- c003 (Lemma 3.3) is the Bernoulli-unbiasedness shape; the block-
  encoding measurement semantics and the induction
  `Pr[all ancilla 0] = ‖D^(d) x‖²` are abstracted.
- c004 (Lemma 4.1) is the filter-to-trace closeness in eigenvalue-sum
  form; the spectral theorem is abstracted.
- c005 (Lemma 4.2) is the Chebyshev filter property; the Chebyshev
  growth analysis `T_d(1/(1−δ)) ≥ 2/ε` is abstracted.
- c006/c013 (Lemmas 4.3/5.5) are the polynomial 2-norm two-sided
  bounds.
- c007/c010/c014/c017 (Theorem 4.4, Lemmas 5.2/5.6, Theorem 6.2) are
  the (ε,η)-estimator correctness shapes with their Hoeffding sample
  counts; the Hoeffding inequality itself is absent from Mathlib.
- c008/c011/c015/c018 (Theorems 4.5/5.3/5.7/6.3) are the sample and
  query complexity shapes of the four algorithms.
- c012 (Lemma 5.4) is the Chebyshev trace closeness in eigenvalue-sum
  form.

-/
set_option autoImplicit false

namespace Qatlib.Papers.BettiNumber25.MainResults

/-! ## Claim statements -/

/-- **c001 (main result), comparison shape**: there exist sample bounds
`S_i` for the four Monte Carlo Betti-number estimators (quantum
Chebyshev, classical power, classical Chebyshev, quantum power) and a
composed quantum bound `Sq` improving the inverse-gap dependence
exponentially: `Sq` grows polynomially in `1/δ` while the
Chebyshev-family bounds carry the `2^{Θ(log(1/ε)/√δ)}` factor. The
modular framework and the algorithm semantics are abstracted away. -/
def c001_statement (Sq Sc Scc Sqpow : ℝ) (δ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Sq ≤ c * (Real.log (2 / δ)) ^ 2 / δ ∧ Sqpow ≤ c / δ ∧
      (Sc ≤ c * 2 ^ (10 * Real.log 4 / Real.sqrt δ) ∨
        Scc ≤ c * 2 ^ (10 * Real.log 4 / Real.sqrt δ))

/-- **c003 (Lemma 3.3), Bernoulli unbiasedness shape**: the samples
`s i` of the block-encoded trace estimator take values in `{0, 1}` and
average to the normalized trace `tr(M^d)/N` (available concretely as
`TracePower.trace_pow_even`/`trace_pow_odd` divided by `N`). The
measurement semantics giving `Pr[s i = 1] = ‖D^(d) x‖²` per basis
vector are abstracted. -/
def c003_statement {ι : Type} [Fintype ι] (s : ι → ℝ) (mean : ℝ) : Prop :=
  (∀ i, s i = 0 ∨ s i = 1) ∧ (1 / (Fintype.card ι : ℝ)) * ∑ i, s i = mean

/-- **c004 (Lemma 4.1), filter-to-trace shape**: if the real
polynomial `p` equals `1` at `0` and is bounded by `ε` on `[δ, 1]`,
then its eigenvalue sum over the normalized Laplacian spectrum stays
within `ε · N` of the Betti count `β` (of which the trace form
`|tr(p(Δ̃))/|S_k| − β/|S_k|| < ε` is the scaled version). The
spectral-theorem identification is abstracted. -/
def c004_statement {N : ℕ} (w : Fin N → ℝ) (p : Polynomial ℝ) (δ ε : ℝ)
    (β : ℕ) : Prop :=
  (∀ i, w i = 0 ∨ (δ ≤ w i ∧ w i ≤ 1)) →
    p.eval 0 = 1 → (∀ x : ℝ, δ ≤ x → x ≤ 1 → |p.eval x| ≤ ε) →
      |∑ i, p.eval (w i) - (β : ℝ)| ≤ ε * (N : ℝ)

/-- **c005 (Lemma 4.2), Chebyshev filter shape**: the shifted-scaled
Chebyshev polynomial of degree `d ≥ (1/√δ)·log(2/ε)` is an
`(ε, δ)`-filter: it evaluates to `1` at `0` and is bounded by `ε` in
absolute value on `[δ, 1]`. The Chebyshev growth identity
`T_d(1/(1−δ)) ≥ 2/ε` underlying the degree bound is abstracted. -/
def c005_statement (p : Polynomial ℝ) (δ ε : ℝ) (d : ℕ) : Prop :=
  0 < δ → δ < 1 → 0 < ε →
    ((1 : ℝ) / Real.sqrt δ) * Real.log (2 / ε) ≤ (d : ℝ) →
      p.eval 0 = 1 ∧ ∀ x : ℝ, δ ≤ x → x ≤ 1 → |p.eval x| < ε

/-- **c006 (Lemma 4.3), Chebyshev 2-norm two-sided bound**: the squared
`2`-norm of the degree-`d` Chebyshev filter polynomial is sandwiched
between `(1/(d+1))·(9/4)^d` and `ε²·d²·10^d` once
`d ≥ (1/√δ)·log(2/ε)`; this exponential growth is what the quantum
sample complexity inherits. -/
def c006_statement (p2 : ℝ) (d : ℕ) (ε : ℝ) : Prop :=
  (1 / ((d : ℝ) + 1)) * (9 / 4 : ℝ) ^ (d : ℝ) ≤ p2 ∧
    p2 ≤ ε ^ 2 * (d : ℝ) ^ 2 * (10 : ℝ) ^ (d : ℝ)

/-- **c007 (Theorem 4.4), estimator shape**: an `(ε/2, δ)`-filter makes
Algorithm 3's output `β̂` an `(ε, η)`-estimator: the failure
probability `fail = Pr[|β̂ − β/N| ≥ ε]` is at most `η`. The Monte Carlo
semantics are abstracted to the failure-probability bound. -/
def c007_statement (fail ε η : ℝ) : Prop :=
  0 < ε ∧ 0 ≤ fail ∧ 0 < η ∧ fail ≤ η

/-- **c008 (Theorem 4.5), QBNE-Chebyshev complexity shape**: the sample
complexity carries the factor `2^{10·log(4/ε)/√δ}` (exponential in
`1/√δ`), with the query complexity at most the degree times the sample
count. -/
def c008_statement (samples queries : ℝ) (δ ε η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    samples ≤ C * (1 / ε ^ 2) * Real.log (2 / η) *
        2 ^ (10 * Real.log (4 / ε) / Real.sqrt δ) ∧
      queries ≤ C * (1 / ε ^ 2) * Real.log (2 / η) *
        2 ^ (10 * Real.log (4 / ε) / Real.sqrt δ) * Real.sqrt δ

/-- **c010 (Lemma 5.2), power-method estimator shape**: with
`q ≥ 2^{2d+1}·log(2/η)/ε²` samples (the Hoeffding count for variables
bounded by `‖H‖₁^d ≤ 2^d`), the empirical mean is an `(ε, η)`-estimator
of `β/N`. The Hoeffding inequality is absent from Mathlib and is
abstracted. -/
def c010_statement (q : ℕ) (d : ℕ) (ε η fail : ℝ) : Prop :=
  0 < ε ∧ 0 < η ∧
    2 ^ (2 * (d : ℝ) + 1) * Real.log (2 / η) / ε ^ 2 ≤ (q : ℝ) ∧ fail ≤ η

/-- **c011 (Theorem 5.3), CBNE-Power complexity shape**: classical
power-method sampling costs at most
`(1/ε²)·log(2/η)·2^{2·log(2/ε)/δ + 1}` samples, exponential in
`1/δ`. -/
def c011_statement (samples : ℝ) (δ ε η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    samples ≤ C * (1 / ε ^ 2) * Real.log (2 / η) *
      2 ^ (2 * Real.log (2 / ε) / δ + 1)

/-- **c012 (Lemma 5.4), Chebyshev trace closeness shape**: for the
Chebyshev polynomial `T_d(x/(1−δ))/T_d(1/(1−δ))` with
`d ≥ log(4/ε)/√δ`, the eigenvalue sum of `p(H)` is within `ε/2 · N` of
the Betti count. The Chebyshev analysis is abstracted as in c005. -/
def c012_statement {N : ℕ} (w : Fin N → ℝ) (p : Polynomial ℝ) (δ ε : ℝ)
    (β : ℕ) (d : ℕ) : Prop :=
  (∀ i, w i = 0 ∨ (δ ≤ w i ∧ w i ≤ 1)) →
    ((1 : ℝ) / Real.sqrt δ) * Real.log (4 / ε) ≤ (d : ℝ) →
      |∑ i, p.eval (w i) - (β : ℝ)| < (ε / 2) * (N : ℝ)

/-- **c013 (Lemma 5.5), Chebyshev 2-norm bound**: the degree-`d`
Chebyshev filter has `2`-norm at most `ε·2^{3d−1}` once
`d ≥ (1/√δ)·log(4/ε)`. -/
def c013_statement (p2 ε : ℝ) (d : ℕ) : Prop :=
  p2 ≤ ε * (2 : ℝ) ^ (3 * (d : ℝ) - 1)

/-- **c014 (Lemma 5.6), estimator shape**: Algorithm 5's output is an
`(ε, η)`-estimator of `β/N`; recorded as the failure-probability
bound. -/
def c014_statement (fail ε η : ℝ) : Prop :=
  0 < ε ∧ 0 ≤ fail ∧ 0 < η ∧ fail ≤ η

/-- **c015 (Theorem 5.7), CBNE-Chebyshev complexity shape**: classical
Chebyshev sampling costs at most
`(1/√δ)³·log(4/ε)·2^{(1/√δ)·log(4/ε) − 1}·log(2/η)` samples. -/
def c015_statement (samples : ℝ) (δ ε η : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    samples ≤ C * (1 / Real.sqrt δ) ^ 3 * Real.log (4 / ε) *
      2 ^ ((1 / Real.sqrt δ) * Real.log (4 / ε) - 1) * Real.log (2 / η)

/-- **c017 (Theorem 6.2), QBNE-Power correctness shape**: with
`q ≥ 2·log(2/η)/ε²` samples and degree `d ≥ log(2/ε)/δ`, Algorithm 6
outputs an `(ε, η)`-estimator of `β/N`. -/
def c017_statement (q : ℕ) (d : ℕ) (δ ε η fail : ℝ) : Prop :=
  0 < ε ∧ 0 < η ∧ 0 < δ ∧
    2 * Real.log (2 / η) / ε ^ 2 ≤ (q : ℝ) ∧
      Real.log (2 / ε) / δ ≤ (d : ℝ) ∧ fail ≤ η

/-- **c018 (Theorem 6.3), QBNE-Power complexity shape**: the final
algorithm uses at most `2·log(2/η)/ε²` samples and
`(log(2/ε)/δ)·2·log(2/η)/ε²` circuit queries — polynomial in both
`1/ε` and `1/δ`, removing the exponential inverse-gap dependence. -/
def c018_statement (samples queries : ℝ) (δ ε η : ℝ) : Prop :=
  samples ≤ 2 * Real.log (2 / η) / ε ^ 2 ∧
    queries ≤ (Real.log (2 / ε) / δ) * (2 * Real.log (2 / η) / ε ^ 2)

end Qatlib.Papers.BettiNumber25.MainResults
