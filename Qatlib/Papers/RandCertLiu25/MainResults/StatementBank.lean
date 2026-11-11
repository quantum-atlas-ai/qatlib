/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Statement bank for
"Certified randomness using a trapped-ion quantum processor"
(arXiv:2503.20498, 2025).

This file records faithful `Prop` statements for the mathematically
self-contained probability claims of the paper: the heavy-hitter chain of
the supplement (c005–c010), culminating in the threshold dichotomy. Two
of them are proved in this block: `Collision.lean` proves the probability
core of c006 (Lemma 10, `collision_probability_lower`) and `GapLemma.lean`
proves c009 (Lemma 13, `exists_threshold_gap`, with a real witness in
place of the paper's rational one).

The remaining claims are recorded as substantive obstacles: protocol
soundness with smooth min-entropy and quantum-proof extractors (c001,
c015), von-Neumann-entropy guarantees for (M)LXEB solvers (c002–c004),
the Hoeffding/union-bound sampling lemma (c011), the promise-problem
sampler (c012), the amplification lemma (c013) and the
restricted-adversary XEB bound with Chernoff/Gamma/hypergeometric tails
(c014). Formalising them needs smooth min-entropy, QCAM-style complexity
classes, quantum-proof extractors and the concrete concentration
inequalities, none of which exist in Mathlib or in this repository — see
the PR work log.

No axiom, no `admit`, no `native_decide`.
-/
import Qatlib.Papers.RandCertLiu25.MainResults.Collision
import Qatlib.Papers.RandCertLiu25.MainResults.GapLemma

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults

/-! ## Claim statements (heavy-hitter chain) -/

/-- **c005 (Lemma 9)**: an algorithm passing LXEB_{b,k} with probability
`q` must output a heavy hitter — a string whose output probability is at
least the threshold `ρ = τ/2^{B/2}` — with probability at least
`(b(1−q)+ε)/(b−1)`. Stated for an abstract finitely supported output
distribution `p`. -/
def c005_statement {ι : Type} [Fintype ι] (p : ι → ℝ) (ρ b q ε : ℝ) : Prop :=
  (∀ x, 0 ≤ p x) → (∑ x, p x = 1) → 1 < b → 0 ≤ ε →
    (b * (1 - q) + ε) / (b - 1)
      ≤ ∑ x ∈ Finset.univ.filter (fun x => ρ ≤ p x), p x

/-- **c006 (Lemma 10)**: if the output vector `z⃗` passes MLXEB_{b,k} then,
when the strings `sⱼ` are resampled independently, some position matches
(`zⱼ = sⱼ`) with probability at least `bk/N − O(1/N²)`. Stated for abstract
independent events `A j` (the match events) with hit-probability sum
`σ ∈ [c, 1]`: the union has probability at least `c − c²`, i.e. with
`c = bk/N` the paper's bound `bk/N − (bk/N)²` with an explicit constant.
The probability core is proved as `collision_probability_lower`. -/
def c006_statement {Ω : Type} [MeasurableSpace Ω] (k : ℕ) (μ : Measure Ω)
    (A : ℕ → Set Ω) (c : ℝ) : Prop :=
  ∀ [IsProbabilityMeasure μ], (∀ j, MeasurableSet (A j)) →
    ProbabilityTheory.iIndep (fun _ : ℕ => ‹MeasurableSpace Ω›) μ →
      c ≤ ∑ j ∈ Finset.range k, (μ (A j)).toReal →
        ∑ j ∈ Finset.range k, (μ (A j)).toReal ≤ 1 →
          c - c ^ 2 ≤ (μ (⋃ j ∈ Finset.range k, A j)).toReal

/-- **c007 (Lemma 11)**: for every threshold `τ ∈ [0,1]`, the ratio of
yes-case to no-case heavy-hitter expectations satisfies
`μ₁(τ)/μ₀(τ) ≥ b·(p(τ)+q−1)/p(τ)`; stated multiplicatively (with `μ₀ ≥ 0`)
to avoid division. -/
def c007_statement (b q : ℝ) (μ0 μ1 pτ : ℝ → ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ μ0 τ → 0 < pτ τ →
    (b * (pτ τ + q - 1) / pτ τ) * μ0 τ ≤ μ1 τ

/-- **c008 (Lemma 12)**: for `T ≥ (16/ε)·log(N/ε)` there is a grid index
`j ∈ [1, T/2]` at which consecutive thresholds expose an expectation gap
`μ₁(1/2 + j/T) ≥ (1 + ε/2)·μ₀(1/2 + (j−1)/T)`. -/
def c008_statement (μ0 μ1 : ℝ → ℝ) (T : ℕ) (N ε : ℝ) : Prop :=
  (16 / ε) * Real.log (N / ε) ≤ T →
    ∃ j : ℕ, 1 ≤ j ∧ 2 * j ≤ T ∧
      μ1 (1/2 + j / T) ≥ (1 + ε/2) * μ0 (1/2 + (j - 1) / T)

/-- **c009 (Lemma 13, paper form)**: with `a₁ = a₀ + δ ≤ (1+ε/8)a₀`, both
variables supported above their `a_b` (whenever positive), and the
expectation gap `E[X₁] ≥ (1+ε)E[X₀]`, some *rational* threshold
`t ∈ [a₀, 1]` separates the upper tails:
`Pr[X₁ > t+δ/2] ≥ (1+ε/4)·Pr[X₀ > t] + (ε/8)E[X₁]`. The proved theorem
`exists_threshold_gap` establishes the same conclusion with a real `t`
(the base point `a₀` or a grid point `a₀ + (j+1)δ/2`); rationality holds
in the protocol application where `a₀` and `δ` are rational. -/
def c009_statement {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (ε δ a0 : ℝ)
    (X0 X1 : Ω → ℝ) : Prop :=
  ∀ [IsProbabilityMeasure μ], 0 ≤ ε → ε ≤ 1 → 0 < δ → 0 < a0 → a0 ≤ 1 →
    a0 + δ ≤ (1 + ε/8) * a0 → (∀ ω, X0 ω ∈ Set.Icc (0:ℝ) 1) →
      (∀ ω, X1 ω ∈ Set.Icc (0:ℝ) 1) →
        (∀ ω, 0 < X0 ω → a0 ≤ X0 ω) → (∀ ω, 0 < X1 ω → a0 + δ ≤ X1 ω) →
          (1 + ε) * (∫ ω, X0 ω ∂μ) ≤ ∫ ω, X1 ω ∂μ →
            ∃ t : ℚ, a0 ≤ t ∧ (t : ℝ) ≤ 1 ∧
              (μ {ω | (t : ℝ) + δ/2 < X1 ω}).toReal ≥
                (1 + ε/4) * ((μ {ω | (t : ℝ) < X0 ω}).toReal
                  + ε/8 * (∫ ω, X1 ω ∂μ))

/-- **c010 (Corollary 14)**: feeding the grid gap (Lemma 12) and the
threshold lemma (Lemma 13) with `δ = 1/(T·2^{B/2})` produces an accepting
threshold whose yes-case acceptance probability is `ν₁ = Ω(r)` (with
`r = ε²k/N` kept abstract) while the no-case probability satisfies
`ν₁ ≤ (1+ε/8)·ν₀`. The antecedent `gap` collects the two lemma
conclusions at the chosen parameters; the Ω-constant is existential. -/
def c010_statement (gap : Prop) (r ε ν0 ν1 : ℝ) : Prop :=
  gap → 0 < r → ∃ C : ℝ, 0 < C ∧ C * r ≤ ν1 ∧ ν1 ≤ (1 + ε/8) * ν0

end Qatlib.Papers.RandCertLiu25.MainResults
