/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Uniform decay of the matrix-valued conditional mutual information

Claims c008 (Theorem 2.3), c017 (Lemma D.1) and c018 (Theorem D.2) of
arXiv:2412.01732v1.

`H_σ(A:C|D)` denotes the operator norm `‖H_σ(A:C|D)‖∞` of the MCMI of
Definition 2.2, eq. (2), carried by `McmiNorm` from the source model.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Mcmi

open Qatlib.Papers.GibbsSampling25.MainResults.Model

/-- **Theorem 2.3 (Uniform decay of the MCMI)**, arXiv:2412.01732v1 p.4,
eq. (3). Let `σ` be the Gibbs state of a `(κ,r)`-local and `J`-bounded
Hamiltonian on a graph `Λ` with growth constant `g`. If `H_Λ` admits a strong
local effective Hamiltonian (Appendix A.4.3;
`IsStrongLocalEffectiveHamiltonian`),
then there exist constants `K, ξ > 0` such that, for any partition
`Λ = A ⊔ B ⊔ C ⊔ D`,

`H_σ(A:C|D) ≤ K|Λ| exp(-dist(A,C)/ξ)`.

The `(κ,r)`-locality, `J`-boundedness and growth constant enter only through
the hypothesis that a strong local effective Hamiltonian exists (that is the
content of Appendix A.4.3); they are kept as named parameters to mirror the
source statement. -/
def uniform_mcmi_decay {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (dist : Λ → Λ → ℝ) (J r κ g β : ℝ) (hJ : 0 ≤ J) (hr : 0 < r) (hκ : 0 ≤ κ)
    (hg : 0 < g) (mcmi : McmiNorm Λ)
    (hEff : ∃ (hterm : Finset Λ → Finset Λ → ℝ) (Δ μ : ℝ),
      0 ≤ Δ ∧ 0 < μ ∧ IsStrongLocalEffectiveHamiltonian mcmi hterm Δ μ)  : Prop :=
    ∃ K ξ : ℝ, 0 < K ∧ 0 < ξ ∧ ∀ A C Dd : Finset Λ,
      mcmi A C Dd ≤ K * (Fintype.card Λ : ℝ) * Real.exp (- setDistOf dist A C / ξ)
  -- Source: arXiv:2412.01732v1, Theorem 2.3 (p.4, eq. (3)); proof via
  -- Lemma D.1 (Appendix D.1) combined with the construction of a strong
  -- effective Hamiltonian for `(κ,r)`-local `J`-bounded systems with growth
  -- constant `g` (Appendix A.4.3 / [BluhmCapelPerezHernandez2024]).
  -- Proof route: the strong local effective Hamiltonian provides effective
  -- terms `h̃^A_X` with decay `μ > 0` and interaction-norm bound `Δ`; Lemma D.1
  -- then gives `H_σ(A:C|D) ≤ 4 min{|A|,|C|} Δ e^{-μ dist(A,C)}`, and
  -- `min{|A|,|C|} ≤ |Λ|`, so the claim holds with `ξ = 1/μ` and
  -- `K = 4Δ`.
  -- Scope note: only the interface predicate `IsStrongLocalEffectiveHamiltonian`
  -- is available; the derivation of its existence from `(κ,r)`-locality,
  -- `J`-boundedness and growth constant `g` (cluster expansion of
  -- [BluhmCapelPerezHernandez2024]) is outside this file's scope, and the matrix-level MCMI is
  -- an interface datum.
  -- Related result: `mcmi_decay_from_effective_hamiltonian`
  -- (Lemma D.1 below), `Finset.card_le_univ`, `Real.exp_pos`.
  -- The cardinality estimate in this application of Lemma D.1 is
  -- `4 * min |A| |C| * Δ ≤ 4 * |Λ| * Δ`, using `Finset.card_le_univ`.

/-- **Lemma D.1 (MCMI-decay from locality of the effective Hamiltonian)**,
arXiv:2412.01732v1 p.46, eq. (73). Assume a strong effective Hamiltonian for
`H_Λ` with uniform interaction-norm bound `Δ` and decay `μ` (eq. (72)). Then
for any partition `Λ = A ⊔ B ⊔ C ⊔ D`,

`‖H(A:C|D)_σ‖∞ ≤ 4 min{|A|,|C|} Δ e^{-μ dist(A,C)}`. -/
def mcmi_decay_from_effective_hamiltonian {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (Δ μ : ℝ) (hΔ : 0 ≤ Δ) (hμ : 0 < μ)
    (hterm : Finset Λ → Finset Λ → ℝ)
    (hEff : IsStrongLocalEffectiveHamiltonian mcmi hterm Δ μ) (A C Dd : Finset Λ)  : Prop :=
    mcmi A C Dd ≤ 4 * (min A.card C.card : ℝ) * Δ * Real.exp (- μ * setDistOf dist A C)
  -- Source: arXiv:2412.01732v1, Lemma D.1 (p.46), proof on pp.46–47.
  -- Proof route (fully written out in the paper): insert the definition of
  -- the MCMI as `∑_X (h̃^{ACD}_X + h̃^D_X − h̃^{AD}_X − h̃^{CD}_X)`; the terms
  -- with `X ∩ A = ∅` or `X ∩ C = ∅` vanish by locality (`hlocal`); for the
  -- remaining `X` use the triangle inequality and (72), i.e.
  -- `∑_X ‖h̃_X‖ ≤ e^{-μ dist(A,C)} ∑_{x∈A} ∑_{X∋x} ‖h̃_X‖ e^{μ diam X}
  --           ≤ 4 |A| Δ e^{-μ dist(A,C)}`,
  -- using `dist(A,C) ≤ diam(X)` whenever `X` meets both `A` and `C`, and
  -- symmetry to replace `|A|` by `min{|A|,|C|}`.
  -- Scope note: the inequality `setDistOf dist A C ≤ (X.card : ℝ)` (diameter
  -- bound for a set meeting both `A` and `C`) and the counting estimate
  -- `∑_{X : X∩A≠∅, X∩C≠∅} ... ≤ 4 ∑_{x∈A} ∑_{X∋x} ...` are not formalised;
  -- the MCMI reconstruction and bound are assumptions (`hdiff`, `hbound`).
  -- Related inequalities and hypotheses: `Finset.sum_le_sum`,
  -- `Finset.sum_comm`, `Finset.sum_const`, `Real.exp_le_exp`,
  -- `Finset.card_le_card`, `hEff.1`, `hEff.2.1`, `hEff.2.2`.
  -- Termwise, the triangle inequality gives
  -- `|h̃^{ACD}_X + h̃^D_X − h̃^{AD}_X − h̃^{CD}_X| ≤ 4 max ...`.
  -- Summing this inequality and the interaction-norm bound over `x ∈ A`
  -- (or `x ∈ C`) gives the factor `4 * min A.card C.card * Δ`.

/-- **Theorem D.2 (MCMI decay for marginal commuting systems at high
temperature)**, arXiv:2412.01732v1 p.47. Let `H_Λ` be marginal commuting
([BluhmCapelPerezHernandez2024, Definition 3.5]). For
`β < 1/(gκ(1+κg)e^{1/2} gJ)` and every partition `Λ = A ⊔ B ⊔ C ⊔ D`,

`‖H_σ(A:C|D)‖∞ ≤ 4 min{|A|,|C|} e^{-μ dist(A,C)}`

with `μ = (1/r) log(1/(gκ(1+κg)e^{1/2} gJβ))`. -/
def mcmi_decay_marginal_commuting {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (g κ J r β : ℝ)
    (hg : 0 < g) (hκ : 0 ≤ κ) (hr : 0 < r) (hJ : 0 < J) (hβpos : 0 < β)
    (hβ : β < 1 / (g * κ * (1 + κ * g) * Real.exp (1 / 2) * g * J))
    (hEff : ∃ (hterm : Finset Λ → Finset Λ → ℝ) (Δ : ℝ), Δ = 1 ∧
      IsStrongLocalEffectiveHamiltonian mcmi hterm Δ
        ((1 / r) * Real.log (1 / (g * κ * (1 + κ * g) * Real.exp (1 / 2) * g * J * β))))
    (A C Dd : Finset Λ)  : Prop :=
    mcmi A C Dd ≤ 4 * (min A.card C.card : ℝ) *
      Real.exp (-((1 / r) * Real.log (1 / (g * κ * (1 + κ * g) * Real.exp (1 / 2) * g * J * β)))
        * setDistOf dist A C)
  -- Source: arXiv:2412.01732v1, Theorem D.2 (p.47), proof on pp.47–48.
  -- Proof route: the temperature condition `β < 1/(gκ(1+κg)e^{1/2}gJ)` gives
  -- `|||H_Λ|||_{μ_ε} < 1/(gκ(1+κg)e^2 β)`; combined with marginal
  -- commutativity ([BluhmCapelPerezHernandez2024, Theorem 3.8]) this yields a strong effective
  -- Hamiltonian with `H̃^{A}_{μ_ε} ≤ 1` for every `A`, i.e. `Δ = 1`; Lemma D.1
  -- then gives the bound with decay `μ = (1/r) log(1/(gκ(1+κg)e^{1/2}gJβ))`.
  -- Scope note: marginal commutativity of the Hamiltonian, the [BluhmCapelPerezHernandez2024]
  -- cluster-expansion theorem producing the strong effective Hamiltonian, and
  -- the matrix-level MCMI are all outside the formalised API; we record the
  -- existence of the strong effective Hamiltonian with `Δ = 1` as hypothesis
  -- `hEff`, which is exactly the conclusion of the [BluhmCapelPerezHernandez2024, Theorem 3.8]
  -- step.
  -- Related result: `mcmi_decay_from_effective_hamiltonian`;
  -- `Real.log_pos`, `Real.exp_pos`, `div_pos`, `one_div`.
  -- This is the application of Lemma D.1 with `Δ = 1` and the stated `μ`;
  -- the prefactor simplifies from `4 * min A.card C.card * 1`.

end Qatlib.Papers.GibbsSampling25.MainResults.Mcmi
