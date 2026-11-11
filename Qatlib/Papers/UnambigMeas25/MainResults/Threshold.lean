/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel

set_option backward.isDefEq.respectTransparency false

/-!
# The threshold setting — Section 4.2

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025).

This file states Proposition 3 (p. 22), Theorem 5 (p. 24), Proposition 16
(p. 22), Theorem 4 (p. 22), Proposition 17 (p. 22–23), Corollary 2 (p. 23),
Proposition 18 (p. 23) and Proposition 19 (p. 23).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults.Threshold

open Matrix BigOperators Filter
open scoped Classical MatrixOrder ComplexOrder BigOperators Topology

/-- The integer threshold `⌈γ d⌉` used in Theorem 5. -/
def gammaD (γ : ℝ) (d : ℕ) : ℕ := ⌈γ * (d : ℝ)⌉₊

/-- **Proposition 3** (arXiv:2510.07298v2, p. 22).  In the threshold setting,
`ρ(S, τ) ≤ min { 2^τ ∑_{i∈V} |α̂_i|² : V is τ-universal }`.

Source: Proposition 3, p. 22.  Proof: for a `τ`-universal `V`, take the dual
solution `b_i = 2^τ 1_V(i)`; Equation (3) follows from the `τ`-universality of
`V`, hence `ρ = σ^L ≤ 2^τ ∑_{i∈V}|α̂_i|²`; take the infimum over `V`. -/
def proposition3 {n : ℕ} (S : SymFamily n) (τ : ℕ) (hτ : τ ≤ n) : Prop :=
  rho S (Cthr τ) ≤ universalValue S τ
  -- Paper: arXiv:2510.07298v2, Proposition 3, p. 22.
  -- Key steps: b_i = 2^τ * 1_V(i); the coset constraint at level k becomes
  -- |{i ∈ V : G i = s}| ≥ 2^{k-τ}, proved by extending G to a full-rank
  -- (n-τ)×n matrix and using τ-universality of V; then σ^L(S,b) = 2^τ ∑_{i∈V}|α̂_i|².
  -- Gap: no `sigmaL_le_of_dualFeasible` lemma, and no counting argument for the
  -- extension of G.
  -- Suggested tactic: build `b` and show `DualFeasible (Cthr τ) b`; use
  -- `csInf_le` to bound `universalValue`; conclude via Proposition 17.

/-- **Theorem 5** (arXiv:2510.07298v2, p. 24).  Let `γ > 2`, let `d → ∞`, and
let `ε = ∑_{i ∉ B_d}|α̂_i|²`.  Then `ρ(S, ⌈γd⌉) ≤ ε(1+o(1))`.

The paper's `o(1)` is formalised in the usual `ε`-form: for every `ε' > 0` the
inequality `ρ(S, ⌈γd⌉) ≤ ε(1+ε')` holds eventually in `n` along any sequence of
symmetric families. -/
def theorem5 (γ : ℝ) (hγ : 2 < γ) (S : (n : ℕ) → SymFamily n)
    (d : ℕ → ℕ) (hd : Tendsto (fun n => (d n : ℝ)) atTop atTop) : Prop :=
  ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n : ℕ in atTop,
      rho (S n) (Cthr (gammaD γ (d n))) ≤ epsilonOut (S n) (d n) * (1 + ε')
  -- Paper: arXiv:2510.07298v2, Theorem 5, p. 24; proof in Appendix B.
  -- Key steps: for τ = ⌈γd⌉ one exhibits a τ-universal set V with
  -- ∑_{i∈V}|α̂_i|² ≤ ε(1+o(1)) by taking V = (a small set meeting every affine
  -- subspace in B_d), using |V ∩ B_d| ≤ Σ_{a≤d} C(τ,a) and γ > 2; then apply
  -- Proposition 3/17.
  -- Gap: the paper's argument is asymptotic and combinatorial; the model has no
  -- asymptotics of `epsilonOut`, no probabilistic-method argument for `V`.
  -- Suggested tactic: prove the finite estimate
  -- `universalValue S τ ≤ epsilonOut S d * (1 + ε')` for `(1+ε') ≥ (|V∩B_d|/...)`,
  -- then `Filter.eventually_atTop` to extract a threshold N.
  -- Candidate dependencies: Proposition 19 (this file), `Nat.choose_le_pow`.

/-- **Proposition 16** (arXiv:2510.07298v2, p. 22).  `V` is `k`-universal iff it
meets every dual coset `D_H(s)`, `H ∈ Λ_k`, `s ∈ F₂^{n-k}`.

Source: Proposition 16, p. 22.  Proof: an affine `k`-subspace is exactly a
fibre `{x : G x = s}` of a full-rank `(n-k) × n` matrix `G`, and these are
precisely the dual cosets `D_H(s)`. -/
theorem proposition16 (n k : ℕ) (V : Finset (F2 n)) :
    UniversalParity n k V ↔ UniversalFinset n k V := by
  constructor
  · intro h W hW
    obtain ⟨G, s, hWs⟩ := hW
    obtain ⟨i, hiV, hi⟩ := h G s
    exact ⟨i, hiV, hWs ▸ hi⟩
  · intro h G s
    obtain ⟨i, hiV, hi⟩ := h {x : F2 n | matVec G.1 x = s} ⟨G, s, rfl⟩
    exact ⟨i, hiV, hi⟩

/-- **Theorem 4** (arXiv:2510.07298v2, p. 22).  `ρ(S, τ) = 0` iff there is a
`τ`-universal set `V` on which all Fourier coefficients `α̂_i` vanish.

Source: Theorem 4, p. 22.  Proof: `⇐` is Corollary 2; `⇒` is Proposition 18
combined with strong duality Proposition 15. -/
def theorem4 {n : ℕ} (S : SymFamily n) (τ : ℕ) (hτ : τ ≤ n) : Prop :=
  rho S (Cthr τ) = 0 ↔
      ∃ V : Finset (F2 n), UniversalFinset n τ V ∧ ∀ i ∈ V, S.hat i = 0
  -- Paper: arXiv:2510.07298v2, Theorem 4, p. 22.
  -- Key steps: (⇐) Corollary 2; (⇒) Proposition 18 gives V from ρ = σ^L = 0
  -- after Proposition 15 identifies the two values.
  -- Gap: Corollary 2 and Proposition 18 are stated below but not proved.
  -- Suggested tactic: `constructor`; `·` use `proposition18` + `proposition15`;
  -- `·` use `corollary2`.

/-- **Proposition 17** (arXiv:2510.07298v2, p. 22–23).  In the threshold
setting `ρ(S;τ) = σ^L(S;τ) ≤ min{2^τ ∑_{i∈V}|α̂_i|² : V is τ-universal}`.

Source: Proposition 17, p. 22–23.  Proof: the equality is strong duality
(Proposition 15); the inequality is the explicit dual solution `b_i = 2^τ 1_V(i)`
as in Proposition 3. -/
def proposition17 {n : ℕ} (S : SymFamily n) (τ : ℕ) (hτ : τ ≤ n) : Prop :=
  rho S (Cthr τ) = sigmaL S (Cthr τ) ∧
      sigmaL S (Cthr τ) ≤ universalValue S τ
  -- Paper: arXiv:2510.07298v2, Proposition 17, p. 22–23.
  -- Key steps: Proposition 15 for the equality; the dual solution 2^τ 1_V and
  -- Constraint (11) for the inequality (via `sInf_le`).
  -- Gap: strong duality and the coset-counting lemma are not proved.
  -- Suggested tactic: `⟨proposition15 S (Cthr τ) (fun k => ?_), ?_⟩`;
  -- for the second, `csInf_le` with `b := fun i => 2^τ * (if i ∈ V then 1 else 0)`.

/-- **Corollary 2** (arXiv:2510.07298v2, p. 23).  If there exists a
`τ`-universal set `V` with `α̂_i = 0` for all `i ∈ V`, then `ρ(S;τ) = 0`. -/
def corollary2 {n : ℕ} (S : SymFamily n) (τ : ℕ) (hτ : τ ≤ n)
    (V : Finset (F2 n)) (hV : UniversalFinset n τ V)
    (hzero : ∀ i ∈ V, S.hat i = 0) : Prop :=
  rho S (Cthr τ) = 0
  -- Paper: arXiv:2510.07298v2, Corollary 2, p. 23.
  -- Key steps: Proposition 17 gives ρ ≤ 2^τ ∑_{i∈V}|α̂_i|² = 0, and ρ ≥ 0.
  -- Gap: Proposition 17 not proved; `rho` is an `sSup`, so also need 0 ≤ rho.
  -- Suggested tactic: `le_antisymm`; bound `rho` by `universalValue = 0` using
  -- `proposition17`; show `universalValue S τ ≤ 0` via `csInf_le` and `hzero`.

/-- **Proposition 18** (arXiv:2510.07298v2, p. 23).  If `ρ(S;τ) = σ^L(S;τ) = 0`,
then there is a `τ`-universal set on which all `α̂_i` vanish.

Source: Proposition 18, p. 23.  Proof: take an optimal dual solution `b`, let
`T = {i : b_i ≠ 0}`; dual feasibility gives `T ∩ D_H(s) ≠ ∅` for all `k ≥ τ`,
so `T` contains a `τ`-universal set; `σ^L = 0` forces `α̂_i = 0` on `T`. -/
def proposition18 {n : ℕ} (S : SymFamily n) (τ : ℕ) (hτ : τ ≤ n)
    (hρ : rho S (Cthr τ) = 0) (hσ : sigmaL S (Cthr τ) = 0) : Prop :=
  ∃ V : Finset (F2 n), UniversalFinset n τ V ∧ ∀ i ∈ V, S.hat i = 0
  -- Paper: arXiv:2510.07298v2, Proposition 18, p. 23.
  -- Key steps: choose an optimal dual `b` (attainment of the `sInf`); set
  -- `T = {i : b i ≠ 0}`; each dual constraint at level k ≥ τ forces
  -- `T ∩ D_H(s) ≠ ∅`, hence `T` is τ-universal by Proposition 16; finally
  -- `σ^L = 0` and `b ≥ 0` imply `α̂_i = 0` for `i ∈ T`.
  -- Gap: attainment of the dual optimum and the passage from `sInf = 0` to an
  -- optimal `b` are not available; `T` should be a `Finset`.
  -- Suggested tactic: use `Nat.card`/`Finset.univ.filter` to build `T`, show
  -- universality via `proposition16`, and use `Finset.sum_eq_zero_iff` to get
  -- the individual vanishings.

/-- **Proposition 19** (arXiv:2510.07298v2, p. 23).  For every `k`-dimensional
affine subspace `V ⊆ 𝔽₂ⁿ`, `|V ∩ B_d| ≤ ∑_{a=0}^{d} C(k,a)`.

Source: Proposition 19, p. 23.  Proof: write `V = v + W`, choose `k` columns
`I` of a generator of `W` forming an invertible `k × k` matrix; then
`V ∩ B_d` injects into the Hamming ball of radius `d` in `𝔽₂^k`, whose size is
`∑_{a≤d} C(k,a)`. -/
def proposition19 (n k d : ℕ) (V : Set (F2 n)) (hV : AffineKSubspace n k V) : Prop :=
  Nat.card (V ∩ ball d : Set (F2 n)) ≤
      ∑ a ∈ Finset.range (d + 1), Nat.choose k a
  -- Paper: arXiv:2510.07298v2, Proposition 19, p. 23.
  -- Key steps: pick an invertible k×k column submatrix `G_I` of the generator
  -- `G ∈ Λ_{n-k}`; `s ↦ (G_I)ᵀ s + v_I` is a bijection onto V, and
  -- `|Gᵀ s + v|_H ≥ |(G_I)ᵀ s + v_I|_H`; count the latter by Hamming ball size.
  -- Gap: no column-selection / rank argument for matrices over `ZMod 2`, and no
  -- cardinality API for `Nat.card` of a set intersection.
  -- Suggested tactic: `obtain ⟨G, s, rfl⟩ := hV`; build the bijection
  -- `Finset.univ.filter (· ∈ ball d)` and compare cardinalities; bound by
  -- `Finset.card_biUnion` and `Finset.sum_choose`-style identities.
  -- Candidate dependencies: `Matrix.exists_mulVec_injective`,
  -- `Finset.card_le_card` with an injection.

end Qatlib.Papers.UnambigMeas25.MainResults.Threshold
