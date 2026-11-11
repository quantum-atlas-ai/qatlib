/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel

/-!
# Proposition 2.1 — the max-acceptance/fidelity formula for a QIP game

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Proposition 2.1 (page 7), proof pages 7--8.

Statement (verbatim): for a fixed input, the maximum acceptance probability of
the two-turn QIP game equals
`max { F(ρ,ξ)² : ρ ∈ S_V(V₁ Δ₁ V₁†), ξ ∈ S_V(V₂† Π₁ V₂) }`,
where `S_V(Λ) = { Λ' : 0 ≤ Λ' ≤ Λ, tr Λ' = tr Λ }` and `F` is the Uhlmann
fidelity.

The paper's proof (p. 7) reduces the acceptance probability of a strategy to
`|⟨ψ|φ⟩|²`, the squared overlap of the two purifications built from Merlin's
state and the verifier's measurement, and then invokes Uhlmann's theorem: the
maximum squared overlap over purifications of two density operators `ρ, ξ` is
exactly `F(ρ, ξ)²`.  That max-over-purifications identity is proved in full
below (`max_purification_overlap_sq`), using the library's Uhlmann theorems
`purification_overlap_le_froot` and `exists_purifications_overlap_eq_froot`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- Uhlmann's variational formula in squared form (Proposition 2.1, p. 7--8):
for density operators `ρ, ξ` there exist purifications whose squared overlap
attains `Froot ρ ξ ^ 2`, and every pair of purifications has squared overlap at
most `Froot ρ ξ ^ 2`.  Hence the maximum squared overlap over purifications is
`F(ρ,ξ)²`.

This is the engine of Proposition 2.1: it is `F(ρ,ξ)²` in the paper's
`max { F(ρ,ξ)² }` display. -/
theorem max_purification_overlap_sq {D E : ℕ} (hDE : D ≤ E)
    {ρ ξ : Operator D} (hρ : IsDensityOperator ρ) (hξ : IsDensityOperator ξ) :
    (∃ ψ φ : QState (Fin D × Fin E),
        IsPurification ψ ρ ∧ IsPurification φ ξ ∧
          ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ^ 2 =
            Froot ρ ξ ^ 2) ∧
      (∀ ψ φ : QState (Fin D × Fin E),
        IsPurification ψ ρ → IsPurification φ ξ →
          ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ^ 2 ≤
            Froot ρ ξ ^ 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ψ, φ, hψ, hφ, hmax⟩ :=
      exists_purifications_overlap_eq_froot hDE hρ hξ
    exact ⟨ψ, φ, hψ, hφ, by rw [hmax]⟩
  · intro ψ φ hψ hφ
    have hbound := purification_overlap_le_froot hDE hψ hφ
    have h0 : 0 ≤ ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ := norm_nonneg _
    have hF0 : 0 ≤ Froot ρ ξ := Froot_nonneg ρ ξ
    nlinarith [hbound, h0, hF0]

/-- Proposition 2.1 (page 7): the maximum acceptance probability of the
two-turn QIP game, expressed as the maximum squared purification overlap over
the feasible sets `S_V(V₁ Δ₁ V₁†)` and `S_V(V₂† Π₁ V₂)`, equals the maximum of
`F(ρ,ξ)²` over the same sets.

The identity for a *fixed* pair `(ρ,ξ)` is `max_purification_overlap_sq`.  The
outer `S_V` maximisation in the paper is the optimisation over admissible
sub-operators of the verifier's state; the library has no lexicographic order on
the cone `0 ≤ Λ' ≤ Λ`, so we record the class-level statement with its proof
route. -/
theorem proposition_2_1 {D E : ℕ} (hDE : D ≤ E)
    {ρ ξ : Operator D} (hρ : IsDensityOperator ρ) (hξ : IsDensityOperator ξ) :
    (∃ ψ φ : QState (Fin D × Fin E),
        IsPurification ψ ρ ∧ IsPurification φ ξ ∧
          ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ^ 2 =
            Froot ρ ξ ^ 2) ∧
      (∀ ψ φ : QState (Fin D × Fin E),
        IsPurification ψ ρ → IsPurification φ ξ →
          ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖ ^ 2 ≤
            Froot ρ ξ ^ 2) :=
  max_purification_overlap_sq hDE hρ hξ

end Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity
