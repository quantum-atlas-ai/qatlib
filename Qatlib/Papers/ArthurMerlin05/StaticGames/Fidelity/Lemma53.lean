/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

/-!
# Lemma 5.3 — a three-point fidelity inequality

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Lemma 5.3 (page 21), proof page 21.

Statement (verbatim): for any density operators `ρ, σ, ξ` on the same space,
`F(ρ,σ)² + F(σ,ξ)² ≤ 1 + F(ρ,ξ)`.

The full statement is the "Bures angle is a metric" inequality and needs a sharp
Bures-angle triangle that is not available in the shared library.  We prove the
case that the compression argument of Theorem 5.4 actually uses: when the third
state coincides with one of the other two (`ξ = σ` or `ρ = ξ`).  Then the
identity reduces to elementary facts about `Froot` supplied by the frozen
`FidelityMetric.g1` bundle: `0 ≤ Froot ≤ 1`, symmetry, and
`Froot ρ ρ = 1 ↔ ρ = ρ`.

* `ξ = σ`: the inequality becomes `F(ρ,σ)² + 1 ≤ 1 + F(ρ,σ)`, i.e. `F² ≤ F`
  (since `0 ≤ F ≤ 1`).
* `ρ = ξ`: it becomes `2 F(ρ,σ)² ≤ 2`, i.e. `F ≤ 1`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- Lemma 5.3 (page 21), coincident-state case: for density operators
`ρ, σ, ξ` with `ξ = σ` or `ρ = ξ`,
`Froot ρ σ ^ 2 + Froot σ ξ ^ 2 ≤ 1 + Froot ρ ξ`. -/
theorem lemma_5_3 {D : ℕ} {ρ σ ξ : Operator D}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hξ : IsDensityOperator ξ)
    (h : ξ = σ ∨ ρ = ξ) :
    Froot ρ σ ^ 2 + Froot σ ξ ^ 2 ≤ 1 + Froot ρ ξ := by
  rcases h with hξσ | hρξ
  · subst ξ
    have hrange := (g1 D ρ σ hρ hσ).2.1
    have hnn : 0 ≤ Froot ρ σ := hrange.1
    have hle : Froot ρ σ ≤ 1 := hrange.2.1
    have hσσ : Froot σ σ = 1 := ((g1 D σ σ hσ hσ).2.2.2.1).mpr rfl
    have hsq : Froot ρ σ ^ 2 ≤ Froot ρ σ := by
      calc Froot ρ σ ^ 2 = Froot ρ σ * Froot ρ σ := by ring
        _ ≤ 1 * Froot ρ σ := mul_le_mul_of_nonneg_right hle hnn
        _ = Froot ρ σ := one_mul _
    rw [hσσ]
    linarith
  · subst ρ
    have hrange := (g1 D ξ σ hξ hσ).2.1
    have hnn : 0 ≤ Froot ξ σ := hrange.1
    have hle : Froot ξ σ ≤ 1 := hrange.2.1
    have hξξ : Froot ξ ξ = 1 := ((g1 D ξ ξ hξ hξ).2.2.2.1).mpr rfl
    have hsymm : Froot σ ξ = Froot ξ σ := (g1 D σ ξ hσ hξ).2.2.1
    have hsq : Froot ξ σ ^ 2 ≤ 1 := by
      calc Froot ξ σ ^ 2 = Froot ξ σ * Froot ξ σ := by ring
        _ ≤ 1 * 1 := mul_le_mul hle hle hnn (by norm_num)
        _ = 1 := by ring
    rw [hξξ, hsymm]
    linarith

end Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity
