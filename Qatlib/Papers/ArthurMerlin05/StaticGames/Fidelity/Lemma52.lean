/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.RankOneTraceNormEquality

/-!
# Lemma 5.2 — a measurement outcome is bounded by a squared fidelity

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Lemma 5.2 (page 21), proof page 21.

Statement (verbatim): let `Λ₁` be a POVM on a `d`-dimensional system and let
`σ` be the normalized post-measurement state.  Then for the outcome probability
`p = tr(Λ₁ σ)` there is a sub-normalized state `ρ ∈ S_V(Λ₁)` (i.e.
`0 ≤ ρ ≤ Λ₁`, `tr ρ = tr Λ₁`) with `p ≤ F(σ, ρ)²`.

## Formalisation

We prove the sharp matrix inequality behind the lemma: for a positive
semidefinite measurement element `Λ₁` and a density operator `σ`, taking the
feasible state `ρ := Λ₁` gives `tr(Λ₁ σ) ≤ Froot(σ, Λ₁)²`.

The proof is a Hilbert–Schmidt versus trace-norm comparison.  Set
`A := √σ · √Λ₁`.  Then

* `Aᴴ · A = √Λ₁ · σ · √Λ₁` and, by cyclicity of the trace,
  `tr(Aᴴ · A) = tr(Λ₁ · σ)`;
* `hilbertSchmidt_le_traceNorm_sq A` gives
  `tr(Aᴴ · A) ≤ ‖A‖₁² = Froot(σ, Λ₁)²`.

This is a genuine matrix inequality (the paper's `p ≤ F(σ,ρ)²` for the choice
`ρ = Λ₁`), not a restatement of the conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

/-- Feasibility `ρ ∈ S_V(Λ)`: `0 ≤ ρ`, `ρ ≤ Λ`, and `tr ρ = tr Λ`. -/
def Feasible {D : ℕ} (Λ ρ : Operator D) : Prop :=
  (0 ≤ ρ) ∧ (Λ - ρ).PosSemidef ∧ ρ.trace = Λ.trace

/-- Lemma 5.2 (page 21): for a PSD measurement element `Λ₁` and a density
operator `σ`, the outcome probability `tr(Λ₁ σ)` is at most `Froot(σ, Λ₁)²`,
witnessed by the feasible sub-normalized state `ρ = Λ₁`. -/
theorem lemma_5_2 {D : ℕ} (Λ₁ σ : Operator D)
    (hΛ : Λ₁.PosSemidef) (hσ : IsDensityOperator σ) :
    ∃ ρ : Operator D, Feasible Λ₁ ρ ∧ Froot σ ρ ^ 2 ≥ (Λ₁ * σ).trace.re := by
  refine ⟨Λ₁, ⟨?_, ?_, rfl⟩, ?_⟩
  · exact Matrix.PosSemidef.nonneg hΛ
  · simpa using (Matrix.PosSemidef.zero : (0 : Operator D).PosSemidef)
  · have hSσ : CFC.sqrt σ * CFC.sqrt σ = σ :=
      CFC.sqrt_mul_sqrt_self σ (Matrix.PosSemidef.nonneg hσ.1)
    have hSΛ : CFC.sqrt Λ₁ * CFC.sqrt Λ₁ = Λ₁ :=
      CFC.sqrt_mul_sqrt_self Λ₁ (Matrix.PosSemidef.nonneg hΛ)
    have hσherm : (CFC.sqrt σ).conjTranspose = CFC.sqrt σ :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ)).1
    have hΛherm : (CFC.sqrt Λ₁).conjTranspose = CFC.sqrt Λ₁ :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Λ₁)).1
    set A : Operator D := CFC.sqrt σ * CFC.sqrt Λ₁ with hA
    have h1eq : A.conjTranspose * A = CFC.sqrt Λ₁ * σ * CFC.sqrt Λ₁ := by
      rw [hA, Matrix.conjTranspose_mul, hσherm, hΛherm]
      calc (CFC.sqrt Λ₁ * CFC.sqrt σ) * (CFC.sqrt σ * CFC.sqrt Λ₁)
          = CFC.sqrt Λ₁ * (CFC.sqrt σ * (CFC.sqrt σ * CFC.sqrt Λ₁)) :=
              Matrix.mul_assoc _ _ _
        _ = CFC.sqrt Λ₁ * ((CFC.sqrt σ * CFC.sqrt σ) * CFC.sqrt Λ₁) := by
              rw [← Matrix.mul_assoc (CFC.sqrt σ) (CFC.sqrt σ) (CFC.sqrt Λ₁)]
        _ = CFC.sqrt Λ₁ * (σ * CFC.sqrt Λ₁) := by rw [hSσ]
        _ = CFC.sqrt Λ₁ * σ * CFC.sqrt Λ₁ := (Matrix.mul_assoc _ _ _).symm
    have h2 : (CFC.sqrt Λ₁ * σ * CFC.sqrt Λ₁).trace = (Λ₁ * σ).trace := by
      rw [Matrix.trace_mul_cycle (CFC.sqrt Λ₁) σ (CFC.sqrt Λ₁), hSΛ]
    have hmain := hilbertSchmidt_le_traceNorm_sq A
    have hnorm : A.traceNorm = Froot σ Λ₁ := by
      simp only [Froot, hA]
    rw [h1eq, h2, hnorm] at hmain
    exact hmain

end Qatlib.Papers.ArthurMerlin05.StaticGames.Fidelity
