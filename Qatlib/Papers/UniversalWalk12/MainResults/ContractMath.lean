/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.UniversalWalk12.MainResults.Model.SourceModel
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section


/-! Literal legacy contracts with their actual quantifier strength.
The common approximant premise is stronger than the source truncation premise.
The normalization constant is chosen after the packet length, so it gives no
uniform asymptotic estimate from the source Lemma 4.
-/
set_option autoImplicit false
noncomputable section
open Set
namespace Qatlib.Papers.UniversalWalk12.MainResults.ContractMath
open Qatlib.Papers.UniversalWalk12.MainResults.Model

/-- Two vectors within the same error of a common vector differ by at most twice that error. -/
theorem commonApprox {E : Type*} [SeminormedAddCommGroup E]
    (u v w : E) (δ : ℝ) (hu : ‖u - w‖ ≤ δ) (hv : ‖v - w‖ ≤ δ) :
    ‖u - v‖ ≤ 2 * δ := by
  calc
    ‖u - v‖ = ‖(u - w) + (w - v)‖ := by congr 1; abel
    _ ≤ ‖u - w‖ + ‖w - v‖ := norm_add_le _ _
    _ ≤ δ + δ := add_le_add hu (by simpa only [norm_sub_rev] using hv)
    _ = 2 * δ := by ring

/-- The displayed truncation multiplier dominates the common-approximant error. -/
theorem truncScalar (Hnorm t δ : ℝ) (N : ℕ)
    (hH : 0 ≤ Hnorm) (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    2 * δ ≤ (4 * Real.exp 1 * Hnorm * t / (N : ℝ) + 2) *
      (δ + (2 : ℝ) ^ (-(N : ℝ)) * (1 + δ)) := by
  have ha : 0 ≤ 4 * Real.exp 1 * Hnorm * t / (N : ℝ) := by positivity
  have hb : 0 ≤ (2 : ℝ) ^ (-(N : ℝ)) * (1 + δ) := by positivity
  have hc := mul_nonneg ha hδ
  have hd := mul_nonneg ha hb
  nlinarith

/-- The literal legacy truncation bound follows from its two common-approximant premises. -/
theorem source_lemma2_truncation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (H P : E →L[ℂ] E) (Φ : E) (T δ : ℝ) (N₀ : ℕ) (hδ : 0 < δ)
    (γ : ℝ → E)
    (hγH : ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ - γ t‖ ≤ δ)
    (hγHt : ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ - γ t‖ ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ
        - NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖
      ≤ (4 * Real.exp 1 * ‖H‖ * t / (N₀ : ℝ) + 2) *
          (δ + (2 : ℝ) ^ (-(N₀ : ℝ)) * (1 + δ)) := by
  intro t ht
  exact (commonApprox _ _ (γ t) δ (hγH t ht) (hγHt t ht)).trans
    (truncScalar ‖H‖ t δ N₀ (norm_nonneg _) ht.1 hδ.le)

/-- A constant chosen after the length proves only the literal pointwise normalization target. -/
theorem source_lemma4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ket : ℤ × ℤ → E) (M L : ℕ) (hL : 0 < L) (θ : ℝ) (σ : ℤ) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      |‖twoState ket (twoAlphaAmp M L t θ σ)‖ ^ 2 - 1| ≤ C / (L : ℝ) := by
  refine ⟨|‖twoState ket (twoAlphaAmp M L t θ σ)‖ ^ 2 - 1| * L,
    mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _), ?_⟩
  have hne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [mul_div_cancel_right₀ _ hne]

end Qatlib.Papers.UniversalWalk12.MainResults.ContractMath
