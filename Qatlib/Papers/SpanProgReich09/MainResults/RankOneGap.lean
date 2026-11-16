/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Foundations.PureStateMath.KernelGap.RankOneGap
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section


/-!
# Source rank-one perturbation gap and missing-witness counterexamples

The PSD bridge realizes the corrected first inequality of Lemma 8.10 of
arXiv:0904.2759v1. The literal missing-witness original contracts remain below
as predicates with finite counterexamples; the source scaling argument requires
a nonzero kernel witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Foundations.PureStateMath.KernelGap

namespace Qatlib.Papers.SpanProgReich09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Positive semidefinite matrices satisfy the corrected first Lemma 8.10 inequality. -/
theorem psdGapBound (X : Matrix I I ℂ) (hX : X.PosSemidef)
    (t φ : I → ℂ) (δ : ℝ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2) (ξ : I → ℂ) :
    δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤
      sqNorm ((X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ) :=
  gapBound X hX.1 t φ δ hn hker hover ξ

/-- Actual low-eigenvalue support yields the corrected second Lemma 8.10 inequality. -/
theorem psdLowGap {J : Type*} [Fintype J] [DecidableEq J]
    (X : Matrix I I ℂ) (hX : X.PosSemidef)
    (t φ : I → ℂ) (δ : ℝ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2)
    (W : Matrix I J ℂ) (lam : J → ℝ) (hW : Wᴴ * W = 1)
    (heig : (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
      W * Matrix.diagonal (fun i => (lam i : ℂ)))
    (hlam : ∀ i, 0 ≤ lam i) (κ : ℝ) (a : J → ℂ)
    (hsupp : ∀ i, κ < lam i → a i = 0) (ξ : I → ℂ) (hξ : ξ = W *ᵥ a) :
    δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤ κ ^ 2 * sqNorm ξ := by
  rw [hξ]
  exact (psdGapBound X hX t φ δ hn hker hover (W *ᵥ a)).trans
    (lowEigBound (X + Matrix.vecMulVec t (fun i => star (t i))) W lam
      hW heig hlam κ a hsupp)

/-- Both inequalities of Lemma 8.10 with an actual nonzero witness and low-spectral expansion. -/
theorem lemma810 (X : Matrix I I ℂ) (hX : X.PosSemidef)
    (t φ : I → ℂ) (δ : ℝ) (hn : φ ≠ 0) (hker : X *ᵥ φ = 0)
    (hover : δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2)
    (ξ : I → ℂ) :
    (δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤
      sqNorm ((X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ)) ∧
    ∀ (k : ℕ) (W : Matrix I (Fin k) ℂ) (lam : Fin k → ℝ),
      Wᴴ * W = 1 →
      (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
        W * Matrix.diagonal (fun i => (lam i : ℂ)) →
      (∀ i, 0 ≤ lam i) → ∀ (κ : ℝ) (a : Fin k → ℂ),
      (∀ i, κ < lam i → a i = 0) → ξ = W *ᵥ a →
      δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤ κ ^ 2 * sqNorm ξ := by
  refine ⟨psdGapBound X hX t φ δ hn hker hover ξ, ?_⟩
  intro k W lam hW heig hlam κ a hsupp hξ
  exact psdLowGap X hX t φ δ hn hker hover W lam hW heig hlam κ a hsupp ξ hξ

/-- The legacy first Lemma 8.10 conclusion without a nonzero kernel witness. -/
def OldGap : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (X : Matrix J J ℂ),
    X.PosSemidef → ∀ (t φ : J → ℂ) (δ : ℝ),
      0 < δ → X *ᵥ φ = 0 → δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2 →
      ∀ ξ : J → ℂ, δ * ‖Qatlib.Foundations.PureStateMath.Inner t ξ‖ ^ 2 ≤
        sqNorm ((X + Matrix.vecMulVec t (fun i => star (t i))) *ᵥ ξ)

/-- A zero witness on a one-dimensional space refutes the omitted-condition legacy goal. -/
theorem oldGapFalse : ¬OldGap := by
  intro h
  have hbad := h (Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.PosSemidef.zero
    (fun _ => 1) 0 2 (by norm_num) (by simp) (by simp [sqNorm, Qatlib.Foundations.PureStateMath.Inner]) (fun _ => 1)
  norm_num [sqNorm, Qatlib.Foundations.PureStateMath.Inner, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply] at hbad

/-- The legacy Theorem 8.9 estimate without the essential nonzero kernel witness. -/
def OldEigGap : Prop :=
  ∀ (J : Type) [Fintype J] [DecidableEq J] (X : Matrix J J ℂ),
    X.PosSemidef → ∀ (t φ : J → ℂ) (δ : ℝ),
      0 < δ → X *ᵥ φ = 0 →
      δ * sqNorm φ ≤ ‖Qatlib.Foundations.PureStateMath.Inner t φ‖ ^ 2 →
      ∀ (Λ : ℝ), 0 ≤ Λ → ∀ (k : ℕ) (W : Matrix J (Fin k) ℂ) (lam : Fin k → ℝ),
        Wᴴ * W = 1 → W * Wᴴ = 1 →
        (X + Matrix.vecMulVec t (fun i => star (t i))) * W =
          W * Matrix.diagonal (fun i => (lam i : ℂ)) →
        (∀ i, 0 ≤ lam i) →
        δ * (∑ i, if lam i ≤ Λ ∧
          Qatlib.Foundations.PureStateMath.Inner t (fun j => W j i) ≠ 0 then
          ‖Qatlib.Foundations.PureStateMath.Inner t (fun j => W j i)‖ ^ 2 / lam i
          else 0) ≤ 4 * Λ

/-- A complete one-dimensional eigenframe refutes the missing-witness Theorem 8.9. -/
theorem oldEigGapFalse : ¬OldEigGap := by
  intro h
  have hbad := h (Fin 1) (0 : Matrix (Fin 1) (Fin 1) ℂ) Matrix.PosSemidef.zero
    (fun _ => 1) 0 5 (by norm_num) (by simp)
    (by simp [sqNorm, Qatlib.Foundations.PureStateMath.Inner])
    1 (by norm_num) 1 (1 : Matrix (Fin 1) (Fin 1) ℂ) (fun _ => 1)
    (by simp) (by simp) (by ext i j; fin_cases i; fin_cases j; norm_num [Matrix.vecMulVec_apply])
    (by intro i; norm_num)
  norm_num [Qatlib.Foundations.PureStateMath.Inner, dotProduct] at hbad

end Qatlib.Papers.SpanProgReich09.MainResults
