/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLossEstimation

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
The remaining theorems prove only their displayed algebraic inequalities or identities.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.LossEstimation
open Qatlib.Papers.QRegression21.MainResults


variable {N d : ℕ}

/-- The sample least-squares loss `L_S(θ) = (1/N)∑_i (⟨x_i,θ⟩ - y_i)²` of Section 3
(fixed arXiv:2110.13086v2, p. 16). -/
def lsLoss (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ) (θ : Fin d → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, (∑ j, X i j * θ j - y i) ^ 2

/-- The Hessian quadratic form of `L_S`: `⟨v, ∇²L_S v⟩ = (2/N)‖Xv‖₂²` for all `v`
(fixed arXiv:2110.13086v2, proof of Theorem 3.2, p. 16). -/
def hessianForm (X : Fin N → Fin d → ℝ) (v : Fin d → ℝ) : ℝ :=
  (2 / (N : ℝ)) * ∑ i, (∑ j, X i j * v j) ^ 2

/-- **Theorem 3.2** (fixed arXiv:2110.13086v2, p. 16). If all entries of the data matrix lie
in `[-1,1]`, then the Frank-Wolfe curvature constant of `L_S` with respect to `B₁^d` is at
most `8`.  This is exactly the bound `(2/N)‖X(s-x)‖₂² ≤ 8` for `x, s ∈ B₁^d` obtained from
`∇²L_S = 2XᵀX/N`.

Proof route (paper, p. 16): each coordinate of `X(s-x)` is a sum of `d` terms of modulus at
most `|s_j - x_j|`, hence at most `‖s‖₁ + ‖x‖₁ ≤ 2` in modulus; therefore
`(2/N)‖X(s-x)‖₂² ≤ (2/N)·4N = 8`. -/
theorem theorem_3_2_curvature (X : Fin N → Fin d → ℝ)
    (hX : ∀ i j, |X i j| ≤ 1) :
    ∀ x s : Fin d → ℝ, l1Ball x → l1Ball s →
      hessianForm X (fun j => s j - x j) ≤ 8 := by
  intro x s hx hs
  have hrow : ∀ i : Fin N, |∑ j, X i j * (s j - x j)| ≤ 2 := by
    intro i
    have h1 : |∑ j, X i j * (s j - x j)|
        ≤ ∑ j, |X i j * (s j - x j)| :=
      Finset.abs_sum_le_sum_abs (fun j => X i j * (s j - x j)) Finset.univ
    have h2 : ∑ j, |X i j * (s j - x j)| ≤ ∑ j, |s j - x j| := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hXj := hX i j
      have hnn : 0 ≤ |s j - x j| := abs_nonneg _
      nlinarith
    have h3 : ∑ j, |s j - x j| ≤ 2 := by
      have hsplit : ∑ j, |s j - x j| ≤ ∑ j, (|s j| + |x j|) := by
        apply Finset.sum_le_sum
        intro j _
        have h := abs_add_le (s j) (-(x j))
        simpa [sub_eq_add_neg] using h
      have hsum : ∑ j, (|s j| + |x j|) = l1Norm s + l1Norm x := by
        simp [l1Norm, Finset.sum_add_distrib]
      have hs' : l1Norm s ≤ 1 := hs
      have hx' : l1Norm x ≤ 1 := hx
      linarith
    linarith
  have hsum4 : ∑ i, (∑ j, X i j * (s j - x j)) ^ 2 ≤ 4 * (N : ℝ) := by
    calc ∑ i, (∑ j, X i j * (s j - x j)) ^ 2 ≤ ∑ _i : Fin N, (4 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hle := abs_le.mp (hrow i)
          have h := sq_le_sq' hle.1 hle.2
          nlinarith
      _ = 4 * (N : ℝ) := by simp [mul_comm]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [hessianForm]
  · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simp only [hessianForm]
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ hNpos]
    nlinarith

/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem_3_4_gradient_unitary`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem_3_4_gradient_unitary_statement (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ)
    (θ : Fin d → ℝ) (hθ : l1Ball θ) (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ 64 * Real.log (1 / δ) / β ∧
      alg.successProb ≥ 1 - δ


/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem_3_5_loss_unitary`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem_3_5_loss_unitary_statement (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ)
    (θ : Fin d → ℝ) (hθ : l1Ball θ) (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ 64 * Real.log (1 / δ) / β ∧
      alg.successProb ≥ 1 - δ


/-- **Statement only — not proved in Qatlib.** Resource specification for `corollary_3_6_uniform`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def corollary_3_6_uniform_statement (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ) {m : ℕ}
    (θs : Fin m → Fin d → ℝ) (hθ : ∀ h, l1Ball (θs h)) (β δ : ℝ)
    (hβ : 0 < β) (hδ : 0 < δ)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ 64 * Real.log (1 / δ) / β ∧
      alg.successProb ≥ 1 - δ


/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem_3_7_sample_set`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem_3_7_sample_set_statement (X : Fin N → Fin d → ℝ) (y : Fin N → ℝ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.gateCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.spaceCost ≤ 64 / ε ∧
      alg.successProb ≥ 2 / 3


/-- **Statement only — not proved in Qatlib.** Resource specification for `corollary_3_8_distribution`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def corollary_3_8_distribution_statement (N d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ 64 * Real.log (d : ℝ) / ε ^ 2)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.gateCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 2 ∧
      alg.spaceCost ≤ 64 / ε ∧
      alg.successProb ≥ 2 / 3


/-- **Statement only — not proved in Qatlib.** Resource specification for `corollary_3_9_classical_bits`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def corollary_3_9_classical_bits_statement (N d : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ 64 * Real.log (d : ℝ) / ε ^ 2)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧
      alg.queryCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 3 ∧
      alg.gateCost ≤ 64 * Real.sqrt (d : ℝ) / ε ^ 3 ∧
      alg.spaceCost ≤ 64 / ε ∧
      alg.successProb ≥ 2 / 3


end Qatlib.Papers.QRegression21.MainResults.LossEstimation
