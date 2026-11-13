/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationSharedDefs
import QuantumInfo.ForMathlib.HermitianMat.CFC
import Qatlib.Concepts.MatrixWeights.ApproxGibbs

/-!
# Positive components and counterexamples for SDP contracts

This module separates provable components of the source SDP contracts from counterexamples to
their combined statements. It proves Golden--Thompson consequences through `clause21_conj12`,
identity rescaling through `clause4_lemma2_part`, parameter existence through
`clause4_normalized_kernel_part` and `clause25_conj2b_part`, and the width-rescaling identities
in `clause25_conj2_part`.

The contracts arise in the quantum SDP setting of [BrandaoSvore2017]. The refutations identify
failures in the exact quantified statements here: a scaled payoff can be negative, local
bisection budgets do not bound an arbitrary number of guesses, and the certificate objective
bound lacks a sufficient restriction on the distinguished constraint value.

## Main statements

* `clause21_conj12`: The Hermitian Golden--Thompson gap is nonnegative with equality exactly for
  commuting inputs, and the positive-definite logarithmic-input inequality holds.
* `clause4_lemma2_part` and `clause4_normalized_kernel_part`: Provide the stated rescaling and
  positive real parameter witnesses.
* `clause25_conj2_part` and `clause25_conj2b_part`: Prove the width-rescaling formulas and
  existence of a positive integer horizon.
* `clause3_conj1_refuted`, `clause3_conj3_refuted`, and `clause4_refuted`: Refute the combined
  contracts through their respective false components.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixWeights.ApproxGibbs

set_option autoImplicit false

open Qatlib.Concepts.SdpDuality.ConeSeparation Qatlib.Concepts.MatrixWeights.ApproxGibbs
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Qatlib.Concepts.SdpDuality.ConeSeparation
open Filter Topology
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib

/-- Refutes the proposed combined scaled-payoff contract under its listed positivity and width
assumptions. A scalar instance has scaled payoff trace minus two, contradicting the asserted
positive semidefiniteness. -/
theorem clause3_conj1_refuted : ¬
    (∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
        (y : Fin m → ℝ) (ρ : Operator D) (α R ε η δ : ℝ)
        (j₀ : Fin m),
      0 < D → 0 < m → 0 < α → 0 < R → 0 < ε → 0 < η → 0 < δ →
      (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
      Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
      (∀ i, 1 ≤ b i) →
      IsDensityOperator ρ →
      (∀ i, 0 ≤ y i) →
      (∑ i, b i * y i ≤ sourceWidthBudget α R ε) →
      (sourcePayoffTarget D Cv ρ α ε ≤ ∑ i, y i * (Matrix.trace (A i * ρ)).re) →
      (2 * R * ε ≤ 1 / 2) →
      ((sourceScaledPayoff A Cv α y).IsHermitian ∧
        (sourceScaledPayoff A Cv α y).PosSemidef ∧
        ‖sourceScaledPayoff A Cv α y‖ ≤ 1)
      ∧ ((∑ i, b i * (y i / (1 + 2 * R * ε))) ≤ α)
        ∧ (exactWidthSlack α R ε = sourceWidthBudget α R ε - α)
        ∧ ((sourcePayoffTarget D Cv ρ α ε - exactWidthSlack α R ε) / (1 + 2 * R * ε) ≤
          ∑ i, (y i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re)
      ∧ (∀ η' : ℝ, 0 < η' → η' < ε → ∃ T : ℕ, 0 < T ∧ η' + Real.log D / (η' * T) < ε)
      ∧ (∀ (T : ℕ) (ys : ℕ → Fin m → ℝ) (ht : 0 < T),
        (∀ t < T, ∀ i, 0 ≤ ys t i) →
        (∀ t < T, ∑ i, b i * ys t i ≤ sourceWidthBudget α R ε) →
        (∑ i, sdpDualCertificate m δ α R j₀ ys T i * b i ≤
          (1 + δ) * α + exactWidthSlack α R ε))) := by
  intro hall
  set A0 : Fin 1 → Operator 1 := fun _ => 0
  set Cv0 : Operator 1 := 1
  set b0 : Fin 1 → ℝ := fun _ => 1
  set y0 : Fin 1 → ℝ := fun _ => 0
  set ρ0 : Operator 1 := 1
  have h := hall 1 1 A0 Cv0 b0 y0 ρ0 (0.1 : ℝ) (0.05 : ℝ) (5 : ℝ) (0.1 : ℝ) (0.1 : ℝ) 0
  have hd : (0:ℕ) < 1 := by norm_num
  have hm : (0:ℕ) < 1 := by norm_num
  have hα : (0:ℝ) < 0.1 := by norm_num
  have hR : (0:ℝ) < 0.05 := by norm_num
  have hε : (0:ℝ) < 5 := by norm_num
  have hη : (0:ℝ) < 0.1 := by norm_num
  have hδ : (0:ℝ) < 0.1 := by norm_num
  have hA : ∀ i : Fin 1, (A0 i).IsHermitian ∧ ‖A0 i‖ ≤ 1 := by
    intro i
    show ((fun _ => (0 : Operator 1)) i).IsHermitian ∧ ‖(fun _ => (0 : Operator 1)) i‖ ≤ 1
    simp
  have hCv : Cv0.IsHermitian ∧ ‖Cv0‖ ≤ 1 := by
    show ((1 : Operator 1)).IsHermitian ∧ ‖(1 : Operator 1)‖ ≤ 1
    exact ⟨Matrix.isHermitian_one, le_of_eq norm_one⟩
  have hb : ∀ i : Fin 1, 1 ≤ b0 i := by
    intro i
    show (1:ℝ) ≤ (fun _ => (1:ℝ)) i
    simp
  have hρ : IsDensityOperator ρ0 := by
    show IsDensityOperator (1 : Operator 1)
    exact ⟨Matrix.PosSemidef.one, by simp⟩
  have hy : ∀ i : Fin 1, 0 ≤ y0 i := by
    intro i
    show (0:ℝ) ≤ (fun _ => (0:ℝ)) i
    simp
  have hwidth : (∑ i, b0 i * y0 i) ≤ sourceWidthBudget (0.1:ℝ) 0.05 5 := by
    show (∑ i : Fin 1, (fun _ => (1:ℝ)) i * (fun _ => (0:ℝ)) i) ≤ _
    simp [sourceWidthBudget]
    norm_num
  have hpayoff : sourcePayoffTarget 1 Cv0 ρ0 (0.1:ℝ) 5
      ≤ ∑ i, y0 i * (Matrix.trace (A0 i * ρ0)).re := by
    show sourcePayoffTarget 1 (1:Operator 1) (1:Operator 1) 0.1 5
      ≤ ∑ i : Fin 1, (fun _ => (0:ℝ)) i * _
    simp only [sourcePayoffTarget]
    rw [Matrix.trace_fin_one]
    simp only [Matrix.mul_apply, Matrix.one_apply]
    norm_num
  have htwo : 2 * (0.05:ℝ) * 5 ≤ 1 / 2 := by norm_num
  have hconj : ((sourceScaledPayoff A0 Cv0 (0.1:ℝ) y0).IsHermitian ∧
      (sourceScaledPayoff A0 Cv0 (0.1:ℝ) y0).PosSemidef ∧
      ‖sourceScaledPayoff A0 Cv0 (0.1:ℝ) y0‖ ≤ 1) ∧ _ :=
    h hd hm hα hR hε hη hδ hA hCv hb hρ hy hwidth hpayoff htwo
  obtain ⟨⟨-, hpsd, -⟩, -⟩ := hconj
  have htr := Matrix.PosSemidef.trace_nonneg hpsd
  have hcalc : Matrix.trace (sourceScaledPayoff A0 Cv0 (0.1:ℝ) y0) = ((-2 : ℝ) : ℂ) := by
    show Matrix.trace (sourceScaledPayoff (fun _ => (0 : Operator 1)) (1 : Operator 1)
      (0.1 : ℝ) (fun _ => (0 : ℝ))) = _
    rw [Matrix.trace_fin_one]
    simp only [sourceScaledPayoff, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.sum_apply, Matrix.zero_apply, Matrix.one_apply]
    push_cast
    norm_num
  rw [hcalc] at htr
  have hre : (0:ℝ) ≤ -2 := by
    have h1 := (RCLike.nonneg_iff (K := ℂ)).mp htr
    exact h1.1
  linarith

/-- The Golden--Thompson gap of Hermitian matrices is nonnegative and vanishes exactly when they
commute. For positive definite Hermitian inputs, the real trace of the exponential of the
sum of their spectral logarithms is at most the real trace of their product. -/
theorem clause21_conj12 :
    (∀ (n : ℕ) (H K : Matrix (Fin n) (Fin n) ℂ),
      H.IsHermitian → K.IsHermitian →
      0 ≤ gtHermitianGap H K ∧ (gtHermitianGap H K = 0 ↔ Commute H K))
    ∧ (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      A.mat.PosDef → B.mat.PosDef →
      logInputGT A B ≤ (Matrix.trace (A.mat * B.mat)).re) := by
  constructor
  · intro n H K hH hK
    exact ⟨gt_gap_nonneg H K hH hK, gt_gap_zero_iff_commute H K hH hK⟩
  · intro n A B hA hB
    exact log_input_gt_le A B hA hB

/-- Provides a legal `Lemma2Rescale` preserving the stated feasibility and objective comparisons
in both directions. The witness keeps `bp = b`, uses scale one and zero value error, and
takes each comparison state to itself. -/
theorem clause4_lemma2_part : ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (α R δ : ℝ),
    0 < D → 0 < m → 0 < α → 0 < R → 0 < δ →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∃ S : Lemma2Rescale A b, S.legal ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i)) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i + S.valueError)) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
          ∃ σ' : Operator D, IsDensityOperator σ' ∧
            (∀ i, (Matrix.trace (A i * σ')).re ≤ S.bp i) ∧
            (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
          ∃ σ' : Operator D, IsDensityOperator σ' ∧
            (∀ i, (Matrix.trace (A i * σ')).re ≤ b i + S.valueError) ∧
            (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError)) := by
  intro D m A Cv b _α _R _δ _hD _hm _hα _hR _hδ _hA _hCv hb
  refine ⟨⟨b, 1, 0⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show Lemma2Rescale.legal A b ⟨b, 1, 0⟩
    exact ⟨by norm_num, hb, by norm_num⟩
  · intro σ _hσ h i
    exact h i
  · intro σ _hσ h i
    show (Matrix.trace (A i * σ)).re ≤ b i + 0
    rw [add_zero]
    exact h i
  · intro σ hσ h
    refine ⟨σ, hσ, fun i => h i, ?_⟩
    show (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ)).re + 0
    rw [add_zero]
  · intro σ _hσ h
    refine ⟨σ, ‹_›, ?_, ?_⟩
    · intro i
      show (Matrix.trace (A i * σ)).re ≤ b i + 0
      rw [add_zero]
      exact h i
    · show (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ)).re + 0
      rw [add_zero]

/-- Constructs positive real parameters `η ≤ 1` and `T` satisfying `η ≤ δ / (8 * R)` and
`Real.log D / (η * T) ≤ δ * α / (4 * R)`. It also supplies the stated self-comparison
objective inequality with additive slack `δ * α / 2` for each feasible density operator. -/
theorem clause4_normalized_kernel_part : ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (α R δ : ℝ),
    0 < D → 0 < m → 0 < α → 0 < R → 0 < δ →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∃ (η T : ℝ) (hη : 0 < η ∧ η ≤ 1) (hT : 0 < T),
      η ≤ δ / (8 * R) ∧
      Real.log D / (η * T) ≤ δ * α / (4 * R) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
          (Matrix.trace (Cv * σ)).re ≤
            (Matrix.trace (Cv * σ)).re + (δ * α) / 2)) := by
  intro D m A Cv b α R δ hD _hm hα hR hδ _hA _hCv _hb
  have hlog : 0 ≤ Real.log D :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hD)
  have hlog1 : (0:ℝ) < Real.log D + 1 := by linarith
  have hP : 0 < δ * α := mul_pos hδ hα
  have hQ : 0 < 4 * R := mul_pos (by norm_num) hR
  have hηpos : 0 < min 1 (δ / (16 * R)) :=
    lt_min (by norm_num) (div_pos hδ (mul_pos (by norm_num) hR))
  refine ⟨min 1 (δ / (16 * R)),
    (Real.log D + 1) * (4 * R) / (min 1 (δ / (16 * R)) * (δ * α)), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hηpos, min_le_left 1 _⟩
  · exact div_pos (mul_pos hlog1 hQ) (mul_pos hηpos hP)
  · refine le_trans (min_le_right 1 _) ?_
    exact div_le_div_of_nonneg_left (le_of_lt hδ) (mul_pos (by norm_num) hR)
      (by linarith [hR])
  · have hηT : ∀ (η : ℝ), η ≠ 0 →
        η * ((Real.log D + 1) * (4 * R) / (η * (δ * α))) = (Real.log D + 1) * (4 * R) / (δ * α) := by
      intro η hηne
      field_simp [hηne, hP.ne']
    rw [hηT _ hηpos.ne']
    have hLHS : Real.log D / ((Real.log D + 1) * (4 * R) / (δ * α))
        = Real.log D * (δ * α) / ((Real.log D + 1) * (4 * R)) := by
      field_simp [hP.ne', (mul_pos hlog1 hQ).ne']
    rw [hLHS]
    have hrew : δ * α / (4 * R)
        = (δ * α) * (Real.log D + 1) / ((Real.log D + 1) * (4 * R)) := by
      field_simp [hQ.ne', hlog1.ne']
    rw [hrew]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt (mul_pos hlog1 hQ))
    nlinarith [hlog, hP]
  · intro σ _hσ _hfeas
    exact le_add_of_nonneg_right (div_nonneg (le_of_lt hP) (by norm_num))

/-- Refutes the proposed universal bisection-budget conclusion for every real `R` and `δ`. Zero
legal budgets allow choosing the number of guesses one larger than its asserted logarithmic
bound. -/
theorem clause4_conj3_counterexample : ∀ (R δ : ℝ),
    ¬ (∀ (N : ℕ) (guess : Fin N → ℝ) (spend : Fin N → BisectionBudget)
        (totalFail totalError : ℝ),
      (∀ i, (spend i).legal (totalFail / N) (totalError / N)) →
      (∑ i : Fin N, (spend i).failMass ≤ totalFail) ∧
      (∑ i : Fin N, (spend i).errorMass ≤ totalError) ∧
      (∀ i : Fin N, guess i = 0 ∨ guess i = 2 * R ∨ guess i ≤ 0 →
        (spend i).errorMass ≤ totalError / N) ∧
      N ≤ 2 * Nat.ceil (Real.log (4 * R / δ) / Real.log 2) + 2) := by
  intro R δ h
  have hres := (h (2 * Nat.ceil (Real.log (4 * R / δ) / Real.log 2) + 2 + 1)
    (fun _ => 0) (fun _ => (⟨0, 0, 0⟩ : BisectionBudget)) 0 0 (by
      intro i
      show BisectionBudget.legal (⟨0, 0, 0⟩ : BisectionBudget) ((0:ℝ) / _) ((0:ℝ) / _)
      rw [zero_div]
      exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)).2.2.2
  omega

/-- Refutes the universal claim that per-guess legal bisection budgets force the stated
logarithmic bound on the number of guesses, by specializing `clause4_conj3_counterexample`
to `R = δ = 1`. -/
theorem clause4_conj3_refuted : ¬
    (∀ (R δ : ℝ) (N : ℕ) (guess : Fin N → ℝ) (spend : Fin N → BisectionBudget)
        (totalFail totalError : ℝ),
      (∀ i, (spend i).legal (totalFail / N) (totalError / N)) →
      (∑ i : Fin N, (spend i).failMass ≤ totalFail) ∧
      (∑ i : Fin N, (spend i).errorMass ≤ totalError) ∧
      (∀ i : Fin N, guess i = 0 ∨ guess i = 2 * R ∨ guess i ≤ 0 →
        (spend i).errorMass ≤ totalError / N) ∧
      N ≤ 2 * Nat.ceil (Real.log (4 * R / δ) / Real.log 2) + 2) := by
  intro h
  exact clause4_conj3_counterexample 1 1 (h 1 1)

/-- Refutes the combined rescaling, normalized-parameter, and bisection contract by extracting
its false universal bound on the number of guesses from a scalar zero-matrix instance. -/
theorem clause4_refuted : ¬
    (∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
        (α R δ : ℝ),
      0 < D → 0 < m → 0 < α → 0 < R → 0 < δ →
      (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
      Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
      (∀ i, 1 ≤ b i) →
      (∃ S : Lemma2Rescale A b, S.legal ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
            (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i)) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
            (∀ i, (Matrix.trace (A i * σ)).re ≤ b i + S.valueError)) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
            ∃ σ' : Operator D, IsDensityOperator σ' ∧
              (∀ i, (Matrix.trace (A i * σ')).re ≤ S.bp i) ∧
              (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
            ∃ σ' : Operator D, IsDensityOperator σ' ∧
              (∀ i, (Matrix.trace (A i * σ')).re ≤ b i + S.valueError) ∧
              (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError))
      ∧
      (∃ (η T : ℝ) (hη : 0 < η ∧ η ≤ 1) (hT : 0 < T),
        η ≤ δ / (8 * R) ∧
        Real.log D / (η * T) ≤ δ * α / (4 * R) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
            (Matrix.trace (Cv * σ)).re ≤
              (Matrix.trace (Cv * σ)).re + (δ * α) / 2))
      ∧
      (∀ (N : ℕ) (guess : Fin N → ℝ) (spend : Fin N → BisectionBudget)
          (totalFail totalError : ℝ),
        (∀ i, (spend i).legal (totalFail / N) (totalError / N)) →
        (∑ i : Fin N, (spend i).failMass ≤ totalFail) ∧
        (∑ i : Fin N, (spend i).errorMass ≤ totalError) ∧
        (∀ i : Fin N, guess i = 0 ∨ guess i = 2 * R ∨ guess i ≤ 0 →
          (spend i).errorMass ≤ totalError / N) ∧
        N ≤ 2 * Nat.ceil (Real.log (4 * R / δ) / Real.log 2) + 2)) := by
  intro hall
  set A0 : Fin 1 → Operator 1 := fun _ => 0
  set Cv0 : Operator 1 := 0
  set b0 : Fin 1 → ℝ := fun _ => 1
  have h := hall 1 1 A0 Cv0 b0 (1:ℝ) (1:ℝ) (1:ℝ)
  have hD : (0:ℕ) < 1 := by norm_num
  have hm : (0:ℕ) < 1 := by norm_num
  have hα : (0:ℝ) < 1 := by norm_num
  have hR : (0:ℝ) < 1 := by norm_num
  have hδ : (0:ℝ) < 1 := by norm_num
  have hA : ∀ i : Fin 1, (A0 i).IsHermitian ∧ ‖A0 i‖ ≤ 1 := by
    intro i
    show ((fun _ => (0 : Operator 1)) i).IsHermitian ∧ ‖(fun _ => (0 : Operator 1)) i‖ ≤ 1
    refine ⟨Matrix.isHermitian_zero, ?_⟩
    rw [norm_zero]
    norm_num
  have hCv : Cv0.IsHermitian ∧ ‖Cv0‖ ≤ 1 := by
    show ((0 : Operator 1)).IsHermitian ∧ ‖(0 : Operator 1)‖ ≤ 1
    exact ⟨Matrix.isHermitian_zero, by rw [norm_zero]; norm_num⟩
  have hb : ∀ i : Fin 1, 1 ≤ b0 i := by
    intro i
    show (1:ℝ) ≤ (fun _ => (1:ℝ)) i
    simp
  obtain ⟨_, _, h3⟩ := h hD hm hα hR hδ hA hCv hb
  exact clause4_conj3_counterexample (1:ℝ) (1:ℝ) h3

/-- Dividing the constraint weights by `1 + 2 * R * ε` turns the source width bound into the
bound `α`, identifies the exact width slack, and preserves the stated slack-adjusted payoff
inequality. The proof requires positivity of `α`, `R`, and `ε` and the two given width and
payoff inequalities. -/
theorem clause25_conj2_part (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
    (y : Fin m → ℝ) (ρ : Operator D) (α R ε : ℝ)
    (hα : 0 < α) (hR : 0 < R) (hε : 0 < ε)
    (hb : ∑ i, b i * y i ≤ sourceWidthBudget α R ε)
    (htgt : sourcePayoffTarget D Cv ρ α ε ≤ ∑ i, y i * (Matrix.trace (A i * ρ)).re) :
    (∑ i, b i * (y i / (1 + 2 * R * ε)) ≤ α) ∧
    (exactWidthSlack α R ε = sourceWidthBudget α R ε - α) ∧
    ((sourcePayoffTarget D Cv ρ α ε - exactWidthSlack α R ε) / (1 + 2 * R * ε) ≤
      ∑ i, (y i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) := by
  have hc : 0 < 1 + 2 * R * ε := by positivity
  have hwb : sourceWidthBudget α R ε = α * (1 + 2 * R * ε) := rfl
  have hsl : exactWidthSlack α R ε = 2 * α * R * ε := rfl
  have hsum1 : (∑ i, b i * (y i / (1 + 2 * R * ε))) =
      (∑ i, b i * y i) / (1 + 2 * R * ε) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hsum2 : (∑ i, (y i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re) =
      (∑ i, y i * (Matrix.trace (A i * ρ)).re) / (1 + 2 * R * ε) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hsl0 : 0 ≤ 2 * α * R * ε := by positivity
  have h1 : sourcePayoffTarget D Cv ρ α ε - exactWidthSlack α R ε ≤
      ∑ i, y i * (Matrix.trace (A i * ρ)).re := by
    rw [hsl]
    linarith [htgt, hsl0]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum1, div_le_iff₀ hc]
    linarith [hb, hwb]
  · rw [hsl, hwb]
    ring
  · rw [hsum2]
    have hinv : ∀ x : ℝ, x / (1 + 2 * R * ε) = x * (1 + 2 * R * ε)⁻¹ := by
      intro x
      field_simp
    rw [hinv, hinv]
    exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (le_of_lt hc))

/-- Refutes the proposed combined contract through its certificate-objective conclusion. In the
scalar example with distinguished constraint bound ten and zero history, the certificate
offset alone exceeds `(1 + δ) * α + exactWidthSlack α R ε`. -/
theorem clause3_conj3_refuted : ¬
  ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : Fin m → ℝ) (ρ : Operator D) (α R ε η δ : ℝ)
      (j₀ : Fin m),
    0 < D → 0 < m → 0 < α → 0 < R → 0 < ε → 0 < η → 0 < δ →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    IsDensityOperator ρ →
    (∀ i, 0 ≤ y i) →
    (∑ i, b i * y i ≤ sourceWidthBudget α R ε) →
    (sourcePayoffTarget D Cv ρ α ε ≤ ∑ i, y i * (Matrix.trace (A i * ρ)).re) →
    (2 * R * ε ≤ 1 / 2) →

    ((sourceScaledPayoff A Cv α y).IsHermitian ∧
      (sourceScaledPayoff A Cv α y).PosSemidef ∧
      ‖sourceScaledPayoff A Cv α y‖ ≤ 1)
    ∧

    (∑ i, b i * (y i / (1 + 2 * R * ε)) ≤ α) ∧
    (exactWidthSlack α R ε = sourceWidthBudget α R ε - α) ∧
    ((sourcePayoffTarget D Cv ρ α ε - exactWidthSlack α R ε) / (1 + 2 * R * ε) ≤
      ∑ i, (y i / (1 + 2 * R * ε)) * (Matrix.trace (A i * ρ)).re)
    ∧

    (∀ η' : ℝ, 0 < η' → η' < ε →
      ∃ T : ℕ, 0 < T ∧ η' + Real.log D / (η' * T) < ε)
    ∧

    (∀ (T : ℕ) (ys : ℕ → Fin m → ℝ) (ht : 0 < T),
      (∀ t < T, ∀ i, 0 ≤ ys t i) →
      (∀ t < T, ∑ i, b i * ys t i ≤ sourceWidthBudget α R ε) →
      (∑ i, sdpDualCertificate m δ α R j₀ ys T i * b i ≤
        (1 + δ) * α + exactWidthSlack α R ε)) := by
  intro hall
  set A0 : Fin 1 → Operator 1 := fun _ => (0 : Operator 1)
  set Cv0 : Operator 1 := 0
  set b0 : Fin 1 → ℝ := fun _ => 10
  set y0 : Fin 1 → ℝ := fun _ => 0
  set ρ0 : Operator 1 := 1
  have h := hall 1 1 A0 Cv0 b0 y0 ρ0 (1:ℝ) (1:ℝ) ((1:ℝ)/4) ((1:ℝ)/2) (1:ℝ) 0
  have hA : ∀ i : Fin 1, (A0 i).IsHermitian ∧ ‖A0 i‖ ≤ 1 := by
    intro i
    show ((0 : Operator 1)).IsHermitian ∧ ‖(0 : Operator 1)‖ ≤ 1
    exact ⟨Matrix.isHermitian_zero, by simp⟩
  have hCv : ((0 : Operator 1)).IsHermitian ∧ ‖(0 : Operator 1)‖ ≤ 1 :=
    ⟨Matrix.isHermitian_zero, by simp⟩
  have hb : ∀ i : Fin 1, (1:ℝ) ≤ b0 i := by intro i; show (1:ℝ) ≤ 10; norm_num
  have hρ : IsDensityOperator ρ0 := by
    show IsDensityOperator (1 : Operator 1)
    refine ⟨Matrix.PosSemidef.one, ?_⟩
    simp [Matrix.trace]
  have hy : ∀ i : Fin 1, (0:ℝ) ≤ y0 i := by intro i; show (0:ℝ) ≤ 0; exact le_rfl
  have hwidth : ∑ i : Fin 1, b0 i * y0 i ≤ sourceWidthBudget (1:ℝ) (1:ℝ) ((1:ℝ)/4) := by
    show ∑ i : Fin 1, (10:ℝ) * 0 ≤ sourceWidthBudget (1:ℝ) (1:ℝ) ((1:ℝ)/4)
    norm_num [sourceWidthBudget]
  have hpay : sourcePayoffTarget 1 (0 : Operator 1) ρ0 (1:ℝ) ((1:ℝ)/4) ≤
      ∑ i : Fin 1, y0 i * (Matrix.trace (A0 i * ρ0)).re := by
    show sourcePayoffTarget 1 (0 : Operator 1) (1 : Operator 1) (1:ℝ) ((1:ℝ)/4) ≤
      ∑ i : Fin 1, (0:ℝ) * (Matrix.trace ((0 : Operator 1) * (1 : Operator 1))).re
    norm_num [sourcePayoffTarget]
  have h2Re : (2:ℝ) * (1:ℝ) * ((1:ℝ)/4) ≤ 1/2 := by norm_num
  obtain ⟨-, -, -, -, -, hconj3⟩ := h (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hCv hb hρ hy hwidth hpay h2Re
  have hT0 : (0:ℕ) < 1 := by norm_num
  have hys1 : ∀ t < (1:ℕ), ∀ i : Fin 1, (0:ℝ) ≤ (fun _ _ => (0:ℝ)) t i := by
    intro t ht i
    show (0:ℝ) ≤ 0
    exact le_rfl
  have hys2 : ∀ t < (1:ℕ), ∑ i : Fin 1, b0 i * (fun _ _ => (0:ℝ)) t i ≤
      sourceWidthBudget (1:ℝ) (1:ℝ) ((1:ℝ)/4) := by
    intro t ht
    show ∑ i : Fin 1, (10:ℝ) * (0:ℝ) ≤ sourceWidthBudget (1:ℝ) (1:ℝ) ((1:ℝ)/4)
    norm_num [sourceWidthBudget]
  have hbad := hconj3 1 (fun _ _ => (0:ℝ)) hT0 hys1 hys2
  simp only [sdpDualCertificate] at hbad
  norm_num [exactWidthSlack] at hbad

/-- For `0 < η' < ε`, there is a positive natural horizon `T` for which `η' + Real.log D / (η' *
T) < ε`, under the listed positivity assumptions on dimension and tolerance. -/
theorem clause25_conj2b_part (D : ℕ) (ε η' : ℝ)
    (_hD : 0 < D) (_hε : 0 < ε) (hη' : 0 < η') (hη'ε : η' < ε) :
    ∃ T : ℕ, 0 < T ∧ η' + Real.log D / (η' * T) < ε := by
  by_cases hlog : Real.log D ≤ 0
  · refine ⟨1, by norm_num, ?_⟩
    have hden : (0:ℝ) < η' * 1 := by positivity
    have h1 : Real.log D / (η' * 1) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hlog (le_of_lt hden)
    linarith
  · have hlog0 : 0 < Real.log D := lt_of_not_ge hlog
    have hden : 0 < η' * (ε - η') := by positivity
    set c := Real.log D / (η' * (ε - η')) with hcdef
    have hc0 : 0 < c := by
      unfold c
      exact div_pos hlog0 hden
    refine ⟨Nat.ceil c + 1, Nat.succ_pos _, ?_⟩
    have hT : c < ((Nat.ceil c + 1 : ℕ) : ℝ) := by
      have h1 : c ≤ ((Nat.ceil c : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil c : ℕ) : ℝ) < ((Nat.ceil c + 1 : ℕ) : ℝ) := by
        simp [Nat.cast_add, Nat.cast_one]
      linarith
    have hpos : (0:ℝ) < η' * ((Nat.ceil c + 1 : ℕ) : ℝ) := by positivity
    have hlt : Real.log D / (η' * ((Nat.ceil c + 1 : ℕ) : ℝ)) < ε - η' := by
      rw [div_lt_iff₀ hpos]
      have hA : (ε - η') * (η' * ((Nat.ceil c + 1 : ℕ) : ℝ)) =
          (η' * ((Nat.ceil c + 1 : ℕ) : ℝ)) * (ε - η') := by ring
      rw [hA]
      have hB : η' * c * (ε - η') = Real.log D := by
        have h1 : η' * (Real.log D / (η' * (ε - η'))) = Real.log D / (ε - η') := by
          have hη0 : η' ≠ 0 := ne_of_gt hη'
          have hs0 : ε - η' ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hη'ε))
          field_simp [hη0, hs0]
        rw [hcdef, h1]
        have hs0 : ε - η' ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hη'ε))
        exact div_mul_cancel₀ _ hs0
      have hC : (η' * ((Nat.ceil c + 1 : ℕ) : ℝ)) * (ε - η') >
          η' * c * (ε - η') := by
        nlinarith [hT, hη', hden]
      linarith
    linarith
end Qatlib.Concepts.SdpDuality.ConeSeparation
