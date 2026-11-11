/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Payoff error accumulation and a Gibbs counterexample

`sdpCumulativePayoffError` and `sdpScaledPayoffError` quantify cumulative and mass-scaled payoff
errors. `not_sdpSparsificationGibbsError` gives a two-dimensional example showing that the
proposed per-round error bound alone cannot ensure an arbitrary Gibbs trace-distance tolerance.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `not_sdpSparsificationGibbsError`: The proposed `SdpSparsificationGibbsError` contract is
  false: its payoff error hypotheses do not ensure every positive trace-distance tolerance.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.WeightsCore

namespace Qatlib.Concepts.SdpMmwSolver.OracleError
open scoped BigOperators Matrix.Norms.L2Operator

/-- Per-round operator-norm errors at most 1/(4T) accumulate to at most ηt/(4T) in the Gibbs
exponents when T > 0 and η ≥ 0. -/
theorem sdpCumulativePayoffError (D T t : ℕ) (M N : ℕ → Operator D) (η : ℝ)
    (hT : 0 < T) (hη : 0 ≤ η)
    (herr : ∀ s, ‖M s - N s‖ ≤ 1 / (4 * (T : ℝ))) :
    ‖-η • (∑ s ∈ Finset.range t, M s) -
      -η • (∑ s ∈ Finset.range t, N s)‖ ≤ η * (t : ℝ) / (4 * (T : ℝ)) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg hη]
  calc
    _ ≤ η * (∑ s ∈ Finset.range t, ‖M s - N s‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hη
    _ ≤ η * (∑ _s ∈ Finset.range t, 1 / (4 * (T : ℝ))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => herr s) hη
    _ = η * (t : ℝ) / (4 * (T : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- For α > 0, the mass-scaled payoff error equals the constraint-sum approximation error
divided by 4α. See [BrandaoSvore2017]. -/
theorem sdpScaledPayoffError (D m Q : ℕ) (A : Fin m → Operator D) (Cv : Operator D)
    (α mass : ℝ) (idx : Fin Q → Fin m) (y : ℕ → Fin m → ℝ) (t : ℕ)
    (hα : 0 < α) :
    ‖sdpScaledSparsifiedPayoff D m Q A Cv α mass idx - sdpDualPayoff D m A Cv α y t‖ =
      ‖mass • ((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - (∑ i, y t i • A i)‖ /
        (4 * α) := by
  have he : sdpScaledSparsifiedPayoff D m Q A Cv α mass idx -
      sdpDualPayoff D m A Cv α y t =
      (4 * α)⁻¹ •
        (mass • ((Q : ℝ)⁻¹ • (∑ j : Fin Q, A (idx j))) - (∑ i, y t i • A i)) := by
    unfold sdpScaledSparsifiedPayoff sdpDualPayoff
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (4 * α)⁻¹)]
  ring

/-- The two-dimensional diagonal constraint matrix with entries 1 and 0 used in the Gibbs
approximation counterexample. -/
private def testA : Operator 2 := Matrix.diagonal ![1, 0]
/-- The constant exact payoff history with α = 2, zero objective matrix, and zero dual response. -/
private def exactM : ℕ → Operator 2 := sdpDualPayoff 2 1 (fun _ => testA) 0 2 (fun _ _ => 0)
/-- The constant sampled payoff history formed by sampling `testA` once with α = 2. -/
private def sampleM : ℕ → Operator 2 :=
    fun _s => sdpSparsifiedPayoff 2 1 1 (fun _ => testA) 0 2 (fun _ => 0)

/-- The exact payoff in the counterexample is the diagonal matrix with both entries 1/2. -/
private lemma payoff_exact (s : ℕ) : exactM s = Matrix.diagonal ![(1/2:ℂ), 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [exactM, sdpDualPayoff, Matrix.diagonal]

/-- The sampled payoff in the counterexample is the diagonal matrix with entries 5/8 and 1/2. -/
private lemma payoff_sample (s : ℕ) : sampleM s = Matrix.diagonal ![(5/8:ℂ), 1/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sampleM, sdpSparsifiedPayoff, testA, Matrix.diagonal]

/-- The complex exponential of −n log(2) equals the reciprocal of 2 raised to the natural power
n. -/
private lemma scalar_exp (n : ℕ) :
    NormedSpace.exp ((-(n:ℝ)*Real.log 2 : ℝ) : ℂ) = ((2:ℝ)^n)⁻¹ := by
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]
  congr 1
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]

/-- After one round at learning rate 8 log(2), the exact Gibbs state is diagonal with entries
1/2 and 1/2. -/
private lemma state_exact : mmwState 2 exactM (8 * Real.log 2) 1 =
    Matrix.diagonal ![(1/2:ℂ), 1/2] := by
  have he : mmwWeight 2 exactM (8 * Real.log 2) 1 =
      Matrix.diagonal ![(1/16:ℂ), 1/16] := by
    unfold mmwWeight
    simp only [Finset.sum_range_one, payoff_exact]
    have hh : -(8 * Real.log 2) • Matrix.diagonal ![(1/2:ℂ), 1/2] =
        Matrix.diagonal (fun _ : Fin 2 => ((-(4:ℝ)*Real.log 2:ℝ):ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring
    rw [hh, Matrix.exp_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    simp only [Pi.exp_def]
    fin_cases i <;> have h4 := scalar_exp 4 <;> norm_num at h4 ⊢ <;> exact h4
  unfold mmwState
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_two, Matrix.diagonal]

/-- After one round at learning rate 8 log(2), the sampled Gibbs state is diagonal with entries
1/3 and 2/3. -/
private lemma state_sample : mmwState 2 sampleM (8 * Real.log 2) 1 =
    Matrix.diagonal ![(1/3:ℂ), 2/3] := by
  have he : mmwWeight 2 sampleM (8 * Real.log 2) 1 =
      Matrix.diagonal ![(1/32:ℂ), 1/16] := by
    unfold mmwWeight
    simp only [Finset.sum_range_one, payoff_sample]
    have hh : -(8 * Real.log 2) • Matrix.diagonal ![(5/8:ℂ), 1/2] =
        Matrix.diagonal ![((-(5:ℝ)*Real.log 2:ℝ):ℂ), ((-(4:ℝ)*Real.log 2:ℝ):ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> ring
    rw [hh, Matrix.exp_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> simp only [Pi.coe_exp]
    · have h5 := scalar_exp 5
      norm_num at h5 ⊢
      exact h5
    · have h4 := scalar_exp 4
      norm_num at h4 ⊢
      exact h4
  unfold mmwState
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.trace, Fin.sum_univ_two, Matrix.diagonal]

/-- The proposed `SdpSparsificationGibbsError` contract is false: its payoff error hypotheses do
not ensure every positive trace-distance tolerance. -/
theorem not_sdpSparsificationGibbsError : ¬ SdpSparsificationGibbsError := by
  intro h
  have hdiff : mmwState 2 exactM (8 * Real.log 2) 1 -
      mmwState 2 sampleM (8 * Real.log 2) 1 ≠ 0 := by
    rw [state_exact, state_sample]
    intro hz
    have hi := congrArg (fun B : Operator 2 => B 0 0) hz
    norm_num [Matrix.diagonal] at hi
  let distance := Matrix.traceNorm (mmwState 2 exactM (8 * Real.log 2) 1 -
      mmwState 2 sampleM (8 * Real.log 2) 1)
  have hdistance : 0 < distance := lt_of_le_of_ne (Matrix.traceNorm_nonneg _)
    (Ne.symm (fun he => hdiff ((Matrix.traceNorm_zero_iff _).mp he)))
  have hnorm : ‖testA‖ ≤ (1:ℝ) := by
    rw [testA, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro i
    fin_cases i <;> norm_num
  have herr (t : ℕ) : ‖sampleM t - exactM t‖ ≤ 1 / (4 * (2:ℝ)) := by
    rw [payoff_exact, payoff_sample, Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1/(4*2))).mpr
    intro i
    fin_cases i <;> norm_num
  have hf := h 2 1 1 2 (fun _ => testA) 0 (fun _ => 1) (fun _ _ => 0)
    2 (distance/2) (8 * Real.log 2) (fun _ _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by positivity)
    (by
      intro i
      constructor
      · unfold testA
        rw [Matrix.isHermitian_diagonal_iff]
        intro j
        fin_cases j <;> simp [IsSelfAdjoint]
      · exact hnorm)
    ⟨Matrix.isHermitian_zero, by simp⟩ (by intro i; norm_num)
    (by intro t; exact ⟨by intro i; norm_num, by norm_num⟩) herr 1 (by norm_num)
  change distance ≤ distance/2 at hf
  linarith

end Qatlib.Concepts.SdpMmwSolver.OracleError
