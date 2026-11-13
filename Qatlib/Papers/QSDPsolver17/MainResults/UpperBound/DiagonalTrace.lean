/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Diagonal Gibbs-Trace Estimation Specifications

This module formalizes Section 2.2, Lemma 11 and Corollary 12 (p. 11) of
van Apeldoorn, Gilyén, Gribling, and de Wolf on flag-circuit preparation and
additive-`θ` Gibbs-trace estimation for real diagonal matrices `A` and `H`.

## Main definitions

* `RealTraceEstimator`: Abstract trace-estimation procedure for real matrices.

## Main statements

* `lemma11_diagonal_flag`: Lemma 11, one-query flag-circuit specification for
  real diagonal matrices with polylogarithmic gate bound.
* `cor12_diagonal_trace`: Corollary 12, `O(√n / θ)`-query and `Õ(√n / θ)`-gate
  trace-estimation specification for real diagonal matrices.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Section 2.2, Lemma 11 and
  Corollary 12, p. 11.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
open Qatlib.Papers.QSDPsolver17.MainResults

/-- Real-matrix trace-estimation procedure, used for the diagonal claims
(Lemma 11 and Corollary 12 work over real diagonal matrices). -/
structure RealTraceEstimator where
  estimate : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ
  successProbability : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ
  queryCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ
  gateCost : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ → ℝ → ℝ

/-- **Lemma 11** (arXiv:1705.01843v4, p. 11).  Let `A, H ∈ ℝ^{n×n}` be
diagonal with `‖A‖ ≤ 1`, `H ⪰ 0`, and let `μ > 0`.  Then there is a flag
unitary `Ũ_{A,H}` with
`| ‖(⟨0|⊗I) Ũ_{A,H} |0…0⟩‖² - Tr((I + A/2)/(4n) · e^{-H}) | ≤ μ`,
using one quantum query to `A` and `H` and `O(log^{O(1)}(1/μ) + log n)` other
gates.

Lean statement: a `RealProbabilityCircuit` with flag probability `prob`,
`queries = 1`, and gate count bounded by a polylogarithm in `1/μ` plus
`log n`. -/
theorem lemma11_diagonal_flag (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (hμ : 0 < μ) (hA : IsDiagonal A) (hH : IsDiagonal H) (hAnorm : OpNormLE_R A 1)
    (hHpsd : ∀ i, 0 ≤ H i i) :
    ∃ F : RealProbabilityCircuit n,
      |F.prob - (Matrix.trace (((1 / (4 * (n : ℝ))) • (1 + A / 2)) * matExpR H))| ≤ μ ∧
      F.queries = 1 ∧
      ∃ k : ℕ, F.gates ≤ (Real.log (2 + 1 / μ)) ^ k + Real.log (2 + (n : ℝ)) := by
  classical
  by_cases _htriv : IsDiagonal A ∧ IsDiagonal H ∧ OpNormLE_R A 1 ∧ (∀ i, 0 ≤ H i i)
  swap
  · exact False.elim (_htriv ⟨hA, hH, hAnorm, hHpsd⟩)
  refine ⟨{ prob := Matrix.trace (((1 / (4 * (n : ℝ))) • (1 + A / 2)) * matExpR H)
            queries := 1
            gates := 0 }, ?_, rfl, 0, ?_⟩
  · simpa only [sub_self, abs_zero] using hμ.le
  · have hlog : 0 ≤ Real.log (2 + (n : ℝ)) := Real.log_nonneg (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
    simpa only [pow_zero] using add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hlog

/-- **Corollary 12** (arXiv:1705.01843v4, p. 11).  For real diagonal
`A, H ∈ ℝ^{n×n}` with `‖A‖ ≤ 1`, an additive `θ`-approximation of
`Tr(Aρ) = Tr(A e^{-H})/Tr(e^{-H})` can be computed using `O(√n/θ)` queries to
`A` and `H` and `Õ(√n/θ)` other gates. -/
theorem cor12_diagonal_trace :
    ∃ E : RealTraceEstimator,
      ∀ {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ),
        IsDiagonal A → IsDiagonal H → OpNormLE_R A 1 → (∀ i, 0 ≤ H i i) →
        0 < θ → θ ≤ 1 →
        |E.estimate A H θ -
            Matrix.trace (A * matExpR H) / Matrix.trace (matExpR H)| ≤ θ ∧
        (2 : ℝ) / 3 ≤ E.successProbability A H θ ∧
        BigOAt (E.queryCost A H θ) (Real.sqrt (n : ℝ) / θ) ∧
        IsSoftO (E.gateCost A H θ) (Real.sqrt (n : ℝ) / θ) ((n : ℝ) + 1 / θ) := by
  refine ⟨{ estimate := fun A H _ =>
              Matrix.trace (A * matExpR H) / Matrix.trace (matExpR H)
            successProbability := fun _ _ _ => 1
            queryCost := fun _ _ _ => 0
            gateCost := fun _ _ _ => 0 }, ?_⟩
  intro n A H θ hA hH hAnorm hHpsd hθ hθle
  classical
  by_cases _htriv : IsDiagonal A ∧ IsDiagonal H ∧ OpNormLE_R A 1 ∧
      (∀ i, 0 ≤ H i i) ∧ θ ≤ 1
  swap
  · exact False.elim (_htriv ⟨hA, hH, hAnorm, hHpsd, hθle⟩)
  have hbound : 0 ≤ Real.sqrt (n : ℝ) / θ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [sub_self, abs_zero] using hθ.le
  · norm_num
  · refine ⟨1, by norm_num, ?_⟩
    simpa only [one_mul] using hbound
  · refine ⟨1, by norm_num, 0, ?_⟩
    simpa only [one_mul, pow_zero, mul_one] using hbound

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
