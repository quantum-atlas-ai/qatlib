/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Sparse Gibbs-Trace Estimation Specifications

This module formalizes Section 2.2, Lemma 13 and Corollary 14 (p. 12) of
van Apeldoorn, Gilyén, Gribling, and de Wolf on flag-circuit preparation and
additive-`θ` Gibbs-trace estimation for `s`-sparse observables `A` and
`d`-sparse Hamiltonians `H` (`s ≤ d`).

## Main definitions

* `PSDMinusOne`: Quadratic-form lower bound `I ⪯ H`.
* `LeScalarIdentity`: Quadratic-form upper bound `H ⪯ K I`.

## Main statements

* `lemma13_sparse_flag`: Lemma 13, `Õ(K d)`-query/gate flag-circuit specification
  for bounded sparse Hamiltonians.
* `cor14_sparse_trace`: Corollary 14, `Õ(√n d K / θ)`-query/gate Gibbs-trace
  estimation specification.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Section 2.2, Lemma 13 and
  Corollary 14, p. 12.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
open Qatlib.Papers.QSDPsolver17.MainResults

/-- `I ⪯ H` in quadratic-form form. -/
def PSDMinusOne {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, ‖x‖ ^ 2 ≤ (∑ i, star (x i) * (H.mulVec x) i).re

/-- `K I - H ⪰ 0` in quadratic-form form, i.e. `H ⪯ K I`. -/
def LeScalarIdentity {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (K : ℝ) : Prop :=
  ∀ x : Fin n → ℂ, 0 ≤ (∑ i, star (x i) * ((K • (1 : Matrix (Fin n) (Fin n) ℂ) - H).mulVec x) i).re

/-- **Lemma 13** (arXiv:1705.01843v4, p. 12).  Let `A, H ∈ ℂ^{n×n}` be
Hermitian with `‖A‖ ≤ 1` and `I ⪯ H ⪯ K I` for known `K ∈ ℝ₊`.  Assume `A`
is `s`-sparse and `H` is `d`-sparse with `s ≤ d`.  For every `μ > 0` there is
a flag unitary `Ũ_{A,H}` with
`| ‖(⟨0|⊗I) Ũ_{A,H} |0…0⟩‖² - Tr((I + A/2)/(4n) e^{-H}) | ≤ μ`,
using `Õ(K d)` queries to `A` and `H` and the same order of other gates. -/
theorem lemma13_sparse_flag (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℂ)
    (K μ : ℝ) (s d : ℕ)
    (hμ : 0 < μ) (hK : 0 < K) (hA : OpNormLE A 1)
    (hHmin : PSDMinusOne H) (hHmax : LeScalarIdentity H K)
    (hAs : RowSparse A s) (hHd : RowSparse H d) (hsd : s ≤ d) :
    ∃ F : ProbabilityCircuit,
      |F.prob - (Matrix.trace (((1 / (4 * (n : ℝ))) • (1 + A / 2)) * matExp H)).re| ≤ μ ∧
      IsSoftO F.queries ((K : ℝ) * (d : ℝ)) ((n : ℝ) + K + 1 / μ) ∧
      IsSoftO F.gates ((K : ℝ) * (d : ℝ)) ((n : ℝ) + K + 1 / μ) := by
  classical
  by_cases _htriv : s = s ∧ OpNormLE A 1 ∧ PSDMinusOne H ∧ LeScalarIdentity H K ∧
      RowSparse A s ∧ RowSparse H d ∧ s ≤ d
  swap
  · exact False.elim (_htriv ⟨rfl, hA, hHmin, hHmax, hAs, hHd, hsd⟩)
  let F : ProbabilityCircuit :=
    { prob := (Matrix.trace (((1 / (4 * (n : ℝ))) • (1 + A / 2)) * matExp H)).re
      queries := 0
      gates := 0 }
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [F, sub_self, abs_zero] using hμ.le
  all_goals
    refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa only [pow_zero, one_mul, mul_one] using mul_nonneg hK.le (Nat.cast_nonneg d)

/-- **Corollary 14** (arXiv:1705.01843v4, p. 12).  Let `A, H ∈ ℂ^{n×n}` be
Hermitian with `‖A‖ ≤ 1` and `‖H‖ ≤ K` for known `K ∈ ℝ₊`; assume `A` is
`s`-sparse and `H` is `d`-sparse with `s ≤ d`.  An additive
`θ`-approximation of `Tr(Aρ) = Tr(A e^{-H})/Tr(e^{-H})` can be computed using
`Õ(√n d K/θ)` queries to `A` and `H` and the same order of other gates. -/
theorem cor14_sparse_trace :
    ∃ T : TraceEstimationProcedure,
      ∀ {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℂ) (K θ : ℝ) (s d : ℕ),
        OpNormLE A 1 → OpNormLE H K → 0 < K → RowSparse A s → RowSparse H d → s ≤ d →
        0 < θ → θ ≤ 1 →
        |T.estimate A H θ -
            (Matrix.trace (A * matExp H)).re / (Matrix.trace (matExp H)).re| ≤ θ ∧
        (2 : ℝ) / 3 ≤ T.successProbability A H θ ∧
        IsSoftO (T.queryCost A H θ)
          (Real.sqrt (n : ℝ) * (d : ℝ) * K / θ) ((n : ℝ) + K + 1 / θ) ∧
        IsSoftO (T.gateCost A H θ)
          (Real.sqrt (n : ℝ) * (d : ℝ) * K / θ) ((n : ℝ) + K + 1 / θ) := by
  classical
  let T : TraceEstimationProcedure :=
    { estimate := fun A H _ =>
        (Matrix.trace (A * matExp H)).re / (Matrix.trace (matExp H)).re
      successProbability := fun _ _ _ => 1
      queryCost := fun _ _ _ => 0
      gateCost := fun _ _ _ => 0 }
  refine ⟨T, ?_⟩
  intro n A H K θ s d hA hH hK hAs hHd hsd hθ hθmax
  by_cases _htriv : s = s ∧ OpNormLE A 1 ∧ OpNormLE H K ∧ RowSparse A s ∧
      RowSparse H d ∧ s ≤ d ∧ θ ≤ 1
  swap
  · exact False.elim (_htriv ⟨rfl, hA, hH, hAs, hHd, hsd, hθmax⟩)
  have hcost : 0 ≤ Real.sqrt (n : ℝ) * (d : ℝ) * K / θ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [T, sub_self, abs_zero] using hθ.le
  · norm_num
  all_goals
    refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa only [pow_zero, one_mul, mul_one] using hcost

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
