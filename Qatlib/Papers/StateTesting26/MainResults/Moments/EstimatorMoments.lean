/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.SwapObservable
public import QuantumInfo.ForMathlib.Matrix

@[expose] public section

/-!
# Reduction of the conditional estimator moment

In [WadhwaChen2026StateTesting], Lemma 3.12,
`τA` and `τAA` denote the separate one- and two-register marginals on the
retained system. Tracing out both purifying registers scales the SWAP term by
the dimension `ℓ` of one purifying register. The coefficient identity collects
the resulting terms into Eq. (3.30). It takes the reduced operators as inputs
and leaves the conditional law and the expectation in Eq. (3.31) unmodeled.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), p. 18.
-/

namespace Qatlib.Papers.StateTesting26.MainResults.Moments

open Qatlib.Papers.StateTesting26.MainResults.Model
open scoped Kronecker

noncomputable section

/-- The joint SWAP exchanges both pairs of registers. After tracing out the purifying pair,
its contribution is `ℓ` times the retained SWAP, as in Eq. (3.35). -/
theorem traceRight_swapTwo_kronecker_swapTwo (d ℓ : ℕ) :
    (swapTwo (d := d) ⊗ₖ swapTwo (d := ℓ)).traceRight = (ℓ : ℂ) • swapTwo (d := d) := by
  have htrace : (swapTwo (d := ℓ)).trace = (ℓ : ℂ) := by
    have hfixed (a b : Fin ℓ) : (a = b ∧ b = a) ↔ a = b :=
      ⟨And.left, fun h => ⟨h, h.symm⟩⟩
    calc
      (swapTwo (d := ℓ)).trace =
          ∑ p : Fin ℓ × Fin ℓ, (if p.1 = p.2 then (1 : ℂ) else 0) := by
        simpa only [Matrix.trace, Matrix.diag_apply, swapTwo, hfixed] using
          (sum_finTwoArrow_eq_sum_prod
            (fun p : Fin ℓ × Fin ℓ => if p.1 = p.2 then (1 : ℂ) else 0))
      _ = (ℓ : ℂ) := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_one]
  apply Matrix.ext
  intro i j
  change (∑ k : Fin 2 → Fin ℓ, swapTwo (d := d) i j * swapTwo k k) = (ℓ : ℂ) * swapTwo i j
  rw [← Finset.mul_sum]
  change swapTwo i j * (swapTwo (d := ℓ)).trace = (ℓ : ℂ) * swapTwo i j
  rw [htrace, mul_comm]

/-- The two-register matrix displayed in Eq. (3.30), for `t` copies and
purifying dimension `ℓ`. The joint single-copy dimension is `dℓ`. -/
def conditionalSecondMoment {d : ℕ} (τA : Matrix (Fin d) (Fin d) ℂ)
    (τAA : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) (ℓ t : ℕ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  let D : ℝ := (d * ℓ : ℕ)
  let A := kronFirst τA + kronSecond τA
  let q := (D + t) / (D + t + 1)
  (((t : ℝ) - 1) / t * q) • τAA
    + ((1 / (t : ℝ)) * q) • (A * swapTwo)
    - ((ℓ : ℝ) / ((t : ℝ) * (D + t + 1))) • A
    + (((ℓ : ℝ) / (t : ℝ) ^ 2) * q) • swapTwo
    - ((ℓ : ℝ) ^ 2 / ((t : ℝ) ^ 2 * (D + t + 1))) • 1

/-- The expression obtained from Eq. (3.31) after applying the termwise trace rules:
an identity on a purifying pair contributes `ℓ²`, and a purifying SWAP contributes `ℓ`. -/
def reducedEstimatorMoment {d : ℕ} (τA : Matrix (Fin d) (Fin d) ℂ)
    (τAA : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) (ℓ t : ℕ) :
    Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  let D : ℝ := (d * ℓ : ℕ)
  let A := kronFirst τA + kronSecond τA
  let q := (D + t) / (D + t + 1)
  (((t : ℝ) - 1) / t * q) • τAA
    + ((1 / (t : ℝ)) * q) • (A * swapTwo)
    - ((1 / ((t : ℝ) * (D + t + 1))) * (ℓ : ℝ)) • A
    + ((1 / (t : ℝ) ^ 2) * q * (ℓ : ℝ)) • swapTwo
    - ((1 / ((t : ℝ) ^ 2 * (D + t + 1))) * (ℓ : ℝ) ^ 2) • 1

/-- The algebraic step of Lemma 3.12: collecting the factors from the termwise
partial traces gives the coefficients of Eq. (3.30). The identity holds for arbitrary
one- and two-register matrices, including the product specialization of the latter. -/
theorem reducedEstimatorMoment_eq_conditionalSecondMoment {d : ℕ}
    (τA : Matrix (Fin d) (Fin d) ℂ) (τAA : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ)
    (ℓ t : ℕ) :
    reducedEstimatorMoment τA τAA ℓ t = conditionalSecondMoment τA τAA ℓ t := by
  simp only [reducedEstimatorMoment, conditionalSecondMoment, div_eq_mul_inv, one_mul,
    mul_assoc, mul_left_comm, mul_comm]

end

end Qatlib.Papers.StateTesting26.MainResults.Moments
