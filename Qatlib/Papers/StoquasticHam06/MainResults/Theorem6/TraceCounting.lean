/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Theorem6.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn

/-!
# Ordered-product expansion for trace counting

`seqProd` preserves the order of a finite sequence of matrices. Expanding a power of a matrix
sum over all index sequences gives `pow_sum_eq_sum_seqProd` and its scaled trace form, while a
logarithmic threshold gap supplies a power comparison. See [BravyiEtAl2008Stoquastic].

## Main statements

* `pow_sum_eq_sum_seqProd`: a power of a sum expands over ordered products.
* `scaled_pow_trace_eq`: the scaled trace has the corresponding sequence expansion.
* `large_ge_two_pow_mul_small`: a logarithmic gap yields a factor `2 ^ n` between threshold
  powers.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.StoquasticHam06.MainResults.Theorem6

open Matrix

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordered product of the matrices in a sequence indexed by `Fin L`. -/
def seqProd {L : ℕ} (A : Fin L → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (List.ofFn A).prod

/-- The ordered product of an empty matrix sequence is the identity matrix. -/
@[simp]
theorem seqProd_zero (A : Fin 0 → Matrix ι ι ℝ) : seqProd A = 1 := by
  simp [seqProd]

/-- Prepending a matrix to a finite sequence multiplies its ordered product on the left. -/
theorem seqProd_cons {L : ℕ} (a : Matrix ι ι ℝ) (f : Fin L → Matrix ι ι ℝ) :
    seqProd (Fin.cons a f) = a * seqProd f := by
  unfold seqProd
  rw [List.ofFn_cons, List.prod_cons]

/-- The `L`th power of a finite sum of matrices equals the sum of ordered products over all
length-`L` sequences of summand indices. See [BravyiEtAl2008Stoquastic]. -/
theorem pow_sum_eq_sum_seqProd [Fintype τ] (A : τ → Matrix ι ι ℝ) (L : ℕ) :
    (∑ t, A t) ^ L = ∑ tv : Fin L → τ, seqProd (fun i => A (tv i)) := by
  induction L with
  | zero =>
      simp only [pow_zero]
      haveI : Unique (Fin 0 → τ) := Pi.uniqueOfIsEmpty _
      rw [Finset.sum_eq_single (default : Fin 0 → τ)]
      · rw [seqProd_zero]
      · intro b _ hb; exact absurd (Subsingleton.elim b _) hb
      · intro h; exact absurd (Finset.mem_univ _) h
  | succ L ih =>
      rw [pow_succ', ih, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => τ))
        (fun tv => seqProd (fun i => A (tv i)))]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun tv _ => ?_))
      have h1 : (Fin.consEquiv (fun _ => τ)) (t, tv) = Fin.cons t tv := by
        simp [Fin.consEquiv]
      have hfun : (fun i => A ((Fin.consEquiv (fun _ => τ)) (t, tv) i))
          = Fin.cons (A t) (fun i => A (tv i)) := by
        funext i
        rw [h1]
        cases i using Fin.cases <;> rfl
      rw [hfun, seqProd_cons]

/-- The trace of the `L`th power of a scalar multiple of a finite matrix sum is `c ^ L` times
the sum of traces of all ordered length-`L` products. See [BravyiEtAl2008Stoquastic]. -/
theorem scaled_pow_trace_eq [Fintype τ] (A : τ → Matrix ι ι ℝ) (c : ℝ) (L : ℕ) :
    ((c • ∑ t, A t) ^ L).trace
      = c ^ L * ∑ tv : Fin L → τ, (seqProd (fun i => A (tv i))).trace := by
  simp only [smul_pow, pow_sum_eq_sum_seqProd, Matrix.trace_smul, Matrix.trace_sum,
    smul_eq_mul, Finset.mul_sum]

/-- For positive thresholds and positive `p`, a logarithmic gap at least `1 / p` implies `2 ^ n
* muM ^ (2 * n * p) ≤ muP ^ (2 * n * p)`. See [BravyiEtAl2008Stoquastic]. -/
theorem large_ge_two_pow_mul_small (muP muM : ℝ) (n p : ℕ) (hp : 0 < p)
    (hM : 0 < muM) (hP : 0 < muP)
    (hgap : 1 / (p : ℝ) ≤ Real.log muP - Real.log muM) :
    (2 : ℝ) ^ n * muM ^ (2 * n * p) ≤ muP ^ (2 * n * p) := by
  have hmain := log_gap_trace_ratio muP muM n p hp hM hP hgap
  have hle : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (2 * n) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hMk : 0 ≤ muM ^ (2 * n * p) := pow_nonneg hM.le _
  calc (2 : ℝ) ^ n * muM ^ (2 * n * p)
      ≤ (2 : ℝ) ^ (2 * n) * muM ^ (2 * n * p) := by
        exact mul_le_mul_of_nonneg_right hle hMk
    _ ≤ muP ^ (2 * n * p) := hmain

end Qatlib.Papers.StoquasticHam06.MainResults.Theorem6
