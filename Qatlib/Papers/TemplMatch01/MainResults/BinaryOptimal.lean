/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs

/-!
# Binary template score in a diagonal basis

This module defines the binary template score and the complementary diagonal selectors `mvZero`
and `mvOne` used in [SasakiCarliniJozsa2001]. Their conjugates `optimalZero` and `optimalOne`
are positive semidefinite and sum to the identity when `Pᴴ * P = 1`.

Given the stated unitary diagonalization of `W0 - W1` and the real trace of `W1`,
`optimalBinaryScore` evaluates the score of `optimalZero P` as a partial sum of the supplied
diagonal coefficients.

## Main statements

* `optimalZero_add_optimalOne`: proves completeness of the conjugated pair under the stated
  condition on `P`.
* `optimalZero_posSemidef` and `optimalOne_posSemidef`: prove positivity of the conjugated
  selectors.
* `optimalBinaryScore`: evaluates the binary score under the supplied diagonalization.

## References

* [Sasaki et al., 2001][SasakiCarliniJozsa2001]
-/

set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.BinaryOptimal

open Qatlib.Foundations.PureStateMath
open Matrix BigOperators
open scoped ComplexOrder BigOperators MatrixOrder Matrix

set_option autoImplicit false

/-- The binary score `Re tr (A * W0) + Re tr ((1 - A) * W1)`. -/
noncomputable def binaryScore {d : ℕ} (W0 W1 A : Operator d) : ℝ :=
  (Matrix.trace (A * W0)).re + (Matrix.trace ((1 - A) * W1)).re

/-- The diagonal selector with value one at indices `k ≤ N / 2` and zero at the other indices. -/
noncomputable def mvZero (N : ℕ) : Operator (N + 1) :=
  Matrix.diagonal (fun k : Fin (N + 1) => if (k : ℕ) ≤ N / 2 then (1 : ℂ) else 0)

/-- The diagonal selector complementary to `mvZero N`. -/
noncomputable def mvOne (N : ℕ) : Operator (N + 1) :=
  Matrix.diagonal (fun k : Fin (N + 1) => if (k : ℕ) ≤ N / 2 then (0 : ℂ) else 1)

/-- The conjugate `Pᴴ * mvZero N * P` of the first diagonal selector. -/
noncomputable def optimalZero {N : ℕ} (P : Operator (N + 1)) : Operator (N + 1) :=
  Pᴴ * mvZero N * P

/-- The conjugate `Pᴴ * mvOne N * P` of the second diagonal selector. -/
noncomputable def optimalOne {N : ℕ} (P : Operator (N + 1)) : Operator (N + 1) :=
  Pᴴ * mvOne N * P

/-- The two complementary diagonal selectors sum to the identity [SasakiCarliniJozsa2001]. -/
theorem mvZero_add_mvOne (N : ℕ) : mvZero N + mvOne N = 1 := by
  rw [mvZero, mvOne, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext k
  by_cases hk : (k : ℕ) ≤ N / 2 <;> simp [hk]

/-- The first diagonal selector is positive semidefinite. -/
theorem mvZero_posSemidef (N : ℕ) : (mvZero N).PosSemidef := by
  rw [mvZero]
  exact Matrix.PosSemidef.diagonal (fun k => by
    by_cases hk : (k : ℕ) ≤ N / 2 <;> simp [hk])

/-- The complementary diagonal selector is positive semidefinite. -/
theorem mvOne_posSemidef (N : ℕ) : (mvOne N).PosSemidef := by
  rw [mvOne]
  exact Matrix.PosSemidef.diagonal (fun k => by
    by_cases hk : (k : ℕ) ≤ N / 2 <;> simp [hk])

/-- If `Pᴴ * P = 1`, the two conjugated diagonal selectors sum to the identity
[SasakiCarliniJozsa2001]. -/
theorem optimalZero_add_optimalOne {N : ℕ} (P : Operator (N + 1))
    (hP : Pᴴ * P = 1) :
    optimalZero P + optimalOne P = 1 := by
  have hd := congrArg (fun A : Operator (N + 1) => Pᴴ * A * P) (mvZero_add_mvOne N)
  simpa [optimalZero, optimalOne, mul_add, add_mul, mul_one, hP] using hd

/-- The conjugated first selector is positive semidefinite for every `P`. -/
theorem optimalZero_posSemidef {N : ℕ} (P : Operator (N + 1)) :
    (optimalZero P).PosSemidef := by
  have h := (mvZero_posSemidef N).conjTranspose_mul_mul_same P
  simpa [optimalZero] using h

/-- The conjugated second selector is positive semidefinite for every `P`. -/
theorem optimalOne_posSemidef {N : ℕ} (P : Operator (N + 1)) :
    (optimalOne P).PosSemidef := by
  have h := (mvOne_posSemidef N).conjTranspose_mul_mul_same P
  simpa [optimalOne] using h

/-- If `P * Pᴴ = 1`, the trace of the product of the two conjugates of `A` and `B` equals
`Matrix.trace (A * B)`. -/
lemma trace_conj_mul {n : ℕ} (A B P : Operator n)
    (hPP : P * Pᴴ = 1) :
    Matrix.trace ((Pᴴ * A * P) * (Pᴴ * B * P)) = Matrix.trace (A * B) := by
  have h1 : (Pᴴ * A * P) * (Pᴴ * B * P) = Pᴴ * A * (P * Pᴴ) * B * P := by
    noncomm_ring
  have h2 : Pᴴ * A * (P * Pᴴ) * B * P = Pᴴ * (A * B) * P := by
    rw [hPP]
    noncomm_ring
  rw [h1, h2]
  rw [Matrix.trace_mul_cycle]
  rw [hPP, one_mul]

/-- Under the stated unitary diagonalization of `W0 - W1` and real-trace condition on `W1`, the
score of `optimalZero P` equals one half plus `Real.cos θ` multiplied by the sum of `lam k`
over indices `k ≤ N / 2` [SasakiCarliniJozsa2001]. -/
theorem optimalBinaryScore (N : ℕ) (W0 W1 P : Operator (N + 1))
    (lam : Fin (N + 1) → ℝ) (θ : ℝ)
    (_hP : Pᴴ * P = 1) (hPP : P * Pᴴ = 1)
    (hD : W0 - W1
      = Pᴴ * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ) * (Real.cos θ : ℂ)) * P)
    (hW1 : (Matrix.trace W1).re = 1 / 2) :
    binaryScore W0 W1 (optimalZero P)
      = 1 / 2 + Real.cos θ * ∑ k : Fin (N + 1), if (k : ℕ) ≤ N / 2 then lam k else 0 := by
  set D : Operator (N + 1) :=
    Pᴴ * Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ) * (Real.cos θ : ℂ)) * P with hDdef
  have hDsub : W0 - W1 = D := by rw [hD, hDdef]
  have hW0 : W0 = W1 + D := by
    have h : W0 = D + W1 := (sub_eq_iff_eq_add).mp hDsub
    exact h.trans (add_comm D W1)
  have htrace0 : Matrix.trace ((optimalZero P) * W0)
      = Matrix.trace ((optimalZero P) * W1) + Matrix.trace ((optimalZero P) * D) := by
    rw [hW0, mul_add, Matrix.trace_add]
  have htraceD : Matrix.trace ((optimalZero P) * D)
      = Matrix.trace (mvZero N *
          Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ) * (Real.cos θ : ℂ))) := by
    rw [optimalZero, hDdef]
    exact trace_conj_mul (mvZero N)
      (Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ) * (Real.cos θ : ℂ))) P hPP
  have hdiag : Matrix.trace (mvZero N *
        Matrix.diagonal (fun k => ((lam k : ℝ) : ℂ) * (Real.cos θ : ℂ)))
      = ((Real.cos θ : ℂ) *
          ∑ k : Fin (N + 1),
            (((if (k : ℕ) ≤ N / 2 then lam k else 0 : ℝ)) : ℂ)) := by
    rw [mvZero, Matrix.diagonal_mul_diagonal]
    simp only [Matrix.trace_diagonal]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) ≤ N / 2
    · simp [hk]; ring
    · simp [hk]
  have hADre : (Matrix.trace ((optimalZero P) * D)).re
      = Real.cos θ * ∑ k : Fin (N + 1), if (k : ℕ) ≤ N / 2 then lam k else 0 := by
    rw [htraceD, hdiag]
    rw [Complex.re_ofReal_mul]
    congr 1
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun k _ => Complex.ofReal_re _
  have hsplit : Matrix.trace ((optimalZero P) * W1)
      + Matrix.trace ((1 - optimalZero P) * W1) = Matrix.trace W1 := by
    rw [← Matrix.trace_add]
    congr 1
    rw [sub_mul, one_mul]
    abel
  have hsumRe : (Matrix.trace ((optimalZero P) * W1)).re
      + (Matrix.trace ((1 - optimalZero P) * W1)).re = 1 / 2 := by
    rw [← Complex.add_re, hsplit, hW1]
  rw [binaryScore, htrace0, Complex.add_re]
  linarith [hsumRe, hADre]

end Qatlib.Papers.TemplMatch01.MainResults.BinaryOptimal
