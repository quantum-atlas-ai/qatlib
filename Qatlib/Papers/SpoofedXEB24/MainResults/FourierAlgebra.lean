/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open Finset BigOperators
set_option autoImplicit false

/-!
# Pauli-path Fourier algebra for `SpoofedXEB24`

The paper (Tanggara–Gu–Bharti, arXiv:2405.00789v2, §3 and Appendices G–H) approximates the
single-block mQSVT output probability `p(U, x)` by the Pauli-path ansatz

`q(U, x) = 2^{-n} + F(U, r, x)`,

expands `p(U, x) = ∑_s F(U, s, x)` over all Pauli paths `s`, and then "expands the squares and
simplifies" the sXQUATH mean-squared-error difference into the terms (i), (ii), (iii) of
eqn. (13) and eqn. (57); the sXES score is reduced to eqn. (16) by the same expansion.

This module formalises that *algebraic* core in a finite model: `U` is a finite type of
unitaries with the uniform average `avg`, `X` is a finite type of nonzero outcomes, and
`F s u x` is the value of the Pauli-path Fourier coefficient `F(U, s, x)`.  Nothing here
assumes any estimate on the Fourier coefficients — the Haar/Weingarten moment bounds that
supply the constants `α, β, c` are *not* formalised; only the exact algebraic reductions are.

The reductions are stated in the form that follows from the definitions of eqn. (2) and
eqn. (1).  The printed eqn. (57) carries a sign inherited from the source OCR of the square
expansion; the correct reduction of `E[(p − 2^{-n})²] − E[(p − q)²]` with `q = 2^{-n} + F_r`
is `E[F_r²] + 2 ∑_{s≠r} E[F_s F_r] − 2·2^{-n} E[F_r]`, which is the statement proved below
(`sXQ_eq_sums`).  We keep the mathematically verified sign and record the discrepancy here.
-/

namespace Qatlib.Papers.SpoofedXEB24.MainResults

variable {ι U X : Type*} [Fintype ι] [Fintype U] [Fintype X] [DecidableEq ι]

noncomputable section

/-- The Pauli-path decomposition of the mQSVT output probability: `p(U, x) = ∑_s F(U, s, x)`
(eqn. (7) of the paper). -/
def pauliProb (F : ι → U → X → ℝ) (u : U) (x : X) : ℝ := ∑ s, F s u x

/-- The Pauli-path approximant `q(U, x) = 2^{-n} + F(U, r, x)` of eqn. (8). -/
def pauliApprox (F : ι → U → X → ℝ) (r : ι) (n : ℕ) (u : U) (x : X) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) + F r u x

/-- The uniform average over the finite family of unitaries. -/
def avg (g : U → ℝ) : ℝ := (∑ u, g u) / (Fintype.card U : ℝ)

/-- The sXQUATH mean-squared-error difference of eqn. (2):
`E_{U,X}[(p − 2^{-n})²] − E_{U,X}[(p − q)²]`, with `X` uniform over the nonzero outcomes. -/
def sXQ (F : ι → U → X → ℝ) (r : ι) (n : ℕ) : ℝ :=
  (1 / (Fintype.card X : ℝ)) *
      (∑ x, avg (fun u => (pauliProb F u x - (2 : ℝ) ^ (-(n : ℤ))) ^ 2)) -
    (1 / (Fintype.card X : ℝ)) *
      (∑ x, avg (fun u => (pauliProb F u x - pauliApprox F r n u x) ^ 2))

/-- The sXES score of eqn. (1) with the Pauli-path approximant used for the experimental
probability: `∑_{x≠0} E_U[p(U,x) q(U,x)]`. -/
def sXES (F : ι → U → X → ℝ) (r : ι) (n : ℕ) : ℝ :=
  ∑ x, avg (fun u => pauliProb F u x * pauliApprox F r n u x)

/-- The uniform average is additive. -/
lemma avg_add (g h : U → ℝ) : avg (fun u => g u + h u) = avg g + avg h := by
  unfold avg
  rw [Finset.sum_add_distrib, add_div]

/-- The uniform average is additive in the negative direction. -/
lemma avg_sub (g h : U → ℝ) : avg (fun u => g u - h u) = avg g - avg h := by
  unfold avg
  rw [Finset.sum_sub_distrib, sub_div]

/-- **Pointwise square-expansion.**  With `q = 2^{-n} + F_r` the difference of squared errors
collapses to the cross term `2 p F_r − 2·2^{-n} F_r − F_r²`.  This is the algebraic content of
"expanding the squares and simplifying the terms" in Appendix G. -/
lemma mse_pointwise (F : ι → U → X → ℝ) (r : ι) (n : ℕ) (u : U) (x : X) :
    (pauliProb F u x - (2 : ℝ) ^ (-(n : ℤ))) ^ 2 -
        (pauliProb F u x - pauliApprox F r n u x) ^ 2
      = 2 * pauliProb F u x * F r u x
        - 2 * (2 : ℝ) ^ (-(n : ℤ)) * F r u x - (F r u x) ^ 2 := by
  unfold pauliApprox
  ring

/-- **sXQUATH reduction, cross-term form (eqn. (55)).**  The mean-squared-error difference
equals the average of `2 p F_r − 2·2^{-n} F_r − F_r²` over outcomes and unitaries. -/
theorem sXQ_eq_cross (F : ι → U → X → ℝ) (r : ι) (n : ℕ) :
    sXQ F r n
      = (1 / (Fintype.card X : ℝ)) *
          ∑ x, avg (fun u => 2 * pauliProb F u x * F r u x
            - 2 * (2 : ℝ) ^ (-(n : ℤ)) * F r u x - (F r u x) ^ 2) := by
  unfold sXQ
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← avg_sub]
  exact congrArg avg (funext fun u => mse_pointwise F r n u x)

/-- **sXQUATH reduction, Pauli-path form (eqn. (57)).**  Substituting `p = ∑_s F_s` turns the
cross term into `F_r² + 2 ∑_{s≠r} F_s F_r − 2·2^{-n} F_r`; the sum over `s ≠ r` is exactly the
IIIrd term of eqn. (13). -/
theorem sXQ_eq_sums (F : ι → U → X → ℝ) (r : ι) (n : ℕ) :
    sXQ F r n
      = (1 / (Fintype.card X : ℝ)) *
          ∑ x, avg (fun u =>
            (F r u x) ^ 2
              + 2 * (∑ s ∈ Finset.univ.erase r, F s u x) * F r u x
              - 2 * (2 : ℝ) ^ (-(n : ℤ)) * F r u x) := by
  rw [sXQ_eq_cross]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold avg
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [pauliProb]
  have h := Finset.sum_erase_add (Finset.univ : Finset ι) (fun s => F s u x)
    (Finset.mem_univ r)
  rw [← h]
  ring

/-- **sXES reduction (eqn. (16)).**  Expanding `p q` with `q = 2^{-n} + F_r` and `p = ∑_s F_s`
gives `p q = p/2^n + F_r² + ∑_{s≠r} F_s F_r`, hence the sXES score splits into the uniform
baseline `∑_x E[p]/2^n`, the diagonal `∑_x E[F_r²]`, and the off-diagonal correlation
`∑_x ∑_{s≠r} E[F_s F_r]` — the same term (iii) that appears in the sXQUATH reduction. -/
theorem sXES_eq_sums (F : ι → U → X → ℝ) (r : ι) (n : ℕ) :
    sXES F r n
      = ∑ x, avg (fun u => pauliProb F u x * (2 : ℝ) ^ (-(n : ℤ)))
        + ∑ x, avg (fun u => (F r u x) ^ 2)
        + ∑ x, avg (fun u => (∑ s ∈ Finset.univ.erase r, F s u x) * F r u x) := by
  unfold sXES
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← avg_add, ← avg_add]
  congr 1
  funext u
  unfold pauliApprox
  simp only [pauliProb]
  have h := Finset.sum_erase_add (Finset.univ : Finset ι) (fun s => F s u x)
    (Finset.mem_univ r)
  rw [← h]
  ring

end

end Qatlib.Papers.SpoofedXEB24.MainResults
