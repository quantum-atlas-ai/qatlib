/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs

/-!
# Average score of the multiple-template measurement

Defines the seed score matrix `wZero`, the constant measurement vector `muZero`, and its outer
product `muProjector` for the multiple-template construction of [SasakiCarliniJozsa2001].
Entry-sum identities reduce the trace pairing with this effect to a scalar expression.

The theorem `maximumAverageScore` evaluates the resulting score as one half plus a finite sum of
adjacent overlaps. Its statement computes this score for positive `M`.

## Main statements

* `trace_mul_muProjector`: reduces a trace pairing to `M⁻¹` times the sum of matrix entries.
* `maximumAverageScore`: evaluates the score of the specified measurement effect.

## References

* [Sasaki et al., 2001][SasakiCarliniJozsa2001]
-/

set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

set_option autoImplicit false

variable {d : ℕ}

/-- The sum of all entries of a finite-dimensional operator. -/
noncomputable def entrySum (A : Operator d) : ℂ := ∑ i : Fin d, ∑ j : Fin d, A i j

/-- The sum of the entries of the zero operator is zero. -/
lemma entrySum_zero : entrySum (0 : Operator d) = 0 := by
  simp [entrySum]

/-- The sum of matrix entries is additive. -/
lemma entrySum_add (A B : Operator d) : entrySum (A + B) = entrySum A + entrySum B := by
  simp only [entrySum, Matrix.add_apply, Finset.sum_add_distrib]

/-- Taking the sum of matrix entries commutes with complex scalar multiplication. -/
lemma entrySum_smul (c : ℂ) (A : Operator d) : entrySum (c • A) = c * entrySum A := by
  simp only [entrySum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

/-- The sum of the entries of the identity operator is its dimension. -/
lemma entrySum_one : entrySum (1 : Operator d) = (d : ℂ) := by
  simp only [entrySum, Matrix.one_apply]
  simp

/-- The sum of the entries of a single-entry matrix is its specified entry. -/
lemma entrySum_single (i j : Fin d) (c : ℂ) : entrySum (Matrix.single i j c) = c := by
  simp only [entrySum, Matrix.single_apply]
  have hrow : ∀ a : Fin d,
      (∑ b : Fin d, (if i = a ∧ j = b then c else 0)) = if i = a then c else 0 := by
    intro a
    by_cases ha : i = a
    · subst ha
      simp
    · rw [if_neg ha]
      exact Finset.sum_eq_zero fun b _ => by rw [if_neg]; simp [ha]
  rw [Finset.sum_congr rfl (fun a _ => hrow a)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ ha
    rw [if_neg (show ¬ (i = a) from fun h => ha h.symm)]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The entry sum of a finite sum of operators equals the sum of their entry sums. -/
lemma entrySum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Operator d) :
    entrySum (∑ i ∈ s, f i) = ∑ i ∈ s, entrySum (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [entrySum_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, entrySum_add, ih]

/-- The adjacent overlap coefficient `√((N - k) * (k + 1))`, with the product formed in the
natural numbers. -/
noncomputable def overlap (N : ℕ) (k : Fin N) : ℝ :=
  Real.sqrt (((N - (k : ℕ)) * ((k : ℕ) + 1) : ℕ) : ℝ)

/-- The seed score operator with a scaled identity term and symmetric adjacent entries weighted
by `overlap`. -/
noncomputable def wZero (N : ℕ) : Operator (N+1) :=
  ((2*((N:ℝ)+1) : ℝ)⁻¹ : ℂ) • (1 : Operator (N+1)) +
  ((2*((N:ℝ)+1)*((N:ℝ)+2) : ℝ)⁻¹ : ℂ) •
    (∑ k : Fin N,
      ((overlap N k : ℝ) : ℂ) •
        (Matrix.single (Fin.castSucc k) (Fin.succ k) 1 +
         Matrix.single (Fin.succ k) (Fin.castSucc k) 1))

/-- Evaluates the sum of all entries of `wZero` as the identity contribution plus twice the
scaled sum of adjacent overlaps. See [SasakiCarliniJozsa2001]. -/
lemma entrySum_wZero (N : ℕ) :
    entrySum (wZero N)
      = (((N:ℝ)+1) * (2*((N:ℝ)+1))⁻¹ +
          (2*((N:ℝ)+1)*((N:ℝ)+2))⁻¹ * ∑ k : Fin N, overlap N k * 2 : ℝ) := by
  rw [wZero, entrySum_add, entrySum_smul, entrySum_one, entrySum_smul,
      entrySum_finset_sum]
  have hinner : (∑ k : Fin N, entrySum (((overlap N k : ℝ) : ℂ) •
        (Matrix.single (Fin.castSucc k) (Fin.succ k) 1 +
         Matrix.single (Fin.succ k) (Fin.castSucc k) 1)))
      = ∑ k : Fin N, ((overlap N k : ℝ) : ℂ) * 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [entrySum_smul, entrySum_add, entrySum_single, entrySum_single]
    ring
  rw [hinner]
  push_cast
  ring

/-- The complex cast of the inverse real square root of the number of templates. -/
noncomputable def muZeroAmp (M : ℕ) : ℂ := ((Real.sqrt (M:ℝ))⁻¹ : ℝ)

/-- The vector in dimension `N + 1` with every coordinate equal to `muZeroAmp M`. -/
noncomputable def muZero (N M : ℕ) : Fin (N+1) → ℂ := fun _ => muZeroAmp M

/-- The outer product of the constant vector `muZero` with its conjugate. -/
noncomputable def muProjector (N M : ℕ) : Operator (N+1) :=
  Matrix.vecMulVec (muZero N M) (star (muZero N M))

/-- For nonzero `M`, the squared modulus of `muZeroAmp M` is `M⁻¹`. -/
lemma muZeroAmp_mul_star (M : ℕ) (hM : (M:ℝ) ≠ 0) :
    muZeroAmp M * star (muZeroAmp M) = ((M:ℂ))⁻¹ := by
  have hnn : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  have hsq : Real.sqrt (M:ℝ) * Real.sqrt (M:ℝ) = (M:ℝ) := Real.mul_self_sqrt hnn
  have hs : Real.sqrt (M:ℝ) ≠ 0 := by
    intro h
    apply hM
    rw [← hsq, h, mul_zero]
  have hreal : (Real.sqrt (M:ℝ))⁻¹ * (Real.sqrt (M:ℝ))⁻¹ = ((M:ℝ))⁻¹ := by
    rw [← mul_inv, hsq]
  have hstar : star (muZeroAmp M) = muZeroAmp M := by
    simp [muZeroAmp]
  rw [hstar]
  simp only [muZeroAmp]
  rw [← Complex.ofReal_mul, hreal, Complex.ofReal_inv]
  push_cast
  rfl

/-- For nonzero `M`, the trace of `A * muProjector N M` is `M⁻¹` times the sum of the entries of
`A`. -/
lemma trace_mul_muProjector (N M : ℕ) (hM : (M:ℝ) ≠ 0) (A : Operator (N+1)) :
    Matrix.trace (A * muProjector N M) = ((M:ℂ))⁻¹ * entrySum A := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have hentry : ∀ i : Fin (N+1), (A * muProjector N M) i i = ((M:ℂ))⁻¹ * (∑ j, A i j) := by
    intro i
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [muProjector, muZero, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [muZeroAmp_mul_star M hM]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hentry i)]
  rw [← Finset.mul_sum]
  rfl

/-- Simplifies the scalar score expression to one half plus the sum of overlaps divided by `(N +
1) * (N + 2)`. -/
lemma scalar_identity (N : ℕ) :
    ((N:ℝ)+1) * (2*((N:ℝ)+1))⁻¹ +
        (2*((N:ℝ)+1)*((N:ℝ)+2))⁻¹ * ∑ k : Fin N, overlap N k * 2
      = 1/2 + ∑ k : Fin N, overlap N k / (((N:ℝ)+1)*((N:ℝ)+2)) := by
  have h2sum : (∑ k : Fin N, overlap N k * 2) = 2 * ∑ k : Fin N, overlap N k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdivsum : (∑ k : Fin N, overlap N k / (((N:ℝ)+1)*((N:ℝ)+2)))
      = (∑ k : Fin N, overlap N k) / (((N:ℝ)+1)*((N:ℝ)+2)) := (Finset.sum_div ..).symm
  rw [h2sum, hdivsum]
  have h1 : ((N:ℝ)+1) ≠ 0 := by positivity
  have h2 : ((N:ℝ)+2) ≠ 0 := by positivity
  field_simp

/-- For positive `M`, evaluates `M` times the real trace of `wZero * muProjector` as one half
plus the normalized sum of adjacent overlaps. See [SasakiCarliniJozsa2001]. -/
theorem maximumAverageScore (N M : ℕ) (hM : 0 < M) :
    (M : ℝ) * (Matrix.trace (wZero N * muProjector N M)).re
      = 1/2 + ∑ k : Fin N, overlap N k / (((N:ℝ)+1)*((N:ℝ)+2)) := by
  have hMne : (M:ℝ) ≠ 0 := by
    have hpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
    exact ne_of_gt hpos
  have htr : (Matrix.trace (wZero N * muProjector N M)).re
      = ((M:ℝ))⁻¹ * (entrySum (wZero N)).re := by
    rw [trace_mul_muProjector N M hMne]
    change ((((M:ℝ) : ℂ))⁻¹ * entrySum (wZero N)).re
      = ((M:ℝ))⁻¹ * (entrySum (wZero N)).re
    rw [← Complex.ofReal_inv]
    exact Complex.re_ofReal_mul _ _
  rw [htr, entrySum_wZero, Complex.ofReal_re]
  rw [← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
  exact scalar_identity N

end Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate
