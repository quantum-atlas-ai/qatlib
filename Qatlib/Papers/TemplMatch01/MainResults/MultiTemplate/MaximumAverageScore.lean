/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelityDefs
set_option warningAsError false

namespace Qatlib.Papers.TemplMatch01.MainResults.MultiTemplate

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

set_option autoImplicit false

variable {d : ℕ}

noncomputable def entrySum (A : Operator d) : ℂ := ∑ i : Fin d, ∑ j : Fin d, A i j

lemma entrySum_zero : entrySum (0 : Operator d) = 0 := by
  simp [entrySum]

lemma entrySum_add (A B : Operator d) : entrySum (A + B) = entrySum A + entrySum B := by
  simp only [entrySum, Matrix.add_apply, Finset.sum_add_distrib]

lemma entrySum_smul (c : ℂ) (A : Operator d) : entrySum (c • A) = c * entrySum A := by
  simp only [entrySum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

lemma entrySum_one : entrySum (1 : Operator d) = (d : ℂ) := by
  simp only [entrySum, Matrix.one_apply]
  simp

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

lemma entrySum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Operator d) :
    entrySum (∑ i ∈ s, f i) = ∑ i ∈ s, entrySum (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [entrySum_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, entrySum_add, ih]

noncomputable def overlap (N : ℕ) (k : Fin N) : ℝ :=
  Real.sqrt (((N - (k : ℕ)) * ((k : ℕ) + 1) : ℕ) : ℝ)

noncomputable def wZero (N : ℕ) : Operator (N+1) :=
  ((2*((N:ℝ)+1) : ℝ)⁻¹ : ℂ) • (1 : Operator (N+1)) +
  ((2*((N:ℝ)+1)*((N:ℝ)+2) : ℝ)⁻¹ : ℂ) •
    (∑ k : Fin N,
      ((overlap N k : ℝ) : ℂ) •
        (Matrix.single (Fin.castSucc k) (Fin.succ k) 1 +
         Matrix.single (Fin.succ k) (Fin.castSucc k) 1))

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

noncomputable def muZeroAmp (M : ℕ) : ℂ := ((Real.sqrt (M:ℝ))⁻¹ : ℝ)

noncomputable def muZero (N M : ℕ) : Fin (N+1) → ℂ := fun _ => muZeroAmp M

noncomputable def muProjector (N M : ℕ) : Operator (N+1) :=
  Matrix.vecMulVec (muZero N M) (star (muZero N M))

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
