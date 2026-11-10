/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.Hadamard
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.ExponentialWord
import Mathlib.Analysis.Normed.Ring.InfiniteSum
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance : NormedAlgebra ℚ (A →L[ℝ] A) := .restrictScalars ℚ ℝ _

def generatorCoefficient : List A → ℕ → A
  | [], _ => 0
  | K :: ks, n => (if n = 0 then K else 0) +
      ∑ ij ∈ Finset.antidiagonal n,
        ((ij.1.factorial : ℝ)⁻¹) • adIter K ij.1 (generatorCoefficient ks ij.2)

def operatorCoefficient : List A → ℕ → (A →L[ℝ] A)
  | [], _ => 0
  | K :: ks, n => (if n = 0 then left K else 0) +
      ∑ ij ∈ Finset.antidiagonal n,
        (((ij.1.factorial : ℝ)⁻¹) • adMap K ^ ij.1) * operatorCoefficient ks ij.2

def operatorGenerator : List A → ℝ → (A →L[ℝ] A)
  | [], _ => 0
  | K :: ks, t => left K + NormedSpace.exp (t • adMap K) * operatorGenerator ks t

theorem operatorGenerator_one (ks : List A) (t : ℝ) :
    operatorGenerator ks t 1 = generator ks t := by
  induction ks with
  | nil => rfl
  | cons K ks ih =>
    simp only [operatorGenerator, generator, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, left_apply, mul_one, ih, exp_ad_apply]
omit [CompleteSpace A] in

theorem operatorCoefficient_one (ks : List A) (n : ℕ) :
    operatorCoefficient ks n 1 = generatorCoefficient ks n := by
  induction ks generalizing n with
  | nil => rfl
  | cons K ks ih =>
    simp only [operatorCoefficient, generatorCoefficient, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.smul_apply, adMap_pow_apply, ih]
    split_ifs <;> simp only [left_apply, mul_one, ContinuousLinearMap.zero_apply, zero_add]

theorem operatorGenerator_series (ks : List A) (t : ℝ) :
    (Summable fun n : ℕ => ‖t^n • operatorCoefficient ks n‖) ∧
    HasSum (fun n : ℕ => t^n • operatorCoefficient ks n) (operatorGenerator ks t) := by
  induction ks with
  | nil =>
    have hz (n : ℕ) : t^n • (0 : A →L[ℝ] A) = 0 := by
      apply ContinuousLinearMap.ext
      intro X
      change t^n • (0 : A) = 0
      exact smul_zero (t^n)
    constructor
    · simpa only [operatorCoefficient, hz, norm_zero] using
        (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    · simpa only [operatorCoefficient, operatorGenerator, hz] using
        (hasSum_zero : HasSum (fun _ : ℕ => (0 : A →L[ℝ] A)) 0)
  | cons K ks ih =>
    let f : ℕ → (A →L[ℝ] A) := fun n => (t^n / (n.factorial : ℝ)) • adMap K ^ n
    let g : ℕ → (A →L[ℝ] A) := fun n => t^n • operatorCoefficient ks n
    have hpow (F : A →L[ℝ] A) (n : ℕ) : (t • F)^n = t^n • F^n := by
      ext X
      exact scaled_pow_apply F t n X
    have hf : Summable fun n => ‖f n‖ := by
      convert! NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) (t • adMap K) using 1
      funext n
      simp only [f, hpow, smul_smul, div_eq_mul_inv]
      rw [mul_comm]
    have hfs : HasSum f (NormedSpace.exp (t • adMap K)) := by
      convert! NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • adMap K) using 1
      funext n
      simp only [f, hpow, smul_smul, div_eq_mul_inv]
      rw [mul_comm]
    have hc := summable_norm_sum_mul_antidiagonal_of_summable_norm hf ih.1
    have hcs : HasSum (fun n => ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2)
        (NormedSpace.exp (t • adMap K) * operatorGenerator ks t) := by
      convert! hc.of_norm.hasSum using 1
      rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf ih.1,
        hfs.tsum_eq, ih.2.tsum_eq]
    have heq (n : ℕ) : t^n • operatorCoefficient (K :: ks) n =
        (if n = 0 then left K else 0) +
        ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
      simp only [operatorCoefficient, smul_add, Finset.smul_sum]
      congr 1
      · split_ifs with h <;> simp [h]
      · apply Finset.sum_congr rfl
        intro ij hij
        apply ContinuousLinearMap.ext
        intro X
        simp only [f, g, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
          map_smul, smul_smul, div_eq_mul_inv]
        congr 1
        rw [← Finset.mem_antidiagonal.mp hij, pow_add]
        ring
    simp_rw [heq]
    have hi : HasSum (fun n : ℕ => if n = 0 then left K else 0) (left K) := by
      simpa using hasSum_ite_eq 0 (left K)
    have hin : Summable fun n : ℕ => ‖if n = 0 then left K else 0‖ := by
      simpa only [apply_ite norm, norm_zero] using
        (hasSum_ite_eq 0 ‖left K‖).summable
    exact ⟨(hin.add hc).of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_add_le _ _),
        hi.add hcs⟩

theorem generator_hasSum (ks : List A) (t : ℝ) :
    HasSum (fun n : ℕ => t^n • generatorCoefficient ks n) (generator ks t) := by
  have h := (ContinuousLinearMap.apply ℝ A (1 : A)).hasSum (operatorGenerator_series ks t).2
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
    operatorCoefficient_one, operatorGenerator_one] using h
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
