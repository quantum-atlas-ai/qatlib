/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.PolynomialSecant
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.TwoSpectra

open Matrix Polynomial
open scoped BigOperators Classical Matrix.Norms.L2Operator
open PolynomialSecant
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath

variable {I : Type} [Fintype I] [DecidableEq I]

def plus (T : Matrix I I ℂ) : Matrix I I ℂ := (1 / 2 : ℂ) • (1 + T)

def minus (T : Matrix I I ℂ) : Matrix I I ℂ := (1 / 2 : ℂ) • (1 - T)

omit [Fintype I] in

theorem split_sum (T : Matrix I I ℂ) : plus T + minus T = 1 := by
  unfold plus minus
  rw [← smul_add]
  have h : (1 + T) + (1 - T) = (1 : Matrix I I ℂ) + 1 := by abel
  rw [h, smul_add, ← add_smul]
  norm_num

omit [Fintype I] in

theorem split_sub (T : Matrix I I ℂ) : plus T - minus T = T := by
  unfold plus minus
  rw [← smul_sub]
  have h : (1 + T) - (1 - T) = T + T := by abel
  rw [h, smul_add, ← add_smul]
  norm_num

theorem plus_action (T : Matrix I I ℂ) (hT : T * T = 1) : T * plus T = plus T := by
  unfold plus
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one, hT]
  congr 1
  abel

theorem minus_action (T : Matrix I I ℂ) (hT : T * T = 1) : T * minus T = -minus T := by
  unfold minus
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, hT, ← smul_neg]
  congr 1
  abel

theorem power_action (Y P : Matrix I I ℂ) (a : ℂ) (hY : Y * P = a • P) (n : ℕ) :
    Y ^ n * P = a ^ n • P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, hY, smul_smul, pow_succ]

theorem polynomial_action (Y P : Matrix I I ℂ) (a : ℂ) (hY : Y * P = a • P) (p : Polynomial ℂ) :
    aeval Y p * P = p.eval a • P := by
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  simp_rw [Matrix.smul_mul, power_action Y P a hY, smul_smul]
  rw [← Finset.sum_smul, Polynomial.eval_eq_sum_range]

theorem aeval_factor (X : Matrix I I ℂ) (p : Polynomial ℂ) (a : ℂ) :
    aeval X p - p.eval a • 1 = aeval X (secant p a) * (X - a • 1) := by
  calc
    _ = aeval X (p - C (p.eval a)) := by simp [Algebra.algebraMap_eq_smul_one]
    _ = aeval X (secant p a * (Polynomial.X - C a)) := by rw [factor, mul_comm]
    _ = _ := by simp [Algebra.algebraMap_eq_smul_one]

theorem sector_difference (X Y P : Matrix I I ℂ) (a : ℂ) (hY : Y * P = a • P) (p : Polynomial ℂ) :
    (aeval X p - aeval Y p) * P = aeval X (secant p a) * (X - Y) * P := by
  have hp := polynomial_action Y P a hY p
  have he : (X - a • 1) * P = (X - Y) * P := by
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hY]
  calc
    _ = (aeval X p - p.eval a • 1) * P := by
      rw [Matrix.sub_mul, Matrix.sub_mul, hp, Matrix.smul_mul, Matrix.one_mul]
    _ = aeval X (secant p a) * ((X - a • 1) * P) := by rw [aeval_factor, Matrix.mul_assoc]
    _ = _ := by rw [he, Matrix.mul_assoc]

theorem decomposition (X T : Matrix I I ℂ) (hT : T * T = 1) (s : ℂ) (p : Polynomial ℂ) :
    aeval X p - aeval (s • T) p =
      aeval X (secant p s) * (X - s • T) * plus T +
        aeval X (secant p (-s)) * (X - s • T) * minus T := by
  have hp : (s • T) * plus T = s • plus T := by rw [Matrix.smul_mul, plus_action T hT]
  have hm : (s • T) * minus T = (-s) • minus T := by
    rw [Matrix.smul_mul, minus_action T hT, smul_neg, neg_smul]
  calc
    _ = (aeval X p - aeval (s • T) p) * (plus T + minus T) := by rw [split_sum, Matrix.mul_one]
    _ = _ := by rw [Matrix.mul_add, sector_difference X (s • T) (plus T) s hp,
      sector_difference X (s • T) (minus T) (-s) hm]

theorem target_polynomial (T : Matrix I I ℂ) (hT : T * T = 1) (s : ℂ) (p : Polynomial ℂ)
    (hp : p.eval s = 1) (hm : p.eval (-s) = -1) : aeval (s • T) p = T := by
  have hsp : (s • T) * plus T = s • plus T := by rw [Matrix.smul_mul, plus_action T hT]
  have hsm : (s • T) * minus T = (-s) • minus T := by
    rw [Matrix.smul_mul, minus_action T hT, smul_neg, neg_smul]
  calc
    _ = aeval (s • T) p * (plus T + minus T) := by rw [split_sum, Matrix.mul_one]
    _ = p.eval s • plus T + p.eval (-s) • minus T := by
      rw [Matrix.mul_add, polynomial_action _ _ s hsp, polynomial_action _ _ (-s) hsm]
    _ = _ := by rw [hp, hm, one_smul, neg_one_smul, ← sub_eq_add_neg, split_sub]

theorem split_vectors_bound {E : Type} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) (hy : ‖y‖ = ‖x‖) :
    ‖(1 / 2 : ℂ) • (x + y)‖ + ‖(1 / 2 : ℂ) • (x - y)‖ ≤ (3 / 2 : ℝ) * ‖x‖ := by
  have h := parallelogram_law_with_norm ℂ x y
  rw [hy] at h
  have hn1 := norm_nonneg (x + y)
  have hn2 := norm_nonneg (x - y)
  have hnx := norm_nonneg x
  rw [norm_smul, norm_smul]
  norm_num
  nlinarith [sq_nonneg (‖x + y‖ - ‖x - y‖)]

theorem unitary_action_norm (T : Matrix I I ℂ) (hT : T ∈ unitaryGroup I ℂ) (x : EuclideanSpace ℂ I) :
    ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) T x‖ = ‖x‖ := by
  exact norm_toEuclideanCLM_of_mem_unitaryGroup hT x

theorem apply_norm_le (G : Matrix I I ℂ) (x : EuclideanSpace ℂ I) :
    ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) G x‖ ≤ ‖G‖ * ‖x‖ := by
  simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
    (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) G).le_opNorm x

theorem two_sector_bound (T E Gp Gm : Matrix I I ℂ) (hT : T ∈ unitaryGroup I ℂ)
    (L : ℝ) (hL : 0 ≤ L) (hp : ‖Gp‖ ≤ L) (hm : ‖Gm‖ ≤ L) :
    ‖Gp * E * plus T + Gm * E * minus T‖ ≤ (3 / 2 : ℝ) * L * ‖E‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM (Gp * E * plus T + Gm * E * minus T)]
  apply (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
    (Gp * E * plus T + Gm * E * minus T)).opNorm_le_bound (by positivity)
  intro x
  let a := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (plus T) x
  let b := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (minus T) x
  have hs : ‖a‖ + ‖b‖ ≤ (3 / 2 : ℝ) * ‖x‖ := by
    simpa only [a, b, plus, minus, map_smul, map_add, map_sub, map_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] using
      split_vectors_bound x (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) T x) (unitary_action_norm T hT x)
  simp only [map_add, map_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply]
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) Gp (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) E a)‖ +
        ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) Gm (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) E b)‖ := norm_add_le _ _
    _ ≤ ‖Gp‖ * ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) E a‖ +
        ‖Gm‖ * ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) E b‖ :=
      add_le_add (apply_norm_le Gp _) (apply_norm_le Gm _)
    _ ≤ L * (‖E‖ * ‖a‖) + L * (‖E‖ * ‖b‖) :=
      add_le_add (mul_le_mul hp (apply_norm_le E a) (norm_nonneg _) hL)
        (mul_le_mul hm (apply_norm_le E b) (norm_nonneg _) hL)
    _ = (L * ‖E‖) * (‖a‖ + ‖b‖) := by ring
    _ ≤ (L * ‖E‖) * ((3 / 2 : ℝ) * ‖x‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end Qatlib.Papers.CommutLCHS26.MainResults.TwoSpectra
