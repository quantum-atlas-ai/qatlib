/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.GramReadout
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix
open scoped BigOperators Classical ComplexOrder

namespace Qatlib.Papers.QuantumSVM13.GramDensity

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.CopyEvolution.GramReadout

variable {M N : ℕ}

noncomputable def dataVecNorm (v : Fin N → ℝ) : ℝ := Real.sqrt (∑ k, (v k) ^ 2)

noncomputable def dataNormSq (x : Fin M → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ k, (x i k) ^ 2

noncomputable def dataUnit (x : Fin M → Fin N → ℝ) (i : Fin M) : QState (Fin N) :=
  fun k => ((x i k / dataVecNorm (x i) : ℝ) : ℂ)

noncomputable def dataWeight (x : Fin M → Fin N → ℝ) (i : Fin M) : ℝ :=
  dataVecNorm (x i) / Real.sqrt (dataNormSq x)

noncomputable def kernelDensity (x : Fin M → Fin N → ℝ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => ((1 / dataNormSq x : ℝ) : ℂ) * ((∑ k, x i k * x j k : ℝ) : ℂ)

theorem dataUnit_normalized (x : Fin M → Fin N → ℝ) (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2)
    (i : Fin M) : Normalized (dataUnit x i) := by
  unfold Normalized
  simp only [dataUnit, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsq : (dataVecNorm (x i)) ^ 2 = ∑ k, (x i k) ^ 2 := by
    rw [dataVecNorm, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
  calc ∑ k, (x i k / dataVecNorm (x i)) ^ 2
      = (∑ k, (x i k) ^ 2) / (dataVecNorm (x i)) ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [hsq, div_self (ne_of_gt (hx i))]

theorem dataNormSq_pos (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) : 0 < dataNormSq x := by
  unfold dataNormSq
  exact Finset.sum_pos (fun i _ => hx i) (Finset.univ_nonempty_iff.2 ⟨⟨0, hM⟩⟩)

theorem dataWeight_sq_sum (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) : (∑ i, (dataWeight x i) ^ 2) = 1 := by
  have hN : 0 < dataNormSq x := dataNormSq_pos x hM hx
  have hsqrt : (Real.sqrt (dataNormSq x)) ^ 2 = dataNormSq x :=
    Real.sq_sqrt hN.le
  have hsq (i : Fin M) : (dataVecNorm (x i)) ^ 2 = ∑ k, (x i k) ^ 2 := by
    rw [dataVecNorm, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
  unfold dataWeight
  calc ∑ i, (dataVecNorm (x i) / Real.sqrt (dataNormSq x)) ^ 2
      = (∑ i, (dataVecNorm (x i)) ^ 2) / (Real.sqrt (dataNormSq x)) ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (∑ i, ∑ k, (x i k) ^ 2) / dataNormSq x := by
        rw [hsqrt]
        congr 1
        exact Finset.sum_congr rfl fun i _ => hsq i
    _ = 1 := by exact div_self (ne_of_gt hN)

theorem gramMatrix_eq_kernelDensity (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) :
    gramMatrix (dataUnit x) (dataWeight x) = kernelDensity x := by
  have hN : 0 < dataNormSq x := dataNormSq_pos x hM hx
  ext i j
  simp only [gramMatrix, gramColumn, kernelDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dataUnit, dataWeight, map_mul, RCLike.star_def,
    Complex.conj_ofReal]

  have hterm (k : Fin N) :
      (dataVecNorm (x i) / Real.sqrt (dataNormSq x) *
          (x i k / dataVecNorm (x i))) *
        (dataVecNorm (x j) / Real.sqrt (dataNormSq x) *
          (x j k / dataVecNorm (x j)))
      = (1 / dataNormSq x) * (x i k * x j k) := by
    have hi : (dataVecNorm (x i)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hx i))
    have hj : (dataVecNorm (x j)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hx j))
    have hNne : (dataNormSq x) ≠ 0 := ne_of_gt hN
    field_simp
    rw [Real.sq_sqrt hN.le]
    ring
  calc ∑ k, (((dataVecNorm (x i) / Real.sqrt (dataNormSq x) : ℝ) : ℂ) *
        ((x i k / dataVecNorm (x i) : ℝ) : ℂ)) *
        (((dataVecNorm (x j) / Real.sqrt (dataNormSq x) : ℝ) : ℂ) *
        ((x j k / dataVecNorm (x j) : ℝ) : ℂ))
      = ∑ k, (((1 / dataNormSq x) * (x i k * x j k) : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        congr 1
        exact hterm k
    _ = ((1 / dataNormSq x : ℝ) : ℂ) * ((∑ k, x i k * x j k : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sum, ← Complex.ofReal_mul]
        congr 1
        rw [Finset.mul_sum]

theorem kernelDensity_bridge (x : Fin M → Fin N → ℝ) (hM : 0 < M)
    (hx : ∀ i, 0 < ∑ k, (x i k) ^ 2) :
    Normalized (gramState (dataUnit x) (dataWeight x)) ∧
    PartialTrace (outerProduct (gramState (dataUnit x) (dataWeight x))) = kernelDensity x ∧
    IsDensityOperator (kernelDensity x) := by
  have hmain := gramFirstRegisterDensity M N (dataUnit x)
    (dataUnit_normalized x hx) (dataWeight x)
    (fun i => by
      unfold dataWeight
      exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (dataWeight_sq_sum x hM hx)
  refine ⟨hmain.1, ?_, ?_⟩
  · rw [hmain.2.1, gramMatrix_eq_kernelDensity x hM hx]
  · rw [← gramMatrix_eq_kernelDensity x hM hx]
    exact hmain.2.2

end Qatlib.Papers.QuantumSVM13.GramDensity
