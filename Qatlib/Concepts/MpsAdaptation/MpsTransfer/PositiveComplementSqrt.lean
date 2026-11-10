/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.PositiveComplementSqrtDefs
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.HermitianSylvester
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Matrix
open scoped Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {N : Type*} [Fintype N] [DecidableEq N]

noncomputable local instance complementMatrixCStar : CStarAlgebra (Matrix N N ℂ) where

private theorem complement_scalar_mono {a b : ℝ} (hab : a ≤ b) :
    a • (1 : Matrix N N ℂ) ≤ b • (1 : Matrix N N ℂ) := by
  change (b • (1 : Matrix N N ℂ)-a • (1 : Matrix N N ℂ)).PosSemidef
  rw [← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hab)

private theorem complement_sqrt_scalar (a : ℝ) (ha : 0 ≤ a) :
    CFC.sqrt (a • (1 : Matrix N N ℂ)) = Real.sqrt a • (1 : Matrix N N ℂ) := by
  apply CFC.sqrt_unique
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.one_mul, Real.mul_self_sqrt ha]
  · exact (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg a)).nonneg

theorem positive_complement_sqrt_bounds (E : Matrix N N ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hE : E.PosSemidef)
    (hcap : (q • (1 : Matrix N N ℂ)-E).PosSemidef) :
    let S := positiveComplementSqrt E
    S.PosSemidef ∧ S*S=1-E ∧
    (S-Real.sqrt (1-q) • (1 : Matrix N N ℂ)).PosSemidef ∧
    (1-S).PosSemidef ∧ ‖S-1‖ ≤ q := by
  let S := positiveComplementSqrt E
  have hE1 : E ≤ (1 : Matrix N N ℂ) := by
    exact (show E ≤ q • (1 : Matrix N N ℂ) from hcap).trans
      (by simpa only [one_smul] using complement_scalar_mono (N := N) hq1.le)
  have hbase : 0 ≤ (1 : Matrix N N ℂ)-E := sub_nonneg.mpr hE1
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg (1-E)
  have hsquare : S*S=1-E := CFC.sqrt_mul_sqrt_self (1-E) hbase
  have hlow : (1-q) • (1 : Matrix N N ℂ) ≤ 1-E := by
    change (1-E-(1-q) • (1 : Matrix N N ℂ)).PosSemidef
    convert! hcap using 1
    rw [sub_smul, one_smul]
    abel
  have hSlow : Real.sqrt (1-q) • (1 : Matrix N N ℂ) ≤ S := by
    calc
      _ = CFC.sqrt ((1-q) • (1 : Matrix N N ℂ)) :=
        (complement_sqrt_scalar (N := N) (1-q) (by linarith)).symm
      _ ≤ S := CFC.sqrt_le_sqrt _ _ hlow
  have hS1 : S ≤ (1 : Matrix N N ℂ) := by
    have hh := CFC.sqrt_le_sqrt (1-E) (1 : Matrix N N ℂ) (sub_le_self _ hE.nonneg)
    simpa only [CFC.sqrt_one] using! hh
  have hc0 := Real.sqrt_nonneg (1-q)
  have hcsq := Real.sq_sqrt (by linarith : 0 ≤ 1-q)
  have hc1 : Real.sqrt (1-q) ≤ 1 := by nlinarith
  have hcl : 1-q ≤ Real.sqrt (1-q) := by
    have hh := mul_le_mul_of_nonneg_right hc1 hc0
    nlinarith
  have hSrough : (1-q) • (1 : Matrix N N ℂ) ≤ S :=
    (complement_scalar_mono hcl).trans hSlow
  have hdiff : (1 : Matrix N N ℂ)-S ≤ q • (1 : Matrix N N ℂ) := by
    calc
      _ ≤ 1-(1-q) • (1 : Matrix N N ℂ) := sub_le_sub_left hSrough 1
      _ = _ := by rw [sub_smul, one_smul]; abel
  have hnorm : ‖(1 : Matrix N N ℂ)-S‖ ≤ q := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hq (sub_nonneg.mpr hS1)).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hdiff
  exact ⟨hS0.posSemidef, hsquare, hSlow, hS1, by rwa [norm_sub_rev]⟩

theorem positive_complement_sqrt_stability (E D : Matrix N N ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (hE : E.PosSemidef)
    (hEc : (q • (1 : Matrix N N ℂ)-E).PosSemidef) (hD : D.PosSemidef)
    (hDc : (q • (1 : Matrix N N ℂ)-D).PosSemidef) :
    ‖positiveComplementSqrt E-positiveComplementSqrt D‖ ≤
      ‖E-D‖/(2*Real.sqrt (1-q)) := by
  have hs := positive_complement_sqrt_bounds E q hq hq1 hE hEc
  have ht := positive_complement_sqrt_bounds D q hq hq1 hD hDc
  have hc : 0 < Real.sqrt (1-q) := Real.sqrt_pos.mpr (by linarith)
  have hh := hermitian_square_difference_bound (positiveComplementSqrt E)
    (positiveComplementSqrt D) (Real.sqrt (1-q)) hc hs.1.isHermitian ht.1.isHermitian
    hs.2.2.1 ht.2.2.1
  rw [hs.2.1, ht.2.1, show (1-E)-(1-D)=D-E by abel, norm_sub_rev D E] at hh
  exact hh

theorem positive_complement_sqrt_stability_small (E D : Matrix N N ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 3/4) (hE : E.PosSemidef)
    (hEc : (q • (1 : Matrix N N ℂ)-E).PosSemidef) (hD : D.PosSemidef)
    (hDc : (q • (1 : Matrix N N ℂ)-D).PosSemidef) :
    ‖positiveComplementSqrt E-positiveComplementSqrt D‖ ≤ ‖E-D‖ := by
  have hh := positive_complement_sqrt_stability E D q hq (by linarith) hE hEc hD hDc
  have hc0 := Real.sqrt_nonneg (1-q)
  have hcsq := Real.sq_sqrt (by linarith : 0 ≤ 1-q)
  have hc : 1 ≤ 2*Real.sqrt (1-q) := by nlinarith
  exact hh.trans (div_le_self (norm_nonneg _) hc)

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
