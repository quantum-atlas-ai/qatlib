/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Basic
import Qatlib.Papers.HermitianMap26.Construction.PostProcessing
import Qatlib.Concepts.KrausCompile.BornMoments.BornReadout
import Qatlib.Concepts.KrausCompile.BornMoments.IndependentShots
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.KrausCompile.BornMoments
open scoped ComplexOrder BigOperators

namespace Qatlib.Papers.HermitianMap26.Construction.SignedKraus

variable {d r : ℕ} (D : SignedKraus d r)

def shotWeight : Fin (r+1) → ℝ := fun i => (D.postProcessingWeight D.normalization i).re

def shotLaw (hd : 0 < d) (ρ V : Op d) (hρ : ρ.PosSemidef) (htρ : ρ.trace = 1)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : FinDist (Fin (r+1) × Fin d) :=
  bornLaw D.compiledFamily (D.compiledFamily_complete hd) ρ V hρ htρ hV

theorem sign_im_zero (i : Fin r) : (D.α i).im = 0 := by
  rcases D.sign i with h | h <;> simp [h]

theorem sign_re_sq (i : Fin r) : (D.α i).re ^ 2 = 1 := by
  rcases D.sign i with h | h <;> simp [h]

theorem weighted_branch_mean (hd : 0 < d) (ρ O : Op d) :
    (∑ i, D.shotWeight i * (D.compiledFamily i * ρ * (D.compiledFamily i)ᴴ * O).trace.re) =
      D.compiledMean ρ O := by
  rw [Fin.sum_univ_castSucc]
  simp only [shotWeight, compiledFamily, postProcessingWeight_castSucc,
    postProcessingWeight_last, completedKraus_castSucc, completedKraus_last,
    Complex.zero_re, zero_mul, add_zero, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have h :=
      congrArg Complex.re (D.trace_postprocessing D.normalization (D.normalization_pos hd) ρ O)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum, D.sign_im_zero, Finset.mul_sum] at h
  simpa only [mul_assoc, compiledMean] using h.symm

theorem actual_shot_mean (hd : 0 < d) (ρ V : Op d) (hρ : ρ.PosSemidef)
    (htρ : ρ.trace = 1) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ) :
    (D.shotLaw hd ρ V hρ htρ hV).expect (readout D.shotWeight eig) =
      D.compiledMean ρ (observable V eig) := by
  rw [shotLaw, readout_mean, D.weighted_branch_mean hd]

theorem re_trace_normalizedKraus_sq (hd : 0 < d) (i : Fin r) (ρ O : Op d) :
    (D.normalizedKraus D.normalization i * ρ *
      (D.normalizedKraus D.normalization i)ᴴ * O ^ 2).trace.re =
        D.normalization⁻¹ * (D.K i * ρ * (D.K i)ᴴ * O ^ 2).trace.re := by
  rw [trace_normalizedKraus D _ (D.normalization_pos hd) i ρ (O ^ 2),
    sqrtScale_mul_star _ (D.normalization_pos hd), ← Complex.ofReal_inv]
  simp [Complex.mul_re]

theorem weighted_branch_second (hd : 0 < d) (ρ O : Op d) :
    (∑ i, D.shotWeight i ^ 2 *
      (D.compiledFamily i * ρ * (D.compiledFamily i)ᴴ * O ^ 2).trace.re) =
        D.normalization * ∑ i, (D.K i * ρ * (D.K i)ᴴ * O ^ 2).trace.re := by
  rw [Fin.sum_univ_castSucc]
  simp only [shotWeight, compiledFamily, postProcessingWeight_castSucc,
    postProcessingWeight_last, completedKraus_castSucc, completedKraus_last,
    Complex.zero_re, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, D.sign_re_sq, mul_one, D.re_trace_normalizedKraus_sq hd]
  have hγ := D.normalization_pos hd
  field_simp

theorem single_shot_variance (hd : 0 < d) (ρ V : Op d) (hρ : ρ.PosSemidef)
    (htρ : ρ.trace = 1) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ) :
    (D.shotLaw hd ρ V hρ htρ hV).variance (readout D.shotWeight eig) =
      D.normalization * (∑ i, (D.K i * ρ * (D.K i)ᴴ * observable V eig ^ 2).trace.re) -
        (D.compiledMean ρ (observable V eig)) ^ 2 := by
  rw [shotLaw, readout_variance, D.weighted_branch_second hd, D.weighted_branch_mean hd]

theorem independent_average_variance (hd : 0 < d) (ρ V : Op d) (hρ : ρ.PosSemidef)
    (htρ : ρ.trace = 1) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ)
    (M : ℕ) (hM : 0 < M) :
    (iidLaw (D.shotLaw hd ρ V hρ htρ hV) M).variance
      (FinDist.avg (readout D.shotWeight eig)) =
        (D.normalization * (∑ i, (D.K i * ρ * (D.K i)ᴴ * observable V eig ^ 2).trace.re) -
          (D.compiledMean ρ (observable V eig)) ^ 2) / M := by
  rw [iid_average_variance _ M _ hM, D.single_shot_variance hd]

theorem independent_rms_bound (hd : 0 < d) (ρ V : Op d) (hρ : ρ.PosSemidef)
    (htρ : ρ.trace = 1) (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ)
    (M : ℕ) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hbudget : (D.shotLaw hd ρ V hρ htρ hV).variance (readout D.shotWeight eig) / ε^2 ≤ M) :
    Real.sqrt ((iidLaw (D.shotLaw hd ρ V hρ htρ hV) M).variance
      (FinDist.avg (readout D.shotWeight eig))) ≤ ε := by
  rw [iid_average_variance _ M _ hM, Real.sqrt_le_left hε.le]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hM)).mpr
  have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hbudget
  simpa only [mul_comm] using h

end Qatlib.Papers.HermitianMap26.Construction.SignedKraus
