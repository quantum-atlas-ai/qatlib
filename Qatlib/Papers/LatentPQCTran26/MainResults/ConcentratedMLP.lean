/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.NoBiasBarrenPlateau
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Trigonometric
set_option warningAsError false

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Qatlib.Papers.LatentPQCTran26.MainResults.ConcentratedMLP
open EuclideanLayer LinearMetaGrad NoBiasBarrenPlateau

def feature {d : ℕ} (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ) (z : Fin d → ℝ) : Fin 1 → ℝ :=
  fun _ => Real.tanh (a z + c)

theorem feature_bound {d : ℕ} (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (z : Fin d → ℝ) (j : Fin 1) : |feature a c z j| ≤ 1 :=
  (Real.abs_tanh_lt_one _).le

theorem feature_continuous {d : ℕ} (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ) :
    Continuous (feature a c) := by
  have ht : Continuous Real.tanh := by
    exact (Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')).congr
      (fun x => (Real.tanh_eq_sinh_div_cosh x).symm)
  exact continuous_pi (fun _ => ht.comp (a.continuous.add continuous_const))

def weights {K : ℕ} (theta v : EuclideanSpace ℝ (Fin K)) (gamma : ℝ) : Parameters K 1 :=
  WithLp.toLp 2 (fun ij => match ij.2 with | none => theta ij.1 | some _ => gamma * v ij.1)

theorem decoder_weights {K : ℕ} (theta v : EuclideanSpace ℝ (Fin K)) (gamma : ℝ)
    (u : Fin 1 → ℝ) :
    decoder K 1 u (weights theta v gamma) = theta + (gamma * u 0) • v := by
  ext i
  simp [decoder_apply,weights]
  ring

theorem output_radius {K d : ℕ} (theta v : EuclideanSpace ℝ (Fin K))
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (hv : ‖v‖ ≤ 1)
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ) (z : Fin d → ℝ) :
    ‖decoder K 1 (feature a c z) (weights theta v gamma) - theta‖ ≤ gamma := by
  rw [decoder_weights]
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hgamma]
  calc
    gamma * |feature a c z 0| * ‖v‖ ≤ gamma * 1 * 1 := by
      gcongr
      exact feature_bound a c z 0
    _ = gamma := by ring

theorem tanh_meta_gradient {K d : ℕ}
    (r : Measure (Fin d → ℝ)) [IsProbabilityMeasure r]
    (a : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ)
    (L : EuclideanSpace ℝ (Fin K) → ℝ) (hL : Differentiable ℝ L)
    (hD : Continuous (fderiv ℝ L))
    (B C : ℝ) (hB : ∀ x, ‖L x‖ ≤ B) (hC : ∀ x, ‖fderiv ℝ L x‖ ≤ C)
    (theta v : EuclideanSpace ℝ (Fin K)) (hv : ‖v‖ ≤ 1)
    (Lambda gamma g : ℝ) (hLambda : 0 < Lambda) (hgamma0 : 0 ≤ gamma)
    (hLip : ∀ x y, ‖fderiv ℝ L x - fderiv ℝ L y‖ ≤ Lambda * ‖x - y‖)
    (hg : g ≤ ‖gradient L theta‖) (hgamma : gamma ≤ g / (2 * Lambda)) :
    g / 2 ≤ ‖gradient (fun b : EuclideanSpace ℝ (Fin K) =>
      expectedLoss r (feature a c) L (weights theta v gamma + bias K 1 b)) 0‖ ∧
    ‖gradient (fun b : EuclideanSpace ℝ (Fin K) =>
      expectedLoss r (feature a c) L (weights theta v gamma + bias K 1 b)) 0‖ ≤
      ‖gradient (expectedLoss r (feature a c) L) (weights theta v gamma)‖ := by
  exact proposition10_actual r (feature a c) (feature_continuous a c).aestronglyMeasurable
    1 (feature_bound a c) L hL hD B C hB hC (weights theta v gamma) theta Lambda gamma g
    hLambda hLip (output_radius theta v gamma hgamma0 hv a c) hg hgamma

theorem input_weight_expansion {d : ℕ} (a : (Fin d → ℝ) →L[ℝ] ℝ) (z : Fin d → ℝ) :
    a z = ∑ j, z j * a (Pi.single j 1) := by
  have hz : z = ∑ j, z j • Pi.single j 1 := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hz,map_sum]
  simp only [map_smul,smul_eq_mul]

theorem parameter_count (K d : ℕ) :
    Fintype.card (Fin d) + 1 + Fintype.card (Fin K × Option (Fin 1)) = d + 2*K + 1 := by
  simp
  omega

theorem parameter_count_bound (K d : ℕ) (hK : 0 < K) (hd : 0 < d) :
    d + 2*K + 1 ≤ 4*d*K := by
  have h1 : d ≤ d*K := by nlinarith
  have h2 : K ≤ d*K := by nlinarith
  have h3 : 1 ≤ d*K := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hd hK))
  nlinarith

end Qatlib.Papers.LatentPQCTran26.MainResults.ConcentratedMLP
