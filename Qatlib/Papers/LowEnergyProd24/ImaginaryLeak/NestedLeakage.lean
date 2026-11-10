/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.WeightedNested
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.InteractionWeight
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}

def sourceEll (L k d : ℕ) (J : ℝ) (n : ℕ) : ℝ :=
  (L : ℝ)*(n.factorial : ℝ)*(J*k*d*Real.exp 1)^n*Real.exp 1*J

theorem sourceEll_nonneg (L k d n : ℕ) (J : ℝ) (hJ : 0 ≤ J) : 0 ≤ sourceEll L k d J n := by
  unfold sourceEll
  positivity

theorem actual_weighted_source_ell (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ) (seed : Fin M)
    (hL : (h.labels seed).card ≤ L) (xs : List (Fin M)) :
    ‖weighted h.total (RetainedError.nested h seed xs) (1/(2*J*k*d))‖ ≤ sourceEll L k d J xs.length := by
  calc
    _ ≤ (L : ℝ)*((k*d)^xs.length*xs.length.factorial : ℕ)*(2*J)^(xs.length+1) :=
      actual_weighted_nested h hJ hk hd L seed hL xs
    _ ≤ (L : ℝ)*((k*d)^xs.length*xs.length.factorial : ℕ)*(Real.exp 1*J)^(xs.length+1) := by
      gcongr
      exact Real.exp_one_gt_two.le
    _ = _ := by
      unfold sourceEll
      push_cast
      rw [mul_pow, pow_succ]
      ring

theorem actual_nested_leakage (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ) (seed : Fin M)
    (hL : (h.labels seed).card ≤ L) (xs : List (Fin M)) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*RetainedError.nested h seed xs*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*sourceEll L k d J xs.length :=
  (weighted_leakage h.total (RetainedError.nested h seed xs) h.total_hermitian Δ Λ
    (1/(2*J*k*d)) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (actual_weighted_source_ell h hJ hk hd L seed hL xs) (Real.exp_pos _).le)

def nestedProduct (h : Hamiltonian N R M k d J) (factors : List (Fin M × List (Fin M))) :=
  (factors.map (fun factor => RetainedError.nested h factor.1 factor.2)).prod

theorem actual_weighted_nested_product (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (factors : List (Fin M × List (Fin M))) :
    ‖weighted h.total (nestedProduct h factors) (1/(2*J*k*d))‖ ≤
      (factors.map (fun factor => sourceEll L k d J factor.2.length)).prod := by
  induction factors with
  | nil =>
    have he : weighted h.total 1 (1/(2*J*k*d)) = 1 := by
      simpa only [evolve, neg_zero, Complex.ofReal_zero, zero_mul, zero_smul, NormedSpace.exp_zero] using
        weighted_exact_evolve h (1/(2*J*k*d)) 0
    simpa only [nestedProduct, List.map_nil, List.prod_nil, he, norm_one] using (le_refl (1 : ℝ))
  | cons factor factors ih =>
    change ‖weighted h.total (RetainedError.nested h factor.1 factor.2*nestedProduct h factors) (1/(2*J*k*d))‖ ≤
      sourceEll L k d J factor.2.length * (factors.map (fun factor => sourceEll L k d J factor.2.length)).prod
    rw [weighted_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul
      (actual_weighted_source_ell h hJ hk hd L factor.1 (hL factor.1) factor.2) ih
      (norm_nonneg _) (sourceEll_nonneg L k d factor.2.length J hJ.le))

theorem actual_nested_product_leakage (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (factors : List (Fin M × List (Fin M))) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*nestedProduct h factors*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*(factors.map (fun factor => sourceEll L k d J factor.2.length)).prod :=
  (weighted_leakage h.total (nestedProduct h factors) h.total_hermitian Δ Λ
    (1/(2*J*k*d)) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (actual_weighted_nested_product h hJ hk hd L hL factors) (Real.exp_pos _).le)
end Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
