/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationJackson
import Qatlib.Papers.Cbmd26.Algorithms.ApproximationAmplifier
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Floor.Semiring
set_option warningAsError false

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Polynomial
open scoped Classical

private def clippedRamp (g x : ℝ) : ℝ := min 1 (max (-1) (2 / g * x - 1))

private theorem clippedRamp_continuous (g : ℝ) : Continuous (clippedRamp g) := by
  unfold clippedRamp
  fun_prop

private theorem clippedRamp_bounded (g x : ℝ) : |clippedRamp g x| ≤ 1 := by
  apply abs_le.mpr
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

private theorem clippedRamp_lipschitz {g : ℝ} (hg : 0 < g) (x y : ℝ) :
    |clippedRamp g x - clippedRamp g y| ≤ (2 / g) * |x - y| := by
  have hl := ((LipschitzWith.id.const_max (-1 : ℝ)).const_min 1).dist_le_mul
    (2 / g * x - 1) (2 / g * y - 1)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] at hl
  have he : (2 / g * x - 1) - (2 / g * y - 1) = (2 / g) * (x - y) := by ring
  have hpos : 0 < 2 / g := div_pos (by norm_num) hg
  simpa only [clippedRamp, he, abs_mul, abs_of_pos hpos] using hl

private theorem clippedRamp_low {g : ℝ} (hg : 0 < g) {x : ℝ} (hx : x ≤ 0) :
    clippedRamp g x = -1 := by
  have hh : 2 / g * x - 1 ≤ -1 := by
    have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 / g) hx
    linarith
  simp [clippedRamp, max_eq_left hh]

private theorem clippedRamp_high {g : ℝ} (hg : 0 < g) {x : ℝ} (hx : g ≤ x) :
    clippedRamp g x = 1 := by
  have hh : 1 ≤ 2 / g * x - 1 := by
    have := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 2 / g)
    have he : 2 / g * g = 2 := div_mul_cancel₀ 2 hg.ne'
    linarith
  exact min_eq_left (hh.trans (le_max_right _ _))

theorem bounded_step_polynomial_exists (g : ℝ) (hg : 0 < g)
    (K m : ℕ) (hK : 0 < K) (hKg : 512 / g ≤ (K : ℝ)) :
    ∃ W : Polynomial ℝ,
      W.natDegree ≤ 4 * m * (K - 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, W.eval x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 0, W.eval x ≤ (1 / 2 : ℝ) ^ m) ∧
      (∀ x ∈ Set.Icc g 1, 1 - W.eval x ≤ (1 / 2 : ℝ) ^ m) := by
  obtain ⟨P, hd, hb, he⟩ := bounded_jackson_polynomial_exists (clippedRamp g)
    (clippedRamp_continuous g) (2 / g) (by positivity)
    (fun x _ => clippedRamp_bounded g x)
    (fun x _ y _ => clippedRamp_lipschitz hg x y) K hK
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have herr : 32 * (2 / g) / (K : ℝ) ≤ 1 / 8 := by
    apply (div_le_iff₀ hKpos).mpr
    calc
      32 * (2 / g) = (1 / 8) * (512 / g) := by ring
      _ ≤ (1 / 8) * (K : ℝ) := mul_le_mul_of_nonneg_left hKg (by norm_num)
  let Q : Polynomial ℝ := C (1 / 2) * (P + 1)
  have hQ (x : ℝ) : Q.eval x = (P.eval x + 1) / 2 := by simp [Q]; ring
  have hQb (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      Q.eval x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hQ]
    have hp := abs_le.mp (hb x hx)
    constructor <;> linarith [hp.1, hp.2]
  let W := (majorityPolynomial m).comp Q
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · have hQd : Q.natDegree ≤ 2 * (K - 1) := by
      apply (natDegree_mul_le).trans
      have hp := natDegree_add_le P 1
      simp only [natDegree_one, max_zero] at hp
      simpa only [natDegree_C, zero_add] using hp.trans hd
    exact (natDegree_comp_le).trans ((Nat.mul_le_mul (majorityPolynomial_degree m) hQd).trans_eq
      (by ring))
  · intro x hx
    simpa only [W, eval_comp] using majorityPolynomial_unit_interval m (Q.eval x) (hQb x hx)
  · intro x hx
    have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1, hx.2.trans (by norm_num)⟩
    have he' := (he x hx').trans herr
    rw [clippedRamp_low hg hx.2] at he'
    have hlow : Q.eval x ∈ Set.Icc (0 : ℝ) (1 / 8) := by
      refine ⟨(hQb x hx').1, ?_⟩
      rw [hQ]
      linarith [(abs_le.mp he').2]
    simpa only [W, eval_comp] using majorityPolynomial_low m (Q.eval x) hlow
  · intro x hx
    have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨(by linarith [hx.1]), hx.2⟩
    have he' := (he x hx').trans herr
    rw [clippedRamp_high hg hx.1] at he'
    have hhigh : Q.eval x ∈ Set.Icc (7 / 8 : ℝ) 1 := by
      refine ⟨?_, (hQb x hx').2⟩
      rw [hQ]
      linarith [(abs_le.mp he').1]
    simpa only [W, eval_comp] using majorityPolynomial_high m (Q.eval x) hhigh

def dyadicOrder (ε : ℝ) : ℕ := ⌈Real.log ε⁻¹ / Real.log 2⌉₊

theorem dyadicOrder_error {ε : ℝ} (hε : 0 < ε) :
    (1 / 2 : ℝ) ^ dyadicOrder ε ≤ ε := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := (div_le_iff₀ htwo).mp (Nat.le_ceil (Real.log ε⁻¹ / Real.log 2))
  rw [Real.log_inv] at hm
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  calc
    (1 / 2 : ℝ) ^ dyadicOrder ε = Real.exp ((dyadicOrder ε : ℝ) * Real.log (1 / 2)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log ε) := by
      apply Real.exp_le_exp.mpr
      rw [hh]
      have hm' : -Real.log ε ≤ (dyadicOrder ε : ℝ) * Real.log 2 := by
        simpa only [dyadicOrder, Real.log_inv] using hm
      linarith
    _ = ε := Real.exp_log hε

theorem bounded_step_polynomial_precision (g ε : ℝ) (hg : 0 < g) (hε : 0 < ε) :
    ∃ W : Polynomial ℝ,
      W.natDegree ≤ 4 * dyadicOrder ε * ⌈512 / g⌉₊ ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, W.eval x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 0, W.eval x ≤ ε) ∧
      (∀ x ∈ Set.Icc g 1, 1 - W.eval x ≤ ε) := by
  obtain ⟨W, hd, hb, hl, hh⟩ := bounded_step_polynomial_exists g hg
    ⌈512 / g⌉₊ (dyadicOrder ε) (Nat.ceil_pos.mpr (by positivity)) (Nat.le_ceil _)
  refine ⟨W, hd.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _)), hb,
    fun x hx => (hl x hx).trans (dyadicOrder_error hε),
    fun x hx => (hh x hx).trans (dyadicOrder_error hε)⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
