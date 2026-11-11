/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevNodes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Conditioning of Chebyshev multi-product formulas

The rounded Chebyshev nodes and interpolation weights are compared with exact Chebyshev roots to
control the coefficient mass of the multi-product construction in [AftabAnTrivisa2026]. The
estimates yield logarithmic weight mass, an O(m² log² m) query factor, and a local approximation
error with explicit constants.

## Main statements

* `weight_mass_bound`: bounds the absolute weight sum by a logarithm.
* `query_factor_isBigO`: gives the asymptotic query factor.
* `construction`: collects positivity, distinctness, cost, coefficient matching, and local
  error.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevCondition
open Real Set
open Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevNodes
open scoped BigOperators

/-- For 0 ≤ a ≤ b ≤ π/2, the cosine difference is at least (b² - a²)/π. -/
private theorem cosine_gap {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    (b ^ 2 - a ^ 2) / Real.pi ≤ Real.cos a - Real.cos b := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    ((continuous_const.mul continuous_id).intervalIntegrable a b)
    (Real.continuous_sin.intervalIntegrable a b)
    (fun x hx => Real.mul_le_sin (ha.trans hx.1) (hx.2.trans hb))
  change (∫ x in a..b, (2 / Real.pi) * x) ≤ ∫ x in a..b, Real.sin x at h
  rw [intervalIntegral.integral_const_mul, integral_id, integral_sin] at h
  convert! h using 1
  ring

/-- For positive m, the sequence of node values multiplied by the sine of twice their angles is
strictly decreasing. -/
theorem scaled_sine_strictAnti (m : ℕ) (hm : 0 < m) :
    StrictAnti (fun j : Fin m => (node m j : ℝ) * Real.sin (2 * angle m j)) := by
  intro i j hij
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hi := angle_bounds m hm i
  have hj := angle_bounds m hm j
  have hij' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hij
  have hin : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have htheta : angle m i ≤ angle m j := by
    dsimp [angle]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hgap := cosine_gap hi.1.le htheta (by linarith [Real.pi_pos])
  have hquant : Real.sin (2 * angle m j) ≤
      8 * (m : ℝ) * (Real.cos (angle m i) - Real.cos (angle m j)) := by
    have hsin := Real.sin_le (by linarith [hj.1] : 0 ≤ 2 * angle m j)
    have hg := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 8 * (m : ℝ))
    have hid : 2 * angle m j ≤
        8 * (m : ℝ) * ((angle m j ^ 2 - angle m i ^ 2) / Real.pi) := by
      dsimp [angle]
      field_simp
      have : (1 : ℝ) ≤ (j.val : ℝ) := by linarith
      nlinarith [sq_nonneg ((j.val : ℝ) - (i.val : ℝ) - 1)]
    exact hsin.trans (hid.trans hg)
  have hsj : 0 < Real.sin (2 * angle m j) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hj.1]) (by linarith [hj.2, Real.pi_pos])
  have hsi : 0 < Real.sin (2 * angle m i) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hi.1]) (by linarith [hi.2, Real.pi_pos])
  have hceilj := Nat.ceil_lt_add_one (realNode_pos m hm j).le
  change (node m j : ℝ) < realNode m j + 1 at hceilj
  have hceili := Nat.le_ceil (realNode m i)
  change realNode m i ≤ (node m i : ℝ) at hceili
  have he (k : Fin m) : realNode m k * Real.sin (2 * angle m k) =
      8 * (m : ℝ) * Real.cos (angle m k) := by
    have hk := angle_bounds m hm k
    have hs := Real.sin_pos_of_pos_of_lt_pi hk.1 (by linarith [Real.pi_pos])
    rw [realNode, Real.sin_two_mul]
    field_simp
    ring
  have hu := mul_lt_mul_of_pos_right hceilj hsj
  have hl := mul_le_mul_of_nonneg_right hceili hsi.le
  rw [add_mul, he j] at hu
  rw [he i] at hl
  linarith

/-- The cross-product inequality r t ≤ q s bounds both normalized square factors when 0 < r < q
and 0 < s < t. -/
private theorem two_factor_comparison {q r s t : ℝ} (hr : 0 < r) (hqr : r < q)
    (hs : 0 < s) (hst : s < t) (h : r * t ≤ q * s) :
    q ^ 2 / (q ^ 2 - r ^ 2) ≤ t ^ 2 / (t ^ 2 - s ^ 2) ∧
      r ^ 2 / (q ^ 2 - r ^ 2) ≤ s ^ 2 / (t ^ 2 - s ^ 2) := by
  have hq := hr.trans hqr
  have ht := hs.trans hst
  have hdenq : 0 < q ^ 2 - r ^ 2 := by nlinarith
  have hdent : 0 < t ^ 2 - s ^ 2 := by nlinarith
  have hprod : (r * t) ^ 2 ≤ (q * s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  constructor
  · apply (div_le_div_iff₀ hdenq hdent).mpr
    nlinarith only [hprod]
  · apply (div_le_div_iff₀ hdenq hdent).mpr
    nlinarith only [hprod]

/-- Each absolute interpolation factor for the rounded nodes is bounded by the corresponding
sine-based reference factor. -/
theorem factor_le_reference (m : ℕ) (hm : 0 < m) (j l : Fin m) (hlj : l ≠ j) :
    |(node m j : ℝ) ^ 2 / ((node m j : ℝ) ^ 2 - (node m l : ℝ) ^ 2)| ≤
      |Real.sin (2 * angle m l) ^ 2 /
        (Real.sin (2 * angle m l) ^ 2 - Real.sin (2 * angle m j) ^ 2)| := by
  have hnj : 0 < (node m j : ℝ) := by exact_mod_cast node_pos m hm j
  have hnl : 0 < (node m l : ℝ) := by exact_mod_cast node_pos m hm l
  have hbj := angle_bounds m hm j
  have hbl := angle_bounds m hm l
  have hsj := Real.sin_pos_of_pos_of_lt_pi (by linarith [hbj.1] : 0 < 2 * angle m j)
    (by linarith [hbj.2, Real.pi_pos])
  have hsl := Real.sin_pos_of_pos_of_lt_pi (by linarith [hbl.1] : 0 < 2 * angle m l)
    (by linarith [hbl.2, Real.pi_pos])
  have hsin : StrictMono (fun k : Fin m => Real.sin (2 * angle m k)) := by
    intro a b hab
    have ha := angle_bounds m hm a
    have hb := angle_bounds m hm b
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [ha.1, Real.pi_pos])
      (by linarith [hb.2])
    have hab' : (a.val : ℝ) < (b.val : ℝ) := by exact_mod_cast hab
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
    unfold angle
    apply mul_lt_mul_of_pos_left _ (by norm_num : (0 : ℝ) < 2)
    apply div_lt_div_of_pos_right _ (by positivity)
    exact mul_lt_mul_of_pos_left (by linarith) Real.pi_pos
  rcases lt_or_gt_of_ne hlj with hlt | hgt
  · have hnodes : (node m j : ℝ) < (node m l : ℝ) := by exact_mod_cast node_strictAnti m hm hlt
    have hcmp := (two_factor_comparison hnj hnodes hsl (hsin hlt)
      (scaled_sine_strictAnti m hm hlt).le).2
    have hdq : (node m j : ℝ) ^ 2 - (node m l : ℝ) ^ 2 < 0 := by nlinarith
    have hds : Real.sin (2 * angle m l) ^ 2 - Real.sin (2 * angle m j) ^ 2 < 0 := by
      nlinarith [hsin hlt]
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_neg hdq,
      abs_div, abs_of_nonneg (sq_nonneg _), abs_of_neg hds]
    simpa only [neg_sub] using! hcmp
  · have hnodes : (node m l : ℝ) < (node m j : ℝ) := by exact_mod_cast node_strictAnti m hm hgt
    have hcmp := (two_factor_comparison hnl hnodes hsj (hsin hgt)
      (scaled_sine_strictAnti m hm hgt).le).1
    have hdq : 0 < (node m j : ℝ) ^ 2 - (node m l : ℝ) ^ 2 := by nlinarith
    have hds : 0 < Real.sin (2 * angle m l) ^ 2 - Real.sin (2 * angle m j) ^ 2 := by
      nlinarith [hsin hgt]
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hdq,
      abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos hds]
    exact hcmp

open Polynomial

/-- The Chebyshev root phase π(2j + 1)/(2m). -/
def phase (m : ℕ) (j : Fin m) : ℝ := Real.pi * (2 * (j.val : ℝ) + 1) / (2 * (m : ℝ))

/-- For positive m, every reference phase lies strictly between 0 and π. -/
theorem phase_bounds (m : ℕ) (hm : 0 < m) (j : Fin m) :
    0 < phase m j ∧ phase m j < Real.pi := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hj : (j.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr j.isLt
  constructor
  · unfold phase; positivity
  · rw [phase, div_lt_iff₀ (by positivity : 0 < 2 * (m : ℝ))]
    nlinarith [Real.pi_pos]

/-- For positive m, the cosines of the reference phases form a strictly decreasing sequence. -/
theorem cosine_strictAnti (m : ℕ) (hm : 0 < m) :
    StrictAnti (fun j : Fin m => Real.cos (phase m j)) := by
  intro i j hij
  have hi := phase_bounds m hm i
  have hj := phase_bounds m hm j
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  apply Real.cos_lt_cos_of_nonneg_of_le_pi hi.1.le hj.2.le
  unfold phase
  apply div_lt_div_of_pos_right _ (by positivity)
  exact mul_lt_mul_of_pos_left (by linarith) Real.pi_pos

/-- Each cosine of a reference phase is a root of the degree-m Chebyshev polynomial. -/
theorem reference_root (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (Polynomial.Chebyshev.T ℝ m).eval (Real.cos (phase m j)) = 0 := by
  rw [Polynomial.Chebyshev.T_real_cos]
  have he : ((m : ℤ) : ℝ) * phase m j = (j.val : ℝ) * Real.pi + Real.pi / 2 := by
    have hmpos : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    simp only [Int.cast_natCast]
    unfold phase
    field_simp
  rw [he, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

/-- The degree-m Chebyshev polynomial is its leading coefficient times the nodal polynomial of
the reference roots. -/
theorem reference_nodal (m : ℕ) (hm : 0 < m) :
    Polynomial.Chebyshev.T ℝ m =
      Polynomial.C (Polynomial.Chebyshev.T ℝ m).leadingCoeff *
        Lagrange.nodal Finset.univ (fun j : Fin m => Real.cos (phase m j)) := by
  have hlc : (Polynomial.Chebyshev.T ℝ m).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.Chebyshev.T_ne_zero ℝ m)
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ
    (cosine_strictAnti m hm).injective.injOn
  · simp [Polynomial.Chebyshev.degree_T]
  · rw [Polynomial.degree_C_mul hlc, Lagrange.degree_nodal]
    simp [Polynomial.Chebyshev.degree_T]
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Lagrange.nodal_monic.leadingCoeff, mul_one]
  · intro j hj
    rw [reference_root m hm j, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_nodal_at_node (v := fun k : Fin m => Real.cos (phase m k)) hj, mul_zero]

/-- The Lagrange basis polynomial for the reference Chebyshev roots, evaluated at 1. -/
def referenceWeight (m : ℕ) (j : Fin m) : ℝ :=
  (Lagrange.basis Finset.univ (fun k : Fin m => Real.cos (phase m k)) j).eval 1

/-- A reference weight multiplied by the Chebyshev derivative at its root and the distance of
that root from 1 equals 1. -/
theorem reference_weight_derivative (m : ℕ) (hm : 0 < m) (j : Fin m) :
    referenceWeight m j * (Polynomial.Chebyshev.T ℝ m).derivative.eval (Real.cos (phase m j)) *
      (1 - Real.cos (phase m j)) = 1 := by
  let v := fun k : Fin m => Real.cos (phase m k)
  have hnode : 1 ≠ v j := by
    have ht := phase_bounds m hm j
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) ht.2.le ht.1
    simpa [v] using! h.ne.symm
  have hderiv := congrArg (fun p : Polynomial ℝ => p.derivative.eval (v j)) (reference_nodal m hm)
  simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C] at hderiv
  have heval := congrArg (Polynomial.eval (1 : ℝ)) (reference_nodal m hm)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.Chebyshev.T_eval_one] at heval
  have hd : (Lagrange.nodal Finset.univ v).derivative.eval (v j) ≠ 0 := by
    rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ j), Lagrange.eval_nodal]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1
      ((cosine_strictAnti m hm).injective h).symm)
  unfold referenceWeight
  change (Lagrange.basis Finset.univ v j).eval 1 * _ * _ = _
  rw [Lagrange.eval_basis_not_at_node (Finset.mem_univ j) hnode,
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ j), hderiv]
  change _ * _ * (1 - v j) = _
  field_simp [hd, sub_ne_zero.mpr hnode]
  change (Lagrange.nodal Finset.univ v).eval 1 *
    (Polynomial.Chebyshev.T ℝ m).leadingCoeff *
    (Lagrange.nodal Finset.univ v).derivative.eval (v j) = _
  have hz : (Lagrange.nodal Finset.univ v).eval 1 *
      (Polynomial.Chebyshev.T ℝ m).leadingCoeff = 1 := by
    simpa only [mul_comm] using! heval.symm
  rw [hz, one_mul]

/-- At a reference root, the absolute Chebyshev derivative multiplied by the sine of its phase
equals m. -/
theorem reference_derivative_abs (m : ℕ) (hm : 0 < m) (j : Fin m) :
    |(Polynomial.Chebyshev.T ℝ m).derivative.eval (Real.cos (phase m j))| *
      Real.sin (phase m j) = (m : ℝ) := by
  have hp := phase_bounds m hm j
  have hs : 0 < Real.sin (phase m j) := Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2
  have hd : (Polynomial.Chebyshev.T ℝ m).derivative.eval (Real.cos (phase m j)) *
      Real.sin (phase m j) = (m : ℝ) * Real.sin ((m : ℝ) * phase m j) := by
    rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul, Polynomial.eval_intCast]
    have hu := Polynomial.Chebyshev.U_real_cos (phase m j) ((m : ℤ) - 1)
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] at hu
    simp only [mul_assoc, hu, Int.cast_natCast]
  have hc : Real.cos ((m : ℝ) * phase m j) = 0 := by
    simpa only [Polynomial.Chebyshev.T_real_cos, Int.cast_natCast] using! reference_root m hm j
  have habs : |Real.sin ((m : ℝ) * phase m j)| = 1 := by
    have h := Real.sin_sq_add_cos_sq ((m : ℝ) * phase m j)
    simp only [hc, zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
    exact (sq_eq_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa [sq_abs, sq] using! h)
  have h := congrArg abs hd
  simpa only [abs_mul, abs_of_pos hs, abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m),
      habs, mul_one] using! h

/-- The absolute reference weight at index j is at most 2/(j + 1). -/
theorem reference_weight_bound (m : ℕ) (hm : 0 < m) (j : Fin m) :
    |referenceWeight m j| ≤ 2 / ((j.val : ℝ) + 1) := by
  have hp := phase_bounds m hm j
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hs : 0 < Real.sin (phase m j / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hc : 0 < 1 - Real.cos (phase m j) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hp.2.le hp.1
    simpa using! sub_pos.mpr h
  have ha := congrArg abs (reference_weight_derivative m hm j)
  simp only [abs_mul, abs_of_pos hc, abs_one] at ha
  have hd := reference_derivative_abs m hm j
  have he : |referenceWeight m j| * (m : ℝ) * (1 - Real.cos (phase m j)) =
      Real.sin (phase m j) := by
    calc
      _ = (|referenceWeight m j| *
          |(Polynomial.Chebyshev.T ℝ m).derivative.eval (Real.cos (phase m j))| *
          (1 - Real.cos (phase m j))) * Real.sin (phase m j) := by rw [← hd]; ring
      _ = _ := by rw [ha, one_mul]
  have hhalf : |referenceWeight m j| * (m : ℝ) * Real.sin (phase m j / 2) =
      Real.cos (phase m j / 2) := by
    have hphase : phase m j = 2 * (phase m j / 2) := by ring
    rw [hphase, Real.cos_two_mul_eq_one_sub, Real.sin_two_mul] at he
    have hzero : (|referenceWeight m j| * (m : ℝ) * Real.sin (phase m j / 2) -
        Real.cos (phase m j / 2)) * (2 * Real.sin (phase m j / 2)) = 0 := by
      nlinarith only [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (by positivity))
  have hsine := Real.mul_le_sin (by linarith [hp.1] : 0 ≤ phase m j / 2)
    (by linarith [hp.2] : phase m j / 2 ≤ Real.pi / 2)
  have hlower : ((j.val : ℝ) + 1) / 2 ≤ (m : ℝ) * Real.sin (phase m j / 2) := by
    have h := mul_le_mul_of_nonneg_left hsine hmpos.le
    have heq : (m : ℝ) * ((2 / Real.pi) * (phase m j / 2)) =
        (2 * (j.val : ℝ) + 1) / 2 := by
      unfold phase
      field_simp
    rw [heq] at h
    linarith [show (0 : ℝ) ≤ (j.val : ℝ) from Nat.cast_nonneg _]
  apply (le_div_iff₀ (by positivity : 0 < (j.val : ℝ) + 1)).mpr
  have h := mul_le_mul_of_nonneg_left hlower (abs_nonneg (referenceWeight m j))
  rw [← mul_assoc, hhalf] at h
  linarith [Real.cos_le_one (phase m j / 2)]

/-- The reference phase is four times the node angle. -/
theorem phase_eq_four_angle (m : ℕ) (j : Fin m) : phase m j = 4 * angle m j := by
  unfold phase angle
  ring

/-- A reference weight is the product of the corresponding sine-square interpolation factors. -/
theorem reference_weight_product (m : ℕ) (j : Fin m) :
    referenceWeight m j = ∏ l ∈ Finset.univ.erase j,
      Real.sin (2 * angle m l) ^ 2 /
        (Real.sin (2 * angle m l) ^ 2 - Real.sin (2 * angle m j) ^ 2) := by
  unfold referenceWeight Lagrange.basis
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l _
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  have he (k : Fin m) : Real.cos (phase m k) = 1 - 2 * Real.sin (2 * angle m k) ^ 2 := by
    rw [phase_eq_four_angle]
    rw [show 4 * angle m k = 2 * (2 * angle m k) by ring,
      Real.cos_two_mul_eq_one_sub]
  rw [he j, he l]
  have hd : (1 - 2 * Real.sin (2 * angle m j) ^ 2) -
      (1 - 2 * Real.sin (2 * angle m l) ^ 2) =
        2 * (Real.sin (2 * angle m l) ^ 2 - Real.sin (2 * angle m j) ^ 2) := by ring
  rw [hd, mul_inv_rev]
  simp only [div_eq_mul_inv]
  ring

/-- For positive m, each rounded-node weight is bounded in absolute value by its reference
weight. -/
theorem weight_le_reference (m : ℕ) (hm : 0 < m) (j : Fin m) :
    |weight m j| ≤ |referenceWeight m j| := by
  rw [weight_product m hm j, reference_weight_product]
  simp only [Finset.abs_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro l hl
  exact factor_le_reference m hm j l (Finset.mem_erase.mp hl).1

/-- For positive m, the absolute rounded-node weight at index j is at most 2/(j + 1). -/
theorem weight_bound (m : ℕ) (hm : 0 < m) (j : Fin m) :
    |weight m j| ≤ 2 / ((j.val : ℝ) + 1) :=
  (weight_le_reference m hm j).trans (reference_weight_bound m hm j)

/-- The total absolute weight is at most twice the m-th harmonic number. -/
theorem weight_mass_harmonic (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, |weight m j|) ≤ 2 * (harmonic m : ℝ) := by
  calc
    _ ≤ ∑ j : Fin m, 2 / ((j.val : ℝ) + 1) :=
      Finset.sum_le_sum (fun j _ => weight_bound m hm j)
    _ = _ := by
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ j ∈ Finset.range m, ((j : ℝ) + 1)⁻¹ :=
          Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j : ℝ) + 1)⁻¹) m
        _ = _ := by unfold harmonic; push_cast; rfl

/-- The total absolute weight is bounded by (2 + 2/log 2) log(m + 1). -/
theorem weight_mass_bound (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, |weight m j|) ≤
      (2 + 2 / Real.log 2) * Real.log ((m : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hmono : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hu : (2 : ℝ) ≤ (2 / Real.log 2) * Real.log ((m : ℝ) + 1) := by
    calc
      _ = (2 / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hh := harmonic_le_one_add_log m
  have hmass := weight_mass_harmonic m hm
  nlinarith only [hu, hh, hmass, hmono]

/-- The total absolute Chebyshev weight is O(log m) as m tends to infinity. -/
theorem weight_mass_isBigO :
    (fun m : ℕ => ∑ j : Fin m, |weight m j|) =O[Filter.atTop]
      (fun m : ℕ => Real.log (m : ℝ)) := by
  let C := 2 + 2 / Real.log 2
  have hC : 0 ≤ C := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C]; positivity
  apply Asymptotics.IsBigO.of_bound (2 * C)
  filter_upwards [Filter.eventually_ge_atTop 2] with m hm
  have hmpos : 0 < m := by omega
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith)
  have hlogbound : Real.log ((m : ℝ) + 1) ≤ 2 * Real.log (m : ℝ) := by
    calc
      _ ≤ Real.log ((m : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hn : 0 ≤ ∑ j : Fin m, |weight m j| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  simp only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hlog]
  calc
    _ ≤ C * Real.log ((m : ℝ) + 1) := weight_mass_bound m hmpos
    _ ≤ C * (2 * Real.log (m : ℝ)) := mul_le_mul_of_nonneg_left hlogbound hC
    _ = _ := by ring

/-- The product of total absolute weight and total node count is bounded by an explicit constant
times m² log²(m + 1). -/
theorem query_factor_bound (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, |weight m j|) * (∑ j : Fin m, (node m j : ℝ)) ≤
      (2 + 2 / Real.log 2) * (16 + 17 / Real.log 2) *
        (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1) ^ 2 := by
  have hlog : 0 ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m])
  have hconst : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := mul_le_mul (weight_mass_bound m hm) (node_sum_bound m hm)
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
  convert! h using 1
  ring

/-- The product of total absolute weight and total node count is O(m² log² m). -/
theorem query_factor_isBigO :
    (fun m : ℕ => (∑ j : Fin m, |weight m j|) * (∑ j : Fin m, (node m j : ℝ)))
      =O[Filter.atTop] (fun m : ℕ => (m : ℝ) ^ 2 * Real.log (m : ℝ) ^ 2) := by
  have h := weight_mass_isBigO.mul node_sum_isBigO
  have he : (fun m : ℕ => Real.log (m : ℝ) * ((m : ℝ) ^ 2 * Real.log (m : ℝ))) =
      (fun m : ℕ => (m : ℝ) ^ 2 * Real.log (m : ℝ) ^ 2) := by
    funext m
    ring
  rw [he] at h
  exact h

open Qatlib.Papers.CommutLCHS26.MainResults
open MPFRemainder GeneralMPF
open scoped Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The Chebyshev multi-product formula has local error bounded by the exponential Taylor tail
of order 2m + 1 times the explicit logarithmic conditioning factor. -/
theorem well_conditioned_local_error (X Y : Matrix I I ℂ) (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ‖multiProduct (fun j => strangRepeats X Y (node m j)) (weight m) t -
      NormedSpace.exp (t • (X + Y))‖ ≤
      ((2 + 2 / Real.log 2) * Real.log ((m : ℝ) + 1) + 1) *
        (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
          ((2 * m + 1).factorial : ℝ)) := by
  apply (local_error X Y m hm t).trans
  apply mul_le_mul_of_nonneg_right (_root_.add_le_add (weight_mass_bound m hm) le_rfl)
  positivity

/-- The Chebyshev construction has positive distinct nodes, controlled weight mass and word
length, coefficient matching through degree 2m, and the stated local error bound
[AftabAnTrivisa2026]. -/
theorem construction (X Y : Matrix I I ℂ) (m : ℕ) (hm : 0 < m) :
    (∀ j : Fin m, 0 < node m j) ∧ Function.Injective (node m) ∧
    1 ≤ (∑ j : Fin m, |weight m j|) ∧
    (∑ j : Fin m, |weight m j|) ≤ (2 + 2 / Real.log 2) * Real.log ((m : ℝ) + 1) ∧
    (∑ j : Fin m, ((strangRepeats X Y (node m j)).length : ℝ)) ≤
      3 * (16 + 17 / Real.log 2) * (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1) ∧
    (∀ n : ℕ, n < 2 * m + 1 →
      coefficient (fun j => strangRepeats X Y (node m j)) (weight m) n =
        ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n) ∧
    (∀ t : ℝ,
      ‖multiProduct (fun j => strangRepeats X Y (node m j)) (weight m) t -
        NormedSpace.exp (t • (X + Y))‖ ≤
        ((2 + 2 / Real.log 2) * Real.log ((m : ℝ) + 1) + 1) *
          (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
            ((2 * m + 1).factorial : ℝ))) :=
  ⟨node_pos m hm, (node_strictAnti m hm).injective, weight_mass_lower m hm,
    weight_mass_bound m hm, visits_bound X Y m hm,
    coefficients X Y m hm, well_conditioned_local_error X Y m hm⟩

end Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevCondition
