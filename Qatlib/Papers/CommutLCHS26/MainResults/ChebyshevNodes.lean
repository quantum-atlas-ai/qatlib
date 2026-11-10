/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.GeneralMPF
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.LinearAlgebra.Lagrange
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevNodes

open Real Set
open scoped BigOperators Matrix.Norms.L2Operator

def angle (m : ℕ) (j : Fin m) : ℝ := Real.pi * (2 * (j.val : ℝ) + 1) / (8 * (m : ℝ))

def realNode (m : ℕ) (j : Fin m) : ℝ := 4 * (m : ℝ) / Real.sin (angle m j)

def node (m : ℕ) (j : Fin m) : ℕ := Nat.ceil (realNode m j)

theorem angle_bounds (m : ℕ) (hm : 0 < m) (j : Fin m) :
    0 < angle m j ∧ angle m j < Real.pi / 4 := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hj : (j.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  constructor
  · unfold angle; positivity
  · rw [angle, div_lt_iff₀ (by positivity : 0 < 8 * (m : ℝ))]
    nlinarith [Real.pi_pos]

theorem realNode_pos (m : ℕ) (hm : 0 < m) (j : Fin m) : 0 < realNode m j := by
  have h := angle_bounds m hm j
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  exact div_pos (by positivity) (Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [Real.pi_pos]))

theorem node_pos (m : ℕ) (hm : 0 < m) (j : Fin m) : 0 < node m j :=
  Nat.ceil_pos.mpr (realNode_pos m hm j)

private theorem sine_gap {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 4) :
    (b - a) / Real.pi ≤ Real.sin b - Real.sin a := by
  have hc : (1 / 2 : ℝ) ≤ Real.cos ((b + a) / 2) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have hs := Real.mul_le_sin (x := (b - a) / 2) (by linarith) (by linarith [Real.pi_pos])
  have h := mul_le_mul hc hs (by positivity) (by linarith)
  calc
    _ = 2 * ((1 / 2 : ℝ) * ((2 / Real.pi) * ((b - a) / 2))) := by ring
    _ ≤ 2 * (Real.cos ((b + a) / 2) * Real.sin ((b - a) / 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by rw [Real.sin_sub_sin]; ring

private theorem inverse_sine_gap {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ Real.pi / 4) :
    (b - a) / Real.pi ≤ (Real.sin a)⁻¹ - (Real.sin b)⁻¹ := by
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])
  have hsb : 0 < Real.sin b :=
      Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hab) (by linarith [Real.pi_pos])
  have hgap := sine_gap ha hab hb
  have hnum : 0 ≤ Real.sin b - Real.sin a :=
    (div_nonneg (sub_nonneg.mpr hab) Real.pi_pos.le).trans hgap
  have hprod : Real.sin a * Real.sin b ≤ 1 := by
    nlinarith [mul_le_mul (Real.sin_le_one a) (Real.sin_le_one b) hsb.le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    _ ≤ Real.sin b - Real.sin a := hgap
    _ ≤ (Real.sin b - Real.sin a) / (Real.sin a * Real.sin b) := by
      apply (le_div_iff₀ (mul_pos hsa hsb)).mpr
      simpa only [mul_one] using! mul_le_mul_of_nonneg_left hprod hnum
    _ = _ := by field_simp

theorem realNode_gap (m : ℕ) (hm : 0 < m) (i j : Fin m) (hij : i < j) :
    (j.val : ℝ) - (i.val : ℝ) ≤ realNode m i - realNode m j := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
  have hi := angle_bounds m hm i
  have hj := angle_bounds m hm j
  have ht : angle m i ≤ angle m j := by
    unfold angle
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have h := mul_le_mul_of_nonneg_left (inverse_sine_gap hi.1 ht hj.2.le)
    (by positivity : 0 ≤ 4 * (m : ℝ))
  have he : 4 * (m : ℝ) * ((angle m j - angle m i) / Real.pi) =
      (j.val : ℝ) - (i.val : ℝ) := by
    unfold angle
    field_simp
    ring
  rw [he] at h
  exact h.trans_eq (by dsimp [realNode]; ring)

theorem node_strictAnti (m : ℕ) (hm : 0 < m) : StrictAnti (node m) := by
  intro i j hij
  have hgap := realNode_gap m hm i j hij
  have hdiff : (1 : ℝ) ≤ (j.val : ℝ) - (i.val : ℝ) := by
    have h : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (show i.val + 1 ≤ j.val from hij)
    linarith
  have hlow := Nat.le_ceil (realNode m i)
  have hupp := Nat.ceil_lt_add_one (realNode_pos m hm j).le
  by_contra h
  have hle : node m i ≤ node m j := Nat.le_of_not_gt h
  have hle' : (node m i : ℝ) ≤ (node m j : ℝ) := by exact_mod_cast hle
  change realNode m i ≤ (node m i : ℝ) at hlow
  change (node m j : ℝ) < realNode m j + 1 at hupp
  linarith

theorem realNode_bound (m : ℕ) (hm : 0 < m) (j : Fin m) :
    realNode m j ≤ 16 * (m : ℝ) ^ 2 / (2 * (j.val : ℝ) + 1) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht := angle_bounds m hm j
  have hs : (2 * (j.val : ℝ) + 1) / (4 * (m : ℝ)) ≤ Real.sin (angle m j) := by
    have h := Real.mul_le_sin ht.1.le (by linarith [Real.pi_pos] : angle m j ≤ Real.pi / 2)
    have he : (2 / Real.pi) * angle m j = (2 * (j.val : ℝ) + 1) / (4 * (m : ℝ)) := by
      unfold angle
      field_simp
      ring
    simpa only [he] using! h
  have hd : 0 < (2 * (j.val : ℝ) + 1) / (4 * (m : ℝ)) := by positivity
  calc
    _ ≤ (4 * (m : ℝ)) / ((2 * (j.val : ℝ) + 1) / (4 * (m : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) hd hs
    _ = _ := by field_simp; ring

theorem node_bound (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (node m j : ℝ) ≤ 16 * (m : ℝ) ^ 2 / (2 * (j.val : ℝ) + 1) + 1 :=
  (Nat.ceil_lt_add_one (realNode_pos m hm j).le).le.trans
    (_root_.add_le_add (realNode_bound m hm j) le_rfl)

theorem node_sum_harmonic (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, (node m j : ℝ)) ≤ 16 * (m : ℝ) ^ 2 * (harmonic m : ℝ) + m := by
  have hb (j : Fin m) : (node m j : ℝ) ≤ 16 * (m : ℝ) ^ 2 / ((j.val : ℝ) + 1) + 1 := by
    apply (node_bound m hm j).trans
    apply _root_.add_le_add _ le_rfl
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by linarith [show (0 : ℝ) ≤ (j.val : ℝ) from Nat.cast_nonneg j.val])
  calc
    _ ≤ ∑ j : Fin m, (16 * (m : ℝ) ^ 2 / ((j.val : ℝ) + 1) + 1) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, div_eq_mul_inv]
      rw [← Finset.mul_sum]
      have hh : (∑ j : Fin m, ((j.val : ℝ) + 1)⁻¹) = (harmonic m : ℝ) := by
        calc
          _ = ∑ j ∈ Finset.range m, ((j : ℝ) + 1)⁻¹ :=
            Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j : ℝ) + 1)⁻¹) m
          _ = _ := by unfold harmonic; push_cast; rfl
      rw [hh]

theorem node_sum_bound (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, (node m j : ℝ)) ≤
      (16 + 17 / Real.log 2) * (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log ((m : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hmono : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hcost := node_sum_harmonic m hm
  have hhar := harmonic_le_one_add_log m
  have hstep : 16 * (m : ℝ) ^ 2 * (harmonic m : ℝ) + m ≤
      (m : ℝ) ^ 2 * (17 + 16 * Real.log ((m : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_left hhar (by positivity : 0 ≤ 16 * (m : ℝ) ^ 2)
    have h' := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 16 * (m : ℝ) ^ 2)
    nlinarith [sq_nonneg ((m : ℝ) - 1)]
  have hunit : (17 : ℝ) ≤ (17 / Real.log 2) * Real.log ((m : ℝ) + 1) := by
    calc
      _ = (17 / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  apply hcost.trans (hstep.trans ?_)
  have h := mul_le_mul_of_nonneg_left hunit (sq_nonneg (m : ℝ))
  nlinarith

theorem node_sum_isBigO :
    (fun m : ℕ => ∑ j : Fin m, (node m j : ℝ)) =O[Filter.atTop]
      (fun m : ℕ => (m : ℝ) ^ 2 * Real.log (m : ℝ)) := by
  let C := 16 + 17 / Real.log 2
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
  have hn : 0 ≤ ∑ j : Fin m, (node m j : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hr : 0 ≤ (m : ℝ) ^ 2 * Real.log (m : ℝ) := mul_nonneg (sq_nonneg _) hlog
  simp only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hr]
  calc
    _ ≤ C * (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1) := node_sum_bound m hmpos
    _ ≤ C * (m : ℝ) ^ 2 * (2 * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogbound (mul_nonneg hC (sq_nonneg _))
    _ = _ := by ring

def coordinate (m : ℕ) (j : Fin m) : ℝ := ((node m j : ℝ) ^ 2)⁻¹

theorem coordinate_injective (m : ℕ) (hm : 0 < m) : Function.Injective (coordinate m) := by
  intro i j he
  apply (node_strictAnti m hm).injective
  have hi : 0 < (node m i : ℝ) := by exact_mod_cast node_pos m hm i
  have hj : 0 < (node m j : ℝ) := by exact_mod_cast node_pos m hm j
  have hs : (node m i : ℝ) ^ 2 = (node m j : ℝ) ^ 2 := inv_injective he
  exact_mod_cast ((sq_eq_sq₀ hi.le hj.le).mp hs)

def weight (m : ℕ) (j : Fin m) : ℝ :=
  (Lagrange.basis Finset.univ (coordinate m) j).eval 0

theorem weight_moments (m : ℕ) (hm : 0 < m) (r : ℕ) (hr : r < m) :
    (∑ j : Fin m, weight m j / (node m j : ℝ) ^ (2 * r)) = (0 : ℝ) ^ r := by
  have hd : (Polynomial.X ^ r : Polynomial ℝ).degree < (Finset.univ : Finset (Fin m)).card := by
    rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hr
  have h := congrArg (Polynomial.eval (0 : ℝ))
    (Lagrange.eq_interpolate (coordinate_injective m hm).injOn hd)
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
  calc
    _ = ∑ j : Fin m, (coordinate m j) ^ r * weight m j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [coordinate, pow_mul, inv_pow]
      ring
    _ = _ := h.symm

theorem weight_product (m : ℕ) (hm : 0 < m) (j : Fin m) :
    weight m j = ∏ l ∈ Finset.univ.erase j,
      (node m j : ℝ) ^ 2 / ((node m j : ℝ) ^ 2 - (node m l : ℝ) ^ 2) := by
  unfold weight Lagrange.basis
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro l hl
  have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
  have hc : coordinate m j - coordinate m l ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hlj ((coordinate_injective m hm) he).symm
  have hqj : (node m j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (node_pos m hm j))
  have hql : (node m l : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (node_pos m hm l))
  have hs : (node m j : ℝ) ^ 2 - (node m l : ℝ) ^ 2 ≠ 0 := by
    intro he
    apply hc
    unfold coordinate
    rw [sub_eq_zero.mp he, sub_self]
  have hrev : -(node m j : ℝ) ^ 2 + (node m l : ℝ) ^ 2 ≠ 0 := by
    intro he
    apply hs
    linarith
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, zero_sub]
  unfold coordinate at *
  field_simp [hqj, hql, hs]
  ring_nf
  field_simp [hrev]

theorem weight_mass_lower (m : ℕ) (hm : 0 < m) : 1 ≤ ∑ j : Fin m, |weight m j| := by
  have h := weight_moments m hm 0 hm
  simp only [Nat.mul_zero, pow_zero, div_one] at h
  have he := Finset.abs_sum_le_sum_abs (f := weight m) (s := Finset.univ)
  simpa only [h, abs_one] using! he

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Papers.CommutLCHS26.MainResults
open MPFRemainder SubdivisionPolynomial GeneralMPF

variable {I : Type} [Fintype I] [DecidableEq I]

theorem coefficients (X Y : Matrix I I ℂ) (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : n < 2 * m + 1) :
    coefficient (fun j => strangRepeats X Y (node m j)) (weight m) n =
      ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n :=
  coefficients_from_scalar_moments X Y (node m) (weight m) m hm
    (node_pos m hm) (weight_moments m hm) n hn

theorem local_error (X Y : Matrix I I ℂ) (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ‖multiProduct (fun j => strangRepeats X Y (node m j)) (weight m) t -
      NormedSpace.exp (t • (X + Y))‖ ≤
      ((∑ j : Fin m, |weight m j|) + 1) *
        (Real.exp (|t| * (‖X‖ + ‖Y‖)) * (|t| * (‖X‖ + ‖Y‖)) ^ (2 * m + 1) /
          ((2 * m + 1).factorial : ℝ)) :=
  uniform_local_error_from_moments X Y (node m) (weight m) m hm
    (node_pos m hm) (weight_moments m hm) t

omit [Fintype I] [DecidableEq I] in

theorem visits_bound (X Y : Matrix I I ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ j : Fin m, ((strangRepeats X Y (node m j)).length : ℝ)) ≤
      3 * (16 + 17 / Real.log 2) * (m : ℝ) ^ 2 * Real.log ((m : ℝ) + 1) := by
  calc
    _ = 3 * ∑ j : Fin m, (node m j : ℝ) := by
      simp only [strangRepeats_length, Nat.cast_mul, Nat.cast_ofNat, Finset.mul_sum]
    _ ≤ _ := by nlinarith [node_sum_bound m hm]

end Qatlib.Papers.CommutLCHS26.MainResults.ChebyshevNodes
