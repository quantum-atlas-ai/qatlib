/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.tacticAnalysis.introMerge false
noncomputable section

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators

noncomputable def generalizedChebyshev (y x : ℝ) : ℝ :=
  Real.cosh (y * Real.arcosh x)

noncomputable def dolphWindowScale (ε : ℝ) (n : ℕ) : ℝ :=
  generalizedChebyshev ((1 : ℝ) / n) (ε⁻¹)

noncomputable def dolphWindowPolynomial (ε : ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ε *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
      (Polynomial.C (dolphWindowScale ε n) * Polynomial.X)

def DolphFeasible (n : ℕ) (P : Polynomial ℝ) : Prop :=
  P.degree ≤ n ∧
    (∀ x : ℝ, |x| ≤ 1 → |P.eval x| ≤ 1) ∧
    P.eval 1 = 1 ∧
    P.eval (-1) = ((-1 : ℝ) ^ n)

def DolphFlatCenter (P : Polynomial ℝ) (ε lam : ℝ) : Prop :=
  ∀ x : ℝ, |x| ≤ lam → |P.eval x| ≤ ε

noncomputable def dolphWindowDegree (ε δ : ℝ) : ℕ :=
  Nat.ceil (Real.log (2 / ε) / Real.sqrt (2 * δ))

theorem chebyshev_eval_cosh (n : ℤ) (θ : ℝ) :
    (Polynomial.Chebyshev.T ℝ n).eval (Real.cosh θ) = Real.cosh (n * θ) :=
  Polynomial.Chebyshev.T_real_cosh θ n

theorem chebyshev_monoOn_one_le {n : ℤ} (hn : 0 ≤ n) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x ≤ y) :
    (Polynomial.Chebyshev.T ℝ n).eval x ≤ (Polynomial.Chebyshev.T ℝ n).eval y := by
  have hθx0 : 0 ≤ Real.arcosh x := Real.arcosh_nonneg hx
  have hθy0 : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy
  have hθxy : Real.arcosh x ≤ Real.arcosh y :=
    (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr hxy
  have hmul : (n : ℝ) * Real.arcosh x ≤ (n : ℝ) * Real.arcosh y :=
    mul_le_mul_of_nonneg_left hθxy (by exact_mod_cast hn)
  rw [← Real.cosh_arcosh hx, ← Real.cosh_arcosh hy, chebyshev_eval_cosh, chebyshev_eval_cosh]
  exact Real.cosh_strictMonoOn.le_iff_le
    (mul_nonneg (by exact_mod_cast hn) hθx0) (mul_nonneg (by exact_mod_cast hn) hθy0) |>.mpr hmul

theorem chebyshev_strictMonoOn_one_le {n : ℤ} (hn : 0 < n) {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : x < y) :
    (Polynomial.Chebyshev.T ℝ n).eval x < (Polynomial.Chebyshev.T ℝ n).eval y := by
  have hθx0 : 0 ≤ Real.arcosh x := Real.arcosh_nonneg hx
  have hθy0 : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy
  have hθxy : Real.arcosh x < Real.arcosh y :=
    (Real.arcosh_lt_arcosh (by linarith) (by linarith)).mpr hxy
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : (n : ℝ) * Real.arcosh x < (n : ℝ) * Real.arcosh y :=
    mul_lt_mul_of_pos_left hθxy hn0
  rw [← Real.cosh_arcosh hx, ← Real.cosh_arcosh hy, chebyshev_eval_cosh, chebyshev_eval_cosh]
  exact Real.cosh_strictMonoOn.lt_iff_lt
    (mul_nonneg (by exact_mod_cast (le_of_lt hn)) hθx0)
    (mul_nonneg (by exact_mod_cast (le_of_lt hn)) hθy0) |>.mpr hmul

theorem chebyshev_node_abs_le_one (n i : ℕ) : |Polynomial.Chebyshev.node n i| ≤ 1 := by
  have h := Polynomial.Chebyshev.node_mem_Icc (n := n) (i := i)
  rw [abs_le]
  exact ⟨h.1, h.2⟩

theorem chebyshev_abs_eval_neg (n : ℕ) (z : ℝ) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (-z)| =
      |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z| := by
  rw [Polynomial.Chebyshev.T_eval_neg, abs_mul]
  simp

theorem chebyshev_abs_eval_eq_abs_of_one_le (n : ℕ) {z : ℝ} (hz : 1 ≤ |z|) :
    |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z| =
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |z| := by
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]
    have hpos : 0 ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval z := by
      have h1 := Polynomial.Chebyshev.one_le_eval_T_real (n : ℤ) (x := |z|) hz
      rw [abs_of_nonneg h] at h1
      linarith
    rw [abs_of_nonneg hpos]
  · rw [abs_of_nonpos h]
    have hpos : 0 ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (-z) := by
      have h1 := Polynomial.Chebyshev.one_le_eval_T_real (n : ℤ) (x := |z|) hz
      rw [abs_of_nonpos h] at h1
      linarith
    rw [← chebyshev_abs_eval_neg n z, abs_of_nonneg hpos]

theorem chebyshev_negOnePow_eq (n : ℕ) :
    (((n : ℤ)).negOnePow : ℝ) = ((-1 : ℝ) ^ n) := by
  rw [Int.coe_negOnePow]
  simp

theorem dolphWindowScale_eval (ε : ℝ) (n : ℕ) (hn : 0 < n) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n) = ε⁻¹ := by
  have hεinv : 1 ≤ ε⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hε).mpr (by linarith)
  have hmul : (n : ℤ) * ((1 : ℝ) / n * Real.arcosh (ε⁻¹)) = Real.arcosh (ε⁻¹) := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
    push_cast
    field_simp
  rw [dolphWindowScale, generalizedChebyshev, chebyshev_eval_cosh, hmul,
    Real.cosh_arcosh hεinv]

theorem dolphWindowPolynomial_eval (ε : ℝ) (n : ℕ) (x : ℝ) :
    (dolphWindowPolynomial ε n).eval x =
      ε * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x) := by
  rw [dolphWindowPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

theorem dolphWindowScale_ge_one (ε : ℝ) (n : ℕ) (hε : 0 < ε) :
    1 ≤ dolphWindowScale ε n := by
  unfold dolphWindowScale generalizedChebyshev
  exact Real.one_le_cosh _

theorem dolphWindowPolynomial_natDegree (ε : ℝ) (n : ℕ) (hn : 0 < n) (hε : 0 < ε) :
    (dolphWindowPolynomial ε n).natDegree = n := by
  have hc : dolphWindowScale ε n ≠ 0 := by
    unfold dolphWindowScale generalizedChebyshev
    exact (Real.cosh_pos _).ne'
  have hdeg : (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree = n := by
    simpa using Polynomial.Chebyshev.natDegree_T (R := ℝ) (n : ℤ)
  have hqdeg : (Polynomial.C (dolphWindowScale ε n) * Polynomial.X).natDegree = 1 := by
    rw [Polynomial.natDegree_C_mul hc]
    simp
  have hqlead : (Polynomial.C (dolphWindowScale ε n) * Polynomial.X).leadingCoeff
      = dolphWindowScale ε n := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X]
    ring
  rw [dolphWindowPolynomial, Polynomial.natDegree_C_mul (by exact hε.ne')]
  rw [Polynomial.natDegree_comp_eq_of_mul_ne_zero]
  · simp [hdeg, hqdeg]
  · rw [Polynomial.Chebyshev.leadingCoeff_T, hqlead, hdeg]
    positivity

theorem dolphWindowPolynomial_eval_one (ε : ℝ) (n : ℕ) (hn : 0 < n) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (dolphWindowPolynomial ε n).eval 1 = 1 := by
  have hscale := dolphWindowScale_eval ε n hn hε hε1
  rw [dolphWindowPolynomial_eval, mul_one, hscale]
  exact mul_inv_cancel₀ hε.ne'

theorem dolphWindowPolynomial_eval_neg_one (ε : ℝ) (n : ℕ) (hn : 0 < n) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (dolphWindowPolynomial ε n).eval (-1) = ((-1 : ℝ) ^ n) := by
  have hscale := dolphWindowScale_eval ε n hn hε hε1
  rw [dolphWindowPolynomial_eval]
  have hneg : (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * (-1))
      = (((n : ℤ)).negOnePow : ℝ) *
        (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n) := by
    have hneg' : dolphWindowScale ε n * (-1) = -(dolphWindowScale ε n) := by ring
    rw [hneg', Polynomial.Chebyshev.T_eval_neg]
  rw [hneg, hscale, chebyshev_negOnePow_eq]
  field_simp

theorem dolphWindowPolynomial_norm_le_one (ε : ℝ) (n : ℕ) (hn : 0 < n) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (x : ℝ) (hx : |x| ≤ 1) :
    |(dolphWindowPolynomial ε n).eval x| ≤ 1 := by
  have hscale := dolphWindowScale_eval ε n hn hε hε1
  have hcpos : 0 < dolphWindowScale ε n := by
    unfold dolphWindowScale generalizedChebyshev
    exact Real.cosh_pos _
  rw [dolphWindowPolynomial_eval, abs_mul, abs_of_pos hε]
  have key : |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x)| ≤ ε⁻¹ := by
    have hzx : |dolphWindowScale ε n * x| ≤ dolphWindowScale ε n := by
      rw [abs_mul, abs_of_pos hcpos]
      calc dolphWindowScale ε n * |x| ≤ dolphWindowScale ε n * 1 := by
            exact mul_le_mul_of_nonneg_left hx (le_of_lt hcpos)
        _ = dolphWindowScale ε n := by ring
    by_cases hz : |dolphWindowScale ε n * x| ≤ 1
    · have h1 := Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hz
      have hinv : 1 ≤ ε⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hε).mpr (by linarith)
      calc |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x)| ≤ 1 := h1
        _ ≤ ε⁻¹ := hinv
    · have hz1 : 1 < |dolphWindowScale ε n * x| := lt_of_not_ge hz
      have hmono := chebyshev_monoOn_one_le (n := (n : ℤ)) (by omega) (by linarith [hz1])
        (by linarith [dolphWindowScale_ge_one ε n hε]) hzx
      have hpos : 0 ≤ (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |dolphWindowScale ε n * x| := by
        have h1 := Polynomial.Chebyshev.one_le_eval_T_real (n : ℤ)
          (x := |dolphWindowScale ε n * x|) (by linarith [hz1])
        linarith
      have habs : |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x)|
          = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval |dolphWindowScale ε n * x| :=
        chebyshev_abs_eval_eq_abs_of_one_le n (by linarith [hz1])
      rw [habs]
      exact le_trans hmono (by rw [hscale])
  calc ε * |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x)| ≤ ε * ε⁻¹ :=
        mul_le_mul_of_nonneg_left key hε.le
    _ = 1 := mul_inv_cancel₀ hε.ne'

theorem dolphWindow_flatCenter_iff (ε : ℝ) (n : ℕ) (hn : 0 < n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (lam : ℝ) (hlam0 : 0 < lam) :
    DolphFlatCenter (dolphWindowPolynomial ε n) ε lam ↔
      lam ≤ (dolphWindowScale ε n)⁻¹ := by
  have hcpos : 0 < dolphWindowScale ε n := by
    unfold dolphWindowScale generalizedChebyshev
    exact Real.cosh_pos _
  constructor
  · intro hflat
    by_contra hcon
    have hlt : (dolphWindowScale ε n)⁻¹ < lam := lt_of_not_ge hcon
    rw [inv_eq_one_div] at hlt
    set x0 := (1 / dolphWindowScale ε n + lam) / 2 with hx0def
    have hx0pos : 0 < x0 := by
      rw [hx0def]
      positivity
    have hx0mem : |x0| ≤ lam := by
      rw [abs_of_nonneg hx0pos.le]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      linarith
    have hgt : 1 < |dolphWindowScale ε n * x0| := by
      have hpos : 0 < dolphWindowScale ε n * x0 := by positivity
      rw [abs_of_pos hpos]
      have hcl : 1 < dolphWindowScale ε n * lam := by
        have h1 : (dolphWindowScale ε n)⁻¹ * dolphWindowScale ε n = 1 := by field_simp
        have := mul_lt_mul_of_pos_left hlt hcpos
        nlinarith
      rw [hx0def]
      field_simp
      nlinarith
    have hbig := Polynomial.Chebyshev.one_lt_abs_eval_T_real (n := (n : ℤ))
      (by exact_mod_cast (Nat.ne_of_gt hn)) hgt
    have hP := hflat x0 hx0mem
    rw [dolphWindowPolynomial_eval, abs_mul, abs_of_pos hε] at hP
    have hstrict : ε * |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x0)| > ε := by
      have h := mul_lt_mul_of_pos_left hbig hε
      linarith
    linarith
  · intro hlam
    intro x hx
    have hcx : |dolphWindowScale ε n * x| ≤ 1 := by
      rw [abs_mul, abs_of_pos hcpos]
      have hinv : |x| ≤ (dolphWindowScale ε n)⁻¹ := by
        calc |x| ≤ lam := hx
          _ ≤ (dolphWindowScale ε n)⁻¹ := hlam
      calc dolphWindowScale ε n * |x| ≤ dolphWindowScale ε n * (dolphWindowScale ε n)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hinv (le_of_lt hcpos)
        _ = 1 := by field_simp
    have h1 := Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hcx
    rw [dolphWindowPolynomial_eval, abs_mul, abs_of_pos hε]
    calc ε * |(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (dolphWindowScale ε n * x)| ≤ ε * 1 := by
          exact mul_le_mul_of_nonneg_left h1 hε.le
      _ = ε := by ring

end Qatlib.Concepts.QsvtCore.ApproxToolkit
