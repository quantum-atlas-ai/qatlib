/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.BlochBranch

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
open Complex

theorem exp_add_neg (x : ℝ) :
    Complex.exp (x * I) + Complex.exp (-(x * I)) = 2 * (Real.cos x : ℂ) := by
  have hx : -(x * I) = ((-x : ℝ) : ℂ) * I := by push_cast; ring
  rw [hx, Complex.exp_ofReal_mul_I (-x), Complex.exp_ofReal_mul_I x,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem exp_two_add_neg (x : ℝ) :
    Complex.exp (2 * x * I) + Complex.exp (-(2 * x) * I) =
      2 * (Real.cos (2 * x) : ℂ) := by
  have h := exp_add_neg (2 * x)
  simpa [mul_assoc] using h

theorem exp_two_mul_neg (x : ℝ) :
    Complex.exp (2 * x * I) * Complex.exp (-(2 * x) * I) = 1 := by
  rw [← Complex.exp_add]
  have h : 2 * x * I + (-(2 * x) * I) = 0 := by ring
  rw [h, Complex.exp_zero]

def traceHalf (a b : ℂ) (x : ℝ) : ℂ := b ^ 2 + a ^ 2 * (Real.cos (2 * x) : ℂ)

theorem symbolMatrix_zero (a b : ℂ) :
    symbolMatrix a b 0 = !![b ^ 2 + a ^ 2, 2 * (a * b); 2 * (a * b), b ^ 2 + a ^ 2] := by
  simp only [symbolMatrix]
  norm_num
  ring

theorem symbolMatrix_trace (a b : ℂ) (x : ℝ) :
    Matrix.trace (symbolMatrix a b x) = 2 * traceHalf a b x := by
  have h := exp_two_add_neg x
  simp only [symbolMatrix, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  unfold traceHalf
  linear_combination (a ^ 2) * h

theorem symbolMatrix_det (a b : ℂ) (x : ℝ) :
    (symbolMatrix a b x).det = (a ^ 2 - b ^ 2) ^ 2 := by
  have h3 : Complex.exp (2 * x * I) * Complex.exp (-(2 * x) * I) = 1 := exp_two_mul_neg x
  have h4 : Complex.exp (x * I) * Complex.exp (-(x * I)) = 1 := by
    rw [← Complex.exp_add]
    have : x * I + (-(x * I)) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hs : (Complex.exp (x * I) + Complex.exp (-(x * I))) ^ 2 =
      (Complex.exp (2 * x * I) + Complex.exp (-(2 * x) * I)) + 2 := by
    have e : Complex.exp (2 * x * I) = Complex.exp (x * I) * Complex.exp (x * I) := by
      rw [← Complex.exp_add]; ring_nf
    have f : Complex.exp (-(2 * x) * I) =
        Complex.exp (-(x * I)) * Complex.exp (-(x * I)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [e, f]; linear_combination (2 : ℂ) * h4
  rw [Matrix.det_fin_two]
  simp only [symbolMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linear_combination (a ^ 4) * h3 - (a ^ 2 * b ^ 2) * hs

theorem symbol_zero_eigenValue (a b : ℂ) :
    (symbolMatrix a b 0).mulVec ![1, 1] = ((a + b) ^ 2) • ![1, 1] := by
  rw [symbolMatrix_zero]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem symbol_zero_eigenValue_minus (a b : ℂ) :
    (symbolMatrix a b 0).mulVec ![1, -1] = ((a - b) ^ 2) • ![1, -1] := by
  rw [symbolMatrix_zero]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem discriminant_eq_radicand (a b : ℂ) (x : ℝ) :
    traceHalf a b x ^ 2 - (a ^ 2 - b ^ 2) ^ 2 =
      a ^ 2 * (Real.cos x : ℂ) ^ 2 * (4 * b ^ 2 + 2 * a ^ 2 * ((Real.cos (2 * x) : ℂ) - 1)) := by
  have hc : (Real.cos (2 * x) : ℂ) = 2 * (Real.cos x : ℂ) ^ 2 - 1 := by
    rw [Real.cos_two_mul]; push_cast; ring
  unfold traceHalf
  rw [hc]
  ring

theorem reducedBranch_at_zero (a b : ℂ) (hab : a + b ≠ 0) :
    (a + b) ^ 2 / (a + b) ^ 2 = 1 :=
  div_self (pow_ne_zero 2 hab)

theorem smooth_branch_derivative (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (lam : ℝ → ℂ) (l : ℂ) (hlam0 : lam 0 = (a + b) ^ 2)
    (hroot : ∀ᶠ x in nhds 0, (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2 = 0)
    (hderiv : HasDerivAt lam l 0) :
    l = 0 := by
  have hQ : HasDerivAt (fun x => traceHalf a b x) 0 0 := by
    unfold traceHalf
    have hcos : HasDerivAt (fun x : ℝ => (Real.cos (2 * x) : ℂ)) 0 0 := by
      have h1 : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) 0 0 := by
        have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
        simpa using! (Real.hasDerivAt_cos (2 * 0)).comp 0 h2
      exact h1.ofReal_comp
    have hb2 : HasDerivAt (fun _ : ℝ => b ^ 2) 0 0 := hasDerivAt_const 0 (b ^ 2)
    have h := hb2.add (hcos.const_mul (a ^ 2))
    simpa only [Pi.add_apply, zero_add, mul_zero] using! h
  have hp : HasDerivAt (fun x => (lam x) ^ 2) (2 * lam 0 * l) 0 := by
    simpa [hlam0] using! hderiv.pow 2
  have hmul : HasDerivAt (fun x => 2 * traceHalf a b x * (lam x))
      (2 * (0 * lam 0 + traceHalf a b 0 * l)) 0 := by
    have h := (hQ.const_mul 2).mul hderiv
    convert! h using 1 <;> ring
  have hc : HasDerivAt (fun _ : ℝ => (a ^ 2 - b ^ 2) ^ 2) 0 0 :=
    hasDerivAt_const 0 _
  have hg := (hp.sub hmul).add hc
  have hroot' : (fun x => (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2)
      =ᶠ[nhds 0] (fun _ => 0) := by
    filter_upwards [hroot] with x hx
    exact hx
  have hfun : (fun x => (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2)
      = ((fun x => (lam x) ^ 2) - (fun x => 2 * traceHalf a b x * (lam x))) +
        (fun _ => (a ^ 2 - b ^ 2) ^ 2) := by
    ext x; simp only [Pi.add_apply, Pi.sub_apply]
  have hderiv0 : (2 * lam 0 * l - 2 * (0 * lam 0 + traceHalf a b 0 * l)) = 0 := by
    have hd := hg.deriv
    rw [← hfun] at hd
    have hd0 : deriv (fun x => (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2) 0 = 0 := by
      rw [hroot'.deriv_eq]; simp
    rw [hd] at hd0
    simpa using hd0
  have hQ0 : traceHalf a b 0 = a ^ 2 + b ^ 2 := by
    unfold traceHalf; simp; ring
  rw [hlam0, hQ0] at hderiv0
  have hl : (4 * a * b) * l = 0 := by
    ring_nf at hderiv0 ⊢
    exact hderiv0
  have h4ab : (4 : ℂ) * a * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  exact (mul_eq_zero.mp hl).resolve_left h4ab

theorem dispersion_of_mass (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    schrodingerCoeff (particleMass1D a b) = dispersionCoeff a b :=
  schrodingerCoeff_mass a b ha hb

theorem bloch_branch_fragments (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (x : ℝ) :
    (symbolMatrix a b 0).mulVec ![1, 1] = ((a + b) ^ 2) • ![1, 1] ∧
    (symbolMatrix a b 0).mulVec ![1, -1] = ((a - b) ^ 2) • ![1, -1] ∧
    (symbolMatrix a b x).det = (a ^ 2 - b ^ 2) ^ 2 ∧
    Matrix.trace (symbolMatrix a b x) = 2 * traceHalf a b x ∧
    traceHalf a b x ^ 2 - (a ^ 2 - b ^ 2) ^ 2 =
      a ^ 2 * (Real.cos x : ℂ) ^ 2 *
        (4 * b ^ 2 + 2 * a ^ 2 * ((Real.cos (2 * x) : ℂ) - 1)) ∧
    schrodingerCoeff (particleMass1D a b) = dispersionCoeff a b :=
  ⟨symbol_zero_eigenValue a b, symbol_zero_eigenValue_minus a b,
    symbolMatrix_det a b x, symbolMatrix_trace a b x,
    discriminant_eq_radicand a b x, dispersion_of_mass a b ha hb⟩

def Q (a b : ℂ) (x : ℝ) : ℂ := traceHalf a b x

def Q1 (a : ℂ) (_b : ℂ) (x : ℝ) : ℂ := -(2 : ℂ) * a ^ 2 * (Real.sin (2 * x) : ℂ)

def Q1d (a : ℂ) (_b : ℂ) (x : ℝ) : ℂ := -(4 : ℂ) * a ^ 2 * (Real.cos (2 * x) : ℂ)

theorem Q_hasDerivAt (a b : ℂ) (x : ℝ) : HasDerivAt (Q a b) (Q1 a b x) x := by
  unfold Q Q1 traceHalf
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hcosR : HasDerivAt (fun x : ℝ => Real.cos (2 * x))
      ((-2 : ℝ) * Real.sin (2 * x)) x := by
    have h := (Real.hasDerivAt_cos (2 * x)).comp x h2
    convert! h using 1
    ring
  have hcos : HasDerivAt (fun x : ℝ => (Real.cos (2 * x) : ℂ))
      (((-2 : ℝ) * Real.sin (2 * x) : ℝ) : ℂ) x := hcosR.ofReal_comp
  have h1 : HasDerivAt (fun x : ℝ => (b ^ 2 : ℂ)) 0 x := hasDerivAt_const x (b ^ 2)
  have h := h1.add (hcos.const_mul (a ^ 2))
  convert! h using 1
  push_cast; ring

theorem Q1_hasDerivAt (a b : ℂ) (x : ℝ) : HasDerivAt (Q1 a b) (Q1d a b x) x := by
  unfold Q1 Q1d
  have h2 : HasDerivAt (fun x : ℝ => (2 : ℝ) * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
  have hsinR : HasDerivAt (fun x : ℝ => Real.sin (2 * x))
      ((2 : ℝ) * Real.cos (2 * x)) x := by
    have h := (Real.hasDerivAt_sin (2 * x)).comp x h2
    convert! h using 1
    ring
  have hsin : HasDerivAt (fun x : ℝ => (Real.sin (2 * x) : ℂ))
      (((2 : ℝ) * Real.cos (2 * x) : ℝ) : ℂ) x := hsinR.ofReal_comp
  have h := (hasDerivAt_const x (-(2 : ℂ) * a ^ 2)).mul hsin
  convert! h using 1
  push_cast; ring

theorem second_order_coefficient (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (lam : ℝ → ℂ) (l2 : ℂ)
    (hlam0 : lam 0 = (a + b) ^ 2)
    (hroot : ∀ᶠ x in nhds (0 : ℝ),
      (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2 = 0)
    (hlam : ∀ x : ℝ, HasDerivAt lam (deriv lam x) x)
    (hderiv : HasDerivAt lam 0 0)
    (hderiv2 : HasDerivAt (fun x => deriv lam x) l2 0) :
    l2 = -2 * (a / b) * (a + b) ^ 2 := by
  let g : ℝ → ℂ := fun x =>
    (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2
  let gp : ℝ → ℂ := fun x =>
    2 * (lam x * deriv lam x) - 2 * (Q1 a b x * lam x) - 2 * (Q a b x * deriv lam x)
  have hdlam0 : deriv lam 0 = 0 := hderiv.deriv
  have hQ1zero : Q1 a b 0 = 0 := by unfold Q1; simp
  have hQ0 : Q a b 0 = a ^ 2 + b ^ 2 := by unfold Q traceHalf; simp; ring
  have hQ1d0 : Q1d a b 0 = -(4 : ℂ) * a ^ 2 := by unfold Q1d; simp
  have hg_deriv : ∀ x : ℝ, HasDerivAt g (gp x) x := by
    intro x
    have hQ := Q_hasDerivAt a b x
    have hlamx := hlam x
    have h1 : HasDerivAt (fun y : ℝ => (lam y) ^ 2)
        (2 * (lam x * deriv lam x)) x := by
      have h := hlamx.pow 2
      convert! h using 1
      ring
    have h2 : HasDerivAt (fun y : ℝ => 2 * traceHalf a b y * (lam y))
        (2 * (Q1 a b x * lam x + Q a b x * deriv lam x)) x := by
      have h := (hQ.const_mul 2).mul hlamx
      convert! h using 1
      ring
    have hc : HasDerivAt (fun _ : ℝ => (a ^ 2 - b ^ 2) ^ 2) 0 x :=
      hasDerivAt_const x _
    have h := (h1.sub h2).add hc
    have hval : 2 * (lam x * deriv lam x) -
        (2 * (Q1 a b x * lam x) + 2 * (Q a b x * deriv lam x)) = gp x := by
      simp only [gp]; ring
    convert! h using 1
    rw [← hval]; ring
  have hg_zero : g =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [hroot] with x hx
    simpa only [g] using hx
  have hderiv_g_zero : deriv g =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
    simpa using hg_zero.deriv
  have hderiv2_g_zero : deriv (deriv g) 0 = 0 := by
    rw [hderiv_g_zero.deriv_eq]; simp
  have hderiv_g_eq : ∀ x : ℝ, deriv g x = gp x := fun x => (hg_deriv x).deriv
  have hgp_deriv : HasDerivAt gp
      (2 * ((a + b) ^ 2 * l2) - 2 * (Q1d a b 0 * (a + b) ^ 2) -
        2 * ((a ^ 2 + b ^ 2) * l2)) 0 := by
    have hlam0' : HasDerivAt lam (deriv lam 0) 0 := by
      rw [hdlam0]; exact hderiv
    have h1 : HasDerivAt (fun x : ℝ => lam x * deriv lam x)
        ((a + b) ^ 2 * l2) 0 := by
      have h := hlam0'.mul hderiv2
      rw [hdlam0, hlam0] at h
      simpa using! h
    have h2 : HasDerivAt (fun x : ℝ => Q1 a b x * lam x)
        (Q1d a b 0 * (a + b) ^ 2) 0 := by
      have h := (Q1_hasDerivAt a b 0).mul hlam0'
      rw [hdlam0, hlam0, hQ1zero] at h
      simpa using! h
    have h3 : HasDerivAt (fun x : ℝ => Q a b x * deriv lam x)
        ((a ^ 2 + b ^ 2) * l2) 0 := by
      have h := (Q_hasDerivAt a b 0).mul hderiv2
      rw [hdlam0, hQ1zero, hQ0] at h
      simpa using! h
    have h := ((h1.const_mul 2).sub (h2.const_mul 2)).sub (h3.const_mul 2)
    simpa [gp] using! h
  have hderiv_gp : deriv (deriv g) 0 = 2 * ((a + b) ^ 2 * l2) -
      2 * (Q1d a b 0 * (a + b) ^ 2) - 2 * ((a ^ 2 + b ^ 2) * l2) := by
    have hfun : deriv g = gp := by
      ext x; exact hderiv_g_eq x
    rw [hfun]
    exact hgp_deriv.deriv
  have hval0 : 2 * ((a + b) ^ 2 * l2) - 2 * (Q1d a b 0 * (a + b) ^ 2) -
      2 * ((a ^ 2 + b ^ 2) * l2) = 0 := by
    rw [← hderiv_gp, hderiv2_g_zero]
  rw [hQ1d0] at hval0
  have hkey : (4 : ℂ) * a * b * l2 = -8 * a ^ 2 * (a + b) ^ 2 := by
    linear_combination hval0
  have h4ab : (4 : ℂ) * a * b ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  calc
    l2 = ((4 : ℂ) * a * b * l2) / ((4 : ℂ) * a * b) := by
      field_simp [h4ab]
    _ = (-8 * a ^ 2 * (a + b) ^ 2) / ((4 : ℂ) * a * b) := by rw [hkey]
    _ = -2 * (a / b) * (a + b) ^ 2 := by
      field_simp [ha, hb]; ring

theorem smooth_branch_relative_quadratic (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (lam : ℝ → ℂ) (l2 : ℂ)
    (hlam0 : lam 0 = (a + b) ^ 2)
    (hroot : ∀ᶠ x in nhds (0 : ℝ),
      (lam x) ^ 2 - 2 * traceHalf a b x * (lam x) + (a ^ 2 - b ^ 2) ^ 2 = 0)
    (hlam : ∀ x : ℝ, HasDerivAt lam (deriv lam x) x)
    (hderiv : HasDerivAt lam 0 0)
    (hderiv2 : HasDerivAt (fun x => deriv lam x) l2 0)
    (hab : a + b ≠ 0) :
    (l2 / 2) / (a + b) ^ 2 = -(a / b) := by
  have h2 := second_order_coefficient a b ha hb lam l2 hlam0 hroot hlam hderiv hderiv2
  rw [h2]
  have hsq : (a + b) ^ 2 ≠ 0 := pow_ne_zero 2 hab
  field_simp [hb, hsq]

theorem traceHalf_zero (a b : ℂ) : traceHalf a b 0 = a ^ 2 + b ^ 2 := by
  unfold traceHalf; simp; ring

theorem discriminant_at_zero (a b : ℂ) :
    traceHalf a b 0 ^ 2 - (a ^ 2 - b ^ 2) ^ 2 = 4 * a ^ 2 * b ^ 2 := by
  rw [traceHalf_zero]; ring

theorem discriminant_at_zero_ne_zero (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    traceHalf a b 0 ^ 2 - (a ^ 2 - b ^ 2) ^ 2 ≠ 0 := by
  rw [discriminant_at_zero]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) (pow_ne_zero 2 hb)

theorem branch_simple_root (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    2 * (a + b) ^ 2 - 2 * traceHalf a b 0 ≠ 0 := by
  rw [traceHalf_zero]
  intro h
  have h4 : (4 : ℂ) * a * b = 0 := by linear_combination h
  exact (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) h4

end Qatlib.Papers.QMechSim97.MainResults.BlochBranch
