/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Topology

namespace Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Complex

theorem mass_is_real (a b : ℂ)
    (hunit : a * (starRingEnd ℂ) b + (starRingEnd ℂ) a * b = 0) :
    ∃ r : ℝ, particleMass1D a b = (r : ℂ) := by
  have hre : a.re * b.re + a.im * b.im = 0 := by
    have h := congrArg Complex.re hunit
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.zero_re] at h
    ring_nf at h
    linarith
  refine ⟨(particleMass1D a b).re, ?_⟩
  apply Complex.ext
  · simp
  · show (particleMass1D a b).im = 0
    unfold particleMass1D
    have hbI_re : (b * Complex.I).re = -b.im := by simp [Complex.mul_re]
    have hbI_im : (b * Complex.I).im = b.re := by simp [Complex.mul_im]
    rw [Complex.div_im, hbI_re, hbI_im]
    have key : b.re * a.re - (-b.im) * a.im = 0 := by
      have h2 : b.re * a.re - (-b.im) * a.im = a.re * b.re + a.im * b.im := by ring
      rw [h2]; exact hre
    rw [div_sub_div_same, key, zero_div]

theorem collision2_unitary (a b : ℂ)
    (hn : Complex.normSq a + Complex.normSq b = 1)
    (hab : a * (starRingEnd ℂ) b + (starRingEnd ℂ) a * b = 0) :
    Matrix.conjTranspose (collision2 a b) * collision2 a b = 1 := by
  have hbb : (starRingEnd ℂ) b * b = (Complex.normSq b : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have haa : (starRingEnd ℂ) a * a = (Complex.normSq a : ℂ) := by
    rw [mul_comm, Complex.mul_conj]
  have hnorm_ab : (Complex.normSq a : ℂ) + (Complex.normSq b : ℂ) = 1 := by
    exact_mod_cast hn
  have hnorm_ba : (Complex.normSq b : ℂ) + (Complex.normSq a : ℂ) = 1 := by
    rw [add_comm]; exact hnorm_ab
  have hab' : (starRingEnd ℂ) b * a + (starRingEnd ℂ) a * b = 0 := by
    have h2 : (starRingEnd ℂ) b * a + (starRingEnd ℂ) a * b
        = a * (starRingEnd ℂ) b + (starRingEnd ℂ) a * b := by ring
    rw [h2]; exact hab
  have hab'' : (starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a = 0 := by
    rw [add_comm]; exact hab'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [collision2, Matrix.mul_apply, Fin.sum_univ_two,
      hbb, haa, hnorm_ab, hnorm_ba, hab', hab'']

theorem schrodingerCoeff_mass (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    schrodingerCoeff (particleMass1D a b) = dispersionCoeff a b := by
  unfold schrodingerCoeff particleMass1D dispersionCoeff
  field_simp

theorem diagonal_phase_unitary {J : Type*} [Fintype J] [DecidableEq J] (phase : J → ℂ)
    (h : ∀ i, Complex.normSq (phase i) = 1) :
    Matrix.conjTranspose (Matrix.diagonal phase) * Matrix.diagonal phase = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hfun : (fun i => (star phase) i * phase i) = (fun _ => (1 : ℂ)) := by
    funext i
    have h1 : (star phase) i * phase i = (Complex.normSq (phase i) : ℂ) := by
      rw [Pi.star_apply, show star (phase i) = (starRingEnd ℂ) (phase i) from rfl,
        ← Complex.normSq_eq_conj_mul_self]
    rw [h1]
    simp [h i]
  rw [hfun, Matrix.diagonal_one]

theorem normSq_exp_pure_imaginary (θ : ℝ) :
    Complex.normSq (Complex.exp (θ * I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem mass_and_collision_fragments (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hp : IsUnitaryPair a b) :
    (∃ r : ℝ, particleMass1D a b = (r : ℂ)) ∧
    Matrix.conjTranspose (collision2 a b) * collision2 a b = 1 ∧
    schrodingerCoeff (particleMass1D a b) = dispersionCoeff a b :=
  ⟨mass_is_real a b hp.2, collision2_unitary a b hp.1 hp.2,
    schrodingerCoeff_mass a b ha hb⟩

end Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
