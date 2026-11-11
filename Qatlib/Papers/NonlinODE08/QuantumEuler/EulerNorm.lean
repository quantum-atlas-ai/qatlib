/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# EulerNorm — the norm behaviour of one Euler step on amplitude vectors

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: §4, equations (22)--(24).

The paper integrates `z′ = f(z)` by the Euler map `z ↦ z + h f(z)` on amplitude
vectors.  When the encoded dynamics is norm preserving in the sense
`Re ⟨z, f(z)⟩ = 0` with `‖z‖ = 1`, one Euler step is *not* exactly normalised:

  `‖z + h f(z)‖² = 1 + h² ‖f(z)‖²`,

so the raw Euler update leaves the unit sphere at order `h²`.  This module
proves that identity for finite complex amplitude vectors, deduces that the
update is strictly outside the unit sphere whenever `h ≠ 0` and `f ≠ 0`, and
shows that the renormalised update

  `z ↦ (z + h f(z)) / ‖z + h f(z)‖`

is exactly normalised.  These are exactly the amplitude-level facts that the
paper's branch construction consumes; the Euler discretisation error of the
classical flow is a separate analytic statement.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.NonlinODE08.QuantumEuler

/-- Squared Euclidean norm `∑_j |z_j|²` of a finite complex amplitude vector. -/
def sqNorm {d : ℕ} (z : Fin d → ℂ) : ℝ := ∑ j, Complex.normSq (z j)

/-- The real inner product `Re ∑_j z_j conj(f_j)`, equal to `Re ⟨z, f⟩`. -/
def reInner {d : ℕ} (z f : Fin d → ℂ) : ℝ := ∑ j, (z j * starRingEnd ℂ (f j)).re

/-- Equation (22): the pointwise Euler update `z_j ↦ z_j + h f_j(z)`. -/
def eulerStep {d : ℕ} (h : ℝ) (z f : Fin d → ℂ) : Fin d → ℂ := fun j => z j + (h : ℂ) * f j

/-- The renormalised Euler update `(z + h f)/‖z + h f‖`. -/
def normalizedEulerStep {d : ℕ} (h : ℝ) (z f : Fin d → ℂ) : Fin d → ℂ :=
  fun j => (((Real.sqrt (sqNorm (eulerStep h z f)))⁻¹ : ℝ) : ℂ) * eulerStep h z f j

/-- `sqNorm` is nonnegative. -/
theorem sqNorm_nonneg {d : ℕ} (z : Fin d → ℂ) : 0 ≤ sqNorm z :=
  Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (z j)

/-- The per-coordinate expansion of one Euler step. -/
theorem normSq_eulerStep_coord {d : ℕ} (z f : Fin d → ℂ) (h : ℝ) (j : Fin d) :
    Complex.normSq (eulerStep h z f j) =
      Complex.normSq (z j) + h ^ 2 * Complex.normSq (f j)
        + 2 * h * (z j * starRingEnd ℂ (f j)).re := by
  unfold eulerStep
  rw [Complex.normSq_add]
  have h1 : Complex.normSq ((h : ℂ) * f j) = h ^ 2 * Complex.normSq (f j) := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have hc : starRingEnd ℂ ((h : ℂ)) = (h : ℂ) := Complex.conj_ofReal h
  have h2 : (z j * starRingEnd ℂ ((h : ℂ) * f j)).re = h * (z j * starRingEnd ℂ (f j)).re := by
    rw [show starRingEnd ℂ ((h : ℂ) * f j) =
        starRingEnd ℂ ((h : ℂ)) * starRingEnd ℂ (f j) from map_mul (starRingEnd ℂ) _ _]
    rw [hc]
    rw [show z j * ((h : ℂ) * starRingEnd ℂ (f j)) =
        (h : ℂ) * (z j * starRingEnd ℂ (f j)) by ring]
    rw [Complex.mul_re]
    simp
  rw [h1, h2]
  ring

/-- Equation (23)--(24) at the level of squared norms: a Euler step on a
norm-one vector with `Re ⟨z, f⟩ = 0` has squared norm `1 + h²‖f‖²`. -/
theorem sqNorm_eulerStep {d : ℕ} (z f : Fin d → ℂ) (h : ℝ)
    (horth : reInner z f = 0) (hz : sqNorm z = 1) :
    sqNorm (eulerStep h z f) = 1 + h ^ 2 * sqNorm f := by
  unfold sqNorm
  calc
    ∑ j, Complex.normSq (eulerStep h z f j)
        = ∑ j, (Complex.normSq (z j) + h ^ 2 * Complex.normSq (f j)
            + 2 * h * (z j * starRingEnd ℂ (f j)).re) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [normSq_eulerStep_coord z f h j]
    _ = (∑ j, Complex.normSq (z j)) + h ^ 2 * (∑ j, Complex.normSq (f j))
          + 2 * h * (∑ j, (z j * starRingEnd ℂ (f j)).re) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 1 + h ^ 2 * (∑ j, Complex.normSq (f j)) := by
          rw [show (∑ j, (z j * starRingEnd ℂ (f j)).re) = reInner z f from rfl, horth]
          rw [show (∑ j, Complex.normSq (z j)) = sqNorm z from rfl, hz]
          ring

/-- The raw Euler step leaves the unit sphere whenever `h ≠ 0` and `f ≠ 0`. -/
theorem eulerStep_sqNorm_gt_one {d : ℕ} (z f : Fin d → ℂ) (h : ℝ)
    (horth : reInner z f = 0) (hz : sqNorm z = 1) (hh : h ≠ 0)
    (hf : ∃ j, f j ≠ 0) : 1 < sqNorm (eulerStep h z f) := by
  rw [sqNorm_eulerStep z f h horth hz]
  have hpos : 0 < sqNorm f := by
    obtain ⟨j, hj⟩ := hf
    apply Finset.sum_pos'
    · intro i _
      exact Complex.normSq_nonneg (f i)
    · exact ⟨j, Finset.mem_univ j, (Complex.normSq_pos.mpr hj)⟩
  have h2pos : 0 < h ^ 2 := pow_two_pos_of_ne_zero hh
  nlinarith

/-- `sqNorm` of a real multiple. -/
theorem sqNorm_smul {d : ℕ} (c : ℝ) (x : Fin d → ℂ) :
    sqNorm (fun j => ((c : ℂ)) * x j) = c ^ 2 * sqNorm x := by
  unfold sqNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- The renormalised Euler update is exactly normalised: this is the
"approximate normalized amplitude encoding" the paper feeds to the branch
construction. -/
theorem sqNorm_normalizedEulerStep {d : ℕ} (z f : Fin d → ℂ) (h : ℝ)
    (horth : reInner z f = 0) (hz : sqNorm z = 1) :
    sqNorm (normalizedEulerStep h z f) = 1 := by
  have hnonneg : (0 : ℝ) ≤ sqNorm (eulerStep h z f) := sqNorm_nonneg _
  have hpos : 0 < sqNorm (eulerStep h z f) := by
    rw [sqNorm_eulerStep z f h horth hz]
    have hnonneg' : 0 ≤ h ^ 2 * sqNorm f := mul_nonneg (sq_nonneg h) (sqNorm_nonneg f)
    linarith
  unfold normalizedEulerStep
  rw [sqNorm_smul]
  have hsq : Real.sqrt (sqNorm (eulerStep h z f)) ^ 2 = sqNorm (eulerStep h z f) :=
    Real.sq_sqrt hnonneg
  have hinv : ((Real.sqrt (sqNorm (eulerStep h z f)))⁻¹) ^ 2 =
      (sqNorm (eulerStep h z f))⁻¹ := by
    rw [inv_pow, hsq]
  rw [hinv]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

end Qatlib.Papers.NonlinODE08.QuantumEuler
