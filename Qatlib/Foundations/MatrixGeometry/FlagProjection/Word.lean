/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.FlagProjection.Defs

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.FlagProjection
variable {X : Type*} [Fintype X] [DecidableEq X]

def check8 (S : Finset X) (x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  x - (2 : ℂ) • project S x

def checkFig (S : Finset X) (x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  (2 : ℂ) • project S x - x

def hyper (t x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  x - ((2 : ℂ) * inner ℂ t x) • t

def reflect (v x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  ((2 : ℂ) * inner ℂ v x) • v - x

omit [Fintype X] in

theorem check_sign (S : Finset X) (x : EuclideanSpace ℂ X) :
    checkFig S x = -check8 S x := by
  unfold checkFig check8; module

omit [Fintype X] in

theorem project_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    project S (a • v + b • tail S v) =
      (a * (Real.sqrt (mass S v) : ℂ) + b) • tail S v := by
  rw [project_add, project_smul, project_smul, project_source S v hp, project_tail]
  module

theorem corrected_lemma6 (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    hyper (tail S v) (a • v + b • tail S v) = check8 S (a • v + b • tail S v) := by
  have hi : inner ℂ (tail S v) (a • v + b • tail S v) =
      a * (Real.sqrt (mass S v) : ℂ) + b := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, tail_inner S v hp, tail_unit S v hp]
    ring
  rw [hyper, hi, check8, project_span S v hp]
  module

theorem figure_lemma6 (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    hyper (tail S v) (a • v + b • tail S v) = -checkFig S (a • v + b • tail S v) := by
  rw [check_sign, neg_neg, corrected_lemma6 S v hp]

omit [Fintype X] in

theorem check_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    check8 S (a • v + b • tail S v) = a • v +
      (-(2 : ℂ) * a * (Real.sqrt (mass S v) : ℂ) - b) • tail S v := by
  rw [check8, project_span S v hp]
  module

theorem reflect_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (a b : ℂ) :
    reflect v (a • v + b • tail S v) =
      (a + 2 * b * (Real.sqrt (mass S v) : ℂ)) • v - b • tail S v := by
  have hi : inner ℂ v (tail S v) = (Real.sqrt (mass S v) : ℂ) := by
    rw [← inner_conj_symm, tail_inner S v hp, Complex.conj_ofReal]
  rw [reflect, inner_add_right, inner_smul_right, inner_smul_right, hu, hi]
  module

def step (S : Finset X) (v x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  reflect v (check8 S x)

def stepFig (S : Finset X) (v x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  reflect v (checkFig S x)

theorem step_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (a b : ℂ) :
    step S v (a • v + b • tail S v) =
      (a + 2 * (-(2 : ℂ) * a * (Real.sqrt (mass S v) : ℂ) - b) *
        (Real.sqrt (mass S v) : ℂ)) • v +
      (2 * a * (Real.sqrt (mass S v) : ℂ) + b) • tail S v := by
  rw [step, check_span S v hp, reflect_span S v hp hu]
  module

theorem step_smul (S : Finset X) (v x : EuclideanSpace ℂ X) (c : ℂ) :
    step S v (c • x) = c • step S v x := by
  simp only [step, check8, project_smul, reflect, inner_sub_right, inner_smul_right]
  module

theorem stepFig_sign (S : Finset X) (v x : EuclideanSpace ℂ X) :
    stepFig S v x = -step S v x := by
  rw [stepFig, check_sign, step, reflect, inner_neg_right, reflect]
  module

def run (S : Finset X) (v : EuclideanSpace ℂ X) : ℕ → EuclideanSpace ℂ X
  | 0 => v
  | n+1 => step S v (run S v n)

def runFig (S : Finset X) (v : EuclideanSpace ℂ X) : ℕ → EuclideanSpace ℂ X
  | 0 => v
  | n+1 => stepFig S v (runFig S v n)

def coeff (r : ℂ) : ℕ → ℂ × ℂ
  | 0 => (1,0)
  | n+1 => let p := coeff r n
    (p.1 + 2 * (-2 * p.1 * r - p.2) * r, 2 * p.1 * r + p.2)

theorem run_coeff (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (n : ℕ) :
    run S v n = (coeff (Real.sqrt (mass S v) : ℂ) n).1 • v +
      (coeff (Real.sqrt (mass S v) : ℂ) n).2 • tail S v := by
  induction n with
  | zero => simp [run, coeff]
  | succ n ih => rw [run, ih, step_span S v hp hu]; rfl

theorem runFig_phase (S : Finset X) (v : EuclideanSpace ℂ X) (n : ℕ) :
    runFig S v n = ((-1 : ℂ)^n) • run S v n := by
  induction n with
  | zero => simp [runFig, run]
  | succ n ih =>
    rw [runFig, ih, stepFig_sign, step_smul, run, pow_succ]
    module
omit [DecidableEq X] in

theorem reflect_inner (v x y : EuclideanSpace ℂ X) (hu : inner ℂ v v = 1) :
    inner ℂ (reflect v x) (reflect v y) = inner ℂ x y := by
  simp only [reflect, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hu, map_mul, map_ofNat, inner_conj_symm]
  ring

theorem check_norm_sq (S : Finset X) (v : EuclideanSpace ℂ X) :
    ‖check8 S v‖^2 = ‖v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖v.ofLp x - 2 * (if x ∈ S then v.ofLp x else 0)‖^2 = ‖v.ofLp x‖^2
  by_cases hx : x ∈ S
  · rw [if_pos hx]
    have he : v.ofLp x - 2 * v.ofLp x = -v.ofLp x := by ring
    rw [he, norm_neg]
  · simp [hx]

theorem run_norm_sq (S : Finset X) (v : EuclideanSpace ℂ X)
    (hu : inner ℂ v v = 1) (n : ℕ) : ‖run S v n‖^2 = ‖v‖^2 := by
  have hr (x : EuclideanSpace ℂ X) : ‖reflect v x‖^2 = ‖x‖^2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), reflect_inner v x x hu, inner_self_eq_norm_sq]
  induction n with
  | zero => rfl
  | succ n ih => rw [run, step, hr, check_norm_sq, ih]
end Qatlib.Foundations.MatrixGeometry.FlagProjection
