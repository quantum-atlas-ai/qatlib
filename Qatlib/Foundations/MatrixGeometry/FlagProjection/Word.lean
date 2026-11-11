/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.FlagProjection.Defs

/-!
# Repeated flag reflections and sign conventions

`check8` and `checkFig` define opposite sign conventions for a flag reflection, while `reflect`
gives reflection about a unit source vector. The module computes their action on the source-tail
span and represents the repeated word `run` by the complex coefficient recursion `coeff`.

`runFig_phase` shows that the alternate word differs by the global phase `(-1)^n`. The module
also proves inner-product preservation for the source reflection and norm preservation for the
check and repeated word, making the sign and normalization identities explicit for
[PaparoEtAl2014].

## Main statements

* `corrected_lemma6`: the tail hyperplane reflection agrees with the Equation (8) check on the
  source-tail span.
* `run_coeff`: every repeated word has the explicit recursive source-tail coefficients.
* `runFig_phase`: the alternate convention differs by `(-1)^n`.

## References

* [Paparo et al., 2014][PaparoEtAl2014]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.FlagProjection
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The flag check `x - 2 • project S x`, negating flagged coordinates and retaining the others. -/
def check8 (S : Finset X) (x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  x - (2 : ℂ) • project S x

/-- The opposite flag-check convention `2 • project S x - x`. -/
def checkFig (S : Finset X) (x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  (2 : ℂ) • project S x - x

/-- The map subtracting `2 * inner ℂ t x` times `t` from `x`. -/
def hyper (t x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  x - ((2 : ℂ) * inner ℂ t x) • t

/-- The map `x ↦ (2 * inner ℂ v x) • v - x`, which is reflection about the line spanned by a
unit `v`. -/
def reflect (v x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  ((2 : ℂ) * inner ℂ v x) • v - x

omit [Fintype X] in

/-- The Figure 2 flag check is the negative of the Equation (8) check, making the sign
conventions in [PaparoEtAl2014] explicit. -/
theorem check_sign (S : Finset X) (x : EuclideanSpace ℂ X) :
    checkFig S x = -check8 S x := by
  unfold checkFig check8; module

omit [Fintype X] in

/-- For positive flagged mass, projecting a source-tail span vector gives the tail scaled by `a
* sqrt (mass S v) + b`. -/
theorem project_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    project S (a • v + b • tail S v) =
      (a * (Real.sqrt (mass S v) : ℂ) + b) • tail S v := by
  rw [project_add, project_smul, project_smul, project_source S v hp, project_tail]
  module

/-- For positive flagged mass, the tail hyperplane reflection equals the Equation (8) flag check
on the source-tail span. This gives the corresponding sign identity for Lemma 6 of
[PaparoEtAl2014]. -/
theorem corrected_lemma6 (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    hyper (tail S v) (a • v + b • tail S v) = check8 S (a • v + b • tail S v) := by
  have hi : inner ℂ (tail S v) (a • v + b • tail S v) =
      a * (Real.sqrt (mass S v) : ℂ) + b := by
    rw [inner_add_right, inner_smul_right, inner_smul_right, tail_inner S v hp, tail_unit S v hp]
    ring
  rw [hyper, hi, check8, project_span S v hp]
  module

/-- For positive flagged mass, the tail hyperplane reflection equals the negative Figure 2 check
on the source-tail span, expressing the Lemma 6 sign convention of [PaparoEtAl2014]. -/
theorem figure_lemma6 (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    hyper (tail S v) (a • v + b • tail S v) = -checkFig S (a • v + b • tail S v) := by
  rw [check_sign, neg_neg, corrected_lemma6 S v hp]

omit [Fintype X] in

/-- For positive source flagged mass, the Equation (8) check retains the source coefficient and
replaces the tail coefficient by `-2 * a * sqrt (mass S v) - b`. -/
theorem check_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (a b : ℂ) :
    check8 S (a • v + b • tail S v) = a • v +
      (-(2 : ℂ) * a * (Real.sqrt (mass S v) : ℂ) - b) • tail S v := by
  rw [check8, project_span S v hp]
  module

/-- For a unit source with positive flagged mass, source reflection sends source-tail
coefficients `(a, b)` to `(a + 2 * b * sqrt (mass S v), -b)`. -/
theorem reflect_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (a b : ℂ) :
    reflect v (a • v + b • tail S v) =
      (a + 2 * b * (Real.sqrt (mass S v) : ℂ)) • v - b • tail S v := by
  have hi : inner ℂ v (tail S v) = (Real.sqrt (mass S v) : ℂ) := by
    rw [← inner_conj_symm, tail_inner S v hp, Complex.conj_ofReal]
  rw [reflect, inner_add_right, inner_smul_right, inner_smul_right, hu, hi]
  module

/-- The Equation (8) flag check followed by reflection about the source. -/
def step (S : Finset X) (v x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  reflect v (check8 S x)

/-- The Figure 2 flag check followed by reflection about the source. -/
def stepFig (S : Finset X) (v x : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  reflect v (checkFig S x)

/-- For a unit source with positive flagged mass, one reflection step stays in the source-tail
span with the displayed coefficient update. This is the finite-word recursion used in
[PaparoEtAl2014]. -/
theorem step_span (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (a b : ℂ) :
    step S v (a • v + b • tail S v) =
      (a + 2 * (-(2 : ℂ) * a * (Real.sqrt (mass S v) : ℂ) - b) *
        (Real.sqrt (mass S v) : ℂ)) • v +
      (2 * a * (Real.sqrt (mass S v) : ℂ) + b) • tail S v := by
  rw [step, check_span S v hp, reflect_span S v hp hu]
  module

/-- A reflection step commutes with complex scalar multiplication of its input. -/
theorem step_smul (S : Finset X) (v x : EuclideanSpace ℂ X) (c : ℂ) :
    step S v (c • x) = c • step S v x := by
  simp only [step, check8, project_smul, reflect, inner_sub_right, inner_smul_right]
  module

/-- The Figure 2 reflection step is the negative of the Equation (8) reflection step. -/
theorem stepFig_sign (S : Finset X) (v x : EuclideanSpace ℂ X) :
    stepFig S v x = -step S v x := by
  rw [stepFig, check_sign, step, reflect, inner_neg_right, reflect]
  module

/-- The iterated Equation (8) reflection word, starting at the source vector. -/
def run (S : Finset X) (v : EuclideanSpace ℂ X) : ℕ → EuclideanSpace ℂ X
  | 0 => v
  | n+1 => step S v (run S v n)

/-- The iterated Figure 2 reflection word, starting at the source vector. -/
def runFig (S : Finset X) (v : EuclideanSpace ℂ X) : ℕ → EuclideanSpace ℂ X
  | 0 => v
  | n+1 => stepFig S v (runFig S v n)

/-- The complex coefficient recursion starting at `(1, 0)` and applying the two-reflection
coefficient update with overlap parameter `r`. -/
def coeff (r : ℂ) : ℕ → ℂ × ℂ
  | 0 => (1,0)
  | n+1 => let p := coeff r n
    (p.1 + 2 * (-2 * p.1 * r - p.2) * r, 2 * p.1 * r + p.2)

/-- For a unit source with positive flagged mass, the iterated word is the source-tail
combination given by `coeff` at the square root of that mass. This computes the repeated
reflection word associated with [PaparoEtAl2014]. -/
theorem run_coeff (S : Finset X) (v : EuclideanSpace ℂ X) (hp : 0 < mass S v)
    (hu : inner ℂ v v = 1) (n : ℕ) :
    run S v n = (coeff (Real.sqrt (mass S v) : ℂ) n).1 • v +
      (coeff (Real.sqrt (mass S v) : ℂ) n).2 • tail S v := by
  induction n with
  | zero => simp [run, coeff]
  | succ n ih => rw [run, ih, step_span S v hp hu]; rfl

/-- After `n` iterations, the Figure 2 word equals the Equation (8) word multiplied by the
global phase `(-1)^n`, as in the sign transport for [PaparoEtAl2014]. -/
theorem runFig_phase (S : Finset X) (v : EuclideanSpace ℂ X) (n : ℕ) :
    runFig S v n = ((-1 : ℂ)^n) • run S v n := by
  induction n with
  | zero => simp [runFig, run]
  | succ n ih =>
    rw [runFig, ih, stepFig_sign, step_smul, run, pow_succ]
    module
omit [DecidableEq X] in

/-- Reflection about a unit source preserves all complex inner products, providing the
reflection normalization identity used in [PaparoEtAl2014]. -/
theorem reflect_inner (v x y : EuclideanSpace ℂ X) (hu : inner ℂ v v = 1) :
    inner ℂ (reflect v x) (reflect v y) = inner ℂ x y := by
  simp only [reflect, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hu, map_mul, map_ofNat, inner_conj_symm]
  ring

/-- The Equation (8) flag check preserves the squared Hilbert norm. -/
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

/-- For a unit source, every iterated Equation (8) reflection word has the same squared norm as
the source. -/
theorem run_norm_sq (S : Finset X) (v : EuclideanSpace ℂ X)
    (hu : inner ℂ v v = 1) (n : ℕ) : ‖run S v n‖^2 = ‖v‖^2 := by
  have hr (x : EuclideanSpace ℂ X) : ‖reflect v x‖^2 = ‖x‖^2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), reflect_inner v x x hu, inner_self_eq_norm_sq]
  induction n with
  | zero => rfl
  | succ n ih => rw [run, step, hr, check_norm_sq, ih]
end Qatlib.Foundations.MatrixGeometry.FlagProjection
