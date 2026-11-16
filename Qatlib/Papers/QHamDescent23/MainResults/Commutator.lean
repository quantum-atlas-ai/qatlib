/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic
public import Qatlib.Papers.QHamDescent23.MainResults.Commutators

@[expose] public section


/-!
# The multiplication-position-momentum commutator

The exact differential-operator identity (B.14c), arXiv:2303.01471v1.
Both test functions are differentiable, so the identity uses the ordinary
product rule without treating the derivative of an arbitrary function formally.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Qatlib.Papers.QHamDescent23.MainResults.Commutators

namespace Qatlib.Papers.QHamDescent23.MainResults.Commutators

/-
/-- Position acts by multiplication by the real coordinate. -/
def xop (f : ℝ → ℂ) : ℝ → ℂ := (fun x : ℝ => (x : ℂ)) * f

/-- Momentum acts by minus the imaginary unit times differentiation. -/
def pop (f : ℝ → ℂ) : ℝ → ℂ := fun x => -Complex.I * deriv f x

/-- Position followed by momentum on a test function. -/
def xpop (f : ℝ → ℂ) : ℝ → ℂ := xop (pop f)

/-- Multiplication by a scalar-valued function. -/
def fop (f g : ℝ → ℂ) : ℝ → ℂ := f * g

/-- The commutator of multiplication by a differentiable function with
position times momentum is multiplication by minus the coordinate times its derivative. -/
theorem source_commutator_f_xp (f g : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Complex.I • (fop f (xpop g) - xpop (fop f g))
      = fun x : ℝ => -((x : ℂ) * deriv f x * g x) := by
  funext x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, fop, xpop, xop]
  change Complex.I * (f x * ((x : ℂ) * (-Complex.I * deriv g x)) -
    (x : ℂ) * (-Complex.I * deriv (f * g) x)) =
    -((x : ℂ) * deriv f x * g x)
  rw [deriv_mul (hf x) (hg x)]
  ring_nf
  simp [Complex.I_sq]

/-- Momentum applied twice is minus the second derivative. -/
def pop2 (f : ℝ → ℂ) : ℝ → ℂ := pop (pop f)

/-- Position applied twice multiplies by the square of the coordinate. -/
def xop2 (f : ℝ → ℂ) : ℝ → ℂ := xop (xop f)

 -/
/-- The square of momentum equals minus the iterated derivative. -/
lemma pop2_eq (f : ℝ → ℂ) : pop2 f = fun x => -deriv (deriv f) x := by
  funext x
  change -Complex.I * deriv (fun y => -Complex.I * deriv f y) x = -deriv (deriv f) x
  rw [deriv_const_mul_field]
  ring_nf
  simp [Complex.I_sq]

/-- The coordinate function has complex-valued real derivative one. -/
lemma coord_deriv (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
  convert! (Complex.ofRealCLM.hasDerivAt (x := x)) using 1

/-- Applying the product rule twice to multiplication by position. -/
lemma d2_xop (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hdf : Differentiable ℝ (deriv f)) (x : ℝ) :
    deriv (deriv (xop f)) x = 2 * deriv f x + (x : ℂ) * deriv (deriv f) x := by
  have hd : deriv (xop f) = fun y => f y + (y : ℂ) * deriv f y := by
    funext y
    change deriv ((fun z : ℝ => (z : ℂ)) * f) y = _
    simpa only [one_mul] using ((coord_deriv y).mul (hf y).hasDerivAt).deriv
  rw [hd]
  convert ((hf x).hasDerivAt.add ((coord_deriv x).mul (hdf x).hasDerivAt)).deriv using 1
  simp only [one_mul]
  ring

/-
/-- The momentum-squared and position-squared commutator on twice continuously
differentiable test functions has the canonical differential-operator form. -/
theorem source_commutator_p2_x2 (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    Complex.I • (pop2 (xop2 f) - xop2 (pop2 f))
      = (4 : ℂ) • xpop f - (2 * Complex.I) • f := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hd : deriv (xop2 f) = fun y : ℝ =>
      (2 : ℂ) * (y : ℂ) * f y + (y : ℂ) ^ 2 * deriv f y := by
    have hfun : xop2 f = (fun y : ℝ => (y : ℂ)) ^ 2 * f := by
      funext y
      simp only [xop2, xop, Pi.mul_apply, Pi.pow_apply]
      ring
    rw [hfun]
    funext y
    convert (((coord_deriv y).pow 2).mul (hfd y).hasDerivAt).deriv using 1
    norm_num [Pi.pow_apply]
  have hdd (x : ℝ) : deriv (deriv (xop2 f)) x =
      2 * f x + 4 * (x : ℂ) * deriv f x + (x : ℂ) ^ 2 * deriv (deriv f) x := by
    rw [hd]
    convert ((((coord_deriv x).const_mul 2).mul (hfd x).hasDerivAt).add
      (((coord_deriv x).pow 2).mul (hfdd x).hasDerivAt)).deriv using 1
    norm_num
    ring
  funext x
  change Complex.I * (pop2 (xop2 f) x - (x : ℂ) * ((x : ℂ) * pop2 f x)) =
    4 * ((x : ℂ) * (-Complex.I * deriv f x)) - (2 * Complex.I) * f x
  rw [pop2_eq, pop2_eq]
  dsimp only
  rw [hdd]
  ring

/-- The momentum-squared and position-momentum commutator on thrice continuously
differentiable test functions equals twice momentum squared. -/
theorem source_commutator_p2_xp (f : ℝ → ℂ) (hf : ContDiff ℝ 3 f) :
    Complex.I • (pop2 (xpop f) - xpop (pop2 f)) = (2 : ℂ) • pop2 f := by
  have hf2 : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hfd : Differentiable ℝ (deriv f) := hf2.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (deriv (deriv f)) := hf2.differentiable_deriv_two
  have hp : Differentiable ℝ (pop f) := by
    intro x
    change DifferentiableAt ℝ (fun y => -Complex.I * deriv f y) x
    exact ((hfd x).hasDerivAt.const_mul (-Complex.I)).differentiableAt
  have dpop : deriv (pop f) = fun x : ℝ => -Complex.I * deriv (deriv f) x := by
    funext x
    change deriv (fun y => -Complex.I * deriv f y) x = _
    rw [deriv_const_mul_field]
  have hdp : Differentiable ℝ (deriv (pop f)) := by
    rw [dpop]
    intro x
    exact ((hfdd x).hasDerivAt.const_mul (-Complex.I)).differentiableAt
  funext x
  change Complex.I * (pop2 (xop (pop f)) x - (x : ℂ) * pop (pop2 f) x) = 2 * pop2 f x
  rw [pop2_eq, pop2_eq]
  dsimp only
  rw [d2_xop (pop f) hp hdp x]
  rw [dpop]
  change Complex.I * (-(2 * (-Complex.I * deriv (deriv f) x) +
    (x : ℂ) * deriv (fun y : ℝ => -Complex.I * deriv (deriv f) y) x) -
    (x : ℂ) * (-Complex.I * deriv (fun y : ℝ => -deriv (deriv f) y) x)) =
      2 * -deriv (deriv f) x
  rw [deriv_const_mul_field]
  have hneg : deriv (fun y : ℝ => -deriv (deriv f) y) x = -deriv (deriv (deriv f)) x := by
    change deriv (-deriv (deriv f)) x = _
    exact (hfdd x).hasDerivAt.neg.deriv
  rw [hneg]
  ring_nf
  simp [Complex.I_sq]

 -/
end Qatlib.Papers.QHamDescent23.MainResults.Commutators
