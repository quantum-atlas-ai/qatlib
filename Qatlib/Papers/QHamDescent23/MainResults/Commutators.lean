/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Position-Momentum Generator Commutators for Quantum Hamiltonian Descent

This module proves Lemma 2 (Equations B.14a--B.14c) of Leng, Hickman, Li, and Wu on
the canonical position (`xop`), momentum (`pop = -i ∂_x`), dilation (`xpop`), and
potential (`fop`) differential operators used in the Lyapunov analysis of Quantum
Hamiltonian Descent.

## Main statements

* `source_commutator_p2_x2`: `i [p̂², x̂²] = 4 x̂ p̂ - 2 i` on `C²` test functions.
* `source_commutator_p2_xp`: `i [p̂², x̂ p̂] = 2 p̂²` on `C³` test functions.
* `source_commutator_f_xp`: `i [f, x̂ p̂] g = -x f'(x) g(x)` on differentiable functions.

## References

* [Leng et al., 2023][LengEtAl2023QHD], Appendix B.1, Lemma 2, Eqs. (B.14a)--(B.14c), p. 22.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.Commutators

open Qatlib.Papers.QHamDescent23.MainResults

/-- Position operator `x̂`: multiplication by `x`. -/
def xop (f : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * f x

/-- Momentum operator `p̂ = -i ∂_x`. -/
def pop (f : ℝ → ℂ) : ℝ → ℂ := fun x => (-Complex.I) * deriv f x

/-- `p̂² = -∂_x²`. -/
def pop2 (f : ℝ → ℂ) : ℝ → ℂ := pop (pop f)

/-- `x̂²`: multiplication by `x²`. -/
def xop2 (f : ℝ → ℂ) : ℝ → ℂ := xop (xop f)

/-- `x̂ p̂`. -/
def xpop (f : ℝ → ℂ) : ℝ → ℂ := xop (pop f)

/-- Multiplication by a function `f`. -/
def fop (f : ℝ → ℂ) (g : ℝ → ℂ) : ℝ → ℂ := fun x => f x * g x

private theorem hasDerivAt_xop {g : ℝ → ℂ} (hg : Differentiable ℝ g) (x : ℝ) :
    HasDerivAt (xop g) (g x + (x : ℂ) * deriv g x) x := by
  simpa [xop] using! Complex.ofRealCLM.hasDerivAt.mul (hg x).hasDerivAt

private theorem differentiable_xop {g : ℝ → ℂ} (hg : Differentiable ℝ g) :
    Differentiable ℝ (xop g) :=
  fun x => (hasDerivAt_xop hg x).differentiableAt

private theorem pop_xop {g : ℝ → ℂ} (hg : Differentiable ℝ g) (x : ℝ) :
    pop (xop g) x = (-Complex.I) * g x + (x : ℂ) * pop g x := by
  unfold pop
  rw [(hasDerivAt_xop hg x).deriv]
  ring

private theorem hasDerivAt_pop_xop {g : ℝ → ℂ} (hg : Differentiable ℝ g)
    (hpg : Differentiable ℝ (pop g)) (x : ℝ) :
    HasDerivAt (pop (xop g))
      ((-Complex.I) * deriv g x + (pop g x + (x : ℂ) * deriv (pop g) x)) x := by
  have heq : pop (xop g) = fun y => (-Complex.I) * g y + xop (pop g) y :=
    funext (pop_xop hg)
  rw [heq]
  exact ((hg x).hasDerivAt.const_mul (-Complex.I)).add (hasDerivAt_xop hpg x)

private theorem pop2_xop {g : ℝ → ℂ} (hg : Differentiable ℝ g)
    (hpg : Differentiable ℝ (pop g)) (x : ℝ) :
    pop2 (xop g) x = (-2 * Complex.I) * pop g x + (x : ℂ) * pop2 g x := by
  change (-Complex.I) * deriv (pop (xop g)) x = _
  rw [(hasDerivAt_pop_xop hg hpg x).deriv]
  simp only [pop2, pop]
  ring

/-- **Equation (B.14a)**: `i [p̂², x̂²] = 4 x̂ p̂ - 2 i` on twice continuously
differentiable test functions. -/
theorem source_commutator_p2_x2 (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) :
    Complex.I • (pop2 (xop2 f) - xop2 (pop2 f))
      = (4 : ℂ) • xpop f - (2 * Complex.I) • f := by
  have hdf : Differentiable ℝ f := hf.differentiable (by decide)
  have hpf : Differentiable ℝ (pop f) :=
    hf.differentiable_deriv_two.const_mul (-Complex.I)
  have hxf : Differentiable ℝ (xop f) := differentiable_xop hdf
  have hpxf : Differentiable ℝ (pop (xop f)) :=
    fun x => (hasDerivAt_pop_xop hdf hpf x).differentiableAt
  ext x
  change Complex.I * (pop2 (xop (xop f)) x - (x : ℂ) * ((x : ℂ) * pop2 f x))
    = 4 * ((x : ℂ) * pop f x) - (2 * Complex.I) * f x
  rw [pop2_xop hxf hpxf, pop_xop hdf, pop2_xop hdf hpf]
  ring_nf
  simp [Complex.I_sq, add_comm]

/-- **Equation (B.14b)**: `i [p̂², x̂ p̂] = 2 p̂²` on thrice continuously
differentiable test functions. -/
theorem source_commutator_p2_xp (f : ℝ → ℂ) (hf : ContDiff ℝ 3 f) :
    Complex.I • (pop2 (xpop f) - xpop (pop2 f)) = (2 : ℂ) • pop2 f := by
  have hderiv : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hpf : ContDiff ℝ 2 (pop f) := contDiff_const.mul hderiv
  have hdpf : Differentiable ℝ (pop f) := hpf.differentiable (by decide)
  have hppf : Differentiable ℝ (pop (pop f)) :=
    hpf.differentiable_deriv_two.const_mul (-Complex.I)
  ext x
  change Complex.I * (pop2 (xop (pop f)) x - (x : ℂ) * pop2 (pop f) x)
    = 2 * pop2 f x
  rw [pop2_xop hdpf hppf]
  change Complex.I * ((-2 * Complex.I) * pop2 f x
    + (x : ℂ) * pop2 (pop f) x - (x : ℂ) * pop2 (pop f) x) = 2 * pop2 f x
  ring_nf
  simp [Complex.I_sq]

/-- **Equation (B.14c)**: `i [f, x̂ p̂] = -x̂ · ∇f`, i.e. multiplication by `-x f'(x)`. -/
theorem source_commutator_f_xp (f g : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    Complex.I • (fop f (xpop g) - xpop (fop f g))
      = fun (x : ℝ) => -((x : ℂ) * deriv f x * g x) := by
  ext x
  have hmul : deriv (fop f g) x = deriv f x * g x + f x * deriv g x :=
    ((hf x).hasDerivAt.mul (hg x).hasDerivAt).deriv
  change Complex.I * (f x * ((x : ℂ) * ((-Complex.I) * deriv g x))
    - (x : ℂ) * ((-Complex.I) * deriv (fop f g) x))
    = -((x : ℂ) * deriv f x * g x)
  rw [hmul]
  ring_nf
  simp [Complex.I_sq]

end Qatlib.Papers.QHamDescent23.MainResults.Commutators
