/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan, Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Derivatives of polynomial cosine compositions

This module records the chain rule for a real polynomial evaluated at cosine. The formulas
`hasDerivAt_cosComp` and `deriv_cosComp` supply derivative identities used in Bernstein–Szegő
estimates and the approximation infrastructure associated with [WangEtAl2026].

## Main statements

* `hasDerivAt_cosComp`: Give the derivative witness for a cosine composition.
* `deriv_cosComp`: Evaluate its derivative.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

namespace Qatlib.Foundations.CbmdAnalysis.Approximation

section

open Real Polynomial

namespace Causalean.Mathlib.Analysis.BernsteinSzegoTrig

/-- The composition of a real polynomial with cosine has derivative equal to the polynomial
derivative at cosine times minus sine. -/
theorem hasDerivAt_cosComp (R : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (fun s => R.eval (Real.cos s))
      (R.derivative.eval (Real.cos t) * (-Real.sin t)) t := by
  have h1 : HasDerivAt (fun x => Polynomial.eval x R)
      (R.derivative.eval (Real.cos t)) (Real.cos t) := R.hasDerivAt (Real.cos t)
  have h2 : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
  exact h1.comp t h2

/-- The derivative of a real polynomial evaluated at cosine is its polynomial derivative
evaluated at cosine times minus sine. -/
theorem deriv_cosComp (R : Polynomial ℝ) (t : ℝ) :
    deriv (fun s => R.eval (Real.cos s)) t
      = R.derivative.eval (Real.cos t) * (-Real.sin t) :=
  (hasDerivAt_cosComp R t).deriv

end Causalean.Mathlib.Analysis.BernsteinSzegoTrig

end
end Qatlib.Foundations.CbmdAnalysis.Approximation
