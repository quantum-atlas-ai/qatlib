/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
set_option warningAsError false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def boolEval (p : MvPolynomial I ℝ) (g : I → Bool) : ℝ :=
  MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p

noncomputable def exactDegree (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ g : I → Bool, boolEval p g = if f g then (1 : ℝ) else 0})

noncomputable def approxDegree (f : (I → Bool) → Bool) : ℕ :=
  sInf ((fun p : MvPolynomial I ℝ => p.totalDegree) ''
    {p | ∀ g : I → Bool, |boolEval p g - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3})

end Qatlib.Concepts.QueryComplexity.DegreeMethod
