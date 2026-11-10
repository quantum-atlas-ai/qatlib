/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def ampState (lam : ℝ) : QState (Fin 2) :=
  fun i => if i = 0 then Real.sqrt (1 - lam) else Real.sqrt lam

noncomputable def targetReflection (beta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => if i = 0 then 1 else Complex.exp (Complex.I * beta)

noncomputable def stateReflection (lam alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct (ampState lam)

noncomputable def groverIterate (lam alpha beta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -(stateReflection lam alpha * targetReflection beta)

noncomputable def cheb (n : ℕ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x

noncomputable def ylcGamma (L : ℕ) (delta : ℝ) : ℝ :=
  1 / Real.cosh (Real.arcosh (1 / delta) / L)

noncomputable def ylcAlpha (L j : ℕ) (gamma : ℝ) : ℝ :=
  2 * (Real.pi / 2 - Real.arctan (Real.tan (2 * Real.pi * j / L) *
    Real.sqrt (1 - gamma ^ 2)))

noncomputable def responseProb (L : ℕ) (delta lam : ℝ) : ℝ :=
  1 - (delta * cheb L (Real.sqrt (1 - lam) / ylcGamma L delta)) ^ 2

noncomputable def ylcWordMatrix (l : ℕ) (delta lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let L := 2 * l + 1
  let gamma := ylcGamma L delta
  ((List.range l).map fun i =>
    groverIterate lam (ylcAlpha L (i + 1) gamma) (-(ylcAlpha L (l - i) gamma))).reverse.prod

noncomputable def ylcLength (lam0 delta : ℝ) : ℕ :=
  if lam0 = 1 then 1
  else 2 * Nat.ceil (Real.arcosh (1 / delta) /
      Real.arcosh (1 / Real.sqrt (1 - lam0))) + 1

def wordQueryCount (l : ℕ) : ℕ := 2 * l

def wordPreparationCount (l : ℕ) : ℕ := 2 * l

noncomputable def fullStateReflection (s : QState I) (alpha : ℝ) :
    Matrix I I ℂ :=
  1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct s

noncomputable def alignedTarget (T s : QState I) : QState I :=
  (‖Qatlib.Foundations.PureStateMath.Inner T s‖ / Qatlib.Foundations.PureStateMath.Inner T s) • T

noncomputable def fullTargetReflectionFull (t : QState I) (beta : ℝ) :
    Matrix I I ℂ :=
  1 - (1 - Complex.exp (Complex.I * beta)) • outerProduct t

noncomputable def fullWordMatrix (s t : QState I) (L : ℕ) (delta : ℝ) :
    Matrix I I ℂ :=
  let gamma := ylcGamma L delta
  ((List.range ((L - 1) / 2)).map fun i =>
    -(fullStateReflection s (ylcAlpha L (i + 1) gamma) *
      fullTargetReflectionFull t (-(ylcAlpha L (L - 1 - i) gamma)))).reverse.prod

noncomputable def fullSuccessProb (s T : QState I) (L : ℕ) (delta : ℝ) : ℝ :=
  ‖Qatlib.Foundations.PureStateMath.Inner T (fullWordMatrix s (alignedTarget T s) L delta *ᵥ s)‖ ^ 2

noncomputable def goodMass (T s : QState I) : ℝ :=
    ‖Qatlib.Foundations.PureStateMath.Inner T s‖ ^ 2

noncomputable def nestedPhase (a1 a2 : ℕ → ℝ) (l1 _l2 j : ℕ) : ℝ :=
  let L1 := 2 * l1 + 1
  let r := j % L1
  if r = 0 then a2 (j / L1)
  else if r ≤ l1 then a1 r
  else -(a1 (L1 - r))

noncomputable def nestedWordMatrix (a1 a2 : ℕ → ℝ) (l1 l2 : ℕ) (lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let l := l1 + 2 * l1 * l2 + l2
  ((List.range l).map fun i =>
    groverIterate lam (nestedPhase a1 a2 l1 l2 (i + 1))
      (-(nestedPhase a1 a2 l1 l2 (l - i)))).reverse.prod

noncomputable def conditionalOutput (T psi : QState I) : QState I :=
  (Qatlib.Foundations.PureStateMath.Inner T psi / (‖Qatlib.Foundations.PureStateMath.Inner T psi‖ : ℂ)) • T

end Qatlib.Papers.FixedPtSearch14.FixedPoint
