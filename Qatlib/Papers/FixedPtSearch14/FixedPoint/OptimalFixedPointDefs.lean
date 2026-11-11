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

/-!
# Two-level fixed-point search definitions

This module defines the amplitude state, generalized Grover reflections, analytic phase
schedule, and Chebyshev response used in the fixed-point search construction of
[YoderLowChuang2014]. `ylcLength` chooses an odd length from a good-mass lower bound and an
error parameter, while the resource functions record query and preparation counts.

Full-register reflections, overlap-based success expressions, nested phase schedules, and
conditional target vectors provide the definitions used by subsequent bounds and transport
results.

## Main definitions

* `ylcGamma` and `ylcAlpha`: width and analytic phase parameters.
* `responseProb`: the Chebyshev success-response expression.
* `ylcWordMatrix`: the two-level phase word.
* `fullWordMatrix`: a full-register reflection word.
* `nestedWordMatrix`: the word formed from a nested phase schedule.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The two-component amplitude vector with coordinates `√(1 - lam)` and `√lam`. -/
noncomputable def ampState (lam : ℝ) : QState (Fin 2) :=
  fun i => if i = 0 then Real.sqrt (1 - lam) else Real.sqrt lam

/-- The diagonal target phase rotation with diagonal entries one and `exp(i * beta)`. -/
noncomputable def targetReflection (beta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => if i = 0 then 1 else Complex.exp (Complex.I * beta)

/-- The rank-one phase update `1 - (1 - exp(-i * alpha)) • outerProduct (ampState lam)`. -/
noncomputable def stateReflection (lam alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct (ampState lam)

/-- The generalized Grover iterate given by the negative product of the source and target phase
rotations. -/
noncomputable def groverIterate (lam alpha beta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -(stateReflection lam alpha * targetReflection beta)

/-- Evaluation of the Chebyshev polynomial of the first kind of natural degree `n` at `x`. -/
noncomputable def cheb (n : ℕ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x

/-- The Yoder–Low–Chuang width parameter `1 / cosh(arcosh(1 / delta) / L)` from
[YoderLowChuang2014]. -/
noncomputable def ylcGamma (L : ℕ) (delta : ℝ) : ℝ :=
  1 / Real.cosh (Real.arcosh (1 / delta) / L)

/-- The analytic phase angle indexed by `j`, with length parameter `L` and width parameter
`gamma`, from [YoderLowChuang2014]. -/
noncomputable def ylcAlpha (L j : ℕ) (gamma : ℝ) : ℝ :=
  2 * (Real.pi / 2 - Real.arctan (Real.tan (2 * Real.pi * j / L) *
    Real.sqrt (1 - gamma ^ 2)))

/-- The Chebyshev response expression `1 - (delta * cheb L (√(1 - lam) / ylcGamma L delta)) ^ 2`
from [YoderLowChuang2014]. -/
noncomputable def responseProb (L : ℕ) (delta lam : ℝ) : ℝ :=
  1 - (delta * cheb L (Real.sqrt (1 - lam) / ylcGamma L delta)) ^ 2

/-- The reverse-ordered product of `l` generalized Grover iterates using the analytic phase
schedule of [YoderLowChuang2014]. -/
noncomputable def ylcWordMatrix (l : ℕ) (delta lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let L := 2 * l + 1
  let gamma := ylcGamma L delta
  ((List.range l).map fun i =>
    groverIterate lam (ylcAlpha L (i + 1) gamma) (-(ylcAlpha L (l - i) gamma))).reverse.prod

/-- The chosen odd length from the ceiling of the ratio of inverse hyperbolic cosines, with
length one when `lam0 = 1`. -/
noncomputable def ylcLength (lam0 delta : ℝ) : ℕ :=
  if lam0 = 1 then 1
  else 2 * Nat.ceil (Real.arcosh (1 / delta) /
      Real.arcosh (1 / Real.sqrt (1 - lam0))) + 1

/-- The query count `2 * l` assigned to a word with `l` iterates. -/
def wordQueryCount (l : ℕ) : ℕ := 2 * l

/-- The preparation-access count `2 * l` assigned to a word with `l` iterates. -/
def wordPreparationCount (l : ℕ) : ℕ := 2 * l

/-- The rank-one source phase update about a state vector `s` in an arbitrary finite register. -/
noncomputable def fullStateReflection (s : QState I) (alpha : ℝ) :
    Matrix I I ℂ :=
  1 - (1 - Complex.exp (-(Complex.I * alpha))) • outerProduct s

/-- The target vector rescaled by the overlap phase factor `‖Inner T s‖ / Inner T s`. -/
noncomputable def alignedTarget (T s : QState I) : QState I :=
  (‖Qatlib.Foundations.PureStateMath.Inner T s‖ / Qatlib.Foundations.PureStateMath.Inner T s) • T

/-- The rank-one target phase update `1 - (1 - exp(i * beta)) • outerProduct t`. -/
noncomputable def fullTargetReflectionFull (t : QState I) (beta : ℝ) :
    Matrix I I ℂ :=
  1 - (1 - Complex.exp (Complex.I * beta)) • outerProduct t

/-- The reverse-ordered product of full-register source and target phase updates with the
displayed `ylcAlpha` indices. -/
noncomputable def fullWordMatrix (s t : QState I) (L : ℕ) (delta : ℝ) :
    Matrix I I ℂ :=
  let gamma := ylcGamma L delta
  ((List.range ((L - 1) / 2)).map fun i =>
    -(fullStateReflection s (ylcAlpha L (i + 1) gamma) *
      fullTargetReflectionFull t (-(ylcAlpha L (L - 1 - i) gamma)))).reverse.prod

/-- The squared target overlap after applying `fullWordMatrix` to the source using
`alignedTarget T s`. -/
noncomputable def fullSuccessProb (s T : QState I) (L : ℕ) (delta : ℝ) : ℝ :=
  ‖Qatlib.Foundations.PureStateMath.Inner T (fullWordMatrix s (alignedTarget T s) L delta *ᵥ s)‖ ^ 2

/-- The squared modulus of the overlap between the target vector `T` and source vector `s`. -/
noncomputable def goodMass (T s : QState I) : ℝ :=
    ‖Qatlib.Foundations.PureStateMath.Inner T s‖ ^ 2

/-- The nested phase schedule that selects an outer phase at block boundaries and inner phases
with the displayed sign reversal elsewhere. -/
noncomputable def nestedPhase (a1 a2 : ℕ → ℝ) (l1 _l2 j : ℕ) : ℝ :=
  let L1 := 2 * l1 + 1
  let r := j % L1
  if r = 0 then a2 (j / L1)
  else if r ≤ l1 then a1 r
  else -(a1 (L1 - r))

/-- The two-level Grover word with `l1 + 2 * l1 * l2 + l2` iterates and the nested phase
schedule. -/
noncomputable def nestedWordMatrix (a1 a2 : ℕ → ℝ) (l1 l2 : ℕ) (lam : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let l := l1 + 2 * l1 * l2 + l2
  ((List.range l).map fun i =>
    groverIterate lam (nestedPhase a1 a2 l1 l2 (i + 1))
      (-(nestedPhase a1 a2 l1 l2 (l - i)))).reverse.prod

/-- The target vector multiplied by its overlap with `psi` divided by the modulus of that
overlap. -/
noncomputable def conditionalOutput (T psi : QState I) : QState I :=
  (Qatlib.Foundations.PureStateMath.Inner T psi / (‖Qatlib.Foundations.PureStateMath.Inner T psi‖ : ℂ)) • T

end Qatlib.Papers.FixedPtSearch14.FixedPoint
