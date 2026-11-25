/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PolynomialFamily
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# Time derivatives of the rational Bateman powers

The fields in Eq. (6) use powers of the two rational Bateman scalars.
The common denominator stays nonzero on real space-time, so both
powers satisfy the ordinary time derivative rule everywhere.
-/

set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily

private theorem time_den_ne (x y z t : ℝ) :
    ((radialAux x y z t : ℝ) + Complex.I * (2 * t : ℝ) : ℂ) ≠ 0 := by
  intro hz
  have hRe : radialAux x y z t = 0 := by
    simpa using congrArg Complex.re hz
  have hIm : 2 * t = 0 := by
    simpa using congrArg Complex.im hz
  have ht : t = 0 := by linarith
  have hp := pair_denominator_pos x y z t
  rw [pairDenominator, hRe, ht] at hp
  norm_num at hp

/-- The time derivative of the first Bateman scalar raised to a natural power. -/
theorem alpha_time_pow (p : ℕ) (x y z t : ℝ) :
    HasDerivAt (fun s : ℝ => rationalAlpha x y z s ^ p)
      ((p : ℂ) * rationalAlpha x y z t ^ (p - 1) * deriv (rationalAlpha x y z) t) t := by
  have hd : DifferentiableAt ℝ (rationalAlpha x y z) t := by
    unfold rationalAlpha
    exact DifferentiableAt.div (by unfold radialAux; fun_prop)
      (by unfold radialAux; fun_prop) (time_den_ne x y z t)
  exact hd.hasDerivAt.fun_pow p

/-- The time derivative of the second Bateman scalar raised to a natural power. -/
theorem beta_time_pow (p : ℕ) (x y z t : ℝ) :
    HasDerivAt (fun s : ℝ => rationalBeta x y z s ^ p)
      ((p : ℂ) * rationalBeta x y z t ^ (p - 1) * deriv (rationalBeta x y z) t) t := by
  have hd : DifferentiableAt ℝ (rationalBeta x y z) t := by
    unfold rationalBeta
    exact DifferentiableAt.div (by fun_prop) (by unfold radialAux; fun_prop) (time_den_ne x y z t)
  exact hd.hasDerivAt.fun_pow p

end Qatlib.Papers.KnotLight13.TorusFamily
