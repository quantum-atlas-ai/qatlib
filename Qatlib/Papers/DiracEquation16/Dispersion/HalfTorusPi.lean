/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DiracEquation16.LieStep.NativeWalk

@[expose] public section

/-!
# The half-torus character corner

Eqs. (28)-(31) of [FillionGourdeauMacLeanLaflamme2017] discuss the fermion-doubling corners of the
first Brillouin zone. On an integer register of width `n` the corner `(π, π)` is the root character
with frequency `2 ^ (n - 1)`, and the directional streaming factors there are the spin rotations
`-1`, so the two-axis walk fixes every such character mode.

This module records the angle arithmetic `2π · 2 ^ (n-1) / 2 ^ n = π` and the resulting invariance
of the root-character modes. It complements the half-`CFL` zero-mode classification of the public
`Qatlib.Papers.DiracEquation16.Dispersion.halfbox_zero_mode_iff`, which only covers the half box.

## Main statements

* `rootChar_angle_half_torus`: the half-torus frequency has angle `π`.
* `binary_pi_mode_fixed`: the two-axis binary walk fixes the `(π, π)` character mode.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiracEquation16.Dispersion

open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.MatrixAlgebra
open Qatlib.Foundations.MatrixAlgebra.CliffordWalk
open Qatlib.Papers.DiracEquation16.LieStep
open Qatlib.Papers.DiracEquation16.SpinGates

/-- The root-character frequency `2 ^ (n - 1)` of a width-`n` binary register has angle `π`, the
half-torus value of Eqs. (28)-(31). -/
theorem rootChar_angle_half_torus (n : ℕ) (hn : 1 ≤ n) :
    RootChars.angle (2 ^ n) ((2 : ℤ) ^ (n - 1)) = Real.pi := by
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
    ring
  unfold RootChars.angle
  push_cast
  rw [hpow, div_eq_iff (by positivity)]
  ring

/-- At angle `π` every alpha rotation is minus the identity. -/
theorem rotation_alpha_pi_eq_neg_one (a : Fin 3) :
    CliffordWalk.rotation (alpha a) Real.pi = -(1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [CliffordWalk.rotation_euler_complex _ (alpha_sq a), Real.cos_pi, Real.sin_pi]
  simp

/-- Both directional streaming factors at the `(π, π)` corner fix every root-character mode of the
binary register. -/
theorem binary_pi_mode_fixed (n : ℕ) (hn : 1 ≤ n) (v : Fin 4 → ℂ) :
    (axis 1 (1 : ZMod (2 ^ n)) * axis 2 (1 : ZMod (2 ^ n))) *ᵥ
        BinaryShift.mode (RootChars.plane (2 ^ n) ((2 : ℤ) ^ (n - 1))) v =
      BinaryShift.mode (RootChars.plane (2 ^ n) ((2 : ℤ) ^ (n - 1))) v := by
  have hπ := rootChar_angle_half_torus n hn
  rw [← Matrix.mulVec_mulVec, axis_binary_mode, axis_binary_mode, hπ,
    rotation_alpha_pi_eq_neg_one, rotation_alpha_pi_eq_neg_one]
  simp [Matrix.neg_mulVec, Matrix.one_mulVec]

end Qatlib.Papers.DiracEquation16.Dispersion
