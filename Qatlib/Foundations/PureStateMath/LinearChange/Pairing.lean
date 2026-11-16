/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit

@[expose] public section


/-! # Inverse-adjoint transport for finite complex vector pairings

The span-program change-of-basis theorem uses this exact transport of target
pairings and dual input coordinates.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Foundations.PureStateMath.LinearChange

/-- The adjoint of an invertible matrix cancels the adjoint of its inverse. -/
theorem adjInvCancel {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : M.det ≠ 0) (u : I → ℂ) :
    Mᴴ *ᵥ ((M⁻¹)ᴴ *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)]
  simp

/-- Simultaneous matrix and inverse-adjoint transport preserves the actual inner product. -/
theorem invPair {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : M.det ≠ 0) (t u : I → ℂ) :
    Inner (M *ᵥ t) ((M⁻¹)ᴴ *ᵥ u) = Inner t u := by
  rw [inner_mulVec_left_rect, adjInvCancel M hM]

end Qatlib.Foundations.PureStateMath.LinearChange
