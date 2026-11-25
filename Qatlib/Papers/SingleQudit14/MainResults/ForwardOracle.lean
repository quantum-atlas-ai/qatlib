/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Papers.SingleQudit14.MainResults.QuditFourier

@[expose] public section

/-!
# Basis oracle convention and normalized Fourier columns

The positive- and negative-cycle analysis uses pullback by an inverse
permutation. This file relates the pullback to the forward basis action
and supplies the normalization factor in Eq. (7) of arXiv:1403.5861v3.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SingleQudit14.MainResults

namespace Qatlib.Papers.SingleQudit14.MainResults

variable {d : ℕ}

/-- Pullback along a permutation sends a basis vector to the basis vector
indexed by the inverse permutation. -/
theorem applyPerm_basisVec (σ : Equiv.Perm (ZMod d)) (i : ZMod d) :
    applyPerm σ (basisVec i) = basisVec (σ.symm i) := by
  funext j
  have h : σ j = i ↔ j = σ.symm i := σ.eq_symm_apply.symm
  simp only [applyPerm, Function.comp_apply, basisVec, Pi.single_apply, h]

/-- The physical forward oracle is pullback by the inverse permutation. -/
theorem forward_oracle_basis (f : Equiv.Perm (ZMod d)) (i : ZMod d) :
    applyPerm f.symm (basisVec i) = basisVec (f i) := by
  simpa using applyPerm_basisVec f.symm i

/-- Each Fourier column in Eq. (7) has total probability one after
scaling by the inverse square root of the qudit dimension. -/
theorem qudit_fourier_col_normalized [NeZero d] (k : ZMod d) :
    Normalized (((Real.sqrt (d : ℝ))⁻¹ : ℂ) • qftVec k) := by
  classical
  unfold Normalized
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), qftVec, ZMod.stdAddChar_apply, Circle.norm_coe,
    mul_one, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne d))

end Qatlib.Papers.SingleQudit14.MainResults
