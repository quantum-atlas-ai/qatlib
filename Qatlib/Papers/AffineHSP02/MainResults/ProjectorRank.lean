/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Qatlib.Papers.AffineHSP02.HarmonicCore.GaussSums

/-!
# Phase vectors and normalized projectors

Defines the phase vectors `phaseVec` and `phaseVecInv`, their outer-product matrix `projNum`,
and the normalized matrix `proj`. The module proves that `proj` is Hermitian and idempotent with
trace one, and gives its action on vectors explicitly as a scalar multiple of the nonzero phase
vector. See [MooreEtAl2002].

## Main statements

* `proj_mul_self`: the normalized phase matrix is idempotent.
* `proj_conjTranspose`: the normalized phase matrix is Hermitian.
* `proj_mulVec`: the image of a vector is an explicit multiple of `phaseVec`.

## References

* [Moore et al., 2002][MooreEtAl2002]
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.AffineHSP02.MainResults

open HarmonicCore (qroot stdAddChar_eq_qroot_pow norm_qroot_pow)

noncomputable section

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- The standard additive character of `ZMod p`, viewed as a complex number, has norm one. -/
theorem norm_stdAddChar_coe (t : ZMod p) : ‖(ZMod.stdAddChar t : ℂ)‖ = 1 := by
  rw [stdAddChar_eq_qroot_pow p t]
  exact norm_qroot_pow p t.val

/-- Evaluating the standard additive character at `-t` gives the inverse of its value at `t`. -/
theorem stdAddChar_neg_coe (t : ZMod p) :
    (ZMod.stdAddChar (-t) : ℂ) = ((ZMod.stdAddChar t : ℂ))⁻¹ :=
  AddChar.map_neg_eq_inv (ZMod.stdAddChar (N := p)) t

/-- The complex conjugate of the standard additive character at `t` is its value at `-t`. -/
theorem conj_stdAddChar_coe (t : ZMod p) :
    (star ((ZMod.stdAddChar t : ℂ))) = (ZMod.stdAddChar (-t) : ℂ) := by
  rw [Complex.star_def, stdAddChar_neg_coe]
  exact (Complex.inv_eq_conj (norm_stdAddChar_coe t)).symm

/-- The vector whose entry at `s` is the standard additive character at `k * x s * b`. -/
def phaseVec (k b : ℕ) (x : ZMod q → ZMod p) : ZMod q → ℂ :=
  fun s => (ZMod.stdAddChar ((k : ZMod p) * x s * (b : ZMod p)) : ℂ)

/-- The vector whose entry at `s` is the standard additive character at `-(k * x s * b)`. -/
def phaseVecInv (k b : ℕ) (x : ZMod q → ZMod p) : ZMod q → ℂ :=
  fun s => (ZMod.stdAddChar (-((k : ZMod p) * x s * (b : ZMod p))) : ℂ)

/-- The matrix with entry at `(s, t)` equal to the standard additive character at `k * (x s - x
t) * b`. -/
def projNum (k b : ℕ) (x : ZMod q → ZMod p) : Matrix (ZMod q) (ZMod q) ℂ :=
  fun s t => (ZMod.stdAddChar ((k : ZMod p) * (x s - x t) * (b : ZMod p)) : ℂ)

omit [NeZero q] in

/-- Each entry of `projNum` factors as a phase-vector entry times an inverse-phase-vector entry. -/
theorem projNum_eq_mul (k b : ℕ) (x : ZMod q → ZMod p) (s t : ZMod q) :
    projNum k b x s t = phaseVec k b x s * phaseVecInv k b x t := by
  unfold projNum phaseVec phaseVecInv
  have h : (k : ZMod p) * (x s - x t) * (b : ZMod p)
      = (k : ZMod p) * x s * (b : ZMod p)
        + (-((k : ZMod p) * x t * (b : ZMod p))) := by ring
  rw [h, AddChar.map_add_eq_mul]

/-- The square of `projNum` equals `q` times `projNum`. -/
theorem projNum_mul_self (k b : ℕ) (x : ZMod q → ZMod p) :
    projNum k b x * projNum k b x = (q : ℂ) • projNum k b x := by
  ext s t
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm : ∀ r : ZMod q,
      projNum k b x s r * projNum k b x r t
        = (ZMod.stdAddChar ((k : ZMod p) * (x s - x t) * (b : ZMod p)) : ℂ) := by
    intro r
    unfold projNum
    have h : (k : ZMod p) * (x s - x r) * (b : ZMod p)
        + (k : ZMod p) * (x r - x t) * (b : ZMod p)
        = (k : ZMod p) * (x s - x t) * (b : ZMod p) := by ring
    rw [← h, AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]
  rfl

/-- The phase matrix `projNum` normalized by the complex inverse of `q`. -/
def proj (k b : ℕ) (x : ZMod q → ZMod p) : Matrix (ZMod q) (ZMod q) ℂ :=
  ((q : ℂ)⁻¹) • projNum k b x

/-- The normalized phase matrix `proj` is idempotent. -/
theorem proj_mul_self (k b : ℕ) (x : ZMod q → ZMod p) :
    proj k b x * proj k b x = proj k b x := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  unfold proj
  rw [Matrix.smul_mul, Matrix.mul_smul, projNum_mul_self, smul_smul, smul_smul]
  congr 1
  field_simp

omit [NeZero q] in

/-- Every diagonal entry of `projNum` is one. -/
theorem projNum_diag (k b : ℕ) (x : ZMod q → ZMod p) (s : ZMod q) :
    Matrix.diag (projNum k b x) s = 1 := by
  change (ZMod.stdAddChar ((k : ZMod p) * (x s - x s) * (b : ZMod p)) : ℂ) = 1
  have h : (k : ZMod p) * (x s - x s) * (b : ZMod p) = 0 := by ring
  rw [h, AddChar.map_zero_eq_one]

/-- The normalized phase matrix `proj` has trace one. -/
theorem proj_trace (k b : ℕ) (x : ZMod q → ZMod p) :
    Matrix.trace (proj k b x) = 1 := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  unfold proj
  rw [Matrix.trace_smul]
  have hN : Matrix.trace (projNum k b x) = (q : ℂ) := by
    rw [Matrix.trace]
    rw [Finset.sum_congr rfl (fun s _ => projNum_diag k b x s),
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  rw [hN]
  simp only [smul_eq_mul]
  exact inv_mul_cancel₀ hq

omit [NeZero q] in

/-- The normalized phase matrix `proj` equals its conjugate transpose. -/
theorem proj_conjTranspose (k b : ℕ) (x : ZMod q → ZMod p) :
    Matrix.conjTranspose (proj k b x) = proj k b x := by
  ext s t
  rw [Matrix.conjTranspose_apply]
  unfold proj
  simp only [Matrix.smul_apply, smul_eq_mul, projNum]
  rw [star_mul, conj_stdAddChar_coe]
  have hstarq : star ((q : ℂ)⁻¹) = (q : ℂ)⁻¹ := by
    rw [Complex.star_def]
    norm_num
  rw [hstarq]
  have harg : -((k : ZMod p) * (x t - x s) * (b : ZMod p))
      = (k : ZMod p) * (x s - x t) * (b : ZMod p) := by ring
  rw [harg, mul_comm]

/-- Multiplying `projNum` by `v` gives `phaseVec` scaled by the sum of the inverse phases times
the coordinates of `v`. -/
theorem projNum_mulVec (k b : ℕ) (x : ZMod q → ZMod p) (v : ZMod q → ℂ) :
    (projNum k b x).mulVec v
      = (∑ t, phaseVecInv k b x t * v t) • phaseVec k b x := by
  ext s
  rw [Matrix.mulVec, dotProduct]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [projNum_eq_mul]
  ring

/-- Multiplying `proj` by `v` gives `phaseVec` scaled by `q⁻¹` times the sum of the inverse
phases times the coordinates of `v`. -/
theorem proj_mulVec (k b : ℕ) (x : ZMod q → ZMod p) (v : ZMod q → ℂ) :
    (proj k b x).mulVec v
      = (((q : ℂ)⁻¹ * ∑ t, phaseVecInv k b x t * v t)) • phaseVec k b x := by
  unfold proj
  rw [Matrix.smul_mulVec, projNum_mulVec, smul_smul]

omit [NeZero q] in

/-- The phase vector `phaseVec k b x` is nonzero. -/
theorem phaseVec_ne_zero (k b : ℕ) (x : ZMod q → ZMod p) :
    phaseVec k b x ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  unfold phaseVec at h0
  have h1 := norm_stdAddChar_coe ((k : ZMod p) * x 0 * (b : ZMod p))
  rw [h0] at h1
  norm_num at h1

/-- The orbit map sending a residue `s` modulo `q` to `a^s.val * j` modulo `p`. -/
def multOrbit (p q : ℕ) (a : (ZMod p)ˣ) (j : ZMod p) : ZMod q → ZMod p :=
  fun s => ((a : ZMod p) ^ s.val) * j

end

end Qatlib.Papers.AffineHSP02.MainResults
