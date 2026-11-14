/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# A fixed vector of the moving grid walk

`coin4C` is the four-dimensional Grover coin, and `movingBlock` combines it with a diagonal
phase matrix. The explicit vector `movingEig` is fixed by this block when both phase parameters
are nonzero.

The module computes its overlap with the uniform coin vector `sVec4` and bounds its squared norm
when the phase parameters have unit modulus. This development supports the analysis in
[AmbainisKempeRivosh2004].

## Main statements

* `movingBlock_eigen`: the moving block fixes `movingEig` for nonzero parameters.
* `re_inner_sVec4_movingEig`: express the real overlap through trigonometric functions.
* `normSq_movingEig_le`: bound the squared norm by 16 for unit-modulus parameters.

## References

* [Ambainis et al., 2004][AmbainisKempeRivosh2004]
-/

open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.GridWalk

/-- The four-dimensional Grover coin with diagonal entries `-1 / 2` and off-diagonal entries `1
/ 2`. -/
def coin4C : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if i = j then (-(1 : ℂ) / 2) else ((1 : ℂ) / 2)

/-- The uniform four-component coin vector, with every component equal to `1 / 2`. -/
def sVec4 : Fin 4 → ℂ := fun _ => ((1 : ℂ) / 2)

/-- The diagonal matrix with entries `a`, `a⁻¹`, `b`, and `b⁻¹`. -/
def phaseDiag (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![a, a⁻¹, b, b⁻¹]

/-- The moving-walk block obtained by multiplying `phaseDiag a b` by `coin4C`. -/
def movingBlock (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  phaseDiag a b * coin4C

/-- The explicit vector with components `a * (1 + b)`, `1 + b`, `b * (1 + a)`, and `1 + a`. -/
def movingEig (a b : ℂ) : Fin 4 → ℂ :=
  ![a * (1 + b), 1 + b, b * (1 + a), 1 + a]

/-- Each component of the Grover coin applied to `v` is half the sum of its components minus the
corresponding component of `v`. -/
lemma coin4C_mulVec (v : Fin 4 → ℂ) (i : Fin 4) :
    (coin4C *ᵥ v) i = (∑ j, v j) / 2 - v i := by
  simp only [coin4C, Matrix.mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_four]
  fin_cases i <;> simp <;> ring

/-- For nonzero `a` and `b`, the block `movingBlock a b` fixes `movingEig a b`. See
[AmbainisKempeRivosh2004]. -/
theorem movingBlock_eigen (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    movingBlock a b *ᵥ movingEig a b = movingEig a b := by

  have hsum : (∑ j, movingEig a b j) = 2 * (1 + a) * (1 + b) := by
    simp [movingEig, Fin.sum_univ_four]
    ring

  have hC0 : coin4C *ᵥ movingEig a b
      = fun k => (1 + a * b + a + b) - movingEig a b k := by
    funext k
    rw [coin4C_mulVec, hsum]
    congr 1
    ring
  funext i
  rw [movingBlock, ← Matrix.mulVec_mulVec, hC0]
  rw [phaseDiag, Matrix.mulVec_diagonal]
  have e0 : movingEig a b 0 = a * (1 + b) := by simp [movingEig]
  have e1 : movingEig a b 1 = 1 + b := by simp [movingEig]
  have e2 : movingEig a b 2 = b * (1 + a) := by simp [movingEig]
  have e3 : movingEig a b 3 = 1 + a := by simp [movingEig]
  have p0 : (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) 0 = a := by simp
  have p1 : (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) 1 = a⁻¹ := by simp
  have p2 : (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) 2 = b := by simp
  have p3 : (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) 3 = b⁻¹ := by simp
  fin_cases i
  · change (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) (0 : Fin 4) *
      (1 + a * b + a + b - movingEig a b (0 : Fin 4)) = movingEig a b (0 : Fin 4)
    rw [p0, e0]
    ring
  · change (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) (1 : Fin 4) *
      (1 + a * b + a + b - movingEig a b (1 : Fin 4)) = movingEig a b (1 : Fin 4)
    rw [p1, e1]
    have h : (1 + a * b + a + b) - (1 + b) = a * (1 + b) := by ring
    rw [h, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  · change (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) (2 : Fin 4) *
      (1 + a * b + a + b - movingEig a b (2 : Fin 4)) = movingEig a b (2 : Fin 4)
    rw [p2, e2]
    ring
  · change (![a, a⁻¹, b, b⁻¹] : Fin 4 → ℂ) (3 : Fin 4) *
      (1 + a * b + a + b - movingEig a b (3 : Fin 4)) = movingEig a b (3 : Fin 4)
    rw [p3, e3]
    have h : (1 + a * b + a + b) - (1 + a) = b * (1 + a) := by ring
    rw [h, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- The inner product of `sVec4` with `movingEig a b` equals `(1 + a) * (1 + b)`. -/
theorem inner_sVec4_movingEig (a b : ℂ) :
    (∑ i, star (sVec4 i) * movingEig a b i) = (1 + a) * (1 + b) := by
  simp [sVec4, movingEig, Fin.sum_univ_four]
  ring

/-- The complex phase `exp (φ * I)` associated with a real angle `φ`. -/
def phaseC (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))

/-- For phase parameters `φ` and `ψ`, the real part of the uniform-vector overlap is `1 + cos φ
+ cos ψ + cos (φ + ψ)`. See [AmbainisKempeRivosh2004]. -/
theorem re_inner_sVec4_movingEig (φ ψ : ℝ) :
    ((∑ i, star (sVec4 i) * movingEig (phaseC φ) (phaseC ψ) i)).re
      = 1 + Real.cos φ + Real.cos ψ + Real.cos (φ + ψ) := by
  rw [inner_sVec4_movingEig]
  have ha : phaseC φ = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
    simpa [phaseC, mul_comm] using Complex.exp_ofReal_mul_I φ
  have hb : phaseC ψ = ((Real.cos ψ : ℝ) : ℂ) + ((Real.sin ψ : ℝ) : ℂ) * Complex.I := by
    simpa [phaseC, mul_comm] using Complex.exp_ofReal_mul_I ψ
  rw [ha, hb]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]

  have hcos : Real.cos (φ + ψ) = Real.cos φ * Real.cos ψ - Real.sin φ * Real.sin ψ :=
    Real.cos_add φ ψ
  rw [hcos]
  ring

/-- When `a` and `b` have norm one, the sum of squared component norms of `movingEig a b` is at
most 16. See [AmbainisKempeRivosh2004]. -/
theorem normSq_movingEig_le (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∑ i, ‖movingEig a b i‖ ^ 2 ≤ 16 := by
  have ha1 : ‖1 + b‖ ≤ 2 := by
    calc ‖1 + b‖ ≤ ‖(1 : ℂ)‖ + ‖b‖ := norm_add_le _ _
      _ = 2 := by simp [hb]; norm_num
  have hb1 : ‖1 + a‖ ≤ 2 := by
    calc ‖1 + a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_add_le _ _
      _ = 2 := by simp [ha]; norm_num
  have h1 : ‖a * (1 + b)‖ ≤ 2 := by
    rw [norm_mul, ha]
    simpa using ha1
  have h2 : ‖1 + b‖ ≤ 2 := ha1
  have h3 : ‖b * (1 + a)‖ ≤ 2 := by
    rw [norm_mul, hb]
    simpa using hb1
  have h4 : ‖1 + a‖ ≤ 2 := hb1
  have h1sq : ‖a * (1 + b)‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg (a * (1 + b))) h1 2
    norm_num at h
    simpa [norm_mul] using h
  have h2sq : ‖1 + b‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg (1 + b)) h2 2
    norm_num at h
    exact h
  have h3sq : ‖b * (1 + a)‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg (b * (1 + a))) h3 2
    norm_num at h
    simpa [norm_mul] using h
  have h4sq : ‖1 + a‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg (1 + a)) h4 2
    norm_num at h
    exact h
  have e0 : movingEig a b 0 = a * (1 + b) := by simp [movingEig]
  have e1 : movingEig a b 1 = 1 + b := by simp [movingEig]
  have e2 : movingEig a b 2 = b * (1 + a) := by simp [movingEig]
  have e3 : movingEig a b 3 = 1 + a := by simp [movingEig]
  rw [Fin.sum_univ_four, e0, e1, e2, e3]
  linarith [h1sq, h2sq, h3sq, h4sq]

end Qatlib.Papers.QWalkAmbainis04.MainResults.GridWalk
