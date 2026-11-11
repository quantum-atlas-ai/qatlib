/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Eigenvector identities for abstract search

This module works over an arbitrary finite coordinate type to define the diagonal phase matrix
`diagM`, the marked-state update `reflM`, and their product `walkM`. The cotangent vector
`wPrime` and the vector `omega` implement the eigenvector construction used in
[AmbainisKempeRivosh2004].

Under normalization, orthogonality, and nonvanishing sine hypotheses,
`lemma13_omega_eigenvector` proves the required eigenvector equation. The theorem
`rotation_overlap` then computes an exact cosine overlap for the sum of the vectors at opposite
phases after any natural number of walk steps.

## Main statements

* `walkM_mulVec` gives the coordinate formula for a walk step.
* `inner_wPrime_cast` expresses the cotangent inner product as a real weighted sum.
* `lemma13_omega_eigenvector` establishes the eigenvector equation with phase `α`.
* `rotation_overlap` evaluates the overlap of the evolved opposite-phase sum as `2 * cos (α *
  t)`.

## References

* [Ambainis et al., 2004][AmbainisKempeRivosh2004]
-/

open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Eigen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Hermitian inner product on complex functions over the finite coordinate type,
conjugate-linear in the first argument. -/
def inner (u v : ι → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- The sum of the squared complex norms of all coordinates of `v`. -/
def normSq (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- The outer-product matrix with entries `u i * star (v j)`. -/
def rankOne (u v : ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun i j => u i * star (v j)

/-- The matrix `I - 2 * p p*`, expressed using `rankOne p p`. -/
def reflM (p : ι → ℂ) : Matrix ι ι ℂ := 1 - (2 : ℂ) • rankOne p p

/-- The diagonal matrix whose entry at coordinate `i` is `exp (I * β i)`. -/
def diagM (β : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => Complex.exp (Complex.I * (β i : ℂ))

/-- The product `diagM β * reflM ψ`, applying the marked-state update before the diagonal phase
matrix. -/
def walkM (β : ι → ℝ) (ψ : ι → ℂ) : Matrix ι ι ℂ := diagM β * reflM ψ

/-- The vector with coordinate `ψ i * cot ((α - β i) / 2)` at index `i`. -/
def wPrime (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) : ι → ℂ :=
  fun i => ψ i * (Real.cot ((α - β i) / 2) : ℂ)

/-- The vector `ψ + I • wPrime β ψ α` used in the abstract search eigenvector equation. -/
def omega (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) : ι → ℂ :=
  ψ + Complex.I • wPrime β ψ α

/-- The `i`th coordinate of `rankOne p p *ᵥ v` equals `p i * inner p v`. -/
lemma rankOne_mulVec (p v : ι → ℂ) (i : ι) :
    (rankOne p p *ᵥ v) i = p i * inner p v := by
  simp only [rankOne, Matrix.of_apply, Matrix.mulVec, dotProduct, inner]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Applying twice `rankOne p p` to `v` gives `(2 * inner p v) • p`. -/
lemma smul_two_rankOne_mulVec (p v : ι → ℂ) :
    ((2 : ℂ) • rankOne p p) *ᵥ v = (2 * inner p v) • p := by
  rw [Matrix.smul_mulVec]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, rankOne_mulVec]
  ring

/-- Applying `reflM p` to `v` subtracts `(2 * inner p v) • p` from `v`. -/
lemma reflM_mulVec (p v : ι → ℂ) :
    reflM p *ᵥ v = v - (2 * inner p v) • p := by
  rw [reflM, Matrix.sub_mulVec, Matrix.one_mulVec, smul_two_rankOne_mulVec]

/-- Applying `diagM β` multiplies coordinate `i` by `exp (I * β i)`. -/
lemma diagM_mulVec (β : ι → ℝ) (v : ι → ℂ) :
    diagM β *ᵥ v = fun i => Complex.exp (Complex.I * (β i : ℂ)) * v i := by
  funext i
  simp only [diagM, Matrix.mulVec_diagonal]

/-- Computes a walk step coordinatewise as the reflection update followed by multiplication by
`exp (I * β i)`. -/
lemma walkM_mulVec (β : ι → ℝ) (ψ v : ι → ℂ) (i : ι) :
    (walkM β ψ *ᵥ v) i
      = Complex.exp (Complex.I * (β i : ℂ)) * (v i - (2 * inner ψ v) * ψ i) := by
  rw [walkM, ← Matrix.mulVec_mulVec, reflM_mulVec, diagM_mulVec]
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]

/-- The inner product distributes over addition in its second argument. -/
lemma inner_add_right (u v w : ι → ℂ) : inner u (v + w) = inner u v + inner u w := by
  simp only [inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The inner product distributes over addition in its first argument. -/
lemma inner_add_left (u v w : ι → ℂ) : inner (u + v) w = inner u w + inner v w := by
  simp only [inner, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

/-- Scaling the second argument by a complex scalar scales the inner product by that scalar. -/
lemma inner_smul_right (u w : ι → ℂ) (c : ℂ) : inner u (c • w) = c * inner u w := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The product of a complex number with its conjugate is the complex embedding of its squared
norm. -/
lemma star_mul_self_cast (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, ← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj z

/-- The inner product of `ψ` with itself is the complex embedding of `normSq ψ`. -/
lemma inner_self_cast (ψ : ι → ℂ) : inner ψ ψ = (normSq ψ : ℂ) := by
  have hp : ∀ i, star (ψ i) * ψ i = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [mul_comm, ← Complex.normSq_eq_norm_sq]
    exact Complex.mul_conj (ψ i)
  calc inner ψ ψ = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [inner]
        exact Finset.sum_congr rfl fun i _ => hp i
    _ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring

/-- Expresses `inner ψ (wPrime β ψ α)` as the complex embedding of the real sum weighted by `‖ψ
i‖^2` and `cot ((α - β i) / 2)`. -/
lemma inner_wPrime_cast (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) :
    inner ψ (wPrime β ψ α)
      = ((∑ i, ‖ψ i‖ ^ 2 * Real.cot ((α - β i) / 2) : ℝ) : ℂ) := by
  have hp : ∀ i, star (ψ i) * (ψ i * (Real.cot ((α - β i) / 2) : ℂ))
      = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) * (Real.cot ((α - β i) / 2) : ℂ) := by
    intro i
    rw [← mul_assoc, star_mul_self_cast]
  calc inner ψ (wPrime β ψ α)
      = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) * (Real.cot ((α - β i) / 2) : ℂ) := by
        simp only [inner, wPrime]
        exact Finset.sum_congr rfl fun i _ => hp i
    _ = ((∑ i, ‖ψ i‖ ^ 2 * Real.cot ((α - β i) / 2) : ℝ) : ℂ) := by push_cast; ring

/-- Expands a coordinate of `omega β ψ α` into `ψ i` plus its imaginary cotangent correction. -/
lemma omega_apply (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) (i : ι) :
    omega β ψ α i = ψ i + Complex.I * (ψ i * (Real.cot ((α - β i) / 2) : ℂ)) := by
  simp [omega, wPrime, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- If `ψ` has self-inner-product one and is orthogonal to `wPrime β ψ α`, then `inner ψ (omega
β ψ α) = 1`. -/
lemma inner_omega (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ)
    (hnorm : inner ψ ψ = 1) (horth : inner ψ (wPrime β ψ α) = 0) :
    inner ψ (omega β ψ α) = 1 := by
  rw [omega, inner_add_right, inner_smul_right, hnorm, horth, mul_zero, add_zero]

/-- For nonzero `sin x`, relates `-1 + I * cot x` to `1 + I * cot x` by multiplication by `exp
(2 * I * x)`. -/
lemma cot_half_identity (x : ℝ) (hx : Real.sin x ≠ 0) :
    -1 + Complex.I * (Real.cot x : ℂ)
      = Complex.exp (2 * Complex.I * (x : ℂ)) * (1 + Complex.I * (Real.cot x : ℂ)) := by
  have hs : (Real.sin x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hcot : (Real.cot x : ℂ) = (Real.cos x : ℂ) / (Real.sin x : ℂ) := by
    rw [Real.cot_eq_cos_div_sin]; push_cast; ring
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsq : ((Real.cos x : ℂ)) ^ 2 + ((Real.sin x : ℂ)) ^ 2 = 1 := by
    have h : (Real.cos x) ^ 2 + (Real.sin x) ^ 2 = 1 := by
      have h2 := Real.sin_sq_add_cos_sq x
      linarith
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, h, Complex.ofReal_one]
  have hcs : ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I)
        * ((Real.sin x : ℂ) + Complex.I * (Real.cos x : ℂ)) = Complex.I := by
    linear_combination ((Real.cos x : ℂ) * (Real.sin x : ℂ)) * hI2 + Complex.I * hsq
  have hI : ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) * Complex.I
      = -(Real.sin x : ℂ) + Complex.I * (Real.cos x : ℂ) := by
    linear_combination (Real.sin x : ℂ) * hI2
  have hexp : Complex.exp (2 * Complex.I * (x : ℂ))
      = ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) ^ 2 := by
    have h1 : Complex.exp (2 * Complex.I * (x : ℂ))
        = Complex.exp ((x : ℂ) * Complex.I) * Complex.exp ((x : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have key : ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) ^ 2
        * ((Real.sin x : ℂ) + Complex.I * (Real.cos x : ℂ))
      = -(Real.sin x : ℂ) + Complex.I * (Real.cos x : ℂ) := by
    rw [sq, mul_assoc, hcs, hI]
  rw [hcot, hexp]
  refine (mul_right_cancel₀ hs) ?_
  calc (-1 + Complex.I * ((Real.cos x : ℂ) / (Real.sin x : ℂ))) * (Real.sin x : ℂ)
      = -(Real.sin x : ℂ) + Complex.I * (Real.cos x : ℂ) := by
        field_simp
    _ = ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) ^ 2
          * ((Real.sin x : ℂ) + Complex.I * (Real.cos x : ℂ)) := by rw [key]
    _ = (((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) ^ 2
          * (1 + Complex.I * ((Real.cos x : ℂ) / (Real.sin x : ℂ)))) * (Real.sin x : ℂ) := by
        field_simp

/-- For unit `ψ` orthogonal to `wPrime β ψ α`, and with all specified half-angle sines nonzero,
proves the eigenvector equation for `omega β ψ α` with eigenvalue `exp (I * α)`. This is the
algebraic construction of Lemma 13 in [AmbainisKempeRivosh2004]. -/
theorem lemma13_omega_eigenvector (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ)
    (hnorm : inner ψ ψ = 1) (horth : inner ψ (wPrime β ψ α) = 0)
    (hsin : ∀ i, Real.sin ((α - β i) / 2) ≠ 0) :
    walkM β ψ *ᵥ (omega β ψ α)
      = (Complex.exp (Complex.I * (α : ℂ))) • omega β ψ α := by
  funext i
  rw [walkM_mulVec, inner_omega β ψ α hnorm horth, omega_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hcotid := cot_half_identity ((α - β i) / 2) (hsin i)
  have hexp2 : Complex.exp (Complex.I * (β i : ℂ))
        * Complex.exp (2 * Complex.I * (((α - β i) / 2 : ℝ) : ℂ))
      = Complex.exp (Complex.I * (α : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have key : Complex.exp (Complex.I * (β i : ℂ))
        * (-1 + Complex.I * (Real.cot ((α - β i) / 2) : ℂ))
      = Complex.exp (Complex.I * (α : ℂ))
        * (1 + Complex.I * (Real.cot ((α - β i) / 2) : ℂ)) := by
    rw [hcotid, ← mul_assoc, hexp2]
  calc Complex.exp (Complex.I * (β i : ℂ))
        * (ψ i + Complex.I * (ψ i * (Real.cot ((α - β i) / 2) : ℂ)) - 2 * 1 * ψ i)
      = ψ i * (Complex.exp (Complex.I * (β i : ℂ))
          * (-1 + Complex.I * (Real.cot ((α - β i) / 2) : ℂ))) := by ring
    _ = ψ i * (Complex.exp (Complex.I * (α : ℂ))
          * (1 + Complex.I * (Real.cot ((α - β i) / 2) : ℂ))) := by rw [key]
    _ = Complex.exp (Complex.I * (α : ℂ))
          * (ψ i + Complex.I * (ψ i * (Real.cot ((α - β i) / 2) : ℂ))) := by ring

/-- An eigenvector equation for `M` implies that every natural power `M^t` acts on the same
vector by the scalar `μ^t`. -/
lemma matrix_pow_mulVec_eigen (M : Matrix ι ι ℂ) (w : ι → ℂ) (μ : ℂ)
    (h : M *ᵥ w = μ • w) : ∀ t : ℕ, (M ^ t) *ᵥ w = (μ ^ t) • w := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']

/-- The `t`th power of a complex exponential equals the exponential of `t` times its argument. -/
lemma exp_pow_eq_exp_mul (z : ℂ) (t : ℕ) : Complex.exp z ^ t = Complex.exp (t * z) :=
  (Complex.exp_nat_mul z t).symm

/-- The exponentials at opposite imaginary angles sum to the complex embedding of `2 * cos x`. -/
lemma exp_I_add_exp_neg_I (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) + Complex.exp (-(Complex.I * (x : ℂ)))
      = ((2 * Real.cos x : ℝ) : ℂ) := by
  have h2 : -(Complex.I * (x:ℂ)) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h1 : Complex.I * (x:ℂ) = (x:ℂ) * Complex.I := by ring
  rw [h2, h1, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- The `t`th powers of the exponentials at phases `α` and `-α` sum to the complex embedding of
`2 * cos (α * t)`. -/
lemma exp_sum_eq_two_cos (α : ℝ) (t : ℕ) :
    Complex.exp (Complex.I * (α : ℂ)) ^ t
      + Complex.exp (Complex.I * ((-α : ℝ) : ℂ)) ^ t
      = ((2 * Real.cos (α * t) : ℝ) : ℂ) := by
  rw [exp_pow_eq_exp_mul, exp_pow_eq_exp_mul]
  have h1 : (t : ℂ) * (Complex.I * (α : ℂ)) = Complex.I * ((α * t : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (t : ℂ) * (Complex.I * ((-α : ℝ) : ℂ))
      = -(Complex.I * ((α * t : ℝ) : ℂ)) := by push_cast; ring
  rw [h1, h2, exp_I_add_exp_neg_I]

/-- Under the normalization, orthogonality, and nonvanishing sine hypotheses at both phases, the
overlap of `ψ` with the evolved sum of the two `omega` vectors equals `2 * cos (α * t)`. -/
theorem rotation_overlap (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ)
    (hnorm : inner ψ ψ = 1)
    (horthα : inner ψ (wPrime β ψ α) = 0)
    (horthm : inner ψ (wPrime β ψ (-α)) = 0)
    (hsinα : ∀ i, Real.sin ((α - β i) / 2) ≠ 0)
    (hsinm : ∀ i, Real.sin ((-α - β i) / 2) ≠ 0) (t : ℕ) :
    inner ψ (((walkM β ψ) ^ t) *ᵥ (omega β ψ α + omega β ψ (-α)))
      = ((2 * Real.cos (α * (t : ℝ)) : ℝ) : ℂ) := by
  have hαeig := lemma13_omega_eigenvector β ψ α hnorm horthα hsinα
  have hmEig := lemma13_omega_eigenvector β ψ (-α) hnorm horthm hsinm
  have hdist : ((walkM β ψ) ^ t) *ᵥ (omega β ψ α + omega β ψ (-α))
      = ((walkM β ψ) ^ t) *ᵥ omega β ψ α + ((walkM β ψ) ^ t) *ᵥ omega β ψ (-α) :=
    Matrix.mulVec_add _ _ _
  have h1 : inner ψ (((walkM β ψ) ^ t) *ᵥ omega β ψ α)
      = Complex.exp (Complex.I * (α : ℂ)) ^ t := by
    rw [matrix_pow_mulVec_eigen (walkM β ψ) (omega β ψ α) _ hαeig t,
      inner_smul_right, inner_omega β ψ α hnorm horthα, mul_one]
  have h2 : inner ψ (((walkM β ψ) ^ t) *ᵥ omega β ψ (-α))
      = Complex.exp (Complex.I * ((-α : ℝ) : ℂ)) ^ t := by
    rw [matrix_pow_mulVec_eigen (walkM β ψ) (omega β ψ (-α)) _ hmEig t,
      inner_smul_right, inner_omega β ψ (-α) hnorm horthm, mul_one]
  rw [hdist, inner_add_right, h1, h2]
  exact exp_sum_eq_two_cos α t

end Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Eigen
