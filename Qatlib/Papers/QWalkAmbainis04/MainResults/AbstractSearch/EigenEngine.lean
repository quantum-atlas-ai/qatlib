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

open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Eigen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def inner (u v : ι → ℂ) : ℂ := ∑ i, star (u i) * v i

def normSq (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def rankOne (u v : ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun i j => u i * star (v j)

def reflM (p : ι → ℂ) : Matrix ι ι ℂ := 1 - (2 : ℂ) • rankOne p p

def diagM (β : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => Complex.exp (Complex.I * (β i : ℂ))

def walkM (β : ι → ℝ) (ψ : ι → ℂ) : Matrix ι ι ℂ := diagM β * reflM ψ

def wPrime (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) : ι → ℂ :=
  fun i => ψ i * (Real.cot ((α - β i) / 2) : ℂ)

def omega (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) : ι → ℂ :=
  ψ + Complex.I • wPrime β ψ α

lemma rankOne_mulVec (p v : ι → ℂ) (i : ι) :
    (rankOne p p *ᵥ v) i = p i * inner p v := by
  simp only [rankOne, Matrix.of_apply, Matrix.mulVec, dotProduct, inner]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma smul_two_rankOne_mulVec (p v : ι → ℂ) :
    ((2 : ℂ) • rankOne p p) *ᵥ v = (2 * inner p v) • p := by
  rw [Matrix.smul_mulVec]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, rankOne_mulVec]
  ring

lemma reflM_mulVec (p v : ι → ℂ) :
    reflM p *ᵥ v = v - (2 * inner p v) • p := by
  rw [reflM, Matrix.sub_mulVec, Matrix.one_mulVec, smul_two_rankOne_mulVec]

lemma diagM_mulVec (β : ι → ℝ) (v : ι → ℂ) :
    diagM β *ᵥ v = fun i => Complex.exp (Complex.I * (β i : ℂ)) * v i := by
  funext i
  simp only [diagM, Matrix.mulVec_diagonal]

lemma walkM_mulVec (β : ι → ℝ) (ψ v : ι → ℂ) (i : ι) :
    (walkM β ψ *ᵥ v) i
      = Complex.exp (Complex.I * (β i : ℂ)) * (v i - (2 * inner ψ v) * ψ i) := by
  rw [walkM, ← Matrix.mulVec_mulVec, reflM_mulVec, diagM_mulVec]
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]

lemma inner_add_right (u v w : ι → ℂ) : inner u (v + w) = inner u v + inner u w := by
  simp only [inner, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma inner_add_left (u v w : ι → ℂ) : inner (u + v) w = inner u w + inner v w := by
  simp only [inner, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

lemma inner_smul_right (u w : ι → ℂ) (c : ℂ) : inner u (c • w) = c * inner u w := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma star_mul_self_cast (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, ← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj z

lemma inner_self_cast (ψ : ι → ℂ) : inner ψ ψ = (normSq ψ : ℂ) := by
  have hp : ∀ i, star (ψ i) * ψ i = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [mul_comm, ← Complex.normSq_eq_norm_sq]
    exact Complex.mul_conj (ψ i)
  calc inner ψ ψ = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
        simp only [inner]
        exact Finset.sum_congr rfl fun i _ => hp i
    _ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring

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

lemma omega_apply (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ) (i : ι) :
    omega β ψ α i = ψ i + Complex.I * (ψ i * (Real.cot ((α - β i) / 2) : ℂ)) := by
  simp [omega, wPrime, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

lemma inner_omega (β : ι → ℝ) (ψ : ι → ℂ) (α : ℝ)
    (hnorm : inner ψ ψ = 1) (horth : inner ψ (wPrime β ψ α) = 0) :
    inner ψ (omega β ψ α) = 1 := by
  rw [omega, inner_add_right, inner_smul_right, hnorm, horth, mul_zero, add_zero]

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

lemma matrix_pow_mulVec_eigen (M : Matrix ι ι ℂ) (w : ι → ℂ) (μ : ℂ)
    (h : M *ᵥ w = μ • w) : ∀ t : ℕ, (M ^ t) *ᵥ w = (μ ^ t) • w := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']

lemma exp_pow_eq_exp_mul (z : ℂ) (t : ℕ) : Complex.exp z ^ t = Complex.exp (t * z) :=
  (Complex.exp_nat_mul z t).symm

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
