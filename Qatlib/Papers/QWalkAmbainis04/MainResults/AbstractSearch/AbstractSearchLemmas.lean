/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch

def inner {n : ℕ} (u v : Fin n → ℂ) : ℂ := ∑ i, star (u i) * v i

def normSq {n : ℕ} (v : Fin n → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def vnorm {n : ℕ} (v : Fin n → ℂ) : ℝ := Real.sqrt (normSq v)

def rankOne {n : ℕ} (u v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => u i * star (v j)

def reflection {n : ℕ} (p : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - (2 : ℂ) • rankOne p p

def normalize {n : ℕ} (v : Fin n → ℂ) : Fin n → ℂ :=
  fun i => v i / (vnorm v : ℂ)

def HasEig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) : Prop :=
  ∃ v : Fin n → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v

def InArc (tmin : ℝ) (μ : ℂ) : Prop :=
  ∃ θ : ℝ, -tmin < θ ∧ θ < tmin ∧ μ = Complex.exp (Complex.I * θ)

structure AbstractSearchSetup where

  n : ℕ

  m : ℕ

  U₂ : Matrix (Fin n) (Fin n) ℂ

  U₁ : Matrix (Fin n) (Fin n) ℂ

  U' : Matrix (Fin n) (Fin n) ℂ

  hU' : U' = U₂ * U₁

  ψstart : Fin n → ℂ

  ψgood : Fin n → ℂ

  hU₁ : ∀ v : Fin n → ℂ, U₁ *ᵥ v = v - (2 * inner ψgood v) • ψgood

  θ : Fin m → ℝ

  hθpos : ∀ j, 0 < θ j

  hθlt : ∀ j, θ j < Real.pi

  Φp : Fin m → Fin n → ℂ

  Φm : Fin m → Fin n → ℂ

  hΦp : ∀ j, U₂ *ᵥ Φp j = (Complex.exp (Complex.I * (θ j))) • Φp j

  hΦm : ∀ j, U₂ *ᵥ Φm j = (Complex.exp (-(Complex.I * (θ j)))) • Φm j

  a0 : ℝ

  a : Fin m → ℝ

  ha0 : a0 ≠ 0

  α : ℝ

  hαpos : 0 < α

  hαarc : ∀ j, α < θ j

  hcot : a0 ^ 2 * Real.cot (α / 2) +
      ∑ j : Fin m, (a j) ^ 2 *
        (Real.cot ((α + θ j) / 2) + Real.cot ((α - θ j) / 2)) = 0

  wα : Fin n → ℂ

  wmα : Fin n → ℂ

  hwα : U' *ᵥ wα = (Complex.exp (Complex.I * α)) • wα

  hwmα : U' *ᵥ wmα = (Complex.exp (-(Complex.I * α))) • wmα

namespace AbstractSearchSetup

variable (D : AbstractSearchSetup)

def wStartRaw : Fin D.n → ℂ :=
  fun i => ((1 / Real.sqrt 2 : ℝ) : ℂ) * D.wα i - ((1 / Real.sqrt 2 : ℝ) : ℂ) * D.wmα i

def wStart : Fin D.n → ℂ := normalize (wStartRaw D)

def wGood : Fin D.n → ℂ :=
  fun i => ((1 / Real.sqrt 2 : ℝ) : ℂ) * D.wα i + ((1 / Real.sqrt 2 : ℝ) : ℂ) * D.wmα i

def wPrime (β : ℝ) : Fin D.n → ℂ :=
  fun i => D.a0 * Real.cot (β / 2) * D.ψstart i +
    ∑ j : Fin D.m, D.a j *
      (Real.cot ((β - D.θ j) / 2) * D.Φp j i +
       Real.cot ((β + D.θ j) / 2) * D.Φm j i)

def alphaScale : ℝ :=
  1 / Real.sqrt (∑ j : Fin D.m, (D.a j) ^ 2 / (D.a0) ^ 2 *
    (1 / (1 - Real.cos (D.θ j))))

def lemma4Scale : ℝ :=
  D.α ^ 4 * (∑ j : Fin D.m, (D.a j) ^ 2 / (D.a0) ^ 2 *
    (1 / (1 - Real.cos (D.θ j)) ^ 2))

def goodScale : ℝ :=
  min (1 / Real.sqrt (∑ j : Fin D.m, (D.a j) ^ 2 *
    (Real.cot (D.θ j / 4)) ^ 2)) 1

end AbstractSearchSetup

open AbstractSearchSetup

private lemma star_eq_self_of_im_zero {z : ℂ} (h : z.im = 0) : star z = z := by
  apply Complex.ext
  · simp
  · simp [h]

private lemma inner_smul_left {n : ℕ} (u : ℂ) (Φ ψ : Fin n → ℂ) :
    inner (fun i => u * Φ i) ψ = star u * inner Φ ψ := by
  unfold inner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [star_mul]
  ring

private lemma exists_unit_phases (a : ℂ) :
    ∃ u v : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ star u * a = star v * star a ∧
      (star u * a).im = 0 := by
  by_cases ha : a = 0
  · exact ⟨1, 1, by norm_num, by norm_num, by simp [ha], by simp [ha]⟩
  · have hr : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
    have hcc : ‖((‖a‖ : ℝ) : ℂ)‖ = ‖a‖ := by simp
    refine ⟨a / (‖a‖ : ℂ), star a / (‖a‖ : ℂ), ?_, ?_, ?_, ?_⟩
    · rw [norm_div, hcc, div_self (ne_of_gt hr)]
    · rw [norm_div, norm_star, hcc, div_self (ne_of_gt hr)]
    · have hstar1 : star (a / (‖a‖ : ℂ)) = star a / (‖a‖ : ℂ) := by simp
      have hstar2 : star (star a / (‖a‖ : ℂ)) = a / (‖a‖ : ℂ) := by simp
      rw [hstar1, hstar2]
      ring
    · have hstar1 : star (a / (‖a‖ : ℂ)) = star a / (‖a‖ : ℂ) := by simp
      rw [hstar1, div_mul_eq_mul_div]
      have hns : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
        calc star a * a = a * star a := mul_comm _ _
          _ = ↑(Complex.normSq a) := Complex.mul_conj a
          _ = ↑(‖a‖ ^ 2) := by rw [Complex.normSq_eq_norm_sq]
      rw [hns]
      have hval : (((‖a‖ ^ 2 : ℝ) : ℂ) / (‖a‖ : ℂ)) = ((‖a‖ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_div]
        congr 1
        field_simp
      rw [hval]
      simp

theorem lemma2_realEqualCoefficients {n : ℕ} (Φp Φm ψ : Fin n → ℂ)
    (hconj : ∀ i, Φm i = star (Φp i)) (hψreal : ∀ i, (ψ i).im = 0) :
    ∃ u v : ℂ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
      inner (fun i => u * Φp i) ψ = inner (fun i => v * Φm i) ψ ∧
      (inner (fun i => u * Φp i) ψ).im = 0 := by

  obtain ⟨u, v, hu, hv, heq, him⟩ := exists_unit_phases (inner Φp ψ)
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · have hinnerM : inner Φm ψ = star (inner Φp ψ) := by
      unfold inner
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hconj i, star_mul, star_star, star_eq_self_of_im_zero (hψreal i)]
      ring
    rw [inner_smul_left u Φp ψ, inner_smul_left v Φm ψ, hinnerM]
    exact heq
  · rw [inner_smul_left u Φp ψ]
    exact him

end Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch
