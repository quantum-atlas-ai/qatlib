/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Defs

def halfPower (q n : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ n)

@[simp] theorem halfPower_zero (q : ℕ) : halfPower q 0 = 1 := by
  simp [halfPower]

theorem halfPower_nonneg (q n : ℕ) : 0 ≤ halfPower q n := Real.sqrt_nonneg _

theorem halfPower_sq (q n : ℕ) : halfPower q n ^ 2 = (q : ℝ) ^ n :=
  Real.sq_sqrt (by positivity)

theorem halfPower_eq_sqrt_pow (q n : ℕ) :
    halfPower q n = (Real.sqrt (q : ℝ)) ^ n := by
  induction n with
  | zero => simp [halfPower]
  | succ n ih =>
      unfold halfPower
      rw [pow_succ, Real.sqrt_mul (by positivity)]
      rw [show Real.sqrt ((q : ℝ) ^ n) = (Real.sqrt (q : ℝ)) ^ n from ih]
      rw [pow_succ]

theorem halfPower_mono_exp {q : ℕ} (hq : 1 ≤ q) :
    Monotone (halfPower q) := by
  intro m n hmn
  unfold halfPower
  apply Real.sqrt_le_sqrt
  exact pow_le_pow_right₀ (by exact_mod_cast hq) hmn

structure CurveData where
  q : ℕ
  g : ℕ
  d : ℕ
  pointCount : ℕ → ℕ
  classNumber : ℕ → ℕ
  primeDivisorCount : ℕ → ℕ

def PointCountWeil (C : CurveData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((C.q : ℝ) ^ n - 2 * (C.g : ℝ) * halfPower C.q n ≤ (C.pointCount n : ℝ)) ∧
    ((C.pointCount n : ℝ) ≤ (C.q : ℝ) ^ n + 2 * (C.g : ℝ) * halfPower C.q n)

def OrbitCountIdentity (C : CurveData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (C.pointCount n : ℝ) = ∑ i ∈ n.divisors, (i : ℝ) * (C.primeDivisorCount i : ℝ)

def PluckerBound (C : CurveData) : Prop :=
  C.g ≤ (C.d - 1) * (C.d - 2) / 2

structure UniformSampler (V : Type) [Fintype V] where
  b : ℝ
  hb : 1 ≤ b
  dist : V → ℝ
  dist_nonneg : ∀ x, 0 ≤ dist x
  dist_sum : ∑ x, dist x = 1
  success : ℝ
  success_nonneg : 0 ≤ success
  success_le_one : success ≤ 1
  uniform : ∀ x y, dist x ≤ b * dist y

def IsOneUniform {V : Type} [Fintype V] (O : UniformSampler V) : Prop :=
  O.b ≤ 1

noncomputable def minProb {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

theorem minProb_le {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) (x : V) :
    minProb p ≤ p x :=
  Finset.inf'_le _ (Finset.mem_univ x)

theorem exists_minProb_eq {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) :
    ∃ x : V, minProb p = p x := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset V))
    Finset.univ_nonempty p
  exact ⟨x, hx⟩

def PolyBoundedTwo (cost : ℕ → ℕ → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ a b : ℕ, cost a b ≤ c * (a + b + 1) ^ e

def PolyBoundedThree (cost : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ a b n : ℕ, cost a b n ≤ c * (a + b + n + 1) ^ e

structure CurveDescriptor where
  q : ℕ
  g : ℕ
  d : ℕ
  logq : ℕ

structure ZetaNumeratorAlgorithm where
  output : CurveDescriptor → Polynomial ℚ
  cost : CurveDescriptor → ℕ
  successProb : CurveDescriptor → ℝ

structure ClassNumberAlgorithm where
  output : CurveDescriptor → ℕ → ℕ
  cost : CurveDescriptor → ℕ → ℕ
  successProb : CurveDescriptor → ℕ → ℝ

structure ClassGroupGeneratorAlgorithm (G : Type) [AddCommGroup G] where
  output : Finset G
  cost : ℕ → ℕ
  successProb : ℝ

theorem OrbitCountIdentity.one {C : CurveData} (h : OrbitCountIdentity C) :
    (C.pointCount 1 : ℝ) = (C.primeDivisorCount 1 : ℝ) := by
  have h1 := h 1 (le_refl 1)
  simpa [Nat.divisors_one] using h1

theorem halfPower_even (q n : ℕ) :
    halfPower q (2 * n) = (q : ℝ) ^ n := by
  unfold halfPower
  rw [mul_comm 2 n, pow_mul]
  exact Real.sqrt_sq (by positivity)

end Qatlib.Papers.ZetaCurve04.MainResults.Defs
