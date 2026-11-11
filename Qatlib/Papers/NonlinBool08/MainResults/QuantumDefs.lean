/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.BentFacts

/-!
# Amplitude semantics for Boolean oracle circuits

Defines complex amplitude functions, phase oracles, and a Walsh-Hadamard transform with
normalization `hnorm`. For even dimension the transform is involutive; gate lists `Program`
carry evaluation semantics and an explicit oracle count. See [Roetteler2008].

## Main statements

* `hadamard_hadamard`: the transform is involutive in even dimension.
* `Program.eval`: programs evaluate their gates in list order.
* `Program.oracleCount`: the resource count is the number of phase-oracle gates.

## References

* [Roetteler, 2008][Roetteler2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.QuantumDefs

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

/-- Complex amplitude functions on the binary vector space of length `n`. -/
abbrev State (n : ℕ) : Type := BVec n → ℂ

/-- The complex normalization factor given by the reciprocal of `2 ^ (n / 2)`. -/
def hnorm (n : ℕ) : ℂ := ((2 : ℂ) ^ (n / 2))⁻¹

/-- The binary character transform of an amplitude function, scaled by `hnorm n`. -/
def hadamard {n : ℕ} (ψ : State n) : State n :=
  fun y => hnorm n * ∑ x : BVec n, (eps (dot y x) : ℂ) * ψ x

/-- The amplitude function equal to one at `u` and zero at every other vector. -/
def basisState {n : ℕ} (u : BVec n) : State n :=
  fun x => if x = u then 1 else 0

/-- The computational basis state at the zero binary vector. -/
def initState (n : ℕ) : State n := basisState (n := n) 0

/-- The operator multiplying each amplitude by the binary sign of the Boolean oracle value. -/
def phaseOracle {n : ℕ} (f : BVec n → ZMod 2) (ψ : State n) : State n :=
  fun x => (eps (f x) : ℂ) * ψ x

/-- The squared complex norm of the amplitude at `z`. -/
def prob {n : ℕ} (ψ : State n) (z : BVec n) : ℝ := Complex.normSq (ψ z)

/-- The binary dot product is symmetric. -/
lemma dot_comm {n : ℕ} (a b : BVec n) : dot a b = dot b a := by
  simp only [dot]
  rw [dotProduct_comm]

/-- The complex-valued sum of a binary character is `2 ^ n` for the zero vector and zero
otherwise. -/
lemma sum_eps_dot_c {n : ℕ} (v : BVec n) :
    ∑ x : BVec n, (eps (dot v x) : ℂ) = if v = 0 then (2 : ℂ) ^ n else 0 := by
  have h : (∑ x : BVec n, (eps (dot v x) : ℂ))
      = ((∑ x : BVec n, eps (dot v x) : ℤ) : ℂ) := by
    rw [Int.cast_sum]
  rw [h, sum_eps_dot]
  by_cases hv : v = 0
  · simp [hv]
  · simp [hv]

/-- Casting an integer Walsh coefficient to the complex numbers gives the corresponding sum of
complex sign products. -/
lemma walsh_cast {n : ℕ} (f : BVec n → ZMod 2) (w : BVec n) :
    ((walsh f w : ℤ) : ℂ)
      = ∑ x : BVec n, (eps (dot w x) : ℂ) * (eps (f x) : ℂ) := by
  rw [walsh, Int.cast_sum]
  exact Finset.sum_congr rfl (fun x _ => Int.cast_mul _ _)

/-- For even `n`, the product of two complex powers `2 ^ (n / 2)` equals `2 ^ n`. -/
lemma pow_half_mul_c {n : ℕ} (hn : Even n) :
    (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) = (2 : ℂ) ^ n := by
  obtain ⟨k, hk⟩ := hn
  subst hk
  have hdiv : (k + k) / 2 = k := by omega
  rw [hdiv, ← pow_add]

/-- For even `n`, the square of the Hadamard normalization factor times `2 ^ n` equals one. -/
lemma hnorm_sq_mul {n : ℕ} (hn : Even n) : hnorm n * hnorm n * (2 : ℂ) ^ n = 1 := by
  have h2 : (2 : ℂ) ^ (n / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsq : (2 : ℂ) ^ n = (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) :=
    (pow_half_mul_c hn).symm
  unfold hnorm
  rw [hsq]
  rw [show ((2 : ℂ) ^ (n / 2))⁻¹ * ((2 : ℂ) ^ (n / 2))⁻¹
        * ((2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2))
      = (((2 : ℂ) ^ (n / 2))⁻¹ * (2 : ℂ) ^ (n / 2))
        * (((2 : ℂ) ^ (n / 2))⁻¹ * (2 : ℂ) ^ (n / 2)) from by ring]
  rw [inv_mul_cancel₀ h2, one_mul]

/-- In even dimension, applying the Hadamard transform twice recovers every amplitude function. -/
theorem hadamard_hadamard {n : ℕ} (hn : Even n) (ψ : State n) :
    hadamard (hadamard ψ) = ψ := by
  funext z
  simp only [hadamard]
  have hinner : ∀ x : BVec n,
      (∑ y : BVec n, (eps (dot z y) : ℂ) * (eps (dot y x) : ℂ))
        = if x = z then (2 : ℂ) ^ n else 0 := by
    intro x
    have hterm : ∀ y : BVec n,
        (eps (dot z y) : ℂ) * (eps (dot y x) : ℂ) = (eps (dot (z + x) y) : ℂ) := by
      intro y
      have harg : dot z y + dot y x = dot (z + x) y := by
        rw [dot_comm y x]
        simp only [dot]
        rw [← add_dotProduct]
      rw [← Int.cast_mul, ← eps_add, harg]
    simp only [hterm]
    rw [sum_eps_dot_c]
    by_cases hxz : x = z
    · rw [if_pos hxz, if_pos (by rw [hxz, BentCore.add_self_bvec])]
    · rw [if_neg hxz, if_neg]
      intro h0
      exact hxz ((add_eq_zero_iff_eq_bvec z x).mp h0).symm
  have hswap : (∑ y : BVec n, (eps (dot z y) : ℂ) * (hnorm n * ∑ x : BVec n,
        (eps (dot y x) : ℂ) * ψ x))
      = hnorm n * ∑ x : BVec n, ψ x * (∑ y : BVec n,
          (eps (dot z y) : ℂ) * (eps (dot y x) : ℂ)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hswap]
  simp only [hinner]
  rw [Finset.sum_eq_single z]
  · rw [if_pos rfl]
    rw [show hnorm n * (hnorm n * (ψ z * (2 : ℂ) ^ n))
        = ψ z * (hnorm n * hnorm n * (2 : ℂ) ^ n) from by ring, hnorm_sq_mul hn,
      mul_one]
  · intro x _ hx
    rw [if_neg hx, mul_zero]
  · intro hmem
    simp at hmem

/-- The Hadamard transform of the zero basis state is the constant amplitude function `hnorm n`. -/
theorem hadamard_init (n : ℕ) : hadamard (initState n) = fun _ => hnorm n := by
  funext y
  simp only [hadamard, initState, basisState]
  have h : (∑ x : BVec n, (eps (dot y x) : ℂ) * (if x = 0 then (1 : ℂ) else 0)) = 1 := by
    rw [Finset.sum_eq_single (0 : BVec n)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hmem
      simp at hmem
  rw [h, mul_one]

/-- In even dimension, the Hadamard transform of a constant amplitude is supported at zero, with
value `2 ^ (n / 2) * v` there. -/
theorem hadamard_const {n : ℕ} (hn : Even n) (v : ℂ) (y : BVec n) :
    hadamard (fun _ : BVec n => v) y
      = if y = 0 then (2 : ℂ) ^ (n / 2) * v else 0 := by
  simp only [hadamard]
  rw [show (∑ x : BVec n, (eps (dot y x) : ℂ) * v)
      = (∑ x : BVec n, (eps (dot y x) : ℂ)) * v from by rw [Finset.sum_mul]]
  rw [sum_eps_dot_c]
  by_cases hy : y = 0
  · rw [if_pos hy, if_pos hy]
    have h2 : (2 : ℂ) ^ (n / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsq : (2 : ℂ) ^ n = (2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) :=
      (pow_half_mul_c hn).symm
    unfold hnorm
    rw [hsq]
    rw [show ((2 : ℂ) ^ (n / 2))⁻¹ * ((2 : ℂ) ^ (n / 2) * (2 : ℂ) ^ (n / 2) * v)
        = (2 : ℂ) ^ (n / 2) * v from by
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]]
  · rw [if_neg hy, if_neg hy]
    simp

/-- The gate type consisting of a Hadamard transform or a phase oracle for a Boolean function. -/
inductive Gate (n : ℕ) where

  | had : Gate n

  | orcl : (BVec n → ZMod 2) → Gate n

namespace Gate

/-- The amplitude-function action of a gate, interpreted as a Hadamard transform or a phase
oracle. -/
def eval {n : ℕ} : Gate n → State n → State n
  | .had, ψ => hadamard ψ
  | .orcl f, ψ => phaseOracle f ψ

/-- The Boolean indicator that a gate is a phase-oracle query. -/
def isOracle {n : ℕ} : Gate n → Bool
  | .had => false
  | .orcl _ => true

end Gate

/-- Finite lists of gates acting on length-`n` binary amplitude functions. -/
abbrev Program (n : ℕ) : Type := List (Gate n)

/-- Evaluates a gate list on an initial amplitude function by applying its gates from left to
right. -/
def Program.eval {n : ℕ} (p : Program n) (ψ : State n) : State n :=
  p.foldl (fun ψ g => g.eval ψ) ψ

/-- The number of phase-oracle gates in a program. -/
def Program.oracleCount {n : ℕ} (p : Program n) : ℕ :=
  (p.filter Gate.isOracle).length

end Qatlib.Papers.NonlinBool08.MainResults.QuantumDefs
