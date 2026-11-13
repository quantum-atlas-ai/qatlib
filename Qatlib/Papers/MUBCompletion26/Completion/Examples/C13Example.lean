/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Existence of a Flat Six-Dimensional Phase Hadamard Matrix Without Zero Three-Minors

This module formalizes the existence statement of Appendix A of Sun: there exists
a `6 × 6` complex phase Hadamard matrix `H` with unit-modulus entries satisfying
`H H* = 6 I_6` such that all `400` positional `3 × 3` minors of `H` are nonzero,
providing an explicit flat unitary `H / √6` satisfying the middle-minor
hypothesis of Theorem 3.1.

## Main statements

* `UnitModulusEntries`: every entry of `H` has unit modulus (`Complex.normSq (H i j) = 1`).
* `PhaseHadamardFlat`: phase Hadamard condition `H * Hᴴ = (6 : ℂ) • 1`.
* `AllPositionalThreeMinorsNonzero`: all `400` positional `3 × 3` minors are nonzero.
* `appendix_a_c13`: existence of `H : Matrix (Fin 6) (Fin 6) ℂ` satisfying all three properties.

## References

* [Sun, 2026][Sun2026], Appendix A, Eq. (A.1) and Sections A.1--A.3.
-/

open Matrix
open scoped Matrix BigOperators

set_option autoImplicit false

namespace Qatlib.Papers.MUBCompletion26.Completion.Examples

/-- All entries have unit modulus. -/
def UnitModulusEntries (H : Matrix (Fin 6) (Fin 6) ℂ) : Prop :=
  ∀ i j : Fin 6, Complex.normSq (H i j) = 1

/-- `H` is a phase Hadamard matrix in the normalization `H H* = 6 I_6`. -/
def PhaseHadamardFlat (H : Matrix (Fin 6) (Fin 6) ℂ) : Prop :=
  H * Hᴴ = (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)

/-- All `400` positional `3 × 3` minors are nonzero. -/
def AllPositionalThreeMinorsNonzero (H : Matrix (Fin 6) (Fin 6) ℂ) : Prop :=
  ∀ e f : Fin 3 → Fin 6, Function.Injective e → Function.Injective f →
    Matrix.det (fun a b : Fin 3 => H (e a) (f b)) ≠ 0

private noncomputable def omega : ℂ := (-1 + Complex.I * Real.sqrt 3) / 2

private lemma omega_sq : omega ^ 2 = -1 - omega := by
  apply Complex.ext <;>
    norm_num [omega, pow_two, Complex.mul_re, Complex.mul_im]
  · nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  · ring

private lemma omega_conj : star omega = -1 - omega := by
  apply Complex.ext <;> norm_num [omega]
  ring

private lemma normSq_omega_pow (k : Fin 3) : Complex.normSq (omega ^ (k : ℕ)) = 1 := by
  have h : Complex.normSq omega = 1 := by
    norm_num [omega, Complex.normSq_apply]
  rw [map_pow, h, one_pow]

-- Tao's symmetric Butson matrix, encoded by powers of the cube root of unity.
private def taoExp : Matrix (Fin 6) (Fin 6) (Fin 3) :=
  ![![0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 2, 2],
    ![0, 1, 0, 2, 2, 1],
    ![0, 1, 2, 0, 1, 2],
    ![0, 2, 2, 1, 0, 1],
    ![0, 2, 1, 2, 1, 0]]

private noncomputable def taoH : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => omega ^ (taoExp i j : ℕ)

private noncomputable def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * omega

private lemma toC_zero_iff (p : ℤ × ℤ) : toC p = 0 ↔ p = (0, 0) := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    norm_num [toC, omega] at him hre
    exact Prod.ext (by simpa [him] using hre) him
  · rintro rfl
    simp [toC]

private def eisAdd (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 + q.1, p.2 + q.2)
private def eisSub (p q : ℤ × ℤ) : ℤ × ℤ := (p.1 - q.1, p.2 - q.2)
private def eisMul (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1 - p.2 * q.2)
private def eisConj (p : ℤ × ℤ) : ℤ × ℤ := (p.1 - p.2, -p.2)

private lemma toC_add (p q : ℤ × ℤ) : toC (eisAdd p q) = toC p + toC q := by
  simp only [toC, eisAdd, Int.cast_add]
  ring

private lemma toC_sub (p q : ℤ × ℤ) : toC (eisSub p q) = toC p - toC q := by
  simp only [toC, eisSub, Int.cast_sub]
  ring

private lemma toC_mul (p q : ℤ × ℤ) : toC (eisMul p q) = toC p * toC q := by
  simp only [toC, eisMul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  calc
    _ = ((p.1 : ℂ) + p.2 * omega) * ((q.1 : ℂ) + q.2 * omega) -
        (p.2 : ℂ) * q.2 * (omega ^ 2 - (-1 - omega)) := by ring
    _ = _ := by rw [omega_sq]; ring

private lemma toC_conj (p : ℤ × ℤ) : toC (eisConj p) = star (toC p) := by
  simp only [toC, eisConj, Int.cast_sub, Int.cast_neg, star_add, star_mul,
    star_intCast, omega_conj]
  ring

private def unitPowEis (k : Fin 3) : ℤ × ℤ := ![(1, 0), (0, 1), (-1, -1)] k

private lemma toC_unitPowEis (k : Fin 3) : toC (unitPowEis k) = omega ^ (k : ℕ) := by
  fin_cases k <;> simp [unitPowEis, toC, omega_sq, sub_eq_add_neg]

private def taoEis (i j : Fin 6) : ℤ × ℤ := unitPowEis (taoExp i j)

private lemma toC_taoEis (i j : Fin 6) : toC (taoEis i j) = taoH i j :=
  toC_unitPowEis (taoExp i j)

private def eisDot (i j : Fin 6) : ℤ × ℤ :=
  (List.ofFn fun k : Fin 6 => eisMul (taoEis i k) (eisConj (taoEis j k))).foldr
    eisAdd (0, 0)

private lemma eisDot_eq :
    ∀ i j : Fin 6, eisDot i j = if i = j then (6, 0) else (0, 0) := by
  decide

private lemma taoH_flat : PhaseHadamardFlat taoH := by
  ext i j
  have h : (taoH * taoHᴴ) i j = toC (eisDot i j) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, eisDot, List.ofFn_succ,
      Fin.sum_univ_succ]
    simp only [toC_add, toC_mul, toC_conj, toC_taoEis]
    simp [toC]
  rw [h, eisDot_eq]
  by_cases hij : i = j <;> simp [hij, toC]

private def det3Eis (M : Matrix (Fin 3) (Fin 3) (ℤ × ℤ)) : ℤ × ℤ :=
  eisSub (eisAdd (eisAdd
    (eisSub (eisSub (eisMul (eisMul (M 0 0) (M 1 1)) (M 2 2))
      (eisMul (eisMul (M 0 0) (M 1 2)) (M 2 1)))
      (eisMul (eisMul (M 0 1) (M 1 0)) (M 2 2)))
    (eisMul (eisMul (M 0 1) (M 1 2)) (M 2 0)))
    (eisMul (eisMul (M 0 2) (M 1 0)) (M 2 1)))
    (eisMul (eisMul (M 0 2) (M 1 1)) (M 2 0))

private lemma toC_det3Eis (M : Matrix (Fin 3) (Fin 3) (ℤ × ℤ)) :
    toC (det3Eis M) = Matrix.det (fun a b => toC (M a b)) := by
  simp only [det3Eis, toC_sub, toC_add, toC_mul, Matrix.det_fin_three]

-- Only the 400 pairs of increasing triples require determinant computations.
private lemma sorted_minors_nonzero :
    ∀ i₀ i₁ i₂ j₀ j₁ j₂ : Fin 6,
      i₀ < i₁ → i₁ < i₂ → j₀ < j₁ → j₁ < j₂ →
      det3Eis (fun a b => taoEis (![i₀, i₁, i₂] a) (![j₀, j₁, j₂] b)) ≠ (0, 0) := by
  decide

private lemma taoH_minors : AllPositionalThreeMinorsNonzero taoH := by
  intro e f he hf hzero
  let σ := Tuple.sort e
  let τ := Tuple.sort f
  have hs : StrictMono (e ∘ σ) :=
    (Tuple.monotone_sort e).strictMono_of_injective (he.comp σ.injective)
  have ht : StrictMono (f ∘ τ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp τ.injective)
  have hsorted := sorted_minors_nonzero
    (e (σ 0)) (e (σ 1)) (e (σ 2)) (f (τ 0)) (f (τ 1)) (f (τ 2))
    (hs (by decide : (0 : Fin 3) < 1)) (hs (by decide : (1 : Fin 3) < 2))
    (ht (by decide : (0 : Fin 3) < 1)) (ht (by decide : (1 : Fin 3) < 2))
  apply hsorted
  apply (toC_zero_iff _).1
  rw [toC_det3Eis]
  have heq : ∀ a : Fin 3, ![e (σ 0), e (σ 1), e (σ 2)] a = e (σ a) := by
    intro a; fin_cases a <;> rfl
  have hfq : ∀ b : Fin 3, ![f (τ 0), f (τ 1), f (τ 2)] b = f (τ b) := by
    intro b; fin_cases b <;> rfl
  simp only [heq, hfq, toC_taoEis]
  change Matrix.det (Matrix.submatrix
    (Matrix.submatrix (fun a b : Fin 3 => taoH (e a) (f b)) id τ) σ id) = (0 : ℂ)
  rw [Matrix.det_permute, Matrix.det_permute', hzero, mul_zero, mul_zero]

/-- Appendix A: there exists a `6 × 6` complex matrix `H` with unit-modulus
entries, `H H* = 6 I_6`, and all `400` positional `3 × 3` minors nonzero. -/
theorem appendix_a_c13 :
    ∃ H : Matrix (Fin 6) (Fin 6) ℂ,
      UnitModulusEntries H ∧ PhaseHadamardFlat H ∧ AllPositionalThreeMinorsNonzero H := by
  exact ⟨taoH, fun i j => normSq_omega_pow (taoExp i j), taoH_flat, taoH_minors⟩

end Qatlib.Papers.MUBCompletion26.Completion.Examples
