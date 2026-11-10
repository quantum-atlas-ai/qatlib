/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QWalkDiff01.MainResults

def columnSize (n j : ℕ) : ℕ :=
  if j ≤ n then 2 ^ j else 2 ^ (2 * n - j)

def vertexCount (n : ℕ) : ℕ := 2 ^ (n + 1) + 2 ^ n - 2

def reducedHamiltonian (n : ℕ) (γ : ℝ) : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℝ :=
  fun i j =>
    if i = j then
      (if i.val = 0 ∨ i.val = n ∨ i.val = 2 * n then 2 * γ else 3 * γ)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
      -Real.sqrt 2 * γ
    else 0

def reducedHamiltonianC (n : ℕ) (γ : ℝ) :
    Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℂ :=
  (reducedHamiltonian n γ).map (algebraMap ℝ ℂ)

def quantumPropagator (n : ℕ) (γ t : ℝ) :
    Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℂ :=
  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • reducedHamiltonianC n γ)

def rightRate (n : ℕ) (γ : ℝ) (j : Fin (2 * n + 1)) : ℝ :=
  if 2 * n ≤ j.val then 0 else if j.val < n then 2 * γ else γ

def leftRate (n : ℕ) (γ : ℝ) (j : Fin (2 * n + 1)) : ℝ :=
  if j.val = 0 then 0 else if j.val ≤ n then γ else 2 * γ

def classicalColumnGenerator (n : ℕ) (γ : ℝ) :
    Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℝ :=
  fun i j =>
    if i = j then -(rightRate n γ i + leftRate n γ i)
    else if j.val + 1 = i.val then rightRate n γ j
    else if i.val + 1 = j.val then leftRate n γ j
    else 0

def classicalColumnProb (n : ℕ) (γ t : ℝ) : Fin (2 * n + 1) → ℝ :=
  NormedSpace.exp (t • classicalColumnGenerator n γ) *ᵥ (Pi.single 0 1)

def leftRoot (n : ℕ) : Fin (2 * n + 1) := 0

def rightRoot (n : ℕ) : Fin (2 * n + 1) := ⟨2 * n, by omega⟩

@[simp] theorem columnSize_zero (n : ℕ) : columnSize n 0 = 1 := by
  simp [columnSize]

@[simp] theorem columnSize_self (n : ℕ) : columnSize n n = 2 ^ n := by
  simp [columnSize]

theorem sum_pow_two_range (m : ℕ) :
    (∑ j ∈ Finset.range m, 2 ^ j) = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    omega

theorem sum_columnSize (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1), columnSize n j) = vertexCount n := by
  rw [show 2 * n + 1 = (n + 1) + n by omega, Finset.sum_range_add]
  have hleft : (∑ j ∈ Finset.range (n + 1), columnSize n j) = 2 ^ (n + 1) - 1 := by
    rw [← sum_pow_two_range (n + 1)]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj' : j ≤ n := by
      simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
    simp [columnSize, hj']
  have hright : (∑ i ∈ Finset.range n, columnSize n (n + 1 + i)) = 2 ^ n - 1 := by
    have hcongr : ∀ i ∈ Finset.range n, columnSize n (n + 1 + i) = 2 ^ (n - 1 - i) := by
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      have hle : ¬ (n + 1 + i ≤ n) := by omega
      have hexp : 2 * n - (n + 1 + i) = n - 1 - i := by omega
      simp [columnSize, hle, hexp]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_range_reflect (fun j => 2 ^ j) n]
    exact sum_pow_two_range n
  rw [hleft, hright, vertexCount]
  have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

theorem columnSize_pos (n j : ℕ) : 0 < columnSize n j := by
  unfold columnSize
  split <;> exact Nat.two_pow_pos _

theorem reducedHamiltonian_apply_comm (n : ℕ) (γ : ℝ) (i j : Fin (2 * n + 1)) :
    reducedHamiltonian n γ i j = reducedHamiltonian n γ j i := by
  unfold reducedHamiltonian
  by_cases hij : i = j
  · subst hij; simp
  · have hji : ¬ j = i := fun h => hij h.symm
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · have hadj' : j.val + 1 = i.val ∨ i.val + 1 = j.val := hadj.symm
      simp [hij, hji, hadj, hadj']
    · have hadj' : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
        rintro (h | h)
        · exact hadj (Or.inr h)
        · exact hadj (Or.inl h)
      simp [hij, hji, hadj, hadj']

theorem reducedHamiltonian_transpose (n : ℕ) (γ : ℝ) :
    (reducedHamiltonian n γ)ᵀ = reducedHamiltonian n γ := by
  ext i j
  simpa using reducedHamiltonian_apply_comm n γ j i

theorem leftRoot_ne_rightRoot (n : ℕ) (hn : 1 ≤ n) : leftRoot n ≠ rightRoot n := by
  intro h
  have hv := congrArg Fin.val h
  simp [leftRoot, rightRoot] at hv
  omega

@[simp] theorem rightRate_rightRoot (n : ℕ) (γ : ℝ) :
    rightRate n γ (rightRoot n) = 0 := by
  simp [rightRate, rightRoot]

@[simp] theorem leftRate_leftRoot (n : ℕ) (γ : ℝ) :
    leftRate n γ (leftRoot n) = 0 := by
  simp [leftRate, leftRoot]

end Qatlib.Papers.QWalkDiff01.MainResults
