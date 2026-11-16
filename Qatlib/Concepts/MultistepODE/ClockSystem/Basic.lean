/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Complex.Basic

@[expose] public section


/-! # Actual finite multistep clock matrix

Demand: HighOrderODE10 Eq.(27)-(28). The entries are genuine finite complex
matrix blocks: explicit-Euler startup, the given multistep coefficients, and
constant final-time padding. Multiplication is proved to be the actual row
recurrence. No stability, inverse-norm, solver or state-preparation assertion
is encoded in a free numerical field.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix

namespace Qatlib.Concepts.MultistepODE.ClockSystem

variable {I : Type*}

/-- A single nonzero matrix block at an actual input time. -/
def pulse {n : ℕ} (p s : Fin n) (B : Matrix I I ℂ) : Matrix I I ℂ :=
  if s = p then B else 0

/-- The actual preceding valid clock index of a positive time. -/
def previous {N : ℕ} (t : Fin (N+1)) : Fin (N+1) :=
  ⟨t.val-1, by omega⟩

/-- The actual time j-k+ell in a valid multistep row j>=k. -/
def termTime {N k : ℕ} (t : Fin (N+1)) (ht : k ≤ t.val)
    (ell : Fin (k+1)) : Fin (N+1) := ⟨t.val-k+ell.val, by omega⟩

/-- The exact block in row t and column s of the finite source clock matrix. -/
def blocks [DecidableEq I] {N : ℕ} (k : ℕ) (alpha beta : Fin (k+1) → ℂ)
    (h : ℂ) (A : Matrix I I ℂ) (t s : Fin (N+1)) : Matrix I I ℂ :=
  if hs : t.val < k then
    pulse t s 1 - if 0 < t.val then pulse (previous t) s (1 + h • A) else 0
  else if t.val ≤ N/2 then
    ∑ ell : Fin (k+1), pulse (termTime t (by omega) ell) s
      (alpha ell • 1 - (h * beta ell) • A)
  else
    pulse t s 1 - if 0 < t.val then pulse (previous t) s 1 else 0

/-- Flatten an actual block family into an ordinary finite complex matrix. -/
def flattenMat {n : ℕ} (B : Fin n → Fin n → Matrix I I ℂ) :
    Matrix (Fin n × I) (Fin n × I) ℂ := fun u v => B u.1 v.1 u.2 v.2

/-- The actual source clock matrix on the product of time and spatial indices. -/
def clockMatrix [DecidableEq I] {N : ℕ} (k : ℕ) (alpha beta : Fin (k+1) → ℂ)
    (h : ℂ) (A : Matrix I I ℂ) : Matrix (Fin (N+1) × I) (Fin (N+1) × I) ℂ :=
  flattenMat (blocks k alpha beta h A)

/-- Flatten a history vector without changing any amplitudes. -/
def flatVec {n : ℕ} (x : Fin n → I → ℂ) : (Fin n × I) → ℂ := fun u => x u.1 u.2

/-- The source right-hand side keeps startup and multistep forcing coefficients distinct. -/
def rhs {N : ℕ} (k : ℕ) (beta : Fin (k+1) → ℂ) (h : ℂ)
    (initial forcing : I → ℂ) (t : Fin (N+1)) : I → ℂ :=
  if t.val = 0 then initial else if t.val < k then h • forcing
  else if t.val ≤ N/2 then (h * ∑ ell, beta ell) • forcing else 0

variable [Fintype I]

/-- An actual flattened matrix product equals the sum of its actual block products. -/
theorem blockMul {n : ℕ} (B : Fin n → Fin n → Matrix I I ℂ)
    (x : Fin n → I → ℂ) (t : Fin n) (i : I) :
    (flattenMat B *ᵥ flatVec x) (t,i) = ∑ s, (B t s *ᵥ x s) i := by
  simp only [flattenMat, flatVec, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- A single actual matrix block samples exactly its designated input vector. -/
theorem pulseSum {n : ℕ} (p : Fin n) (B : Matrix I I ℂ)
    (x : Fin n → I → ℂ) (i : I) :
    (∑ s, (pulse p s B *ᵥ x s) i) = (B *ᵥ x p) i := by
  rw [Finset.sum_eq_single p]
  · simp [pulse]
  · intro s _ hsp
    simp [pulse, hsp]
  · intro hp
    exact (hp (Finset.mem_univ p)).elim

/-- Multiplication by an actual finite matrix sum distributes over its summands. -/
theorem sumApply {J : Type*} [Fintype J] (B : J → Matrix I I ℂ) (x : I → ℂ) :
    (∑ j, B j) *ᵥ x = ∑ j, B j *ᵥ x := by
  classical
  have hs : ∀ S : Finset J, (∑ j ∈ S, B j) *ᵥ x = ∑ j ∈ S, B j *ᵥ x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih => simp [hj, Matrix.add_mulVec, ih]
  exact hs Finset.univ

/-- The startup row of the actual matrix is the explicit-Euler residual. -/
theorem startRow [DecidableEq I] {N k : ℕ} (alpha beta : Fin (k+1) → ℂ)
    (h : ℂ) (A : Matrix I I ℂ) (x : Fin (N+1) → I → ℂ)
    (t : Fin (N+1)) (ht : t.val < k) (i : I) :
    (clockMatrix k alpha beta h A *ᵥ flatVec x) (t,i) =
      x t i - (if 0 < t.val then ((1 + h • A) *ᵥ x (previous t)) i else 0) := by
  rw [clockMatrix, blockMul]
  by_cases hz : 0 < t.val
  · simp [blocks, ht, hz, Matrix.sub_mulVec, Finset.sum_sub_distrib, pulseSum]
  · simp [blocks, ht, hz, pulseSum]

/-- The main row of the actual matrix is exactly the given multistep residual. -/
theorem mainRow [DecidableEq I] {N k : ℕ} (alpha beta : Fin (k+1) → ℂ)
    (h : ℂ) (A : Matrix I I ℂ) (x : Fin (N+1) → I → ℂ)
    (t : Fin (N+1)) (ht : k ≤ t.val) (hL : t.val ≤ N/2) (i : I) :
    (clockMatrix k alpha beta h A *ᵥ flatVec x) (t,i) =
      ∑ ell, ((alpha ell • 1 - (h * beta ell) • A) *ᵥ x (termTime t ht ell)) i := by
  rw [clockMatrix, blockMul]
  simp only [blocks, dite_eq_right (by omega : ¬ t.val < k), ite_eq_left hL, sumApply,
    Finset.sum_apply]
  rw [Finset.sum_comm]
  simp only [pulseSum]

/-- The actual padding row copies its immediately preceding history vector. -/
theorem tailRow [DecidableEq I] {N k : ℕ} (alpha beta : Fin (k+1) → ℂ)
    (h : ℂ) (A : Matrix I I ℂ) (x : Fin (N+1) → I → ℂ)
    (t : Fin (N+1)) (hkL : k ≤ N/2) (ht : N/2 < t.val) (i : I) :
    (clockMatrix k alpha beta h A *ᵥ flatVec x) (t,i) =
      x t i - x (previous t) i := by
  have hnotk : ¬ t.val < k := by omega
  have hnotL : ¬ t.val ≤ N/2 := by omega
  have hpos : 0 < t.val := by omega
  rw [clockMatrix, blockMul]
  simp [blocks, hnotk, hnotL, hpos, Matrix.sub_mulVec, Finset.sum_sub_distrib, pulseSum]

end Qatlib.Concepts.MultistepODE.ClockSystem
