/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.SortDistinct01.MainResults.Sorting

abbrev QIdx (Z N : ℕ) : Type := Fin Z × Fin N

abbrev QState (Z N : ℕ) : Type := EuclideanSpace ℂ (QIdx Z N)

def mkQ {Z N : ℕ} (f : QIdx Z N → ℂ) : QState Z N := WithLp.toLp 2 f

def phaseOracle {Z N : ℕ} (x : Fin N → ℂ) (u : QState Z N) : QState Z N :=
  mkQ fun j => x j.2 * u j

def shiftCycle {N : ℕ} (hN : 0 < N) (k d : ℕ) : Equiv.Perm (Fin N) :=
  ((List.range d).map fun i =>
    Equiv.swap ⟨(k + i) % N, Nat.mod_lt _ hN⟩
      ⟨(k + i + 1) % N, Nat.mod_lt _ hN⟩).prod

def sortingWeight {N : ℕ} (hN : 0 < N) (σ τ : Equiv.Perm (Fin N)) : ℝ :=
  ∑ k ∈ Finset.range N, ∑ d ∈ Finset.range N,
    if k + d < N ∧ 1 ≤ d ∧ τ = shiftCycle hN k d * σ then (1 : ℝ) / (d : ℝ) else 0

def sortingPotential {Z N : ℕ} (hN : 0 < N)
    (ψ : Equiv.Perm (Fin N) → ℕ → QState Z N) (j : ℕ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
    sortingWeight hN σ τ * Complex.re ⟪ψ σ j, ψ τ j⟫

theorem lemma8_sorting_step_bound {Z N T : ℕ} (hN : 2 ≤ N)
    (χ : Equiv.Perm (Fin N) → Fin N → ℂ)
    (ψ : Equiv.Perm (Fin N) → ℕ → QState Z N)
    (U : QState Z N ≃ₗᵢ[ℂ] QState Z N)
    (_hunit : ∀ x j, ‖ψ x j‖ = 1)
    (_hstep : ∀ x j, ψ x (j + 1) = U (phaseOracle (χ x) (ψ x j)))
    {j : ℕ} (_hj : j < T)
    (γ : Fin (N - 1) → ℝ)
    (hregroup : |sortingPotential (by omega : 0 < N) ψ j
        - sortingPotential (by omega : 0 < N) ψ (j + 1)|
      ≤ 2 * ∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
          γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * γ k)
    (hhilb : |∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
        γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * γ k|
      ≤ Real.pi * Real.sqrt (∑ i, (γ i) ^ 2) * Real.sqrt (∑ k, (γ k) ^ 2))
    (hnorm : (∑ i : Fin (N - 1), (γ i) ^ 2) ≤ (Nat.factorial N : ℝ)) :
    |sortingPotential (by omega : 0 < N) ψ j
        - sortingPotential (by omega : 0 < N) ψ (j + 1)|
      ≤ 2 * Real.pi * (Nat.factorial N : ℝ) := by
  set X : ℝ := ∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
      γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * γ k with hXdef
  set a : ℝ := Real.sqrt (∑ i : Fin (N - 1), (γ i) ^ 2) with hadef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ∑ i : Fin (N - 1), (γ i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hX : |X| ≤ Real.pi * a * a := hhilb
  have hmain : |sortingPotential (by omega : 0 < N) ψ j
      - sortingPotential (by omega : 0 < N) ψ (j + 1)| ≤ 2 * X := hregroup
  have hstep1 : 2 * X ≤ 2 * |X| := by nlinarith [le_abs_self X]
  have hXle : 2 * |X| ≤ 2 * Real.pi * (Nat.factorial N : ℝ) := by
    calc 2 * |X| ≤ 2 * (Real.pi * a * a) := by linarith
      _ = 2 * Real.pi * a ^ 2 := by ring
      _ ≤ 2 * Real.pi * (Nat.factorial N : ℝ) := by
          rw [ha2]
          have := Real.pi_pos
          nlinarith [hnorm, Real.pi_pos]
  linarith [hmain, hstep1, hXle]

end Qatlib.Papers.SortDistinct01.MainResults.Sorting
