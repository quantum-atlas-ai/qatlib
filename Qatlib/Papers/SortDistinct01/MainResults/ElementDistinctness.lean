/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fintype.Perm

/-!
# Annotated-permutation potentials for element distinctness

This module defines annotated permutations, cyclic-shift steps, reciprocal-distance weights, and
the associated real overlap potential. Given a regrouping estimate, a Hilbert-form bound, and
squared-norm bounds, `lemma10_element_distinctness_step_bound` proves the `2*pi*N!*sqrt N` step
estimate from the element-distinctness analysis of [HoyerNeerbekShi2001].

## Main statements

* `annotWeight`: The sum of reciprocal shift distances over valid steps taking annotated
  permutation `σ` to `τ`.
* `lemma10_element_distinctness_step_bound`: Assuming the stated regrouping, Hilbert-form, and
  squared-norm bounds, one potential step changes by at most `2*pi*N!*sqrt N`, the bound in
  [Hoyer et al., Lemma 10][HoyerNeerbekShi2001].

## References

* [Hoyer et al., 2001][HoyerNeerbekShi2001]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexInnerProductSpace

namespace Qatlib.Papers.SortDistinct01.MainResults.ElementDistinctness

/-- The joint index type for a workspace of size `Z` and a query register of size `N`. -/
abbrev QIdx (Z N : ℕ) : Type := Fin Z × Fin N

/-- The finite-dimensional complex Euclidean state space on workspace/query indices. -/
abbrev QState (Z N : ℕ) : Type := EuclideanSpace ℂ (QIdx Z N)

/-- The Euclidean state vector with coordinate function `f`. -/
def mkQ {Z N : ℕ} (f : QIdx Z N → ℂ) : QState Z N := WithLp.toLp 2 f

/-- The coordinatewise oracle action multiplying each amplitude by the input value at its query
index. -/
def phaseOracle {Z N : ℕ} (x : Fin N → ℂ) (u : QState Z N) : QState Z N :=
  mkQ fun j => x j.2 * u j

/-- A permutation of `Fin N` together with a marked index. -/
structure AnnotPerm (N : ℕ) where

  perm : Equiv.Perm (Fin N)

  mark : Fin N
deriving Fintype, DecidableEq

/-- The permutation given by the ordered product of `d` adjacent swaps starting at `k`, with
indices reduced modulo positive `N`. -/
def shiftCycle {N : ℕ} (hN : 0 < N) (k d : ℕ) : Equiv.Perm (Fin N) :=
  ((List.range d).map fun i =>
    Equiv.swap ⟨(k + i) % N, Nat.mod_lt _ hN⟩
      ⟨(k + i + 1) % N, Nat.mod_lt _ hN⟩).prod

/-- The annotated permutation obtained by left-composing with `shiftCycle` and marking `k` when
in range, or `0` otherwise. -/
def annotStep {N : ℕ} (hN : 0 < N) (k d : ℕ) (σ : AnnotPerm N) : AnnotPerm N :=
  { perm := shiftCycle hN k d * σ.perm
    mark := if h : k < N then ⟨k, h⟩ else ⟨0, hN⟩ }

/-- The sum of reciprocal shift distances over valid steps taking annotated permutation `σ` to
`τ`. -/
def annotWeight {N : ℕ} (hN : 0 < N) (σ τ : AnnotPerm N) : ℝ :=
  ∑ k ∈ Finset.range N, ∑ d ∈ Finset.range N,
    if k + d < N ∧ 1 ≤ d ∧ τ = annotStep hN k d σ then (1 : ℝ) / (d : ℝ) else 0

/-- The weighted sum of real inner products over all pairs of annotated permutations at time
`j`. -/
def annotPotential {Z N : ℕ} (hN : 0 < N)
    (ψ : AnnotPerm N → ℕ → QState Z N) (j : ℕ) : ℝ :=
  ∑ σ : AnnotPerm N, ∑ τ : AnnotPerm N,
    annotWeight hN σ τ * Complex.re ⟪ψ σ j, ψ τ j⟫

/-- Assuming the stated regrouping, Hilbert-form, and squared-norm bounds, one potential step
changes by at most `2*pi*N!*sqrt N`, the bound in [Hoyer et al., Lemma
10][HoyerNeerbekShi2001]. -/
theorem lemma10_element_distinctness_step_bound {Z N T : ℕ} (hN : 2 ≤ N)
    (χ : AnnotPerm N → Fin N → ℂ)
    (ψ : AnnotPerm N → ℕ → QState Z N)
    (U : QState Z N ≃ₗᵢ[ℂ] QState Z N)
    (_hunit : ∀ x j, ‖ψ x j‖ = 1)
    (_hstep : ∀ x j, ψ x (j + 1) = U (phaseOracle (χ x) (ψ x j)))
    {j : ℕ} (_hj : j < T)
    (γ δ : Fin (N - 1) → ℝ)
    (hregroup : |annotPotential (by omega : 0 < N) ψ j
        - annotPotential (by omega : 0 < N) ψ (j + 1)|
      ≤ 2 * ∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
          γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * δ k)
    (hhilb : |∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
        γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * δ k|
      ≤ Real.pi * Real.sqrt (∑ i, (γ i) ^ 2) * Real.sqrt (∑ k, (δ k) ^ 2))
    (hγnorm : (∑ i : Fin (N - 1), (γ i) ^ 2) ≤ (Nat.factorial N : ℝ))
    (hδnorm : (∑ k : Fin (N - 1), (δ k) ^ 2)
      ≤ (Nat.factorial N : ℝ) * ((N : ℝ) - 1)) :
    |annotPotential (by omega : 0 < N) ψ j
        - annotPotential (by omega : 0 < N) ψ (j + 1)|
      ≤ 2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ) := by
  set X : ℝ := ∑ i : Fin (N - 1), ∑ k : Fin (N - 1),
      γ i * (1 / ((i : ℝ) + (k : ℝ) + 1)) * δ k with hXdef
  set a : ℝ := Real.sqrt (∑ i : Fin (N - 1), (γ i) ^ 2) with hadef
  set b : ℝ := Real.sqrt (∑ k : Fin (N - 1), (δ k) ^ 2) with hbdef
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = ∑ i : Fin (N - 1), (γ i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hb2 : b ^ 2 = ∑ k : Fin (N - 1), (δ k) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hfpos : (0 : ℝ) ≤ (Nat.factorial N : ℝ) := by positivity
  have hX : |X| ≤ Real.pi * a * b := hhilb
  have hmain : |annotPotential (by omega : 0 < N) ψ j
      - annotPotential (by omega : 0 < N) ψ (j + 1)| ≤ 2 * X := hregroup
  have h1 : 2 * X ≤ 2 * |X| := by nlinarith [le_abs_self X]

  have haN : a ^ 2 ≤ (Nat.factorial N : ℝ) := by rw [ha2]; exact hγnorm
  have hbN : b ^ 2 ≤ (Nat.factorial N : ℝ) * ((N : ℝ) - 1) := by rw [hb2]; exact hδnorm
  have hab2 : (a * b) ^ 2 ≤ (Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * ((N : ℝ) - 1)) := by
    have : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by ring
    rw [this]
    exact mul_le_mul haN hbN (sq_nonneg b) hfpos
  have hab : a * b ≤ Real.sqrt ((Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * ((N : ℝ) - 1))) := by
    rw [← Real.sqrt_sq (mul_nonneg ha hb)]
    exact Real.sqrt_le_sqrt hab2

  have hsqrt_le : Real.sqrt ((Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * ((N : ℝ) - 1)))
      ≤ (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ) := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := by omega
      exact_mod_cast this
    have hprod : (Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * ((N : ℝ) - 1))
        ≤ ((Nat.factorial N : ℝ) * Real.sqrt (N : ℝ)) ^ 2 := by
      have hsq : ((Nat.factorial N : ℝ) * Real.sqrt (N : ℝ)) ^ 2
          = (Nat.factorial N : ℝ) ^ 2 * (N : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hNpos.le]
      rw [hsq]
      have h1 : (Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * ((N : ℝ) - 1))
          = (Nat.factorial N : ℝ) ^ 2 * ((N : ℝ) - 1) := by ring
      rw [h1]
      have : ((N : ℝ) - 1) ≤ (N : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc Real.sqrt ((Nat.factorial N : ℝ) * ((Nat.factorial N : ℝ) * ((N : ℝ) - 1)))
        ≤ Real.sqrt (((Nat.factorial N : ℝ) * Real.sqrt (N : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ) :=
          Real.sqrt_sq (mul_nonneg hfpos (Real.sqrt_nonneg _))
  have habN : a * b ≤ (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ) := le_trans hab hsqrt_le
  have hXle : 2 * |X| ≤ 2 * Real.pi * (Nat.factorial N : ℝ) * Real.sqrt (N : ℝ) := by
    have h2 : |X| ≤ Real.pi * ((Nat.factorial N : ℝ) * Real.sqrt (N : ℝ)) := by
      calc |X| ≤ Real.pi * a * b := hX
        _ = Real.pi * (a * b) := by ring
        _ ≤ Real.pi * ((Nat.factorial N : ℝ) * Real.sqrt (N : ℝ)) :=
            mul_le_mul_of_nonneg_left habN Real.pi_pos.le
    have : 0 ≤ Real.pi := Real.pi_pos.le
    nlinarith [h2]
  linarith [hmain, h1, hXle]

end Qatlib.Papers.SortDistinct01.MainResults.ElementDistinctness
