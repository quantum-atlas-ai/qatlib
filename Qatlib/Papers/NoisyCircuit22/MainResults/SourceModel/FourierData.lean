/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — abstract Fourier data

Aharonov--Gao--Landau--Liu--Vazirani, fixed arXiv:2211.03999v1.

The Pauli-path analysis only uses three structural inputs about the Fourier coefficients
`f(C,s,x)` of Definition 1 (p.7, Eq. (7)):

* linearity of the circuit expectation `E_C`;
* orthogonality of distinct Pauli paths (Lemma 3, Eq. (21), p.10);
* the fact that `f(C,s,x)^2 = f(C,s,0^n)^2` for every `x` (Eq. (14), p.8).

This file packages those inputs abstractly so that the Fourier-weight and XEB identities
of Lemmas 4, 7, 9, Theorems 3--6 can be derived without re-formalising the circuit
distribution each time.  The concrete Pauli-path objects live in `PauliPath.lean`; the
expectation `E` is an arbitrary real-linear functional (an expectation is linear).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

open BigOperators
open scoped BigOperators

variable {Ω Path : Type*}

/-- A circuit expectation: a real-linear functional on observables `Ω → ℝ`. -/
abbrev Expectation (Ω : Type*) := (Ω → ℝ) →ₗ[ℝ] ℝ

/-- Lemma 3 / Eq. (21), p.10: distinct Pauli paths have orthogonal Fourier coefficients,
`E_C[f(C,s,x) f(C,s',x)] = 0` for `s ≠ s'`. -/
def Orthogonality (E : Expectation Ω) (f : Ω → Path → ℝ) : Prop :=
  ∀ s s' : Path, s ≠ s' → E (fun C => f C s * f C s') = 0

/-- Definition 5 / Eq. (24), p.11: the Fourier weight of degree `k`. -/
def FourierWeight [Fintype Path] (n : ℕ) (E : Expectation Ω) (f : Ω → Path → ℝ)
    (weight : Path → ℕ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * n) *
    ∑ s ∈ Finset.univ.filter (fun s => weight s = k), E (fun C => (f C s) ^ 2)

/-- Definition 4 / Eq. (23), p.10: anti-concentration with an explicit constant. -/
def AntiConcentration (n : ℕ) (E : Expectation Ω)
    (p : Ω → (Fin n → Bool) → ℝ) : Prop :=
  ∃ Cac : ℝ, (2 : ℝ) ^ n * ∑ x : Fin n → Bool, E (fun C => (p C x) ^ 2) ≤ Cac

/-- The expectation of the square of a finite sum of orthogonal Fourier coefficients
splits into the sum of the per-path second moments (the orthogonality step used in
Eqs. (25), (28), (56), (63)). -/
theorem inner_sq_expansion [Fintype Path] (E : Expectation Ω) (f : Ω → Path → ℝ)
    (horth : Orthogonality E f) (t : Finset Path) :
    E (fun C => (∑ s ∈ t, f C s) ^ 2) =
      ∑ s ∈ t, E (fun C => (f C s) ^ 2) := by
  have hsquare : (fun C => (∑ s ∈ t, f C s) ^ 2) =
      ∑ s ∈ t, ∑ s' ∈ t, fun C => f C s * f C s' := by
    funext C
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.sum_apply]
  rw [hsquare]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_eq_single_of_mem s hs]
  · simp [pow_two]
  · intro s' _ hne
    exact horth s s' (Ne.symm hne)

/-- Orthogonality also gives the second moment of the sum over the complement of one
path: only the diagonal term survives. -/
theorem inner_sq_expansion_erase [Fintype Path] [DecidableEq Path] (E : Expectation Ω)
    (f : Ω → Path → ℝ) (horth : Orthogonality E f) (s0 : Path) :
    E (fun C => (∑ s ∈ Finset.univ.erase s0, f C s) ^ 2) =
      ∑ s ∈ Finset.univ.erase s0, E (fun C => (f C s) ^ 2) :=
  inner_sq_expansion E f horth (Finset.univ.erase s0)

/-- Removing one coefficient from a second moment isolates that coefficient:
`E[(Σ_all f)^2] - E[(Σ_{s≠s0} f)^2] = E[f_{s0}^2]`. -/
theorem second_moment_diff [Fintype Path] [DecidableEq Path] (E : Expectation Ω) (f : Ω → Path → ℝ)
    (horth : Orthogonality E f) (s0 : Path) :
    E (fun C => (∑ s, f C s) ^ 2) - E (fun C => (∑ s ∈ Finset.univ.erase s0, f C s) ^ 2)
      = E (fun C => (f C s0) ^ 2) := by
  rw [inner_sq_expansion E f horth, inner_sq_expansion E f horth]
  rw [← Finset.add_sum_erase Finset.univ (fun s => E (fun C => (f C s) ^ 2))
    (Finset.mem_univ s0)]
  ring

/-- Equation (24) is the weight decomposition: the full sum over paths of
`2^{2n} E[f^2]` is the sum of all Fourier weights. -/
theorem sum_fourierWeight [Fintype Path] (n : ℕ) (E : Expectation Ω)
    (f : Ω → Path → ℝ) (weight : Path → ℕ) (N : ℕ) (hN : ∀ s, weight s ≤ N) :
    (2 : ℝ) ^ (2 * n) * ∑ s, E (fun C => (f C s) ^ 2) =
      ∑ k ∈ Finset.range (N + 1), FourierWeight n E f weight k := by
  simp only [FourierWeight]
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_fiberwise_of_maps_to
    (t := Finset.range (N + 1))
    (fun s _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN s)))
    (fun s => E (fun C => (f C s) ^ 2))).symm

end Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel
