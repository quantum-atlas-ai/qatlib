/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Parity vanishing in a weighted kernel

This module isolates a finite weighted parity structure `TreeHamiltonian` with a height
condition that supports induction. It supplies an abstract form of the odd-depth kernel
vanishing argument associated with Lemma 11 in [Ambainis2007].

## Main statements

* `TreeHamiltonian` records symmetric complex weights, zero diagonal, parity crossing, and a
  descending-height neighbor condition.
* `odd_amplitudes_vanish` proves that a vector in the weighted kernel vanishes at every vertex
  whose parity is `false`.

## References

* [Ambainis, 2007][Ambainis2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NANDAmbainis07.MainResults

open scoped BigOperators

/-- A finite weighted parity structure with symmetric complex weights, zero diagonal, and
weights only between opposite parities. Each false-parity vertex has a true-parity neighbor
whose other weighted neighbors have smaller height. -/
structure TreeHamiltonian (V : Type*) [Fintype V] [DecidableEq V] where

  par : V → Bool

  ht : V → ℕ

  wt : V → V → ℂ

  wt_symm : ∀ u v, wt u v = wt v u

  wt_irrefl : ∀ u, wt u u = 0

  par_cross : ∀ u v, wt u v ≠ 0 → par u ≠ par v

  step : ∀ u, par u = false →
    ∃ c, par c = true ∧ wt c u ≠ 0 ∧
      ∀ w, w ≠ u → wt c w ≠ 0 → ht w < ht u

/-- A vector satisfying all weighted kernel equations for `TreeHamiltonian` vanishes at every
vertex whose parity is `false`. This is an abstract parity-vanishing statement corresponding
to [Ambainis, Lemma 11][Ambainis2007]. -/
theorem odd_amplitudes_vanish {V : Type*} [Fintype V] [DecidableEq V]
    (G : TreeHamiltonian V) (α : V → ℂ)
    (hker : ∀ u, ∑ v, G.wt u v * α v = 0) :
    ∀ u, G.par u = false → α u = 0 := by
  have main : ∀ n, ∀ u, G.ht u = n → G.par u = false → α u = 0 := by
    intro n
    refine Nat.strong_induction_on n
      (p := fun n => ∀ u, G.ht u = n → G.par u = false → α u = 0) ?_
    intro n ih u hu hpar

    obtain ⟨c, hcpar, hcu, hstep⟩ := G.step u hpar

    have hc := hker c

    have hzero : ∑ v ∈ (Finset.univ.erase u), G.wt c v * α v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [Finset.mem_erase] at hv
      obtain ⟨hvu, _⟩ := hv
      by_cases hwv : G.wt c v = 0
      · simp [hwv]
      · have hvpar : G.par v = false := by
          have hne := G.par_cross c v hwv
          rw [hcpar] at hne
          cases h : G.par v <;> simp_all
        have hvlt : G.ht v < G.ht u := hstep v hvu hwv
        have hvlt' : G.ht v < n := by omega
        have hih : α v = 0 := ih (G.ht v) hvlt' v rfl hvpar
        rw [hih]
        simp

    have hc' : G.wt c u * α u + ∑ v ∈ (Finset.univ.erase u), G.wt c v * α v = 0 := by
      rw [Finset.add_sum_erase (Finset.univ) (fun v => G.wt c v * α v) (Finset.mem_univ u)]
      exact hc
    rw [hzero, add_zero] at hc'
    rcases mul_eq_zero.mp hc' with h0 | h0
    · exact absurd h0 hcu
    · exact h0
  intro u hpar
  exact main (G.ht u) u rfl hpar

end Qatlib.Papers.NANDAmbainis07.MainResults
