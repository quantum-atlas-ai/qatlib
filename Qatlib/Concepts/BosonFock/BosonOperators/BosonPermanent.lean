/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# Bosonic occupation matrices and permanent weights

`FockOccupation` records finitely many mode counts with prescribed total particle number.
Repeating matrix rows according to these counts gives `bosonRowMatrix`; `bosonWeight` is its
squared permanent divided by the occupation factorial product. The module also specifies
collision-free occupations and a standard one-particle-per-mode input.

The mathematical background is described in [KoehlerLeung2026].

## Main statements

* `bosonRows_length`: the repeated mode list has the total occupation length.
* `bosonWeight`: the factorial-normalized squared permanent weight.
* `bosonOneState`: the standard input in the first half of `2 * n` modes.

## References

* [Koehler and Leung, 2026][KoehlerLeung2026]
-/

namespace Qatlib.Concepts.BosonFock.BosonOperators

open scoped BigOperators Nat

/-- The finite type of occupations of `n` particles in `m` modes, with mode counts summing to
`n`. -/
def FockOccupation (m n : ℕ) : Type := {s : Fin m → Fin (n + 1) // ∑ i, (s i : ℕ) = n}

instance {m n : ℕ} : Fintype (FockOccupation m n) := by
  unfold FockOccupation
  exact Subtype.fintype _

open Classical in
noncomputable instance {m n : ℕ} : DecidableEq (FockOccupation m n) := by
  unfold FockOccupation
  exact Classical.decEq _

/-- The list of mode labels repeating each mode `i` exactly `s i` times, in mode order. -/
def bosonRows {m : ℕ} (s : Fin m → ℕ) : List (Fin m) :=
  (List.finRange m).flatMap (fun i => List.replicate (s i) i)

/-- Summing a natural-valued function over the finite range list equals its finite-type sum. -/
private theorem listSum_finRange : ∀ (m : ℕ) (f : Fin m → ℕ),
    ((List.finRange m).map f).sum = ∑ i, f i
  | 0, _ => by simp
  | k + 1, f => by
    have e2 : ((List.finRange k).map Fin.succ).map f
        = (List.finRange k).map (fun i => f i.succ) := by
      simp only [List.map_map, Function.comp_def]
    rw [List.finRange_succ, List.map_cons, List.sum_cons, Fin.sum_univ_succ, e2,
      listSum_finRange k (fun i => f i.succ)]

/-- The length of the repeated mode list equals the sum of the mode occupations. -/
theorem bosonRows_length {m : ℕ} (s : Fin m → ℕ) :
    (bosonRows s).length = ∑ i, s i := by
  simp only [bosonRows, List.length_flatMap, List.length_replicate]
  exact listSum_finRange m s

/-- The square matrix formed by repeating the rows of `A` according to occupation `S`. -/
def bosonRowMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (S : FockOccupation m n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    A ((bosonRows (fun i => (S.1 i : ℕ))).get ⟨j.val, by
      have hlen : (bosonRows (fun i => (S.1 i : ℕ))).length = n :=
        (bosonRows_length (fun i => (S.1 i : ℕ))).trans S.2
      rw [hlen]
      exact j.isLt⟩) k

/-- The squared magnitude of the permanent of the repeated-row matrix, divided by the product of
occupation factorials. -/
noncomputable def bosonWeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (S : FockOccupation m n) : ℝ :=
  Complex.normSq (Matrix.permanent (bosonRowMatrix A S)) / ∏ i, (S.1 i : ℕ)!

/-- The finite set of occupations in which every mode contains at most one particle. -/
def collisionFreeFock (m n : ℕ) : Finset (FockOccupation m n) :=
  Finset.univ.filter (fun S => ∀ i, (S.1 i : ℕ) ≤ 1)

/-- The mode-count function with one particle in each of the first `n` modes of `2 * n` modes
and zero in the rest. -/
def oneStateFun (n : ℕ) (i : Fin (2 * n)) : Fin (n + 1) :=
  ⟨if (i : ℕ) < n then 1 else 0, by
    by_cases h : (i : ℕ) < n
    · simp only [if_pos h]; omega
    · simp only [if_neg h]; omega⟩

/-- The standard one-particle-per-mode count function has total occupation `n`. -/
theorem oneState_sum (n : ℕ) :
    ∑ i : Fin (2 * n), ((oneStateFun n i : Fin (n + 1)) : ℕ) = n := by
  have hpush : ∀ i : Fin (2 * n),
      ((oneStateFun n i : Fin (n + 1)) : ℕ) = if (i : ℕ) < n then (1 : ℕ) else 0 := by
    intro i
    by_cases h : (i : ℕ) < n <;> simp [oneStateFun, h]
  calc ∑ i : Fin (2 * n), ((oneStateFun n i : Fin (n + 1)) : ℕ)
      = ∑ i : Fin (2 * n), (if (i : ℕ) < n then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun i _ => hpush i
    _ = n := by
        rw [Fin.sum_univ_eq_sum_range (fun k => if k < n then (1 : ℕ) else 0) (2 * n),
          show 2 * n = n + n by rw [Nat.two_mul], Finset.sum_range_add]
        have h1 : ∑ x ∈ Finset.range n, (if x < n then (1 : ℕ) else 0) = n := by
          rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx)),
            Finset.sum_const, Finset.card_range]
          simp
        have h2 : ∑ x ∈ Finset.range n, (if n + x < n then (1 : ℕ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun x hx => if_neg ?_
          simp only [Finset.mem_range] at hx
          omega
        rw [h1, h2, Nat.add_zero]

/-- The occupation of `n` particles occupying the first `n` modes of `2 * n` modes once each. -/
def bosonOneState (n : ℕ) : FockOccupation (2 * n) n :=
  ⟨oneStateFun n, oneState_sum n⟩

end Qatlib.Concepts.BosonFock.BosonOperators
