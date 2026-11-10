/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

namespace Qatlib.Concepts.BosonFock.BosonOperators

open scoped BigOperators Nat

def FockOccupation (m n : ℕ) : Type := {s : Fin m → Fin (n + 1) // ∑ i, (s i : ℕ) = n}

instance {m n : ℕ} : Fintype (FockOccupation m n) := by
  unfold FockOccupation
  exact Subtype.fintype _

open Classical in
noncomputable instance {m n : ℕ} : DecidableEq (FockOccupation m n) := by
  unfold FockOccupation
  exact Classical.decEq _

def bosonRows {m : ℕ} (s : Fin m → ℕ) : List (Fin m) :=
  (List.finRange m).flatMap (fun i => List.replicate (s i) i)

private theorem listSum_finRange : ∀ (m : ℕ) (f : Fin m → ℕ),
    ((List.finRange m).map f).sum = ∑ i, f i
  | 0, _ => by simp
  | k + 1, f => by
    have e2 : ((List.finRange k).map Fin.succ).map f
        = (List.finRange k).map (fun i => f i.succ) := by
      simp only [List.map_map, Function.comp_def]
    rw [List.finRange_succ, List.map_cons, List.sum_cons, Fin.sum_univ_succ, e2,
      listSum_finRange k (fun i => f i.succ)]

theorem bosonRows_length {m : ℕ} (s : Fin m → ℕ) :
    (bosonRows s).length = ∑ i, s i := by
  simp only [bosonRows, List.length_flatMap, List.length_replicate]
  exact listSum_finRange m s

def bosonRowMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (S : FockOccupation m n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    A ((bosonRows (fun i => (S.1 i : ℕ))).get ⟨j.val, by
      have hlen : (bosonRows (fun i => (S.1 i : ℕ))).length = n :=
        (bosonRows_length (fun i => (S.1 i : ℕ))).trans S.2
      rw [hlen]
      exact j.isLt⟩) k

noncomputable def bosonWeight {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (S : FockOccupation m n) : ℝ :=
  Complex.normSq (Matrix.permanent (bosonRowMatrix A S)) / ∏ i, (S.1 i : ℕ)!

def collisionFreeFock (m n : ℕ) : Finset (FockOccupation m n) :=
  Finset.univ.filter (fun S => ∀ i, (S.1 i : ℕ) ≤ 1)

def oneStateFun (n : ℕ) (i : Fin (2 * n)) : Fin (n + 1) :=
  ⟨if (i : ℕ) < n then 1 else 0, by
    by_cases h : (i : ℕ) < n
    · simp only [if_pos h]; omega
    · simp only [if_neg h]; omega⟩

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

def bosonOneState (n : ℕ) : FockOccupation (2 * n) n :=
  ⟨oneStateFun n, oneState_sum n⟩

end Qatlib.Concepts.BosonFock.BosonOperators
