/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-! # Exact multiplicities in the actual repeated-mode list

Demand: LinearOptics10 general polynomial coefficient expansion. These
concrete list/count arguments are rederived from the locked public
BosonDistributionNormalizationThec helpers (Qatlib9eb6a0d). They do not
invoke private mangled declarations or assume a coefficient identity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.BosonFock.BosonOperators.RowFibers
open Qatlib.Concepts.BosonFock.BosonOperators

/-- Summing the indicator of a list value over all positions gives its count. -/
theorem sumGetCount {α : Type*} [DecidableEq α] (L : List α) (a : α) :
    ∑ p : Fin L.length, (if L.get p = a then (1 : ℕ) else 0) = L.count a := by
  induction L with
  | nil => simp
  | cons x t ih =>
      show (∑ p : Fin (t.length + 1), (if (x :: t).get p = a then (1 : ℕ) else 0))
        = List.count a (x :: t)
      rw [Fin.sum_univ_succ]
      have e0 : (if (x :: t).get 0 = a then (1 : ℕ) else 0)
          = (if x = a then (1 : ℕ) else 0) := rfl
      have es : ∀ p : Fin t.length,
          (if (x :: t).get (Fin.succ p) = a then (1 : ℕ) else 0)
            = (if t.get p = a then (1 : ℕ) else 0) := fun p => rfl
      rw [e0, Finset.sum_congr rfl (fun p _ => es p), ih, List.count_cons]
      by_cases hxa : x = a
      · subst hxa; simp [Nat.add_comm]
      · simp [hxa]

/-- Mode `i₀` occurs in the repeated mode list exactly as many times as its occupation count. -/
theorem rowCount {m : ℕ} (s : Fin m → ℕ) (i₀ : Fin m) :
    (bosonRows s).count i₀ = s i₀ := by
  induction m with
  | zero => exact absurd i₀.isLt (Nat.not_lt_zero _)
  | succ m ih =>
      have hsplit : bosonRows s = List.replicate (s 0) (0 : Fin (m + 1))
          ++ List.map (Fin.succ : Fin m → Fin (m + 1))
              (bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j))) := by
        have hfun1 : (fun j : Fin m =>
              List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j))
                ((Fin.succ : Fin m → Fin (m + 1)) j))
            = (fun j : Fin m => List.map (Fin.succ : Fin m → Fin (m + 1))
                (List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j)) j)) :=
          funext fun j => List.map_replicate.symm
        rw [bosonRows, List.finRange_succ, List.flatMap_cons, List.flatMap_map, hfun1,
          ← List.map_flatMap,
          show (List.finRange m).flatMap
              (fun j : Fin m => List.replicate (s ((Fin.succ : Fin m → Fin (m + 1)) j)) j)
            = bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j)) from rfl]
      rw [hsplit, List.count_append]
      rcases Fin.eq_zero_or_eq_succ i₀ with rfl | ⟨j, rfl⟩
      · have h0 : (List.map (Fin.succ : Fin m → Fin (m + 1))
            (bosonRows (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j)))).count
            (0 : Fin (m + 1)) = 0 :=
          List.count_eq_zero_of_not_mem (fun hmem => by
            rcases List.mem_map.mp hmem with ⟨p, _, hp⟩
            exact Fin.succ_ne_zero p hp)
        rw [List.count_replicate_self, h0, Nat.add_zero]
      · rw [List.count_map_of_injective _ (Fin.succ : Fin m → Fin (m + 1))
          (Fin.succ_injective _) j]
        have hne : (List.replicate (s 0) (0 : Fin (m + 1))).count
            ((Fin.succ : Fin m → Fin (m + 1)) j) = 0 := by
          refine List.count_eq_zero_of_not_mem (fun hmem => ?_)
          rw [List.mem_replicate] at hmem
          exact Fin.succ_ne_zero j hmem.2
        rw [hne, Nat.zero_add, ih (fun j : Fin m => s ((Fin.succ : Fin m → Fin (m + 1)) j))]


end Qatlib.Concepts.BosonFock.BosonOperators.RowFibers
