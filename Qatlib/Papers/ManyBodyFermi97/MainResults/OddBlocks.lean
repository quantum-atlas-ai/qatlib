/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodyFermi97.MainResults.ParallelBlocks
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ManyBodyFermi97.MainResults.OddBlocks
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

open ParallelBlocks

def oddSite (k : ℕ) (x : Bool × Fin (k-1)) : Fin (2*k) :=
  ⟨2*x.2.val + 1 + (if x.1 then 1 else 0), by
    have h := x.2.isLt
    split <;> omega⟩

theorem oddSite_injective (k : ℕ) : Function.Injective (oddSite k) := by
  intro x y h
  have hv := congrArg Fin.val h
  rcases x with ⟨b,a⟩
  rcases y with ⟨d,c⟩
  cases b <;> cases d <;>
    simp only [oddSite, Bool.false_eq_true, if_false, if_true] at hv
  all_goals first
    | omega
    | (have hac : a = c := Fin.ext (by omega); subst c; rfl)

theorem oddSite_surjective_on (k : ℕ) (hk : 1 ≤ k) (i : Fin (2*k))
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ 2*k - 2) :
    ∃ x : Bool × Fin (k-1), oddSite k x = i := by
  refine ⟨(decide (i.val % 2 = 0), ⟨(i.val - 1) / 2, by omega⟩), Fin.ext ?_⟩
  simp only [oddSite]
  by_cases h : i.val % 2 = 0
  · simp [h]; omega
  · simp [h]; omega

theorem oddSite_ne_zero (k : ℕ) (hk : 1 ≤ k) (x : Bool × Fin (k-1)) :
    oddSite k x ≠ (⟨0, by omega⟩ : Fin (2*k)) := by
  intro h
  have hv := congrArg Fin.val h
  rcases x with ⟨b,a⟩
  cases b <;> simp only [oddSite, Bool.false_eq_true, if_false, if_true] at hv
  all_goals omega

theorem oddSite_ne_last (k : ℕ) (x : Bool × Fin (k-1)) :
    oddSite k x ≠ ⟨2*k - 1, by have := x.2.isLt; omega⟩ := by
  intro h
  have hv := congrArg Fin.val h
  rcases x with ⟨b,a⟩
  cases b <;> simp only [oddSite, Bool.false_eq_true, if_false, if_true] at hv
  all_goals omega

theorem oddBlocks_interior (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (a : Fin (k-1)) :
    oddBlocks (2*k) t ⟨2*a.val+1, by have := a.isLt; omega⟩
      ⟨2*a.val+2, by have := a.isLt; omega⟩ = (t : ℂ) := by
  unfold oddBlocks chainHopping
  have hne : (2*a.val+1)/2 ≠ (2*a.val+2)/2 := by omega
  rw [if_pos hne]
  rw [if_pos (by
    left
    simp only [Fin.val_mk]
    push_cast
    omega)]

theorem oddBlocks_diagonal_zero (m : ℕ) (t : ℝ) (i : Fin m) :
    oddBlocks m t i i = 0 := by
  simp [oddBlocks, chainHopping]

theorem chainHopping_eq_zero_of_not_adj (m : ℕ) (t : ℂ) {i j : Fin m}
    (h : ¬ ((i.val : ℤ) + 1 = (j.val : ℤ) ∨ (j.val : ℤ) + 1 = (i.val : ℤ))) :
    chainHopping m t i j = 0 := by
  unfold chainHopping
  rw [if_neg h]

theorem oddBlocks_zero_site (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (j : Fin (2*k)) :
    oddBlocks (2*k) t (⟨0, by omega⟩ : Fin (2*k)) j = 0 := by
  by_cases h : ((⟨0, by omega⟩ : Fin (2*k)).val / 2 = j.val / 2)
  · unfold oddBlocks
    rw [if_neg (by omega)]
  · unfold oddBlocks
    rw [if_pos (by omega)]
    refine chainHopping_eq_zero_of_not_adj _ _ (by
      have h0 : (((⟨0, by omega⟩ : Fin (2*k))).val : ℤ) = 0 := by simp
      rw [h0]
      omega)

theorem oddBlocks_zero_last (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (j : Fin (2*k)) :
    oddBlocks (2*k) t ⟨2*k - 1, by omega⟩ j = 0 := by
  by_cases h : ((⟨2*k - 1, by omega⟩ : Fin (2*k)).val / 2 = j.val / 2)
  · unfold oddBlocks
    rw [if_neg (by omega)]
  · unfold oddBlocks
    rw [if_pos (by omega)]
    refine chainHopping_eq_zero_of_not_adj _ _ (by
      have hlast : (((⟨2*k - 1, by omega⟩ : Fin (2*k))).val : ℤ) = (k : ℤ) * 2 - 1 := by
        simp; omega
      rw [hlast]
      omega)

def oddWord (k : ℕ) (t time : ℝ) : Circuit (Bool × Fin (k-1)) :=
  word (k-1) t time

theorem oddWord_correct (k : ℕ) (t time : ℝ) :
    IsUnitaryCircuit (oddWord k t time) ∧
      QueryCount (oddWord k t time) = 0 ∧
      GateCount (oddWord k t time) = 1 := by
  unfold oddWord
  exact (word_correct (k-1) t time (fun _ => 0)).2

theorem block_step_cost_le {q : ℕ} (hq : 1 ≤ q) :
    firstQuantHubbardStepCost q ≤ 14 * q ^ 2 :=
  firstQuantHubbardStepCost_bound hq

end Qatlib.Papers.ManyBodyFermi97.MainResults.OddBlocks
