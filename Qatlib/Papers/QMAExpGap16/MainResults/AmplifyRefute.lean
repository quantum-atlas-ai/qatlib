/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QMAExpGap16.MainResults.SourceModel
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMAExpGap16.MainResults

open Qatlib.Papers.QMAExpGap16.MainResults

/-- An empty-promise zero-budget protocol refutes the legacy amplification contract.
For k=0, r=1 and gap 1/2, its asserted workspace upper bound is strictly negative. -/
theorem amp8_counter :
    ∃ (t k m : ℕ → ℕ) (c s : ℕ → ℝ) (r : ℕ → ℕ) (L : PromiseProblem),
      (∀ n, 1 ≤ r n) ∧ InBoundedQMA t k m c s L ∧
      ¬ (∃ t' k' : ℕ → ℕ,
        (∃ Ct : ℝ, 0 < Ct ∧ ∀ n,
          (t' n : ℝ) ≤ Ct * (r n : ℝ) * (t n : ℝ) * (c n - s n)) ∧
        (∃ Ck : ℝ, 0 < Ck ∧ ∀ n,
          (k' n : ℝ) ≤ Ck * ((k n : ℝ) + (r n : ℝ) * Real.log (c n - s n))) ∧
        InBoundedQMA t' k' m
          (fun n => 1 - (2 : ℝ) ^ (-((r n : ℤ))))
          (fun n => (2 : ℝ) ^ (-((r n : ℤ)))) L) := by
  let L : PromiseProblem := ⟨∅, ∅⟩
  have hL : InBoundedQMA (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 1) (fun _ => (1 / 2 : ℝ)) L := by
    refine ⟨{
      time := fun _ => 0
      workspace := fun _ => 0
      witness := fun _ => 0
      accept := fun _ _ => False
      accept_nonneg := by intro x q h; exact h.elim
      accept_le_one := by intro x q h; exact h.elim
    }, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact le_rfl
    · intro n
      exact le_rfl
    · intro n
      exact le_rfl
    · intro x hx
      exact False.elim hx
    · intro x hx
      exact False.elim hx
  refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 0),
    (fun _ => 1), (fun _ => (1 / 2 : ℝ)), (fun _ => 1), L,
    (by intro n; exact le_rfl), hL, ?_⟩
  rintro ⟨t', k', _ht, ⟨Ck, hCk, hk⟩, _hamp⟩
  have hb := hk 0
  norm_num at hb
  have hlog : Real.log (1 / 2 : ℝ) < 0 :=
    Real.log_neg (by norm_num) (by norm_num)
  have hnegative : Ck * Real.log (1 / 2 : ℝ) < 0 :=
    mul_neg_of_pos_of_neg hCk hlog
  have hnonnegative : (0 : ℝ) ≤ (k' 0 : ℝ) := Nat.cast_nonneg _
  linarith

end Qatlib.Papers.QMAExpGap16.MainResults
