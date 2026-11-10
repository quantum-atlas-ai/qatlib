/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.Policy

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators

namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

theorem bestProduct_attained (p : ℝ≥0) (S C : ℕ) :
    ∃ widths : Fin S → ℕ, (∑ i, widths i) ≤ C ∧
      bestProduct p S C = ∏ i, (1-p^(widths i)) := by
  induction S generalizing C with
  | zero => exact ⟨Fin.elim0, by simp, by simp [bestProduct]⟩
  | succ S ih =>
    obtain ⟨n,hn,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k : Fin (C+1) => (1-p^k.val) * bestProduct p S (C-k.val))
    obtain ⟨tail,ht,hprod⟩ := ih (C-n.val)
    refine ⟨Fin.cons n.val tail, ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hnC : n.val ≤ C := Nat.le_of_lt_succ n.isLt
      omega
    · change Finset.univ.sup' _ _ = _
      rw [he, hprod, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

theorem allocation_width_le {S C : ℕ} (widths : Fin S → ℕ)
    (h : (∑ i, widths i) ≤ C) (i : Fin S) : widths i ≤ C :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
