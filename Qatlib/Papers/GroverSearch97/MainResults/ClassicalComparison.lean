/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.NeedleSearch
import Qatlib.Foundations.PureStateMath.Reflection.Basic

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

namespace Qatlib.Papers.GroverSearch97.MainResults

theorem classical_exact_query_lower (n M : ℕ) (tree : QueryTree (Reg n) Bool (Reg n))
    (hcorrect : ∀ y, (run (needleOracle y) tree).1 = y)
    (hcost : ∀ y, (run (needleOracle y) tree).2 ≤ M) : 2 ^ n ≤ M + 1 := by
  simpa only [card_reg] using actual_needle_exact_lower tree M hcorrect hcost

theorem classical_half_success_query_lower {S : Type} [Fintype S]
    (n M : ℕ) (weight : S → ℝ) (tree : S → QueryTree (Reg n) Bool (Reg n))
    (hw : ∀ s, 0 ≤ weight s) (hmass : ∑ s, weight s = 1)
    (hcost : ∀ s y, (run (needleOracle y) (tree s)).2 ≤ M)
    (hsuccess : (1 / 2 : ℝ) ≤ ∑ s, weight s * needleSuccess (tree s)) :
    (2 ^ n : ℝ) / 2 - 1 ≤ M := by
  have hb := randomized_needle_success_upper weight tree M hw hmass hcost
  rw [card_reg, Nat.cast_pow, Nat.cast_ofNat] at hb
  have hden : (0 : ℝ) < 2 ^ n := by positivity
  have h := (le_div_iff₀ hden).mp (hsuccess.trans hb)
  linarith

theorem classical_two_state_guess_counterexample (w : Reg 1) :
    needleSuccess (I := Reg 1) (QueryTree.leaf w) = (1 / 2 : ℝ) ∧
      ∀ y : Reg 1, (run (needleOracle y) (QueryTree.leaf w)).2 = 0 := by
  constructor
  · have hf : Finset.univ.filter (fun y : Reg 1 => w = y) = {w} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact eq_comm
    change ((Finset.univ.filter (fun y : Reg 1 => w = y)).card : ℝ) /
      Fintype.card (Reg 1) = 1 / 2
    rw [hf]
    norm_num
  · intro y
    rfl

end Qatlib.Papers.GroverSearch97.MainResults
