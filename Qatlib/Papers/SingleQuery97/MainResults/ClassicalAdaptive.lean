/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Qatlib.Papers.SingleQuery97.MainResults.CoinProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.SingleQuery97.MainResults.ClassicalAdaptive

open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
open DatabaseDefs

def weighing {n : ℕ} (y x : DbVec n) : Fin (n+1) :=
  ⟨weight (wedge x y), Nat.lt_succ_of_le (weight_le_length _)⟩

theorem coin_classical_card (n : ℕ) (tree : QueryTree (DbVec n) (Fin (n+1)) (DbVec n))
    (hcorrect : ∀ y, (run (weighing y) tree).1 = y) :
    2^n ≤ (n+1)^(depth tree) := by
  simpa [DbVec] using exact_recovery_card weighing tree hcorrect

theorem coin_classical_log (n : ℕ) (hn : 0<n)
    (tree : QueryTree (DbVec n) (Fin (n+1)) (DbVec n))
    (hcorrect : ∀ y, (run (weighing y) tree).1 = y) :
    (n:ℝ)/Real.logb 2 (n+1) ≤ depth tree := by
  have hc : (2:ℝ)^n ≤ (n+1:ℝ)^(depth tree) := by
    exact_mod_cast coin_classical_card n tree hcorrect
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^n) hc
  rw [Real.log_pow,Real.log_pow] at hl
  have h2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hN : (0:ℝ)<Real.log (n+1) := Real.log_pos (by exact_mod_cast (show 1<n+1 by omega))
  rw [Real.logb, div_le_iff₀ (div_pos hN h2), ← mul_div_assoc, le_div_iff₀ h2]
  exact hl

theorem actual_coin_classical_log (n : ℕ) (hn : 0<n)
    (tree : QueryTree (DbVec n) (Fin (n+1)) (DbVec n)) (M : ℕ)
    (hcorrect : ∀ y, (run (weighing y) tree).1 = y)
    (hcost : ∀ y, (run (weighing y) tree).2 ≤ M) :
    (n:ℝ)/Real.logb 2 (n+1) ≤ M := by
  have hc : (2:ℝ)^n ≤ (n+1:ℝ)^M := by
    exact_mod_cast (show 2^n ≤ (n+1)^M from by
      simpa [DbVec] using actual_exact_recovery_card weighing tree M hcorrect hcost)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^n) hc
  rw [Real.log_pow,Real.log_pow] at hl
  have h2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hN : (0:ℝ)<Real.log (n+1) := Real.log_pos (by exact_mod_cast (show 1<n+1 by omega))
  rw [Real.logb, div_le_iff₀ (div_pos hN h2), ← mul_div_assoc, le_div_iff₀ h2]
  exact hl

theorem weighing_source_value {n : ℕ} (y x : DbVec n) :
    (weighing y x).val = (CoinProgram.weighing y x).val := by
  change weight (wedge x y) = (weight (wedge x y) : ZMod (registerN n)).val
  rw [ZMod.val_natCast, weight_mod_registerN_eq]

theorem coin_query_comparison (n : ℕ) (hn : 0<n)
    (tree : QueryTree (DbVec n) (Fin (n+1)) (DbVec n)) (M : ℕ)
    (hcorrect : ∀ y, (run (weighing y) tree).1 = y)
    (hcost : ∀ y, (run (weighing y) tree).2 ≤ M) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (CoinProgram.word n) = 1 ∧
      (n:ℝ)/Real.logb 2 (n+1) ≤ M :=
  ⟨(CoinProgram.word_resources n).1, actual_coin_classical_log n hn tree M hcorrect hcost⟩

theorem binary_index_lower {I : Type} (q : ℕ) (oracle : Fin (2^q) → I → Bool)
    (tree : QueryTree I Bool (Fin (2^q))) (M : ℕ)
    (hcorrect : ∀ y, (run (oracle y) tree).1 = y)
    (hcost : ∀ y, (run (oracle y) tree).2 ≤ M) : q ≤ M := by
  have hc : 2^q ≤ 2^M := by
    simpa using actual_exact_recovery_card oracle tree M hcorrect hcost
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc

end Qatlib.Papers.SingleQuery97.MainResults.ClassicalAdaptive
