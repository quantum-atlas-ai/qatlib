/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Qatlib.Papers.SingleQuery97.MainResults.CoinProgram

/-!
# Adaptive classical query bounds for coin weighing

`weighing` records the number of marked coins in a queried subset as an answer in `Fin (n + 1)`.
Exact recovery by a finite adaptive query tree forces both a leaf-count bound and a logarithmic
lower bound on the number of queries, which can be compared with the explicit one-query quantum
word. See [TerhalSmolin1998] for the source development.

## Main statements

* `coin_classical_card`: bounds `2 ^ n` by `(n + 1) ^ depth tree` for a correct tree.
* `actual_coin_classical_log`: bounds any uniform executed-query budget below by `n / log₂ (n +
  1)`.
* `coin_query_comparison`: combines the classical lower bound with the quantum word query count.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.SingleQuery97.MainResults.ClassicalAdaptive

open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs
open DatabaseDefs

/-- The subset-weighing answer, equal to the Hamming weight of the intersection of query `x` and
database `y`, as an element of `Fin (n + 1)`. -/
def weighing {n : ℕ} (y x : DbVec n) : Fin (n+1) :=
  ⟨weight (wedge x y), Nat.lt_succ_of_le (weight_le_length _)⟩

/-- Any adaptive weighing tree that recovers every `n`-bit database satisfies `2 ^ n ≤ (n + 1) ^
depth tree`. -/
theorem coin_classical_card (n : ℕ) (tree : QueryTree (DbVec n) (Fin (n+1)) (DbVec n))
    (hcorrect : ∀ y, (run (weighing y) tree).1 = y) :
    2^n ≤ (n+1)^(depth tree) := by
  simpa [DbVec] using exact_recovery_card weighing tree hcorrect

/-- For `n > 0`, a correct adaptive weighing tree has depth at least `n / log₂ (n + 1)`. -/
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

/-- For `n > 0`, any uniform bound `M` on the executed queries of a correct adaptive weighing
tree satisfies `n / log₂ (n + 1) ≤ M`. -/
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

/-- The bounded natural-number weighing answer and the cyclic answer used by `CoinProgram` have
the same numerical value. -/
theorem weighing_source_value {n : ℕ} (y x : DbVec n) :
    (weighing y x).val = (CoinProgram.weighing y x).val := by
  change weight (wedge x y) = (weight (wedge x y) : ZMod (registerN n)).val
  rw [ZMod.val_natCast, weight_mod_registerN_eq]

/-- For `n > 0`, the quantum coin word uses one query, whereas any uniform executed-query bound
`M` for a correct classical adaptive tree is at least `n / log₂ (n + 1)`. See
[TerhalSmolin1998]. -/
theorem coin_query_comparison (n : ℕ) (hn : 0<n)
    (tree : QueryTree (DbVec n) (Fin (n+1)) (DbVec n)) (M : ℕ)
    (hcorrect : ∀ y, (run (weighing y) tree).1 = y)
    (hcost : ∀ y, (run (weighing y) tree).2 ≤ M) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount (CoinProgram.word n) = 1 ∧
      (n:ℝ)/Real.logb 2 (n+1) ≤ M :=
  ⟨(CoinProgram.word_resources n).1, actual_coin_classical_log n hn tree M hcorrect hcost⟩

/-- A correct adaptive tree identifying one of `2 ^ q` labels through binary answers needs a
uniform executed-query budget of at least `q`. See [TerhalSmolin1998]. -/
theorem binary_index_lower {I : Type} (q : ℕ) (oracle : Fin (2^q) → I → Bool)
    (tree : QueryTree I Bool (Fin (2^q))) (M : ℕ)
    (hcorrect : ∀ y, (run (oracle y) tree).1 = y)
    (hcost : ∀ y, (run (oracle y) tree).2 ≤ M) : q ≤ M := by
  have hc : 2^q ≤ 2^M := by
    simpa using actual_exact_recovery_card oracle tree M hcorrect hcost
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc

end Qatlib.Papers.SingleQuery97.MainResults.ClassicalAdaptive
