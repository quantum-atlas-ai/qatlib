/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveInfo.NeedleSearch
import Qatlib.Foundations.PureStateMath.Reflection.Basic

/-!
# Classical query comparisons for singleton search

Deterministic query trees that locate every singleton target need a worst case budget of at
least `2^n - 1`. For finite probability mixtures of query trees, average success at least one
half gives the lower bound `2^n / 2 - 1`.

`classical_two_state_guess_counterexample` records that a fixed guess already has average
success one half on two states while making no queries. See [Grover1997].

## Main statements

* `classical_exact_query_lower`: A deterministic query tree locating every singleton target in
  `Reg n` with at most `M` queries satisfies `2^n ≤ M + 1`.
* `classical_half_success_query_lower`: A finite probability mixture of query trees with worst
  case budget `M` and average singleton success at least `1/2` satisfies `2^n / 2 - 1 ≤ M`.

## References

* [Grover, 1997][Grover1997]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdaptiveInfo.ClassicalDefs

namespace Qatlib.Papers.GroverSearch97.MainResults

/-- A deterministic query tree locating every singleton target in `Reg n` with at most `M`
queries satisfies `2^n ≤ M + 1`. See [Grover1997]. -/
theorem classical_exact_query_lower (n M : ℕ) (tree : QueryTree (Reg n) Bool (Reg n))
    (hcorrect : ∀ y, (run (needleOracle y) tree).1 = y)
    (hcost : ∀ y, (run (needleOracle y) tree).2 ≤ M) : 2 ^ n ≤ M + 1 := by
  simpa only [card_reg] using actual_needle_exact_lower tree M hcorrect hcost

/-- A finite probability mixture of query trees with worst case budget `M` and average singleton
success at least `1/2` satisfies `2^n / 2 - 1 ≤ M`. See [Grover1997]. -/
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

/-- On a two state register, the query tree that always guesses `w` has average singleton
success `1/2` and makes zero queries for every oracle. See [Grover1997]. -/
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
