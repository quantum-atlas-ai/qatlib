/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Counterfeit10.MainResults.ParityRestrictedIP
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# The balance oracle (Counterfeit10, §1 and §3)

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Section 1 (definition of the
`B`-oracle) and Section 3 (weight schemes).

A `B`-oracle query is a string `q ∈ {0,1,-1}^N` with equally many `1`s and `-1`s.  We model it by
its two *pans*, two disjoint equally sized subsets of the `N` coins.  For an oracle string `x` the
answer is "balanced" when the number of counterfeit (`true`) coins on the left pan equals the
number on the right pan; otherwise it "tilts".  Writing `q_i = 1` on the left, `q_i = -1` on the
right and `q_i = 0` elsewhere, this is exactly the paper's condition `q · x = 0` (balanced)
versus `q · x ≠ 0` (tilted).

The main structural fact recorded here is that the `B`-oracle cannot distinguish `x` from its
pointwise complement `x̄`, because complementing every coin leaves both pan counts equally reduced.
This is the paper's justification for assuming `k < N/2`.
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- A weighing: two disjoint, equally sized sets of coins placed on the two pans. -/
structure PanPair (N : ℕ) where
  /-- The coins placed on the left pan. -/
  left : Finset (Fin N)
  /-- The coins placed on the right pan. -/
  right : Finset (Fin N)
  /-- The pans are disjoint. -/
  disjoint : Disjoint left right
  /-- Both pans carry the same number of coins. -/
  equalSize : left.card = right.card

/-- The number of counterfeit (`true`) coins of `x` that lie on the pan set `s`. -/
def falseIn {N : ℕ} (x : CoinString N) (s : Finset (Fin N)) : ℕ :=
  (s.filter fun i => x i = true).card

/-- The `B`-oracle answers "balanced" when both pans carry equally many counterfeit coins. -/
def balanced {N : ℕ} (x : CoinString N) (p : PanPair N) : Prop :=
  falseIn x p.left = falseIn x p.right

/-- The `B`-oracle tilts exactly when the counterfeit counts of the two pans differ. -/
def tilted {N : ℕ} (x : CoinString N) (p : PanPair N) : Prop :=
  ¬ balanced x p

/-- The pan sets together with their complement cover every coin. -/
def rest {N : ℕ} (p : PanPair N) : Finset (Fin N) :=
  Finset.univ \ (p.left ∪ p.right)

/-- Counting counterfeit coins on a pan set as a sum of per-coin indicators. -/
lemma falseIn_eq_sum {N : ℕ} (x : CoinString N) (s : Finset (Fin N)) :
    falseIn x s = ∑ i ∈ s, (if x i = true then 1 else 0) := by
  rw [falseIn, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The number of counterfeit coins on a pan set plus the number of fair coins there is the pan
size; equivalently, complementing the oracle complements the pan count. -/
lemma falseIn_compl_add {N : ℕ} (x : CoinString N) (s : Finset (Fin N)) :
    falseIn (compl x) s + falseIn x s = s.card := by
  rw [falseIn_eq_sum, falseIn_eq_sum, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold compl
  cases hx : x i <;> simp

/-- Complementing every coin leaves both pan counts equally reduced, hence preserves the answer
of the `B`-oracle: the model cannot distinguish `x` from `x̄`. -/
theorem balanced_compl {N : ℕ} (x : CoinString N) (p : PanPair N) :
    balanced (compl x) p ↔ balanced x p := by
  unfold balanced
  have h1 := falseIn_compl_add x p.left
  have h2 := falseIn_compl_add x p.right
  have he := p.equalSize
  constructor <;> intro h <;> omega

/-- Tilt is likewise complement-invariant. -/
theorem tilted_compl {N : ℕ} (x : CoinString N) (p : PanPair N) :
    tilted (compl x) p ↔ tilted x p := by
  unfold tilted
  rw [balanced_compl]

/-- An oracle with no counterfeit coin balances every weighing. -/
theorem balanced_zeroString {N : ℕ} (p : PanPair N) :
    balanced (zeroString (N := N)) p := by
  unfold balanced falseIn zeroString
  simp

/-- Complementary oracles have weights summing to `N`; this is why `x` and `x̄` are the same
`B`-oracle input and the paper restricts to `k < N/2`. -/
theorem weight_and_compl {N : ℕ} (x : CoinString N) :
    coinWeight x + coinWeight (compl x) = N := by
  rw [coinWeight_eq_sum x, coinWeight_eq_sum (compl x), ← Finset.sum_add_distrib]
  have hstep : ∀ i : Fin N,
      ((if x i then (1 : ℕ) else 0) + (if compl x i then 1 else 0)) = 1 := by
    intro i
    unfold compl
    cases hx : x i <;> simp
  calc (∑ i : Fin N, ((if x i then (1 : ℕ) else 0) + (if compl x i then 1 else 0)))
      = ∑ _i : Fin N, 1 := Finset.sum_congr rfl (fun i _ => hstep i)
    _ = N := by simp

end Qatlib.Papers.Counterfeit10.MainResults
