/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRelatedKey13.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2: the related-key hiding function meets Simon's conditions

Rötteler–Steinwandt, *A note on quantum related-key attacks*, fixed
arXiv:1306.2301v2 (14 Nov 2013), Theorem 2, p. 6:

> For every `s ∈ {0,1}^k \ {0^k}` the function `f_s` defined above satisfies
> the conditions needed to apply Theorem 1, and the bound `t_{f_s}` can be
> chosen to be polynomial.

The paper (`f_s(x) = {E_x(~m), E_{s⊕x}(~m)}`, Section 3, p. 3) establishes the
Simon collision promise with the argument of pp. 3--4:

* if `E_x(~m) = E_{x'}(~m)` then `x = x'` by the plaintext-ciphertext
  uniqueness hypothesis, so no collapse occurs;
* if `E_x(~m) = E_{s⊕x'}(~m)` then `x = s ⊕ x'` for the same reason;
* the converse uses `s ⊕ (x' ⊕ s) = x'`.

`relatedKeyHidingFunction_simonPromise` records exactly this statement, and
`relatedKeyHidingFunction_pair_ne` records the paper's non-collapse remark.
`hidingEvalCost_poly` records the polynomial bound on `t_{f_s}` transcribed
from the cost ledger of pp. 4--6.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Papers.QRelatedKey13.MainResults.SourceModel

namespace Qatlib.Papers.QRelatedKey13.MainResults.HidingFunction

/-- Every Boolean vector is its own additive inverse, used for the paper's
`x' ⊕ s ⊕ s = x'` step (p. 4). -/
theorem add_self_booleanVec {k : ℕ} (s : BooleanVec k) : s + s = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  calc s i + s i = 2 * s i := by ring
    _ = 0 := by rw [h2, zero_mul]

/-- **Theorem 2 (Simon promise).** Fixed arXiv:1306.2301v2, Theorem 2, p. 6 and
the argument of pp. 3--4: if the key is uniquely determined by the tuple `~m`
(i.e. `K ↦ E_K(~m)` is injective, paper Section 2.1) and `s ≠ 0^k`, then the
hiding function `f_s(x) = {E_x(~m), E_{s⊕x}(~m)}` satisfies the Simon collision
promise with secret `s`: `f_s x = f_s y ↔ x = y ∨ x = y + s`. -/
theorem relatedKeyHidingFunction_simonPromise {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k)
    (hE : Function.Injective (fun K => E K m)) (_hs : s ≠ 0) :
    BooleanSimonPromise (relatedKeyHidingFunction E m s) s := by
  intro x y
  constructor
  · intro hxy
    have hx : E x m ∈ relatedKeyHidingFunction E m s y := by
      rw [← hxy]
      exact Finset.mem_insert_self _ _
    simp only [relatedKeyHidingFunction, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · exact Or.inl (hE h)
    · exact Or.inr (hE h)
  · rintro (rfl | hxy)
    · rfl
    · subst hxy
      show ({E (y + s) m, E ((y + s) + s) m} : Finset (BooleanVec (r * n))) =
        {E y m, E (y + s) m}
      have hss : (y + s) + s = y := by
        rw [add_assoc, add_self_booleanVec, add_zero]
      rw [hss]
      exact Finset.pair_comm _ _

/-- **Theorem 2 (no singleton collapse).** Fixed arXiv:1306.2301v2, p. 3: for
`s ≠ 0^k` the two values in `f_s(x)` are distinct, so each image is a genuine
two-element set, as the paper remarks before the reduction. -/
theorem relatedKeyHidingFunction_pair_ne {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k)
    (hE : Function.Injective (fun K => E K m)) (hs : s ≠ 0) (x : BooleanVec k) :
    E x m ≠ E (x + s) m := by
  intro h
  apply hs
  have h1 : x = x + s := hE h
  have h2 : x + 0 = x + s := by rw [add_zero]; exact h1
  have h3 : (0 : BooleanVec k) = s := add_left_cancel h2
  exact h3.symm

/-- **Theorem 2 (HSP form).** Fixed arXiv:1306.2301v2, Theorem 2, p. 6: the
promise is exactly the paper's "conditions needed to apply Theorem 1", i.e.
`f_s` hides the cyclic subgroup `{0, s}` of `BooleanVec k` in the sense of the
abelian hidden-subgroup problem (paper Section 2.2). -/
theorem relatedKeyHidingFunction_hidesSubgroup {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k)
    (hE : Function.Injective (fun K => E K m)) (hs : s ≠ 0) :
    HidesSubgroup (relatedKeyHidingFunction E m s) (booleanSimonSubgroup s) :=
  (booleanSimonPromise_iff_hidesSubgroup _ _).mp
    (relatedKeyHidingFunction_simonPromise E m s hE hs)

/-- **Theorem 2 (encoded Simon oracle).** Fixed arXiv:1306.2301v2, Theorem 2 and
Section 3, pp. 3--4: after the unique `2rn`-bit `(min,max)` encoding of the
unordered pair, `x ↦ (min, max)(E_x(~m), E_{s⊕x}(~m))` satisfies the same
Simon promise, now with the finite additive codomain
`BooleanVec (r·n) × BooleanVec (r·n)` used by the actual Simon execution. -/
theorem encodedRelatedKeyHidingFunction_simonPromise {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k)
    (hE : Function.Injective (fun K => E K m)) (_hs : s ≠ 0) :
    BooleanSimonPromise (encodedRelatedKeyHidingFunction E m s) s := by
  intro x y
  constructor
  · intro hxy
    have hset : ({E x m, E (x + s) m} : Finset (BooleanVec (r * n))) =
        {E y m, E (y + s) m} :=
      finset_eq_of_unorderedPairEncode_eq hxy
    have hx : E x m ∈ ({E y m, E (y + s) m} : Finset (BooleanVec (r * n))) := by
      rw [← hset]
      exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · exact Or.inl (hE h)
    · exact Or.inr (hE h)
  · rintro (rfl | hxy)
    · rfl
    · subst hxy
      show unorderedPairEncode (E (y + s) m) (E ((y + s) + s) m) =
        unorderedPairEncode (E y m) (E (y + s) m)
      have hss : (y + s) + s = y := by
        rw [add_assoc, add_self_booleanVec, add_zero]
      rw [hss]
      exact unorderedPairEncode_comm _ _

/-- **Theorem 2 (polynomial evaluation bound).** Fixed arXiv:1306.2301v2,
Theorem 2, p. 6 and Section 3, pp. 4--6: if one cipher evaluation on the
`r`-block tuple costs `cipherCost k`, and the tuple length `r` and block length
`n` are polynomially bounded in `k`, then the evaluation ledger
`t_{f_s} = 2 · cipherCost + 2 rn + 1` of `f_s` is polynomially bounded in `k`. -/
theorem hidingEvalCost_poly (cipherCost r n : ℕ → ℕ)
    (hc : PolyBounded cipherCost) (hr : PolyBounded r) (hn : PolyBounded n) :
    PolyBounded (fun k => hidingEvalCost (cipherCost k) (r k) (n k)) := by
  unfold hidingEvalCost
  have h1 : PolyBounded (fun k => 2 * cipherCost k) := PolyBounded.const_mul 2 hc
  have h2 : PolyBounded (fun k => r k * n k) := PolyBounded.mul hr hn
  have h3 : PolyBounded (fun k => 2 * (r k * n k)) := PolyBounded.const_mul 2 h2
  have h4 : PolyBounded (fun k => 2 * (r k * n k) + 1) :=
    PolyBounded.add h3 (PolyBounded.const 1)
  exact PolyBounded.add h1 h4

end Qatlib.Papers.QRelatedKey13.MainResults.HidingFunction
