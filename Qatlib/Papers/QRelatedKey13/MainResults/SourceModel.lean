/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonSampling

set_option backward.isDefEq.respectTransparency false

/-!
# Source model: quantum related-key attacks

Rötteler–Steinwandt, *A note on quantum related-key attacks*, fixed
arXiv:1306.2301v2 (14 Nov 2013).

This file fixes only the objects the paper uses to state Theorem 2 and the main
result of Section 3:

* `CipherTuple k r n` is a block cipher evaluated on an `r`-block message tuple
  `~m ∈ {0,1}^{r n}` (paper Section 2, p. 2, and the notation `E_K(~m)` of
  Section 3, p. 3);
* `relatedKeyHidingFunction E m s` is exactly the paper's
  `f_s(x) = {E_x(~m), E_{s⊕x}(~m)}` (paper Section 3, p. 3);
* `unorderedPairEncode` is the unique `(min,max)` representation of the
  unordered pair as a `2 r n`-bit string (paper Section 3, pp. 3--4);
* `PolyBounded` and its closure lemmas are the Lean reading of "the bound
  `t_{f_s}` can be chosen to be polynomial" (paper Theorem 2, p. 6).

The linear order used for `min`/`max` is the paper's "interpret elements of
`{0,1}^{r n}` as unsigned integers" order, modelled here by the canonical
enumeration index of the finite type `BooleanVec (r n)`.  Any injective
`BooleanVec N → ℕ` gives the same encoding contract, and the proofs only use
totality, antisymmetry and injectivity of the index, not its arithmetic shape.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QRelatedKey13.MainResults.SourceModel

/-- A block cipher evaluated on an `r`-block message tuple. The key and the
related-key XOR mask both live in `BooleanVec k`; plaintext and ciphertext
tuples are `r · n` bit strings, `n` being the block length (paper Section 2,
p. 2: `E_K(~m) = (E_K(m_1), ..., E_K(m_r)) ∈ {0,1}^{rn}`). -/
abbrev CipherTuple (k r n : ℕ) :=
  BooleanVec k → BooleanVec (r * n) → BooleanVec (r * n)

/-- The paper's hiding function `f_s(x) = {E_x(~m), E_{s⊕x}(~m)}` of Section 3
(p. 3), as the unordered two-element family of ciphertext tuples. -/
def relatedKeyHidingFunction {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k) :
    BooleanVec k → Finset (BooleanVec (r * n)) :=
  fun x => {E x m, E (x + s) m}

/-- Canonical enumeration index of a Boolean vector. It plays the role of the
paper's "interpret elements in `{0,1}^{rn}` as unsigned integers" and hence
supplies an injective total order on bit strings (paper Section 3, p. 3). -/
def booleanVecIndex {N : ℕ} (v : BooleanVec N) : ℕ :=
  (Fintype.equivFin (BooleanVec N) v : ℕ)

/-- The index is injective, so it induces a genuine linear order. -/
theorem booleanVecIndex_injective {N : ℕ} :
    Function.Injective (booleanVecIndex (N := N)) := by
  intro a b h
  exact (Fintype.equivFin (BooleanVec N)).injective (Fin.ext h)

/-- The unique ordered `(min c, max c')` representation of the unordered pair
`{c, c'}` (paper Section 3, p. 3: "store the ordered pair `(min(c,c'), max(c,c'))`
as its unique `k_0`-bit representation"). -/
def unorderedPairEncode {N : ℕ} (c c' : BooleanVec N) : BooleanVec N × BooleanVec N :=
  if booleanVecIndex c ≤ booleanVecIndex c' then (c, c') else (c', c)

/-- The pair encoding ignores the order of its arguments: `f_s` is well defined
as a function into unordered pairs (paper Section 3, p. 3). -/
theorem unorderedPairEncode_comm {N : ℕ} (c c' : BooleanVec N) :
    unorderedPairEncode c c' = unorderedPairEncode c' c := by
  unfold unorderedPairEncode
  by_cases h : booleanVecIndex c ≤ booleanVecIndex c'
  · rw [if_pos h]
    by_cases h' : booleanVecIndex c' ≤ booleanVecIndex c
    · rw [if_pos h']
      have hc : c = c' := booleanVecIndex_injective (Nat.le_antisymm h h')
      rw [hc]
    · rw [if_neg h']
  · rw [if_neg h]
    have h' : booleanVecIndex c' ≤ booleanVecIndex c :=
      Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [if_pos h']

/-- Equality of the `(min,max)` encodings forces equality of the underlying
unordered pairs. This is the encoding's uniqueness property used to transfer
collisions of the encoded oracle back to `f_s` (paper Section 3, p. 3). -/
theorem finset_eq_of_unorderedPairEncode_eq {N : ℕ} {c c' a b : BooleanVec N}
    (h : unorderedPairEncode c c' = unorderedPairEncode a b) :
    ({c, c'} : Finset (BooleanVec N)) = {a, b} := by
  unfold unorderedPairEncode at h
  split_ifs at h
  · injection h with h1 h2
    rw [h1, h2]
  · injection h with h1 h2
    rw [h1, h2]
    exact Finset.pair_comm b a
  · injection h with h1 h2
    rw [h1, h2]
    exact Finset.pair_comm b a
  · injection h with h1 h2
    rw [h1, h2]

/-- The encoded hiding function: the paper's `f_s`, read through the unique
`2rn`-bit `(min,max)` representation so that it can serve as a Simon oracle
with a finite additive codomain (paper Section 3, pp. 3--4). -/
def encodedRelatedKeyHidingFunction {k r n : ℕ} (E : CipherTuple k r n)
    (m : BooleanVec (r * n)) (s : BooleanVec k) :
    BooleanVec k → BooleanVec (r * n) × BooleanVec (r * n) :=
  fun x => unorderedPairEncode (E x m) (E (x + s) m)

/-- A natural-valued function is bounded by some polynomial in the key length. -/
def PolyBounded (t : ℕ → ℕ) : Prop :=
  ∃ C D : ℕ, ∀ k, t k ≤ C * (k + 1) ^ D

namespace PolyBounded

/-- Constant functions are polynomially bounded. -/
theorem const (c : ℕ) : PolyBounded (fun _ : ℕ => c) :=
  ⟨c, 0, fun _ => by simp⟩

/-- Polynomial boundedness is closed under addition. -/
theorem add {t u : ℕ → ℕ} (ht : PolyBounded t) (hu : PolyBounded u) :
    PolyBounded (fun k => t k + u k) := by
  obtain ⟨C1, D1, h1⟩ := ht
  obtain ⟨C2, D2, h2⟩ := hu
  refine ⟨C1 + C2, D1 + D2, fun k => ?_⟩
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have e1 : (k + 1) ^ D1 ≤ (k + 1) ^ (D1 + D2) :=
    Nat.pow_le_pow_right hk (Nat.le_add_right D1 D2)
  have e2 : (k + 1) ^ D2 ≤ (k + 1) ^ (D1 + D2) :=
    Nat.pow_le_pow_right hk (Nat.le_add_left D2 D1)
  calc t k + u k ≤ C1 * (k + 1) ^ D1 + C2 * (k + 1) ^ D2 :=
        Nat.add_le_add (h1 k) (h2 k)
    _ ≤ C1 * (k + 1) ^ (D1 + D2) + C2 * (k + 1) ^ (D1 + D2) :=
        Nat.add_le_add (Nat.mul_le_mul_left C1 e1) (Nat.mul_le_mul_left C2 e2)
    _ = (C1 + C2) * (k + 1) ^ (D1 + D2) := by ring

/-- Polynomial boundedness is closed under multiplication. -/
theorem mul {t u : ℕ → ℕ} (ht : PolyBounded t) (hu : PolyBounded u) :
    PolyBounded (fun k => t k * u k) := by
  obtain ⟨C1, D1, h1⟩ := ht
  obtain ⟨C2, D2, h2⟩ := hu
  refine ⟨C1 * C2, D1 + D2, fun k => ?_⟩
  calc t k * u k ≤ (C1 * (k + 1) ^ D1) * (C2 * (k + 1) ^ D2) :=
        Nat.mul_le_mul (h1 k) (h2 k)
    _ = C1 * C2 * (k + 1) ^ (D1 + D2) := by rw [pow_add]; ring

/-- Polynomial boundedness is closed under multiplication by a constant. -/
theorem const_mul (c : ℕ) {t : ℕ → ℕ} (ht : PolyBounded t) :
    PolyBounded (fun k => c * t k) := by
  obtain ⟨C, D, h⟩ := ht
  refine ⟨c * C, D, fun k => ?_⟩
  rw [mul_assoc]
  exact Nat.mul_le_mul_left c (h k)

end PolyBounded

/-- The paper's evaluation ledger for `f_s`: two evaluations of the cipher on
the `r`-block tuple plus a linear-cost comparison/conditional-swap/copy of two
`r·n`-bit strings (paper Section 3, pp. 4--6: "computing the two values
`E_x(~m)` and `E_{s⊕x}(~m)` ... sorting them"). -/
def hidingEvalCost (cipherCost r n : ℕ) : ℕ :=
  2 * cipherCost + (2 * (r * n) + 1)

end Qatlib.Papers.QRelatedKey13.MainResults.SourceModel
