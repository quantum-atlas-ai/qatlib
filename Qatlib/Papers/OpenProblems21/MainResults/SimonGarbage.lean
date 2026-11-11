/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OpenProblems21.MainResults.OracleModels

set_option backward.isDefEq.respectTransparency false

/-!
# OpenProblems21.MainResults — the Simon-plus-garbage candidate of Problem 11

Source: Scott Aaronson, *Open Problems Related to Quantum Query Complexity*,
arXiv:2109.06917v1 (fixed version), §9 "Comparing Query Models", p. 6, the
displayed candidate between Problem 11 and §10:

```
f(x) = ⟨h(x), gar(x)⟩
```

where `h` is a Simon function and `gar(x)` is a long string of random garbage
depending on `x`. This module formalizes the deterministic skeleton of the
candidate and proves the facts the paper states about it:

* `garbagePair` is the candidate `f = ⟨h, gar⟩`; it is injective exactly when
  the garbage `gar` is injective (the paper's "the inclusion of `gar(x)` makes
  `f` injective with overwhelming probability" is the probabilistic counting
  statement `garbage_injective_card` below, an exact count over a uniformly
  chosen garbage function);
* the standard oracle on the candidate is the XOR update on the product
  register, and is an involution;
* the paper's displayed computation
  `|x⟩ → |x,h(x),gar(x)⟩ → |x,h(x),gar(x),h(x)⟩ → |x,h(x)⟩`
  is a theorem: with a free copy gate between two standard queries the garbage
  is uncomputed and the clean pair `|x⟩|h(x)⟩` remains (`standardOracle_simon_gadget`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OpenProblems21.MainResults

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## §1. The garbage pair `f(x) = ⟨h(x), gar(x)⟩` -/

/-- The candidate function of §9, p. 6: `f(x) = ⟨h(x), gar(x)⟩`. -/
def garbagePair {N k g : ℕ} (h : Fin N → Reg k) (gar : Fin N → Reg g) :
    Fin N → Reg k × Reg g :=
  fun x => (h x, gar x)

/-- `f = ⟨h, gar⟩` separates points exactly when the pair `(h, gar)` does:
two inputs are equal as soon as both the Simon value and the garbage agree.
This is the precise deterministic content of "the inclusion of `gar(x)` makes
`f` injective": the garbage distinguishes any two inputs that the Simon
function `h` does not. -/
theorem garbagePair_injective_iff_forall {N k g : ℕ} (h : Fin N → Reg k)
    (gar : Fin N → Reg g) :
    Function.Injective (garbagePair h gar) ↔
      ∀ x y, h x = h y → gar x = gar y → x = y := by
  constructor
  · intro hf x y hx hy
    exact hf (Prod.ext hx hy)
  · intro hsep x y hxy
    exact hsep x y (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)

/-- In particular, an injective garbage function makes the candidate injective
(the paper's sufficient condition, §9, p. 6). -/
theorem garbagePair_injective_of_injective_gar {N k g : ℕ} (h : Fin N → Reg k)
    (gar : Fin N → Reg g) (hg : Function.Injective gar) :
    Function.Injective (garbagePair h gar) := by
  rw [garbagePair_injective_iff_forall]
  intro x y _ hxy
  exact hg hxy

/-- Injective garbage functions and embeddings are the same data. -/
def injectiveGarbageEquivEmbedding (N g : ℕ) :
    {gar : Fin N → Reg g // Function.Injective gar} ≃ (Fin N ↪ Reg g) where
  toFun f := ⟨f.1, f.2⟩
  invFun e := ⟨e, e.injective⟩
  left_inv f := by cases f; rfl
  right_inv e := by cases e; rfl

/-- The exact number of injective garbage functions `Fin N → Reg g`: the
falling factorial `(2^g).descFactorial N`. Equivalently, for uniformly chosen
garbage the probability that the candidate is injective is
`(2^g).descFactorial N / (2^g)^N`; this is the count behind the paper's
"injective with overwhelming probability" (arXiv:2109.06917v1, §9, p. 6). -/
theorem garbage_injective_card (N g : ℕ) :
    Fintype.card {gar : Fin N → Reg g // Function.Injective gar} =
      Nat.descFactorial (2 ^ g) N := by
  rw [Fintype.card_congr (injectiveGarbageEquivEmbedding N g),
    Fintype.card_embedding_eq, card_reg, Fintype.card_fin]

/-- The total number of garbage functions `Fin N → Reg g`. (arXiv:2109.06917v1, §9, p. 6). -/
theorem garbage_function_card (N g : ℕ) :
    Fintype.card (Fin N → Reg g) = (2 ^ g) ^ N := by
  rw [Fintype.card_fun, card_reg, Fintype.card_fin]

/-! ## §2. XOR on the product register -/

/-- Componentwise XOR on `Reg k × Reg g`, the target-register operation of the
standard oracle for the pair-valued candidate. -/
def pairXor {k g : ℕ} (u v : Reg k × Reg g) : Reg k × Reg g :=
  (fun j => u.1 j ^^ v.1 j, fun j => u.2 j ^^ v.2 j)

/-- `pairXor` is commutative. (arXiv:2109.06917v1, §9, p. 6). -/
theorem pairXor_comm {k g : ℕ} (u v : Reg k × Reg g) : pairXor u v = pairXor v u := by
  apply Prod.ext <;> funext j <;> simp [pairXor, Bool.xor_comm]

/-- `pairXor` is associative. (arXiv:2109.06917v1, §9, p. 6). -/
theorem pairXor_assoc {k g : ℕ} (u v w : Reg k × Reg g) :
    pairXor (pairXor u v) w = pairXor u (pairXor v w) := by
  apply Prod.ext <;> funext j <;> simp [pairXor]

/-- XORing a pair with itself cancels both components. (arXiv:2109.06917v1, §9, p. 6). -/
theorem pairXor_self {k g : ℕ} (u : Reg k × Reg g) :
    pairXor u u = (ZeroStr k, ZeroStr g) := by
  apply Prod.ext <;> funext j <;> simp [pairXor, ZeroStr]

/-- The all-zero pair is a neutral element for `pairXor`. (arXiv:2109.06917v1, §9, p. 6). -/
theorem pairXor_zero_left {k g : ℕ} (v : Reg k × Reg g) :
    pairXor (ZeroStr k, ZeroStr g) v = v := by
  apply Prod.ext <;> funext j <;> simp [pairXor, ZeroStr]

/-! ## §3. The standard oracle on the candidate -/

/-- One standard query on the pair-valued candidate:
`(x, a) ↦ (x, a ⊕ ⟨h(x), gar(x)⟩)`. -/
def pairUpdate {N k g : ℕ} (f : Fin N → Reg k × Reg g)
    (s : Fin N × (Reg k × Reg g)) : Fin N × (Reg k × Reg g) :=
  (s.1, pairXor s.2 (f s.1))

/-- The pair-valued standard query is an involution: a second query uncomputes
the first, as in the paper's displayed chain. (arXiv:2109.06917v1, §9, p. 6). -/
theorem pairUpdate_involutive {N k g : ℕ} (f : Fin N → Reg k × Reg g) :
    Function.Involutive (pairUpdate f) := by
  intro s
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> funext j <;>
      simp [pairUpdate, pairXor]

/-- The standard oracle matrix of the candidate is a permutation gate. -/
def standardPairOracle {N k g : ℕ} (f : Fin N → Reg k × Reg g) :
    Matrix (Fin N × (Reg k × Reg g)) (Fin N × (Reg k × Reg g)) ℂ :=
  permMatrix (pairUpdate f)

/-- The standard oracle of the candidate acts on a basis state by the pair XOR
update. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardPairOracle_ket {N k g : ℕ} (f : Fin N → Reg k × Reg g) (x : Fin N)
    (a : Reg k × Reg g) :
    ApplyGate (standardPairOracle f) (Ket (x, a)) = Ket (pairUpdate f (x, a)) :=
  applyGate_permMatrix_ket (pairUpdate_involutive f) (x, a)

/-- A single query on the clean state `|x, 0⟩` yields `|x, ⟨h(x), gar(x)⟩⟩`. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardPairOracle_ket_clean {N k g : ℕ} (h : Fin N → Reg k) (gar : Fin N → Reg g)
    (x : Fin N) :
    ApplyGate (standardPairOracle (garbagePair h gar))
        (Ket (x, (ZeroStr k, ZeroStr g))) =
      Ket (x, (h x, gar x)) := by
  rw [standardPairOracle_ket]
  simp [pairUpdate, garbagePair, pairXor_zero_left]

/-! ## §4. The paper's uncompute chain `|x⟩ → |x,h,gar⟩ → |x,h,gar,h⟩ → |x,h⟩` -/

/-- The state of the gadget: input label, value/garbage target, and a copy
register for the Simon output. -/
abbrev GadgetState (N k g : ℕ) := Fin N × (Reg k × Reg g) × Reg k

/-- A standard query applied to the value/garbage target of the gadget. -/
def gadgetQuery {N k g : ℕ} (f : Fin N → Reg k × Reg g) (s : GadgetState N k g) :
    GadgetState N k g :=
  (s.1, pairXor s.2.1 (f s.1), s.2.2)

/-- A free CNOT copying the `h` component of the value/garbage target into the
copy register (the paper's "`h(x)`" appearing a second time). -/
def gadgetCopy {N k g : ℕ} (s : GadgetState N k g) : GadgetState N k g :=
  (s.1, s.2.1, fun j => s.2.2 j ^^ s.2.1.1 j)

/-- **The paper's displayed computation (arXiv:2109.06917v1, §9, p. 6).**
Starting from `|x⟩ |0,0⟩ |0⟩`, one standard query produces `|x,h(x),gar(x)⟩|0⟩`,
a free copy produces `|x,h(x),gar(x),h(x)⟩`, and the second standard query
uncomputes the garbage, leaving `|x,0,0⟩|h(x)⟩`. This is exactly the
`|x⟩ → |x,h(x),gar(x)⟩ → |x,h(x),gar(x),h(x)⟩ → |x,h(x)⟩` chain of the paper
(with the uncomputed target suppressed in the last step). -/
theorem standardOracle_simon_gadget {N k g : ℕ} (h : Fin N → Reg k) (gar : Fin N → Reg g)
    (x : Fin N) :
    gadgetQuery (garbagePair h gar)
        (gadgetCopy (gadgetQuery (garbagePair h gar)
          (x, (ZeroStr k, ZeroStr g), ZeroStr k))) =
      (x, (ZeroStr k, ZeroStr g), h x) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Prod.ext <;> funext j <;>
        simp [gadgetQuery, gadgetCopy, pairXor, garbagePair, ZeroStr]
    · funext j
      simp [gadgetQuery, gadgetCopy, pairXor, garbagePair, ZeroStr]

/-- The garbage registers are clean after the two standard queries, while the
Simon value survives in the copy register: the standard model "is no bar to
running Simon's algorithm". (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardOracle_gadget_garbage_clean {N k g : ℕ} (h : Fin N → Reg k)
    (gar : Fin N → Reg g) (x : Fin N) :
    (gadgetQuery (garbagePair h gar)
        (gadgetCopy (gadgetQuery (garbagePair h gar)
          (x, (ZeroStr k, ZeroStr g), ZeroStr k)))).2.1 =
      (ZeroStr k, ZeroStr g) := by
  rw [standardOracle_simon_gadget]

end Qatlib.Papers.OpenProblems21.MainResults
