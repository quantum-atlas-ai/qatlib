/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SymQueryComm20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Complexity measures of SymQueryComm20 and their semantic laws

Source: arXiv:2012.05233v2, §2.1 (query complexity, Definition 2.4 and the
notations `Q(·)`, `Q_E^{cc}(·)`, `Q^{cc,*}(·)`, `UPP^{cc}(·)` on pp. 9–11),
§4 (Theorem 1.2/4.4) and §5 (Theorems 5.1–5.2, Lemmas 5.4–5.5).

The paper works with quantum protocols, which are not formalised in this
library.  In the spirit of the paper-layer developments of this repository we
therefore fix the *numerical measures* as an abstract `ComplexityProfile` and
record the semantic laws that the development actually uses.  Every law is a
statement that is true of the concrete measures of the paper:

* `Q_preprocess_le` — deterministic preprocessing of the input is free in the
  query model (§2.1; also used in Theorem 5.2, p. 24);
* `QccStar_preprocess_le`, `UPPcc_preprocess_le` — free deterministic local
  preprocessing cannot increase communication complexity; this is exactly the
  reduction step of the proof of Lemma 5.4 (p. 25);
* `Q_le_card` — the trivial protocol that reads the whole input costs at most
  the input length in queries.

No theorem of the paper is assumed as a field: the fields only state
elementary and independently true properties of the measures.
-/

namespace Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.SymQueryComm20.MainResults.SourceModel
open scoped BigOperators

/-! ## The paper's asymptotic notation -/

/-- `F = O(G)` for a one-parameter complexity family.  The constant is
absolute, as in the paper's `O(·)` notation. -/
def BigO (F G : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → F n ≤ C * G n

/-- `F = Ω(G)` for a one-parameter complexity family. -/
def BigOmega (F G : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → c * G n ≤ F n

/-- `F = Θ(G)`. -/
def BigTheta (F G : ℕ → ℝ) : Prop := BigO F G ∧ BigOmega F G

/-! ## The complexity profile -/

/-- The four measures of the paper together with the three semantic laws used
in the reductions.  The measures take the paper's objects:

* `Q f` — quantum query complexity (§2.1, p. 9);
* `QEcc G` — exact quantum communication complexity of a two-party function
  (§2.3, p. 11);
* `QccStar F` — bounded-error (`1/3`) quantum communication complexity with
  free entanglement, `Q^{cc,*}` (p. 3 and §2.3);
* `UPPcc F` — unbounded-error quantum communication complexity `UPP^{cc}`
  (§1 and §5.2).

The first argument of the communication measures is the number of blocks `n`;
inputs of both parties are words indexed by `Fin n × ι` (Alice) and
`Fin n × κ` (Bob), exactly the objects produced by `composeWord`. -/
structure ComplexityProfile where
  /-- Quantum query complexity `Q(f)`. -/
  Q : (ι : Type) → [Fintype ι] → (Word ι → Bool) → ℕ
  /-- Exact quantum communication complexity `Q_E^{cc}(G)`. -/
  QEcc : (j k : ℕ) → (Cube j → Cube k → Bool) → ℕ
  /-- Bounded-error quantum communication complexity with free entanglement. -/
  QccStar : (n : ℕ) → (ι : Type) → (κ : Type) → [Fintype ι] → [Fintype κ] →
    (Word (Fin n × ι) → Word (Fin n × κ) → Bool) → ℕ
  /-- Unbounded-error quantum communication complexity. -/
  UPPcc : (n : ℕ) → (ι : Type) → (κ : Type) → [Fintype ι] → [Fintype κ] →
    (Word (Fin n × ι) → Word (Fin n × κ) → Bool) → ℕ
  /-- Deterministic preprocessing of an input is free in the query model: if
  `f' x = f (π x)` then a query algorithm for `f` solves `f'` with the same
  number of queries. -/
  Q_preprocess_le : ∀ {ι ι' : Type} [Fintype ι] [Fintype ι'] (f : Word ι → Bool)
    (f' : Word ι' → Bool) (π : Word ι' → Word ι),
    (∀ x, f' x = f (π x)) → Q ι' f' ≤ Q ι f
  /-- Free local preprocessing does not increase communication complexity
  (the reduction step in the proof of Lemma 5.4, p. 25). -/
  QccStar_preprocess_le : ∀ (n : ℕ) {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ]
    [Fintype ι'] [Fintype κ']
    (F : Word (Fin n × ι) → Word (Fin n × κ) → Bool)
    (F' : Word (Fin n × ι') → Word (Fin n × κ') → Bool)
    (πA : Word (Fin n × ι') → Word (Fin n × ι))
    (πB : Word (Fin n × κ') → Word (Fin n × κ)),
    (∀ x y, F' x y = F (πA x) (πB y)) → QccStar n ι' κ' F' ≤ QccStar n ι κ F
  /-- The same law for the unbounded-error model. -/
  UPPcc_preprocess_le : ∀ (n : ℕ) {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ]
    [Fintype ι'] [Fintype κ']
    (F : Word (Fin n × ι) → Word (Fin n × κ) → Bool)
    (F' : Word (Fin n × ι') → Word (Fin n × κ') → Bool)
    (πA : Word (Fin n × ι') → Word (Fin n × ι))
    (πB : Word (Fin n × κ') → Word (Fin n × κ)),
    (∀ x y, F' x y = F (πA x) (πB y)) → UPPcc n ι' κ' F' ≤ UPPcc n ι κ F
  /-- The trivial protocol that queries (or sends) every input bit. -/
  Q_le_card : ∀ (ι : Type) [Fintype ι] (f : Word ι → Bool), Q ι f ≤ Fintype.card ι

/-! ## The two-bit gadgets

`AND₂` and `XOR₂` are the two two-party functions of §1 (p. 3).  Under the
sign encoding `true ↦ +1`, `false ↦ −1` of `SourceModel`, `AND₂` returns
`−1` exactly when both inputs are `−1` (so that `IP_n = PARITY_n ∘ AND₂`,
Definition 2.14) and `XOR₂` returns the product of the two signs (so that
`EQ_n = NOR_n ∘ XOR₂`).  In particular `−1` is the identity of `AND₂` and
`+1` the identity of `XOR₂`, which is what makes the preprocessing of
Lemma 5.4 work. -/

/-- `AND₂(a, −1) = a`: `−1` is the identity of `AND₂`. -/
@[simp] theorem and2_false (a : Bool) : and2 a false = a := by cases a <;> rfl

/-- `AND₂(−1, b) = b`. -/
@[simp] theorem and2_false_left (b : Bool) : and2 false b = b := by cases b <;> rfl

/-- `XOR₂(a, +1) = a`: `+1` is the identity of `XOR₂`. -/
@[simp] theorem xor2_true (a : Bool) : xor2 a true = a := by cases a <;> rfl

/-- `XOR₂(+1, b) = b`. -/
@[simp] theorem xor2_true_left (b : Bool) : xor2 true b = b := by cases b <;> rfl

/-- The two-party function `AND₂ : {−1,1}¹ × {−1,1}¹ → {−1,1}` (§1, p. 3),
in word encoding (each party holds one bit). -/
def and2TwoParty : Cube 1 → Cube 1 → Bool := fun a b => and2 (a 0) (b 0)

/-- The two-party function `XOR₂ : {−1,1}¹ × {−1,1}¹ → {−1,1}` (§1, p. 3). -/
def xor2TwoParty : Cube 1 → Cube 1 → Bool := fun a b => xor2 (a 0) (b 0)

/-! ## Bridging `compose` and `composeWord` -/

/-- `composeWord` is the word encoding of `compose`: it is the same value on
the corresponding inputs. -/
theorem composeWord_apply {n j k : ℕ} (f : Cube n → Bool) (G : Cube j → Cube k → Bool)
    (X : Word (Fin n × Fin j)) (Y : Word (Fin n × Fin k)) :
    composeWord f G X Y = f (fun i => G (fun a => X (i, a)) (fun b => Y (i, b))) := rfl

/-! ## The string `z` of §3 -/

/-- The string `z = (G(X₁,Y₁),…,G(Xₙ,Yₙ)) ∈ {−1,1}ⁿ` of Theorem 3.1 (p. 15). -/
def zString {n j k : ℕ} (G : Cube j → Cube k → Bool)
    (X : Word (Fin n × Fin j)) (Y : Word (Fin n × Fin k)) : Fin n → Bool :=
  fun i => G (fun a => X (i, a)) (fun b => Y (i, b))

/-- The number `|z|` of `−1`s in `z` (Theorem 4.1, p. 21). -/
def zWeight {n j k : ℕ} (G : Cube j → Cube k → Bool)
    (X : Word (Fin n × Fin j)) (Y : Word (Fin n × Fin k)) : ℕ :=
  (Finset.univ.filter (fun i => zString G X Y i = false)).card

end

end Qatlib.Papers.SymQueryComm20.MainResults.SourceComplexity
