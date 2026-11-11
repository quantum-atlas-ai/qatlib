/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Depth3Learn26.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Depth3Learn26 — concept classes

Fixed arXiv:2509.14461v3, Section 2.2–2.3 (p.13–14):

* `DT` is a binary decision tree; `DT.size` counts nodes.
* `Term`/`DNF` model a term (conjunction of literals) and an s-term DNF formula.
* `IsTAC0` models threshold-of-DNFs (Definition 2.3, p.14), with the threshold gate fanin
  and the circuit size.
* `IsJuntaOn`/`JuntaClass` model k-juntas.

Boundary: `gateCount` counts AND/OR/NOT gates, matching the paper's convention that the
size of a term `∧` of `ℓ` literals is `ℓ`; the decision-tree size counts all nodes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.Depth3Learn26.MainResults

noncomputable section

open scoped BigOperators

/-- A conjunction of positive and negative literals. -/
structure Term (n : ℕ) where
  /-- Positive literals. -/
  pos : Finset (Fin n)
  /-- Negative literals. -/
  neg : Finset (Fin n)
  deriving DecidableEq

/-- Evaluation of a term. -/
def Term.eval {n : ℕ} (t : Term n) (x : Cube n) : Bool :=
  decide (∀ i ∈ t.pos, x i = true) && decide (∀ i ∈ t.neg, x i = false)

/-- The number of gates in a term: one AND per literal (plus the conjunction). -/
def Term.gateCount {n : ℕ} (t : Term n) : ℕ := t.pos.card + t.neg.card + 1

/-- An s-term DNF formula. -/
structure DNF (n : ℕ) where
  /-- The terms of the DNF. -/
  terms : Finset (Term n)

/-- Evaluation of a DNF. -/
def DNF.eval {n : ℕ} (d : DNF n) (x : Cube n) : Bool :=
  decide (∃ t ∈ d.terms, t.eval x = true)

/-- Number of AND/OR gates of a DNF (Section 2.2, p.14). -/
def DNF.gateCount {n : ℕ} (d : DNF n) : ℕ :=
  d.terms.card + ∑ t ∈ d.terms, t.gateCount

/-- The class `C_DNF(s)` of s-term DNFs, Section 2.3, p.14. -/
def DNFClass (n s : ℕ) : Set (BoolFun n) :=
  {f | ∃ d : DNF n, d.gateCount ≤ s ∧ ∀ x, f x = d.eval x}

/-- A binary decision tree on `n` variables (Section 2.2, p.14). -/
inductive DT (n : ℕ) where
  /-- A leaf labelled by a Boolean value. -/
  | leaf : Bool → DT n
  /-- A test of variable `i` with the `false` and `true` children. -/
  | node : Fin n → DT n → DT n → DT n

/-- Evaluation of a decision tree. -/
def DT.eval {n : ℕ} : DT n → Cube n → Bool
  | .leaf b, _ => b
  | .node i l r, x => if x i then DT.eval r x else DT.eval l x

/-- The number of nodes of a decision tree (the paper's size, footnote 10, p.14). -/
def DT.size {n : ℕ} : DT n → ℕ
  | .leaf _ => 1
  | .node _ l r => 1 + DT.size l + DT.size r

/-- The class `C_DT(s)` of size-`s` decision trees, Section 2.3, p.14. -/
def DTClass (n s : ℕ) : Set (BoolFun n) :=
  {f | ∃ t : DT n, t.size ≤ s ∧ ∀ x, f x = t.eval x}

/-- A function depends only on the coordinates in `S` (a junta with variable set `S`). -/
def IsJuntaOn {n : ℕ} (f : BoolFun n) (S : Finset (Fin n)) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

/-- The class `C_Jun(k)` of k-juntas (Section 2.2, p.13). -/
def JuntaClass (n k : ℕ) : Set (BoolFun n) :=
  {f | ∃ S : Finset (Fin n), S.card ≤ k ∧ IsJuntaOn f S}

/-- A threshold of `m` DNFs (Definition 2.3, p.14). -/
structure TAC0 (n m : ℕ) where
  /-- The threshold of the top gate. -/
  threshold : ℕ
  /-- The `m` DNF formulas feeding the threshold gate. -/
  clauses : Fin m → DNF n

/-- The sum of the DNF values feeding the threshold gate. -/
def TAC0.value {n m : ℕ} (c : TAC0 n m) (x : Cube n) : ℕ :=
  ∑ i, if (c.clauses i).eval x then 1 else 0

/-- Evaluation of a threshold-of-DNFs circuit (Definition 2.2/2.3, p.14). -/
def TAC0.eval {n m : ℕ} (c : TAC0 n m) (x : Cube n) : Bool :=
  decide (c.threshold ≤ c.value x)

/-- Total AND/OR/NOT gate count of a threshold-of-DNFs circuit. -/
def TAC0.gateCount {n m : ℕ} (c : TAC0 n m) : ℕ :=
  m + ∑ i, (c.clauses i).gateCount

/-- `f` lies in `TAC0_2(s)` with threshold-gate fanin `m` (Definition 2.3, p.14). -/
def IsTAC0 {n : ℕ} (f : BoolFun n) (s m : ℕ) : Prop :=
  ∃ c : TAC0 n m, c.gateCount ≤ s ∧ ∀ x, f x = c.eval x

/-- The class of parities `C_Par`, Section 2.2, p.13. -/
def ParityClass (n : ℕ) : Set (BoolFun n) := Set.range (parityFun (n := n))

end

end Qatlib.Papers.Depth3Learn26.MainResults
