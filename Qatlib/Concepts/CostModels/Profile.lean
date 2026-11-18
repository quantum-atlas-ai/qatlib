/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic

@[expose] public section

/-! # Cost profiles with explicit unmodeled fields

A `CostProfile` records the seven resource fields fixed by the toolkit
contract: oracle queries, macro gates, one-qubit and two-qubit elementary
gates, T-count, depth, and width. Every field is an `Option ℕ`: `none` means
"not applicable or not modeled" and is never a stand-in for a zero cost,
which is always written `some 0`.

Serial and independent-parallel combination determine exactly the fields the
operators can justify: serial adds all counts and depth; independent parallel
adds all counts and width and takes the depth maximum. Serial composition does
not determine width at all (`serialWidthNone`); the same-register width law
needs explicit reusable-wire or ancilla scheduling evidence
(`widthReuseMax`, `widthAncBound`), and without it the maximum rule is false
(`maxNeedsReuse`).

This module is deliberately algebra-only: no circuit representation, gate
word, or compiler output is imported or constructed. Wires enter only as
abstract `Finset W` scheduling evidence.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CostModels.Profile

/-- Modeled addition: two modeled counts add; any unmodeled input leaves the
result unmodeled, so `none` can never silently act as zero. -/
def optAdd : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (a + b)
  | _, _ => none

/-- Modeled maximum: two modeled values combine by `max`; any unmodeled input
leaves the result unmodeled. -/
def optMax : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (max a b)
  | _, _ => none

/-- The seven-field cost profile of the toolkit contract. Each field carries a
measured count, or `none` when that resource is not applicable or has not been
modeled yet. `some 0` is a genuine measured zero; `none` never encodes zero. -/
@[ext]
structure CostProfile where
  /-- Number of oracle queries executed. -/
  queries : Option ℕ
  /-- Number of macro gates (for example matrix-word macro blocks) in the
  segment. -/
  macroGates : Option ℕ
  /-- Number of one-qubit elementary gates in the segment. -/
  oneQ : Option ℕ
  /-- Number of two-qubit elementary gates in the segment. -/
  twoQ : Option ℕ
  /-- T-count of the segment. -/
  tCount : Option ℕ
  /-- Circuit depth of the segment. -/
  depth : Option ℕ
  /-- Width, the number of concurrently active wires, of the segment. -/
  width : Option ℕ

/-- The profile of an empty segment: every field is a genuinely measured zero.
This is a real measurement of an empty composition, not an unmodeled
placeholder. It is not a full identity of `serial`, which still leaves width
undetermined (`serialWidthNone`). -/
def emptyProfile : CostProfile where
  queries := some 0
  macroGates := some 0
  oneQ := some 0
  twoQ := some 0
  tCount := some 0
  depth := some 0
  width := some 0

/-- The fully unmodeled profile: no field has been measured. -/
def opaqueProfile : CostProfile where
  queries := none
  macroGates := none
  oneQ := none
  twoQ := none
  tCount := none
  depth := none
  width := none

/-- Serial composition: run `c`, then `d` on the result. All counts and depths
add. Width is set to `none`: serial composition alone does not determine
width, and the same-register maximum law requires explicit reusable-wire or
ancilla scheduling evidence (see `widthReuseMax`, `widthAncBound`). -/
def serial (c d : CostProfile) : CostProfile where
  queries := optAdd c.queries d.queries
  macroGates := optAdd c.macroGates d.macroGates
  oneQ := optAdd c.oneQ d.oneQ
  twoQ := optAdd c.twoQ d.twoQ
  tCount := optAdd c.tCount d.tCount
  depth := optAdd c.depth d.depth
  width := none

/-- Independent-parallel composition: `c` and `d` run on disjoint wires. All
counts and widths add, and depth is the maximum. -/
def par (c d : CostProfile) : CostProfile where
  queries := optAdd c.queries d.queries
  macroGates := optAdd c.macroGates d.macroGates
  oneQ := optAdd c.oneQ d.oneQ
  twoQ := optAdd c.twoQ d.twoQ
  tCount := optAdd c.tCount d.tCount
  depth := optMax c.depth d.depth
  width := optAdd c.width d.width

/-- Serial composition adds oracle query counts. -/
theorem serialQueryAdd {a b : ℕ} {c d : CostProfile}
    (hc : c.queries = some a) (hd : d.queries = some b) :
    (serial c d).queries = some (a + b) := by
  simp [serial, optAdd, hc, hd]

/-- Serial composition adds macro-gate counts. -/
theorem serialMacroAdd {a b : ℕ} {c d : CostProfile}
    (hc : c.macroGates = some a) (hd : d.macroGates = some b) :
    (serial c d).macroGates = some (a + b) := by
  simp [serial, optAdd, hc, hd]

/-- Serial composition adds every elementary-gate count: one-qubit gates,
two-qubit gates, and T-count. -/
theorem serialGateAdd {a b p q r s : ℕ} {c d : CostProfile}
    (ho : c.oneQ = some a) (hp : d.oneQ = some b)
    (ht : c.twoQ = some p) (hu : d.twoQ = some q)
    (hT : c.tCount = some r) (hU : d.tCount = some s) :
    (serial c d).oneQ = some (a + b) ∧
      (serial c d).twoQ = some (p + q) ∧
      (serial c d).tCount = some (r + s) := by
  simp [serial, optAdd, ho, hp, ht, hu, hT, hU]

/-- Serial composition adds depths. -/
theorem serialDepthAdd {a b : ℕ} {c d : CostProfile}
    (hc : c.depth = some a) (hd : d.depth = some b) :
    (serial c d).depth = some (a + b) := by
  simp [serial, optAdd, hc, hd]

/-- Serial composition leaves width undetermined: no width value is fabricated
without reusable-wire or ancilla scheduling evidence. -/
theorem serialWidthNone (c d : CostProfile) : (serial c d).width = none := rfl

/-- Independent-parallel composition adds the oracle query and macro-gate
counts. -/
theorem parQueryAdd {a b g h : ℕ} {c d : CostProfile}
    (hq : c.queries = some a) (hQ : d.queries = some b)
    (hg : c.macroGates = some g) (hG : d.macroGates = some h) :
    (par c d).queries = some (a + b) ∧ (par c d).macroGates = some (g + h) := by
  simp [par, optAdd, hq, hQ, hg, hG]

/-- Independent-parallel composition adds every elementary-gate count:
one-qubit gates, two-qubit gates, and T-count. -/
theorem parGateAdd {a b p q r s : ℕ} {c d : CostProfile}
    (ho : c.oneQ = some a) (hp : d.oneQ = some b)
    (ht : c.twoQ = some p) (hu : d.twoQ = some q)
    (hT : c.tCount = some r) (hU : d.tCount = some s) :
    (par c d).oneQ = some (a + b) ∧
      (par c d).twoQ = some (p + q) ∧
      (par c d).tCount = some (r + s) := by
  simp [par, optAdd, ho, hp, ht, hu, hT, hU]

/-- Independent-parallel composition takes the depth maximum. -/
theorem parDepthMax {a b : ℕ} {c d : CostProfile}
    (hc : c.depth = some a) (hd : d.depth = some b) :
    (par c d).depth = some (max a b) := by
  simp [par, optMax, hc, hd]

/-- Independent-parallel composition adds widths. -/
theorem parWidthAdd {a b : ℕ} {c d : CostProfile}
    (hc : c.width = some a) (hd : d.width = some b) :
    (par c d).width = some (a + b) := by
  simp [par, optAdd, hc, hd]

/-- Modeled addition is associative, with unmodeled inputs absorbing on both
sides. -/
theorem optAddAssoc (a b c : Option ℕ) :
    optAdd (optAdd a b) c = optAdd a (optAdd b c) := by
  cases a <;> cases b <;> cases c <;> simp [optAdd, Nat.add_assoc]

/-- Modeled maximum is associative, with unmodeled inputs absorbing on both
sides. -/
theorem optMaxAssoc (a b c : Option ℕ) :
    optMax (optMax a b) c = optMax a (optMax b c) := by
  cases a <;> cases b <;> cases c <;> simp [optMax, Nat.max_assoc]

/-- Serial composition is associative, including the undetermined width. -/
theorem serialAssoc (c d e : CostProfile) :
    serial (serial c d) e = serial c (serial d e) := by
  cases c; cases d; cases e
  simp [serial, optAddAssoc]

/-- Independent-parallel composition is associative. -/
theorem parAssoc (c d e : CostProfile) :
    par (par c d) e = par c (par d e) := by
  cases c; cases d; cases e
  simp [par, optAddAssoc, optMaxAssoc]

/-- Same-register serial width under a pure reuse schedule: if every wire the
second segment uses was already used by the first segment, the composed width
`#(ws₁ ∪ ws₂)` is exactly the maximum of the two widths. The subset premise is
the reusable-wire scheduling evidence; without it the law fails (see
`maxNeedsReuse`). -/
theorem widthReuseMax {W : Type*} [DecidableEq W] (ws₁ ws₂ : Finset W)
    (hsub : ws₂ ⊆ ws₁) :
    (ws₁ ∪ ws₂).card = max ws₁.card ws₂.card := by
  have hle : ws₂.card ≤ ws₁.card := Finset.card_le_card hsub
  rw [Finset.union_eq_left.mpr hsub, Nat.max_eq_left hle]

/-- Same-register serial width under a fresh-ancilla schedule: if the second
segment's wires are covered by the first segment's wires together with a
disjoint ancilla set `wa`, then the composed width is bounded by the reused
width plus the ancilla count — additive ancilla accounting, not the bare
maximum. -/
theorem widthAncBound {W : Type*} [DecidableEq W] (ws₁ ws₂ wa : Finset W)
    (hcover : ws₂ ⊆ ws₁ ∪ wa) (hdisj : Disjoint ws₁ wa) :
    (ws₁ ∪ ws₂).card ≤ ws₁.card + wa.card :=
  calc (ws₁ ∪ ws₂).card ≤ (ws₁ ∪ wa).card :=
      Finset.card_le_card (by
        intro x hx
        cases Finset.mem_union.mp hx with
        | inl h => exact Finset.mem_union.mpr (Or.inl h)
        | inr h => exact hcover h)
    _ = ws₁.card + wa.card := Finset.card_union_of_disjoint hdisj

/-- The width maximum rule is falsifiable without reuse evidence: two disjoint
one-wire segments compose to width two, while the maximum is one. This witness
is why `serial` refuses to fabricate a width. -/
theorem maxNeedsReuse :
    ∃ ws₁ ws₂ : Finset (Fin 2), Disjoint ws₁ ws₂ ∧
      (ws₁ ∪ ws₂).card ≠ max ws₁.card ws₂.card :=
  ⟨{0}, {1}, by decide, by decide⟩

end Qatlib.Concepts.CostModels.Profile
