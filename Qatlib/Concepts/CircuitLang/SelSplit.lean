/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.LocGates
public import Qatlib.Concepts.CircuitLang.WireReg

@[expose] public section

/-!
# Completing an injective wire selection into a register split

A located gate names its target wires through an injective `LocSel`; this module completes
such a selection to a wire split, so that a gate can act on arbitrary non-adjacent wires and
not only on the canonical last-wire block of `LocGates`. The completion is a contract
structure `SplitSel` carrying the complementary wires together with a proof that both wire
classes enumerate the register exactly once; the parameterization `m + k` reuses
`regAppendEquiv` and avoids subtraction on wire counts. A fully constructive completion of an
arbitrary `LocSel` into a `SplitSel` (an explicit enumeration of the unselected wires) is not
provided here and stays with the consumer.

## Main statements

* `selLe`: an injective selection of `k` wires needs `k ≤ n`.
* `placedSel_uni`: placing a unitary gate on arbitrary selected wires is unitary.
* `placedSel_bits`: entry form of an arbitrary-wire placement on raw wire reads.
* `placedSel_last`: placement on the canonical split equals the canonical `PlacedLast`.
* `placedSel_comm`: gates on the two disjoint wire classes of a split commute.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.LocGates

namespace Qatlib.Concepts.CircuitLang.SelSplit

/-- An injective selection of `k` wires out of `n` can target at most `n` wires. -/
theorem selLe {n k : ℕ} (s : LocSel n k) : k ≤ n := by
  have h := Fintype.card_le_of_injective s.sel s.inj
  rwa [Fintype.card_fin, Fintype.card_fin] at h

/-- A contract wire split of an `(m + k)`-wire register: `k` selected wires and `m`
complementary wires jointly enumerate every wire exactly once. Carrying the complement as
data avoids subtraction on wire counts; a repeated or missing wire is rejected at the field
level by `bij`. -/
structure SplitSel (m k : ℕ) where
  /-- The `k` selected target wires, in target order. -/
  sel : Fin k → Wire (m + k)
  /-- The `m` complementary wires left untouched by the gate. -/
  compl : Fin m → Wire (m + k)
  /-- Complementary and selected wires together enumerate all wires without repetition. -/
  bij : Function.Bijective (Sum.elim compl sel)

/-- The selected wires of a split form an injective selection. -/
theorem splitSel_inj {m k : ℕ} (S : SplitSel m k) : Function.Injective S.sel := by
  intro a b h
  have h2 : Sum.elim S.compl S.sel (Sum.inr a) = Sum.elim S.compl S.sel (Sum.inr b) := by
    simp [h]
  exact Sum.inr.inj (S.bij.1 h2)

/-- The canonical split of an `(m + k)`-wire register into the first `m` wires and the last
`k` wires. -/
def canSplit (m k : ℕ) : SplitSel m k where
  sel := fun j => Fin.natAdd m j
  compl := fun i => Fin.castAdd k i
  bij := finSumFinEquiv.bijective

/-- The wire-index equivalence induced by a split: every wire is mapped to its position in
the enumeration of complementary and selected wires. -/
noncomputable def wEquiv {m k : ℕ} (S : SplitSel m k) : Fin (m + k) ≃ Fin m ⊕ Fin k :=
  (Equiv.ofBijective (Sum.elim S.compl S.sel) S.bij).symm

/-- The index of a complementary wire is in the left summand. -/
theorem wEquiv_compl {m k : ℕ} (S : SplitSel m k) (i : Fin m) :
    wEquiv S (S.compl i) = Sum.inl i := by
  have h1 : Sum.elim S.compl S.sel (wEquiv S (S.compl i)) = S.compl i :=
    Equiv.ofBijective_apply_symm_apply (Sum.elim S.compl S.sel) S.bij (S.compl i)
  exact S.bij.1 (h1.trans rfl)

/-- The index of a selected wire is in the right summand. -/
theorem wEquiv_sel {m k : ℕ} (S : SplitSel m k) (j : Fin k) :
    wEquiv S (S.sel j) = Sum.inr j := by
  have h1 : Sum.elim S.compl S.sel (wEquiv S (S.sel j)) = S.sel j :=
    Equiv.ofBijective_apply_symm_apply (Sum.elim S.compl S.sel) S.bij (S.sel j)
  exact S.bij.1 (h1.trans rfl)

/-- The wire of a left-summand index is the corresponding complementary wire. -/
theorem wEquivS_compl {m k : ℕ} (S : SplitSel m k) (i : Fin m) :
    (wEquiv S).symm (Sum.inl i) = S.compl i :=
  (Equiv.symm_apply_eq (wEquiv S)).mpr (wEquiv_compl S i).symm

/-- The wire of a right-summand index is the corresponding selected wire. -/
theorem wEquivS_sel {m k : ℕ} (S : SplitSel m k) (j : Fin k) :
    (wEquiv S).symm (Sum.inr j) = S.sel j :=
  (Equiv.symm_apply_eq (wEquiv S)).mpr (wEquiv_sel S j).symm

/-- The canonical split enumerates wires exactly as `finSumFinEquiv`. -/
theorem wEquiv_can (m k : ℕ) : wEquiv (canSplit m k) = finSumFinEquiv.symm := by
  unfold wEquiv canSplit
  exact congrArg Equiv.symm (Equiv.ofBijective_coe (f := finSumFinEquiv (m := m) (n := k)))

/-- The register basis equivalence induced by a split: the complementary wires become the
first factor and the selected wires the second. -/
noncomputable def splitEq {m k : ℕ} (S : SplitSel m k) : Reg (m + k) ≃ Reg m × Reg k :=
  (Equiv.arrowCongr (wEquiv S) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) Bool)

/-- The split equivalence on the canonical split equals `regAppendEquiv`. -/
theorem splitEq_can (m k : ℕ) : splitEq (canSplit m k) = regAppendEquiv m k := by
  unfold splitEq regAppendEquiv
  rw [wEquiv_can]

/-- The split equivalence reads a register as its complementary block and its selected
block. -/
theorem splitEq_apply {m k : ℕ} (S : SplitSel m k) (x : Reg (m + k)) :
    splitEq S x = (fun i => x (S.compl i), fun j => x (S.sel j)) := by
  have h1 : (splitEq S x).1 = fun i => x (S.compl i) := by
    have h : (splitEq S x).1 = fun i => x ((wEquiv S).symm (Sum.inl i)) := rfl
    rw [h]
    exact funext (fun i => congrArg x (wEquivS_compl S i))
  have h2 : (splitEq S x).2 = fun j => x (S.sel j) := by
    have h : (splitEq S x).2 = fun j => x ((wEquiv S).symm (Sum.inr j)) := rfl
    rw [h]
    exact funext (fun j => congrArg x (wEquivS_sel S j))
  rw [show splitEq S x = ((splitEq S x).1, (splitEq S x).2) from rfl, h1, h2]

/-- Place a `Reg k` gate on the selected wires of a split, acting as the identity on the
complementary wires. -/
noncomputable def PlacedSel {m k : ℕ} (S : SplitSel m k) (U : Matrix (Reg k) (Reg k) ℂ) :
    Matrix (Reg (m + k)) (Reg (m + k)) ℂ :=
  Matrix.reindex (splitEq S).symm (splitEq S).symm (TensorGate 1 U)

/-- Place a `Reg m` gate on the complementary wires of a split, acting as the identity on
the selected wires. -/
noncomputable def PlacedCompl {m k : ℕ} (S : SplitSel m k) (V : Matrix (Reg m) (Reg m) ℂ) :
    Matrix (Reg (m + k)) (Reg (m + k)) ℂ :=
  Matrix.reindex (splitEq S).symm (splitEq S).symm (TensorGate V 1)

/-- Placement on arbitrarily selected wires preserves unitarity. -/
theorem placedSel_uni {m k : ℕ} {S : SplitSel m k} {U : Matrix (Reg k) (Reg k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg k) ℂ) :
    PlacedSel S U ∈ Matrix.unitaryGroup (Reg (m + k)) ℂ :=
  reidxUnitary _ (tensorGate_unitary (Submonoid.one_mem _) hU)

/-- Placement on the complementary wires preserves unitarity. -/
theorem placedCompl_uni {m k : ℕ} {S : SplitSel m k} {V : Matrix (Reg m) (Reg m) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Reg m) ℂ) :
    PlacedCompl S V ∈ Matrix.unitaryGroup (Reg (m + k)) ℂ :=
  reidxUnitary _ (tensorGate_unitary hV (Submonoid.one_mem _))

/-- Entry form on raw wire reads: the gate entry on the selected wires, times the identity
indicator on the untouched complementary wires. This generalizes `placedLast_bits` from the
canonical last-wire block to arbitrary injective selections. -/
theorem placedSel_bits {m k : ℕ} (S : SplitSel m k) (U : Matrix (Reg k) (Reg k) ℂ)
    (x y : Reg (m + k)) :
    PlacedSel S U x y =
      (if ∀ i, x (S.compl i) = y (S.compl i) then (1 : ℂ) else 0) *
        U (fun j => x (S.sel j)) (fun j => y (S.sel j)) := by
  simp only [PlacedSel, reidx_apply, Equiv.symm_symm]
  rw [splitEq_apply S x, splitEq_apply S y, tensorGate_apply]
  simp [Matrix.one_apply, funext_iff]

/-- Placement on the canonical split equals the canonical last-wires placement, so consumers of
`PlacedLast` carry over unchanged. -/
theorem placedSel_last (m k : ℕ) (U : Matrix (Reg k) (Reg k) ℂ) :
    PlacedSel (canSplit m k) U = PlacedLast m k U := by
  rw [PlacedSel, PlacedLast, splitEq_can]

/-- Gates placed on the two disjoint wire classes of one split compose to the reindexed
tensor gate. -/
theorem placedSel_tens {m k : ℕ} (S : SplitSel m k) (V : Matrix (Reg m) (Reg m) ℂ)
    (U : Matrix (Reg k) (Reg k) ℂ) :
    PlacedCompl S V * PlacedSel S U
      = Matrix.reindex (splitEq S).symm (splitEq S).symm (TensorGate V U) := by
  rw [PlacedCompl, PlacedSel, ← reidxMul, tensorGate_mul, Matrix.mul_one, Matrix.one_mul]

/-- Gates on the two disjoint wire classes of a split commute. -/
theorem placedSel_comm {m k : ℕ} (S : SplitSel m k) (V : Matrix (Reg m) (Reg m) ℂ)
    (U : Matrix (Reg k) (Reg k) ℂ) :
    PlacedCompl S V * PlacedSel S U = PlacedSel S U * PlacedCompl S V := by
  rw [placedSel_tens, PlacedSel, PlacedCompl, ← reidxMul, tensorGate_mul, Matrix.one_mul,
    Matrix.mul_one]

end Qatlib.Concepts.CircuitLang.SelSplit
