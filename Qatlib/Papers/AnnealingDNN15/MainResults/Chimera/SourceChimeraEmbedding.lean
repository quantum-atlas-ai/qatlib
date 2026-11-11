/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Chain embedding of the 32×32 RBM into the 512-qubit Chimera chip (c002)

Source: *Application of Quantum Annealing to Training of Deep Neural Networks*,
arXiv:1510.06356 (2015), fixed local PDF
`1510.06356.pdf` (SHA-256 `7c273ebf6340223d2ddbc2f0684298e9a16ed3cc89253d212008ae3e3e945f72`).
Section 3.2.2, pp. 8–10, Eq. (21) and Figure 4; Section 4, p. 13.

Paper facts formalized here:

* The Vesuvius chip is an 8×8 array of 8-qubit unit cells, i.e. 512 physical
  qubits (Sec. 3.2.1, Figure 3: 4 vertical and 4 horizontal qubits per cell).
* Each logical RBM node is a *chain* of physical qubits: a visible node is a
  chain of vertical qubits, a hidden node a chain of horizontal qubits
  (Sec. 3.2.2, Figure 4).  With 8 columns × 4 vertical slots there are 32
  visible chains, and with 8 rows × 4 horizontal slots there are 32 hidden
  chains.
* Every visible chain crosses every horizontal chain in exactly one unit cell,
  giving exactly one hardware coupler per logical visible-hidden pair: the ideal
  chip realizes the full 32×32 bipartite graph, 1024 couplers.
* Each physical qubit touches at most 4 couplers (the 4 opposite-orientation
  qubits in its cell), so 8 faulty qubits destroy at most 32 of the 1024
  couplers, leaving at least 992 usable — the paper's "8 faulty qubits" chip on
  which "32 of the 1024 visible-to-hidden node connections cannot be
  implemented", and on which a 32×32 RBM layer is still trained.

The empirical statement that training on this chip succeeded is not a theorem;
it is reported in Sec. 4.  What is proved here is the combinatorial embedding
and the faulty-qubit robustness bound on which that experiment relies.

No `sorry`, no extra axiom.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AnnealingDNN15.MainResults.Chimera

/-- A physical qubit of the 8×8 unit-cell Chimera graph: unit cell `(row, col)`
and slot `k : Fin 8`.  Slots `0–3` are the four vertical (column-running)
qubits of the cell, slots `4–7` the four horizontal (row-running) qubits
(Fig. 3 of the paper). -/
structure Qubit where
  row : Fin 8
  col : Fin 8
  slot : Fin 8
deriving DecidableEq, Fintype

/-- A qubit is vertical iff its slot is `0–3`; it then runs along the column
direction and is used by a visible chain. -/
def Qubit.isVertical (q : Qubit) : Prop := q.slot.val < 4

/-- A qubit is horizontal iff its slot is `4–7`; it then runs along the row
direction and is used by a hidden chain. -/
def Qubit.isHorizontal (q : Qubit) : Prop := 4 ≤ q.slot.val

/-- Every qubit is vertical or horizontal (the chip qubits are exactly the
4 + 4 per unit cell). -/
theorem Qubit.isVertical_or_isHorizontal (q : Qubit) :
    q.isVertical ∨ q.isHorizontal := by
  unfold Qubit.isVertical Qubit.isHorizontal
  omega

/-- Hardware-graph adjacency: two qubits are coupled when they lie in the same
unit cell, one vertical and one horizontal. -/
def Coupled (q r : Qubit) : Prop :=
  q.row = r.row ∧ q.col = r.col ∧ q.isVertical ∧ r.isHorizontal

/-- The chip has 512 physical qubits. -/
theorem qubit_card : Fintype.card Qubit = 512 := by
  rw [Fintype.card_congr
    (show Qubit ≃ (Fin 8 × Fin 8 × Fin 8) from
      { toFun := fun q => (q.row, q.col, q.slot)
        invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
        left_inv := by intro q; cases q; rfl
        right_inv := by rintro ⟨a, b, c⟩; rfl })]
  simp

/-- A visible chain index: its unit-cell column and the vertical slot. -/
abbrev VChain := Fin 8 × Fin 4

/-- A hidden chain index: its unit-cell row and the horizontal slot. -/
abbrev HChain := Fin 8 × Fin 4

/-- The member of the visible chain `c` lying in unit-cell row `row`: the
vertical qubit `(row, c.1, c.2)`. -/
def visibleQubit (c : VChain) (row : Fin 8) : Qubit :=
  ⟨row, c.1, ⟨c.2.val, by have h := c.2.isLt; omega⟩⟩

/-- The member of the hidden chain `d` lying in unit-cell column `col`: the
horizontal qubit `(d.1, col, 4 + d.2)`. -/
def hiddenQubit (d : HChain) (col : Fin 8) : Qubit :=
  ⟨d.1, col, ⟨4 + d.2.val, by have h := d.2.isLt; omega⟩⟩

/-- Visible-chain qubits are vertical. -/
theorem visibleQubit_vertical (c : VChain) (row : Fin 8) :
    (visibleQubit c row).isVertical := by
  show c.2.val < 4
  exact c.2.isLt

/-- Hidden-chain qubits are horizontal. -/
theorem hiddenQubit_horizontal (d : HChain) (col : Fin 8) :
    (hiddenQubit d col).isHorizontal := by
  show 4 ≤ 4 + d.2.val
  omega

/-- A qubit of visible chain `c` and a qubit of hidden chain `d` are coupled iff
they lie in the same unit cell, i.e. the visible member has row `d.1` and the
hidden member has column `c.1`. -/
theorem visibleQubit_coupled_iff (c : VChain) (d : HChain) (row col : Fin 8) :
    Coupled (visibleQubit c row) (hiddenQubit d col) ↔ row = d.1 ∧ c.1 = col := by
  unfold Coupled
  constructor
  · rintro ⟨h1, h2, _⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, c.2.isLt, by show 4 ≤ 4 + d.2.val; omega⟩

/-- Every visible chain meets every hidden chain in at most one unit cell: the
cell `(d.1, c.1)`. -/
theorem visible_hidden_meet_once (c : VChain) (d : HChain) :
    ∃! p : Fin 8 × Fin 8, Coupled (visibleQubit c p.1) (hiddenQubit d p.2) := by
  refine ⟨(d.1, c.1), ?_, ?_⟩
  · show Coupled (visibleQubit c d.1) (hiddenQubit d c.1)
    rw [visibleQubit_coupled_iff]
    exact ⟨rfl, rfl⟩
  · rintro ⟨row, col⟩ hp
    rw [visibleQubit_coupled_iff] at hp
    have hrow : row = d.1 := hp.1
    have hcol : col = c.1 := hp.2.symm
    subst hrow
    subst hcol
    rfl

/-- A hardware coupler between a vertical and a horizontal qubit of one unit
cell, indexed by the cell row/column and the vertical/horizontal slots. -/
structure Coupler where
  row : Fin 8
  col : Fin 8
  v : Fin 4
  h : Fin 4
deriving DecidableEq, Fintype

/-- The coupler seen as its four indices; the chip has `8·8·4·4 = 1024`
variable couplers (16 per unit cell, 64 cells). -/
def couplerEquiv : Coupler ≃ (Fin 8 × Fin 8 × Fin 4 × Fin 4) where
  toFun k := (k.row, k.col, k.v, k.h)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv := by intro k; cases k; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- The ideal 8×8 chip has 1024 couplers. -/
theorem coupler_card : Fintype.card Coupler = 1024 := by
  rw [Fintype.card_congr couplerEquiv]
  simp

/-- The two physical qubits used by a coupler: its vertical and horizontal
qubit. -/
def Coupler.qv (k : Coupler) : Qubit :=
  ⟨k.row, k.col, ⟨k.v.val, by have h := k.v.isLt; omega⟩⟩

/-- The horizontal physical qubit used by a coupler. -/
def Coupler.qh (k : Coupler) : Qubit :=
  ⟨k.row, k.col, ⟨4 + k.h.val, by have h := k.h.isLt; omega⟩⟩

/-- A coupler's two qubits are adjacent in the hardware graph. -/
theorem Coupler.coupled (k : Coupler) : Coupled k.qv k.qh := by
  refine ⟨rfl, rfl, k.v.isLt, ?_⟩
  show 4 ≤ 4 + k.h.val
  omega

/-- **Full 32×32 bipartite realization.**  For every pair (visible chain,
hidden chain) there is exactly one hardware coupler between them; since there
are 32 visible and 32 hidden chain indices, the ideal 512-qubit chip realizes
all 1024 visible-hidden connections (Sec. 3.2.2, p. 9). -/
theorem couplers_realize_full_bipartite :
    (∀ c : VChain, ∀ d : HChain, ∃! k : Coupler,
      Coupled (visibleQubit c k.row) (hiddenQubit d k.col)
        ∧ k.v = c.2 ∧ k.h = d.2) ∧
    Fintype.card VChain * Fintype.card HChain = 1024 := by
  constructor
  · intro c d
    refine ⟨⟨d.1, c.1, c.2, d.2⟩, ?_, ?_⟩
    · exact ⟨(visibleQubit_coupled_iff c d d.1 c.1).2 ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨row, col, v, h⟩ ⟨hcoup, hv, hh⟩
      rw [visibleQubit_coupled_iff] at hcoup
      obtain ⟨h1, h2⟩ := hcoup
      subst hv
      subst hh
      subst h1
      have hcol : col = c.1 := h2.symm
      subst hcol
      rfl
  · simp [VChain, HChain]

/-- A faulty qubit of a given orientation: unit-cell row, unit-cell column and
the slot inside the vertical (`v`) or horizontal (`h`) half. -/
abbrev PhysIndex := Fin 8 × Fin 8 × Fin 4

/-- Couplers whose vertical qubit lies in the faulty-vertical set `Fv`. -/
def lostV (Fv : Finset PhysIndex) : Finset Coupler :=
  (Fv ×ˢ (Finset.univ : Finset (Fin 4))).image
    fun p => ⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩

/-- Couplers whose horizontal qubit lies in the faulty-horizontal set `Fh`. -/
def lostH (Fh : Finset PhysIndex) : Finset Coupler :=
  (Fh ×ˢ (Finset.univ : Finset (Fin 4))).image
    fun p => ⟨p.1.1, p.1.2.1, p.2, p.1.2.2⟩

/-- A single faulty qubit is incident to exactly 4 couplers, so the couplers
lost to `Fv` number exactly `4 * |Fv|`. -/
theorem lostV_card (Fv : Finset PhysIndex) : (lostV Fv).card = 4 * Fv.card := by
  unfold lostV
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_product]
    simp [Nat.mul_comm]
  · rintro ⟨⟨r, c, v⟩, l⟩ ⟨⟨r', c', v'⟩, l'⟩ h
    simp only [Coupler.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl

/-- A single faulty qubit is incident to exactly 4 couplers, so the couplers
lost to `Fh` number exactly `4 * |Fh|`. -/
theorem lostH_card (Fh : Finset PhysIndex) : (lostH Fh).card = 4 * Fh.card := by
  unfold lostH
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_product]
    simp [Nat.mul_comm]
  · rintro ⟨⟨r, c, v⟩, l⟩ ⟨⟨r', c', v'⟩, l'⟩ h
    simp only [Coupler.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl

/-- All couplers destroyed by a set of faulty vertical qubits and a set of
faulty horizontal qubits. -/
def lostCouplers (Fv Fh : Finset PhysIndex) : Finset Coupler :=
  lostV Fv ∪ lostH Fh

/-- Each faulty qubit costs at most 4 couplers: the lost set has at most
`4|Fv| + 4|Fh|` elements. -/
theorem lostCouplers_card_le (Fv Fh : Finset PhysIndex) :
    (lostCouplers Fv Fh).card ≤ 4 * Fv.card + 4 * Fh.card := by
  unfold lostCouplers
  refine (Finset.card_union_le _ _).trans ?_
  rw [lostV_card, lostH_card]

/-- The couplers that remain usable on a chip with faulty qubits. -/
noncomputable def usableCouplers (Fv Fh : Finset PhysIndex) : Finset Coupler :=
  Finset.univ \ lostCouplers Fv Fh

/-- Number of usable couplers: 1024 minus the lost ones. -/
theorem usableCouplers_card (Fv Fh : Finset PhysIndex) :
    (usableCouplers Fv Fh).card = Fintype.card Coupler - (lostCouplers Fv Fh).card := by
  unfold usableCouplers
  rw [Finset.card_sdiff]
  simp

/-- **Faulty-qubit robustness.**  On a chip with 8 faulty qubits (any split
between vertical and horizontal), at most `4 · 8 = 32` of the 1024 couplers are
lost, so at least 992 couplers remain usable.  This is the combinatorial
content of "we have successfully trained ... on a 512-qubit D-Wave machine with
8 faulty qubits", where the paper reports exactly 32 of 1024 connections
missing (Sec. 3.2.2, p. 10). -/
theorem usableCouplers_card_ge (Fv Fh : Finset PhysIndex)
    (h8 : Fv.card + Fh.card = 8) :
    992 ≤ (usableCouplers Fv Fh).card := by
  have hle := lostCouplers_card_le Fv Fh
  have h4 : 4 * Fv.card + 4 * Fh.card = 4 * (Fv.card + Fh.card) := by ring
  rw [h4, h8] at hle
  have hc := usableCouplers_card Fv Fh
  rw [coupler_card] at hc
  omega

/-- **c002 — training scale.**  The 8×8 Chimera chip has 512 physical qubits;
there are 32 visible and 32 hidden chain indices; every visible-hidden chain
pair is joined by exactly one coupler (full 32×32 bipartite graph, 1024
couplers); and any 8 faulty qubits leave at least 992 couplers usable, so a
32 visible × 32 hidden RBM layer remains embeddable. -/
theorem c002_32x32_on_512_qubit_8_faulty :
    Fintype.card Qubit = 512 ∧
    Fintype.card VChain = 32 ∧
    Fintype.card HChain = 32 ∧
    (∀ c : VChain, ∀ d : HChain, ∃! k : Coupler,
      Coupled (visibleQubit c k.row) (hiddenQubit d k.col)
        ∧ k.v = c.2 ∧ k.h = d.2) ∧
    Fintype.card Coupler = 1024 ∧
    (∀ Fv Fh : Finset PhysIndex, Fv.card + Fh.card = 8 →
      992 ≤ (usableCouplers Fv Fh).card) := by
  refine ⟨qubit_card, ?_, ?_, couplers_realize_full_bipartite.1, coupler_card, ?_⟩
  · simp [VChain]
  · simp [HChain]
  · intro Fv Fh h8
    exact usableCouplers_card_ge Fv Fh h8

end Qatlib.Papers.AnnealingDNN15.MainResults.Chimera
