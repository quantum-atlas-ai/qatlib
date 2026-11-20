/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Tanner graphs of binary check matrices

A check matrix defines a simple bipartite graph with one vertex per check and one per data
coordinate. A four-cycle yields a nonzero rectangle in the matrix. A rectangle exclusion
certificate and a six-cycle witness therefore certify extended girth six.
-/

namespace Qatlib.Concepts.CodeCert.DistCert

set_option autoImplicit false

variable {ι κ : Type*}

/-- Edges of the Tanner graph are exactly the nonzero check incidences. -/
def tanner (A : Matrix κ ι (ZMod 2)) : SimpleGraph (κ ⊕ ι) where
  Adj u v := match u, v with
    | .inl r, .inr i => A r i ≠ 0
    | .inr i, .inl r => A r i ≠ 0
    | _, _ => False
  symm := ⟨by
    intro u v h
    cases u <;> cases v <;> exact h⟩
  loopless := ⟨by
    intro u h
    cases u <;> exact h⟩

private def side (v : κ ⊕ ι) : ℕ :=
  match v with
  | .inl _ => 0
  | .inr _ => 1

/-- The parity of a walk is determined by the parts of its two endpoints. -/
private theorem walk_parity (A : Matrix κ ι (ZMod 2)) {u v : κ ⊕ ι}
    (w : (tanner A).Walk u v) : w.length % 2 = (side u + side v) % 2 := by
  induction w with
  | nil => simp only [SimpleGraph.Walk.length_nil]; omega
  | @cons u s v h w ih =>
    have hs : side u + side s = 1 := by
      cases u <;> cases s <;> simp_all [tanner, side]
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- A closed Tanner walk has even length. -/
theorem closed_parity (A : Matrix κ ι (ZMod 2)) {v : κ ⊕ ι}
    (w : (tanner A).Walk v v) : w.length % 2 = 0 := by
  have h := walk_parity A w
  omega

/-- Two distinct rows and columns cannot have all four incidences. -/
abbrev NoRect (A : Matrix κ ι (ZMod 2)) : Prop :=
  ∀ (r s : κ) (i j : ι), r ≠ s → i ≠ j →
    ¬ (A r i ≠ 0 ∧ A r j ≠ 0 ∧ A s i ≠ 0 ∧ A s j ≠ 0)

/-- A finite check of all rectangles in the binary incidence matrix. -/
def checkRect [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (ZMod 2)) : Bool :=
  decide ((Finset.univ.filter (fun p : κ × κ × ι × ι =>
    p.1 ≠ p.2.1 ∧ p.2.2.1 ≠ p.2.2.2 ∧
      A p.1 p.2.2.1 ≠ 0 ∧ A p.1 p.2.2.2 ≠ 0 ∧
      A p.2.1 p.2.2.1 ≠ 0 ∧ A p.2.1 p.2.2.2 ≠ 0)).card = 0)

/-- The finite rectangle checker is exact. -/
theorem checkRect_iff [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (ZMod 2)) : checkRect A = true ↔ NoRect A := by
  rw [checkRect, decide_eq_true_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h r s i j hrs hij hp
    exact h (x := (r, s, i, j)) (Finset.mem_univ _) ⟨hrs, hij, hp⟩
  · rintro h ⟨r, s, i, j⟩ _ ⟨hrs, hij, hp⟩
    exact h r s i j hrs hij hp

/-- A Tanner four-cycle would use two distinct rows and columns forming a nonzero rectangle. -/
theorem no_four (A : Matrix κ ι (ZMod 2)) (hrect : NoRect A) {v : κ ⊕ ι}
    {w : (tanner A).Walk v v} (hw : w.IsCycle) : w.length ≠ 4 := by
  intro len
  let x0 := w.getVert 0
  let x1 := w.getVert 1
  let x2 := w.getVert 2
  let x3 := w.getVert 3
  have e01 : (tanner A).Adj x0 x1 := w.adj_getVert_succ (i := 0) (by omega)
  have e12 : (tanner A).Adj x1 x2 := w.adj_getVert_succ (i := 1) (by omega)
  have e23 : (tanner A).Adj x2 x3 := w.adj_getVert_succ (i := 2) (by omega)
  have e30 : (tanner A).Adj x3 x0 := by
    have e : (tanner A).Adj x3 (w.getVert 4) := w.adj_getVert_succ (i := 3) (by omega)
    simpa only [x0, ← len, SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length]
      using e
  have n02 : x0 ≠ x2 := by
    intro e
    have h : (0 : ℕ) = 2 := hw.getVert_injOn' (by simp [len]) (by simp [len]) e
    omega
  have n13 : x1 ≠ x3 := by
    intro e
    have h : (1 : ℕ) = 3 := hw.getVert_injOn' (by simp [len]) (by simp [len]) e
    omega
  rcases x0 with r0 | i0 <;> rcases x1 with r1 | i1 <;>
    rcases x2 with r2 | i2 <;> rcases x3 with r3 | i3 <;>
    simp [tanner] at e01 e12 e23 e30 n02 n13
  · exact hrect r0 r2 i1 i3 n02 n13 ⟨e01, e30, e12, e23⟩
  · exact hrect r1 r3 i0 i2 n13 n02 ⟨e01, e12, e30, e23⟩

/-- Rectangle exclusion and a six-cycle witness certify Tanner girth six. -/
theorem girth_six (A : Matrix κ ι (ZMod 2)) (hrect : NoRect A) {v : κ ⊕ ι}
    {w : (tanner A).Walk v v} (hw : w.IsCycle) (hlen : w.length = 6) :
    (tanner A).egirth = 6 := by
  apply le_antisymm
  · simpa [hlen] using hw.egirth_le_length
  · rw [SimpleGraph.le_egirth]
    intro a p hp
    have hmin := hp.three_le_length
    have hpar := closed_parity A p
    have h4 := no_four A hrect hp
    have h : 6 ≤ p.length := by omega
    exact_mod_cast h

end Qatlib.Concepts.CodeCert.DistCert
