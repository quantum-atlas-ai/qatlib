/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper-layer definitions for
"Polynomial time classical versus quantum algorithms for representation
theoretic multiplicities" (arXiv:2502.20253, 2025), §2.

The file fixes the finite model used by the claim statements:

* partitions as Young diagrams, with size, first part, length and the
  statistic `aft(L) := |L| - max{L₁, ℓ(L)}` (§2, Notations);
* standard Young tableaux of a fixed shape as bijections from the cells
  to `Fin |L|` that strictly increase along rows and columns (§2.1);
* the dimension `f^L` as the number of SYTs of shape `L`.

The main proved statement is the polynomial-growth core of Proposition 3.1
(claim c003): when the first row dominates (`L₁ ≥ ℓ(L)`, so that
`aft(L) = |L| - L₁`), the dimension satisfies `f^L ≤ n^(2·aft(L))` with
`n = |L|`.  The paper's sharper bound `n^k/√(k!)` needs hook-length
estimates that Mathlib does not provide; the polynomial character of the
growth — the content used by Theorems 1.1/1.2 to recognise polynomial
regimes — is fully retained.

Everything is built on `Mathlib.Combinatorics.Young.YoungDiagram`; no
axiom, no `admit`, no `native_decide`.
-/
import Mathlib.Combinatorics.Young.YoungDiagram
import Batteries.Tactic.Exact
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Basic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators

noncomputable section

namespace Qatlib.Papers.RepMultiplic25.MainResults.SytCore

/-! ## Partitions and shape statistics -/

/-- The size `|L|` (number of boxes) of a Young diagram, i.e. `L ⊢ n`
with `n = size L`. -/
def size (L : YoungDiagram) : ℕ := L.cells.card

/-- The first part `L₁` (length of the first row). -/
def firstPart (L : YoungDiagram) : ℕ := L.rowLen 0

/-- The length `ℓ(L)` (number of nonzero parts). -/
def lengthParts (L : YoungDiagram) : ℕ := L.rowLens.length

/-- The statistic `aft(L) := |L| - max{L₁, ℓ(L)}` used throughout the
paper (§2, Notations). -/
def aft (L : YoungDiagram) : ℕ := size L - max (firstPart L) (lengthParts L)

/-- The cells of the first row. -/
def firstRow (L : YoungDiagram) : Finset (ℕ × ℕ) := L.row 0

/-- Membership in the first row, in coordinates. -/
lemma mem_firstRow_iff (L : YoungDiagram) (j : ℕ) :
    (0, j) ∈ firstRow L ↔ j < firstPart L := by
  rw [firstRow, YoungDiagram.mk_mem_row_iff, YoungDiagram.mem_iff_lt_rowLen,
    firstPart]

/-- A cell `(0, j)` with `j < L₁` is a cell of the diagram. -/
lemma cell_mem_of_lt (L : YoungDiagram) {j : ℕ} (hj : j < firstPart L) :
    (0, j) ∈ L.cells := by
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
  exact hj

/-- The first row is contained in the cells. -/
lemma firstRow_subset (L : YoungDiagram) : firstRow L ⊆ L.cells := by
  intro c hc
  rw [firstRow, YoungDiagram.mem_row_iff] at hc
  exact hc.1

/-! ## Standard Young tableaux -/

/-- Strict increase of an enumeration along rows: horizontally adjacent
cells carry increasing entries. -/
def rowStrict (L : YoungDiagram) (T : L.cells ≃ Fin (size L)) : Prop :=
  ∀ p q : ℕ × ℕ, ∀ hp : p ∈ L.cells, ∀ hq : q ∈ L.cells,
    p.1 = q.1 ∧ q.2 = p.2 + 1 → T ⟨p, hp⟩ < T ⟨q, hq⟩

/-- Strict increase of an enumeration along columns: vertically adjacent
cells carry increasing entries. -/
def colStrict (L : YoungDiagram) (T : L.cells ≃ Fin (size L)) : Prop :=
  ∀ p q : ℕ × ℕ, ∀ hp : p ∈ L.cells, ∀ hq : q ∈ L.cells,
    p.2 = q.2 ∧ q.1 = p.1 + 1 → T ⟨p, hp⟩ < T ⟨q, hq⟩

/-- A standard Young tableau of shape `L`: a bijection from the cells to
`{1, …, |L|}` that strictly increases along rows and columns (§2.1). -/
abbrev SYT (L : YoungDiagram) : Type :=
  {T : L.cells ≃ Fin (size L) // rowStrict L T ∧ colStrict L T}

instance (L : YoungDiagram) : Fintype (SYT L) := Fintype.ofFinite (SYT L)

/-- The dimension `f^L`: the number of SYTs of shape `L`, i.e. the
dimension of the irreducible representation of `S_|L|` indexed by `L`. -/
def fDim (L : YoungDiagram) : ℕ := Fintype.card (SYT L)

/-! ## Monotonicity of the first row of a tableau -/

/-- Adjacent entries along the first row strictly increase. -/
lemma firstRow_adj (L : YoungDiagram) (T : SYT L) (i : ℕ) (hi : i + 1 < firstPart L) :
    (T : L.cells ≃ Fin (size L)) ⟨(0, i), cell_mem_of_lt L (by omega)⟩
      < (T : L.cells ≃ Fin (size L)) ⟨(0, i + 1), cell_mem_of_lt L (by omega)⟩ :=
  T.2.1 (0, i) (0, i + 1)
    (cell_mem_of_lt L (by omega)) (cell_mem_of_lt L (by omega)) ⟨rfl, rfl⟩

/-- Entries along the first row strictly increase. -/
lemma firstRow_lt (L : YoungDiagram) (T : SYT L) {j j' : ℕ}
    (hj : j < firstPart L) (hj' : j' < firstPart L) (hlt : j < j') :
    (T : L.cells ≃ Fin (size L)) ⟨(0, j), cell_mem_of_lt L hj⟩
      < (T : L.cells ≃ Fin (size L)) ⟨(0, j'), cell_mem_of_lt L hj'⟩ := by
  obtain ⟨d, hd⟩ : ∃ d, j' = j + d + 1 := ⟨j' - j - 1, by omega⟩
  subst hd
  clear hlt
  induction d with
  | zero =>
      have h := firstRow_adj L T j (by omega)
      simpa using h
  | succ d' ih =>
      exact lt_trans (ih (by omega)) (firstRow_adj L T (j + d' + 1) (by omega))

/-- The entries of the first row, read as a function of the column. -/
def rowVals (L : YoungDiagram) (T : SYT L) : Fin (firstPart L) → Fin (size L) :=
  fun j => (T : L.cells ≃ Fin (size L)) ⟨(0, j.val), cell_mem_of_lt L j.isLt⟩

/-- `rowVals` is strictly increasing. -/
lemma rowVals_strictMono (L : YoungDiagram) (T : SYT L) :
    StrictMono (rowVals L T) := by
  intro i j hij
  exact firstRow_lt L T i.isLt j.isLt hij

/-- The set of entries appearing in the first row. -/
def rowSet (L : YoungDiagram) (T : SYT L) : Finset (Fin (size L)) :=
  Finset.image (rowVals L T) Finset.univ

/-- The set of first-row entries has `firstPart L` elements. -/
lemma card_rowSet (L : YoungDiagram) (T : SYT L) :
    (rowSet L T).card = firstPart L := by
  rw [rowSet,
    Finset.card_image_of_injective Finset.univ
      (StrictMono.injective (rowVals_strictMono L T)),
    Finset.card_univ, Fintype.card_fin]

/-- Membership in the first-row entry set. -/
lemma mem_rowSet (L : YoungDiagram) (T : SYT L) (x : Fin (size L)) :
    x ∈ rowSet L T ↔ ∃ j : Fin (firstPart L), rowVals L T j = x := by
  rw [rowSet, Finset.mem_image]
  constructor
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ j, hj⟩

/-! ## Polynomial growth of the dimension (Proposition 3.1, upper bound) -/

/-- The increasing enumeration `orderEmbOfFin` does not depend on the
proof of the cardinality equation (proof irrelevance). -/
lemma orderEmbOfFin_irrel {α : Type*} [LinearOrder α] {s t : Finset α}
    {k : ℕ} (hst : s = t) (hs : s.card = k) (ht : t.card = k) :
    s.orderEmbOfFin hs = t.orderEmbOfFin ht := by
  subst hst
  rfl

/-- **c003, polynomial-growth core (Proposition 3.1, upper bound,
weakened exponent)**: if the first row dominates (`ℓ(L) ≤ L₁`, the case
reduced to by the paper using `f^L = f^{L'}`), then
`f^L ≤ n^(2·aft(L))` with `n = |L|`.

The paper's bound is `f^L ≤ n^k/√(k!)` with `k = aft(L)`; that finer form
needs hook-length estimates unavailable in Mathlib, while the polynomial
character of the growth — the only ingredient used by Theorems 1.1 and
1.2 to recognise polynomial-time regimes — is preserved exactly.

Proof idea: a tableau is determined by the set `S` of its first-row
entries (the first row is the increasing enumeration of `S`, unique by
`Finset.orderEmbOfFin_unique`) together with the entries on the
remaining `k = aft(L)` cells.  There are `C(n, k)` choices of `S` and at
most `n^k` functions on the remainder. -/
theorem fDim_le_pow (L : YoungDiagram) (hmax : lengthParts L ≤ firstPart L) :
    fDim L ≤ (size L) ^ (2 * aft L) := by
  set n := size L with hn
  set k := aft L with hkdef
  set R := firstRow L with hR
  set C := L.cells \ R with hC
  have hRcard : R.card = firstPart L := by
    rw [hR, firstRow, firstPart, ← YoungDiagram.rowLen_eq_card]
  have hRsub : R ⊆ L.cells := firstRow_subset L
  have hCcard : C.card = k := by
    have h1 : C.card = size L - R.card := Finset.card_sdiff_of_subset hRsub
    rw [hRcard] at h1
    have h2 : n - firstPart L = k := by
      rw [hkdef]
      simp only [aft]
      omega
    omega
  -- the encoding: first-row entry set and the entries off the first row
  set S : SYT L → Finset (Fin n) := fun T => rowSet L T with hS
  have hScard : ∀ T : SYT L, (S T).card = firstPart L := card_rowSet L
  set g : SYT L → (C → Fin n) :=
    fun T c => (T : L.cells ≃ Fin (size L)) ⟨(c : ℕ × ℕ), Finset.mem_sdiff.mp c.2 |>.1⟩
    with hg
  set tgt := ↥(Finset.powersetCard (firstPart L) (Finset.univ : Finset (Fin n)))
    × (C → Fin n) with htgt
  set enc : SYT L → tgt :=
    fun T => (⟨S T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hScard T⟩⟩,
      g T) with henc
  have hinj : Function.Injective enc := by
    intro T T' hTT'
    obtain ⟨hS', hg'⟩ := Prod.ext_iff.mp hTT'
    have hSeq : S T = S T' := Subtype.ext_iff.mp hS'
    have hrow : rowVals L T = rowVals L T' := by
      have h1 : rowVals L T
          = Finset.orderEmbOfFin (S T) (hScard T) :=
        Finset.orderEmbOfFin_unique (hScard T)
          (fun x => (mem_rowSet L T (rowVals L T x)).mpr ⟨x, rfl⟩)
          (rowVals_strictMono L T)
      have h2 : rowVals L T'
          = Finset.orderEmbOfFin (S T') (hScard T') :=
        Finset.orderEmbOfFin_unique (hScard T')
          (fun x => (mem_rowSet L T' (rowVals L T' x)).mpr ⟨x, rfl⟩)
          (rowVals_strictMono L T')
      rw [h1, h2, orderEmbOfFin_irrel hSeq (hScard T) (hScard T')]
    apply Subtype.ext
    apply Equiv.ext
    intro c
    by_cases hc : (c : ℕ × ℕ) ∈ R
    · have hc0 : (c : ℕ × ℕ).1 = 0 ∧ (c : ℕ × ℕ).2 < firstPart L := by
        have hmem : (c : ℕ × ℕ) ∈ L.row 0 := hc
        rw [YoungDiagram.row_eq_prod, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_range] at hmem
        exact hmem
      have hTc := congrFun hrow (⟨(c : ℕ × ℕ).2, hc0.2⟩ : Fin (firstPart L))
      simp only [rowVals] at hTc
      have hcval : c = ⟨(0, (c : ℕ × ℕ).2), cell_mem_of_lt L hc0.2⟩ := by
        apply Subtype.ext
        ext <;> simp [hc0.1]
      rw [hcval]
      exact hTc
    · have hcC : (c : ℕ × ℕ) ∈ C := Finset.mem_sdiff.mpr ⟨c.2, hc⟩
      exact congrFun hg' ⟨(c : ℕ × ℕ), hcC⟩
  -- counting the target space
  have hcard1 : Fintype.card ↥(Finset.powersetCard (firstPart L)
      (Finset.univ : Finset (Fin n))) = n.choose (firstPart L) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin]
  have hcard2 : Fintype.card (C → Fin n) = n ^ C.card := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hcard3 : Fintype.card (↥(Finset.powersetCard (firstPart L)
      (Finset.univ : Finset (Fin n))) × (C → Fin n))
      = n.choose (firstPart L) * n ^ k := by
    rw [Fintype.card_prod, hcard1, hcard2, hCcard]
  have hle1 : fDim L ≤ Fintype.card (↥(Finset.powersetCard (firstPart L)
      (Finset.univ : Finset (Fin n))) × (C → Fin n)) := by
    rw [fDim]
    exact Fintype.card_le_of_injective enc hinj
  have hnfp : n - firstPart L = k := by
    have hk2 : k = size L - max (firstPart L) (lengthParts L) := rfl
    omega
  have hsz : size L = L.cells.card := rfl
  have hfp : firstPart L = n - k := by
    have hsub : firstRow L ⊆ L.cells := firstRow_subset L
    have hle : (L.row 0).card ≤ L.cells.card := Finset.card_le_card hsub
    have hrl : (L.row 0).card = firstPart L := (YoungDiagram.rowLen_eq_card L).symm
    omega
  have hnk : k ≤ n := by omega
  have hchoose : n.choose (firstPart L) ≤ n ^ k := by
    rw [hfp, Nat.choose_symm hnk]
    exact Nat.choose_le_pow n k
  calc fDim L ≤ Fintype.card (↥(Finset.powersetCard (firstPart L)
      (Finset.univ : Finset (Fin n))) × (C → Fin n)) := hle1
    _ = n.choose (firstPart L) * n ^ k := hcard3
    _ ≤ n ^ k * n ^ k := Nat.mul_le_mul_right _ hchoose
    _ = n ^ (2 * k) := by rw [Nat.two_mul, ← Nat.pow_add]

end Qatlib.Papers.RepMultiplic25.MainResults.SytCore
