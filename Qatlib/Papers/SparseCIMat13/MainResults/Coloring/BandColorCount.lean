/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright: paper-layer formalization for SparseCIMat13.
Source: B. Toloui and P. J. Love, "Quantum Algorithms for Quantum Chemistry based on the
sparsity of the CI-matrix", arXiv:1312.2579 (2013), Section III E p.8, Eqs. (23)-(26).
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Band colouring of the CI graph (arXiv:1312.2579, Section III E, Eqs. (23)-(26))

The band-colouring scheme assigns

* label `0` to the diagonal self-loop of every node (Eq. (23)); there is one such colour;
* one label `(d,u)` to every single-excitation class: `d` is an occupied orbital of `x`,
  `u` an empty orbital, so there are `ne (no-ne)` classes (Eq. (24));
* one label `(d1,u1;d2,u2)` per pair-excitation class: choose two occupied and two empty
  orbitals, `C(ne,2) C(no-ne,2)` classes (Eq. (25)).

Eq. (26) says the total number of colours is exactly the CI sparsity `d` of Eq. (9) — the
band scheme is "linear in the sparsity".  The general `(i,j)` scheme of Section III D uses
at most `d^2` colours, so `d ≤ d^2`.  This file defines the band-label type and proves both
counts.
-/

namespace Qatlib.Papers.SparseCIMat13.MainResults.Coloring

open Finset

/-- Paper Eq. (9) (restated here so this module is self-contained): the CI row degree
`d = C(ne,2) C(no-ne,2) + ne(no-ne) + 1`. -/
def ciRowDegree (no ne : ℕ) : ℕ :=
  Nat.choose ne 2 * Nat.choose (no - ne) 2 + ne * (no - ne) + 1

/-- Number of single-excitation colour classes (Eq. (24)): an occupied orbital `d` and an
empty orbital `u` are exchanged, giving `ne (no-ne)` labels. -/
def singleLabelCount (no ne : ℕ) : ℕ := ne * (no - ne)

/-- Number of pair-excitation colour classes (Eq. (25)): two occupied and two empty
orbitals, `C(ne,2) C(no-ne,2)` labels. -/
def pairLabelCount (no ne : ℕ) : ℕ := Nat.choose ne 2 * Nat.choose (no - ne) 2

/-- Total number of band-colouring labels (Eq. (26)): the diagonal label `0` plus the
single- and pair-excitation classes. -/
def bandColorCount (no ne : ℕ) : ℕ := 1 + singleLabelCount no ne + pairLabelCount no ne

/-- The concrete band label type: `0` (diagonal), a single-excitation label `(d,u)`, or a
pair-excitation label `(d1,u1;d2,u2)` with `d1`/`d2` the deleted and `u1`/`u2` the inserted
orbitals.  The sets are unordered, represented by 2-element finsets. -/
abbrev BandLabel (no ne : ℕ) : Type :=
  Unit ⊕ ((Fin ne × Fin (no - ne)) ⊕
    ({s : Finset (Fin ne) // s.card = 2} ×
     {t : Finset (Fin (no - ne)) // t.card = 2}))

/-- Cardinality of the 2-element subsets of `Fin n` is `C(n,2)` (Eq. (25) count). -/
theorem card_two_subsets (n : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card = 2} = Nat.choose n 2 := by
  classical
  have h : Fintype.card {s : Finset (Fin n) // s.card = 2} =
      (Finset.univ.powersetCard 2 : Finset (Finset (Fin n))).card :=
    Fintype.card_of_subtype (p := fun s : Finset (Fin n) => s.card = 2)
      (Finset.univ.powersetCard 2) (fun s => by simp)
  rw [h, Finset.card_powersetCard]
  simp

/-- Paper Eq. (26): the band-colouring scheme uses exactly `d` colours, the CI sparsity of
Eq. (9) — i.e. the number of one-sparse summands is linear in `d`, not `d^2`. -/
theorem bandColorCount_eq_ciRowDegree (no ne : ℕ) :
    bandColorCount no ne = ciRowDegree no ne := by
  unfold bandColorCount singleLabelCount pairLabelCount ciRowDegree
  ring

/-- The band-label type really has `d` elements: `card (BandLabel no ne) = d`. -/
theorem card_BandLabel (no ne : ℕ) :
    Fintype.card (BandLabel no ne) = ciRowDegree no ne := by
  classical
  have h1 : Fintype.card (BandLabel no ne) =
      1 + (ne * (no - ne) +
        (Fintype.card {s : Finset (Fin ne) // s.card = 2} *
         Fintype.card {t : Finset (Fin (no - ne)) // t.card = 2})) := by
    simp only [BandLabel, Fintype.card_sum, Fintype.card_unit, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe]
  rw [h1, card_two_subsets, card_two_subsets]
  unfold ciRowDegree
  ring

/-- The general `(i,j)` coluring of Section III D uses at most `d^2` colour pairs; the
band scheme needs only `d` of them.  This is the numerical content of "in fact only `d`
colors are actually required". -/
theorem bandColorCount_le_sq (no ne : ℕ) :
    bandColorCount no ne ≤ ciRowDegree no ne ^ 2 := by
  have hd : 0 < ciRowDegree no ne := by unfold ciRowDegree; omega
  have h1 : ciRowDegree no ne ≤ ciRowDegree no ne * ciRowDegree no ne :=
    Nat.le_mul_of_pos_right _ hd
  have h2 : ciRowDegree no ne * ciRowDegree no ne = ciRowDegree no ne ^ 2 :=
    (pow_two _).symm
  rw [bandColorCount_eq_ciRowDegree]
  omega

end Qatlib.Papers.SparseCIMat13.MainResults.Coloring
