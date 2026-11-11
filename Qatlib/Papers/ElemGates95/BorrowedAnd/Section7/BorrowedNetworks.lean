/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis

/-!
# Borrowed-wire AND networks

This module presents the borrowed-wire constructions behind Lemmas 7.2 and 7.3 of
[BarencoEtAl1995] as explicit Toffoli words and elementary-gate lists. `dirtyPrefixWord` and
`borrowedAndWord` encode the recursive prefix computation and its two-pass use, while
`expandToffolis` replaces every Toffoli call by its local elementary implementation.

Under the stated wire-layout conditions, `lemma7_2` toggles a target by the conjunction of `r +
2` controls using `r` wires with arbitrary initial values, restoring every wire except the
target. `lemma7_3_composition` proves the four-block identity for two supplied legal programs
and control predicates invariant under changes to the borrowed wire and target.

## Main statements

* `borrowedAndWord_length` gives exactly `4 * r` Toffoli calls for `r >= 1`.
* `lemma7_2` gives a legal expansion of length `60 * r` with the required computational-basis
  action.
* `lemma7_3_composition` proves legality, length, and the target action of `as ++ bs ++ as ++
  bs`.

## References

* [Barenco et al., 1995][BarencoEtAl1995], Section 7, Lemmas 7.2 and 7.3.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.ElemGates95.BorrowedAnd.Section7

/-- A Toffoli call represented by its two control wires and target wire in an `N`-wire register. -/
abbrev ToffoliCall (N : ℕ) := Fin N × Fin N × Fin N

/-- Expands a list of Toffoli calls by concatenating the elementary-gate implementation
`toffoliLocalSteps` for each call. -/
def expandToffolis {N : ℕ} (w : List (ToffoliCall N)) : List (ReflectionGate N) :=
  w.flatMap (fun g => toffoliLocalSteps g.1 g.2.1 g.2.2)

/-- The recursive Toffoli word for the dirty-wire prefix computation. At each recursive stage,
the previous word is enclosed between two identical calls using the next control and
borrowed wire. -/
def dirtyPrefixWord {N : ℕ} (c w : ℕ → Fin N) : ℕ → List (ToffoliCall N)
  | 0 => []
  | 1 => [(c 0, c 1, w 0)]
  | r + 2 => [(c (r + 2), w r, w (r + 1))] ++ dirtyPrefixWord c w (r + 1) ++
      [(c (r + 2), w r, w (r + 1))]

/-- The dirty-prefix word contains `2 * r - 1` Toffoli calls, with subtraction taken in the
natural numbers. -/
theorem dirtyPrefixWord_length {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) :
    (dirtyPrefixWord c w r).length = 2 * r - 1 := by
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more r _ ih =>
    simp only [dirtyPrefixWord, List.length_append, List.length_singleton, ih]
    omega

/-- Expanding the dirty-prefix Toffoli word gives exactly the elementary-gate list
`noWorkDirtyPrefixSteps`. -/
theorem expand_dirtyPrefixWord {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) :
    expandToffolis (dirtyPrefixWord c w r) = noWorkDirtyPrefixSteps c w r := by
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [expandToffolis, dirtyPrefixWord, noWorkDirtyPrefixSteps]
  | more r _ ih =>
    simp only [dirtyPrefixWord, expandToffolis, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil] at *
    rw [ih]
    rfl

/-- The Toffoli word for the borrowed-wire AND construction, alternating a target call with two
copies of the dirty-prefix word. -/
def borrowedAndWord {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    List (ToffoliCall N) :=
  [(c (r + 1), w (r - 1), t)] ++ dirtyPrefixWord c w r ++
    [(c (r + 1), w (r - 1), t)] ++ dirtyPrefixWord c w r

/-- For `r >= 1`, the borrowed-wire AND word contains exactly `4 * r` Toffoli calls. -/
theorem borrowedAndWord_length {N : ℕ} (c w : ℕ → Fin N) (t : Fin N)
    (r : ℕ) (hr : 1 ≤ r) : (borrowedAndWord c w t r).length = 4 * r := by
  simp only [borrowedAndWord, List.length_append, List.length_singleton,
    dirtyPrefixWord_length]
  omega

/-- Expanding the borrowed-wire AND word gives exactly the elementary-gate list
`noWorkBorrowedAndSteps`. -/
theorem expand_borrowedAndWord {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    expandToffolis (borrowedAndWord c w t r) = noWorkBorrowedAndSteps c w t r := by
  simp only [borrowedAndWord, expandToffolis, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, noWorkBorrowedAndSteps]
  rw [show (dirtyPrefixWord c w r).flatMap
      (fun g => toffoliLocalSteps g.1 g.2.1 g.2.2) = noWorkDirtyPrefixSteps c w r
      from expand_dirtyPrefixWord c w r]

/-- Under the stated layout conditions and `r >= 1`, there is a word of `4 * r` Toffoli calls
whose legal expansion has `60 * r` elementary gates and toggles the target by the
conjunction of `r + 2` controls. All other register values, including the arbitrary initial
borrowed values, are restored, realizing the borrowed-wire construction of Lemma 7.2 in
[BarencoEtAl1995]. -/
theorem lemma7_2 {N : ℕ} (c w : ℕ → Fin N) (t : Fin N)
    (r : ℕ) (hr : 1 ≤ r) (h : noWorkDirtyPrefixLayout c w r)
    (hlast : ∀ j < r, c (r + 1) ≠ w j)
    (hct : ∀ i < r + 2, c i ≠ t) (hwt : ∀ j < r, w j ≠ t) :
    ∃ word : List (ToffoliCall N), word.length = 4 * r ∧
      reflectionLegal (expandToffolis word) ∧
      (expandToffolis word).length = 60 * r ∧
      ∀ x : Reg N, Run (1 : Matrix (Reg N) (Reg N) ℂ)
        (reflectionCompile (expandToffolis word)) (Ket x) =
        Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) (r + 2))) := by
  refine ⟨borrowedAndWord c w t r, borrowedAndWord_length c w t r hr, ?_⟩
  rw [expand_borrowedAndWord]
  exact ⟨noWorkBorrowedAndSteps_legal c w t r hr h hlast hct hwt,
    noWorkBorrowedAndSteps_length c w t r hr,
    noWorkBorrowedAndSteps_ket c w t r hr h hlast hct hwt⟩

/-- If the supplied legal programs toggle `s` by `A` and `t` by `B && x s`, and both predicates
are invariant under updates to `s` and `t`, their four-block concatenation toggles only `t`
by `A && B`. It also has length `2 * as.length + 2 * bs.length`, formalizing the composition
identity used in Lemma 7.3 of [BarencoEtAl1995]. -/
theorem lemma7_3_composition {N : ℕ} (s t : Fin N) (hst : s ≠ t)
    (A B : Reg N → Bool)
    (ha : ∀ (x : Reg N) (v : Bool), A (Function.update x s v) = A x ∧
      A (Function.update x t v) = A x)
    (hb : ∀ (x : Reg N) (v : Bool), B (Function.update x s v) = B x ∧
      B (Function.update x t v) = B x)
    (as bs : List (ReflectionGate N))
    (hal : reflectionLegal as) (hbl : reflectionLegal bs)
    (has : ∀ x : Reg N, Run 1 (reflectionCompile as) (Ket x) =
      Ket (Function.update x s (x s ^^ A x)))
    (hbs : ∀ x : Reg N, Run 1 (reflectionCompile bs) (Ket x) =
      Ket (Function.update x t (x t ^^ (B x && x s)))) :
    reflectionLegal (as ++ bs ++ as ++ bs) ∧
      (as ++ bs ++ as ++ bs).length = 2 * as.length + 2 * bs.length ∧
      ∀ x : Reg N, Run (1 : Matrix (Reg N) (Reg N) ℂ)
        (reflectionCompile (as ++ bs ++ as ++ bs)) (Ket x) =
        Ket (Function.update x t (x t ^^ (A x && B x))) := by
  refine ⟨?_, ?_, noWork_dirty_and_combine s t hst A B ha hb as bs has hbs⟩
  · simp only [reflectionLegal_append]
    exact ⟨⟨⟨hal, hbl⟩, hal⟩, hbl⟩
  · simp only [List.length_append]
    omega

end Qatlib.Papers.ElemGates95.BorrowedAnd.Section7
