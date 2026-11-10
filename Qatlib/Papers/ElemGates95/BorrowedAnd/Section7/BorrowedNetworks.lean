/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
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

abbrev ToffoliCall (N : ℕ) := Fin N × Fin N × Fin N

def expandToffolis {N : ℕ} (w : List (ToffoliCall N)) : List (ReflectionGate N) :=
  w.flatMap (fun g => toffoliLocalSteps g.1 g.2.1 g.2.2)

def dirtyPrefixWord {N : ℕ} (c w : ℕ → Fin N) : ℕ → List (ToffoliCall N)
  | 0 => []
  | 1 => [(c 0, c 1, w 0)]
  | r + 2 => [(c (r + 2), w r, w (r + 1))] ++ dirtyPrefixWord c w (r + 1) ++
      [(c (r + 2), w r, w (r + 1))]

theorem dirtyPrefixWord_length {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) :
    (dirtyPrefixWord c w r).length = 2 * r - 1 := by
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more r _ ih =>
    simp only [dirtyPrefixWord, List.length_append, List.length_singleton, ih]
    omega

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

def borrowedAndWord {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    List (ToffoliCall N) :=
  [(c (r + 1), w (r - 1), t)] ++ dirtyPrefixWord c w r ++
    [(c (r + 1), w (r - 1), t)] ++ dirtyPrefixWord c w r

theorem borrowedAndWord_length {N : ℕ} (c w : ℕ → Fin N) (t : Fin N)
    (r : ℕ) (hr : 1 ≤ r) : (borrowedAndWord c w t r).length = 4 * r := by
  simp only [borrowedAndWord, List.length_append, List.length_singleton,
    dirtyPrefixWord_length]
  omega

theorem expand_borrowedAndWord {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    expandToffolis (borrowedAndWord c w t r) = noWorkBorrowedAndSteps c w t r := by
  simp only [borrowedAndWord, expandToffolis, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, noWorkBorrowedAndSteps]
  rw [show (dirtyPrefixWord c w r).flatMap
      (fun g => toffoliLocalSteps g.1 g.2.1 g.2.2) = noWorkDirtyPrefixSteps c w r
      from expand_dirtyPrefixWord c w r]

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
