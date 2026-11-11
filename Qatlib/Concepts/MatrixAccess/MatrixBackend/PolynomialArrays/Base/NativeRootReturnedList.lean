/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootDecodedCertificate
import Mathlib.Data.List.FinRange

set_option backward.isDefEq.respectTransparency false

/-! Source-order inside-index selection and exponent replication. Coordinate
collisions are preserved; no toFinset/dedup is used in the returned list.
The whole inside-multiset/count connection is in NativeRootReturnedCompleteness. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Abbreviation for Root Decoded Index in the native root returned list model. -/
abbrev RootDecodedIndex {m : ℕ} (f : Fin m → RootIntegerFactorData) :=
  (j : Fin m) × Fin ((f j).n+1)

/-- Outer factor order, inner disk order, then the actual exponent copies. -/
def rootDecodedReturnIndices {m : ℕ} (f : Fin m → RootIntegerFactorData) :
    List (RootDecodedIndex f) :=
  (List.finRange m).flatMap (fun j =>
    (List.finRange ((f j).n+1)).flatMap (fun i =>
      if rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true
      then List.replicate (f j).exponent ⟨j,i⟩ else []))

/-- Exactly the computed grid coordinates in that selected/repeated order. -/
def rootDecodedReturnList {m : ℕ} (f : Fin m → RootIntegerFactorData) (eta : ℚ) :
    List (ℚ×ℚ) :=
  (rootDecodedReturnIndices f).map
    (fun s => rootGridPoint ((f s.1).centers s.2) (eta/16))

/-- The finite construction in `NativeRootReturnedList` satisfies `rootDecodedReturnIndices_inside` under the displayed hypotheses. -/
theorem rootDecodedReturnIndices_inside {m : ℕ} (f : Fin m → RootIntegerFactorData)
    (s : RootDecodedIndex f) (hs : s∈rootDecodedReturnIndices f) :
    rootRationalDiskComputedTag ((f s.1).centers s.2) ((f s.1).radii s.2)=true := by
  obtain ⟨j,_,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨i,_,hs⟩ := List.mem_flatMap.mp hs
  by_cases ht : rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true
  · simp only [ite_eq_left ht] at hs
    have he : s=(⟨j,i⟩ : RootDecodedIndex f) := (List.mem_replicate.mp hs).2
    subst s
    exact ht
  · simp only [ite_eq_right ht,List.not_mem_nil] at hs

/-- The finite construction in `NativeRootReturnedList` satisfies `rootPairMap` under the displayed hypotheses. -/
private theorem rootPairMap {α β γ : Type} (l : List α) (q : α → β) (z : α → γ)
    (R : β → γ → Prop) (h : ∀ s∈l,R (q s) (z s)) :
    List.Forall₂ R (l.map q) (l.map z) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons s rest ih =>
    exact List.Forall₂.cons (h s (by simp))
      (ih (fun t ht => h t (by simp [ht])))

/-- This helper consumes the already-proved same-catalogue inside guarantee.
It is not a new main theorem with output-error answers as assumptions. -/
theorem rootDecodedReturnList_pairing {m : ℕ} (f : Fin m → RootIntegerFactorData)
    (eta : ℚ) (w : (j : Fin m) → Fin ((f j).n+1) → ℂ)
    (hreturn : ∀ j i,rootRationalDiskComputedTag ((f j).centers i) ((f j).radii i)=true →
      ‖rootRationalCoordinate (rootGridPoint ((f j).centers i) (eta/16))‖<1 ∧
      ‖rootRationalCoordinate (rootGridPoint ((f j).centers i) (eta/16))-w j i‖≤(eta : ℝ)) :
    List.Forall₂ (fun q z => ‖rootRationalCoordinate q‖<1 ∧
      ‖rootRationalCoordinate q-z‖≤(eta : ℝ))
      (rootDecodedReturnList f eta)
      ((rootDecodedReturnIndices f).map (fun s => w s.1 s.2)) := by
  apply rootPairMap
  intro s hs
  exact hreturn s.1 s.2 (rootDecodedReturnIndices_inside f s hs)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
