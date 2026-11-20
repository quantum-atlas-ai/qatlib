/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.LogicalOps.Distance

@[expose] public section

/-!
# Branch certificates for CSS distance

A branch state assigns an optional binary Pauli pair to each coordinate. The checker explores
every child at a split. A leaf can close on an exhausted weight budget, a nonzero syndrome row
whose nonzero coefficients are all assigned, or a completely assigned label of no relevance
to the lower bound. An upper witness is checked against the same matrices, weight, and row
spaces as the lower certificate.
-/

namespace Qatlib.Concepts.CodeCert.DistCert

set_option autoImplicit false

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.ErrorCorrection.LogicalOps
open scoped Matrix

variable {ι κX κZ : Type*}

/-- A binary X/Z label at one data coordinate. -/
abbrev Entry := ZMod 2 × ZMod 2

/-- A partial assignment gives a label only at the coordinates already decided. -/
abbrev Partial (ι : Type*) := ι → Option Entry

/-- A finite certificate with a child for every Pauli pair at a split coordinate. -/
inductive Branch (ι κX κZ : Type*) where
  | split (i : ι) (child : Entry → Branch ι κX κZ)
  | heavy
  | closeX (r : κX)
  | closeZ (r : κZ)
  | point

/-- A Pauli label extends all decided coordinates. -/
def Fits (s : Partial ι) (e : PauliLabel ι) : Prop :=
  ∀ i p, s i = some p → (e.1 i, e.2 i) = p

/-- The label obtained by filling every remaining coordinate with the zero pair. -/
def fill (s : Partial ι) : PauliLabel ι :=
  (fun i => ((s i).getD 0).1, fun i => ((s i).getD 0).2)

/-- A filled decided coordinate agrees with any extending label. -/
private theorem fill_eq {s : Partial ι} {e : PauliLabel ι} (hf : Fits s e)
    (i : ι) (hi : (s i).isSome = true) :
    ((fill s).1 i, (fill s).2 i) = (e.1 i, e.2 i) := by
  cases h : s i with
  | none => simp [h] at hi
  | some p => simpa [fill, h] using (hf i p h).symm

/-- A label extending the parent also extends the child selected by its own entry. -/
private theorem fits_update [DecidableEq ι] {s : Partial ι} {e : PauliLabel ι}
    (hf : Fits s e) (i : ι) :
    Fits (Function.update s i (some (e.1 i, e.2 i))) e := by
  intro j p hj
  by_cases hji : j = i
  · subst j
    simpa using hj
  · exact hf j p (by simpa [Function.update_of_ne hji] using hj)

variable [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

/-- Finite coefficient search for membership in both stabilizer row spaces. -/
def checkStab (c : CssData ι κX κZ) (e : PauliLabel ι) : Bool :=
  decide ((∃ a : κX → ZMod 2, c.hXᵀ *ᵥ a = e.1) ∧
    (∃ b : κZ → ZMod 2, c.hZᵀ *ᵥ b = e.2))

omit [DecidableEq ι] in
/-- The finite stabilizer check agrees with the public row-space predicate. -/
theorem checkStab_iff (c : CssData ι κX κZ) (e : PauliLabel ι) :
    checkStab c e = true ↔ IsStabilizerLabel c e := by
  simp only [checkStab, decide_eq_true_eq, IsStabilizerLabel, LinearMap.mem_range,
    Matrix.mulVecLin_apply]

/-- A complete label cannot violate the proposed lower bound when heavy, detectable, or
a stabilizer. -/
def checkPoint (c : CssData ι κX κZ) (d : ℕ) (e : PauliLabel ι) : Bool :=
  decide (d ≤ pauliWeight e.1 e.2 ∨ pauliSyndrome c e ≠ (0, 0)) || checkStab c e

/-- Check an arbitrary branch state against a proposed lower bound. -/
def checkBranch (c : CssData ι κX κZ) (d : ℕ) (s : Partial ι) : Branch ι κX κZ → Bool
  | .split i child =>
      decide (∀ p : Entry, checkBranch c d (Function.update s i (some p)) (child p) = true)
  | .heavy => decide (d ≤ pauliWeight (fill s).1 (fill s).2)
  | .closeX r =>
      decide ((∀ i, c.hX r i ≠ 0 → (s i).isSome = true) ∧ (c.hX *ᵥ (fill s).2) r ≠ 0)
  | .closeZ r =>
      decide ((∀ i, c.hZ r i ≠ 0 → (s i).isSome = true) ∧ (c.hZ *ᵥ (fill s).1) r ≠ 0)
  | .point =>
      decide (∀ i, (s i).isSome = true) && checkPoint c d (fill s)

omit [DecidableEq ι] in
/-- Filling unspecified coordinates with zero cannot increase the weight of an extension. -/
private theorem fill_weight {s : Partial ι} {e : PauliLabel ι} (hf : Fits s e) :
    pauliWeight (fill s).1 (fill s).2 ≤ pauliWeight e.1 e.2 := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  cases h : s i with
  | none => simp [fill, h] at hi
  | some p =>
    have hh := fill_eq hf i (by simp [h])
    have hx : (fill s).1 i = e.1 i := congrArg Prod.fst hh
    have hz : (fill s).2 i = e.2 i := congrArg Prod.snd hh
    simpa only [hx, hz] using hi

omit [DecidableEq ι] in
/-- A check row supported on decided coordinates is constant throughout the branch. -/
private theorem row_agrees {κ : Type*} (A : Matrix κ ι (ZMod 2)) (r : κ)
    (side : Entry → ZMod 2) {s : Partial ι} {e : PauliLabel ι} (hf : Fits s e)
    (hcover : ∀ i, A r i ≠ 0 → (s i).isSome = true) :
    (A *ᵥ fun i => side ((fill s).1 i, (fill s).2 i)) r =
      (A *ᵥ fun i => side (e.1 i, e.2 i)) r := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : A r i = 0
  · simp [h]
  · rw [fill_eq hf i (hcover i h)]

/-- Every low-weight undetectable label extending an accepted branch is a stabilizer. -/
theorem branch_sound (c : CssData ι κX κZ) (d : ℕ) (tr : Branch ι κX κZ)
    (s : Partial ι) (hcheck : checkBranch c d s tr = true) (e : PauliLabel ι)
    (hf : Fits s e) (hs : pauliSyndrome c e = (0, 0))
    (hw : pauliWeight e.1 e.2 < d) : IsStabilizerLabel c e := by
  induction tr generalizing s with
  | split i child ih =>
    have hall : ∀ p : Entry,
        checkBranch c d (Function.update s i (some p)) (child p) = true :=
      of_decide_eq_true hcheck
    exact ih (e.1 i, e.2 i) _ (hall _) (fits_update hf i)
  | heavy =>
    have hd : d ≤ pauliWeight (fill s).1 (fill s).2 := of_decide_eq_true hcheck
    exact (not_lt_of_ge (hd.trans (fill_weight hf)) hw).elim
  | closeX r =>
    have h : (∀ i, c.hX r i ≠ 0 → (s i).isSome = true) ∧
        (c.hX *ᵥ (fill s).2) r ≠ 0 := of_decide_eq_true hcheck
    exact (h.2 ((row_agrees c.hX r Prod.snd hf h.1).trans
      (congrFun (congrArg Prod.fst hs) r))).elim
  | closeZ r =>
    have h : (∀ i, c.hZ r i ≠ 0 → (s i).isSome = true) ∧
        (c.hZ *ᵥ (fill s).1) r ≠ 0 := of_decide_eq_true hcheck
    exact (h.2 ((row_agrees c.hZ r Prod.fst hf h.1).trans
      (congrFun (congrArg Prod.snd hs) r))).elim
  | point =>
    have h : decide (∀ i, (s i).isSome = true) = true ∧ checkPoint c d (fill s) = true :=
      Bool.and_eq_true_iff.mp hcheck
    have hcover : ∀ i, (s i).isSome = true := of_decide_eq_true h.1
    have he : fill s = e :=
      Prod.ext (funext fun i => congrArg Prod.fst (fill_eq hf i (hcover i)))
        (funext fun i => congrArg Prod.snd (fill_eq hf i (hcover i)))
    have hpoint := h.2
    rw [he, checkPoint] at hpoint
    rcases Bool.or_eq_true_iff.mp hpoint with ha | hb
    · rcases of_decide_eq_true ha with hd | hdetect
      · exact (not_lt_of_ge hd hw).elim
      · exact (hdetect hs).elim
    · exact (checkStab_iff c e).mp hb

/-- An accepted tree at the empty assignment certifies the public CSS lower bound. -/
theorem branch_lower (c : CssData ι κX κZ) (d : ℕ) (tr : Branch ι κX κZ)
    (h : checkBranch c d (fun _ => none) tr = true) : (d : ℕ∞) ≤ cssDistance c := by
  apply (distance_ge_iff c d).mpr
  intro e hs hw
  exact branch_sound c d tr _ h e (by simp [Fits]) hs (by exact_mod_cast hw)

/-- Accept an upper logical witness and a lower exclusion tree for one common distance. -/
def checkDistance (c : CssData ι κX κZ) (d : ℕ) (e : PauliLabel ι) (tr : Branch ι κX κZ) :
    Bool :=
  (decide (pauliSyndrome c e = (0, 0) ∧ pauliWeight e.1 e.2 = d) &&
    !checkStab c e) && checkBranch c d (fun _ => none) tr

/-- Acceptance proves the exact CSS distance for the original check matrices. -/
theorem distance_sound (c : CssData ι κX κZ) (d : ℕ) (e : PauliLabel ι)
    (tr : Branch ι κX κZ) (h : checkDistance c d e tr = true) : cssDistance c = d := by
  have hs := Bool.and_eq_true_iff.mp h
  have hu := Bool.and_eq_true_iff.mp hs.1
  have he : pauliSyndrome c e = (0, 0) ∧ pauliWeight e.1 e.2 = d := of_decide_eq_true hu.1
  have hn : ¬ IsStabilizerLabel c e := by
    intro he
    have ht := (checkStab_iff c e).mpr he
    simp [ht] at hu
  apply le_antisymm _ (branch_lower c d tr hs.2)
  simpa only [he.2] using distance_le c e he.1 hn

end Qatlib.Concepts.CodeCert.DistCert
