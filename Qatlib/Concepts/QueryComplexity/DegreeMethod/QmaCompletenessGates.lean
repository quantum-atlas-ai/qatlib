/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.QmaCompletenessNumerics
import Mathlib.Data.List.FinRange
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

abbrev Tag := Atom × Atom
def zeroTag : Tag := (.zero, .zero)
def oneTag : Tag := (.one, .zero)

def regEq {n : ℕ} (x y : Reg n) : Bool :=
  (List.finRange n).all (fun j => decide (x j = y j))

def outsideEq {n : ℕ} (w : Fin n) (x y : Reg n) : Bool :=
  (List.finRange n).all (fun j => decide (j = w ∨ x j = y j))

def identityTag {n : ℕ} (x y : Reg n) : Tag :=
  if regEq x y then oneTag else zeroTag

def hCell (a c : Bool) : Tag :=
  (if a && c then .negRoot else .root, .zero)

def xCell (a c : Bool) : Tag :=
  if a = !c then oneTag else zeroTag

def tCell (a c : Bool) : Tag :=
  if a = c then (if a then (.root, .root) else oneTag) else zeroTag

def tdgCell (a c : Bool) : Tag :=
  if a = c then (if a then (.root, .negRoot) else oneTag) else zeroTag

def oneWireTag (n w : ℕ) (cell : Bool → Bool → Tag) (x y : Reg n) : Tag :=
  if hw : w < n then
    if outsideEq ⟨w, hw⟩ x y then cell (x ⟨w, hw⟩) (y ⟨w, hw⟩)
    else zeroTag
  else identityTag x y

def rawTag (n : ℕ) (g : FiniteGateCode) (x y : Reg n) : Tag :=
  match g with
  | .h w => oneWireTag n w hCell x y
  | .x w => oneWireTag n w xCell x y
  | .t w => oneWireTag n w tCell x y
  | .tdg w => oneWireTag n w tdgCell x y
  | .cx c t =>
      if h : c < n ∧ t < n ∧ c ≠ t then
        if regEq x (Function.update y ⟨t, h.2.1⟩
          (y ⟨t, h.2.1⟩ ^^ y ⟨c, h.1⟩)) then oneTag else zeroTag
      else identityTag x y

def rawCoeff (n b : ℕ) (g : FiniteGateCode) (x y : Reg n) : ℤ × ℤ :=
  let p := rawTag n g x y
  (atomNumerator b p.1, atomNumerator b p.2)

theorem regEq_true_iff {n : ℕ} (x y : Reg n) : regEq x y = true ↔ x = y := by
  constructor
  · intro h
    funext j
    exact of_decide_eq_true ((List.all_eq_true.mp h) j (by simp))
  · intro h
    apply List.all_eq_true.mpr
    intro j _
    simpa only [decide_eq_true_eq] using congrFun h j

theorem outsideEq_true_iff {n : ℕ} (w : Fin n) (x y : Reg n) :
    outsideEq w x y = true ↔ ∀ j : Fin n, j ≠ w → x j = y j := by
  constructor
  · intro h j hj
    have he : j = w ∨ x j = y j :=
      of_decide_eq_true ((List.all_eq_true.mp h) j (by simp))
    exact he.resolve_left hj
  · intro h
    apply List.all_eq_true.mpr
    intro j _
    by_cases hj : j = w
    · simp [hj]
    · simp [hj, h j hj]

theorem rawCoeff_bounds (n b : ℕ) (g : FiniteGateCode) (x y : Reg n) :
    -((2 : ℤ)^b) ≤ (rawCoeff n b g x y).1 ∧
    (rawCoeff n b g x y).1 ≤ (2 : ℤ)^b ∧
    -((2 : ℤ)^b) ≤ (rawCoeff n b g x y).2 ∧
    (rawCoeff n b g x y).2 ≤ (2 : ℤ)^b := by
  exact ⟨(atomNumerator_bounds b (rawTag n g x y).1).1,
    (atomNumerator_bounds b (rawTag n g x y).1).2,
    (atomNumerator_bounds b (rawTag n g x y).2).1,
    (atomNumerator_bounds b (rawTag n g x y).2).2⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
