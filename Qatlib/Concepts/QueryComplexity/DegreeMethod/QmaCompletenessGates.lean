/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.FiniteGateWord.QmaCompletenessNumerics
import Mathlib.Data.List.FinRange

/-!
# Finite gate entries and integer coefficient bounds

This module encodes the real and imaginary parts of finite gate entries as pairs of atomic tags.
The functions `rawTag` and `rawCoeff` describe Hadamard, bit-flip, phase, inverse-phase, and
controlled-NOT gates, with invalid wire choices interpreted as the identity.

The resulting integer numerators have explicit bounds at precision `b`. These finite gate
encodings support the circuit-to-Hamiltonian construction of [KitaevShenVyalyi2002].

## Main statements

* `regEq_true_iff`: The Boolean register comparison detects equality.
* `outsideEq_true_iff`: The one-wire comparison detects agreement away from that wire.
* `rawCoeff_bounds`: Both integer coefficients lie between `-2^b` and `2^b`.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-- A pair of atomic tags encoding the real and imaginary components of a gate entry. -/
abbrev Tag := Atom × Atom
/-- The pair of zero atoms encoding a zero gate entry. -/
def zeroTag : Tag := (.zero, .zero)
/-- The pair consisting of the one atom and the zero atom, encoding a unit gate entry. -/
def oneTag : Tag := (.one, .zero)

/-- Tests equality of two Boolean registers by comparing all coordinates. -/
def regEq {n : ℕ} (x y : Reg n) : Bool :=
  (List.finRange n).all (fun j => decide (x j = y j))

/-- Tests whether two Boolean registers agree at every coordinate other than `w`. -/
def outsideEq {n : ℕ} (w : Fin n) (x y : Reg n) : Bool :=
  (List.finRange n).all (fun j => decide (j = w ∨ x j = y j))

/-- Encodes an identity-matrix entry by `oneTag` on equal registers and `zeroTag` otherwise. -/
def identityTag {n : ℕ} (x y : Reg n) : Tag :=
  if regEq x y then oneTag else zeroTag

/-- The atomic real and imaginary tags for a single-qubit Hadamard entry. -/
def hCell (a c : Bool) : Tag :=
  (if a && c then .negRoot else .root, .zero)

/-- The atomic tags for a single-qubit bit-flip entry. -/
def xCell (a c : Bool) : Tag :=
  if a = !c then oneTag else zeroTag

/-- The atomic tags for a single-qubit T-phase entry. -/
def tCell (a c : Bool) : Tag :=
  if a = c then (if a then (.root, .root) else oneTag) else zeroTag

/-- The atomic tags for a single-qubit inverse T-phase entry. -/
def tdgCell (a c : Bool) : Tag :=
  if a = c then (if a then (.root, .negRoot) else oneTag) else zeroTag

/-- Extends a one-qubit entry rule to a register, requiring agreement off the selected wire and
using the identity when the wire is out of range. -/
def oneWireTag (n w : ℕ) (cell : Bool → Bool → Tag) (x y : Reg n) : Tag :=
  if hw : w < n then
    if outsideEq ⟨w, hw⟩ x y then cell (x ⟨w, hw⟩) (y ⟨w, hw⟩)
    else zeroTag
  else identityTag x y

/-- Computes the atomic entry tags of a finite gate code on an `n`-qubit register, interpreting
invalid wire choices as the identity. -/
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

/-- Converts the real and imaginary atomic entry tags to integer numerators at precision `b`. -/
def rawCoeff (n b : ℕ) (g : FiniteGateCode) (x y : Reg n) : ℤ × ℤ :=
  let p := rawTag n g x y
  (atomNumerator b p.1, atomNumerator b p.2)

/-- The register-equality test is true exactly when the two registers are equal. -/
theorem regEq_true_iff {n : ℕ} (x y : Reg n) : regEq x y = true ↔ x = y := by
  constructor
  · intro h
    funext j
    exact of_decide_eq_true ((List.all_eq_true.mp h) j (by simp))
  · intro h
    apply List.all_eq_true.mpr
    intro j _
    simpa only [decide_eq_true_eq] using congrFun h j

/-- The outside-equality test is true exactly when the registers agree away from the selected
wire. -/
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

/-- Each component of a raw gate coefficient lies between `-2^b` and `2^b`. -/
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
