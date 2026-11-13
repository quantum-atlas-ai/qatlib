/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.FiniteCurve

/-!
# Checked elliptic curve execution on bit registers

This module relates reversible execution on `BitRegisters` to checked point addition on a short
Weierstrass curve. `pointBitStep_safe` proves correctness outside the exceptional inputs, and
`bitRun_checked` lifts successful checked words to bit execution. The addition schedules are
motivated by [RoettelerEtAl2017].

## Main statements

* `bitWordPermutation_apply`: the word permutation agrees with sequential execution.
* `bitRun_checked`: successful checked point execution gives the encoded output.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

open WeierstrassCurve.Affine
open Qatlib.Concepts.FiniteCounts.OffsetWord

variable {K : Type*} [Field K] [DecidableEq K] {w : ℕ} {a b : K}

/-- Encode an affine point into its two coordinate registers with zero auxiliary registers, and
encode the point at infinity by four zero registers. -/
def pointBits (E : FieldEncoding K w) : (shortCurve a b).Point → BitRegisters w
  | .zero => ⟨0,0,0,0⟩
  | .some x y _ => ⟨E.encode x,E.encode y,0,0⟩

/-- The reversible register permutation for one controlled point addition instruction, acting as
the identity for a false control or the zero point. -/
noncomputable def pointBitStep (E : FieldEncoding K w)
    (s : Instruction (shortCurve a b).Point) : Equiv.Perm (BitRegisters w) :=
  if s.1 then match s.2 with
    | .zero => Equiv.refl _
    | .some x y _ => sourcePermutation E x y
  else Equiv.refl _

/-- Avoiding `badInputs` for two affine points implies distinct X coordinates and excludes the
negative double of the added point. -/
theorem safe_affine_domain {x1 y1 x2 y2 : K}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2)
    (h : Point.some x1 y1 h1 ∉ badInputs (Point.some x2 y2 h2)) :
    x1 ≠ x2 ∧
      Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2) := by
  have hh : Point.some x1 y1 h1 ≠ Point.some x2 y2 h2 ∧
      Point.some x1 y1 h1 ≠ -Point.some x2 y2 h2 ∧
      Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2) := by
    simpa [badInputs, Point.some_ne_zero] using h
  exact ⟨fun hx => (Point.X_eq_iff.mp hx).elim hh.1 hh.2.1, hh.2.2⟩

/-- Outside the exceptional input set, the enabled bit step maps the encoding of `P` to the
encoding of `P + B`. -/
theorem pointBitStep_safe (E : FieldEncoding K w) (P B : (shortCurve a b).Point)
    (h : P ∉ badInputs B) :
    pointBitStep E (true,B) (pointBits E P) = pointBits E (P+B) := by
  cases B with
  | zero =>
    change pointBits E P = pointBits E (P + 0)
    rw [add_zero]
  | some x2 y2 h2 =>
    cases P with
    | zero => simp [badInputs, Point.zero_def] at h
    | some x1 y1 h1 =>
      obtain ⟨hx, hm⟩ := safe_affine_domain h1 h2 h
      obtain ⟨x3,y3,h3,he,hbit⟩ := sourcePermutation_native E h1 h2 hx hm
      rw [he]
      exact hbit

/-- Execute a list of controlled point addition instructions on bit registers. -/
noncomputable def bitRun (E : FieldEncoding K w) (r : BitRegisters w) :
    List (Instruction (shortCurve a b).Point) → BitRegisters w
  | [] => r
  | s :: ss => bitRun E (pointBitStep E s r) ss

/-- Compose the reversible bit steps of an instruction list in execution order. -/
noncomputable def bitWordPermutation (E : FieldEncoding K w) :
    List (Instruction (shortCurve a b).Point) → Equiv.Perm (BitRegisters w)
  | [] => Equiv.refl _
  | s :: ss => (pointBitStep E s).trans (bitWordPermutation E ss)

omit [DecidableEq K] in

/-- Applying the composed word permutation agrees with the recursive bit execution. -/
theorem bitWordPermutation_apply (E : FieldEncoding K w)
    (ss : List (Instruction (shortCurve a b).Point)) (r : BitRegisters w) :
    bitWordPermutation E ss r = bitRun E r ss := by
  induction ss generalizing r with
  | nil => rfl
  | cons s ss ih => exact ih _

/-- A successful checked point execution is reproduced by bit execution on the encoded initial
point. -/
theorem bitRun_checked (E : FieldEncoding K w)
    (ss : List (Instruction (shortCurve a b).Point)) (P Q : (shortCurve a b).Point)
    (h : checkedRun P ss = some Q) :
    bitRun E (pointBits E P) ss = pointBits E Q := by
  induction ss generalizing P with
  | nil =>
    simp only [checkedRun, Option.some.injEq] at h
    simpa only [bitRun] using congrArg (pointBits E) h
  | cons s ss ih =>
    obtain ⟨c,B⟩ := s
    cases c
    · simpa only [bitRun, pointBitStep, Bool.false_eq_true, ↓reduceIte,
        Equiv.refl_apply] using ih P (by simpa only [checkedRun, Bool.false_eq_true,
          ↓reduceIte] using h)
    · by_cases hb : P ∈ badInputs B
      · simp [checkedRun, hb] at h
      · simp only [bitRun, pointBitStep_safe E P B hb]
        exact ih (P+B) (by simpa [checkedRun, hb] using h)

end Qatlib.Concepts.CurveGroups.AffineAdd
