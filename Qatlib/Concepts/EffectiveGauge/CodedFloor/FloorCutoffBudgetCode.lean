/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCutoffRowCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCodeFamilyCompiler

/-!
# Floor Cutoff Budget Code

Coded Floor constructions for Effective Gauge.
Defines `floorCutoffCodeBudgetLoop`, `floorCutoffCodeBudget`.
Proves `floorCutoffCodeMagnitude_value`, `floorCutoffCodeBudgetLoop_value`, `floorCutoffCodeBudget_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Cutoff Code Budget Loop in the Coded Floor construction. -/
def floorCutoffCodeBudgetLoop (row : List FloorRationalCode) : ℕ → ℕ
  | 0 => 0
  | m+1 => floorCutoffCodeBudgetLoop row m+
    floorRationalCodeCeil (floorRationalCodeAbs (floorCutoffCodeAt row m))*max 1 (m^m)

/-- Definition of floor Cutoff Code Budget in the Coded Floor construction. -/
def floorCutoffCodeBudget (n : ℕ) : ℕ := floorCutoffCodeBudgetLoop (floorCutoffCodeRow n) (2*n+1)

/-- Original `floorCutoffCodeMagnitude_value` guarantee for the `FloorCutoffBudgetCode` construction; the complete source hypotheses are retained. -/
theorem floorCutoffCodeMagnitude_value (n m : ℕ) :
    floorRationalCodeCeil (floorRationalCodeAbs (floorCutoffCodeAt (floorCutoffCodeRow n) m))=
      (cutoffCoefficientAt (cutoffCoefficientRow n) m).natAbs := by
  rw [floorRationalCodeCeil_value,floorRationalCodeAbs_value,floorCutoffCodeAt_value]
  have hz : (((cutoffCoefficientAt (cutoffCoefficientRow n) m).natAbs : ℕ) : ℚ)=
      |(cutoffCoefficientAt (cutoffCoefficientRow n) m : ℚ)| := by
    rw [Nat.cast_natAbs,Int.cast_abs]
  rw [← hz]
  exact Nat.ceil_natCast _

/-- Original `floorCutoffCodeBudgetLoop_value` guarantee for the `FloorCutoffBudgetCode` construction; the complete source hypotheses are retained. -/
theorem floorCutoffCodeBudgetLoop_value (n k : ℕ) :
    floorCutoffCodeBudgetLoop (floorCutoffCodeRow n) k=
      ∑ m ∈ Finset.range k, (cutoffCoefficientAt (cutoffCoefficientRow n) m).natAbs*max 1 (m^m) := by
  induction k with
  | zero => simp [floorCutoffCodeBudgetLoop]
  | succ k ih => rw [floorCutoffCodeBudgetLoop,ih,floorCutoffCodeMagnitude_value,Finset.sum_range_succ]

/-- Original `floorCutoffCodeBudget_value` guarantee for the `FloorCutoffBudgetCode` construction; the complete source hypotheses are retained. -/
theorem floorCutoffCodeBudget_value (n : ℕ) : floorCutoffCodeBudget n=cutoffBumpMajorant n := by
  rw [floorCutoffCodeBudget,floorCutoffCodeBudgetLoop_value]
  rfl

/-- Original `primrec_floorCutoffCodeBudgetLoop` guarantee for the `FloorCutoffBudgetCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCutoffCodeBudgetLoop : Primrec₂ floorCutoffCodeBudgetLoop := by
  have hr : Primrec (fun p : List FloorRationalCode × (ℕ × ℕ) => p.1) := Primrec.fst
  have hm : Primrec (fun p : List FloorRationalCode × (ℕ × ℕ) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : List FloorRationalCode × (ℕ × ℕ) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hmag := primrec_floorRationalCodeCeil.comp
    (primrec_floorRationalCodeAbs.comp (primrec_floorCutoffCodeAt.comp hr hm))
  have hs : Primrec₂ (fun (row : List FloorRationalCode) (s : ℕ × ℕ) =>
      s.2+floorRationalCodeCeil (floorRationalCodeAbs (floorCutoffCodeAt row s.1))*max 1 (s.1^s.1)) :=
    Primrec.nat_add.comp ha (Primrec.nat_mul.comp hmag
      (Primrec.nat_max.comp (Primrec.const 1) (hpow.comp hm hm)))
  apply (Primrec.nat_rec (Primrec.const 0) hs).of_eq
  intro row k
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [Nat.rec_add_one,floorCutoffCodeBudgetLoop] using congrArg (fun a =>
      a+floorRationalCodeCeil (floorRationalCodeAbs (floorCutoffCodeAt row k))*max 1 (k^k)) ih

/-- Original `primrec_floorCutoffCodeBudget` guarantee for the `FloorCutoffBudgetCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCutoffCodeBudget : Primrec floorCutoffCodeBudget :=
  primrec_floorCutoffCodeBudgetLoop.comp primrec_floorCutoffCodeRow
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1))

/-- Original `floorCutoffCodeBudget_encoded` guarantee for the `FloorCutoffBudgetCode` construction; the complete source hypotheses are retained. -/
theorem floorCutoffCodeBudget_encoded : ∃ c : Nat.Partrec.Code, ∀ n,
    Nat.Partrec.Code.eval c (Encodable.encode n)=Part.some (Encodable.encode (floorCutoffCodeBudget n)) :=
  floorComputableFixedCode floorCutoffCodeBudget primrec_floorCutoffCodeBudget.to_comp

end Qatlib.Concepts.EffectiveGauge.CodedFloor
