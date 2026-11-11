/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorRationalScalarCode
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffPolynomial
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD

/-!
# Floor Cutoff Row Code

Coded Floor constructions for Effective Gauge.
Defines `floorCutoffCodeAt`, `floorCutoffCodeEntry`, `floorCutoffNextCodeRow`.
Proves `floorCutoffCodeRow_length`, `floorCutoffCodeAt_value`, `primrec_floorCutoffCodeAt`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Cutoff Code At in the Coded Floor construction. -/
def floorCutoffCodeAt (row : List FloorRationalCode) (m : ℕ) : FloorRationalCode :=
  row.getD m (floorRationalCodeNat 0)

/-- Definition of floor Cutoff Code Entry in the Coded Floor construction. -/
def floorCutoffCodeEntry (row : List FloorRationalCode) (m : ℕ) : FloorRationalCode :=
  if 2 ≤ m then floorRationalCodeAdd (floorCutoffCodeAt row (m-2))
    (floorRationalCodeNeg (floorRationalCodeMul (floorRationalCodeNat (m-1))
      (floorCutoffCodeAt row (m-1)))) else floorRationalCodeNat 0

/-- Definition of floor Cutoff Next Code Row in the Coded Floor construction. -/
def floorCutoffNextCodeRow (n : ℕ) (row : List FloorRationalCode) : List FloorRationalCode :=
  (List.range (2*(n+1)+1)).map (floorCutoffCodeEntry row)

/-- Definition of floor Cutoff Code Row in the Coded Floor construction. -/
def floorCutoffCodeRow : ℕ → List FloorRationalCode
  | 0 => [floorRationalCodeNat 1]
  | n+1 => floorCutoffNextCodeRow n (floorCutoffCodeRow n)

/-- Original `floorCutoffCodeRow_length` guarantee for the `FloorCutoffRowCode` construction; the complete source hypotheses are retained. -/
theorem floorCutoffCodeRow_length (n : ℕ) : (floorCutoffCodeRow n).length=2*n+1 := by
  cases n <;> simp [floorCutoffCodeRow,floorCutoffNextCodeRow]

/-- Every encoded coefficient, including the zero extension, has the value
of the actual executable integer row used by the analytic cutoff proof. -/
theorem floorCutoffCodeAt_value (n m : ℕ) :
    floorRationalCodeValue (floorCutoffCodeAt (floorCutoffCodeRow n) m)=
      (cutoffCoefficientAt (cutoffCoefficientRow n) m : ℚ) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [floorCutoffCodeAt,floorCutoffCodeRow,floorRationalCodeNat_value,
        cutoffCoefficientAt,cutoffCoefficientRow]
    | succ m => simp [floorCutoffCodeAt,floorCutoffCodeRow,floorRationalCodeNat_value,
        cutoffCoefficientAt]
  | succ n ih =>
    by_cases hm : m<2*(n+1)+1
    · have hlen : m<(floorCutoffCodeRow (n+1)).length := by rw [floorCutoffCodeRow_length]; exact hm
      rw [floorCutoffCodeAt,List.getD_eq_getElem _ _ hlen]
      simp only [floorCutoffCodeRow,floorCutoffNextCodeRow,List.getElem_map,List.getElem_range]
      rw [cutoffCoefficientAt,dif_pos hm]
      simp only [cutoffCoefficientRow,cutoffNextCoefficientRow,Vector.getElem_ofFn]
      by_cases htwo : 2 ≤ m
      · simp only [floorCutoffCodeEntry,if_pos htwo,floorRationalCodeAdd_value,
          floorRationalCodeNeg_value,floorRationalCodeMul_value,floorRationalCodeNat_value,
          ih]
        push_cast
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        simp only [Nat.cast_one,sub_eq_add_neg]
      · simp only [floorCutoffCodeEntry,if_neg htwo,floorRationalCodeNat_value,Nat.cast_zero,Int.cast_zero]
    · rw [floorCutoffCodeAt,List.getD_eq_default _ _ (by rw [floorCutoffCodeRow_length]; omega)]
      rw [floorRationalCodeNat_value,cutoffCoefficientAt,dif_neg hm]
      simp

/-- Original `primrec_floorCutoffCodeAt` guarantee for the `FloorCutoffRowCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCutoffCodeAt : Primrec₂ floorCutoffCodeAt :=
  Primrec.list_getD (floorRationalCodeNat 0)

/-- Original `primrec_floorCutoffCodeEntry` guarantee for the `FloorCutoffRowCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCutoffCodeEntry : Primrec₂ floorCutoffCodeEntry := by
  have h2 : Primrec (fun p : List FloorRationalCode × ℕ => floorCutoffCodeAt p.1 (p.2-2)) :=
    primrec_floorCutoffCodeAt.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 2))
  have h1 : Primrec (fun p : List FloorRationalCode × ℕ => floorCutoffCodeAt p.1 (p.2-1)) :=
    primrec_floorCutoffCodeAt.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
  have hn : Primrec (fun p : List FloorRationalCode × ℕ => floorRationalCodeNat (p.2-1)) :=
    primrec_floorRationalCodeNat.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))
  exact Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) Primrec.snd)
    (primrec_floorRationalCodeAdd.comp h2
      (primrec_floorRationalCodeNeg.comp (primrec_floorRationalCodeMul.comp hn h1)))
    (Primrec.const (floorRationalCodeNat 0))

/-- Original `primrec_floorCutoffNextCodeRow` guarantee for the `FloorCutoffRowCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCutoffNextCodeRow : Primrec₂ floorCutoffNextCodeRow := by
  have hl : Primrec (fun p : ℕ × List FloorRationalCode => 2*(p.1+1)+1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))) (Primrec.const 1)
  have he : Primrec₂ (fun (p : ℕ × List FloorRationalCode) (m : ℕ) => floorCutoffCodeEntry p.2 m) :=
    primrec_floorCutoffCodeEntry.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map (Primrec.list_range.comp hl) he

/-- Original `primrec_floorCutoffCodeRow` guarantee for the `FloorCutoffRowCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorCutoffCodeRow : Primrec floorCutoffCodeRow := by
  apply (Primrec.nat_rec₁ [floorRationalCodeNat 1] primrec_floorCutoffNextCodeRow).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.rec_add_one,floorCutoffCodeRow] using congrArg (floorCutoffNextCodeRow n) ih

end Qatlib.Concepts.EffectiveGauge.CodedFloor
