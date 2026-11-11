/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCutoffRowCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorFlatApproximation

/-!
# Floor Flat Polynomial Code

Coded Floor constructions for Effective Gauge.
Defines `floorFlatPolynomialCodeLoop`, `floorFlatPolynomialCode`.
Proves `floorFlatPolynomialCodeLoop_value`, `floorFlatPolynomialCode_value`, `primrec_floorFlatPolynomialCodeLoop`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Flat Polynomial Code Loop in the Coded Floor construction. -/
def floorFlatPolynomialCodeLoop (p : List FloorRationalCode × FloorRationalCode) : ℕ → FloorRationalCode
  | 0 => floorRationalCodeNat 0
  | m+1 => floorRationalCodeAdd (floorFlatPolynomialCodeLoop p m)
    (floorRationalCodeMul (floorCutoffCodeAt p.1 m) (floorRationalCodePow p.2 m))

/-- Definition of floor Flat Polynomial Code in the Coded Floor construction. -/
def floorFlatPolynomialCode (n : ℕ) (x : FloorRationalCode) : FloorRationalCode :=
  floorFlatPolynomialCodeLoop (floorCutoffCodeRow n,x) (2*n+1)

/-- Original `floorFlatPolynomialCodeLoop_value` guarantee for the `FloorFlatPolynomialCode` construction; the complete source hypotheses are retained. -/
theorem floorFlatPolynomialCodeLoop_value (p : List FloorRationalCode × FloorRationalCode) (m : ℕ) :
    floorRationalCodeValue (floorFlatPolynomialCodeLoop p m)=
      ∑ k ∈ Finset.range m, floorRationalCodeValue (floorCutoffCodeAt p.1 k)*(floorRationalCodeValue p.2)^k := by
  induction m with
  | zero => simp [floorFlatPolynomialCodeLoop,floorRationalCodeNat_value]
  | succ m ih =>
    rw [floorFlatPolynomialCodeLoop,floorRationalCodeAdd_value,floorRationalCodeMul_value,
      floorRationalCodePow_value,ih,Finset.sum_range_succ]

/-- Original `floorFlatPolynomialCode_value` guarantee for the `FloorFlatPolynomialCode` construction; the complete source hypotheses are retained. -/
theorem floorFlatPolynomialCode_value (n : ℕ) (x : FloorRationalCode) :
    floorRationalCodeValue (floorFlatPolynomialCode n x)=floorFlatPolynomialValue n (floorRationalCodeValue x) := by
  simp only [floorFlatPolynomialCode,floorFlatPolynomialCodeLoop_value,
    floorCutoffCodeAt_value,floorFlatPolynomialValue]

/-- Original `primrec_floorFlatPolynomialCodeLoop` guarantee for the `FloorFlatPolynomialCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorFlatPolynomialCodeLoop : Primrec₂ floorFlatPolynomialCodeLoop := by
  have hr : Primrec (fun p : (List FloorRationalCode × FloorRationalCode) × (ℕ × FloorRationalCode) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun p : (List FloorRationalCode × FloorRationalCode) × (ℕ × FloorRationalCode) => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hm : Primrec (fun p : (List FloorRationalCode × FloorRationalCode) × (ℕ × FloorRationalCode) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : (List FloorRationalCode × FloorRationalCode) × (ℕ × FloorRationalCode) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hs : Primrec₂ (fun (p : List FloorRationalCode × FloorRationalCode) (s : ℕ × FloorRationalCode) =>
      floorRationalCodeAdd s.2 (floorRationalCodeMul (floorCutoffCodeAt p.1 s.1) (floorRationalCodePow p.2 s.1))) :=
    primrec_floorRationalCodeAdd.comp ha (primrec_floorRationalCodeMul.comp
      (primrec_floorCutoffCodeAt.comp hr hm) (primrec_floorRationalCodePow.comp hx hm))
  apply (Primrec.nat_rec (Primrec.const (floorRationalCodeNat 0)) hs).of_eq
  intro p m
  induction m with
  | zero => rfl
  | succ m ih =>
    simpa only [Nat.rec_add_one,floorFlatPolynomialCodeLoop] using
      congrArg (fun a => floorRationalCodeAdd a
        (floorRationalCodeMul (floorCutoffCodeAt p.1 m) (floorRationalCodePow p.2 m))) ih

/-- Original `primrec_floorFlatPolynomialCode` guarantee for the `FloorFlatPolynomialCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorFlatPolynomialCode : Primrec₂ floorFlatPolynomialCode :=
  primrec_floorFlatPolynomialCodeLoop.comp
    ((primrec_floorCutoffCodeRow.comp Primrec.fst).pair Primrec.snd)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.const 1))

end Qatlib.Concepts.EffectiveGauge.CodedFloor
