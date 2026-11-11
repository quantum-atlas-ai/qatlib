/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorFlatPolynomialCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorFullNegativeExpCode

/-!
# Floor Flat Approx Code

Coded Floor constructions for Effective Gauge.
Defines `FloorFlatCodeInput`, `floorFlatApproxCode`.
Proves `floorFlatApproxCode_value`, `primrec_floorFlatApproxCode`, `floorFlatMachine_of_primrec`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Floor Flat Code Input in the Coded Floor construction. -/
abbrev FloorFlatCodeInput := ℕ × (FloorRationalCode × FloorRationalCode)

/-- Definition of floor Flat Approx Code in the Coded Floor construction. -/
def floorFlatApproxCode (n : ℕ) (p t : FloorRationalCode) : FloorRationalCode :=
  if floorRationalCodeLE p (floorRationalCodeNat 0) then floorRationalCodeNat 0 else
    let c := floorFlatPolynomialCode n (floorRationalCodeInv p)
    floorRationalCodeMul c (floorRationalNegativeExpCode
      (floorRationalCodeInv p,floorRationalCodeMul t
        (floorRationalCodeInv (floorRationalCodeAdd (floorRationalCodeAbs c) (floorRationalCodeNat 1))))).1.1

/-- Original `floorFlatApproxCode_value` guarantee for the `FloorFlatApproxCode` construction; the complete source hypotheses are retained. -/
theorem floorFlatApproxCode_value (n : ℕ) (p t : FloorRationalCode) :
    floorRationalCodeValue (floorFlatApproxCode n p t)=
      floorFlatApproximation n (floorRationalCodeValue p) (floorRationalCodeValue t) := by
  have hg : floorRationalCodeLE p (floorRationalCodeNat 0) ↔ floorRationalCodeValue p ≤ 0 := by
    rw [floorRationalCodeLE_value,floorRationalCodeNat_value,Nat.cast_zero]
  unfold floorFlatApproxCode
  by_cases h : floorRationalCodeLE p (floorRationalCodeNat 0)
  · rw [if_pos h,floorRationalCodeNat_value,floorFlatApproximation,if_pos (hg.mp h)]
    rfl
  · rw [if_neg h,floorRationalCodeMul_value,floorFlatApproximation,if_neg (mt hg.mpr h)]
    have he := congrArg RationalScalarResult.value (floorRationalNegativeExpCode_value
      (floorRationalCodeInv p,floorRationalCodeMul t
        (floorRationalCodeInv (floorRationalCodeAdd
          (floorRationalCodeAbs (floorFlatPolynomialCode n (floorRationalCodeInv p))) (floorRationalCodeNat 1)))))
    change floorRationalCodeValue (floorRationalNegativeExpCode _).1.1=_ at he
    rw [he]
    simp only [floorFlatPolynomialCode_value,floorRationalCodeInv_value,floorRationalCodeMul_value,
      floorRationalCodeAdd_value,floorRationalCodeAbs_value,floorRationalCodeNat_value,Nat.cast_one,
      div_eq_mul_inv]

/-- Original `primrec_floorFlatApproxCode` guarantee for the `FloorFlatApproxCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorFlatApproxCode :
    Primrec (fun q : FloorFlatCodeInput => floorFlatApproxCode q.1 q.2.1 q.2.2) := by
  have hn : Primrec (fun q : FloorFlatCodeInput => q.1) := Primrec.fst
  have hp : Primrec (fun q : FloorFlatCodeInput => q.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun q : FloorFlatCodeInput => q.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun q : FloorFlatCodeInput => floorFlatPolynomialCode q.1 (floorRationalCodeInv q.2.1)) :=
    primrec_floorFlatPolynomialCode.comp hn (primrec_floorRationalCodeInv.comp hp)
  have hd : Primrec (fun q : FloorFlatCodeInput =>
      floorRationalCodeAdd (floorRationalCodeAbs (floorFlatPolynomialCode q.1 (floorRationalCodeInv q.2.1)))
        (floorRationalCodeNat 1)) :=
    primrec_floorRationalCodeAdd.comp (primrec_floorRationalCodeAbs.comp hc) (Primrec.const (floorRationalCodeNat 1))
  have hs : Primrec (fun q : FloorFlatCodeInput => floorRationalCodeMul q.2.2
      (floorRationalCodeInv (floorRationalCodeAdd
        (floorRationalCodeAbs (floorFlatPolynomialCode q.1 (floorRationalCodeInv q.2.1))) (floorRationalCodeNat 1)))) :=
    primrec_floorRationalCodeMul.comp ht (primrec_floorRationalCodeInv.comp hd)
  have he := primrec_floorRationalNegativeExpCode.comp ((primrec_floorRationalCodeInv.comp hp).pair hs)
  have hv := (Primrec.fst.comp Primrec.fst).comp he
  have hg : PrimrecPred (fun q : FloorFlatCodeInput => floorRationalCodeLE q.2.1 (floorRationalCodeNat 0)) :=
    primrec_floorRationalCodeLE.comp hp (Primrec.const (floorRationalCodeNat 0))
  apply (Primrec.ite hg (Primrec.const (floorRationalCodeNat 0))
    (primrec_floorRationalCodeMul.comp hc hv)).of_eq
  intro q
  rfl

/-- Original `floorFlatMachine_of_primrec` guarantee for the `FloorFlatApproxCode` construction; the complete source hypotheses are retained. -/
private theorem floorFlatMachine_of_primrec {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Primrec f) : ∃ c : Nat.Partrec.Code, ∀ a,
      Nat.Partrec.Code.eval c (Encodable.encode a)=Part.some (Encodable.encode (f a)) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  exact ⟨c,fun a => by simpa using congrFun hc (Encodable.encode a)⟩

/-- Original `floorFlatApproxCode_encoded` guarantee for the `FloorFlatApproxCode` construction; the complete source hypotheses are retained. -/
theorem floorFlatApproxCode_encoded : ∃ c : Nat.Partrec.Code, ∀ n p t,
    Nat.Partrec.Code.eval c (Encodable.encode (n,(p,t)))=
      Part.some (Encodable.encode (floorFlatApproxCode n p t)) := by
  obtain ⟨c,hc⟩ := floorFlatMachine_of_primrec
    (fun q : FloorFlatCodeInput => floorFlatApproxCode q.1 q.2.1 q.2.2) primrec_floorFlatApproxCode
  exact ⟨c,fun n p t => hc (n,(p,t))⟩

end Qatlib.Concepts.EffectiveGauge.CodedFloor
