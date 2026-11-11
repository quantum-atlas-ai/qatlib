/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprOrderBoundCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorProgramSource

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Program Source Code

Coded Floor constructions for Effective Gauge.
Defines `FloorSourceQueryCode`, `floorSpinExprCode`, `floorSourcePrecisionCode`.
Proves `floorSpinExprCode_decode_fin`, `floorSpinExprCode_decode`, `floorSourcePrecisionCode_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Abbreviation for Floor Source Query Code in the Coded Floor construction. -/
abbrev FloorSourceQueryCode := FloorPointCode × (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- Definition of floor Spin Expr Code in the Coded Floor construction. -/
def floorSpinExprCode (axis : ℕ) : ℕ :=
  [floorExprEncode (floorSpinExpr 0),floorExprEncode (floorSpinExpr 1),
    floorExprEncode (floorSpinExpr 2)].getD (axis%3) (floorExprEncode (floorSpinExpr 0))

/-- Definition of floor Source Precision Code in the Coded Floor construction. -/
def floorSourcePrecisionCode (b : ℕ) : FloorRationalCode :=
  floorRationalCodeInv (floorRationalCodePow (floorRationalCodeNat 2) b)

/-- Definition of floor Source Query Multi Index in the Coded Floor construction. -/
def floorSourceQueryMultiIndex (q : FloorSourceQueryCode) (i : Fin 3) : ℕ :=
  if i=0 then q.2.1.1 else if i=1 then q.2.1.2.1 else q.2.1.2.2

/-- Definition of floor Encoded Jet Source in the Coded Floor construction. -/
def floorEncodedJetSource (c : Nat.Partrec.Code) (q : FloorSourceQueryCode) : FloorRationalCode :=
  floorExprRawApprox (floorExprJetCode (floorSpinExprCode q.2.2.2) q.2.1)
    (c,q.1,floorSourcePrecisionCode q.2.2.1)

/-- Original `floorSpinExprCode_decode_fin` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem floorSpinExprCode_decode_fin (i : Fin 3) :
    floorExprDecode (floorSpinExprCode i.val)=floorSpinExpr i := by
  fin_cases i <;> simp [floorSpinExprCode,floorExprDecode_encode]

/-- Original `floorSpinExprCode_decode` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem floorSpinExprCode_decode (axis : ℕ) :
    floorExprDecode (floorSpinExprCode axis)=floorSpinExpr (floorExprAxis axis) := by
  have h := floorSpinExprCode_decode_fin (floorExprAxis axis)
  simpa [floorSpinExprCode,floorExprAxis] using h

/-- Original `floorSourcePrecisionCode_value` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem floorSourcePrecisionCode_value (b : ℕ) :
    floorRationalCodeValue (floorSourcePrecisionCode b)=(2^b : ℚ)⁻¹ := by
  simp [floorSourcePrecisionCode,floorRationalCodeInv_value,floorRationalCodePow_value,floorRationalCodeNat_value]

/-- Original `floorEncodedJetSource_value` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem floorEncodedJetSource_value (c : Nat.Partrec.Code) (q : FloorSourceQueryCode) :
    floorRationalCodeValue (floorEncodedJetSource c q)=
      floorProgramJetSource c ((floorPointCodeValue q.1,floorSourceQueryMultiIndex q),q.2.2.1)
        (floorExprAxis q.2.2.2) := by
  have hmulti : (floorSourceQueryMultiIndex q 0,floorSourceQueryMultiIndex q 1,
      floorSourceQueryMultiIndex q 2)=q.2.1 := by simp [floorSourceQueryMultiIndex]
  rw [floorEncodedJetSource,floorExprRawApprox_value]
  dsimp only
  rw [← hmulti,floorExprDecode_jetCode,floorSpinExprCode_decode,floorSourcePrecisionCode_value]
  rfl

/-- Original `primrec_floorSpinExprCode` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorSpinExprCode : Primrec floorSpinExprCode :=
  (Primrec.list_getD (floorExprEncode (floorSpinExpr 0))).comp
    (Primrec.const [floorExprEncode (floorSpinExpr 0),floorExprEncode (floorSpinExpr 1),floorExprEncode (floorSpinExpr 2)])
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 3))

/-- Original `primrec_floorSourcePrecisionCode` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorSourcePrecisionCode : Primrec floorSourcePrecisionCode :=
  primrec_floorRationalCodeInv.comp
    (primrec_floorRationalCodePow.comp (Primrec.const (floorRationalCodeNat 2)) Primrec.id)

/-- Original `computable_floorEncodedJetSource` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem computable_floorEncodedJetSource : Computable₂ floorEncodedJetSource := by
  have hq : Computable (fun p : Nat.Partrec.Code × FloorSourceQueryCode => p.2) := Computable.snd
  have hx := Computable.fst.comp hq
  have ha := Computable.fst.comp (Computable.snd.comp hq)
  have hb := Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hq))
  have hj := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hq))
  have he := computable_floorExprJetCode.comp (primrec_floorSpinExprCode.to_comp.comp hj) ha
  have ht := primrec_floorSourcePrecisionCode.to_comp.comp hb
  exact computable_floorExprRawApprox.comp he (Computable.fst.pair (hx.pair ht))

/-- Original `floorEncodedJetSource_generator` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem floorEncodedJetSource_generator : ∃ generate : Nat.Partrec.Code → Nat.Partrec.Code,
    Computable generate ∧ ∀ c q,
      Nat.Partrec.Code.eval (generate c) (Encodable.encode q)=
        Part.some (Encodable.encode (floorEncodedJetSource c q)) := by
  obtain ⟨generate,hgenerate,hcorrect⟩ := floorPartrecCodeFamily
    (fun c q => Part.some (floorEncodedJetSource c q)) computable_floorEncodedJetSource.partrec₂
  exact ⟨generate,hgenerate,fun c q => by simpa using hcorrect c q⟩

/-- Original `floorEncodedJetSource_error` guarantee for the `FloorProgramSourceCode` construction; the complete source hypotheses are retained. -/
theorem floorEncodedJetSource_error (c : Nat.Partrec.Code) (q : FloorSourceQueryCode)
    (hX : InFundamentalCube (rationalSpatialPoint (floorPointCodeValue q.1))) :
    |(floorRationalCodeValue (floorEncodedJetSource c q) : ℝ)-
      sourceCanonicalJet (floorPeriodicSpin (floorProgramAmplitude c : ℝ))
        (floorSourceQueryMultiIndex q) (rationalSpatialPoint (floorPointCodeValue q.1))
        (floorExprAxis q.2.2.2)| ≤ (2^q.2.2.1 : ℝ)⁻¹ := by
  rw [floorEncodedJetSource_value]
  exact floorProgramJetSource_accurate c (floorPointCodeValue q.1) (floorSourceQueryMultiIndex q)
    q.2.2.1 hX (floorExprAxis q.2.2.2)

/-- Both programs exist as finite machine codes: one computably generated jet
program for every halting-problem parameter, and one common all-order bound program. -/
theorem floorProgramSourceCode_programs :
    ∃ generate : Nat.Partrec.Code → Nat.Partrec.Code, Computable generate ∧
    ∃ boundMachine : Nat.Partrec.Code,
      (∀ c q, Nat.Partrec.Code.eval (generate c) (Encodable.encode q)=
        Part.some (Encodable.encode (floorEncodedJetSource c q))) ∧
      (∀ order, Nat.Partrec.Code.eval boundMachine (Encodable.encode order)=
        Part.some (Encodable.encode (floorSourceBoundRawCode order))) := by
  obtain ⟨generate,hgenerate,hjets⟩ := floorEncodedJetSource_generator
  obtain ⟨boundMachine,hbounds⟩ := floorSourceBoundRawCode_encoded
  exact ⟨generate,hgenerate,boundMachine,hjets,hbounds⟩

end Qatlib.Concepts.EffectiveGauge.CodedFloor
