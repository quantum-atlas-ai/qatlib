/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprMachineExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Order Bound Code

Coded Floor constructions for Effective Gauge.
Defines `floorExprOrderBoundCode`, `floorExprOrderMachineStep`, `floorExprOrderMachine`.
Proves `primrec_floorExprOrderMachine`, `floorExprOrderMachine_correct`, `floorExprOrderBoundCompiler`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Expr Order Bound Code in the Coded Floor construction. -/
def floorExprOrderBoundCode (order code : ℕ) : ℕ := floorJetOrderBound order (floorExprDecode code)

/-- Definition of floor Expr Order Machine Step in the Coded Floor construction. -/
def floorExprOrderMachineStep (merge d0 d1 d2 previous : Nat.Partrec.Code) : Nat.Partrec.Code :=
  .comp merge (.pair (.comp previous d0) (.pair (.comp previous d1) (.comp previous d2)))

/-- Definition of floor Expr Order Machine in the Coded Floor construction. -/
def floorExprOrderMachine (base merge d0 d1 d2 : Nat.Partrec.Code) (order : ℕ) : Nat.Partrec.Code :=
  (floorExprOrderMachineStep merge d0 d1 d2)^[order] base

/-- Original `primrec_floorExprOrderMachine` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem primrec_floorExprOrderMachine (base merge d0 d1 d2 : Nat.Partrec.Code) :
    Primrec (floorExprOrderMachine base merge d0 d1 d2) := by
  have hs : Primrec (floorExprOrderMachineStep merge d0 d1 d2) :=
    Nat.Partrec.Code.primrec₂_comp.comp (Primrec.const merge)
      (Nat.Partrec.Code.primrec₂_pair.comp
        (Nat.Partrec.Code.primrec₂_comp.comp Primrec.id (Primrec.const d0))
        (Nat.Partrec.Code.primrec₂_pair.comp
          (Nat.Partrec.Code.primrec₂_comp.comp Primrec.id (Primrec.const d1))
          (Nat.Partrec.Code.primrec₂_comp.comp Primrec.id (Primrec.const d2))))
  exact Primrec.nat_iterate Primrec.id (Primrec.const base) (hs.comp Primrec.snd)

/-- Original `floorExprOrderMachine_correct` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem floorExprOrderMachine_correct (base merge d0 d1 d2 : Nat.Partrec.Code)
    (hbase : floorCodeRealizes base floorExprCodeBound)
    (hmerge : floorCodeRealizes merge (fun p : ℕ × ℕ × ℕ => p.1+p.2.1+p.2.2))
    (h0 : floorCodeRealizes d0 (floorExprDiffCode 0))
    (h1 : floorCodeRealizes d1 (floorExprDiffCode 1))
    (h2 : floorCodeRealizes d2 (floorExprDiffCode 2)) (order : ℕ) :
    floorCodeRealizes (floorExprOrderMachine base merge d0 d1 d2 order) (floorExprOrderBoundCode order) := by
  induction order with
  | zero => exact hbase
  | succ order ih =>
    have h := floorCodeRealizes_comp hmerge
      (floorCodeRealizes_pair (floorCodeRealizes_comp ih h0)
        (floorCodeRealizes_pair (floorCodeRealizes_comp ih h1) (floorCodeRealizes_comp ih h2)))
    intro code
    simpa [floorExprOrderMachine,Function.iterate_succ_apply',floorExprOrderMachineStep,
      floorExprOrderBoundCode,floorJetOrderBound,Fin.sum_univ_three,floorExprDecode_diffCode,floorExprAxis]
      using h code

/-- Original `floorExprOrderBoundCompiler` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem floorExprOrderBoundCompiler : ∃ generate : ℕ → Nat.Partrec.Code,
    Computable generate ∧ ∀ n, floorCodeRealizes (generate n) (floorExprOrderBoundCode n) := by
  obtain ⟨base,hbase⟩ := floorCodeRealizes_exists floorExprCodeBound computable_floorExprCodeBound
  obtain ⟨merge,hmerge⟩ := floorCodeRealizes_exists (fun p : ℕ × ℕ × ℕ => p.1+p.2.1+p.2.2)
    ((Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to_comp)
  obtain ⟨d0,h0⟩ := floorCodeRealizes_exists (floorExprDiffCode 0)
    (computable_floorExprDiffCode.comp (Computable.const 0) Computable.id)
  obtain ⟨d1,h1⟩ := floorCodeRealizes_exists (floorExprDiffCode 1)
    (computable_floorExprDiffCode.comp (Computable.const 1) Computable.id)
  obtain ⟨d2,h2⟩ := floorCodeRealizes_exists (floorExprDiffCode 2)
    (computable_floorExprDiffCode.comp (Computable.const 2) Computable.id)
  exact ⟨floorExprOrderMachine base merge d0 d1 d2,
    (primrec_floorExprOrderMachine base merge d0 d1 d2).to_comp,
    floorExprOrderMachine_correct base merge d0 d1 d2 hbase hmerge h0 h1 h2⟩

/-- Original `computable_floorExprOrderBoundCode` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprOrderBoundCode : Computable₂ floorExprOrderBoundCode := by
  obtain ⟨generate,hgenerate,hcorrect⟩ := floorExprOrderBoundCompiler
  exact floorUniformCodeRealizes_computable generate hgenerate floorExprOrderBoundCode hcorrect

/-- Definition of floor Source Bound Raw Code in the Coded Floor construction. -/
def floorSourceBoundRawCode (order : ℕ) : FloorRationalCode :=
  floorRationalCodeNat (floorExprOrderBoundCode order (floorExprEncode (floorSpinExpr 0))+
    floorExprOrderBoundCode order (floorExprEncode (floorSpinExpr 1))+
    floorExprOrderBoundCode order (floorExprEncode (floorSpinExpr 2)))

/-- Original `floorSourceBoundRawCode_value` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem floorSourceBoundRawCode_value (order : ℕ) :
    floorRationalCodeValue (floorSourceBoundRawCode order)=floorSourceJetBound order := by
  simp [floorSourceBoundRawCode,floorRationalCodeNat_value,floorExprOrderBoundCode,
    floorExprDecode_encode,floorSourceJetBound,Fin.sum_univ_three]

/-- Original `computable_floorSourceBoundRawCode` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem computable_floorSourceBoundRawCode : Computable floorSourceBoundRawCode :=
  primrec_floorRationalCodeNat.to_comp.comp (Primrec.nat_add.to_comp.comp
    (Primrec.nat_add.to_comp.comp
      (computable_floorExprOrderBoundCode.comp Computable.id (Computable.const (floorExprEncode (floorSpinExpr 0))))
      (computable_floorExprOrderBoundCode.comp Computable.id (Computable.const (floorExprEncode (floorSpinExpr 1)))))
    (computable_floorExprOrderBoundCode.comp Computable.id (Computable.const (floorExprEncode (floorSpinExpr 2)))))

/-- Original `floorSourceBoundRawCode_encoded` guarantee for the `FloorExprOrderBoundCode` construction; the complete source hypotheses are retained. -/
theorem floorSourceBoundRawCode_encoded : ∃ machine : Nat.Partrec.Code, ∀ order,
    Nat.Partrec.Code.eval machine (Encodable.encode order)=
      Part.some (Encodable.encode (floorSourceBoundRawCode order)) :=
  floorComputableFixedCode floorSourceBoundRawCode computable_floorSourceBoundRawCode

end Qatlib.Concepts.EffectiveGauge.CodedFloor
