/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorTypedCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSourceRawCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCisBackendCode

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Machine Basis

Coded Floor constructions for Effective Gauge.
Defines `floorExprSinRawCode`, `floorExprCosRawCode`, `FloorExprMachineBasis`.
Proves `floorExprMachineBasis_exists`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Expr Sin Raw Code in the Coded Floor construction. -/
def floorExprSinRawCode (p : FloorExpCodeParameters) : FloorRationalCode :=
  (floorRationalCisCode p).1.1.2

/-- Definition of floor Expr Cos Raw Code in the Coded Floor construction. -/
def floorExprCosRawCode (p : FloorExpCodeParameters) : FloorRationalCode :=
  (floorRationalCisCode p).1.1.1

/-- A finite, fixed basis of actual machine programs. None of its fields is a
source-value oracle; all realizations are discharged by explicit raw programs. -/
structure FloorExprMachineBasis where
  coordinate : Nat.Partrec.Code
  parameter : Nat.Partrec.Code
  flat : Nat.Partrec.Code
  scale : Nat.Partrec.Code
  add : Nat.Partrec.Code
  mul : Nat.Partrec.Code
  neg : Nat.Partrec.Code
  sin : Nat.Partrec.Code
  cos : Nat.Partrec.Code
  tolerance : Nat.Partrec.Code

/-- Data and hypotheses for Floor Expr Machine Basis Correct in the Coded Floor construction. -/
structure FloorExprMachineBasisCorrect (basis : FloorExprMachineBasis) : Prop where
  coordinate : floorCodeRealizes basis.coordinate
    (fun q : ℕ × FloorExprQueryCode => floorPointCodeAt q.1 q.2.2.1)
  parameter : floorCodeRealizes basis.parameter floorExprParameterRawCode
  flat : floorCodeRealizes basis.flat
    (fun q : ℕ × FloorExprQueryCode => floorExprFlatRawCode q.1 q.2)
  scale : floorCodeRealizes basis.scale
    (fun q : FloorRationalCode × FloorExprQueryCode => floorExprQueryScale q.1 q.2)
  add : floorCodeRealizes basis.add
    (fun p : FloorRationalCode × FloorRationalCode => floorRationalCodeAdd p.1 p.2)
  mul : floorCodeRealizes basis.mul
    (fun p : FloorRationalCode × FloorRationalCode => floorRationalCodeMul p.1 p.2)
  neg : floorCodeRealizes basis.neg floorRationalCodeNeg
  sin : floorCodeRealizes basis.sin floorExprSinRawCode
  cos : floorCodeRealizes basis.cos floorExprCosRawCode
  tolerance : floorCodeRealizes basis.tolerance (fun q : FloorExprQueryCode => q.2.2)

/-- Original `floorExprMachineBasis_exists` guarantee for the `FloorExprMachineBasis` construction; the complete source hypotheses are retained. -/
theorem floorExprMachineBasis_exists : ∃ basis, FloorExprMachineBasisCorrect basis := by
  obtain ⟨coord,hcoord⟩ := floorCodeRealizes_exists
    (fun q : ℕ × FloorExprQueryCode => floorPointCodeAt q.1 q.2.2.1)
    ((primrec_floorPointCodeAt.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).to_comp)
  obtain ⟨param,hparam⟩ := floorCodeRealizes_exists floorExprParameterRawCode
    primrec_floorExprParameterRawCode.to_comp
  obtain ⟨flat,hflat⟩ := floorCodeRealizes_exists
    (fun q : ℕ × FloorExprQueryCode => floorExprFlatRawCode q.1 q.2) primrec_floorExprFlatRawCode.to_comp
  obtain ⟨scale,hscale⟩ := floorCodeRealizes_exists
    (fun q : FloorRationalCode × FloorExprQueryCode => floorExprQueryScale q.1 q.2) primrec_floorExprQueryScale.to_comp
  obtain ⟨add,hadd⟩ := floorCodeRealizes_exists
    (fun p : FloorRationalCode × FloorRationalCode => floorRationalCodeAdd p.1 p.2) primrec_floorRationalCodeAdd.to_comp
  obtain ⟨mul,hmul⟩ := floorCodeRealizes_exists
    (fun p : FloorRationalCode × FloorRationalCode => floorRationalCodeMul p.1 p.2) primrec_floorRationalCodeMul.to_comp
  obtain ⟨neg,hneg⟩ := floorCodeRealizes_exists floorRationalCodeNeg primrec_floorRationalCodeNeg.to_comp
  have hsin : Primrec floorExprSinRawCode :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp primrec_floorRationalCisCode))
  have hcos : Primrec floorExprCosRawCode :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp primrec_floorRationalCisCode))
  obtain ⟨sin,hsin⟩ := floorCodeRealizes_exists floorExprSinRawCode hsin.to_comp
  obtain ⟨cos,hcos⟩ := floorCodeRealizes_exists floorExprCosRawCode hcos.to_comp
  obtain ⟨tol,htol⟩ := floorCodeRealizes_exists
    (fun q : FloorExprQueryCode => q.2.2) (Primrec.snd.comp Primrec.snd).to_comp
  exact ⟨⟨coord,param,flat,scale,add,mul,neg,sin,cos,tol⟩,
    ⟨hcoord,hparam,hflat,hscale,hadd,hmul,hneg,hsin,hcos,htol⟩⟩

end Qatlib.Concepts.EffectiveGauge.CodedFloor
