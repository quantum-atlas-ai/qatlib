/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorProgramSourceCode

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Source Code Obstruction

Coded Floor constructions for Effective Gauge.
Defines `FloorProgramSourceInputCode`, `floorProgramSourceInputCode`, `FloorProgramSourceCodeRealizes`.
Proves `floorProgramSourceCode_generated`, `floorProgramSourceCode_no_floor_machine`, `floorProgramSourceCode_legal`.
-/

set_option autoImplicit false
open scoped ContDiff
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- The explicit input includes both program codes, the fixed center (3,3,3),
radius 1 and certified boundary gap 1. All geometric data are finite integers. -/
abbrev FloorProgramSourceInputCode := Nat.Partrec.Code × Nat.Partrec.Code × (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- Definition of floor Program Source Input Code in the Coded Floor construction. -/
def floorProgramSourceInputCode (jets bounds : Nat.Partrec.Code) : FloorProgramSourceInputCode :=
  (jets,bounds,(3,3,3),1,1)

/-- Finite input-code realizations of the full jet and bound programs. These
conditions are proved for a computably generated family, rather than assumed
as an unavailable source evaluator. -/
def FloorProgramSourceCodeRealizes (jets bounds c : Nat.Partrec.Code) : Prop :=
  (∀ q, Nat.Partrec.Code.eval jets (Encodable.encode q)=
    Part.some (Encodable.encode (floorEncodedJetSource c q))) ∧
  (∀ order, Nat.Partrec.Code.eval bounds (Encodable.encode order)=
    Part.some (Encodable.encode (floorSourceBoundRawCode order)))

/-- Original `floorProgramSourceCode_generated` guarantee for the `FloorSourceCodeObstruction` construction; the complete source hypotheses are retained. -/
theorem floorProgramSourceCode_generated :
    ∃ generate : Nat.Partrec.Code → Nat.Partrec.Code, Computable generate ∧
    ∃ bounds : Nat.Partrec.Code, ∀ c, FloorProgramSourceCodeRealizes (generate c) bounds c := by
  obtain ⟨generate,hgenerate,bounds,hjets,hbounds⟩ := floorProgramSourceCode_programs
  exact ⟨generate,hgenerate,bounds,fun c => ⟨hjets c,hbounds⟩⟩

/-- A purported machine may inspect all of both finite input codes and may
fail to halt outside this legal family. Even this weaker specification is
impossible: on every generated legal input it must return the reference floor. -/
theorem floorProgramSourceCode_no_floor_machine :
    ¬∃ machine : Nat.Partrec.Code, ∀ jets bounds c,
      FloorProgramSourceCodeRealizes jets bounds c →
      Nat.Partrec.Code.eval machine (Encodable.encode (floorProgramSourceInputCode jets bounds))=
        Part.some (Encodable.encode (⌊floorProgramReferenceMean c⌋ : ℤ)) := by
  classical
  rintro ⟨machine,hmachine⟩
  obtain ⟨generate,hgenerate,bounds,hcorrect⟩ := floorProgramSourceCode_generated
  have hinput : Computable (fun c => Encodable.encode (floorProgramSourceInputCode (generate c) bounds)) :=
    Primrec.encode.to_comp.comp
      (hgenerate.pair ((Computable.const bounds).pair (Computable.const ((3,3,3),1,1))))
  have hresult : Computable (fun c : Nat.Partrec.Code => Encodable.encode (⌊floorProgramReferenceMean c⌋ : ℤ)) :=
    (Nat.Partrec.Code.eval_part.comp (Computable.const machine) hinput).of_eq_tot (fun c => by
      rw [hmachine (generate c) bounds c (hcorrect c)]
      simp)
  have hbool := Primrec.beq.to_comp.comp hresult (Computable.const (Encodable.encode (-1 : ℤ)))
  have hpred : ComputablePred (fun c : Nat.Partrec.Code =>
      Encodable.encode (⌊floorProgramReferenceMean c⌋ : ℤ)=Encodable.encode (-1 : ℤ)) :=
    ComputablePred.computable_iff.mpr ⟨_,hbool,funext (fun c => propext (by simp))⟩
  apply floorProgramReferenceMean_not_computable_pred
  exact hpred.of_eq (fun c => Encodable.encode_injective.eq_iff)

/-- The machine-coded input family meets the original smooth periodic unit
field, all-jet accuracy and all-order bound requirements. Its fixed ball and
gap were established independently of the halting parameter. -/
theorem floorProgramSourceCode_legal (c : Nat.Partrec.Code) :
    ContDiff ℝ ∞ (floorPeriodicSpin (floorProgramAmplitude c : ℝ)) ∧
    IsPeriodicField (floorPeriodicSpin (floorProgramAmplitude c : ℝ)) ∧
    (∀ X, ‖floorPeriodicSpin (floorProgramAmplitude c : ℝ) X‖=1) ∧
    OriginalAllJetAccurate (floorPeriodicSpin (floorProgramAmplitude c : ℝ)) (floorProgramJetSource c) ∧
    OriginalPositiveJetBounds (floorPeriodicSpin (floorProgramAmplitude c : ℝ)) floorSourceJetBound :=
  ⟨floorPeriodicSpin_contDiff _,floorPeriodicSpin_periodic _,floorPeriodicSpin_norm _,
    floorProgramJetSource_accurate c,floorProgramJetSource_bounds c⟩

end Qatlib.Concepts.EffectiveGauge.CodedFloor
