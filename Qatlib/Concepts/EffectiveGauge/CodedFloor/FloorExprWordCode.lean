/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorExprDiffCode
import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorSourceSyntax

set_option backward.isDefEq.respectTransparency false

/-!
# Floor Expr Word Code

Coded Floor constructions for Effective Gauge.
Defines `floorExprRepeatDiffCode`, `floorExprJetCode`.
Proves `floorComputableNatIterate`, `computable_floorExprRepeatDiffCode`, `floorComputableThreeIterates`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.SpectralH1 Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Definition of floor Expr Repeat Diff Code in the Coded Floor construction. -/
def floorExprRepeatDiffCode (axis count code : ℕ) : ℕ :=
  Nat.rec code (fun _ value => floorExprDiffCode axis value) count

/-- Definition of floor Expr Jet Code in the Coded Floor construction. -/
def floorExprJetCode (code : ℕ) (alpha : ℕ × ℕ × ℕ) : ℕ :=
  floorExprRepeatDiffCode 0 alpha.1
    (floorExprRepeatDiffCode 1 alpha.2.1 (floorExprRepeatDiffCode 2 alpha.2.2 code))

/-- Original `floorComputableNatIterate` guarantee for the `FloorExprWordCode` construction; the complete source hypotheses are retained. -/
private theorem floorComputableNatIterate {A B : Type*} [Primcodable A] [Primcodable B]
    (step : A → B → B) (hstep : Computable₂ step) :
    Computable (fun q : A × ℕ × B => Nat.rec (motive := fun _ => B) q.2.2 (fun _ value => step q.1 value) q.2.1) :=
  Computable.nat_rec (Computable.fst.comp Computable.snd)
    (Computable.snd.comp Computable.snd)
    ((hstep.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.snd)).to₂)

/-- Original `computable_floorExprRepeatDiffCode` guarantee for the `FloorExprWordCode` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprRepeatDiffCode : Computable (fun q : ℕ × ℕ × ℕ =>
    floorExprRepeatDiffCode q.1 q.2.1 q.2.2) :=
  floorComputableNatIterate floorExprDiffCode computable_floorExprDiffCode

/-- Original `floorComputableThreeIterates` guarantee for the `FloorExprWordCode` construction; the complete source hypotheses are retained. -/
private theorem floorComputableThreeIterates (iter : ℕ → ℕ → ℕ → ℕ)
    (hrep : Computable (fun q : ℕ × ℕ × ℕ => iter q.1 q.2.1 q.2.2)) :
    Computable (fun q : ℕ × (ℕ × ℕ × ℕ) =>
      iter 0 q.2.1 (iter 1 q.2.2.1 (iter 2 q.2.2.2 q.1))) := by
  have hz : Computable (fun q : ℕ × (ℕ × ℕ × ℕ) => iter 2 q.2.2.2 q.1) :=
    hrep.comp ((Computable.const 2).pair
      ((Computable.snd.comp (Computable.snd.comp Computable.snd)).pair Computable.fst))
  have hy : Computable (fun q : ℕ × (ℕ × ℕ × ℕ) =>
      iter 1 q.2.2.1 (iter 2 q.2.2.2 q.1)) :=
    hrep.comp ((Computable.const 1).pair
      ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair hz))
  exact hrep.comp ((Computable.const 0).pair ((Computable.fst.comp Computable.snd).pair hy))

/-- Original `computable_floorExprJetCode` guarantee for the `FloorExprWordCode` construction; the complete source hypotheses are retained. -/
theorem computable_floorExprJetCode : Computable₂ floorExprJetCode :=
  floorComputableThreeIterates floorExprRepeatDiffCode computable_floorExprRepeatDiffCode

/-- Original `floorExprDecode_iterDiffCode` guarantee for the `FloorExprWordCode` construction; the complete source hypotheses are retained. -/
theorem floorExprDecode_iterDiffCode (axis count code : ℕ) :
    floorExprDecode (floorExprRepeatDiffCode axis count code)=
      floorJetWord (floorExprDecode code) (List.replicate count (floorExprAxis axis)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change floorExprDecode (floorExprDiffCode axis (floorExprRepeatDiffCode axis count code))=_
    rw [floorExprDecode_diffCode,List.replicate_succ,floorJetWord,ih]

/-- Original `floorExprDecode_jetCode` guarantee for the `FloorExprWordCode` construction; the complete source hypotheses are retained. -/
theorem floorExprDecode_jetCode (code : ℕ) (alpha : Fin 3 → ℕ) :
    floorExprDecode (floorExprJetCode code (alpha 0,alpha 1,alpha 2))=
      floorJetWord (floorExprDecode code) (sourceCanonicalWord alpha) := by
  rw [floorExprJetCode,floorExprDecode_iterDiffCode,floorExprDecode_iterDiffCode,
    floorExprDecode_iterDiffCode]
  simp only [sourceCanonicalWord,floorJetWord_append]
  rfl

end Qatlib.Concepts.EffectiveGauge.CodedFloor
