/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorNegativeExpCode

@[expose] public section

/-!
# Floor Encoded Execution

Coded Floor constructions for Effective Gauge.
Proves `floorCode_of_primrec`, `floorExpCodeRun_encoded`, `floorReducedNegativeExpCode_encoded`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- For a primitive-recursive function on primitively codable types, one partial-recursive code
computes every encoded output from the corresponding encoded input. -/
private theorem floorCode_of_primrec {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Primrec f) :
    ∃ c : Nat.Partrec.Code, ∀ a,
      Nat.Partrec.Code.eval c (Encodable.encode a)=Part.some (Encodable.encode (f a)) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf.to_comp
  refine ⟨c,?_⟩
  intro a
  simpa using congrFun hc (Encodable.encode a)

/-- A genuine finite partial-recursive code executes every encoded bounded
Taylor run and returns exactly the encoded finite state, on every payload. -/
theorem floorExpCodeRun_encoded :
    ∃ c : Nat.Partrec.Code, ∀ (p : FloorExpCodeParameters) (s : FloorExpCodeState) (fuel : ℕ),
      Nat.Partrec.Code.eval c (Encodable.encode ((p,s),fuel))=
        Part.some (Encodable.encode (floorExpCodeRun p s fuel)) := by
  obtain ⟨c,hc⟩ := floorCode_of_primrec
    (fun x : (FloorExpCodeParameters × FloorExpCodeState) × ℕ => floorExpCodeRun x.1.1 x.1.2 x.2)
    primrec_floorExpCodeRun
  exact ⟨c,fun p s fuel => hc ((p,s),fuel)⟩

/-- One partial-recursive code computes the encoded result of the reduced negative-exponential
routine for every encoded input pair. -/
theorem floorReducedNegativeExpCode_encoded :
    ∃ c : Nat.Partrec.Code, ∀ p : FloorExpCodeParameters,
      Nat.Partrec.Code.eval c (Encodable.encode p)=
        Part.some (Encodable.encode (floorReducedNegativeExpCode p)) :=
  floorCode_of_primrec floorReducedNegativeExpCode primrec_floorReducedNegativeExpCode

end Qatlib.Concepts.EffectiveGauge.CodedFloor
