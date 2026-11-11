/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Computability.PartrecCode

/-!
# Floor Code Family Compiler

Coded Floor constructions for Effective Gauge.
Proves `floorComputableFixedCode`, `floorPartrecCodeFamily`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor

/-- Original `floorComputableFixedCode` guarantee for the `FloorCodeFamilyCompiler` construction; the complete source hypotheses are retained. -/
theorem floorComputableFixedCode {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Computable f) : ∃ c : Nat.Partrec.Code, ∀ a,
      Nat.Partrec.Code.eval c (Encodable.encode a)=Part.some (Encodable.encode (f a)) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  exact ⟨c,fun a => by simpa using congrFun hc (Encodable.encode a)⟩

/-- Uniform compilation of an actual partial-recursive family. The generator
is computable and the returned finite code has the exact library eval semantics.
This is a compiler lemma, not a source interpreter or floor impossibility theorem. -/
theorem floorPartrecCodeFamily {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    (f : A → B →. C) (hf : Partrec₂ f) :
    ∃ generate : A → Nat.Partrec.Code, Computable generate ∧ ∀ a b,
      Nat.Partrec.Code.eval (generate a) (Encodable.encode b)=(f a b).map Encodable.encode := by
  obtain ⟨base,hbase⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨fun a => Nat.Partrec.Code.curry base (Encodable.encode a),?_,?_⟩
  · exact (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const base) Primrec.encode).to_comp
  · intro a b
    rw [Nat.Partrec.Code.eval_curry]
    simpa using congrFun hbase (Encodable.encode (a,b))

end Qatlib.Concepts.EffectiveGauge.CodedFloor
