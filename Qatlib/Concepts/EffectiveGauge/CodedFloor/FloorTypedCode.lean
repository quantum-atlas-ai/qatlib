/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.CodedFloor.FloorCodeFamilyCompiler

@[expose] public section

/-!
# Floor Typed Code

Coded Floor constructions for Effective Gauge.
Defines `floorCodeRealizes`.
Proves `floorCodeRealizes_comp`, `floorCodeRealizes_pair`, `floorCodeRealizes_const`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor

/-- Exact execution on the standard encodings, without an external evaluator promise. -/
def floorCodeRealizes {A B : Type*} [Primcodable A] [Primcodable B]
    (c : Nat.Partrec.Code) (f : A → B) : Prop :=
  ∀ a, Nat.Partrec.Code.eval c (Encodable.encode a)=Part.some (Encodable.encode (f a))

/-- If the two codes realize typed functions `g : A → B` and `f : B → C`, composing the codes
realizes `f ∘ g` on encoded inputs. -/
theorem floorCodeRealizes_comp {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    {cf cg : Nat.Partrec.Code} {f : B → C} {g : A → B}
    (hf : floorCodeRealizes cf f) (hg : floorCodeRealizes cg g) :
    floorCodeRealizes (.comp cf cg) (fun a => f (g a)) := by
  intro a
  change (Nat.Partrec.Code.eval cg (Encodable.encode a)).bind (fun n : ℕ => Nat.Partrec.Code.eval cf n)=_
  rw [hg a]
  rw [Part.bind_some]
  exact hf (g a)

/-- Pairing codes that realize two functions with a common input type realizes their pointwise
ordered pair. -/
theorem floorCodeRealizes_pair {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    {cf cg : Nat.Partrec.Code} {f : A → B} {g : A → C}
    (hf : floorCodeRealizes cf f) (hg : floorCodeRealizes cg g) :
    floorCodeRealizes (.pair cf cg) (fun a => (f a,g a)) := by
  intro a
  change (Nat.pair <$> Nat.Partrec.Code.eval cf (Encodable.encode a) <*>
    Nat.Partrec.Code.eval cg (Encodable.encode a))=_
  rw [hf a,hg a]
  simp [Seq.seq,Encodable.encode_prod_val]

/-- The partial-recursive constant code for the encoding of `b` realizes the constant function
with value `b` on encoded inputs of any primitively codable type. -/
theorem floorCodeRealizes_const {A B : Type*} [Primcodable A] [Primcodable B] (b : B) :
    floorCodeRealizes (Nat.Partrec.Code.const (Encodable.encode b)) (fun _ : A => b) :=
  fun _ => Nat.Partrec.Code.eval_const _ _

/-- If a code realizes a function on encoded pairs, currying it at the encoding of `a` realizes
the function of the remaining input obtained by fixing the first argument to `a`. -/
theorem floorCodeRealizes_curry {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    {c : Nat.Partrec.Code} {f : A × B → C} (hf : floorCodeRealizes c f) (a : A) :
    floorCodeRealizes (Nat.Partrec.Code.curry c (Encodable.encode a)) (fun b => f (a,b)) := by
  intro b
  rw [Nat.Partrec.Code.eval_curry]
  exact hf (a,b)

/-- Every computable function between primitively codable types has a partial-recursive code
realizing it on encoded inputs. -/
theorem floorCodeRealizes_exists {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Computable f) : ∃ c, floorCodeRealizes c f :=
  floorComputableFixedCode f hf

/-- A function between primitively codable types is computable whenever a partial-recursive code
realizes it on every encoded input. -/
theorem floorCodeRealizes_computable {A B : Type*} [Primcodable A] [Primcodable B]
    {c : Nat.Partrec.Code} {f : A → B} (hf : floorCodeRealizes c f) : Computable f := by
  apply Partrec.of_eq_tot
    ((Nat.Partrec.Code.eval_part.comp (Computable.const c) Primrec.encode.to_comp).bind
      (Computable.decode.comp Computable.snd).ofOption.to₂)
  intro a
  simp [hf a,Encodable.encodek]

end Qatlib.Concepts.EffectiveGauge.CodedFloor
