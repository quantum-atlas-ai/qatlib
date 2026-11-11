/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalBridge

/-!
# Paid Rational Codec

Raw Machine constructions for Effective Gauge.
Defines `read`.
Proves `read_complete`, `read_sound`, `read_eq_some_iff`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalBridge
open Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open Qatlib.Concepts.BitWordCompiler

/-- The actual binary ABI keeps four canonical natural fields and checks the
stored denominator. Parsing correctness alone does not pay its machine cost. -/
def read (bits : CanonicalCodec.Bits) : Option (RedundantRational.Frac × CanonicalCodec.Bits) := do
  let (p,tail) ← CanonicalCodec.readNat bits
  let (n,tail) ← CanonicalCodec.readNat tail
  let (r,tail) ← CanonicalCodec.readNat tail
  let (s,tail) ← CanonicalCodec.readNat tail
  if h : r≠s then pure (⟨(p,n),(r,s),h⟩,tail) else none

/-- Original `read_complete` guarantee for the `PaidRationalCodec` construction; the complete source hypotheses are retained. -/
theorem read_complete (q : RedundantRational.Frac) (tail : CanonicalCodec.Bits) :
    read (encode q++tail)=some (q,tail) := by
  cases q with
  | mk num den hd =>
    rcases num with ⟨p,n⟩
    rcases den with ⟨r,s⟩
    simp [read,encode,PaidFractionInverse.input,List.append_assoc,CanonicalCodec.readNat_complete,hd]

/-- Original `read_sound` guarantee for the `PaidRationalCodec` construction; the complete source hypotheses are retained. -/
theorem read_sound (input : CanonicalCodec.Bits) (q : RedundantRational.Frac) (tail : CanonicalCodec.Bits)
    (h : read input=some (q,tail)) : input=encode q++tail := by
  unfold read at h
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨p,t1⟩,hp,h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨n,t2⟩,hn,h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨r,t3⟩,hr,h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨s,t4⟩,hs,h⟩
  dsimp only at h
  split_ifs at h with hd
  · obtain ⟨hq,ht⟩ := Prod.mk.inj (Option.some.inj h)
    cases hq
    cases ht
    rw [CanonicalCodec.readNat_sound input p t1 hp,CanonicalCodec.readNat_sound t1 n t2 hn,
      CanonicalCodec.readNat_sound t2 r t3 hr,CanonicalCodec.readNat_sound t3 s tail hs]
    simp only [encode,PaidFractionInverse.input,List.append_assoc]

/-- Original `read_eq_some_iff` guarantee for the `PaidRationalCodec` construction; the complete source hypotheses are retained. -/
theorem read_eq_some_iff (input : CanonicalCodec.Bits) (q : RedundantRational.Frac)
    (tail : CanonicalCodec.Bits) : read input=some (q,tail) ↔ input=encode q++tail := by
  constructor
  · exact read_sound input q tail
  · rintro rfl
    exact read_complete q tail

/-- Every original rational value has a well-framed finite payload; this
coverage identity makes no claim about converting an external source ABI. -/
theorem originalRat_coverage (x : ℚ) :
    ∃ payload : RedundantRational.Frac, RedundantRational.value payload=x ∧
      ∀ tail, read (encode payload++tail)=some (payload,tail) :=
  ⟨RedundantRational.ofRat x,RedundantRational.value_ofRat x,read_complete _⟩

end Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalBridge
