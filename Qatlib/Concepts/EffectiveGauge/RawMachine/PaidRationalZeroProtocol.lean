/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidRationalBridge
import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Rational Zero Protocol

Raw Machine constructions for Effective Gauge.
Defines `twoZeroBits`.
Proves `bits_nonempty`, `natBits_head`, `prefix_encode`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
namespace PaidRationalZero

/-- Definition of two Zero Bits in the Raw Machine construction. -/
def twoZeroBits (bits : CanonicalCodec.Bits) : Bool :=
  bits.head?==some false && bits.tail.head?==some false

/-- Original `bits_nonempty` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
private theorem bits_nonempty (n : ℕ) (hn : n≠0) : n.bits≠[] := by
  induction n using Nat.binaryRec' with
  | zero => exact (hn rfl).elim
  | bit b n h =>
    rw [Nat.bits_append_bit n b h]
    intro hbad; cases hbad

/-- Original `natBits_head` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
private theorem natBits_head (n : ℕ) (tail : CanonicalCodec.Bits) :
    (CanonicalCodec.natBits n++tail).head?=some (decide (n≠0)) := by
  by_cases hn : n=0
  · subst n; rfl
  · have hb : 0<n.bits.length := List.length_pos_iff.mpr (bits_nonempty n hn)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.bits.length≠0)
    simp [CanonicalCodec.natBits,hk,hn,List.replicate_succ]

/-- Original `prefix_encode` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
theorem prefix_encode (q : RedundantRational.Frac) :
    twoZeroBits (PaidRationalBridge.encode q)=decide (q.num.1=0 ∧ q.num.2=0) := by
  by_cases hp : q.num.1=0
  · have h0 : CanonicalCodec.natBits 0=[false] := rfl
    simp only [PaidRationalBridge.encode,PaidFractionInverse.input,hp,h0,
      List.singleton_append,twoZeroBits,List.head?_cons,List.tail_cons]
    rw [natBits_head]
    simp
  · have hh := natBits_head q.num.1
      (CanonicalCodec.natBits q.num.2++(CanonicalCodec.natBits q.den.1++CanonicalCodec.natBits q.den.2))
    simp only [PaidRationalBridge.encode,PaidFractionInverse.input,twoZeroBits,hh]
    simp [hp]

/-- Original `inverse_prefix` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
theorem inverse_prefix (q : RedundantRational.Frac) :
    twoZeroBits (PaidRationalBridge.encode (RedundantRational.inv q))=decide (q.num.1=q.num.2) := by
  rw [prefix_encode]
  dsimp only [RedundantRational.inv]
  split_ifs with hz
  · simp [RedundantRational.ofNat,hz]
  · have hd : ¬(q.den.1=0 ∧ q.den.2=0) := by rintro ⟨h1,h2⟩; exact q.den_ne (h1.trans h2.symm)
    simp [hd,hz]

/-- Original `value_zero` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
theorem value_zero (q : RedundantRational.Frac) :
    RedundantRational.value q=0 ↔ q.num.1=q.num.2 := by
  simp only [RedundantRational.value,div_eq_zero_iff,RedundantRational.den_value_ne q,
    or_false,RedundantRational.Pair.value_eq_zero]

/-- Original `compressed_zero` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
theorem compressed_zero (q : RedundantRational.Frac) (hn : 0≤RedundantRational.value q) :
    sourceMeanCompressedBound (RedundantRational.value q)=0 ↔ q.num.1=q.num.2 := by
  rw [←value_zero]
  constructor
  · intro hz
    have he := (sourceMeanCompressedBound_encloses (RedundantRational.value q)).1
    rw [hz] at he
    exact le_antisymm he hn
  · intro hz
    rw [hz]
    norm_num [sourceMeanCompressedBound]

/-- Original `inverse_prefix_compressed` guarantee for the `PaidRationalZeroProtocol` construction; the complete source hypotheses are retained. -/
theorem inverse_prefix_compressed (q : RedundantRational.Frac) (hn : 0≤RedundantRational.value q) :
    twoZeroBits (PaidRationalBridge.encode (RedundantRational.inv q))=
      decide (sourceMeanCompressedBound (RedundantRational.value q)=0) := by
  simp only [inverse_prefix,compressed_zero q hn]

end PaidRationalZero
end Qatlib.Concepts.EffectiveGauge.RawMachine
