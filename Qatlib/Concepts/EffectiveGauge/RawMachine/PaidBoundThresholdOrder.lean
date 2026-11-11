/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundCompressionTest

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Threshold Order

Raw Machine constructions for Effective Gauge.
Defines `leftSum`, `rightSum`.
Proves `binary_cons`, `true_prefix`, `encoded_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundCompression

/-- Original `binary_cons` guarantee for the `PaidBoundThresholdOrder` construction; the complete source hypotheses are retained. -/
private theorem binary_cons (b : Bool) (bits : CanonicalCodec.Bits) :
    CanonicalCodec.binaryValue (b::bits)=2*CanonicalCodec.binaryValue bits+(if b then 1 else 0) := rfl

/-- Original `true_prefix` guarantee for the `PaidBoundThresholdOrder` construction; the complete source hypotheses are retained. -/
private theorem true_prefix (k : ℕ) (bits : CanonicalCodec.Bits) :
    CanonicalCodec.binaryValue (List.replicate k true++bits)+1=
      2^k*(CanonicalCodec.binaryValue bits+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,binary_cons,Nat.pow_succ]
    simp only [if_true]
    nlinarith only [ih]

/-- Original `encoded_value` guarantee for the `PaidBoundThresholdOrder` construction; the complete source hypotheses are retained. -/
private theorem encoded_value (n : ℕ) :
    CanonicalCodec.binaryValue (CanonicalCodec.natBits n)+1=2^n.bits.length*(2*n+1) := by
  have h : CanonicalCodec.natBits n=List.replicate n.bits.length true++false::n.bits := by
    simp only [CanonicalCodec.natBits,List.append_assoc,List.singleton_append]
  rw [h,true_prefix,binary_cons,CanonicalCodec.binaryValue_bits]
  rfl

/-- Original `encoded_strictMono` guarantee for the `PaidBoundThresholdOrder` construction; the complete source hypotheses are retained. -/
private theorem encoded_strictMono : StrictMono (fun n => CanonicalCodec.binaryValue (CanonicalCodec.natBits n)) := by
  intro a b hab
  change CanonicalCodec.binaryValue (CanonicalCodec.natBits a)<CanonicalCodec.binaryValue (CanonicalCodec.natBits b)
  have hl : a.bits.length≤b.bits.length := by
    rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
    exact Nat.size_le_size hab.le
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hl
  have hm := Nat.mul_lt_mul_of_pos_left (show 2*a+1<2*b+1 by omega)
    (pow_pos (by decide : 0<2) a.bits.length)
  have hw := Nat.mul_le_mul_right (2*b+1) hp
  have he : CanonicalCodec.binaryValue (CanonicalCodec.natBits a)+1<
      CanonicalCodec.binaryValue (CanonicalCodec.natBits b)+1 := by
    rw [encoded_value,encoded_value]
    exact hm.trans_le hw
  omega

/-- Original `encoded_lt_iff` guarantee for the `PaidBoundThresholdOrder` construction; the complete source hypotheses are retained. -/
private theorem encoded_lt_iff (a b : ℕ) :
    CanonicalCodec.binaryValue (CanonicalCodec.natBits a)<CanonicalCodec.binaryValue (CanonicalCodec.natBits b) ↔ a<b :=
  encoded_strictMono.lt_iff_lt

/-- Definition of left Sum in the Raw Machine construction. -/
def leftSum (q : RedundantRational.Frac) (j : ℕ) : ℕ :=
  256*(positiveDen q).num.1+j*(positiveDen q).den.2

/-- Definition of right Sum in the Raw Machine construction. -/
def rightSum (q : RedundantRational.Frac) (j : ℕ) : ℕ :=
  256*(positiveDen q).num.2+j*(positiveDen q).den.1

/-- The actual native sum-products outputs can be compared in their
existing framed reverse-word form. No uncharged result parsing is needed. -/
theorem threshold_order (q : RedundantRational.Frac) (j : ℕ) :
    ReadonlyCompare.order (CanonicalCodec.natBits (leftSum q j)).reverse
      (CanonicalCodec.natBits (rightSum q j)).reverse≠BinaryCompare.Tag.gt ↔ enough q j := by
  simp only [ReadonlyCompare.order,List.reverse_reverse,encoded_lt_iff]
  dsimp only [enough,leftSum,rightSum]
  split_ifs <;> simp_all
  all_goals omega

end PaidBoundCompression
end Qatlib.Concepts.EffectiveGauge.RawMachine
