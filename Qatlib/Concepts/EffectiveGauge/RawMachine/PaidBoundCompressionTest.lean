/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundOrientation

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Compression Test

Raw Machine constructions for Effective Gauge.
Defines `enough`, `enoughBit`, `ceilingWitness`.
Proves `enough_iff`, `enough_mono`, `ceilingWitness_cast`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
namespace PaidBoundCompression

/-- A comparison of two sums of natural products on the stored fields.
Its eventual native implementation must pay for all arithmetic and reads. -/
def enough (q : RedundantRational.Frac) (j : ℕ) : Prop :=
  256*(positiveDen q).num.1+j*(positiveDen q).den.2 ≤
    256*(positiveDen q).num.2+j*(positiveDen q).den.1

/-- Decidability of the rational threshold predicate. -/
instance (q : RedundantRational.Frac) (j : ℕ) : Decidable (enough q j) := by
  unfold enough
  infer_instance

/-- Definition of enough Bit in the Raw Machine construction. -/
def enoughBit (q : RedundantRational.Frac) (j : ℕ) : Bool := decide (enough q j)

/-- Original `enough_iff` guarantee for the `PaidBoundCompressionTest` construction; the complete source hypotheses are retained. -/
theorem enough_iff (q : RedundantRational.Frac) (j : ℕ) :
    enough q j ↔ 256*RedundantRational.value q≤(j : ℚ) := by
  rw [←positiveDen_value q]
  dsimp only [RedundantRational.value]
  rw [←mul_div_assoc,div_le_iff₀ (positiveDen_den_value q)]
  dsimp only [enough,RedundantRational.Pair.value]
  constructor
  · intro h
    have hh : (256 : ℚ)*(positiveDen q).num.1+(j : ℚ)*(positiveDen q).den.2 ≤
        256*(positiveDen q).num.2+(j : ℚ)*(positiveDen q).den.1 := by exact_mod_cast h
    linarith
  · intro h
    have hh : (256 : ℚ)*(positiveDen q).num.1+(j : ℚ)*(positiveDen q).den.2 ≤
        256*(positiveDen q).num.2+(j : ℚ)*(positiveDen q).den.1 := by linarith
    exact_mod_cast hh

/-- Original `enough_mono` guarantee for the `PaidBoundCompressionTest` construction; the complete source hypotheses are retained. -/
theorem enough_mono (q : RedundantRational.Frac) {j k : ℕ} (h : enough q j) (hjk : j≤k) : enough q k := by
  rw [enough_iff] at h ⊢
  exact h.trans (by exact_mod_cast hjk)

/-- Proof-side least stopping index, not an extra input or runtime fuel. -/
def ceilingWitness (q : RedundantRational.Frac) : ℕ := (Int.ceil (256*RedundantRational.value q)).toNat

/-- Original `ceilingWitness_cast` guarantee for the `PaidBoundCompressionTest` construction; the complete source hypotheses are retained. -/
theorem ceilingWitness_cast (q : RedundantRational.Frac) (hm : 0≤RedundantRational.value q) :
    (ceilingWitness q : ℚ)=(Int.ceil (256*RedundantRational.value q) : ℚ) := by
  have hz := Int.ceil_nonneg (mul_nonneg (by norm_num : (0 : ℚ)≤256) hm)
  exact_mod_cast Int.toNat_of_nonneg hz

/-- Original `enough_witness` guarantee for the `PaidBoundCompressionTest` construction; the complete source hypotheses are retained. -/
theorem enough_witness (q : RedundantRational.Frac) (hm : 0≤RedundantRational.value q) :
    enough q (ceilingWitness q) := by
  rw [enough_iff,ceilingWitness_cast q hm]
  exact Int.le_ceil _

/-- Original `witness_le_iff` guarantee for the `PaidBoundCompressionTest` construction; the complete source hypotheses are retained. -/
theorem witness_le_iff (q : RedundantRational.Frac) (hm : 0≤RedundantRational.value q) (j : ℕ) :
    ceilingWitness q≤j ↔ enough q j := by
  rw [enough_iff]
  constructor
  · intro h
    exact (enough_iff q (ceilingWitness q)).mp (enough_witness q hm) |>.trans (by exact_mod_cast h)
  · intro h
    have hc : Int.ceil (256*RedundantRational.value q)≤(j : ℤ) := Int.ceil_le.mpr h
    have hq : (Int.ceil (256*RedundantRational.value q) : ℚ)≤(j : ℚ) := by exact_mod_cast hc
    rw [←ceilingWitness_cast q hm] at hq
    exact_mod_cast hq

/-- Original `witness_packet` guarantee for the `PaidBoundCompressionTest` construction; the complete source hypotheses are retained. -/
theorem witness_packet (q : RedundantRational.Frac) (hm : 0≤RedundantRational.value q) :
    (ceilingWitness q : ℚ)/256=sourceMeanCompressedBound (RedundantRational.value q) := by
  rw [ceilingWitness_cast q hm]
  rfl

/-- A scalar upper bound on the compressed value controls the number of
binary-counter iterations, not the magnitude of any raw numerator field. -/
theorem witness_bound (q : RedundantRational.Frac) (hm : 0≤RedundantRational.value q) (K : ℕ)
    (hK : sourceMeanCompressedBound (RedundantRational.value q)≤(K : ℚ)) :
    ceilingWitness q≤256*K := by
  have hh := witness_packet q hm
  have hc : (ceilingWitness q : ℚ)≤256*(K : ℚ) := by linarith
  exact_mod_cast hc

end PaidBoundCompression
end Qatlib.Concepts.EffectiveGauge.RawMachine
