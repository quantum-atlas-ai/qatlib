/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidOriginalConditionalBounds

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Orientation

Raw Machine constructions for Effective Gauge.
Defines `positiveDen`.
Proves `positiveDen_value`, `positiveDen_order`, `positiveDen_den_value`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
namespace PaidBoundCompression

/-- A finite field permutation or identity. No rational reduction, gcd or
real sign oracle is used to orient an original raw bound answer. -/
def positiveDen (q : RedundantRational.Frac) : RedundantRational.Frac :=
  if q.den.2<q.den.1 then q else
    ⟨(q.num.2,q.num.1),(q.den.2,q.den.1),fun h => q.den_ne h.symm⟩

/-- Original `positiveDen_value` guarantee for the `PaidBoundOrientation` construction; the complete source hypotheses are retained. -/
theorem positiveDen_value (q : RedundantRational.Frac) :
    RedundantRational.value (positiveDen q)=RedundantRational.value q := by
  dsimp only [positiveDen]
  split_ifs with h
  · rfl
  · dsimp only [RedundantRational.value,RedundantRational.Pair.value]
    have hn : (q.num.2 : ℚ)-q.num.1=-((q.num.1 : ℚ)-q.num.2) := by ring
    have hd : (q.den.2 : ℚ)-q.den.1=-((q.den.1 : ℚ)-q.den.2) := by ring
    rw [hn,hd,neg_div_neg_eq]

/-- Original `positiveDen_order` guarantee for the `PaidBoundOrientation` construction; the complete source hypotheses are retained. -/
theorem positiveDen_order (q : RedundantRational.Frac) :
    (positiveDen q).den.2<(positiveDen q).den.1 := by
  dsimp only [positiveDen]
  split_ifs with h
  · exact h
  · have hn := q.den_ne
    dsimp only
    omega

/-- Original `positiveDen_den_value` guarantee for the `PaidBoundOrientation` construction; the complete source hypotheses are retained. -/
theorem positiveDen_den_value (q : RedundantRational.Frac) :
    (0 : ℚ)<RedundantRational.Pair.value (positiveDen q).den := by
  dsimp only [RedundantRational.Pair.value]
  apply sub_pos.mpr
  exact_mod_cast positiveDen_order q

/-- Original `positiveDen_num_order` guarantee for the `PaidBoundOrientation` construction; the complete source hypotheses are retained. -/
theorem positiveDen_num_order (q : RedundantRational.Frac) (hm : 0≤RedundantRational.value q) :
    (positiveDen q).num.2≤(positiveDen q).num.1 := by
  have hv : 0≤RedundantRational.value (positiveDen q) := by rw [positiveDen_value]; exact hm
  have hn := (le_div_iff₀ (positiveDen_den_value q)).mp hv
  simp only [zero_mul] at hn
  dsimp only [RedundantRational.Pair.value] at hn
  exact_mod_cast sub_nonneg.mp hn

/-- Orientation preserves the exact stored-word length, including any
cancellation. This is not a machine clock for performing the permutation. -/
theorem positiveDen_length (q : RedundantRational.Frac) :
    (PaidRationalBridge.encode (positiveDen q)).length=(PaidRationalBridge.encode q).length := by
  dsimp only [positiveDen]
  split_ifs
  · rfl
  · simp only [PaidRationalBridge.encode,PaidFractionInverse.input,List.length_append]
    omega

end PaidBoundCompression
end Qatlib.Concepts.EffectiveGauge.RawMachine
