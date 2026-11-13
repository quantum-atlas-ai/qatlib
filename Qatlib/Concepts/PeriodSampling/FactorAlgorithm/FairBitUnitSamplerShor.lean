/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FairBitUnitSamplerStat

/-!
# Fair-bit sampling of modular units

Proves `fairBitUnitSampler`, the exact counting and bit-cost properties of decoding uniform bit
strings as modular units. This supplies the unit-sampling component of the finite factoring
model associated with [Shor1997].

## Main statements

* `fairBitUnitSampler`: Establishes unique unit encodings, rejection counts, and exact bit cost.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

/-- Establishes the unique encoding of each unit, the exact number of rejected strings, and the
exact `k`-bit cost support of the sampler in the factoring model associated with [Shor1997]. -/
theorem fairBitUnitSampler : FairBitUnitSampler := by
  intro N k _ _ hk
  have hfib := bounded_bit_decoder_fibers k (Fintype.card (ZMod N)ˣ) hk
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hdecode : ∀ b : Reg k, decodeUnit N k b = some u ↔
        decodeBoundedBits k (Fintype.card (ZMod N)ˣ) b =
          some (Fintype.equivFin (ZMod N)ˣ u) := by
      intro b
      unfold decodeUnit
      cases h : decodeBoundedBits k (Fintype.card (ZMod N)ˣ) b with
      | none => simp
      | some i =>
        simp only [Option.map_some, Option.some.injEq]
        exact (Fintype.equivFin (ZMod N)ˣ).symm_apply_eq
    simpa only [hdecode] using! hfib.1 (Fintype.equivFin (ZMod N)ˣ u)
  · simpa only [decodeUnit, Option.map_eq_none_iff] using! hfib.2
  · intro ω n hn
    simp [fair_bit_program_joint_distribution, hn]

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
