/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueFairBitSamplerStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueAuxiliary

/-!
# Fair-bit residue sampler correctness

Proves `residueFairBitSampler`, the exact decoding counts and bit-cost support for sampling
residues from fair bits. It includes the power-of-two capacity window for the chosen bit width
used in the factoring model associated with [Shor1997].

## Main statements

* `residueFairBitSampler`: Establishes residue encoding counts, exact bit cost, and the width
  window.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.PeriodSampling.FactorAlgorithm.Shor1997

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

/-- Establishes the unique encoding of each residue, rejection count, exact bit-cost support,
and chosen bit-width window for the residue sampler in the model associated with [Shor1997]. -/
theorem residueFairBitSampler : ResidueFairBitSampler := by
  refine ⟨?_, residue_bit_width_window⟩
  intro N k _ hk
  have hfib := bounded_bit_decoder_fibers k N hk
  refine ⟨?_, ?_, ?_⟩
  · intro y
    let i : Fin N := ⟨y.val, ZMod.val_lt y⟩
    have hd (b : Reg k) : decodeResidue N k b = some y ↔ decodeBoundedBits k N b = some i := by
      unfold decodeResidue
      cases hb : decodeBoundedBits k N b with
      | none => simp
      | some j =>
        change (some (j.val : ZMod N) = some y ↔ some j = some i)
        simp only [Option.some.injEq]
        constructor
        · intro hj
          apply Fin.ext
          have hv := congrArg ZMod.val hj
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt j.isLt, i] using! hv
        · intro hj
          subst j
          simp [i]
    simpa only [hd] using! hfib.1 i
  · have hd (b : Reg k) : decodeResidue N k b = none ↔ decodeBoundedBits k N b = none := by
      unfold decodeResidue
      cases decodeBoundedBits k N b <;> simp
    simpa only [hd] using! hfib.2
  · intro ω n hn
    simp [fair_bit_program_joint_distribution, hn]
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
