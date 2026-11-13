/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecoveryDefs
import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecovery

/-!
# Algebraic hidden subgroup recovery endpoints

This module combines compact presentation decoding with counted Smith computations. It relates
computed factors and operation counts to the presentation data, and records decoding
divisibility and the absence of group enumeration.

For cyclic hidden subgroups, `clause19_endpoint` combines a sampling success bound with the
one-query count of the sampling circuit. See [Lomont2004] for the mathematical background.

## Main statements

* `clause17_endpoint`: compact presentation decoding identities.
* `clause18_endpoint`: decoding and counted Smith-operation bounds.
* `clause19_endpoint`: cyclic recovery probability and query count.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.ReductionCore.CompactPresentation

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical
open Qatlib

/-- The factors returned by counted normalized Smith decoding of the presentation table equal
the presentation factors. -/
theorem clause18_counted_run_factors (p : CompactPresentation) :
    (countedNormalizedSmith (smithDecodeRelations p.table)).1.factors = p.factors := by
  rw [countedNormalizedSmith_value]
  rfl

/-- Each counted binary Smith operation is bounded by the rectangular budget at the allocated
pivot fuel. -/
theorem clause18_bitcost (p : CompactPresentation) (op : SmithKernelOp) :
    (countedSmithRunBinary p.table).2 op ≤
      smithRectangularBudget p.generators p.relations
        ((countedSmithRunBinary p.table).2 .pivotFuelAllocated) op :=
  countedSmithRunBinary_bound p.table op

/-- The recovery ledger records `p.generators * L.length` label reads and gcd reductions, the
supplied Smith count, and zero group enumeration. -/
theorem clause18_ledger (p : CompactPresentation) (L : List (FactorLabel p.smith))
    (ops : ℕ) :
    (recoveryLedger p L ops).labelReads = p.generators * L.length ∧
      (recoveryLedger p L ops).gcdReductions = p.generators * L.length ∧
      (recoveryLedger p L ops).smithOperations = ops ∧
      (recoveryLedger p L ops).groupEnumeration = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact compactDecodeLedger_reads p.smith L
  · exact compactDecodeLedger_reductions p.smith L
  · rfl
  · exact compactDecodeLedger_no_enumeration p.smith L

/-- For a finite compact presentation, generator words match the factor count, normalized
decoding preserves quotient classes, and compact decoding satisfies the displayed
divisibility conditions. -/
theorem clause17_endpoint (p : CompactPresentation) (hp : p.isFinite = true)
    (L : List (FactorLabel p.smith)) :
    p.generatorWords.length = p.factors.length ∧
      (∀ v : Fin p.generators → ℤ,
        (Submodule.Quotient.mk (normalizedDecode p.smith (normalizedEncode p.smith v)) :
          PresentationModule (p.relationMatrix)) = Submodule.Quotient.mk v) ∧
      (∀ l ∈ L, ∀ r : Fin p.generators,
        p.smith.coeff r ∣ l r * compactDecode p.smith L r) := by
  have hf : ∀ r : Fin p.generators, 0 < p.smith.coeff r :=
    coeff_pos_of_finite p.smith hp
  refine ⟨compactPresentation_output_size p, ?_, ?_⟩
  · intro v
    exact compactPresentation_reconstruct p v
  · intro l hl r
    exact compactDecode_annihilates p.smith L hf l hl r

/-- For a finite compact presentation, combine the generator-word count and decoding
divisibility conditions with the counted Smith budget and zero group enumeration. -/
theorem clause18_endpoint (p : CompactPresentation) (hp : p.isFinite = true)
    (L : List (FactorLabel p.smith)) (op : SmithKernelOp) :
    p.generatorWords.length = p.factors.length ∧
      (∀ l ∈ L, ∀ r : Fin p.generators,
        p.smith.coeff r ∣ l r * compactDecode p.smith L r) ∧
      (countedSmithRunBinary p.table).2 op ≤
        smithRectangularBudget p.generators p.relations
          ((countedSmithRunBinary p.table).2 .pivotFuelAllocated) op ∧
      (recoveryLedger p L ((countedSmithRunBinary p.table).2 op)).groupEnumeration = 0 := by
  have hf : ∀ r : Fin p.generators, 0 < p.smith.coeff r :=
    coeff_pos_of_finite p.smith hp
  refine ⟨compactPresentation_output_size p, ?_, clause18_bitcost p op, ?_⟩
  · intro l hl r
    exact compactDecode_annihilates p.smith L hf l hl r
  · exact (clause18_ledger p L ((countedSmithRunBinary p.table).2 op)).2.2.2

/-- For the stated cyclic character encoding, `m` samples recover the hidden subgroup with
probability at least `1 - N * (1 / 2) ^ m`, and the sampling circuit uses one query. -/
theorem clause19_endpoint {N : ℕ} [NeZero N]
    {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : ZMod N → R) (e : ZMod N ≃ AddChar (ZMod N) ℂ) (H : AddSubgroup (ZMod N))
    (hf : HidesSubgroup f H) (m : ℕ)
    (he : ∀ a y : ZMod N, e a y = 1 ↔ a * y = 0) :
    1 - (Fintype.card (ZMod N) : ℝ) * ((2 : ℝ)⁻¹)^m ≤
      (tableGroupRecordDist f e).probEvent (fun xs : Fin m → ZMod N =>
        (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) (List.ofFn xs) : Set (ZMod N))
          = (H : Set (ZMod N))) ∧
      QueryCount (tableSamplingCircuit (R := R) e ((1 : Matrix (ZMod N) (ZMod N) ℂ))) = 1 := by
  refine ⟨compact_cyclic_recovery_probability f e H hf m he, ?_⟩
  exact (compact_cyclic_quantum_ledger f e ((1 : Matrix (ZMod N) (ZMod N) ℂ))).1

end Qatlib.Concepts.HspRecovery.ReductionCore
