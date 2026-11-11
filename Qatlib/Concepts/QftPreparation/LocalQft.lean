/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

/-!
# Fourier circuit costs and finite fair-bit sampling

Collects the exact Fourier matrix implementation and gate cost together with a bounded fair-bit
rejection sampler. `three_label_bounded_fair_bits_impossible` rules out exact equal fibers for
three labels from a fixed number of fair bits, while `aqFairLabelSampler` gives uniform returned
labels with bounded failure probability and bit cost. The Fourier construction has the
background of [NielsenChuang2010].

## Main statements

* `aqLocalQFT_actual_matrix_and_cost`: states the Fourier matrix identity, exact gate count, and
  zero query count.
* `aqFairLabelSampler_distribution_and_bits`: bounds the sampler's failure probability and bit
  costs.
* `three_label_bounded_fair_bits_impossible`: rules out an exact uniform three-label map from
  fixed-length bit strings.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option autoImplicit false
open scoped ENNReal BigOperators
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

namespace Qatlib.Concepts.QftPreparation.LocalQft

/-- No map from `2 ^ k` equally likely bit strings to three labels has all three fibers of equal
cardinality. -/
theorem three_label_bounded_fair_bits_impossible (k : ℕ) :
    ¬ ∃ f : Fin (2 ^ k) → Fin 3, ∀ x y : Fin 3,
      (Finset.univ.filter (fun b => f b = x)).card =
        (Finset.univ.filter (fun b => f b = y)).card := by
  rintro ⟨f, hf⟩
  have htotal : (Finset.univ : Finset (Fin (2 ^ k))).card =
      ∑ x : Fin 3, (Finset.univ.filter (fun b => f b = x)).card := by
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have he : 2 ^ k = 3 * (Finset.univ.filter (fun b => f b = (0 : Fin 3))).card := by
    simpa only [Finset.card_univ, Fintype.card_fin, hf _ 0, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] using htotal
  have hd : 3 ∣ 2 ^ k := ⟨_, he⟩
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at hbad

/-- The finite rejection sampler for `C` labels, using `Nat.clog 2 C` fair bits per attempt and
at most `fuel` attempts. -/
noncomputable def aqFairLabelSampler (C fuel : ℕ) :=
  finiteCoinRun (Nat.clog 2 C) C fuel

/-- For positive `C`, each returned label has mass `(1 - coinRejectMass (Nat.clog 2 C) C ^ fuel)
/ C`, pending mass is at most `1 / 2 ^ fuel`, expected bit cost is at most `2 * Nat.clog 2
C`, and bit cost is bounded by `fuel * Nat.clog 2 C`. -/
theorem aqFairLabelSampler_distribution_and_bits (C fuel : ℕ) (hC : 0 < C) :
    (∀ j : Fin C, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (aqFairLabelSampler C fuel)
      (fun z => z.1 = Sum.inl j) =
      (1 - coinRejectMass (Nat.clog 2 C) C ^ fuel) / (C : ℝ≥0∞)) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (aqFairLabelSampler C fuel) (fun z => z.1 = Sum.inr ()) ≤
      (1 / 2 : ℝ≥0∞) ^ fuel ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (aqFairLabelSampler C fuel) ≤
      ((2 * Nat.clog 2 C : ℕ) : ℝ≥0∞) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (aqFairLabelSampler C fuel) (fuel * Nat.clog 2 C) := by
  have hc := finite_coin_effective_cutoff C fuel hC
  have hd := finite_coin_return_and_pending (Nat.clog 2 C) C fuel hC hc.1
  exact ⟨hd.2, hc.2.2.1, hc.2.2.2,
    (finite_coin_actual_bit_cost (Nat.clog 2 C) C fuel hc.1).1⟩

/-- The local Fourier program implements the relabeled `QFTMatrix (2 ^ n)` using `n + n * (n -
1) / 2 + n / 2` gates and zero queries. -/
theorem aqLocalQFT_actual_matrix_and_cost (n : ℕ) :
    localProgramMatrix (localQFT n) =
      relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
    GateCount (localProgramCircuit (localQFT n)) =
      n + n * (n - 1) / 2 + n / 2 ∧
    QueryCount (localProgramCircuit (localQFT n)) = 0 := by
  exact ⟨(localQFT_exact_positive_matrix n).1,
    (localQFT_exact_gate_counts_and_wires n).2.2.2.1,
    (localQFT_exact_gate_counts_and_wires n).2.2.2.2.1⟩

end Qatlib.Concepts.QftPreparation.LocalQft
