/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PartitionFunc08.MainResults.MainTheorem

/-!
# Partition-function accuracy and walk cost

The cost estimate `theorem1_walk_cost` aggregates assumed per-sample state and reflection costs
over the ratio estimates. The theorem `theorem1_quantum_speedup` pairs this bound with a
probability of at least three quarters for relative accuracy of the scaled product. These
estimates form part of the partition-function scheme in [WocjanEtAl2009a].

## Main statements

* `theorem1_walk_cost`: The assumed sample count, state cost, reflection cost, and total-cost
  decomposition imply the stated sum of two walk-cost bounds, each proportional to `ℓ ^ 2 / sqrt
  δ`.
* `theorem1_quantum_speedup`: Under the per-ratio accuracy and resource-budget hypotheses, the
  scaled product is relatively accurate with probability at least three quarters and the total
  cost satisfies the stated walk-cost bound.

## References

* [Wocjan et al., 2009][WocjanEtAl2009a]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace Qatlib.Papers.PartitionFunc08.MainResults.Speedup

/-- The assumed sample count, state cost, reflection cost, and total-cost decomposition imply
the stated sum of two walk-cost bounds, each proportional to `ℓ ^ 2 / sqrt δ`. See [Wocjan
et al., 2009][WocjanEtAl2009a]. -/
theorem theorem1_walk_cost
    {ℓ : ℕ} (hℓ : 0 < ℓ) {δ ε εR : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεR : 0 < εR)
    {statePerSample reflPerSample samples total : ℝ}
    (hsp : statePerSample ≤ (ℓ : ℝ) / Real.sqrt δ * (Real.log (32 * (ℓ : ℝ))) ^ 2)
    (hr : reflPerSample ≤
      (2 * (ℓ : ℝ) / ε) * (Real.log (1 / εR) / Real.sqrt δ))
    (hs : samples ≤ Real.log (4 * (ℓ : ℝ)))
    (hs0 : 0 ≤ samples) (hsp0 : 0 ≤ statePerSample) (hr0 : 0 ≤ reflPerSample)
    (htot : total ≤ (ℓ : ℝ) * samples * (statePerSample + reflPerSample)) :
    total ≤ (ℓ : ℝ) ^ 2 / Real.sqrt δ * Real.log (4 * (ℓ : ℝ)) *
        (Real.log (32 * (ℓ : ℝ))) ^ 2 +
      (2 * (ℓ : ℝ) ^ 2 / ε) * Real.log (4 * (ℓ : ℝ)) * (Real.log (1 / εR) / Real.sqrt δ) := by
  set A : ℝ := (ℓ : ℝ) / Real.sqrt δ * (Real.log (32 * (ℓ : ℝ))) ^ 2 with hA
  set B : ℝ := (2 * (ℓ : ℝ) / ε) * (Real.log (1 / εR) / Real.sqrt δ) with hB
  have hA_nonneg : 0 ≤ A := le_trans hsp0 hsp
  have hB_nonneg : 0 ≤ B := le_trans hr0 hr
  have hsum : statePerSample + reflPerSample ≤ A + B := by linarith
  have hstep : (ℓ : ℝ) * samples * (statePerSample + reflPerSample) ≤
      (ℓ : ℝ) * Real.log (4 * (ℓ : ℝ)) * (A + B) := by
    have hls : (ℓ : ℝ) * samples ≤ (ℓ : ℝ) * Real.log (4 * (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have hR0 : 0 ≤ (ℓ : ℝ) * Real.log (4 * (ℓ : ℝ)) := by
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
      linarith
    exact mul_le_mul hls hsum (by linarith [hsp0, hr0]) hR0
  have hfinal : (ℓ : ℝ) * Real.log (4 * (ℓ : ℝ)) * (A + B) =
      (ℓ : ℝ) ^ 2 / Real.sqrt δ * Real.log (4 * (ℓ : ℝ)) *
          (Real.log (32 * (ℓ : ℝ))) ^ 2 +
        (2 * (ℓ : ℝ) ^ 2 / ε) * Real.log (4 * (ℓ : ℝ)) * (Real.log (1 / εR) / Real.sqrt δ) := by
    rw [hA, hB]
    ring
  calc total ≤ (ℓ : ℝ) * samples * (statePerSample + reflPerSample) := htot
    _ ≤ (ℓ : ℝ) * Real.log (4 * (ℓ : ℝ)) * (A + B) := hstep
    _ = _ := hfinal

/-- Under the per-ratio accuracy and resource-budget hypotheses, the scaled product is
relatively accurate with probability at least three quarters and the total cost satisfies
the stated walk-cost bound. See [Wocjan et al., 2009][WocjanEtAl2009a]. -/
theorem theorem1_quantum_speedup
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℓ : ℕ) (hℓ : 0 < ℓ) {δ ε Z0 εR : ℝ} (hδ : 0 < δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hZ0 : 0 < Z0) (hεR : 0 < εR)
    (α : Fin ℓ → ℝ) (Q : Fin ℓ → Ω → ℝ) (hα : ∀ i, 0 < α i) (hQ : ∀ i, Measurable (Q i))
    (hacc : ∀ i,
      1 - 1 / (4 * (ℓ : ℝ)) ≤
        μ.real (relAccEvent (α i) (ε / (2 * (ℓ : ℝ))) (Q i)))
    {statePerSample reflPerSample samples total : ℝ}
    (hsp : statePerSample ≤ (ℓ : ℝ) / Real.sqrt δ * (Real.log (32 * (ℓ : ℝ))) ^ 2)
    (hr : reflPerSample ≤
      (2 * (ℓ : ℝ) / ε) * (Real.log (1 / εR) / Real.sqrt δ))
    (hs : samples ≤ Real.log (4 * (ℓ : ℝ)))
    (hs0 : 0 ≤ samples) (hsp0 : 0 ≤ statePerSample) (hr0 : 0 ≤ reflPerSample)
    (htot : total ≤ (ℓ : ℝ) * samples * (statePerSample + reflPerSample)) :
    3 / 4 ≤ μ.real (relAccEvent (Z0 * ∏ i, α i) ε (fun ω => Z0 * ∏ i, Q i ω)) ∧
      total ≤ (ℓ : ℝ) ^ 2 / Real.sqrt δ * Real.log (4 * (ℓ : ℝ)) *
          (Real.log (32 * (ℓ : ℝ))) ^ 2 +
        (2 * (ℓ : ℝ) ^ 2 / ε) * Real.log (4 * (ℓ : ℝ)) * (Real.log (1 / εR) / Real.sqrt δ) :=
  ⟨Qatlib.Papers.PartitionFunc08.MainResults.MainTheorem.theorem2_composite_scheme
    μ ℓ hℓ hε0 hε1 hZ0 α Q hα hQ hacc,
    theorem1_walk_cost hℓ hδ hε0 hεR hsp hr hs hs0 hsp0 hr0 htot⟩

end Qatlib.Papers.PartitionFunc08.MainResults.Speedup
