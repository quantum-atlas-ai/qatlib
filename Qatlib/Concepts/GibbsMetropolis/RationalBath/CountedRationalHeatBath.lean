/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalHeatBathChannel

/-!
# Resource ledgers for rational heat baths

`rationalHeatBathCoins` and `rationalHeatBathComparisons` total the classical costs recorded by
a finite sampling history. The observed heat-bath program has zero queries, one gate, and one
measurement on every leaf.

The module also identifies positive integer weights as Gibbs weights for logarithmic energies
and bounds expected classical sampling costs. See [TemmeEtAl2011] for background.

## Main statements

* `rational_heat_bath_actual_leaf_and_classical_ledgers`: The quantum leaf costs are fixed,
  while any supported history of `m` cutoff-`R` samples uses at most `m * Nat.clog 2
  (weightTotal w) * R` bits and `m * N * R` comparisons.
* `rationalHeatBath_expected_classical_costs`: With positive total weight, the cutoff sampler
  has expected bit cost at most twice the ceiling binary logarithm of the total weight and
  expected comparison cost at most `2 * N`.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath
open Matrix
open scoped Classical BigOperators ComplexOrder ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false

/-- A rejection-sampler configuration, containing either an accepted label or pending costs,
together with its execution cost. -/
abbrev HeatBathSamplerRecord (N : ℕ) := ((Fin N × ℕ × ℕ) ⊕ (ℕ × ℕ)) × ℕ

/-- The sum of the recorded random-bit costs over a heat-bath sampling history. -/
def rationalHeatBathCoins {N : ℕ} (w : Fin N → ℕ) (R m : ℕ)
    (hist : Fin m → HeatBathSamplerRecord N) : ℕ := ∑ k, rejectionBits (hist k).1

/-- The sum of the recorded comparison costs over a heat-bath sampling history. -/
def rationalHeatBathComparisons {N : ℕ} (w : Fin N → ℕ) (R m : ℕ)
    (hist : Fin m → HeatBathSamplerRecord N) : ℕ := ∑ k, rejectionComparisons (hist k).1

/-- Strictly positive integer weights define the Gibbs density for energies `-Real.log (w j)` at
inverse temperature one. -/
theorem rational_heat_bath_gibbs_integer_weight_identification :
    ∀ (N : ℕ) (hN : 0 < N) (w : Fin N → ℕ) (hW : 0 < weightTotal w),
      (∀ j, 0 < w j) → rationalHeatBathDensity w hW =
        diagonalGibbsDensity N hN (fun j => -Real.log (w j : ℝ)) 1 := by
  intro N hN w hW hw
  have hexp (j : Fin N) : Real.exp (-(1:ℝ) * -Real.log (w j : ℝ)) = (w j : ℝ) := by
    rw [neg_one_mul, neg_neg, Real.exp_log (by exact_mod_cast hw j)]
  have hpart : diagonalGibbsPartition N (fun j => -Real.log (w j : ℝ)) 1 =
      (weightTotal w : ℝ) := by
    simp only [diagonalGibbsPartition, hexp]
    simp [weightTotal]
  simp only [rationalHeatBathDensity, diagonalGibbsDensity, diagonalGibbsDist, hexp, hpart]

/-- Every observed heat-bath leaf uses zero oracle queries, one gate, and one measurement. -/
theorem rationalHeatBath_leaf_cost {N : ℕ} (c : Option (Fin N))
    (l : Fin (observedLeafCount (rationalHeatBathProgram c))) :
    (observedLeaf 1 (rationalHeatBathProgram c) l).queries = 0 ∧
    (observedLeaf 1 (rationalHeatBathProgram c) l).gates = 1 ∧
    (observedLeaf 1 (rationalHeatBathProgram c) l).measurements = 1 := by
  have hmem : observedLeaf 1 (rationalHeatBathProgram c) l ∈
      observedKrausLeaves 1 (rationalHeatBathProgram c) := List.get_mem _ _
  rw [rationalHeatBathLeaves] at hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  rw [← hi]
  exact ⟨rfl, rfl, rfl⟩

/-- The quantum leaf costs are fixed, while any supported history of `m` cutoff-`R` samples uses
at most `m * Nat.clog 2 (weightTotal w) * R` bits and `m * N * R` comparisons. -/
theorem rational_heat_bath_actual_leaf_and_classical_ledgers :
    ∀ (N R m : ℕ) (w : Fin N → ℕ) (hW : 0 < weightTotal w)
      (c : Option (Fin N)) (l : Fin (observedLeafCount (rationalHeatBathProgram c))),
      (observedLeaf 1 (rationalHeatBathProgram c) l).queries = 0 ∧
      (observedLeaf 1 (rationalHeatBathProgram c) l).gates = 1 ∧
      (observedLeaf 1 (rationalHeatBathProgram c) l).measurements = 1 ∧
      ∀ hist : Fin m → HeatBathSamplerRecord N,
        (∀ k, hist k ∈ (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R).support) →
        rationalHeatBathCoins w R m hist = (∑ k, rejectionBits (hist k).1) ∧
        rationalHeatBathComparisons w R m hist = (∑ k, rejectionComparisons (hist k).1) ∧
        rationalHeatBathCoins w R m hist ≤ m * Nat.clog 2 (weightTotal w) * R ∧
        rationalHeatBathComparisons w R m hist ≤ m * N * R := by
  intro N R m w hW c l
  have hc := rationalHeatBath_leaf_cost c l
  refine ⟨hc.1, hc.2.1, hc.2.2, ?_⟩
  intro hist hh
  have hb := (rational_effective_truncation_consumer N w R hW).2.2.2.2.2.2
  refine ⟨rfl, rfl, ?_, ?_⟩
  · calc _ ≤ ∑ _ : Fin m, Nat.clog 2 (weightTotal w) * R :=
        Finset.sum_le_sum (fun k _ => (hb (hist k) (hh k)).1)
      _ = _ := by simp [Nat.mul_assoc]
  · calc _ ≤ ∑ _ : Fin m, N * R :=
        Finset.sum_le_sum (fun k _ => (hb (hist k) (hh k)).2)
      _ = _ := by simp [Nat.mul_assoc]

/-- With positive total weight, the cutoff sampler has expected bit cost at most twice the
ceiling binary logarithm of the total weight and expected comparison cost at most `2 * N`. -/
theorem rationalHeatBath_expected_classical_costs {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
      (fun z => (rejectionBits z.1 : ℝ≥0∞)) ≤ (2 * Nat.clog 2 (weightTotal w) : ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
      (fun z => (rejectionComparisons z.1 : ℝ≥0∞)) ≤ (2*N : ℕ) := by
  have h := rational_effective_truncation_consumer N w R hW
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Qatlib.Concepts.GibbsMetropolis.RationalBath
