/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
import Qatlib.Concepts.GibbsMetropolis.RationalBath.CountedRationalHeatBath

/-!
# Counted consumers of rational-energy Gibbs preparation

This module implements rational Taylor evaluation and denominator clearing through
`countedBoltzmannTaylor`, `countedDenominatorProduct`, and `countedIntegerScale`. The
specification `rationalEnergyPreparation_spec` identifies the resulting integer Boltzmann
weights and records exact rational arithmetic counts. The thermal-state preparation setting has
background in [PoulinWocjan2009].

The consumer theorems combine quantum leaf counts with worst-case and expected classical
rejection costs. For the two-level energies `0` and `1`, they compute the degree-three density
and certify reference-system approximation and actual-run costs at precision indices `0` and
`2`.

## Main statements

* `countedBoltzmannTaylor_spec`: identifies the Taylor term, partial sum, and four operation
  counts.
* `rationalEnergyPreparation_spec`: identifies denominator clearing, integer weights, and
  preparation counts.
* `rational_energy_gibbs_expected_classical_cost`: bounds expected random-bit and comparison
  counts.
* `rational_energy_half_gap_actual_run`: combines reference-system error, leaf counts, and
  supported classical histories.

## References

* [Poulin and Wocjan, 2009][PoulinWocjan2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.SamplingBackend.GibbsBackend
open Matrix
open scoped Classical BigOperators ComplexOrder ENNReal
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A rational Taylor-evaluation record containing the current term, accumulated value, and
counts of multiplications, divisions, additions, and subtractions. -/
structure BoltzmannTaylorRecord where
  term : ℚ
  value : ℚ
  multiplies : ℕ
  divides : ℕ
  adds : ℕ
  subtracts : ℕ
  deriving Repr

/-- Evaluates the degree-`K` Taylor sum in `1 - E` by updating the term as `term * (1 - E) / (j
+ 1)`. Each update increments all four arithmetic-operation counters once. -/
def countedBoltzmannTaylor (E : ℚ) : ℕ → BoltzmannTaylorRecord
  | 0 => ⟨1,1,0,0,0,0⟩
  | j+1 =>
    let z := countedBoltzmannTaylor E j
    let t := z.term*(1-E)/(j+1:ℕ)
    ⟨t,z.value+t,z.multiplies+1,z.divides+1,z.adds+1,z.subtracts+1⟩

/-- After `K` updates, the term is `(1 - E)^K / K!`, the accumulated value is
`rationalBoltzmannTaylor K E`, and each of the four arithmetic-operation counters equals
`K`. -/
theorem countedBoltzmannTaylor_spec (E : ℚ) (K : ℕ) :
    (countedBoltzmannTaylor E K).term = (1-E)^K/(K.factorial:ℚ) ∧
    (countedBoltzmannTaylor E K).value = rationalBoltzmannTaylor K E ∧
    (countedBoltzmannTaylor E K).multiplies = K ∧
    (countedBoltzmannTaylor E K).divides = K ∧
    (countedBoltzmannTaylor E K).adds = K ∧
    (countedBoltzmannTaylor E K).subtracts = K := by
  induction K with
  | zero => simp [countedBoltzmannTaylor, rationalBoltzmannTaylor]
  | succ K ih =>
    have ht : (countedBoltzmannTaylor E (K+1)).term = (1-E)^(K+1)/((K+1).factorial:ℚ) := by
      simp only [countedBoltzmannTaylor, ih.1, pow_succ, Nat.factorial_succ, Nat.cast_mul]
      field_simp
    refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩
    · change (countedBoltzmannTaylor E K).value + (countedBoltzmannTaylor E (K+1)).term = _
      rw [ih.2.1, ht]
      simp only [rationalBoltzmannTaylor, Finset.sum_range_succ]
    · simp [countedBoltzmannTaylor, ih]
    · simp [countedBoltzmannTaylor, ih]
    · simp [countedBoltzmannTaylor, ih]
    · simp [countedBoltzmannTaylor, ih]

/-- Multiplies a list of natural denominators, returning the product together with a counter
incremented once per list entry. -/
def countedDenominatorProduct : List ℕ → ℕ × ℕ
  | [] => (1,0)
  | d::ds => let z := countedDenominatorProduct ds; (d*z.1,z.2+1)

/-- The counted denominator routine returns `ds.prod` and a counter equal to `ds.length`. -/
theorem countedDenominatorProduct_spec (ds : List ℕ) :
    (countedDenominatorProduct ds).1 = ds.prod ∧
    (countedDenominatorProduct ds).2 = ds.length := by
  induction ds with
  | nil => simp [countedDenominatorProduct]
  | cons d ds ih => simp [countedDenominatorProduct, ih]

/-- Maps each rational `q` to `q.num.toNat * (D / q.den)`, returning the resulting natural
weights and two counters incremented once per entry. -/
def countedIntegerScale (D : ℕ) : List ℚ → List ℕ × ℕ × ℕ
  | [] => ([],0,0)
  | q::qs => let z := countedIntegerScale D qs
             (q.num.toNat*(D/q.den)::z.1,z.2.1+1,z.2.2+1)

/-- The counted scaling routine returns the list obtained by mapping `q.num.toNat * (D / q.den)`
over `qs`, with both operation counters equal to the list length. -/
theorem countedIntegerScale_spec (D : ℕ) (qs : List ℚ) :
    (countedIntegerScale D qs).1 = qs.map (fun q => q.num.toNat*(D/q.den)) ∧
    (countedIntegerScale D qs).2.1 = qs.length ∧
    (countedIntegerScale D qs).2.2 = qs.length := by
  induction qs with
  | nil => simp [countedIntegerScale]
  | cons q qs ih => simp [countedIntegerScale, ih]

/-- Computes counted Taylor values for the finite energy list, forms the counted product of
their denominators, and scales the values to natural weights using that product. The
returned tuple retains the rational values and the denominator-product and scaling counters. -/
def rationalEnergyPreparation {N : ℕ} (K : ℕ) (E : Fin N → ℚ) :
    List ℚ × (ℕ × ℕ) × (List ℕ × ℕ × ℕ) :=
  let qs := List.ofFn fun i => (countedBoltzmannTaylor (E i) K).value
  let ds := countedDenominatorProduct (qs.map Rat.den)
  (qs, ds, countedIntegerScale ds.1 qs)

/-- The preparation returns the Taylor values, `boltzmannCommonDenominator`, and
`boltzmannIntegerWeights`, with denominator-product and scaling counts equal to `N`. Each
Taylor operation totals `N * K`, and counted weight summation returns the total weight with
counter `N`. -/
theorem rationalEnergyPreparation_spec {N : ℕ} (K : ℕ) (E : Fin N → ℚ) :
    (rationalEnergyPreparation K E).1 = List.ofFn (fun i => rationalBoltzmannTaylor K (E i)) ∧
    (rationalEnergyPreparation K E).2.1 = (boltzmannCommonDenominator K E, N) ∧
    (rationalEnergyPreparation K E).2.2 = (List.ofFn (boltzmannIntegerWeights K E), N, N) ∧
    (∑ i, (countedBoltzmannTaylor (E i) K).multiplies) = N*K ∧
    (∑ i, (countedBoltzmannTaylor (E i) K).divides) = N*K ∧
    (∑ i, (countedBoltzmannTaylor (E i) K).adds) = N*K ∧
    (∑ i, (countedBoltzmannTaylor (E i) K).subtracts) = N*K ∧
    weightTotalCounted (boltzmannIntegerWeights K E) = (weightTotal (boltzmannIntegerWeights K E),N) := by
  have hv (i : Fin N) := (countedBoltzmannTaylor_spec (E i) K).2.1
  have hd : countedDenominatorProduct ((List.ofFn fun i => rationalBoltzmannTaylor K (E i)).map Rat.den) =
      (boltzmannCommonDenominator K E,N) := by
    apply Prod.ext
    · rw [(countedDenominatorProduct_spec _).1, List.map_ofFn, List.prod_ofFn]
      rfl
    · rw [(countedDenominatorProduct_spec _).2]
      simp
  have hw : countedIntegerScale (boltzmannCommonDenominator K E)
      (List.ofFn fun i => rationalBoltzmannTaylor K (E i)) =
      (List.ofFn (boltzmannIntegerWeights K E),N,N) := by
    apply Prod.ext
    · rw [(countedIntegerScale_spec _ _).1, List.map_ofFn]
      rfl
    · apply Prod.ext
      · rw [(countedIntegerScale_spec _ _).2.1]; simp
      · rw [(countedIntegerScale_spec _ _).2.2]; simp
  simp only [rationalEnergyPreparation, hv, hd, hw]
  refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, weightTotalCounted_ofFn _⟩
  · simp [(countedBoltzmannTaylor_spec _ _).2.2.1]
  · simp [(countedBoltzmannTaylor_spec _ _).2.2.2.1]
  · simp [(countedBoltzmannTaylor_spec _ _).2.2.2.2.1]
  · simp [(countedBoltzmannTaylor_spec _ _).2.2.2.2.2]

/-- Every specified observed leaf of the rational heat-bath program has zero queries, one gate,
and one measurement, independently of the energy and precision parameters. -/
theorem rational_energy_gibbs_same_record_quantum_cost :
    ∀ (N k : ℕ) (E : Fin N → ℚ) (c : Option (Fin N)) (i : Fin N),
      let leaf := observedLeaf (1:Operator N) (rationalHeatBathProgram c)
        (Fin.cast (rationalHeatBathProgram_spec c).2.symm i)
      leaf.queries=0 ∧ leaf.gates=1 ∧ leaf.measurements=1 := by
  intro N k E c i
  exact rationalHeatBath_leaf_cost c _

/-- For a supported one-step rejection history using degree-`k + 3` Boltzmann weights and `k +
2` attempts, random-bit use is at most `(k + 2) * clog 2 W` and comparisons are at most `N *
(k + 2)`, where `W` is the positive total weight. -/
theorem rational_energy_gibbs_raw_classical_cost (N k : ℕ) (E : Fin N → ℚ)
    (hW : 0 < weightTotal (boltzmannIntegerWeights (k+3) E))
    (hist : Fin 1 → HeatBathSamplerRecord N)
    (hh : ∀ j, hist j ∈ (rationalRejectionRun (boltzmannIntegerWeights (k+3) E)
      (Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E))) (k+2)).support) :
    rationalHeatBathCoins (boltzmannIntegerWeights (k+3) E) (k+2) 1 hist ≤
      (k+2)*Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E)) ∧
    rationalHeatBathComparisons (boltzmannIntegerWeights (k+3) E) (k+2) 1 hist ≤ N*(k+2) := by
  have h :=
      (rational_effective_truncation_consumer N (boltzmannIntegerWeights (k+3) E) (k+2) hW).2.2.2.2.2.2
  constructor
  · simpa [rationalHeatBathCoins, Fin.sum_univ_one, Nat.mul_comm] using (h (hist 0) (hh 0)).1
  · simpa [rationalHeatBathComparisons, Fin.sum_univ_one] using (h (hist 0) (hh 0)).2

/-- For positive total weight `W`, the degree-`k + 3` rejection run with `k + 2` attempts has
expected random-bit use at most `2 * clog 2 W` and expected comparison count at most `2 *
N`. -/
theorem rational_energy_gibbs_expected_classical_cost (N k : ℕ) (E : Fin N → ℚ)
    (hW : 0 < weightTotal (boltzmannIntegerWeights (k+3) E)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun (boltzmannIntegerWeights (k+3) E)
      (Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E))) (k+2))
      (fun z => (rejectionBits z.1:ℝ≥0∞)) ≤ (2*Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E)):ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun (boltzmannIntegerWeights (k+3) E)
      (Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E))) (k+2))
      (fun z => (rejectionComparisons z.1:ℝ≥0∞)) ≤ (2*N:ℕ) :=
  rationalHeatBath_expected_classical_costs _ hW _

/-- For energies `0` and `1`, the degree-three Taylor weights are `8/3` and `1`, and the
associated rational heat-bath density has diagonal entries `8/11` and `3/11`. -/
theorem rational_energy_half_gap_explicit_consumer :
    let E : Fin 2 → ℚ := fun i => if i=0 then 0 else 1
    rationalBoltzmannTaylor 3 (E 0)=8/3 ∧ rationalBoltzmannTaylor 3 (E 1)=1 ∧
    ∀ hW : 0 < weightTotal (boltzmannIntegerWeights 3 E),
      (rationalHeatBathDensity (boltzmannIntegerWeights 3 E) hW) 0 0=8/11 ∧
      (rationalHeatBathDensity (boltzmannIntegerWeights 3 E) hW) 1 1=3/11 := by
  dsimp
  norm_num [rationalBoltzmannTaylor, Finset.sum_range_succ]
  intro hW
  constructor <;> norm_num [rationalHeatBathDensity, boltzmannIntegerWeights,
    boltzmannCommonDenominator, rationalBoltzmannTaylor, Finset.sum_range_succ,
    Fin.prod_univ_two, weightTotal, Fin.sum_univ_two, Int.toNat]

/-- For energies `0` and `1` and `k` in `{0, 2}`, the one-step heat bath using degree-`k + 3`
weights and `k + 2` attempts approximates the Gibbs reset on every positive semidefinite
reference input within `2^(-k)` times its trace norm. The specified observed leaf also has
one gate. -/
theorem rational_energy_half_gap_reference_consumers (r : ℕ)
    (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (hX : X.PosSemidef) :
    let E : Fin 2 → ℚ := fun i => if i=0 then 0 else 1
    ∀ k ∈ ({0,2}:Finset ℕ), ∀ hW : 0 < weightTotal (boltzmannIntegerWeights (k+3) E),
      Matrix.traceNorm (tensorLeft (rationalHeatBathPower (boltzmannIntegerWeights (k+3) E)
        hW (k+2) 1).map X - TensorGate (rationalEnergyGibbsDensity E) (Matrix.traceLeft X)) ≤
        (1/2:ℝ)^k*Matrix.traceNorm X ∧
      (observedLeaf (1:Operator 2) (rationalHeatBathProgram (some 0))
        (Fin.cast (rationalHeatBathProgram_spec (some 0)).2.symm 0)).gates=1 := by
  intro E k hk hW
  refine ⟨rational_energy_gibbs_actual_reference_precision 2 k r E hW X (by omega) ?_ hX,
    (rational_energy_gibbs_same_record_quantum_cost 2 k E (some 0) 0).2.1⟩
  intro i
  dsimp [E]
  split_ifs <;> norm_num

/-- For energies `0` and `1`, `k` in `{0, 2}`, and a supported one-step history, combines
reference-system error at most `2^(-k)` times the input trace norm with leaf counts of zero
queries, one gate, and one measurement. Random bits are bounded by `(k + 2) * clog 2 W` and
comparisons by `2 * (k + 2)` for the corresponding total weight `W`. -/
theorem rational_energy_half_gap_actual_run (r : ℕ)
    (X : Matrix (Fin 2 × Fin r) (Fin 2 × Fin r) ℂ) (hX : X.PosSemidef) :
    let E : Fin 2 → ℚ := fun i => if i=0 then 0 else 1
    ∀ k ∈ ({0,2}:Finset ℕ), ∀ hW : 0 < weightTotal (boltzmannIntegerWeights (k+3) E),
    ∀ hist : Fin 1 → HeatBathSamplerRecord 2,
      (∀ j, hist j ∈ (rationalRejectionRun (boltzmannIntegerWeights (k+3) E)
        (Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E))) (k+2)).support) →
      Matrix.traceNorm (tensorLeft (rationalHeatBathPower (boltzmannIntegerWeights (k+3) E)
        hW (k+2) 1).map X - TensorGate (rationalEnergyGibbsDensity E) (Matrix.traceLeft X)) ≤
        (1/2:ℝ)^k*Matrix.traceNorm X ∧
      (let leaf := observedLeaf (1:Operator 2) (rationalHeatBathProgram (some 0))
        (Fin.cast (rationalHeatBathProgram_spec (some 0)).2.symm 0);
        leaf.queries=0 ∧ leaf.gates=1 ∧ leaf.measurements=1) ∧
      rationalHeatBathCoins (boltzmannIntegerWeights (k+3) E) (k+2) 1 hist ≤
        (k+2)*Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E)) ∧
      rationalHeatBathComparisons (boltzmannIntegerWeights (k+3) E) (k+2) 1 hist ≤ 2*(k+2) := by
  intro E k hk hW hist hh
  exact ⟨(rational_energy_half_gap_reference_consumers r X hX k hk hW).1,
    rational_energy_gibbs_same_record_quantum_cost 2 k E (some 0) 0,
    rational_energy_gibbs_raw_classical_cost 2 k E hW hist hh⟩

end Qatlib.Concepts.SamplingBackend.GibbsBackend
