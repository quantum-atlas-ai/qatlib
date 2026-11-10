/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GibbsMetropolis.RationalBath.ApproximateRationalGibbs
import Qatlib.Concepts.GibbsMetropolis.RationalBath.CountedRationalHeatBath
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

structure BoltzmannTaylorRecord where
  term : ℚ
  value : ℚ
  multiplies : ℕ
  divides : ℕ
  adds : ℕ
  subtracts : ℕ
  deriving Repr

def countedBoltzmannTaylor (E : ℚ) : ℕ → BoltzmannTaylorRecord
  | 0 => ⟨1,1,0,0,0,0⟩
  | j+1 =>
    let z := countedBoltzmannTaylor E j
    let t := z.term*(1-E)/(j+1:ℕ)
    ⟨t,z.value+t,z.multiplies+1,z.divides+1,z.adds+1,z.subtracts+1⟩

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

def countedDenominatorProduct : List ℕ → ℕ × ℕ
  | [] => (1,0)
  | d::ds => let z := countedDenominatorProduct ds; (d*z.1,z.2+1)

theorem countedDenominatorProduct_spec (ds : List ℕ) :
    (countedDenominatorProduct ds).1 = ds.prod ∧
    (countedDenominatorProduct ds).2 = ds.length := by
  induction ds with
  | nil => simp [countedDenominatorProduct]
  | cons d ds ih => simp [countedDenominatorProduct, ih]

def countedIntegerScale (D : ℕ) : List ℚ → List ℕ × ℕ × ℕ
  | [] => ([],0,0)
  | q::qs => let z := countedIntegerScale D qs
             (q.num.toNat*(D/q.den)::z.1,z.2.1+1,z.2.2+1)

theorem countedIntegerScale_spec (D : ℕ) (qs : List ℚ) :
    (countedIntegerScale D qs).1 = qs.map (fun q => q.num.toNat*(D/q.den)) ∧
    (countedIntegerScale D qs).2.1 = qs.length ∧
    (countedIntegerScale D qs).2.2 = qs.length := by
  induction qs with
  | nil => simp [countedIntegerScale]
  | cons q qs ih => simp [countedIntegerScale, ih]

def rationalEnergyPreparation {N : ℕ} (K : ℕ) (E : Fin N → ℚ) :
    List ℚ × (ℕ × ℕ) × (List ℕ × ℕ × ℕ) :=
  let qs := List.ofFn fun i => (countedBoltzmannTaylor (E i) K).value
  let ds := countedDenominatorProduct (qs.map Rat.den)
  (qs, ds, countedIntegerScale ds.1 qs)

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

theorem rational_energy_gibbs_same_record_quantum_cost :
    ∀ (N k : ℕ) (E : Fin N → ℚ) (c : Option (Fin N)) (i : Fin N),
      let leaf := observedLeaf (1:Operator N) (rationalHeatBathProgram c)
        (Fin.cast (rationalHeatBathProgram_spec c).2.symm i)
      leaf.queries=0 ∧ leaf.gates=1 ∧ leaf.measurements=1 := by
  intro N k E c i
  exact rationalHeatBath_leaf_cost c _

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

theorem rational_energy_gibbs_expected_classical_cost (N k : ℕ) (E : Fin N → ℚ)
    (hW : 0 < weightTotal (boltzmannIntegerWeights (k+3) E)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun (boltzmannIntegerWeights (k+3) E)
      (Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E))) (k+2))
      (fun z => (rejectionBits z.1:ℝ≥0∞)) ≤ (2*Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E)):ℕ) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalRejectionRun (boltzmannIntegerWeights (k+3) E)
      (Nat.clog 2 (weightTotal (boltzmannIntegerWeights (k+3) E))) (k+2))
      (fun z => (rejectionComparisons z.1:ℝ≥0∞)) ≤ (2*N:ℕ) :=
  rationalHeatBath_expected_classical_costs _ hW _

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
