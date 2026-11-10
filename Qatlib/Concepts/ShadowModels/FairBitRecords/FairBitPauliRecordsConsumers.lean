/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.FairBitRecords.FairBitPauliRecords
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.ShadowVariance

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.FairBitRecords
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

theorem fair_record_event_half_l1 {X : Type} [Fintype X] [DecidableEq X]
    (p q : FinDist X) (S : Finset X) :
    |(∑ x ∈ S, p.prob x) - (∑ x ∈ S, q.prob x)| ≤
      (∑ x, |p.prob x - q.prob x|) / 2 := by
  rw [← Finset.sum_sub_distrib]
  have hz : (∑ x, (p.prob x - q.prob x)) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_one, q.sum_one, sub_self]
  have hsplit := S.sum_add_sum_compl (fun x => p.prob x - q.prob x)
  have hcomp : (∑ x ∈ Sᶜ, (p.prob x - q.prob x)) =
      -(∑ x ∈ S, (p.prob x - q.prob x)) := by linarith
  have ha := Finset.abs_sum_le_sum_abs (fun x => p.prob x - q.prob x) S
  have hb := Finset.abs_sum_le_sum_abs (fun x => p.prob x - q.prob x) Sᶜ
  rw [hcomp, abs_neg] at hb
  have hsplitabs := S.sum_add_sum_compl (fun x => |p.prob x - q.prob x|)
  linarith

theorem fair_pauli_fresh_statistics_transport_consumer :
    ∀ (n R B : ℕ) (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
      (S : Finset (Fin B → Fin n → Fin 3 × Bool)),
      |(∑ ω ∈ S, ∏ j, fairPauliRecordProb n R ρ (ω j)) -
        (∑ ω ∈ S, ∏ j, (tensorPauliLaw n ρ hρ).prob (ω j))| ≤
          B * n * (4 : ℝ) ^ (-(R : ℤ)) := by
  intro n R B ρ hρ S
  let p := fairPauliRecordLaw n R ρ hρ
  let q := tensorPauliLaw n ρ hρ
  have hd := (fair_pauli_same_quantum_record_law n R ρ hρ).2.2
  have hp := native_product_l1 B (fun _ => p) (fun _ => q)
  have hb : (∑ ω : Fin B → Fin n → Fin 3 × Bool,
      |(∏ j, p.prob (ω j)) - (∏ j, q.prob (ω j))|) ≤
      (B : ℝ) * (2 * n * (4 : ℝ) ^ (-(R : ℤ))) := by
    apply hp.trans
    have hh := Finset.sum_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin B))) => hd)
    simpa [p, q, fairPauliRecordLaw] using! hh
  change |(∑ ω ∈ S, (independentSampleLaw (fun _ : Fin B => p)).prob ω) -
    (∑ ω ∈ S, (independentSampleLaw (fun _ : Fin B => q)).prob ω)| ≤ _
  apply (fair_record_event_half_l1 _ _ S).trans
  exact (div_le_div_of_nonneg_right hb (by norm_num)).trans_eq (by ring)

def fairPauliNativeMedian {n q : ℕ} (w : Fin q → Fin n → Option (Fin 3))
    (c : Fin q → ℚ) (m r : ℕ)
    (ω : Fin ((2 * r + 1) * m) → Fin n → Fin 3 × Bool) : ℚ × ℕ × ℕ :=
  localSparseMedianCounted w c m r (fun j i => ω (finProdFinEquiv (j, i)))

theorem fair_pauli_native_median_same_record_transport
    (n q m r R : ℕ) (ρ : Operator (2 ^ n)) (hρ : IsDensityOperator ρ)
    (w : Fin q → Fin n → Option (Fin 3)) (c : Fin q → ℚ) (μ ε : ℝ) :
    (∀ ω : Fin ((2 * r + 1) * m) → Fin n → Fin 3 × Bool,
      ((fairPauliNativeMedian w c m r ω).1 : ℝ) =
        sortedBlockMedian r (fun j => (m : ℝ)⁻¹ *
          ∑ i, sparsePauliValue w c (ω (finProdFinEquiv (j, i)))) ∧
      (fairPauliNativeMedian w c m r ω).2.1 = (2 * r + 1) * m * q * (n + 1) ∧
      (fairPauliNativeMedian w c m r ω).2.2 ≤ 10000 * (2 * r + 1)) ∧
    let S := Finset.univ.filter (fun ω : Fin ((2 * r + 1) * m) → Fin n → Fin 3 × Bool =>
      |((fairPauliNativeMedian w c m r ω).1 : ℝ) - μ| ≤ ε)
    |(∑ ω ∈ S, ∏ j, fairPauliRecordProb n R ρ (ω j)) -
      (∑ ω ∈ S, ∏ j, (tensorPauliLaw n ρ hρ).prob (ω j))| ≤
        ((2 * r + 1) * m) * n * (4 : ℝ) ^ (-(R : ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro ω
    exact local_pauli_native_means_median_and_work n q m r w c
      (fun j i => ω (finProdFinEquiv (j, i)))
  · (try dsimp only)
    let S := Finset.univ.filter
      (fun ω : Fin ((2 * r + 1) * m) → Fin n → Fin 3 × Bool =>
        |((fairPauliNativeMedian w c m r ω).1 : ℝ) - μ| ≤ ε)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using!
      fair_pauli_fresh_statistics_transport_consumer n R ((2 * r + 1) * m) ρ hρ S

def fairPauliDecodedRecords {B n R : ℕ} (tapes : Fin B → Fin n → Fin R → Fin 4)
    (outcomes : Fin B → Reg n) : Fin B → Fin n → Fin 3 × Bool :=
  fun j i => ((fairPauliAxis (List.ofFn (tapes j i))).1, outcomes j i)

theorem fair_pauli_same_record_acquisition_ledger (B n R : ℕ)
    (tapes : Fin B → Fin n → Fin R → Fin 4) (outcomes : Fin B → Reg n)
    (ρ : Operator (2 ^ n)) :
    tensorPauliFreshResourceCounts n 1 B
      (fun j _ => fairPauliDecodedRecords tapes outcomes j) = (B, 2 * n * B, n * B, 0) ∧
    fairPauliPrefixBits tapes =
      2 * ∑ j, ∑ i, (fairPauliAxis (List.ofFn (tapes j i))).2 ∧
    fairPauliPrefixBits tapes ≤ 2 * n * B * R ∧
    (∀ j, instrumentProb (fairPauliInstrument n R) ρ (fairPauliDecodedRecords tapes outcomes j) =
      fairPauliRecordProb n R ρ (fairPauliDecodedRecords tapes outcomes j)) := by
  refine ⟨?_, rfl, fairPauliPrefixBits_le B n R tapes, ?_⟩
  · simpa only [mul_one] using! tensorPauliFreshResourceCounts_spec n 1 B
      (fun j _ => fairPauliDecodedRecords tapes outcomes j)
  · intro j
    exact fairPauliInstrument_same_record n R ρ _

end Qatlib.Concepts.ShadowModels.FairBitRecords
