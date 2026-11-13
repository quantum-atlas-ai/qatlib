/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.LchsDefs

/-!
# Refined resource identities for LCHS

This module proves explicit schedule, source-loading, Taylor-order, sampling, and space
identities for the LCHS resource definitions. The linear-combination framework is described in
[AnLiuLin2023]; `clause32_endpoint`, `clause33_endpoint`, `tunableGoal_endpoint`, and
`optGoal_endpoint` collect the corresponding formal resource statements.

The interaction-picture results identify the two-factor branch evolution and the additional
inverse evolution present in `capPrintedThreeFactor`.

## Main statements

* `lchs33_tight_rate`: bounds the native Taylor order times a logarithm by a linear function of
  precision.
* `lchs34_printed_ne_two_factor`: distinguishes the three-factor expression when its extra
  factor is nontrivial.
* `optGoal_endpoint`: collects fixed-gate, register, quantum-space, and ledger identities.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid
open Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Qatlib.Concepts.RandCompile.ChannelBudget.LchsRefined

open Matrix
open Qatlib
open MeasureTheory
open Filter
open Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The total label count is `(M + 1) + (M + 1) * (Mt + 1)`, and the joint schedule has `(M + 1)
* (Mt + 1)` entries. -/
theorem lchs32_joint_schedule_size (M Mt : ℕ) :
    lchs2dLabelCount M Mt = (M + 1) + (M + 1) * (Mt + 1) ∧
      lchs32JointScheduleSize M Mt = (M + 1) * (Mt + 1) := by
  refine ⟨rfl, rfl⟩

/-- The named source-preparation count equals the two-dimensional select-preparation count. -/
theorem lchs32_source_preparation_count (M Mt : ℕ) :
    lchs32SourcePreparationCount M Mt = lchs2dSelectPrepareCount M Mt := rfl

/-- The number of source-grid indices equals the source-state count. -/
theorem lchs32_source_node_count (Mt : ℕ) :
    (Finset.univ : Finset (Fin (Mt + 1))).card = lchs2dSourceStateCount Mt :=
  lchsLoadedNode_count Mt

/-- Source preparations and source-input adjoints each equal `m + 1` times the number of joint
quadrature labels. -/
theorem lchs32_window_ledger_counts (M Mt m : ℕ) :
    (lchs2dWindowLedger M Mt m).sourcePrepare =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card ∧
      (lchs2dWindowLedger M Mt m).sourceInputAdjoint =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card := by
  have h := lchs2d_window_ledger_counts M Mt m
  exact ⟨h.1, h.2.1⟩

/-- Both select-preparation and select-input-adjoint counts equal the cardinality of the joint
label set. -/
theorem lchs32_source_label_count (M Mt : ℕ) :
    lchs2dSelectPrepareCount M Mt =
      (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card ∧
    lchs2dSelectInputAdjointCount M Mt =
      (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card :=
  lchs2d_source_label_count M Mt

/-- For `s ≤ t`, the two-dimensional coefficient mass factors as the kernel mass times one plus
the source mass. -/
theorem lchs32_coefficient_mass (b : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (hst : s ≤ t) :
    coefficientMass (lchs2dCoeff b s t K M Mt) =
      lchs2dKMass K M * (1 + lchs2dSourceMass b s t Mt) :=
  lchs2d_coefficient_mass b s t K M Mt hst

/-- Continuous positive semidefinite dissipative data, continuous Hermitian Hamiltonian data,
and unitary preparation matrices yield a unitary for every unified LCHS label. -/
theorem lchs32_unified_unitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K M Mt : ℕ)
    (B : Matrix I I ℂ) (P : Fin (Mt + 1) → Matrix I I ℂ)
    (hL : Continuous L) (hH : Continuous H)
    (hPSD : ∀ u, (L u).PosSemidef) (hHerm : ∀ u, (H u).IsHermitian)
    (hB : B ∈ unitaryGroup I ℂ) (hP : ∀ l, P l ∈ unitaryGroup I ℂ) :
    ∀ x, lchs2dUnitary L H s t K M Mt B P x ∈ unitaryGroup I ℂ := by
  exact lchs2d_unified_unitary L H s t K M Mt B P hL hH hPSD hHerm hB hP

/-- Each source label uses one preparation and one input adjoint, giving the stated
window-ledger counts. -/
theorem lchs32_label_wiring (M Mt m : ℕ) :
    lchs32LabelSourcePrepare = 1 ∧ lchs32LabelSourceAdjoint = 1 ∧
      (lchs2dWindowLedger M Mt m).sourcePrepare =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card *
          lchs32LabelSourcePrepare ∧
      (lchs2dWindowLedger M Mt m).sourceInputAdjoint =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card *
          lchs32LabelSourceAdjoint := by
  have h := lchs2d_window_ledger_counts M Mt m
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [h.1]
    simp [lchs32LabelSourcePrepare]
  · rw [h.2.1]
    simp [lchs32LabelSourceAdjoint]

/-- The number of label-success rounds equals `m`. -/
theorem lchs32_label_success_rounds (m : ℕ) : lchs32LabelSuccessRounds m = m := rfl

/-- The select-preparation count is the source-node reuse multiplicity times the `Mt + 1` loaded
source states. -/
theorem lchs32_source_node_loading (M Mt : ℕ) :
    lchs2dSelectPrepareCount M Mt = lchs32SourceNodeReuse M * lchs2dSourceStateCount Mt ∧
      lchs2dSourceStateCount Mt = Mt + 1 := by
  refine ⟨?_, rfl⟩
  simp [lchs2dSelectPrepareCount, lchs32SourceNodeReuse, lchs2dSourceStateCount]

/-- The order-`K` Hamiltonian Taylor circuit uses exactly `K` oracle queries. -/
theorem lchs33_query_count (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) :
    lchsHamTQueryCount (I := I) h j₀ τ K = K :=
  lchsHamTQueryCount_eq h j₀ τ K

/-- The order-`K` Hamiltonian Taylor circuit uses exactly `2 * K + 3` gates. -/
theorem lchs33_gate_count (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ) :
    lchsHamTGateCount (I := I) h j₀ τ K = 2 * K + 3 :=
  lchsHamTGateCount_eq h j₀ τ K

/-- The native Taylor order is the least order whose shifted factorial reaches `2^m`, and it is
at most `2 * m + 1`. -/
theorem lchs33_native_order_spec (m : ℕ) :
    2^m ≤ (lchs33HamTOrder m + 1).factorial ∧
      (∀ j < lchs33HamTOrder m, (j + 1).factorial < 2^m) ∧
      lchs33HamTOrder m ≤ 2 * m + 1 := by
  exact lchsHamTNativeOrder_spec m

/-- The Taylor word-label set fits in the number of binary states specified by
`lchs33AncillaBits`. -/
theorem lchs33_ancilla_bits_spec (K : ℕ) :
    (Finset.univ : Finset (TaylorWordLabel J K)).card ≤ 2 ^ (lchs33AncillaBits J K) := by
  exact taylorAncillaBits_spec K

/-- The phase-gate count equals the number of Taylor word labels. -/
theorem lchs33_phase_gate_count (K : ℕ) :
    lchs33PhaseGateCount J K = (Finset.univ : Finset (TaylorWordLabel J K)).card := by
  exact taylorPhaseGateCount_eq K

/-- Eventually, the native Taylor order times `Nat.log 2 m` is bounded by a positive constant
times `m`. -/
theorem lchs33_tight_rate :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      lchs33HamTOrder m * Nat.log 2 m ≤ C * m :=
  lchsHamT_tight_rate

/-- At the native Taylor order, the query count times `Nat.log 2 m` is eventually bounded by a
positive constant times `m`. -/
theorem lchs33_native_query_rate (h : J → ℝ) (j₀ : J) (τ : ℝ) :
    ∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      lchsHamTQueryCount (I := I) h j₀ τ (lchs33HamTOrder m) * Nat.log 2 m ≤ C * m := by
  exact lchsHamT_native_query_rate h j₀ τ

/-- Accepting at least half of all fair-bit strings gives acceptance probability at least one
half. -/
theorem lchs33_accept_prob_ge_half (m : ℕ) (accept : FairBitSample m → Bool)
    (hcard : (((Finset.univ : Finset (FairBitSample m)).filter
      (fun x => accept x = true)).card : ℝ) ≥ (2 ^ m : ℝ) / 2) :
    1 / 2 ≤ hamTAcceptProb m accept :=
  hamTAcceptProb_ge_half m accept hcard

/-- If at least half of the `2^m` strings are accepted, the fraction of length-`r` all-failure
sequences is at most `1 / 2^r`. -/
theorem lchs33_fail_fraction_le (m r a : ℕ) (ha : (a : ℝ) ≥ (2 ^ m : ℝ) / 2)
    (ha' : a ≤ 2 ^ m) :
    (hamTFailSeqCount m r a : ℝ) / (2 ^ m : ℝ) ^ r ≤ 1 / 2 ^ r :=
  hamTFailFraction_le m r a ha ha'

/-- The geometric sum of repetition tails with ratio one half is at most two. -/
theorem lchs33_expected_repetitions_le_two :
    tsum (fun r : ℕ => (1 / 2 : ℝ) ^ r) ≤ 2 :=
  hamTExpectedRepetitions_le_two

/-- The branch evolution factors into a fast-forward Hamiltonian evolution followed by the
time-ordered interaction-picture evolution. -/
theorem lchs34_branch_is_fastforward_then_interaction (L : Matrix I I ℂ)
    (H : ℝ → Matrix I I ℂ) (k t : ℝ) :
    capBranchUnitary L H k t =
      HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t := by
  exact capBranch_is_fastForward_then_interaction L H k t

/-- For Hermitian data, the printed three-factor expression equals the full time-ordered
evolution followed by an additional inverse fast-forward evolution. -/
theorem lchs34_printed_three_factor_extra (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) (hL : L.IsHermitian) (hH : Continuous H)
    (hHerm : ∀ u, (H u).IsHermitian) :
    capPrintedThreeFactor L H k t =
      orderedEvolution (fun u => Complex.I • (H u + k • L)) 0 t *
        HamiltonianEvolution (k • L) (-t) := by
  exact capPrinted_threeFactor_extra L H k t hL hH hHerm

/-- The printed three-factor expression differs from the two-factor branch when the extra
inverse fast-forward evolution is not the identity. -/
theorem lchs34_printed_ne_two_factor (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ)
    (k t : ℝ) (hL : L.IsHermitian) (hH : Continuous H)
    (hHerm : ∀ u, (H u).IsHermitian)
    (hextra : HamiltonianEvolution (k • L) (-t) ≠ 1) :
    capPrintedThreeFactor L H k t ≠
      HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t := by
  exact capPrinted_ne_twoFactor_of_extra_ne L H k t hL hH hHerm hextra

/-- The interaction-picture branch is unitary for Hermitian `L` and continuous Hermitian `H`. -/
theorem lchs34_branch_unitary (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ) (k t : ℝ)
    (hL : L.IsHermitian) (hH : Continuous H) (hHerm : ∀ u, (H u).IsHermitian) :
    capBranchUnitary L H k t ∈ unitaryGroup I ℂ := by
  exact capBranch_unitary L H k t hL hH hHerm

/-- One hybrid sample is assigned exactly one fast-forward application. -/
theorem lchs34_fast_forward_applications :
    lchs34FastForwardApplications = 1 := rfl

/-- The per-sample query budget is `2 * (m - 1)`, and the total query budget is `2 * (m - 1) *
n`. -/
theorem lchs34_hybrid_sample_queries (m n : ℕ) :
    lchsHybridSampleMaxQueries m = 2 * (m - 1) ∧
      lchs34HybridSampleQueries m n = 2 * (m - 1) * n :=
  ⟨rfl, rfl⟩

/-- The single-sample ledger records the source-state count, one fast-forward application, the
sample query budget, and one shot. -/
theorem lchs34_hybrid_sample_ledger (m Mt : ℕ) :
    (lchs34HybridSampleLedger m Mt).sourcePreparations = lchs2dSourceStateCount Mt ∧
      (lchs34HybridSampleLedger m Mt).fastForward = capFastForwardApplications ∧
      (lchs34HybridSampleLedger m Mt).queries = lchsHybridSampleMaxQueries m ∧
      (lchs34HybridSampleLedger m Mt).shots = 1 := by
  simp [lchs34HybridSampleLedger]

/-- The total ledger shares source preparations while assigning `n` fast-forward applications,
the total query budget, and `n` shots. -/
theorem lchs34_hybrid_total_ledger (m Mt n : ℕ) :
    (lchs34HybridTotalLedger m Mt n).sourcePreparations = lchs2dSourceStateCount Mt ∧
      (lchs34HybridTotalLedger m Mt n).fastForward = n * capFastForwardApplications ∧
      (lchs34HybridTotalLedger m Mt n).queries = lchsHybridTotalQueries m n ∧
      (lchs34HybridTotalLedger m Mt n).shots = n := by
  simp [lchs34HybridTotalLedger]

/-- The total hybrid query budget equals the number of shots times the per-sample query budget. -/
theorem lchs34_total_sampling_queries (m n : ℕ) :
    lchsHybridTotalQueries m n = n * lchsHybridSampleMaxQueries m := by
  simp [lchsHybridTotalQueries, lchsHybridSampleMaxQueries]
  ring

/-- The fixed-gate count is exactly `9 * k + 4`. -/
theorem lchs35_fixed_gate_count (k : ℕ) :
    lchs35FixedGateCount k = 9 * k + 4 := by
  exact lchsFixedGateCount_eq k

/-- The register width provides strictly more than `n` binary states. -/
theorem lchs35_register_bits_spec (n : ℕ) : n < 2 ^ (lchs35RegisterBits n) := by
  exact lchsRegisterBits_spec n

/-- The assigned classical widths provide strictly more than `N`, `m`, and `Mt + 1` binary
states, respectively. -/
theorem lchs35_classical_bits_spec (N m Mt : ℕ) :
    N < 2 ^ (lchs35RegisterBits N) ∧ m < 2 ^ (lchs35RegisterBits m) ∧
      Mt + 1 < 2 ^ (lchs35RegisterBits (Mt + 1)) := by
  exact lchsClassicalBits_spec N m Mt

/-- The quantum-space count equals the cardinality of the label and data-state product. -/
theorem lchs35_quantum_space_spec (N : ℕ) (dataStates : ℕ) :
    lchs35QuantumSpace N dataStates =
      (Finset.univ : Finset (Fin N × Fin dataStates)).card := by
  exact lchsQuantumSpace_spec N dataStates

/-- The theorem ledger records `N` labels, window `m`, `9 * m + 4` fixed gates, and `m` oracle
queries. -/
theorem lchs35_theorem_resources (N m Mt dataStates : ℕ) :
    (lchs35ResourceLedger N m Mt dataStates).labels = N ∧
      (lchs35ResourceLedger N m Mt dataStates).window = m ∧
      (lchs35ResourceLedger N m Mt dataStates).fixedGates = 9 * m + 4 ∧
      (lchs35ResourceLedger N m Mt dataStates).oracleQueries = m := by
  have h := lchsTheoremResources_spec N m Mt dataStates
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The first theorem ledger records `N` labels, window `m`, `9 * m + 4` fixed gates, and `m`
oracle queries. -/
theorem lchs35_th1_resources (N m dataStates : ℕ) :
    (lchsTh1Resources N m dataStates).labels = N ∧
      (lchsTh1Resources N m dataStates).window = m ∧
      (lchsTh1Resources N m dataStates).fixedGates = 9 * m + 4 ∧
      (lchsTh1Resources N m dataStates).oracleQueries = m := by
  have h := lchsTh1Resources_spec N m dataStates
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The second theorem ledger records the two-dimensional label count, window `m`, `9 * m + 4`
fixed gates, and `m` oracle queries. -/
theorem lchs35_th2_resources (M Mt m dataStates : ℕ) :
    (lchsTh2Resources M Mt m dataStates).labels = lchs2dLabelCount M Mt ∧
      (lchsTh2Resources M Mt m dataStates).window = m ∧
      (lchsTh2Resources M Mt m dataStates).fixedGates = 9 * m + 4 ∧
      (lchsTh2Resources M Mt m dataStates).oracleQueries = m := by
  have h := lchsTh2Resources_spec M Mt m dataStates
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The third theorem ledger records the two-dimensional label count, window `m`, `9 * m + 5`
fixed gates, and `m` oracle queries. -/
theorem lchs35_th3_resources (M Mt m dataStates : ℕ) :
    (lchsTh3Resources M Mt m dataStates).labels = lchs2dLabelCount M Mt ∧
      (lchsTh3Resources M Mt m dataStates).window = m ∧
      (lchsTh3Resources M Mt m dataStates).fixedGates = 9 * m + 4 + 1 ∧
      (lchsTh3Resources M Mt m dataStates).oracleQueries = m := by
  have h := lchsTh3Resources_spec M Mt m dataStates
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- Collects joint-label cardinalities, source-preparation identities, per-label wiring counts,
success-round counts, and source-node reuse identities. -/
theorem clause32_endpoint :
    (∀ M Mt : ℕ, lchs2dLabelCount M Mt = (M + 1) + (M + 1) * (Mt + 1) ∧
      lchs32JointScheduleSize M Mt = (M + 1) * (Mt + 1)) ∧
    (∀ M Mt : ℕ, lchs32SourcePreparationCount M Mt = lchs2dSelectPrepareCount M Mt) ∧
    (∀ Mt : ℕ, (Finset.univ : Finset (Fin (Mt + 1))).card = lchs2dSourceStateCount Mt) ∧
    (∀ M Mt : ℕ, lchs2dSelectPrepareCount M Mt =
      (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card) ∧
    (∀ M Mt m : ℕ, lchs32LabelSourcePrepare = 1 ∧ lchs32LabelSourceAdjoint = 1 ∧
      (lchs2dWindowLedger M Mt m).sourcePrepare =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card *
          lchs32LabelSourcePrepare ∧
      (lchs2dWindowLedger M Mt m).sourceInputAdjoint =
        (m + 1) * (Finset.univ : Finset (Fin (M + 1) × Fin (Mt + 1))).card *
          lchs32LabelSourceAdjoint) ∧
    (∀ m : ℕ, lchs32LabelSuccessRounds m = m) ∧
    (∀ M Mt : ℕ, lchs2dSelectPrepareCount M Mt =
        lchs32SourceNodeReuse M * lchs2dSourceStateCount Mt ∧
      lchs2dSourceStateCount Mt = Mt + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M Mt
    exact lchs32_joint_schedule_size M Mt
  · intro M Mt
    exact lchs32_source_preparation_count M Mt
  · intro Mt
    exact lchs32_source_node_count Mt
  · intro M Mt
    exact (lchs32_source_label_count M Mt).1
  · intro M Mt m
    exact lchs32_label_wiring M Mt m
  · intro m
    exact lchs32_label_success_rounds m
  · intro M Mt
    exact lchs32_source_node_loading M Mt

/-- Collects Taylor query and gate counts, native-order bounds, ancilla capacity, and the
geometric repetition bound. -/
theorem clause33_endpoint :
    (∀ (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ),
      lchsHamTQueryCount (I := I) h j₀ τ K = K) ∧
    (∀ (h : J → ℝ) (j₀ : J) (τ : ℝ) (K : ℕ),
      lchsHamTGateCount (I := I) h j₀ τ K = 2 * K + 3) ∧
    (∀ m : ℕ, lchs33HamTOrder m ≤ 2 * m + 1) ∧
    (∃ C m₀ : ℕ, 0 < C ∧ 2 ≤ m₀ ∧ ∀ m ≥ m₀,
      lchs33HamTOrder m * Nat.log 2 m ≤ C * m) ∧
    (∀ K : ℕ, (Finset.univ : Finset (TaylorWordLabel J K)).card
      ≤ 2 ^ (lchs33AncillaBits J K)) ∧
    (tsum (fun r : ℕ => (1 / 2 : ℝ) ^ r) ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h j₀ τ K
    exact lchs33_query_count h j₀ τ K
  · intro h j₀ τ K
    exact lchs33_gate_count h j₀ τ K
  · intro m
    exact (lchs33_native_order_spec m).2.2
  · exact lchs33_tight_rate
  · intro K
    exact lchs33_ancilla_bits_spec K
  · exact lchs33_expected_repetitions_le_two

/-- Collects the two-factor interaction-picture identity and the per-sample and total hybrid
resource ledgers. -/
theorem tunableGoal_endpoint :
    (∀ (L : Matrix I I ℂ) (H : ℝ → Matrix I I ℂ) (k t : ℝ),
      capBranchUnitary L H k t =
        HamiltonianEvolution (k • L) t *
          orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) H u) 0 t) ∧
    (lchs34FastForwardApplications = 1) ∧
    (∀ m : ℕ, lchsHybridSampleMaxQueries m = 2 * (m - 1)) ∧
    (∀ m Mt : ℕ,
      (lchs34HybridSampleLedger m Mt).sourcePreparations = lchs2dSourceStateCount Mt ∧
        (lchs34HybridSampleLedger m Mt).fastForward = capFastForwardApplications ∧
        (lchs34HybridSampleLedger m Mt).queries = lchsHybridSampleMaxQueries m ∧
        (lchs34HybridSampleLedger m Mt).shots = 1) ∧
    (∀ m Mt n : ℕ,
      (lchs34HybridTotalLedger m Mt n).sourcePreparations = lchs2dSourceStateCount Mt ∧
        (lchs34HybridTotalLedger m Mt n).fastForward = n * capFastForwardApplications ∧
        (lchs34HybridTotalLedger m Mt n).queries = lchsHybridTotalQueries m n ∧
        (lchs34HybridTotalLedger m Mt n).shots = n) ∧
    (∀ m n : ℕ, lchsHybridTotalQueries m n = n * lchsHybridSampleMaxQueries m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L H k t
    exact lchs34_branch_is_fastforward_then_interaction L H k t
  · exact lchs34_fast_forward_applications
  · intro m
    exact (lchs34_hybrid_sample_queries m 1).1
  · intro m Mt
    exact lchs34_hybrid_sample_ledger m Mt
  · intro m Mt n
    exact lchs34_hybrid_total_ledger m Mt n
  · intro m n
    exact lchs34_total_sampling_queries m n

/-- Collects the fixed-gate formula, classical register capacity, quantum-space cardinality, and
theorem resource counts. -/
theorem optGoal_endpoint :
    (∀ k : ℕ, lchs35FixedGateCount k = 9 * k + 4) ∧
    (∀ n : ℕ, n < 2 ^ (lchs35RegisterBits n)) ∧
    (∀ (N : ℕ) (dataStates : ℕ), lchs35QuantumSpace N dataStates =
      (Finset.univ : Finset (Fin N × Fin dataStates)).card) ∧
    (∀ (N m Mt dataStates : ℕ),
      (lchs35ResourceLedger N m Mt dataStates).labels = N ∧
        (lchs35ResourceLedger N m Mt dataStates).window = m ∧
        (lchs35ResourceLedger N m Mt dataStates).fixedGates = 9 * m + 4 ∧
        (lchs35ResourceLedger N m Mt dataStates).oracleQueries = m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact lchs35_fixed_gate_count k
  · intro n
    exact lchs35_register_bits_spec n
  · intro N dataStates
    exact lchs35_quantum_space_spec N dataStates
  · intro N m Mt dataStates
    exact lchs35_theorem_resources N m Mt dataStates
