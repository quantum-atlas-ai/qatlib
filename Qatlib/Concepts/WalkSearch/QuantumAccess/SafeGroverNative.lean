/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Mathlib.Tactic.Linarith
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
import Qatlib.Concepts.FairRandomBits.RationalReject.CountedWeightedDecoder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.QuantumAccess

theorem no_normalized_empty_search (ψ : QState (Fin 0)) : ¬ Normalized ψ := by
  simp [Normalized]

theorem safeGrover_native_empty_obstruction (sgs : Qatlib.Concepts.WalkSearch.Primitives.SafeGrover) :
    ¬ SafeGrover.NativeRealized sgs := by
  intro h
  obtain ⟨_circuit, start, _unitary, hnorm, _queries, _born⟩ :=
    h 0 (fun _ => false) 0 0
  exact no_normalized_empty_search (start (Classical.choice sgs.seedNe))
    (hnorm (Classical.choice sgs.seedNe))

theorem safeGroverNative_obstruction : ¬ SafeGroverNative := by
  intro h
  obtain ⟨sgs, _hexp, _hκ, hnative⟩ := h 3 (by decide)
  exact safeGrover_native_empty_obstruction sgs hnative

theorem input_dependent_zero_query_word {N : ℕ} (marked : Fin N → Bool)
    (hex : ∃ x, marked x = true) :
    ∃ (C : Circuit (Fin N)) (ψ : QState (Fin N)),
      IsUnitaryCircuit C ∧ Normalized ψ ∧ QueryCount C = 0 ∧ GateCount C = 0 ∧
      MeasureProb (Run (preparedMark (Finset.univ.filter (fun x => marked x = true)))
        C ψ) (Finset.univ.filter (fun x => marked x = true)) = 1 := by
  classical
  obtain ⟨x, hx⟩ := hex
  refine ⟨[], Qatlib.Foundations.PureStateMath.Ket x, isUnitaryCircuit_nil, normalized_ket x,
      rfl, rfl, ?_⟩
  simp [MeasureProb, bornProb_ket, hx]

theorem no_uniform_zero_query_word (C : Circuit (Fin 2))
    (hC : IsUnitaryCircuit C) (hQ : QueryCount C = 0)
    (ψ : QState (Fin 2)) (hψ : Normalized ψ) (ε : ℝ) (hε : ε < 1 / 2) :
    ¬ (1 - ε ≤ MeasureProb (Run (preparedMark ({0} : Finset (Fin 2))) C ψ) {0} ∧
      1 - ε ≤ MeasureProb (Run (preparedMark ({1} : Finset (Fin 2))) C ψ) {1}) := by
  intro h
  have heq₀ := run_eq_of_queryCount_eq_zero (preparedMark ({0} : Finset (Fin 2)))
    (1 : Matrix (Fin 2) (Fin 2) ℂ) C hQ ψ
  have heq₁ := run_eq_of_queryCount_eq_zero (preparedMark ({1} : Finset (Fin 2)))
    (1 : Matrix (Fin 2) (Fin 2) ℂ) C hQ ψ
  have hn := normalized_run (1 : Matrix (Fin 2) (Fin 2) ℂ) (by simp) C hC hψ
  change ∑ i : Fin 2, BornProb (Run (1 : Matrix (Fin 2) (Fin 2) ℂ) C ψ) i = 1 at hn
  rw [Fin.sum_univ_two] at hn
  rw [heq₀, heq₁] at h
  simp only [MeasureProb, Finset.sum_singleton] at h
  linarith [h.1, h.2]

theorem native_candidate_verification {N : ℕ} (x : Fin N) (marked : Fin N → Bool) :
    let C : Circuit (Fin N × Bool) := [Step.query]
    IsUnitaryCircuit C ∧ Normalized (Qatlib.Foundations.PureStateMath.Ket (x, false)) ∧ QueryCount C = 1 ∧
      Run (BitOracleOn marked) C (Qatlib.Foundations.PureStateMath.Ket (x, false)) = Qatlib.Foundations.PureStateMath.Ket (x, marked x) ∧
      MeasureProb (Run (BitOracleOn marked) C (Qatlib.Foundations.PureStateMath.Ket (x, false)))
        (Finset.univ.filter (fun p : Fin N × Bool => p.2 = true)) =
          if marked x = true then 1 else 0 := by
  classical
  refine ⟨by simp, normalized_ket _, rfl, ?_, ?_⟩
  · simpa using run_query_bitOracleOn_ket marked x false
  · rw [run_query_bitOracleOn_ket]
    simp [MeasureProb, bornProb_ket]

open scoped ENNReal BigOperators
open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def validatedGroverWord (A : Matrix I I ℂ) (j : I) (k : ℕ) : Circuit (I × Bool) :=
  [Step.gate (TensorGate 1 PauliX), Step.gate (TensorGate 1 Hadamard)] ++
    LiftCircuit (preparedAACircuit A j k) ++
    [Step.gate (TensorGate 1 Hadamard), Step.gate (TensorGate 1 PauliX), Step.query]

private theorem hadamard_minus : ApplyGate Hadamard Minus = Qatlib.Foundations.PureStateMath.Ket true := by
  rw [← applyGate_hadamard_ket_true, ← applyGate_mul, hadamard_mul_self, applyGate_one]

private theorem pauliX_true : ApplyGate PauliX (Qatlib.Foundations.PureStateMath.Ket true) = Qatlib.Foundations.PureStateMath.Ket false := by
  simpa using applyGate_pauliX_ket true

private theorem marked_phase (f : I → Bool) :
    preparedMark (Finset.univ.filter (fun x => f x = true)) = PhaseOracle f := by
  ext i j
  simp only [preparedMark, PhaseOracle, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Projector, Matrix.diagonal_apply, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hij : i = j
  · subst j
    cases f i <;> norm_num
  · simp [hij]

theorem validatedGroverWord_actual (A : Matrix I I ℂ) (j : I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → Bool) :
    IsUnitaryCircuit (validatedGroverWord A j k) ∧
    QueryCount (validatedGroverWord A j k) = k + 1 ∧
    GateCount (validatedGroverWord A j k) = 3 * k + 5 ∧
    Run (BitOracleOn f) (validatedGroverWord A j k) (Qatlib.Foundations.PureStateMath.Ket (j, false)) =
      ApplyGate (BitOracleOn f) (TensorState
        (Run (PhaseOracle f) (preparedAACircuit A j k) (Qatlib.Foundations.PureStateMath.Ket j)) (Qatlib.Foundations.PureStateMath.Ket false)) := by
  have hc := prepared_aa_actual_circuit A j (Finset.univ.filter (fun x => f x = true)) k hA
  have hx : TensorGate (1 : Matrix I I ℂ) PauliX ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) pauliX_unitary
  have hh : TensorGate (1 : Matrix I I ℂ) Hadamard ∈ Matrix.unitaryGroup (I × Bool) ℂ :=
    tensorGate_unitary (Submonoid.one_mem _) hadamard_unitary
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [validatedGroverWord, isUnitaryCircuit_append, isUnitaryCircuit_gate,
      isUnitaryCircuit_query, isUnitaryCircuit_nil]
    exact ⟨⟨⟨hx, hh, trivial⟩, hc.1.lift⟩, hh, hx, trivial⟩
  · simp [validatedGroverWord, queryCount_append, queryCount_liftCircuit, hc.2.1]
  · simp [validatedGroverWord, gateCount_append, gateCount_liftCircuit, hc.2.2.1]
  · rw [validatedGroverWord, run_append, run_append]
    simp only [run_gate, run_query, run_nil]
    rw [← tensorState_ket_ket, applyGate_tensorGate, applyGate_one, applyGate_pauliX_ket,
      Bool.not_false, applyGate_tensorGate, applyGate_one, applyGate_hadamard_ket_true,
      run_liftCircuit_bitOracleOn, applyGate_tensorGate, applyGate_one, hadamard_minus,
      applyGate_tensorGate, applyGate_one, pauliX_true]

theorem validated_candidate_born (ψ : QState I) (f : I → Bool) (x : I) (b : Bool) :
    BornProb (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false))) (x, b) =
      if b = f x then BornProb ψ x else 0 := by
  unfold BornProb
  rw [applyGate_bitOracleOn]
  cases hf : f x <;> cases b <;> simp [TensorState, BitFlip,
      Qatlib.Foundations.PureStateMath.Ket, hf]

def validatedGroverReadout (p : I × Bool) : Option I :=
  if p.2 then some p.1 else none

theorem validated_candidate_readout_mass (ψ : QState I) (f : I → Bool) (x : I) :
    MeasureProb (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false)))
      (Finset.univ.filter (fun p => validatedGroverReadout p = some x)) =
      if f x = true then BornProb ψ x else 0 := by
  have hs : (Finset.univ.filter (fun p : I × Bool => validatedGroverReadout p = some x)) =
      {(x, true)} := by
    ext p
    obtain ⟨y, b⟩ := p
    cases b <;> simp [validatedGroverReadout, Prod.ext_iff]
  rw [hs, MeasureProb, Finset.sum_singleton, validated_candidate_born]
  cases f x <;> simp

theorem validated_candidate_accept_mass (ψ : QState I) (f : I → Bool) :
    MeasureProb (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false)))
      (Finset.univ.filter (fun p : I × Bool => p.2 = true)) =
    MeasureProb ψ (Finset.univ.filter (fun x : I => f x = true)) := by
  simp only [MeasureProb, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_bool]
  simp [validated_candidate_born]

theorem validatedGroverWord_born_success (A : Matrix I I ℂ) (j : I) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (f : I → Bool) :
    MeasureProb (Run (BitOracleOn f) (validatedGroverWord A j k) (Qatlib.Foundations.PureStateMath.Ket (j, false)))
      (Finset.univ.filter (fun p : I × Bool => p.2 = true)) =
    MeasureProb (Run (preparedMark (Finset.univ.filter (fun x => f x = true)))
      (preparedAACircuit A j k) (Qatlib.Foundations.PureStateMath.Ket j)) (Finset.univ.filter (fun x => f x = true)) := by
  rw [(validatedGroverWord_actual A j k hA f).2.2.2, validated_candidate_accept_mass,
    marked_phase]

theorem native_validation_output_law (ψ : QState I) (hψ : Normalized ψ) (f : I → Bool) :
    (bornDistribution (ApplyGate (BitOracleOn f) (TensorState ψ (Qatlib.Foundations.PureStateMath.Ket false)))
      (normalized_applyGate (bitOracleOn_unitary f)
        (normalized_tensorState hψ (normalized_ket false)))).map validatedGroverReadout =
    (bornDistribution ψ hψ).map (fun x => if f x then some x else none) := by
  ext o
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
    bornDistribution_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp only [validated_candidate_born]
  cases f x <;> simp [validatedGroverReadout]

def sourceSearchCap (N : ℕ) : ℕ := 4 * (Nat.sqrt N + 1)
def sourceSearchWarmup (N : ℕ) : ℕ := 4 * Nat.clog 2 (sourceSearchCap N)
def sourceSearchTail (N floor c : ℕ) : ℕ := 4 * c * Nat.clog 2 (max N floor + 1)

private theorem public_window_reaches_cap (M : ℕ) (hM : 0 < M) :
    geometricWindow M (4 * Nat.clog 2 M) = M := by
  let a := Nat.clog 2 M
  have hp : 2 ^ a ≤ 6 ^ (4 * a) / 5 ^ (4 * a) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num : 2 * 5 ^ 4 ≤ 6 ^ 4) a
  have hm := Nat.le_pow_clog (by norm_num : 1 < 2) M
  have hc : M ≤ (6 ^ (4 * a) + 5 ^ (4 * a) - 1) / 5 ^ (4 * a) := by
    refine (hm.trans hp).trans (Nat.div_le_div_right ?_)
    have hh : 0 < 5 ^ (4 * a) := by positivity
    omega
  unfold geometricWindow
  change max 1 (min M ((6 ^ (4 * a) + 5 ^ (4 * a) - 1) / 5 ^ (4 * a))) = M
  rw [min_eq_left hc, max_eq_right (by omega)]

theorem sourceSearchCap_uniform_angle (N t : ℕ) (ht : 0 < t) (htN : t < N) :
    let θ := Real.arcsin (Real.sqrt ((t : ℝ) / N))
    0 < θ ∧ θ < Real.pi / 2 ∧ (Real.sin θ) ^ 2 = (t : ℝ) / N ∧
      1 ≤ (sourceSearchCap N : ℝ) * Real.sin (2 * θ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have htR : (t : ℝ) < N := by exact_mod_cast htN
  have ha0 : 0 < (t : ℝ) / N := div_pos ht0 hn
  have ha1 : (t : ℝ) / N < 1 := (div_lt_one hn).mpr htR
  have hsq := Real.sq_sqrt ha0.le
  have hs0 : 0 < Real.sqrt ((t : ℝ) / N) := Real.sqrt_pos.mpr ha0
  have hs1 : Real.sqrt ((t : ℝ) / N) < 1 :=
      (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using ha1)
  have hθ0 : 0 < Real.arcsin (Real.sqrt ((t : ℝ) / N)) := Real.arcsin_pos.mpr hs0
  have hθ1 : Real.arcsin (Real.sqrt ((t : ℝ) / N)) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr hs1
  have hsin := Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((t : ℝ) / N)]) hs1.le
  have hcos := Real.cos_arcsin (Real.sqrt ((t : ℝ) / N))
  rw [hsq] at hcos
  have hcosSq : (Real.cos (Real.arcsin (Real.sqrt ((t : ℝ) / N)))) ^ 2 =
      1 - (t : ℝ) / N := by rw [hcos, Real.sq_sqrt (by linarith)]
  have hs2 : (Real.sin (2 * Real.arcsin (Real.sqrt ((t : ℝ) / N)))) ^ 2 =
      4 * ((t : ℝ) / N) * (1 - (t : ℝ) / N) := by
    rw [Real.sin_two_mul, mul_pow, mul_pow, hsin, hsq, hcosSq]
    ring
  have hi : (N : ℝ) - 1 ≤ (t : ℝ) * ((N : ℝ) - t) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have htN1 : (t : ℝ) + 1 ≤ N := by exact_mod_cast htN
    nlinarith [mul_nonneg (by linarith : 0 ≤ (t : ℝ) - 1)
      (by linarith : 0 ≤ (N : ℝ) - t - 1)]
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hprod : (N : ℝ) * (Real.sin (2 * Real.arcsin (Real.sqrt ((t : ℝ) / N)))) ^ 2 ≥ 2 := by
    rw [hs2]
    field_simp
    nlinarith
  have hnat := Nat.lt_succ_sqrt' N
  have hnr : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by exact_mod_cast hnat
  have hc : (sourceSearchCap N : ℝ) ^ 2 > 16 * N := by
    unfold sourceSearchCap
    push_cast
    nlinarith
  have hspos : 0 < Real.sin (2 * Real.arcsin (Real.sqrt ((t : ℝ) / N))) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hmul := mul_lt_mul_of_pos_right hc (sq_pos_of_pos hspos)
  have hbase : 32 ≤ (sourceSearchCap N : ℝ) ^ 2 *
      (Real.sin (2 * Real.arcsin (Real.sqrt ((t : ℝ) / N)))) ^ 2 := by nlinarith
  refine ⟨hθ0, hθ1, by rw [hsin]; exact hsq, ?_⟩
  have hc0 : 0 < (sourceSearchCap N : ℝ) := by unfold sourceSearchCap; positivity
  nlinarith [mul_pos hc0 hspos]

private theorem source_tail_inverse_power (K c : ℕ) (hK : 0 < K) :
    (25 / 32 : ℝ) ^ (4 * c * Nat.clog 2 K) ≤ (K : ℝ) ^ (-(c : ℝ)) := by
  have h4 : (25 / 32 : ℝ) ^ 4 ≤ (1 / 2 : ℝ) := by norm_num
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (25 / 32) ^ 4) h4 (c * Nat.clog 2 K)
  have hnat := Nat.le_pow_clog (by norm_num : 1 < 2) K
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have he : (1 / 2 : ℝ) ^ Nat.clog 2 K ≤ (K : ℝ)⁻¹ := by
    rw [one_div, inv_pow]
    apply inv_anti₀ hk
    exact_mod_cast hnat
  calc
    _ = ((25 / 32 : ℝ) ^ 4) ^ (c * Nat.clog 2 K) := by rw [← pow_mul]; congr 1; ring
    _ ≤ (1 / 2 : ℝ) ^ (c * Nat.clog 2 K) := hpow
    _ = ((1 / 2 : ℝ) ^ Nat.clog 2 K) ^ c := by rw [← pow_mul]; congr 1; ring
    _ ≤ ((K : ℝ)⁻¹) ^ c := pow_le_pow_left₀ (by positivity) he c
    _ = _ := by rw [Real.rpow_neg hk.le, Real.rpow_natCast, inv_pow]

noncomputable def sourceSafeGroverLaw (N : ℕ) (f : Fin N → Bool) (floor c : ℕ) :
    PMF (CappedSearchTrace (Fin N)) :=
  if hN : 0 < N then
    searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN) ⟨0, hN⟩
      (Finset.univ.filter (fun x => f x = true)) f
      (geometricSearchSchedule (sourceSearchCap N)
        (sourceSearchWarmup N + sourceSearchTail N floor c))
  else PMF.pure emptySearchTrace

theorem sourceSafeGroverLaw_empty (f : Fin 0 → Bool) (floor c : ℕ) :
    sourceSafeGroverLaw 0 f floor c = PMF.pure emptySearchTrace := by
  simp [sourceSafeGroverLaw]

theorem sourceSafeGroverLaw_confidence (N : ℕ) (f : Fin N → Bool) (floor c : ℕ)
    (hc : 0 < c) (hex : ∃ x, f x = true) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (sourceSafeGroverLaw N f floor c) (fun tr => tr.result = none)).toReal ≤
      ((max N floor + 1 : ℕ) : ℝ) ^ (-(c : ℝ)) := by
  obtain ⟨x, hx⟩ := hex
  have hN : 0 < N := Nat.pos_of_ne_zero (fun hz => by subst N; exact Fin.elim0 x)
  let S := Finset.univ.filter (fun y : Fin N => f y = true)
  let M := sourceSearchCap N
  let J := sourceSearchWarmup N
  let R := sourceSearchTail N floor c
  let P := searchForSchedule (QFTMatrix N) (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S f
    (geometricSearchSchedule M (J + R))
  rw [sourceSafeGroverLaw, dif_pos hN]
  change (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event P (fun tr => tr.result = none)).toReal ≤ _
  have hvalid : ∀ y : Fin N, f y = true ↔ y ∈ S := by intro y; simp [S]
  have hm0 : 0 < S.card := Finset.card_pos.mpr ⟨x, by simp [S, hx]⟩
  have hmN : S.card ≤ N := by
    have hh := Finset.card_le_card (Finset.subset_univ S)
    simpa using hh
  by_cases hall : S.card = N
  · have hmass : MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) S = 1 := by
      rw [prepared_qft_mark_mass, hall]
      exact div_self (by exact_mod_cast hN.ne')
    have hR : 0 < R := by
      have hk : 1 < max N floor + 1 := by omega
      have hl := Nat.clog_pos (by decide : 1 < 2) hk
      dsimp [R, sourceSearchTail]
      positivity
    have hsome := (geometric_search_zero_one_endpoints_and_path_caps (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S f M (J + R) hvalid).2.1 hmass (by omega)
    change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event P
        (fun tr => tr.result.isSome) = 1 at hsome
    have hpart := event_compl P (fun tr => tr.result = none)
    have he : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event P (fun tr => ¬ tr.result = none) =
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event P (fun tr => tr.result.isSome) := by
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
      intro tr
      cases tr.result <;> simp
    rw [he, hsome] at hpart
    have hz : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event P (fun tr => tr.result = none) = 0 :=
      WithTop.add_right_cancel (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
        (show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event P (fun tr => tr.result = none) + 1 = (0 : ℝ≥0∞) + 1 by
          simpa using hpart)
    rw [hz]
    positivity
  · have hmLt : S.card < N := by omega
    let θ := Real.arcsin (Real.sqrt ((S.card : ℝ) / N))
    have ha := sourceSearchCap_uniform_angle N S.card hm0 hmLt
    change 0 < θ ∧ θ < Real.pi / 2 ∧ (Real.sin θ) ^ 2 = (S.card : ℝ) / N ∧
      1 ≤ (M : ℝ) * Real.sin (2 * θ) at ha
    have hmass : MeasureProb (preparedAAState (QFTMatrix N) ⟨0,hN⟩) S =
        (Real.sin θ) ^ 2 := (prepared_qft_mark_mass N hN S).trans ha.2.2.1.symm
    have hwin : 1 ≤ (geometricWindow M J : ℝ) * Real.sin (2 * θ) := by
      have hM0 : 0 < M := by dsimp [M, sourceSearchCap]; positivity
      change 1 ≤ (geometricWindow M (4 * Nat.clog 2 M) : ℝ) * Real.sin (2 * θ)
      rw [public_window_reaches_cap M hM0]
      exact ha.2.2.2
    have hr := geometric_search_actual_cutoff_failure_probability (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S f M (J + R) J θ hvalid
      ha.1 ha.2.1 hmass hwin
    simp only [Nat.add_sub_cancel_left] at hr
    exact hr.trans (source_tail_inverse_power (max N floor + 1) c (by omega))

theorem sourceSafeGroverLaw_sound (N : ℕ) (f : Fin N → Bool) (floor c : ℕ) :
    ∀ tr ∈ (sourceSafeGroverLaw N f floor c).support,
      ∀ x, tr.result = some x → f x = true := by
  intro tr htr x hx
  by_cases hN : 0 < N
  · have hs := geometric_search_actual_support_soundness_and_metadata (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N)
      (Finset.univ.filter (fun y => f y = true)) f (sourceSearchCap N)
      (sourceSearchWarmup N + sourceSearchTail N floor c) (by intro y; simp)
    rw [sourceSafeGroverLaw, dif_pos hN] at htr
    simpa using (hs tr htr).1 x hx
  · have hz : N = 0 := by omega
    subst N
    exact Fin.elim0 x

private theorem source_schedule_size_bounds (N floor c : ℕ) :
    sourceSearchWarmup N + sourceSearchTail N floor c ≤
      8 * (c + 1) * (Nat.log 2 (max N floor + 1) + 2) ∧
    sourceSearchCap N + 1 ≤ 5 * (Nat.sqrt (max N floor + 1) + 1) := by
  let K := max N floor + 1
  have hclog : Nat.clog 2 K ≤ Nat.log 2 K + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by decide : 1 < 2) K).le
  have hM : sourceSearchCap N ≤ 4 * K := by
    unfold sourceSearchCap
    have hs := Nat.sqrt_le_self N
    dsimp [K]
    omega
  have hclogM : Nat.clog 2 (sourceSearchCap N) ≤ Nat.clog 2 K + 2 := by
    apply Nat.clog_le_of_le_pow
    calc
      _ ≤ 4 * K := hM
      _ ≤ 4 * 2 ^ Nat.clog 2 K := Nat.mul_le_mul_left 4 (Nat.le_pow_clog (by decide) K)
      _ = 2 ^ (Nat.clog 2 K + 2) := by rw [pow_add]; ring
  have hMlog : Nat.clog 2 (sourceSearchCap N) ≤ Nat.log 2 K + 3 := by omega
  have hsqrt := Nat.sqrt_le_sqrt (show N ≤ K by dsimp [K]; omega)
  constructor
  · unfold sourceSearchWarmup sourceSearchTail
    change 4 * Nat.clog 2 (sourceSearchCap N) + 4 * c * Nat.clog 2 K ≤ _
    have hh := Nat.mul_le_mul_left (4 * c) hclog
    nlinarith
  · unfold sourceSearchCap
    nlinarith

private theorem source_schedule_sum_cap (N T : ℕ) :
    (geometricSearchSchedule (sourceSearchCap N) T).sum ≤ T * sourceSearchCap N := by
  rw [geometricSearchSchedule, List.sum_ofFn]
  calc
    _ ≤ ∑ _i : Fin T, sourceSearchCap N := Finset.sum_le_sum (fun i _ =>
      (geometric_search_actual_integer_schedule (sourceSearchCap N) T i.val).2.2.2.2
        (by unfold sourceSearchCap; positivity))
    _ = _ := by simp

theorem sourceSafeGroverLaw_actual_resources (N : ℕ) (f : Fin N → Bool) (floor c check : ℕ) :
    ∀ tr ∈ (sourceSafeGroverLaw N f floor c).support,
      (check + 1) * (tr.phaseQueries + tr.validationQueries) ≤
        40 * (c + 1) * (Nat.log 2 (max N floor + 1) + 2) *
          (check + 1) * (Nat.sqrt (max N floor + 1) + 1) ∧
      tr.macroGates + 4 * tr.validationQueries ≤ 5 * (tr.phaseQueries + tr.validationQueries) := by
  intro tr htr
  by_cases hN : 0 < N
  · let S := Finset.univ.filter (fun y : Fin N => f y = true)
    let T := sourceSearchWarmup N + sourceSearchTail N floor c
    have hvalid : ∀ y : Fin N, f y = true ↔ y ∈ S := by intro y; simp [S]
    rw [sourceSafeGroverLaw, dif_pos hN] at htr
    have hpaths := (geometric_search_zero_one_endpoints_and_path_caps (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S f (sourceSearchCap N) T hvalid).2.2 tr htr
    have hmeta := geometric_search_actual_support_soundness_and_metadata (QFTMatrix N)
      (qftMatrix_unitary hN) (⟨0,hN⟩ : Fin N) S f (sourceSearchCap N) T hvalid tr htr
    have hphase := hpaths.1.trans (source_schedule_sum_cap N T)
    have hv := hpaths.2.1
    have hsz := source_schedule_size_bounds N floor c
    have hsum : tr.phaseQueries + tr.validationQueries ≤ T * (sourceSearchCap N + 1) := by
      nlinarith
    refine ⟨?_, ?_⟩
    · have hm := Nat.mul_le_mul hsz.1 hsz.2
      have hq := Nat.mul_le_mul_left (check + 1) (hsum.trans hm)
      convert hq using 1
      ring
    · rw [hmeta.2.2.2.2.2]
      omega
  · rw [sourceSafeGroverLaw, dif_neg hN, PMF.mem_support_pure_iff] at htr
    subst tr
    simp [emptySearchTrace]

theorem sourceSafeGroverLaw_reject (N : ℕ) (f : Fin N → Bool) (floor c : ℕ)
    (hempty : ∀ x, f x = false) :
    ∀ tr ∈ (sourceSafeGroverLaw N f floor c).support, tr.result = none := by
  intro tr htr
  cases hr : tr.result with
  | none => rfl
  | some x =>
    have hs := sourceSafeGroverLaw_sound N f floor c tr htr x hr
    rw [hempty] at hs
    contradiction

def groverSignedValue {N : ℕ} (f : Fin N → Bool) (x : Fin N) : ℤ := if f x then -1 else 1

def groverIntegerAmplitude (N : ℕ) (f : Fin N → Bool) : ℕ → Fin N → ℤ
  | 0 => fun _ => 1
  | k + 1 => fun x => 2 * (∑ y, groverSignedValue f y * groverIntegerAmplitude N f k y) -
      (N : ℤ) * groverSignedValue f x * groverIntegerAmplitude N f k x

private theorem groverPhase_eq {N : ℕ} (f : Fin N → Bool) :
    preparedMark (Finset.univ.filter (fun x => f x = true)) = PhaseOracle f := by
  ext i j
  simp only [preparedMark, PhaseOracle, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Projector, Matrix.diagonal_apply, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hij : i = j
  · subst j; cases f i <;> norm_num
  · simp [hij]

private theorem uniform_reflection_action (N : ℕ) (hN : 0 < N) (ψ : QState (Fin N))
    (x : Fin N) :
    ApplyGate (ReflectionAbout (outerProduct (preparedAAState (QFTMatrix N) ⟨0,hN⟩))) ψ x =
      2 / (N : ℂ) * (∑ y, ψ y) - ψ x := by
  rw [preparedAAState, qftMatrix_ket_zero]
  simp only [ApplyGate, ReflectionAbout, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, outerProduct_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_inv, Complex.conj_ofReal,
    ← Finset.mul_sum]
  have hs : (Real.sqrt (N : ℝ) : ℂ) ^ 2 = (N : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg N)
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hN : (0 : ℝ) < N)).ne'
  field_simp [hr, hn]
  rw [← hs]
  ring

theorem groverIntegerAmplitude_actual (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) (k : ℕ)
    (x : Fin N) :
    Run (PhaseOracle f) (preparedAACircuit (QFTMatrix N) ⟨0,hN⟩ k) (Qatlib.Foundations.PureStateMath.Ket ⟨0,hN⟩) x =
      (groverIntegerAmplitude N f k x : ℂ) /
        ((N : ℂ) ^ k * (Real.sqrt (N : ℝ) : ℂ)) := by
  let S := Finset.univ.filter (fun y : Fin N => f y = true)
  let A := preparedAAIterate (QFTMatrix N) ⟨0,hN⟩ S
  have hrun (j : ℕ) := (prepared_aa_actual_circuit (QFTMatrix N) ⟨0,hN⟩ S j
    (qftMatrix_unitary hN)).2.2.2
  rw [← groverPhase_eq f, hrun]
  change ApplyGate (A ^ k) (preparedAAState (QFTMatrix N) ⟨0,hN⟩) x = _
  have hA : A = ReflectionAbout (outerProduct (preparedAAState (QFTMatrix N) ⟨0,hN⟩)) *
      PhaseOracle f := by
    dsimp [A]
    rw [preparedAAIterate,
      (prepared_aa_reflection_and_access (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN)).2.2.1,
      groverPhase_eq f]
  have hstep (φ : QState (Fin N)) (y : Fin N) : ApplyGate A φ y =
      2 / (N : ℂ) * (∑ z, (if f z then (-1 : ℂ) else 1) * φ z) -
        (if f y then (-1 : ℂ) else 1) * φ y := by
    rw [hA, applyGate_mul, uniform_reflection_action]
    simp_rw [applyGate_phaseOracle]
  induction k generalizing x with
  | zero => simp [preparedAAState, qftMatrix_ket_zero, groverIntegerAmplitude]
  | succ k ih =>
    rw [pow_succ', applyGate_mul, hstep]
    simp_rw [ih]
    have hcast (y : Fin N) : (if f y then (-1 : ℂ) else 1) = (groverSignedValue f y : ℂ) := by
      cases hf : f y <;> simp [groverSignedValue, hf]
    simp_rw [hcast]
    rw [groverIntegerAmplitude]
    push_cast
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hr : (Real.sqrt (N : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hN : (0 : ℝ) < N)).ne'
    field_simp
    ring

def groverIntegerTicketWeight (N : ℕ) (f : Fin N → Bool) (k : ℕ) (x : Fin N) : ℕ :=
  (groverIntegerAmplitude N f k x).natAbs ^ 2

theorem groverIntegerWeight_born (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) (k : ℕ)
    (x : Fin N) :
    BornProb (Run (PhaseOracle f) (preparedAACircuit (QFTMatrix N) ⟨0,hN⟩ k)
      (Qatlib.Foundations.PureStateMath.Ket ⟨0,hN⟩)) x = (groverIntegerTicketWeight N f k x : ℝ) /
        ((N ^ (2 * k + 1) : ℕ) : ℝ) := by
  rw [BornProb, groverIntegerAmplitude_actual, ← Complex.normSq_eq_norm_sq, Complex.normSq_div, map_mul,
    map_pow, Complex.normSq_intCast, Complex.normSq_natCast, Complex.normSq_ofReal]
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have ha : ((groverIntegerAmplitude N f k x).natAbs : ℝ) ^ 2 =
      (groverIntegerAmplitude N f k x : ℝ) ^ 2 := by
    have hh := congrArg (fun z : ℤ => (z : ℝ))
      (Int.natCast_natAbs (groverIntegerAmplitude N f k x))
    have he : ((groverIntegerAmplitude N f k x).natAbs : ℝ) =
        |(groverIntegerAmplitude N f k x : ℝ)| := by
      simpa only [Int.cast_natCast, Int.cast_abs] using hh
    rw [he]
    exact sq_abs _
  unfold groverIntegerTicketWeight
  push_cast
  rw [ha]
  simp only [← pow_two, hs, ← pow_mul, pow_add, pow_one]

theorem groverIntegerWeight_total (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) (k : ℕ) :
    ∑ x, groverIntegerTicketWeight N f k x = N ^ (2 * k + 1) := by
  have hc := (prepared_aa_actual_circuit (QFTMatrix N) (⟨0,hN⟩ : Fin N)
    (Finset.univ.filter (fun x => f x = true)) k (qftMatrix_unitary hN)).1
  have hn := hc.normalized_run (phaseOracle_unitary f) (normalized_ket (⟨0,hN⟩ : Fin N))
  change (∑ x, BornProb _ x) = 1 at hn
  simp_rw [groverIntegerWeight_born N hN f k] at hn
  rw [← Finset.sum_div] at hn
  have hd : ((N ^ (2 * k + 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have hh := (div_eq_one_iff_eq hd).mp hn
  exact_mod_cast hh

def nativeGroverTicket (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) (k : ℕ)
    (u : Fin (N ^ (2 * k + 1))) : Fin N :=
  weightTicket (groverIntegerTicketWeight N f k)
    (by change 0 < ∑ x, groverIntegerTicketWeight N f k x
        rw [groverIntegerWeight_total N hN f k]
        positivity)
    (Fin.cast (groverIntegerWeight_total N hN f k).symm u)

theorem nativeGroverTicket_fiber (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) (k : ℕ)
    (x : Fin N) :
    (Finset.univ.filter (fun u : Fin (N ^ (2 * k + 1)) => nativeGroverTicket N hN f k u = x)).card =
      groverIntegerTicketWeight N f k x := by
  let w := groverIntegerTicketWeight N f k
  have hW : 0 < weightTotal w := by
    change 0 < ∑ y, groverIntegerTicketWeight N f k y
    rw [groverIntegerWeight_total N hN f k]
    positivity
  have he : weightTotal w = N ^ (2 * k + 1) := groverIntegerWeight_total N hN f k
  have hi (u : Fin (weightTotal w)) : weightTicket w hW u = x ↔
      (weightDecodeCounted w u.val).1 = some x := by
    rw [(weighted_decoder_intervals_and_actual_cost N w).2.2.2.2 hW u]
    simp
  have hcard : (Finset.univ.filter (fun u : Fin (weightTotal w) => weightTicket w hW u = x)).card = w x := by
    simp_rw [hi]
    exact weightDecodeCounted_fibers w x
  let e := finCongr he
  have ht : (Finset.univ.filter (fun u : Fin (N ^ (2 * k + 1)) => nativeGroverTicket N hN f k u = x)).card =
      (Finset.univ.filter (fun u : Fin (weightTotal w) => weightTicket w hW u = x)).card := by
    apply Finset.card_nbij' (fun u => e.symm u) (fun u => e u)
    · intro u hu
      simpa [nativeGroverTicket, e, w] using hu
    · intro u hu
      simpa [nativeGroverTicket, e, w] using hu
    · intro u _
      exact e.apply_symm_apply u
    · intro u _
      exact e.symm_apply_apply u
  exact ht.trans hcard

theorem nativeGroverTicket_born_coupling (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) (k : ℕ)
    (x : Fin N) :
    ((Finset.univ.filter (fun u : Fin (N ^ (2 * k + 1)) =>
      nativeGroverTicket N hN f k u = x)).card : ℝ) / (N ^ (2 * k + 1) : ℕ) =
    BornProb (Run (PhaseOracle f) (preparedAACircuit (QFTMatrix N) ⟨0,hN⟩ k)
      (Qatlib.Foundations.PureStateMath.Ket ⟨0,hN⟩)) x := by
  rw [nativeGroverTicket_fiber, groverIntegerWeight_born]

end Qatlib.Concepts.WalkSearch.QuantumAccess
