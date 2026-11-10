/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StructuralEstimateInterface
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.LiveVtProgramAux
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

noncomputable section
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators
set_option warningAsError false
variable {C : Type} [Fintype C] [DecidableEq C]

theorem data_sharp_median_failure (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (A : Matrix (VtSpace C) (VtSpace C) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (VtSpace C) ℂ) (j₀ : VtSpace C) (S : Finset (VtSpace C)) :
    (aeLaw M A j₀ S hA hM).probEvent (fun ω : Fin (2*r+1) → Fin M =>
      dataEstimateRadius (MeasureProb (preparedAAState A j₀) S) M <
        |vtMedianEstimate M r ω-MeasureProb (preparedAAState A j₀) S|) ≤ (8/9 : ℝ)^r := by
  let p := aeLaw M A j₀ S hA hM
  let a := MeasureProb (preparedAAState A j₀) S
  have hrad : 0 ≤ dataEstimateRadius a M := by unfold dataEstimateRadius; positivity
  have hgood := (prepared_ae_bhmt_error_and_endpoints M hM A j₀ S hA).1
  have hpi : 2/3 ≤ 8/Real.pi^2 := by
    apply (le_div_iff₀ (pow_pos Real.pi_pos 2)).mpr
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hc :=
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement p
      (fun z => |aeEstimate M z-a| ≤ dataEstimateRadius a M)
  simp only [not_le] at hc
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => dataEstimateRadius a M < |aeEstimate M z-a|) ≤ 1/3 := by
    change 8/Real.pi^2 ≤ Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p
        (fun z => |aeEstimate M z-a| ≤ dataEstimateRadius a M) at hgood
    linarith
  exact Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure p
      (aeEstimate M) r a (dataEstimateRadius a M) hrad hb

theorem dataFreshKernel_eq_probOf (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history) (word : List DataVtStep)
    (hw : DataVtWordLegal stages word) (ω : Fin (2*r+1) → Fin M) :
    dataFreshKernel M hM r stages history j₀ word ω =
      (aeLaw M (dataVtWordMatrix stages history j₀ word) j₀ (liveSet C)
        (dataVtWordMatrix_unitary stages history j₀ hl word hw) hM).probOf ω :=
  (vt_fresh_ae_born_law M hM _ (dataVtWordMatrix_unitary stages history j₀ hl word hw)
    j₀ (liveSet C) (2*r+1) ω).symm

theorem dataFreshKernel_sum_one (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history) (word : List DataVtStep)
    (hw : DataVtWordLegal stages word) :
    ∑ ω, dataFreshKernel M hM r stages history j₀ word ω = 1 := by
  simp_rw [dataFreshKernel_eq_probOf M hM r stages history j₀ hl word hw]
  exact FinDist.sum_probOf _ _

theorem dataFreshKernel_nonneg (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (word : List DataVtStep) (ω : Fin (2*r+1) → Fin M) :
    0 ≤ dataFreshKernel M hM r stages history j₀ word ω := measureProb_nonneg _ _

theorem dataFreshKernel_bad_mass (M : ℕ) (hM : 2 ≤ M) (r : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history) (word : List DataVtStep)
    (hw : DataVtWordLegal stages word) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → Fin M =>
      dataEstimateRadius (MeasureProb (dataVtWordState stages history j₀ word) (liveSet C)) M <
        |vtMedianEstimate M r ω-MeasureProb (dataVtWordState stages history j₀ word) (liveSet C)|),
      dataFreshKernel M hM r stages history j₀ word ω) ≤ (8/9 : ℝ)^r := by
  simp_rw [dataFreshKernel_eq_probOf M hM r stages history j₀ hl word hw]
  exact data_sharp_median_failure M hM r _
    (dataVtWordMatrix_unitary stages history j₀ hl word hw) j₀ (liveSet C)

omit [Fintype C] [DecidableEq C] in

theorem prefix_kernel_sum_one {X : Type} [Fintype X] [Inhabited X] (n : ℕ)
    (κ : (Fin n → X) → Fin n → X → ℝ)
    (hdep : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → κ ω i = κ ω' i)
    (hnorm : ∀ ω i, ∑ x, κ ω i x = 1) :
    ∑ ω : Fin n → X, ∏ i, κ ω i (ω i) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let κ' : (Fin n → X) → Fin n → X → ℝ := fun ω i => κ (Fin.snoc ω default) i.castSucc
    have hdep' : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → κ' ω i = κ' ω' i := by
      intro i ω ω' h
      apply hdep
      intro j hj
      have hjn : j.val < n := by omega
      have he : j = (⟨j.val, hjn⟩ : Fin n).castSucc := by ext; rfl
      rw [he, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h _ hj
    have hi := ih κ' hdep' (fun ω i => hnorm (Fin.snoc ω default) i.castSucc)
    have hword (ω : Fin n → X) (x : X) (i : Fin (n+1)) :
        κ (Fin.snoc ω x) i = κ (Fin.snoc ω default) i := by
      apply hdep
      intro j hj
      have hjn : j.val < n := by omega
      have he : j = (⟨j.val, hjn⟩ : Fin n).castSucc := by ext; rfl
      rw [he, Fin.snoc_castSucc, Fin.snoc_castSucc]
    have hs : (∑ ω : Fin (n+1) → X, ∏ i, κ ω i (ω i)) =
        ∑ ω : Fin n → X, ∑ x : X, ∏ i, κ (Fin.snoc ω x) i ((Fin.snoc ω x : Fin (n+1) → X) i) := by
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) => X))]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    rw [hs]
    have he (ω : Fin n → X) (x : X) :
        (∏ i, κ (Fin.snoc ω x) i ((Fin.snoc ω x : Fin (n+1) → X) i)) =
          (∏ i, κ' ω i (ω i))*κ (Fin.snoc ω default) (Fin.last n) x := by
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      simp_rw [hword]
      rfl
    simp_rw [he]
    simp only [← Finset.mul_sum, hnorm, mul_one]
    exact hi

omit [Fintype C] [DecidableEq C] in

theorem prefix_kernel_sum_ge {X : Type} [Fintype X] [Inhabited X] (n : ℕ)
    (κ : (Fin n → X) → Fin n → X → ℝ)
    (hdep : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → κ ω i = κ ω' i)
    (c : ℝ) (hc : 0 ≤ c) (hκ : ∀ ω i x, 0 ≤ κ ω i x)
    (hnorm : ∀ ω i, c ≤ ∑ x, κ ω i x) :
    c^n ≤ ∑ ω : Fin n → X, ∏ i, κ ω i (ω i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let κ' : (Fin n → X) → Fin n → X → ℝ := fun ω i => κ (Fin.snoc ω default) i.castSucc
    have hdep' : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → κ' ω i = κ' ω' i := by
      intro i ω ω' h
      apply hdep
      intro j hj
      have hjn : j.val < n := by omega
      have he : j = (⟨j.val, hjn⟩ : Fin n).castSucc := by ext; rfl
      rw [he, Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact h _ hj
    have hi := ih κ' hdep'
      (fun ω i x => hκ (Fin.snoc ω default) i.castSucc x)
      (fun ω i => hnorm (Fin.snoc ω default) i.castSucc)
    have hword (ω : Fin n → X) (x : X) (i : Fin (n+1)) :
        κ (Fin.snoc ω x) i = κ (Fin.snoc ω default) i := by
      apply hdep
      intro j hj
      have hjn : j.val < n := by omega
      have he : j = (⟨j.val, hjn⟩ : Fin n).castSucc := by ext; rfl
      rw [he, Fin.snoc_castSucc, Fin.snoc_castSucc]
    have hs : (∑ ω : Fin (n+1) → X, ∏ i, κ ω i (ω i)) =
        ∑ ω : Fin n → X, ∑ x : X, ∏ i, κ (Fin.snoc ω x) i ((Fin.snoc ω x : Fin (n+1) → X) i) := by
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) => X))]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      rfl
    rw [hs]
    have he (ω : Fin n → X) (x : X) :
        (∏ i, κ (Fin.snoc ω x) i ((Fin.snoc ω x : Fin (n+1) → X) i)) =
          (∏ i, κ' ω i (ω i))*κ (Fin.snoc ω default) (Fin.last n) x := by
      simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      simp_rw [hword]
      rfl
    simp_rw [he]
    simp only [← Finset.mul_sum]
    calc
      c^(n+1) = c^n*c := pow_succ _ _
      _ ≤ (∑ ω : Fin n → X, ∏ i, κ' ω i (ω i))*c := mul_le_mul_of_nonneg_right hi hc
      _ = ∑ ω : Fin n → X, (∏ i, κ' ω i (ω i))*c := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left
        (hnorm (Fin.snoc ω default) (Fin.last n))
        (Finset.prod_nonneg (fun i _ => hκ (Fin.snoc ω default) i.castSucc (ω i))))

theorem dataRecordLaw_sum_one (M : ℕ) (hM : 2 ≤ M) (r n : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (words : (Fin n → (Fin (2*r+1) → Fin M)) → Fin n → List DataVtStep)
    (hw : ∀ ω i, DataVtWordLegal stages (words ω i))
    (hdep : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → words ω i = words ω' i) :
    ∑ ω, dataRecordLaw M hM r n stages history j₀ words ω = 1 := by
  letI : Inhabited (Fin M) := ⟨⟨0, by omega⟩⟩
  apply prefix_kernel_sum_one
  · intro i ω ω' h
    rw [hdep i ω ω' h]
  · intro ω i
    exact dataFreshKernel_sum_one M hM r stages history j₀ hl _ (hw ω i)

theorem dataRecordLaw_nonneg (M : ℕ) (hM : 2 ≤ M) (r n : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C)
    (words : (Fin n → (Fin (2*r+1) → Fin M)) → Fin n → List DataVtStep)
    (ω : Fin n → (Fin (2*r+1) → Fin M)) :
    0 ≤ dataRecordLaw M hM r n stages history j₀ words ω :=
  Finset.prod_nonneg (fun i _ => dataFreshKernel_nonneg M hM r stages history j₀ (words ω i) (ω i))

theorem dataRecordGood_mass (M : ℕ) (hM : 2 ≤ M) (r n : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (hl : GrowingVtLegal stages history)
    (words : (Fin n → (Fin (2*r+1) → Fin M)) → Fin n → List DataVtStep)
    (hw : ∀ ω i, DataVtWordLegal stages (words ω i))
    (hdep : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → words ω i = words ω' i) :
    1-(n : ℝ)*(8/9 : ℝ)^r ≤
      ∑ ω ∈ dataRecordGood M r n stages history j₀ words,
        dataRecordLaw M hM r n stages history j₀ words ω := by
  letI : Inhabited (Fin M) := ⟨⟨0, by omega⟩⟩
  let P := fun ω i x =>
    |vtMedianEstimate M r x-MeasureProb (dataVtWordState stages history j₀ (words ω i)) (liveSet C)| ≤
      dataEstimateRadius (MeasureProb (dataVtWordState stages history j₀ (words ω i)) (liveSet C)) M
  let κ :=
      fun ω i x => if P ω i x then dataFreshKernel M hM r stages history j₀ (words ω i) x else 0
  have hb : (8/9 : ℝ)^r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hk : ∀ ω i x, 0 ≤ κ ω i x := by
    intro ω i x; dsimp [κ]; split_ifs
    · exact dataFreshKernel_nonneg M hM r stages history j₀ _ _
    · exact le_rfl
  have hd : ∀ i ω ω', (∀ j, j.val < i.val → ω j = ω' j) → κ ω i = κ ω' i := by
    intro i ω ω' h; dsimp [κ, P]; rw [hdep i ω ω' h]
  have hn : ∀ ω i, 1-(8/9 : ℝ)^r ≤ ∑ x, κ ω i x := by
    intro ω i
    have htotal := dataFreshKernel_sum_one M hM r stages history j₀ hl _ (hw ω i)
    have hbad := dataFreshKernel_bad_mass M hM r stages history j₀ hl _ (hw ω i)
    have hsplit : (∑ x, κ ω i x)+
        (∑ x ∈ Finset.univ.filter (fun x => ¬P ω i x),
          dataFreshKernel M hM r stages history j₀ (words ω i) x) = 1 := by
      rw [Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      convert! htotal using 1
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : P ω i x
      · simp only [κ, if_pos hx, if_neg (not_not.mpr hx), _root_.add_zero]
      · simp only [κ, if_neg hx, if_pos hx, _root_.zero_add]
    have hbad' : (∑ x ∈ Finset.univ.filter (fun x => ¬P ω i x),
        dataFreshKernel M hM r stages history j₀ (words ω i) x) ≤ (8/9 : ℝ)^r := by
      simpa only [P, not_le] using! hbad
    linarith
  have hmass := prefix_kernel_sum_ge n κ hd (1-(8/9 : ℝ)^r) (sub_nonneg.mpr hb) hk hn
  have he (ω : Fin n → (Fin (2*r+1) → Fin M)) :
      (∏ i, κ ω i (ω i)) = if ∀ i, P ω i (ω i) then
        dataRecordLaw M hM r n stages history j₀ words ω else 0 := by
    split_ifs with h
    · unfold dataRecordLaw
      apply Finset.prod_congr rfl
      intro i _; simp only [κ, if_pos (h i)]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [κ, hi])
  have hsum : (∑ ω, ∏ i, κ ω i (ω i)) =
      ∑ ω ∈ dataRecordGood M r n stages history j₀ words,
        dataRecordLaw M hM r n stages history j₀ words ω := by
    simp_rw [he]
    rw [dataRecordGood, Finset.sum_filter]
  rw [hsum] at hmass
  have hbernoulli := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(8/9 : ℝ)^r by linarith) n
  have hber : 1-(n : ℝ)*(8/9 : ℝ)^r ≤ (1-(8/9 : ℝ)^r)^n := by
    simpa only [mul_neg, ← sub_eq_add_neg] using! hbernoulli
  exact hber.trans hmass

theorem compiled_plain_word_run (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (word : List DataVtStep)
    (ψ : QState (Fin M × (Bool × VtSpace C))) :
    Run 1 (compiledVtCircuit M stages history j₀ (word.map CompiledVtStep.plain)) ψ =
      ApplyGate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
        (TensorGate (1 : Matrix Bool Bool ℂ) (dataVtWordMatrix stages history j₀ word))) ψ := by
  induction word generalizing ψ with
  | nil => simp [compiledVtCircuit, Circuit.ofGates, tensorGate_one, applyGate_one]
  | cons s word ih =>
    simp only [List.map_cons, compiledVtCircuit, Circuit.ofGates, Run]
    change Run 1 (compiledVtCircuit M stages history j₀ (word.map CompiledVtStep.plain))
      (ApplyGate (compiledVtStepMatrix M stages history j₀ (.plain s)) ψ) = _
    rw [ih, ← applyGate_mul]
    simp only [compiledVtStepMatrix, tensorGate_mul, Matrix.one_mul]
    rw [show s::word = [s]++word from rfl, dataVtWordMatrix_append, dataVtWordMatrix_singleton]

theorem compiled_controlled_word_run (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (word : List DataVtStep)
    (ψ : QState (Fin M × (Bool × VtSpace C))) :
    Run 1 (compiledVtCircuit M stages history j₀ (word.map CompiledVtStep.controlled)) ψ =
      ApplyGate (aeControlledGate M (dataVtWordMatrix stages history j₀ word)) ψ := by
  induction word generalizing ψ with
  | nil => simp [compiledVtCircuit, Circuit.ofGates, aeControlledGate, controlOracle_one,
      tensorGate_one, applyGate_one]
  | cons s word ih =>
    simp only [List.map_cons, compiledVtCircuit, Circuit.ofGates, Run]
    change Run 1 (compiledVtCircuit M stages history j₀ (word.map CompiledVtStep.controlled))
      (ApplyGate (compiledVtStepMatrix M stages history j₀ (.controlled s)) ψ) = _
    rw [ih, ← applyGate_mul]
    simp only [compiledVtStepMatrix, aeControlledGate, tensorGate_mul, Matrix.one_mul,
        controlOracle_mul]
    rw [show s::word = [s]++word from rfl, dataVtWordMatrix_append, dataVtWordMatrix_singleton]

omit [DecidableEq C] in

theorem compiled_data_word_legal_time (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (word : List DataVtStep)
    (hw : DataVtWordLegal stages word) :
    CompiledVtWordLegal stages (word.map (CompiledVtStep.plain (M := M))) ∧
      CompiledVtWordLegal stages (word.map (CompiledVtStep.controlled (M := M))) ∧
      compiledVtWordTime (word.map (CompiledVtStep.plain (M := M))) = dataVtWordTime word ∧
      compiledVtWordTime (word.map (CompiledVtStep.controlled (M := M))) = dataVtWordTime word := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hw t ht
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hw t ht
  · simp [compiledVtWordTime, List.map_map, Function.comp_def, compiledVtStepTime, dataVtWordTime]
  · simp [compiledVtWordTime, List.map_map, Function.comp_def, compiledVtStepTime, dataVtWordTime]

def compiledThreshold (M k : ℕ) : CompiledVtStep M := .workspace
  (permMatrix (fun p : Fin M × Bool => (p.1, if k < p.1.val then !p.2 else p.2)))

def compiledAEBlock (M k : ℕ) (word : List DataVtStep) : List (CompiledVtStep M) :=
  [compiledThreshold M k, .controlled .liveReflection] ++
    (dataVtWordInverse word).map CompiledVtStep.controlled ++
    [.controlled .sourceReflection] ++ word.map CompiledVtStep.controlled ++ [compiledThreshold M k]

def compiledAELoop (M : ℕ) (word : List DataVtStep) : ℕ → List (CompiledVtStep M)
  | 0 => []
  | n+1 => compiledAELoop M word n ++ compiledAEBlock M n word

def compiledAEWord (M : ℕ) (word : List DataVtStep) : List (CompiledVtStep M) :=
  word.map CompiledVtStep.plain ++ [.workspace (TensorGate (QFTMatrix M) 1)] ++
    compiledAELoop M word (M-1) ++ [.workspace (TensorGate (QFTMatrix M)ᴴ 1)]

theorem compiledThreshold_matrix (M k : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C) (j₀ : VtSpace C) :
    compiledVtStepMatrix M stages history j₀ (compiledThreshold M k) =
      permMatrix (phaseThresholdFlip (I := VtSpace C) M k) := by
  ext ⟨p, b, x⟩ ⟨q, c, y⟩
  simp only [compiledThreshold, compiledVtStepMatrix, permMatrix, Matrix.of_apply,
    Matrix.one_apply, phaseThresholdFlip, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem compiledFourier_matrix (M : ℕ) (U : Matrix (Fin M) (Fin M) ℂ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C) (j₀ : VtSpace C) :
    compiledVtStepMatrix M stages history j₀ (.workspace (TensorGate U 1)) =
      TensorGate U (1 : Matrix (Bool × VtSpace C) (Bool × VtSpace C) ℂ) := by
  ext ⟨p, b, x⟩ ⟨q, c, y⟩
  simp only [compiledVtStepMatrix, tensorGate_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [DecidableEq C] in

theorem compiledThreshold_legal (M k : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) :
    CompiledVtStepLegal stages (compiledThreshold M k) := by
  apply permMatrix_unitary
  rintro ⟨p, b⟩
  by_cases h : k < p.val <;> simp [h]

@[simp] theorem compiledVtWordTime_append {M : ℕ} (u v : List (CompiledVtStep M)) :
    compiledVtWordTime (u++v) = compiledVtWordTime u+compiledVtWordTime v := by
  simp [compiledVtWordTime]

theorem compiledAEWord_time (M : ℕ) (word : List DataVtStep) :
    compiledVtWordTime (compiledAEWord M word) = (2*(M-1)+1)*dataVtWordTime word := by
  have hc : compiledVtWordTime (word.map (CompiledVtStep.controlled (M := M))) = dataVtWordTime word := by
    simp [compiledVtWordTime, List.map_map, Function.comp_def, compiledVtStepTime, dataVtWordTime]
  have hp : compiledVtWordTime (word.map (CompiledVtStep.plain (M := M))) = dataVtWordTime word := by
    simp [compiledVtWordTime, List.map_map, Function.comp_def, compiledVtStepTime, dataVtWordTime]
  have hb (k : ℕ) : compiledVtWordTime (compiledAEBlock M k word) = 2*dataVtWordTime word := by
    have hi : compiledVtWordTime ((dataVtWordInverse word).map (CompiledVtStep.controlled (M := M))) =
        dataVtWordTime (dataVtWordInverse word) := by
      simp [compiledVtWordTime, List.map_map, Function.comp_def, compiledVtStepTime, dataVtWordTime]
    simp only [compiledAEBlock, compiledVtWordTime_append, hc, hi, dataVtWordTime_inverse]
    simp [compiledVtWordTime, compiledVtStepTime, compiledThreshold, dataVtStepTime, two_mul]
  have hloop (n : ℕ) : compiledVtWordTime (compiledAELoop M word n) = 2*n*dataVtWordTime word := by
    induction n with
    | zero => simp [compiledAELoop, compiledVtWordTime]
    | succ n ih => rw [compiledAELoop, compiledVtWordTime_append, ih, hb]; ring
  simp only [compiledAEWord, compiledVtWordTime_append, hp, hloop]
  simp only [compiledVtWordTime, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    compiledVtStepTime]
  ring

omit [DecidableEq C] in

theorem compiledAEWord_legal (M : ℕ) (hM : 0 < M)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (word : List DataVtStep)
    (hw : DataVtWordLegal stages word) : CompiledVtWordLegal stages (compiledAEWord M word) := by
  have hc := (compiled_data_word_legal_time M stages word hw).2.1
  have hi := (compiled_data_word_legal_time M stages (dataVtWordInverse word)
    (dataVtWordInverse_legal stages word hw)).2.1
  have hb (k : ℕ) : CompiledVtWordLegal stages (compiledAEBlock M k word) := by
    intro s hs
    simp only [compiledAEBlock, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with ((((ht | hm) | hi') | hr) | hf) | ht
    · subst s; exact compiledThreshold_legal M k stages
    · subst s; trivial
    · exact hi s hi'
    · subst s; trivial
    · exact hc s hf
    · subst s; exact compiledThreshold_legal M k stages
  have hloop (n : ℕ) : CompiledVtWordLegal stages (compiledAELoop M word n) := by
    induction n with
    | zero => intro s hs; simp [compiledAELoop] at hs
    | succ n ih =>
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact ih s hs
      · exact hb n s hs
  intro s hs
  simp only [compiledAEWord, List.mem_append, List.mem_singleton] at hs
  rcases hs with ((hp | hq) | hl) | hq
  · exact (compiled_data_word_legal_time M stages word hw).1 s hp
  · subst s
    exact tensorGate_unitary (qftMatrix_unitary hM) (by simp)
  · exact hloop (M-1) s hl
  · subst s
    exact tensorGate_unitary (conjTranspose_mem_unitaryGroup (qftMatrix_unitary hM)) (by simp)

private theorem compiledVtCircuit_append (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C) (j₀ : VtSpace C)
    (u v : List (CompiledVtStep M)) :
    compiledVtCircuit M stages history j₀ (u++v) =
      compiledVtCircuit M stages history j₀ u ++ compiledVtCircuit M stages history j₀ v := by
  simp only [compiledVtCircuit, List.map_append, Circuit.ofGates]

@[simp] private theorem compiledVtCircuit_nil (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C) (j₀ : VtSpace C) :
    compiledVtCircuit M stages history j₀ [] = [] := rfl

@[simp] private theorem compiledVtCircuit_cons (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C) (j₀ : VtSpace C)
    (s : CompiledVtStep M) (word : List (CompiledVtStep M)) :
    compiledVtCircuit M stages history j₀ (s::word) =
      .gate (compiledVtStepMatrix M stages history j₀ s)::compiledVtCircuit M stages history j₀ word := rfl

theorem compiledAEBlock_run (M k : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (word : List DataVtStep)
    (ψ : QState (Fin M × (Bool × VtSpace C))) :
    Run 1 (compiledVtCircuit M stages history j₀ (compiledAEBlock M k word)) ψ =
      Run (aeControlledGate M (preparedMark (liveSet C)))
        (((phaseThresholdBlock (I := VtSpace C) M k).flatMap expandAEAccess).map
          (aeAccessInstruction M (dataVtWordMatrix stages history j₀ word) j₀)) ψ := by
  rw [compiledAEBlock]
  simp only [compiledVtCircuit_append, run_append, compiledVtCircuit_cons, compiledVtCircuit_nil,
      Run]
  rw [compiled_controlled_word_run, compiled_controlled_word_run, dataVtWordMatrix_inverse]
  rw [compiledThreshold_matrix]
  simp only [compiledVtStepMatrix, dataVtStepMatrix,
    phaseThresholdBlock, List.flatMap_cons, List.flatMap_nil, expandAEAccess, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, aeAccessInstruction, Run]

theorem compiledAEWord_run (M : ℕ)
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) (word : List DataVtStep)
    (ψ : QState (Fin M × (Bool × VtSpace C))) :
    Run 1 (compiledVtCircuit M stages history j₀ (compiledAEWord M word)) ψ =
      Run (aeControlledGate M (preparedMark (liveSet C)))
        (countedAECircuit M (dataVtWordMatrix stages history j₀ word) j₀) ψ := by
  have hloop (n : ℕ) (χ : QState (Fin M × (Bool × VtSpace C))) :
      Run 1 (compiledVtCircuit M stages history j₀ (compiledAELoop M word n)) χ =
        Run (aeControlledGate M (preparedMark (liveSet C)))
          (((phaseThresholdLoop (I := VtSpace C) M n).flatMap expandAEAccess).map
            (aeAccessInstruction M (dataVtWordMatrix stages history j₀ word) j₀)) χ := by
    induction n generalizing χ with
    | zero => rfl
    | succ n ih =>
      rw [compiledAELoop, compiledVtCircuit_append, run_append, ih, compiledAEBlock_run,
        phaseThresholdLoop, List.flatMap_append, List.map_append, run_append]
  rw [compiledAEWord]
  simp only [compiledVtCircuit_append, run_append, compiledVtCircuit_cons, compiledVtCircuit_nil,
      Run]
  rw [compiled_plain_word_run, hloop, compiledFourier_matrix, compiledFourier_matrix]
  simp only [countedAECircuit, aeAccessWord, countedPhaseCircuit, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, expandAEAccess, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, aeAccessInstruction, Run, run_append]

private def physicalGatesMatrix {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Matrix I I ℂ)) : Matrix I I ℂ := gs.reverse.prod

private theorem physicalGatesMatrix_cons {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (gs : List (Matrix I I ℂ)) :
    physicalGatesMatrix (U::gs) = physicalGatesMatrix gs*U := by
  simp [physicalGatesMatrix]

private theorem physicalGatesMatrix_append {I : Type} [Fintype I] [DecidableEq I]
    (gs hs : List (Matrix I I ℂ)) :
    physicalGatesMatrix (gs++hs) = physicalGatesMatrix hs*physicalGatesMatrix gs := by
  simp [physicalGatesMatrix]

private theorem run_physicalGatesMatrix {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Matrix I I ℂ)) (ψ : QState I) :
    Run 1 (Circuit.ofGates gs) ψ = ApplyGate (physicalGatesMatrix gs) ψ := by
  induction gs generalizing ψ with
  | nil => simp [physicalGatesMatrix, Circuit.ofGates, applyGate_one]
  | cons U gs ih =>
    rw [physicalGatesMatrix_cons, applyGate_mul]
    exact ih (ApplyGate U ψ)

private theorem physicalGatesMatrix_left {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (gs : List (Matrix I I ℂ)) :
    physicalGatesMatrix (gs.map (fun U => TensorGate U (1 : Matrix J J ℂ))) =
      TensorGate (physicalGatesMatrix gs) 1 := by
  induction gs with
  | nil => simp [physicalGatesMatrix, tensorGate_one]
  | cons U gs ih =>
    rw [List.map_cons, physicalGatesMatrix_cons, physicalGatesMatrix_cons, ih, tensorGate_mul,
      Matrix.one_mul]

private theorem physicalGatesMatrix_right {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (gs : List (Matrix J J ℂ)) :
    physicalGatesMatrix (gs.map (fun U => TensorGate (1 : Matrix I I ℂ) U)) =
      TensorGate 1 (physicalGatesMatrix gs) := by
  induction gs with
  | nil => simp [physicalGatesMatrix, tensorGate_one]
  | cons U gs ih =>
    rw [List.map_cons, physicalGatesMatrix_cons, physicalGatesMatrix_cons, ih, tensorGate_mul,
      Matrix.one_mul]

private def freshPhysicalMatrix {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) : (n : ℕ) → Matrix (FreshRegister I n) (FreshRegister I n) ℂ
  | 0 => 1
  | n+1 => TensorGate U (freshPhysicalMatrix U n)

private theorem physicalGatesMatrix_fresh {I : Type} [Fintype I] [DecidableEq I]
    (gs : List (Matrix I I ℂ)) (n : ℕ) :
    physicalGatesMatrix (vtFreshGates gs n) = freshPhysicalMatrix (physicalGatesMatrix gs) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vtFreshGates, physicalGatesMatrix_append, physicalGatesMatrix_left,
      physicalGatesMatrix_right, ih, tensorGate_mul, Matrix.one_mul, Matrix.mul_one]
    rfl

theorem vtFreshGates_run_congr {I : Type} [Fintype I] [DecidableEq I]
    (gs hs : List (Matrix I I ℂ))
    (h : ∀ ψ, Run 1 (Circuit.ofGates gs) ψ = Run 1 (Circuit.ofGates hs) ψ)
    (n : ℕ) (ψ : QState (FreshRegister I n)) :
    Run 1 (Circuit.ofGates (vtFreshGates gs n)) ψ =
      Run 1 (Circuit.ofGates (vtFreshGates hs n)) ψ := by
  have he : physicalGatesMatrix gs = physicalGatesMatrix hs := by
    ext p q
    have hq := congrFun (h (Ket q)) p
    simpa only [run_physicalGatesMatrix, ApplyGate, mulVec_ket_apply] using! hq
  rw [run_physicalGatesMatrix, run_physicalGatesMatrix,
    physicalGatesMatrix_fresh, physicalGatesMatrix_fresh, he]

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
