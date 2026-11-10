/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound.Lemmas3To5
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound

open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

theorem list_sum_map_const (l : List ℕ) (c : ℝ) :
    (l.map (fun _ => c)).sum = (l.length : ℝ) * c := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

section Recursion

variable {n w : ℕ} {S : Type}

theorem knownPrecs_cons_known (g : LocalQFTGate n) (m : ℕ)
    (W : List (MixedStep n w S)) :
    knownPrecs (MixedStep.known g m :: W) = m :: knownPrecs W := rfl

theorem knownPrecs_cons_call (s : S) (adj : Bool) (ctrl : Option (Fin n × Bool))
    (W : List (MixedStep n w S)) :
    knownPrecs (MixedStep.call s adj ctrl :: W) = knownPrecs W := rfl

theorem budget_cons_known (g : LocalQFTGate n) (m : ℕ)
    (W : List (MixedStep n w S)) :
    budget (MixedStep.known g m :: W) = ((2 : ℝ)⁻¹) ^ m + budget W := by
  simp [budget, knownPrecs, List.map_cons, List.sum_cons]

theorem budget_cons_call (s : S) (adj : Bool) (ctrl : Option (Fin n × Bool))
    (W : List (MixedStep n w S)) :
    budget (MixedStep.call s adj ctrl :: W) = budget W := by
  simp [budget, knownPrecs]

theorem mem_knownPrecs_cons {s : MixedStep n w S} {W : List (MixedStep n w S)}
    {m : ℕ} (hm : m ∈ knownPrecs W) : m ∈ knownPrecs (s :: W) := by
  simp only [knownPrecs] at hm ⊢
  obtain ⟨a, ha, hf⟩ := List.mem_filterMap.mp hm
  exact List.mem_filterMap.mpr ⟨a, List.mem_cons_of_mem s ha, hf⟩

end Recursion

theorem budget_eq_of_all_prec {n w : ℕ} {S : Type}
    (W : List (MixedStep n w S)) (k : ℕ)
    (hk : ∀ m ∈ knownPrecs W, m = k) :
    budget W = (knownPrecs W).length * (2 : ℝ)⁻¹ ^ k := by
  induction W with
  | nil => simp [budget, knownPrecs]
  | cons s W ih =>
    cases s with
    | known g m =>
      have hk' : ∀ m' ∈ knownPrecs W, m' = k :=
        fun m' hm' => hk m' (mem_knownPrecs_cons hm')
      have hm : m = k := hk m (by
        simp only [knownPrecs]
        exact List.mem_filterMap.mpr
          ⟨MixedStep.known g m, List.mem_cons_self, rfl⟩)
      rw [budget_cons_known, knownPrecs_cons_known]
      simp only [List.length_cons, hm, ih hk']
      push_cast
      ring
    | call slot adj ctrl =>
      have hk' : ∀ m' ∈ knownPrecs W, m' = k :=
        fun m' hm' => hk m' (mem_knownPrecs_cons hm')
      rw [budget_cons_call, knownPrecs_cons_call]
      exact ih hk'

theorem budget_le_length_mul {n w : ℕ} {S : Type}
    (W : List (MixedStep n w S)) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ m ∈ knownPrecs W, (2 : ℝ)⁻¹ ^ m ≤ δ) :
    budget W ≤ (W.length : ℝ) * δ := by
  induction W with
  | nil => simp [budget, knownPrecs]
  | cons s W ih =>
    cases s with
    | known g m =>
      have hδ' : ∀ m' ∈ knownPrecs W, (2 : ℝ)⁻¹ ^ m' ≤ δ :=
        fun m' hm' => hδ m' (mem_knownPrecs_cons hm')
      have hm : (2 : ℝ)⁻¹ ^ m ≤ δ := hδ m (by
        simp only [knownPrecs]
        exact List.mem_filterMap.mpr
          ⟨MixedStep.known g m, List.mem_cons_self, rfl⟩)
      have ih' := ih hδ'
      rw [budget_cons_known, List.length_cons]
      push_cast
      nlinarith
    | call slot adj ctrl =>
      have hδ' : ∀ m' ∈ knownPrecs W, (2 : ℝ)⁻¹ ^ m' ≤ δ :=
        fun m' hm' => hδ m' (mem_knownPrecs_cons hm')
      have ih' := ih hδ'
      rw [budget_cons_call, List.length_cons]
      push_cast
      nlinarith

theorem lemma5_mixedWord_uniform {n w : ℕ} (hw : w ≤ n) (S : Type) [DecidableEq S]
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (paid : List (AccessForm S)) (hv : ValidControls W) (hp : mixedWordLegal W paid)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ m ∈ knownPrecs W, (2 : ℝ)⁻¹ ^ m ≤ δ) :
    ∀ (ψ : QState (Reg n)) (E : Finset (Reg n)), Normalized ψ →
      |MeasureProb (ApplyGate (word hw O W) ψ) E -
        MeasureProb (ApplyGate (mixedWordMatrix hw O W) ψ) E| ≤
        2 * (W.length : ℝ) * δ := by
  intro ψ E hψ
  have hbridge := lemma5_bridge_mixedWord hw S O W paid hv hp hO ψ E hψ
  have hbudget := budget_le_length_mul W δ hδ0 hδ
  nlinarith

theorem lemma5_source_bound {n w : ℕ} (hw : w ≤ n) (S : Type) [DecidableEq S]
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (paid : List (AccessForm S)) (hv : ValidControls W) (hp : mixedWordLegal W paid)
    (hO : ∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : ∀ m ∈ knownPrecs W, (2 : ℝ)⁻¹ ^ m ≤ δ)
    (ψ : QState (Reg n)) (E : Finset (Reg n)) (hψ : Normalized ψ)
    (target ε : ℝ)
    (hε : |MeasureProb (ApplyGate (word hw O W) ψ) E - target| ≤ ε) :
    |MeasureProb (ApplyGate (mixedWordMatrix hw O W) ψ) E - target| ≤
      ε + 2 * (W.length : ℝ) * δ := by
  set A := MeasureProb (ApplyGate (word hw O W) ψ) E with hA
  set B := MeasureProb (ApplyGate (mixedWordMatrix hw O W) ψ) E with hB
  have hbridge := lemma5_mixedWord_uniform hw S O W paid hv hp hO δ hδ0 hδ ψ E hψ
  have hbridge' : |B - A| ≤ 2 * (W.length : ℝ) * δ := by
    simpa [hA, hB, abs_sub_comm] using hbridge
  calc |B - target| = |(B - A) + (A - target)| := by
        rw [show B - target = (B - A) + (A - target) by ring]
    _ ≤ |B - A| + |A - target| := abs_add_le _ _
    _ ≤ 2 * (W.length : ℝ) * δ + ε := add_le_add hbridge' hε
    _ = ε + 2 * (W.length : ℝ) * δ := by ring

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PrecisionBound
