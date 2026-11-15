/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNormalizedChainConstruction
public import Qatlib.Concepts.GraphEnergy.ZeroEnergy.GraphEnergyKernelConsumers
public import Qatlib.Concepts.WalkSearch.ProjectorCS

@[expose] public section
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GraphNormalizedChainConstruction

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Qatlib
open Matrix
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open Qatlib.Concepts.DirichletForm.EnergyIdentity
open Qatlib.Concepts.GraphCutTrial.CutEnergyBound
open Qatlib.Concepts.GraphLaplacian.LaplacianPsd
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open scoped BigOperators Matrix

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For nonzero graph volume, the mass of a set is its volume divided by the total volume. -/
theorem mass_eq_setVolume (hv : volume G ≠ 0) (S : Finset V) :
    mass G S = setVolume G S / volume G := by
  unfold mass setVolume
  simp only [stationary, hv, ite_false]
  calc
    (∑ x ∈ S, (degree G x / volume G))
        = ∑ x ∈ S, (1 / volume G) * degree G x := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = (1 / volume G) * ∑ x ∈ S, degree G x := by rw [Finset.mul_sum]
    _ = (∑ x ∈ S, degree G x) / volume G := by ring

/-- For nonzero graph volume, the outgoing flow is the edge boundary divided by twice the total
volume. -/
theorem flow_eq_edgeBoundary (hv : volume G ≠ 0) (S : Finset V) :
    flow G S = edgeBoundary G S / (2 * volume G) := by
  have hinner : ∀ (x : V), x ∈ S → (∑ y ∈ Sᶜ, stationary G x * kernel G x y)
      = (∑ y ∈ Sᶜ, (if G.Adj x y then (1 : ℝ) else 0)) / (2 * volume G) := by
    intro x hx
    have hterm : ∀ y ∈ Sᶜ, stationary G x * kernel G x y
        = (if G.Adj x y then (1 : ℝ) else 0) / (2 * volume G) := by
      intro y hy
      have hne : x ≠ y := by
        intro hxy
        exact Finset.mem_compl.mp hy (hxy ▸ hx)
      by_cases hxy : x = y
      · exfalso
        exact hne hxy
      · by_cases hdx : degree G x = 0
        · have hstat : stationary G x = 0 := by
            simp only [stationary, hv, ite_false]
            rw [hdx]
            simp
          have hna : ¬ G.Adj x y := not_adj_of_degree_eq_zero G hdx y
          simp [kernel, hdx, hxy, hna, hstat]
        · have hstat : stationary G x = degree G x / volume G := by
            simp only [stationary, hv, ite_false]
          have hker : kernel G x y = (if G.Adj x y then 1 / (2 * degree G x) else 0) := by
            simp only [kernel, hdx, ite_false, hxy, zero_add]
          rw [hstat, hker]
          by_cases hadj : G.Adj x y
          · simp only [hadj, ite_true]
            field_simp
          · simp only [hadj, ite_false]
            ring
    calc
      (∑ y ∈ Sᶜ, stationary G x * kernel G x y)
          = ∑ y ∈ Sᶜ, (if G.Adj x y then (1 : ℝ) else 0) / (2 * volume G) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hterm y hy
      _ = (∑ y ∈ Sᶜ, (if G.Adj x y then (1 : ℝ) else 0)) / (2 * volume G) := by
            rw [Finset.sum_div]
  unfold flow edgeBoundary
  calc
    (∑ x ∈ S, ∑ y ∈ Sᶜ, stationary G x * kernel G x y)
        = ∑ x ∈ S, (∑ y ∈ Sᶜ, (if G.Adj x y then (1 : ℝ) else 0)) / (2 * volume G) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hinner x hx
    _ = (∑ x ∈ S, ∑ y ∈ Sᶜ, (if G.Adj x y then (1 : ℝ) else 0)) / (2 * volume G) := by
          rw [Finset.sum_div]

/-- For nonzero volume and nonzero set mass, cut conductance is the edge boundary divided by
twice the set volume. -/
theorem cutConductance_eq_edgeBoundary_ratio (hv : volume G ≠ 0) (S : Finset V)
    (hmass : mass G S ≠ 0) :
    cutConductance G S = edgeBoundary G S / (2 * setVolume G S) := by
  unfold cutConductance
  rw [flow_eq_edgeBoundary G hv S]
  rw [mass_eq_setVolume G hv S]
  have hne : setVolume G S ≠ 0 := by
    intro hz
    have : mass G S = 0 := by
      rw [mass_eq_setVolume G hv S, hz]
      simp
    exact hmass this
  field_simp

/-- A cut of positive mass at most one half yields a mean-zero function with positive variance
and Rayleigh quotient at most twice its cut conductance. -/
theorem cheeger_upper_bound [Nonempty V] (S : Finset V)
    (hmass : 0 < mass G S) (hmass2 : mass G S ≤ 1/2) :
    ∃ f : V → ℝ, mean G f = 0 ∧ 0 < variance G f ∧
      energy G f / variance G f ≤ 2 * cutConductance G S := by
  refine ⟨centeredIndicator G S, mean_centered G S, ?_, ?_⟩
  · exact variance_pos G S hmass hmass2
  · have hray := Qatlib.Concepts.GraphCutTrial.CutEnergyBound.rayleigh G S hmass hmass2
    have henergy : energy G (centeredIndicator G S) = flow G S := energy_flow G S
    have hvar : variance G (centeredIndicator G S) = mass G S * (1 - mass G S) :=
      variance_mass G S
    have hray' : flow G S / (mass G S * (1 - mass G S)) ≤ 2 * (flow G S / mass G S) := by
      have h := hray
      rw [henergy, hvar] at h
      convert! h using 1; ring
    rw [henergy, hvar]
    unfold cutConductance
    exact hray'

/-- The lazy kernel of a degree-regular graph is symmetric. -/
lemma kernel_symmetric_of_regular {d : ℝ} (hd : IsDegreeRegular G d) (x y : V) :
    kernel G x y = kernel G y x := by
  have hdx : degree G x = d := hd x
  have hdy : degree G y = d := hd y
  by_cases hxy : x = y
  · subst hxy
    simp [kernel]
  · by_cases hzero : d = 0
    · have hx0 : degree G x = 0 := by rw [hdx, hzero]
      have hy0 : degree G y = 0 := by rw [hdy, hzero]
      simp [kernel, hx0, hy0, hxy, Ne.symm hxy]
    · have hxne : degree G x ≠ 0 := by rw [hdx]; exact hzero
      have hyne : degree G y ≠ 0 := by rw [hdy]; exact hzero
      have hadj' : G.Adj y x ↔ G.Adj x y :=
        ⟨fun h => G.adj_symm h, fun h => G.adj_symm h⟩
      have hker : kernel G x y = (if G.Adj x y then 1 / (2 * degree G x) else 0) := by
        simp only [kernel, hxne, ite_false, hxy, zero_add]
      have hker' : kernel G y x = (if G.Adj y x then 1 / (2 * degree G y) else 0) := by
        simp only [kernel, hyne, ite_false, Ne.symm hxy, zero_add]
      rw [hker, hker']
      by_cases hadj : G.Adj x y
      · have hboth : G.Adj y x := hadj'.mpr hadj
        simp [hadj, hboth, hdx, hdy]
      · have hnot : ¬ G.Adj y x := fun h => hadj (hadj'.mp h)
        simp [hadj, hnot]

/-- For a nonempty regular graph of nonzero volume, a lazy chain gap at most one gives the same
symmetric kernel gap. -/
theorem symmetricChainGap_of_regular {d δ : ℝ} (hd : IsDegreeRegular G d)
    (hn : 0 < (Fintype.card V : ℝ)) (hvol : volume G ≠ 0) (hδ : δ ≤ 1)
    (hgap : LazyChainGap G δ) :
    SymmetricChainGap (kernel G) δ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact kernel_nonneg G x y
  · intro x
    exact kernel_sum G x
  · exact kernel_symmetric_of_regular G hd
  · intro v hvsum
    let n : ℝ := Fintype.card V
    have hnpos : 0 < n := hn
    have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
    have hvol' : volume G = d * n := by
      unfold volume
      calc
        (∑ x, degree G x) = ∑ x, d := by
          apply Finset.sum_congr rfl
          intro x _
          exact hd x
        _ = n * d := by
          simp [n, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = d * n := by ring
    have hdne : d ≠ 0 := by
      intro hz
      rw [hvol'] at hvol
      simp [hz] at hvol
    have hstat : ∀ x, stationary G x = 1 / n := by
      intro x
      simp only [stationary, hvol, ite_false]
      rw [hd x, hvol']
      field_simp
    have hmean : mean G v = (1 / n) * (∑ x, v x) := by
      unfold mean
      calc
        (∑ x, stationary G x * v x) = ∑ x, (1 / n) * v x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hstat x]
        _ = (1 / n) * (∑ x, v x) := by rw [Finset.mul_sum]
    have hmean0 : mean G v = 0 := by rw [hmean, hvsum, mul_zero]
    have hvar : variance G v = (1 / n) * (∑ x, (v x)^2) := by
      rw [variance_eq_degree_weighted G hvol v, hmean0]
      calc
        (1 / volume G) * (∑ x, degree G x * (v x - 0)^2)
            = (1 / (d * n)) * (∑ x, d * (v x)^2) := by
              rw [hvol']
              have hsum : (∑ x, degree G x * (v x - 0)^2) = ∑ x, d * (v x)^2 := by
                apply Finset.sum_congr rfl
                intro x _
                rw [hd x]
                ring
              rw [hsum]
        _ = (1 / n) * (∑ x, (v x)^2) := by
          rw [← Finset.mul_sum]
          field_simp
    have henergy : energy G v
        = (1 / n) * ((∑ x, (v x)^2) - ∑ x, ∑ y, v x * kernel G x y * v y) := by
      unfold energy
      simp only [hstat]
      calc
        (∑ x, (1 / n) * v x * (v x - ∑ y, kernel G x y * v y))
            = (1 / n) * ∑ x, (v x * v x - v x * (∑ y, kernel G x y * v y)) := by
              have hsum : (∑ x, (1 / n) * v x * (v x - ∑ y, kernel G x y * v y))
                  = ∑ x, (1 / n) * (v x * v x - v x * (∑ y, kernel G x y * v y)) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
              rw [hsum, ← Finset.mul_sum]
        _ = (1 / n) * ((∑ x, (v x)^2)
              - ∑ x, ∑ y, v x * kernel G x y * v y) := by
          have hinner : (∑ x, (v x * v x - v x * (∑ y, kernel G x y * v y)))
              = (∑ x, (v x)^2) - ∑ x, ∑ y, v x * kernel G x y * v y := by
            calc
              (∑ x, (v x * v x - v x * (∑ y, kernel G x y * v y)))
                  = ∑ x, ((v x)^2 - ∑ y, v x * (kernel G x y * v y)) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    have h2 : v x * (∑ y, kernel G x y * v y)
                        = ∑ y, v x * (kernel G x y * v y) := by
                      rw [Finset.mul_sum]
                    have h1 : (∑ y, v x * (kernel G x y * v y))
                        = ∑ y, v x * kernel G x y * v y := by
                      apply Finset.sum_congr rfl
                      intro y _
                      ring
                    rw [h2, h1]
                    ring
              _ = (∑ x, (v x)^2) - ∑ x, ∑ y, v x * kernel G x y * v y := by
                have hsum' : (∑ x, ∑ y, v x * (kernel G x y * v y))
                    = ∑ x, ∑ y, v x * kernel G x y * v y := by
                  apply Finset.sum_congr rfl
                  intro x _
                  have h1 : (∑ y, v x * (kernel G x y * v y))
                      = ∑ y, v x * kernel G x y * v y := by
                    apply Finset.sum_congr rfl
                    intro y _
                    ring
                  exact h1
                rw [Finset.sum_sub_distrib, hsum']
          rw [hinner]
    have hgap' := hgap v hmean0 hδ
    rw [hvar, henergy] at hgap'
    have h1 : δ * (∑ x, (v x)^2)
        ≤ (∑ x, (v x)^2) - ∑ x, ∑ y, v x * kernel G x y * v y := by
      have hmul := mul_le_mul_of_nonneg_left hgap' hnpos.le
      have h5 : δ * ((1 / n) * (∑ x, (v x)^2))
          ≤ (1 / n) * ((∑ x, (v x)^2) - ∑ x, ∑ y, v x * kernel G x y * v y) :=
        le_of_mul_le_mul_left hmul hnpos
      field_simp at h5
      exact h5
    linarith

def regularKernel (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (x y : V) : ℝ :=
  if G.Adj x y then d⁻¹ else 0

/-- The regular kernel has nonnegative entries when its degree parameter is positive. -/
theorem regularKernel_nonneg {d : ℝ} (hdpos : 0 < d) (x y : V) :
    0 ≤ regularKernel G d x y := by
  unfold regularKernel
  by_cases h : G.Adj x y
  · simp only [h, ite_true]
    exact le_of_lt (inv_pos.mpr hdpos)
  · simp only [h, ite_false]
    exact le_rfl

/-- Each row of the regular kernel sums to one for a regular graph of positive degree. -/
theorem regularKernel_sum {d : ℝ} (hd : IsDegreeRegular G d) (hdpos : 0 < d) (x : V) :
    ∑ y, regularKernel G d x y = 1 := by
  have hdeg : degree G x = d := hd x
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hsplit : (∑ y, regularKernel G d x y)
      = d⁻¹ * (∑ y, if G.Adj x y then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h : G.Adj x y
    · simp [regularKernel, h]
    · simp [regularKernel, h]
  have hsum : (∑ y, if G.Adj x y then (1 : ℝ) else 0) = degree G x := by
    rw [← neighborCount_eq_degree G x]
    simp [neighborCount, adjWeight]
  rw [hsplit, hsum, hdeg]
  exact inv_mul_cancel₀ hdne

/-- The regular kernel is symmetric for every real degree parameter. -/
theorem regularKernel_symm (d : ℝ) (x y : V) :
    regularKernel G d x y = regularKernel G d y x := by
  unfold regularKernel
  by_cases h : G.Adj x y
  · have h' : G.Adj y x := G.adj_symm h
    simp [h, h']
  · have h' : ¬ G.Adj y x := fun hh => h (G.adj_symm hh)
    simp [h, h']

/-- For a graph of positive regular degree, the lazy kernel is half the identity plus half the
regular kernel. -/
theorem kernel_eq_half_add_regularKernel {d : ℝ} (hd : IsDegreeRegular G d)
    (hdpos : 0 < d) (x y : V) :
    kernel G x y = (if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * regularKernel G d x y := by
  have hdx : degree G x = d := hd x
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hdxne : degree G x ≠ 0 := by rw [hdx]; exact hdne
  have hloop : ¬ G.Adj x x := G.loopless.irrefl x
  by_cases hxy : x = y
  · subst hxy
    have hk : kernel G x x = (1 / 2 : ℝ) := by
      rw [kernel, ite_eq_right hdxne, ite_eq_left rfl, ite_eq_right hloop]
      norm_num
    have hr : regularKernel G d x x = 0 := by
      rw [regularKernel, ite_eq_right hloop]
    rw [hk, hr]
    norm_num
  · by_cases hadj : G.Adj x y
    · have hk : kernel G x y = (1 / 2) * regularKernel G d x y := by
        rw [kernel, ite_eq_right hdxne, ite_eq_right hxy, ite_eq_left hadj]
        rw [regularKernel, ite_eq_left hadj]
        have h1 : (1 / (2 * d) : ℝ) = (1 / 2) * d⁻¹ := by field_simp [hdne]
        rw [hdx, h1]
        ring
      rw [hk, ite_eq_right hxy]
      ring
    · have hk : kernel G x y = 0 := by
        rw [kernel, ite_eq_right hdxne, ite_eq_right hxy, ite_eq_right hadj]
        norm_num
      have hr : regularKernel G d x y = 0 := by
        rw [regularKernel, ite_eq_right hadj]
      rw [hk, hr, ite_eq_right hxy]
      norm_num

/-- For a regular graph of positive degree, a lazy chain gap at most one gives twice that gap
for the regular kernel. -/
theorem symmetricChainGap_regularKernel {d δ : ℝ} (hd : IsDegreeRegular G d)
    (hdpos : 0 < d) (hn : 0 < (Fintype.card V : ℝ)) (hvol : volume G ≠ 0)
    (hδ : δ ≤ 1) (hgap : LazyChainGap G δ) :
    SymmetricChainGap (regularKernel G d) (2 * δ) := by
  refine ⟨⟨regularKernel_nonneg G hdpos, ?_⟩, regularKernel_symm G d, ?_⟩
  · intro x
    exact regularKernel_sum G hd hdpos x
  · intro v hvsum
    have hsym := symmetricChainGap_of_regular G hd hn hvol hδ hgap
    have hK : (∑ x, ∑ y, v x * kernel G x y * v y)
        ≤ (1 - δ) * (∑ x, (v x)^2) := hsym.2.2 v hvsum
    have hrel : (∑ x, ∑ y, v x * kernel G x y * v y)
        = (1 / 2) * (∑ x, (v x)^2)
          + (1 / 2) * (∑ x, ∑ y, v x * regularKernel G d x y * v y) := by
      have hpt : ∀ x y : V, kernel G x y
          = (if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * regularKernel G d x y :=
        kernel_eq_half_add_regularKernel G hd hdpos
      have hstep : (∑ x, ∑ y, v x * kernel G x y * v y)
          = ∑ x, ∑ y, v x
              * ((if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * regularKernel G d x y) * v y := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [hpt]
      rw [hstep]
      have hsplit : ∀ x : V,
          (∑ y, v x
              * ((if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * regularKernel G d x y) * v y)
          = (∑ y, v x * (if x = y then (1 / 2 : ℝ) else 0) * v y)
            + (∑ y, v x * ((1 / 2) * regularKernel G d x y) * v y) := by
        intro x
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring
      have h1 : ∀ x : V, (∑ y, v x * (if x = y then (1 / 2 : ℝ) else 0) * v y)
          = (1 / 2) * (v x)^2 := by
        intro x
        rw [Finset.sum_eq_single x]
        · rw [ite_eq_left rfl]
          ring
        · intro y _ hy
          rw [ite_eq_right (Ne.symm hy)]
          ring
        · intro hcon
          exact absurd (Finset.mem_univ _) hcon
      have h2 : ∀ x : V, (∑ y, v x * ((1 / 2) * regularKernel G d x y) * v y)
          = (1 / 2) * (∑ y, v x * regularKernel G d x y * v y) := by
        intro x
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      calc
        (∑ x, (∑ y, v x
              * ((if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * regularKernel G d x y) * v y))
            = ∑ x, ((1 / 2) * (v x)^2
                + (1 / 2) * (∑ y, v x * regularKernel G d x y * v y)) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [hsplit x, h1 x, h2 x]
        _ = (1 / 2) * (∑ x, (v x)^2)
            + (1 / 2) * (∑ x, ∑ y, v x * regularKernel G d x y * v y) := by
              have e1 : (1 / 2) * (∑ x, (v x)^2) = ∑ x, (1 / 2) * (v x)^2 :=
                Finset.mul_sum _ _ _
              have e2 : (1 / 2) * (∑ x, ∑ y, v x * regularKernel G d x y * v y)
                  = ∑ x, (1 / 2) * (∑ y, v x * regularKernel G d x y * v y) :=
                Finset.mul_sum _ _ _
              have e3 : (∑ x, (1 / 2) * (v x)^2)
                    + (∑ x, (1 / 2) * (∑ y, v x * regularKernel G d x y * v y))
                  = ∑ x, ((1 / 2) * (v x)^2
                      + (1 / 2) * (∑ y, v x * regularKernel G d x y * v y)) := by
                rw [Finset.sum_add_distrib]
              rw [e1, e2, e3]
    have hL : (∑ x, ∑ y, v x * regularKernel G d x y * v y)
        = 2 * (∑ x, ∑ y, v x * kernel G x y * v y) - (∑ x, (v x)^2) := by
      linarith [hrel]
    linarith [hK, hL]

def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b
  symm := ⟨fun a b h => h.symm⟩
  loopless := ⟨fun a h => h rfl⟩

instance (n : ℕ) : DecidableRel (completeGraph n).Adj := fun _ _ => by
  unfold completeGraph SimpleGraph.Adj
  infer_instance

/-- The sum of a constant over `Fin n` is `n` times that constant. -/
lemma sum_const_card (n : ℕ) (c : ℝ) : (∑ _ : Fin n, c) = (n : ℝ) * c := by
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]

/-- Every vertex of the complete graph on at least two vertices has degree one less than its
vertex count. -/
lemma completeGraph_degree (n : ℕ) (hn : 2 ≤ n) (x : Fin n) :
    degree (completeGraph n) x = (n : ℝ) - 1 := by
  have hone : (∑ y : Fin n, if y = x then (1 : ℝ) else 0) = 1 := by
    rw [Fintype.sum_ite_eq']
  have hsum : (∑ y : Fin n, if (completeGraph n).Adj x y then (1 : ℝ) else 0)
      = (∑ y : Fin n, (1 : ℝ)) - 1 := by
    calc
      (∑ y : Fin n, if (completeGraph n).Adj x y then (1 : ℝ) else 0)
          = ∑ y : Fin n, if x ≠ y then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases h : x = y
            · simp [completeGraph, h]
            · simp [completeGraph, h]
      _ = ∑ y : Fin n, ((1 : ℝ) - if y = x then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases h : y = x
            · simp [h]
            · have h' : x ≠ y := fun e => h e.symm
              simp [h, h']
      _ = (∑ y : Fin n, (1 : ℝ)) - ∑ y : Fin n, if y = x then (1 : ℝ) else 0 := by
            rw [← Finset.sum_sub_distrib]
      _ = (∑ y : Fin n, (1 : ℝ)) - 1 := by rw [hone]
  rw [degree, hsum, sum_const_card]
  have h1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    calc
      ((n - 1 : ℕ) : ℝ) + 1 = ((n - 1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by norm_num
      _ = ((n - 1 + 1 : ℕ) : ℝ) := by rw [Nat.cast_add]
      _ = (n : ℝ) := by congr 1; omega
  linarith

/-- The volume of a complete graph on at least two vertices is its vertex count times one less
than that count. -/
lemma completeGraph_volume (n : ℕ) (hn : 2 ≤ n) :
    volume (completeGraph n) = (n : ℝ) * ((n : ℝ) - 1) := by
  unfold volume
  rw [Finset.sum_congr rfl (fun x _ => completeGraph_degree n hn x)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]

/-- The stationary distribution of a complete graph on at least two vertices is uniform. -/
lemma completeGraph_stationary (n : ℕ) (hn : 2 ≤ n) (x : Fin n) :
    stationary (completeGraph n) x = 1 / (n : ℝ) := by
  have hvol : volume (completeGraph n) ≠ 0 := by
    rw [completeGraph_volume n hn]
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
    nlinarith
  simp only [stationary, hvol, ite_false]
  rw [completeGraph_degree n hn x, completeGraph_volume n hn]
  have h1 : ((n : ℝ) - 1) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp

/-- The complete graph's edge quadratic form is twice the vertex count times the sum of squares
minus twice the square of the sum. -/
lemma completeGraph_edgeForm (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ) :
    (∑ x, ∑ y, (if (completeGraph n).Adj x y then (f x - f y)^2 else 0))
      = 2 * ((n : ℝ) * (∑ x, f x ^ 2) - (∑ x, f x) ^ 2) := by
  calc
    (∑ x, ∑ y, (if (completeGraph n).Adj x y then (f x - f y)^2 else 0))
        = ∑ x, ∑ y, (if x ≠ y then (f x - f y)^2 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : x = y
          · simp [completeGraph, h]
          · simp [completeGraph, h]
    _ = ∑ x, ∑ y, (f x - f y)^2 := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases h : x = y
          · simp [h]
          · simp [h]
    _ = 2 * ((n : ℝ) * (∑ x, f x ^ 2) - (∑ x, f x) ^ 2) := by
          have h1 : (∑ x, ∑ y, (f x - f y)^2)
              = 2 * ((n : ℝ) * (∑ x, f x ^ 2) - (∑ x, f x) ^ 2) := by
            have hstep : ∀ x : Fin n, (∑ y : Fin n, (f x - f y)^2)
                = (∑ y : Fin n, f x ^ 2) - 2 * (∑ y : Fin n, f x * f y)
                  + (∑ y : Fin n, f y ^ 2) := by
              intro x
              calc
                (∑ y, (f x - f y)^2) = ∑ y, (f x ^ 2 - 2 * (f x * f y) + f y ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro y _
                  ring
                _ = (∑ y, f x ^ 2) - 2 * (∑ y, f x * f y) + (∑ y, f y ^ 2) := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
            have houter : (∑ x : Fin n, ∑ y : Fin n, (f x - f y)^2)
                = (∑ x : Fin n, (∑ y : Fin n, f x ^ 2))
                  - 2 * (∑ x : Fin n, (∑ y : Fin n, f x * f y))
                  + (∑ x : Fin n, (∑ y : Fin n, f y ^ 2)) := by
              have h1 : (∑ x : Fin n, ∑ y : Fin n, (f x - f y)^2)
                  = ∑ x : Fin n, ((∑ y : Fin n, f x ^ 2) - 2 * (∑ y : Fin n, f x * f y)
                      + (∑ y : Fin n, f y ^ 2)) := by
                apply Finset.sum_congr rfl
                intro x _
                rw [hstep x]
              rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
            have hA : (∑ x : Fin n, ∑ y : Fin n, f x ^ 2) = (n : ℝ) * (∑ x : Fin n, f x ^ 2) := by
              calc
                (∑ x : Fin n, ∑ y : Fin n, f x ^ 2) = ∑ x : Fin n, (∑ y : Fin n, f x ^ 2) := rfl
                _ = ∑ x : Fin n, ((n : ℝ) * f x ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [sum_const_card]
                _ = (n : ℝ) * (∑ x : Fin n, f x ^ 2) := by rw [Finset.mul_sum]
            have hB : (∑ x : Fin n, ∑ y : Fin n, f x * f y)
                = (∑ x : Fin n, f x) * (∑ y : Fin n, f y) := by
              calc
                (∑ x : Fin n, ∑ y : Fin n, f x * f y) = ∑ x : Fin n, f x * (∑ y : Fin n, f y) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [Finset.mul_sum]
                _ = ∑ x : Fin n, ((∑ y : Fin n, f y) * f x) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
                _ = (∑ y : Fin n, f y) * (∑ x : Fin n, f x) := by rw [Finset.mul_sum]
            have hC : (∑ x : Fin n, ∑ y : Fin n, f y ^ 2) = (n : ℝ) * (∑ x : Fin n, f x ^ 2) := by
              calc
                (∑ x : Fin n, ∑ y : Fin n, f y ^ 2) = ∑ y : Fin n, (∑ x : Fin n, f y ^ 2) := by
                  rw [Finset.sum_comm]
                _ = ∑ y : Fin n, ((n : ℝ) * f y ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro y _
                  rw [sum_const_card]
                _ = (n : ℝ) * (∑ y : Fin n, f y ^ 2) := by rw [Finset.mul_sum]
            rw [houter, hA, hB, hC]
            ring
          exact h1

/-- Computes the complete graph energy as the vertex count times the sum of squares minus the
square of the sum, divided by twice the graph volume. -/
lemma completeGraph_energy (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ) :
    energy (completeGraph n) f
      = ((n : ℝ) * (∑ x, f x ^ 2) - (∑ x, f x) ^ 2) / (2 * (n : ℝ) * ((n : ℝ) - 1)) := by
  have hvol : volume (completeGraph n) ≠ 0 := by
    rw [completeGraph_volume n hn]
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
    nlinarith
  rw [energy_eq_quarter_edgeForm (completeGraph n) hvol f, completeGraph_edgeForm n hn f]
  rw [completeGraph_volume n hn]
  field_simp
  ring

/-- For a mean-zero function on a complete graph, energy is the sum of squares divided by twice
the difference between the vertex count and one. -/
lemma completeGraph_energy_mean_zero (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ)
    (hmean : mean (completeGraph n) f = 0) :
    energy (completeGraph n) f = (1 / (2 * ((n : ℝ) - 1))) * (∑ x, f x ^ 2) := by
  have hsum0 : (∑ x, f x) = 0 := by
    have h1 : mean (completeGraph n) f = (1 / (n : ℝ)) * (∑ x, f x) := by
      unfold mean
      simp_rw [completeGraph_stationary n hn]
      rw [Finset.mul_sum]
    rw [h1] at hmean
    have hne : (1 / (n : ℝ) : ℝ) ≠ 0 := by
      have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    exact (mul_eq_zero.mp hmean).resolve_left hne
  rw [completeGraph_energy n hn f, hsum0]
  field_simp
  ring

/-- For a mean-zero function on a complete graph, variance is the average of the squared values. -/
lemma completeGraph_variance_mean_zero (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ)
    (hmean : mean (completeGraph n) f = 0) :
    variance (completeGraph n) f = (1 / (n : ℝ)) * (∑ x, f x ^ 2) := by
  unfold variance
  simp_rw [completeGraph_stationary n hn, hmean]
  rw [← Finset.mul_sum]
  ring

/-- A complete graph on at least two vertices satisfies `LazyChainGap` with parameter given by
the vertex count divided by twice its difference from one. -/
theorem complete_graph_lazyChainGap (n : ℕ) (hn : 2 ≤ n) :
    LazyChainGap (completeGraph n) ((n : ℝ) / (2 * ((n : ℝ) - 1))) := by
  intro f hmean hδ
  have henergy := completeGraph_energy_mean_zero n hn f hmean
  have hvar := completeGraph_variance_mean_zero n hn f hmean
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
  have hne : ((n : ℝ) - 1) ≠ 0 := by linarith
  have heq : ((n : ℝ) / (2 * ((n : ℝ) - 1))) * (1 / (n : ℝ)) = 1 / (2 * ((n : ℝ) - 1)) := by
    field_simp
  calc
    ((n : ℝ) / (2 * ((n : ℝ) - 1))) * variance (completeGraph n) f
        = ((n : ℝ) / (2 * ((n : ℝ) - 1))) * ((1 / (n : ℝ)) * (∑ x, f x ^ 2)) := by rw [hvar]
    _ = (((n : ℝ) / (2 * ((n : ℝ) - 1))) * (1 / (n : ℝ))) * (∑ x, f x ^ 2) := by ring
    _ = (1 / (2 * ((n : ℝ) - 1))) * (∑ x, f x ^ 2) := by rw [heq]
    _ ≤ energy (completeGraph n) f := by rw [henergy]

/-- The stated complete graph gap parameter is at least one half when there are at least two
vertices. -/
lemma complete_graph_gap_ge_half (n : ℕ) (hn : 2 ≤ n) :
    (1 / 2 : ℝ) ≤ (n : ℝ) / (2 * ((n : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (1 : ℝ) ≤ ((n : ℝ) - 1) := by linarith
  have hne : ((n : ℝ) - 1) ≠ 0 := by linarith
  rw [le_div_iff₀ (by positivity : 0 < 2 * ((n : ℝ) - 1))]
  linarith

/-- The complete graph on at least two vertices is regular of degree one less than its vertex
count. -/
lemma completeGraph_isDegreeRegular (n : ℕ) (hn : 2 ≤ n) :
    IsDegreeRegular (completeGraph n) ((n : ℝ) - 1) := by
  intro x
  exact completeGraph_degree n hn x

/-- On a connected graph of nonzero volume, a mean-zero function with zero energy vanishes
everywhere. -/
theorem connected_no_zero_energy_mean_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hvol : volume G ≠ 0) (hconn : ∀ x y : V, G.Reachable x y)
    (f : V → ℝ) (hmean : mean G f = 0) (henergy : energy G f = 0) :
    ∀ x, f x = 0 := by
  have hform := energy_eq_quarter_edgeForm G hvol f
  have hS : (1 / (4 * volume G) : ℝ)
      * (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) = 0 := by
    rw [← hform, henergy]
  have hsum0 : (∑ x, ∑ y, (if G.Adj x y then (f x - f y)^2 else 0)) = 0 := by
    rcases mul_eq_zero.mp hS with h | h
    · have hne : (1 / (4 * volume G) : ℝ) ≠ 0 :=
        div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hvol)
      exact (hne h).elim
    · exact h
  have hnonneg : ∀ (x : V) (z : V),
      0 ≤ (if G.Adj x z then (f x - f z)^2 else 0) := by
    intro x z
    split_ifs <;> positivity
  have hedge : ∀ x y : V, G.Adj x y → f x = f y := by
    intro x y hadj
    have hinner : (∑ z, (if G.Adj x z then (f x - f z)^2 else 0)) = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset V))
        (f := fun z => ∑ w, (if G.Adj z w then (f z - f w)^2 else 0))
        (fun z _ => Finset.sum_nonneg (fun w _ => hnonneg z w))).1 hsum0 x (Finset.mem_univ x)
      exact h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (s := (Finset.univ : Finset V))
      (f := fun z => if G.Adj x z then (f x - f z)^2 else 0)
      (fun z _ => hnonneg x z)).1 hinner y (Finset.mem_univ y)
    have hsq : (f x - f y)^2 = 0 := by simpa [hadj] using! hz
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hconst : ∀ {x y : V} (p : G.Walk x y), f x = f y := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hedge _ _ h).trans ih
  have hreach : ∀ x y : V, G.Reachable x y → f x = f y := by
    intro x y hr
    exact hr.elim (fun p => hconst p)
  have hall : ∀ x y : V, f x = f y := fun x y => hreach x y (hconn x y)
  obtain ⟨y0⟩ := (inferInstance : Nonempty V)
  have hmean' : mean G f = f y0 := by
    unfold mean
    calc
      (∑ x, stationary G x * f x) = ∑ x, stationary G x * f y0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hall x y0]
      _ = f y0 * (∑ x, stationary G x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = f y0 := by rw [stationary_sum G, mul_one]
  have hzero : f y0 = 0 := by
    rw [← hmean']
    exact hmean
  intro x
  exact (hall x y0).trans hzero

def cheegerCuts (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter
    (fun S => 0 < mass G S ∧ mass G S ≤ 1/2)

/-- A set belongs to `cheegerCuts` exactly when its mass is positive and at most one half. -/
theorem mem_cheegerCuts (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    S ∈ cheegerCuts G ↔ 0 < mass G S ∧ mass G S ≤ 1/2 := by
  unfold cheegerCuts
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

def graphConductance (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : (cheegerCuts G).Nonempty) : ℝ :=
  ((cheegerCuts G).image (cutConductance G)).min' (Finset.image_nonempty.mpr hne)

/-- Graph conductance is at most the cut conductance of every admissible Cheeger cut. -/
theorem graphConductance_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : (cheegerCuts G).Nonempty) (S : Finset V) (hS : S ∈ cheegerCuts G) :
    graphConductance G hne ≤ cutConductance G S := by
  unfold graphConductance
  exact Finset.min'_le _ (cutConductance G S) (Finset.mem_image_of_mem (cutConductance G) hS)

/-- Some admissible Cheeger cut attains the graph conductance. -/
theorem graphConductance_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : (cheegerCuts G).Nonempty) :
    ∃ S ∈ cheegerCuts G, cutConductance G S = graphConductance G hne := by
  have hmem : graphConductance G hne ∈ (cheegerCuts G).image (cutConductance G) := by
    unfold graphConductance
    exact Finset.min'_mem _ _
  obtain ⟨S, hS, hφ⟩ := Finset.mem_image.mp hmem
  exact ⟨S, hS, hφ⟩

/-- Graph conductance is nonnegative when the family of Cheeger cuts is nonempty. -/
theorem graphConductance_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hne : (cheegerCuts G).Nonempty) : 0 ≤ graphConductance G hne := by
  obtain ⟨S, hS, hφ⟩ := graphConductance_mem G hne
  have hmem : 0 < mass G S ∧ mass G S ≤ 1/2 := (mem_cheegerCuts G S).mp hS
  rw [← hφ]
  unfold cutConductance
  have hflow : 0 ≤ flow G S := by
    unfold flow
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (stationary_nonneg G x) (kernel_nonneg G x y)
  exact div_nonneg hflow (le_of_lt hmem.1)

/-- A nonempty family of Cheeger cuts yields a mean-zero function with positive variance and
Rayleigh quotient at most twice graph conductance. -/
theorem cheeger_upper_bound_min [Nonempty V] (hne : (cheegerCuts G).Nonempty) :
    ∃ f : V → ℝ, mean G f = 0 ∧ 0 < variance G f ∧
      energy G f / variance G f ≤ 2 * graphConductance G hne := by
  obtain ⟨S, hS, hφ⟩ := graphConductance_mem G hne
  have hmem : 0 < mass G S ∧ mass G S ≤ 1/2 := (mem_cheegerCuts G S).mp hS
  obtain ⟨f, hmean, hvar, henergy⟩ := cheeger_upper_bound G S hmem.1 hmem.2
  refine ⟨f, hmean, hvar, ?_⟩
  rw [← hφ]
  exact henergy

def standardConductance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  edgeBoundary G S / setVolume G S

/-- For nonzero volume and set mass, lazy cut conductance is half the standard conductance. -/
theorem cutConductance_eq_half_standard (hv : volume G ≠ 0) (S : Finset V)
    (hmass : mass G S ≠ 0) :
    cutConductance G S = (1 / 2) * standardConductance G S := by
  have hsetvol : setVolume G S ≠ 0 := by
    intro h
    have : mass G S = 0 := by rw [mass_eq_setVolume G hv S, h, zero_div]
    exact hmass this
  rw [cutConductance_eq_edgeBoundary_ratio G hv S hmass]
  unfold standardConductance
  field_simp

/-- A singleton vertex of positive degree has cut conductance one half when graph volume is
nonzero. -/
theorem cutConductance_singleton (hv : volume G ≠ 0) (x : V) (hx : 0 < degree G x) :
    cutConductance G {x} = 1 / 2 := by
  have hset : setVolume G {x} = degree G x := by
    unfold setVolume
    rw [Finset.sum_singleton]
  have hmass : mass G {x} ≠ 0 := by
    rw [mass_eq_setVolume G hv {x}, hset]
    exact div_ne_zero (ne_of_gt hx) hv
  rw [cutConductance_eq_edgeBoundary_ratio G hv {x} hmass, hset]
  have hboundary : edgeBoundary G {x} = degree G x := by
    unfold edgeBoundary
    rw [Finset.sum_singleton]
    have herase : ((Finset.univ : Finset V).erase x) = ({x} : Finset V)ᶜ := by
      ext y
      simp
    rw [← herase]
    have hsum := Finset.sum_erase_add (Finset.univ : Finset V)
      (fun y => if G.Adj x y then (1 : ℝ) else 0) (Finset.mem_univ x)
    have hxx : (if G.Adj x x then (1 : ℝ) else 0) = 0 := by
      rw [ite_eq_right (G.loopless.irrefl x)]
    calc
      (∑ y ∈ (Finset.univ : Finset V).erase x, (if G.Adj x y then (1 : ℝ) else 0))
          = (∑ y ∈ (Finset.univ : Finset V), (if G.Adj x y then (1 : ℝ) else 0))
              - (if G.Adj x x then (1 : ℝ) else 0) := by linarith
      _ = degree G x := by
        rw [show (∑ y ∈ (Finset.univ : Finset V), (if G.Adj x y then (1 : ℝ) else 0))
            = ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) from rfl]
        rw [hxx, sub_zero]
        rw [← neighborCount_eq_degree G x]
        rfl
  rw [hboundary]
  field_simp

section BipartiteFamily

variable (a : ℕ)

/-- The sum of the indicator of indices below `m` in `Fin n` is `m` when `m` is at most `n`. -/
lemma sum_ite_val_lt_fin (n m : ℕ) (hmn : m ≤ n) :
    (∑ y : Fin n, if y.val < m then (1 : ℝ) else 0) = (m : ℝ) := by
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun y => y.val < m)).card = m := by
    have himg : ((Finset.univ : Finset (Fin n)).filter (fun y => y.val < m)).image Fin.val
        = Finset.range m := by
      ext i
      rw [Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨y, hy, h⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have hval : i = y.val := h.symm
        rw [hval]
        exact hy
      · intro hi
        refine ⟨⟨i, by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hi
        · rfl
    rw [← Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin n)).filter
      (fun y => y.val < m)) (fun x y h => Fin.ext h)]
    rw [himg, Finset.card_range m]
  rw [Finset.sum_boole (p := fun y => y.val < m) (s := (Finset.univ : Finset (Fin n)))]
  exact_mod_cast hcard

/-- The sum of the indicator of indices at least `m` in `Fin n` is the natural difference of `n`
and `m`. -/
lemma sum_ite_val_ge_fin (n m : ℕ) (hmn : m ≤ n) :
    (∑ y : Fin n, if m ≤ y.val then (1 : ℝ) else 0) = ((n - m : ℕ) : ℝ) := by
  have hmain : ∀ y : Fin n, (if m ≤ y.val then (1 : ℝ) else 0)
      + (if y.val < m then (1 : ℝ) else 0) = 1 := by
    intro y
    by_cases h1 : y.val < m
    · have h2 : ¬m ≤ y.val := by omega
      simp [h1, h2]
    · have h2 : m ≤ y.val := by omega
      simp [h1, h2]
  have h1 : (∑ y : Fin n, (if m ≤ y.val then (1 : ℝ) else 0))
      + (∑ y : Fin n, (if y.val < m then (1 : ℝ) else 0))
        = (∑ y : Fin n, (1 : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    exact hmain y
  have h2 : (∑ y : Fin n, (1 : ℝ)) = (n : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h3 := sum_ite_val_lt_fin n m hmn
  have h5 : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := Nat.cast_sub hmn
  rw [h5]
  linarith

/-- The bipartite half size is positive for a positive exponent. -/
lemma bipartiteHalf_pos (ha : 0 < a) : 0 < bipartiteHalf a := by
  unfold bipartiteHalf
  positivity

/-- For a positive exponent, two bipartite half sizes sum to the full vertex count. -/
lemma bipartiteHalf_add (ha : 0 < a) : bipartiteHalf a + bipartiteHalf a = 2 ^ a := by
  unfold bipartiteHalf
  have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
    have h1 : 2 ^ (a - 1) * 2 = 2 ^ (a - 1 + 1) := by rw [Nat.pow_succ]
    rw [h1, show a - 1 + 1 = a from by omega]
  rw [← Nat.mul_two, hpow]

/-- For a positive exponent, the bipartite half size is less than the full vertex count. -/
lemma bipartiteHalf_lt (ha : 0 < a) : bipartiteHalf a < 2 ^ a := by
  unfold bipartiteHalf
  have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
    have h1 : 2 ^ (a - 1) * 2 = 2 ^ (a - 1 + 1) := by rw [Nat.pow_succ]
    rw [h1, show a - 1 + 1 = a from by omega]
  have hpos : 0 < 2 ^ (a - 1) := by positivity
  have h := Nat.mul_lt_mul_of_pos_left (show (1 : ℕ) < 2 by omega) hpos
  have h' : 2 ^ (a - 1) < 2 ^ (a - 1) * 2 := by
    calc 2 ^ (a - 1) = 2 ^ (a - 1) * 1 := by ring
      _ < 2 ^ (a - 1) * 2 := by exact Nat.mul_lt_mul_of_pos_left (show (1 : ℕ) < 2 by omega) hpos
  rwa [hpow] at h'

/-- Two vertices of `bipartiteGraph` are adjacent exactly when they lie in opposite halves. -/
lemma bipartiteAdj_iff' (x y : Fin (2 ^ a)) :
    (bipartiteGraph a).Adj x y ↔
      ((x.val < bipartiteHalf a ∧ ¬(y.val < bipartiteHalf a))
        ∨ (¬(x.val < bipartiteHalf a) ∧ y.val < bipartiteHalf a)) := by
  show bipartiteAdj a x y = true ↔ _
  by_cases hx : x.val < bipartiteHalf a <;> by_cases hy : y.val < bipartiteHalf a <;>
    simp [bipartiteAdj, hx, hy]

/-- A vertex in the lower half is adjacent exactly to vertices in the upper half. -/
lemma bipartiteAdj_lower (x y : Fin (2 ^ a)) (hx : x.val < bipartiteHalf a) :
    (bipartiteGraph a).Adj x y ↔ bipartiteHalf a ≤ y.val := by
  rw [bipartiteAdj_iff' a x y]
  constructor
  · intro h
    rcases h with h | h
    · have hne : ¬(y.val < bipartiteHalf a) := h.2
      omega
    · exact (h.1 hx).elim
  · intro h
    have hne : ¬(y.val < bipartiteHalf a) := by omega
    exact Or.inl ⟨hx, hne⟩

/-- A vertex outside the lower half is adjacent exactly to vertices in the lower half. -/
lemma bipartiteAdj_upper (x y : Fin (2 ^ a)) (hx : ¬(x.val < bipartiteHalf a)) :
    (bipartiteGraph a).Adj x y ↔ y.val < bipartiteHalf a := by
  rw [bipartiteAdj_iff' a x y]
  constructor
  · intro h
    rcases h with h | h
    · exact (hx h.1).elim
    · exact h.2
  · intro h
    exact Or.inr ⟨hx, h⟩

/-- For positive `a`, every vertex of `bipartiteGraph` has degree two raised to one less than
`a`. -/
lemma bipartiteGraph_degree (ha : 0 < a) (x : Fin (2 ^ a)) :
    degree (bipartiteGraph a) x = ((2 ^ (a - 1) : ℕ) : ℝ) := by
  rw [Qatlib.Concepts.GraphLaplacian.LaplacianPsd.degree_eq_mathlib]
  rw [(bipartiteGraph a).degree_eq_sum_if_adj (R := ℝ)]
  have hm : bipartiteHalf a ≤ 2 ^ a := by
    have := bipartiteHalf_lt a ha
    omega
  have hsumL : ∀ x : Fin (2 ^ a), x.val < bipartiteHalf a →
      (∑ y : Fin (2 ^ a), if (bipartiteGraph a).Adj x y then (1 : ℝ) else 0)
        = (∑ y : Fin (2 ^ a), if bipartiteHalf a ≤ y.val then (1 : ℝ) else 0) := by
    intro x hx
    apply Finset.sum_congr rfl
    intro y _
    have hiff := bipartiteAdj_lower a x y hx
    by_cases h : (bipartiteGraph a).Adj x y
    · simp [h, (hiff).mp h]
    · simp [h, hiff.not.mp h]
  have hsumU : ∀ x : Fin (2 ^ a), ¬(x.val < bipartiteHalf a) →
      (∑ y : Fin (2 ^ a), if (bipartiteGraph a).Adj x y then (1 : ℝ) else 0)
        = (∑ y : Fin (2 ^ a), if y.val < bipartiteHalf a then (1 : ℝ) else 0) := by
    intro x hx
    apply Finset.sum_congr rfl
    intro y _
    have hiff := bipartiteAdj_upper a x y hx
    by_cases h : (bipartiteGraph a).Adj x y
    · simp [h, (hiff).mp h]
    · simp [h, hiff.not.mp h]
  by_cases hx : x.val < bipartiteHalf a
  · rw [hsumL x hx, sum_ite_val_ge_fin (2 ^ a) (bipartiteHalf a) hm]
    have htwo : 2 ^ a - bipartiteHalf a = bipartiteHalf a := by
      unfold bipartiteHalf
      have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
        have h1 : 2 ^ (a - 1) * 2 = 2 ^ (a - 1 + 1) := by rw [Nat.pow_succ]
        rw [h1, show a - 1 + 1 = a from by omega]
      have h1 : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [Nat.mul_two]
      omega
    rw [htwo]
    rfl
  · rw [hsumU x hx, sum_ite_val_lt_fin (2 ^ a) (bipartiteHalf a) hm]
    rfl

/-- For positive `a`, `bipartiteGraph` is regular of degree two raised to one less than `a`. -/
lemma bipartiteGraph_isDegreeRegular (ha : 0 < a) :
    IsDegreeRegular (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ) := by
  intro x
  exact bipartiteGraph_degree a ha x

/-- The bipartite graph volume is its vertex count times its half size for positive `a`. -/
lemma bipartiteGraph_volume (ha : 0 < a) :
    volume (bipartiteGraph a) = ((2 ^ a : ℕ) : ℝ) * ((2 ^ (a - 1) : ℕ) : ℝ) := by
  unfold volume
  calc
    (∑ x, degree (bipartiteGraph a) x) = ∑ x, ((2 ^ (a - 1) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro x _
      exact bipartiteGraph_degree a ha x
    _ = ((2 ^ a : ℕ) : ℝ) * ((2 ^ (a - 1) : ℕ) : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The bipartite graph has uniform stationary weights for positive `a`. -/
lemma bipartiteGraph_stationary (ha : 0 < a) (x : Fin (2 ^ a)) :
    stationary (bipartiteGraph a) x = ((2 ^ a : ℕ) : ℝ)⁻¹ := by
  unfold stationary
  have hv : volume (bipartiteGraph a) ≠ 0 := by
    rw [bipartiteGraph_volume a ha]
    positivity
  simp only [ite_eq_right hv]
  rw [bipartiteGraph_degree a ha x, bipartiteGraph_volume a ha]
  have hne : ((2 ^ (a - 1) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- For positive `a`, the bipartite graph mean is the uniform average of the function values. -/
lemma bipartiteGraph_mean (ha : 0 < a) (f : Fin (2 ^ a) → ℝ) :
    mean (bipartiteGraph a) f = ((2 ^ a : ℕ) : ℝ)⁻¹ * (∑ x, f x) := by
  unfold mean
  calc
    (∑ x, stationary (bipartiteGraph a) x * f x)
        = ∑ x, ((2 ^ a : ℕ) : ℝ)⁻¹ * f x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [bipartiteGraph_stationary a ha x]
    _ = ((2 ^ a : ℕ) : ℝ)⁻¹ * (∑ x, f x) := by rw [Finset.mul_sum]

/-- For positive `a`, a function has zero bipartite graph mean exactly when its values sum to
zero. -/
lemma bipartiteGraph_mean_zero_iff (ha : 0 < a) (f : Fin (2 ^ a) → ℝ) :
    mean (bipartiteGraph a) f = 0 ↔ (∑ x, f x) = 0 := by
  have hne : ((2 ^ a : ℕ) : ℝ) ≠ 0 := by positivity
  rw [bipartiteGraph_mean a ha f]
  constructor
  · intro h
    have h0 : ((2 ^ a : ℕ) : ℝ)⁻¹ * (∑ x, f x) = 0 := h
    have hne2 : ((2 ^ a : ℕ) : ℝ)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_left hne2
  · intro h
    rw [h, mul_zero]

def bipartiteLowerSum (f : Fin (2 ^ a) → ℝ) : ℝ :=
  ∑ x, if x.val < bipartiteHalf a then f x else 0

def bipartiteUpperSum (f : Fin (2 ^ a) → ℝ) : ℝ :=
  ∑ x, if bipartiteHalf a ≤ x.val then f x else 0

/-- The lower-half sum equals the finite sum over `bipartiteLower`. -/
lemma bipartiteLowerSum_eq (f : Fin (2 ^ a) → ℝ) :
    bipartiteLowerSum a f = ∑ x ∈ bipartiteLower a, f x := by
  unfold bipartiteLowerSum bipartiteLower
  exact (Finset.sum_filter (s := (Finset.univ : Finset (Fin (2 ^ a))))
    (p := fun x => x.val < bipartiteHalf a) f).symm

/-- The upper-half sum equals the finite sum over `bipartiteUpper`. -/
lemma bipartiteUpperSum_eq (f : Fin (2 ^ a) → ℝ) :
    bipartiteUpperSum a f = ∑ x ∈ bipartiteUpper a, f x := by
  unfold bipartiteUpperSum bipartiteUpper
  exact (Finset.sum_filter (s := (Finset.univ : Finset (Fin (2 ^ a))))
    (p := fun x => bipartiteHalf a ≤ x.val) f).symm

/-- The total sum splits into the lower-half and upper-half sums. -/
lemma bipartiteSum_eq (f : Fin (2 ^ a) → ℝ) :
    (∑ x, f x) = bipartiteLowerSum a f + bipartiteUpperSum a f := by
  have hmain : ∀ x : Fin (2 ^ a), f x
      = (if x.val < bipartiteHalf a then f x else 0)
        + (if bipartiteHalf a ≤ x.val then f x else 0) := by
    intro x
    by_cases h : x.val < bipartiteHalf a
    · have hne : ¬(bipartiteHalf a ≤ x.val) := by omega
      simp [h, hne]
    · have hle : bipartiteHalf a ≤ x.val := by omega
      simp [h, hle]
  unfold bipartiteLowerSum bipartiteUpperSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  exact hmain x

/-- The bipartite adjacency quadratic form is twice the product of the two half sums. -/
lemma bipartiteGraph_adj_form (f : Fin (2 ^ a) → ℝ) :
    (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then f x * f y else 0))
      = 2 * bipartiteLowerSum a f * bipartiteUpperSum a f := by
  have hinner : ∀ x : Fin (2 ^ a),
      (∑ y, (if (bipartiteGraph a).Adj x y then f y else 0))
        = if x.val < bipartiteHalf a then bipartiteUpperSum a f
          else bipartiteLowerSum a f := by
    intro x
    by_cases hx : x.val < bipartiteHalf a
    · have hsum : (∑ y, (if (bipartiteGraph a).Adj x y then f y else 0))
          = ∑ y, (if bipartiteHalf a ≤ y.val then f y else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        have hiff := bipartiteAdj_lower a x y hx
        by_cases h : (bipartiteGraph a).Adj x y
        · simp [h, (hiff).mp h]
        · simp [h, hiff.not.mp h]
      rw [hsum, ite_eq_left hx]
      rfl
    · have hsum : (∑ y, (if (bipartiteGraph a).Adj x y then f y else 0))
          = ∑ y, (if y.val < bipartiteHalf a then f y else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        have hiff := bipartiteAdj_upper a x y hx
        by_cases h : (bipartiteGraph a).Adj x y
        · simp [h, (hiff).mp h]
        · simp [h, hiff.not.mp h]
      rw [hsum, ite_eq_right hx]
      rfl
  have hmain : ∀ x : Fin (2 ^ a),
      f x * (if x.val < bipartiteHalf a then bipartiteUpperSum a f
        else bipartiteLowerSum a f)
        = (if x.val < bipartiteHalf a then f x * bipartiteUpperSum a f else 0)
          + (if bipartiteHalf a ≤ x.val then f x * bipartiteLowerSum a f else 0) := by
    intro x
    by_cases h : x.val < bipartiteHalf a
    · have hne : ¬(bipartiteHalf a ≤ x.val) := by omega
      simp [h, hne]
    · have hle : bipartiteHalf a ≤ x.val := by omega
      simp [h, hle]
  have hsplit : (∑ x, (if x.val < bipartiteHalf a then f x * bipartiteUpperSum a f else 0))
      + (∑ x, (if bipartiteHalf a ≤ x.val then f x * bipartiteLowerSum a f else 0))
      = (∑ x, (if x.val < bipartiteHalf a then f x else 0)) * bipartiteUpperSum a f
        + (∑ x, (if bipartiteHalf a ≤ x.val then f x else 0)) * bipartiteLowerSum a f := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_mul]
    rw [Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  calc
    (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then f x * f y else 0))
        = ∑ x, f x * (∑ y, (if (bipartiteGraph a).Adj x y then f y else 0)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          split_ifs <;> ring
    _ = ∑ x, f x * (if x.val < bipartiteHalf a then bipartiteUpperSum a f
          else bipartiteLowerSum a f) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hinner x]
    _ = (∑ x, (if x.val < bipartiteHalf a then f x * bipartiteUpperSum a f else 0))
        + (∑ x, (if bipartiteHalf a ≤ x.val then f x * bipartiteLowerSum a f else 0)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          exact hmain x
    _ = (∑ x, (if x.val < bipartiteHalf a then f x else 0)) * bipartiteUpperSum a f
        + (∑ x, (if bipartiteHalf a ≤ x.val then f x else 0)) * bipartiteLowerSum a f := hsplit
    _ = bipartiteLowerSum a f * bipartiteUpperSum a f
        + bipartiteUpperSum a f * bipartiteLowerSum a f := by
          rw [bipartiteLowerSum, bipartiteUpperSum]
    _ = 2 * bipartiteLowerSum a f * bipartiteUpperSum a f := by ring

/-- Computes the bipartite edge quadratic form from the sum of squares and the product of the
half sums. -/
lemma bipartiteGraph_edgeForm (ha : 0 < a) (f : Fin (2 ^ a) → ℝ) :
    (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then (f x - f y)^2 else 0))
      = 2 * ((2 ^ (a - 1) : ℕ) : ℝ) * (∑ x, (f x)^2)
        - 4 * bipartiteLowerSum a f * bipartiteUpperSum a f := by
  have hform := normalizedLaplacian_quadratic_form (bipartiteGraph a) f
  have hform2 := normalizedLaplacian_form_eq (bipartiteGraph a) f
  have hDA : (1 / 2 : ℝ)
      * (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then (f x - f y)^2 else 0))
      = (∑ x, degree (bipartiteGraph a) x * (f x)^2)
        - (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then f x * f y else 0)) := by
    calc
      (1 / 2 : ℝ)
          * (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then (f x - f y)^2 else 0))
          = (∑ x, ∑ y, degreeScaled (bipartiteGraph a) f x
              * normalizedLaplacian (bipartiteGraph a) x y
              * degreeScaled (bipartiteGraph a) f y) := by rw [hform]
      _ = (∑ x, degree (bipartiteGraph a) x * (f x)^2)
          - (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then f x * f y else 0)) := hform2
  have hdeg : (∑ x, degree (bipartiteGraph a) x * (f x)^2)
      = ((2 ^ (a - 1) : ℕ) : ℝ) * (∑ x, (f x)^2) := by
    calc
      (∑ x, degree (bipartiteGraph a) x * (f x)^2)
          = ∑ x, ((2 ^ (a - 1) : ℕ) : ℝ) * (f x)^2 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [bipartiteGraph_degree a ha x]
      _ = ((2 ^ (a - 1) : ℕ) : ℝ) * (∑ x, (f x)^2) := by rw [Finset.mul_sum]
  have hadj := bipartiteGraph_adj_form a f
  have hE : (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then (f x - f y)^2 else 0))
      = 2 * ((∑ x, degree (bipartiteGraph a) x * (f x)^2)
        - (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then f x * f y else 0))) := by
    linarith [hDA]
  rw [hE, hdeg, hadj]
  ring

/-- For a zero-sum function, the bipartite edge quadratic form is at least twice the half size
times the sum of squares. -/
lemma bipartiteGraph_edgeForm_lower (ha : 0 < a) (f : Fin (2 ^ a) → ℝ)
    (hf : (∑ x, f x) = 0) :
    2 * ((2 ^ (a - 1) : ℕ) : ℝ) * (∑ x, (f x)^2)
      ≤ (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then (f x - f y)^2 else 0)) := by
  have hform := bipartiteGraph_edgeForm a ha f
  have hsum := bipartiteSum_eq a f
  have hzero : bipartiteLowerSum a f + bipartiteUpperSum a f = 0 := by
    rw [← hsum]
    exact hf
  have hUS : bipartiteUpperSum a f = -(bipartiteLowerSum a f) := by linarith
  rw [hform, hUS]
  have hsq : 0 ≤ (bipartiteLowerSum a f)^2 := sq_nonneg _
  nlinarith [hsq]

/-- For positive `a`, the bipartite graph has lazy chain gap one half. -/
lemma bipartiteGraph_lazyChainGap (ha : 0 < a) :
    LazyChainGap (bipartiteGraph a) (1 / 2 : ℝ) := by
  have hdegpos : 0 < ((2 ^ (a - 1) : ℕ) : ℝ) := by positivity
  have hv : volume (bipartiteGraph a) ≠ 0 := by
    rw [bipartiteGraph_volume a ha]
    positivity
  refine lazyChainGap_of_edgeForm (bipartiteGraph a) (d := ((2 ^ (a - 1) : ℕ) : ℝ))
    (bipartiteGraph_isDegreeRegular a ha) hdegpos hv (by norm_num) ?_
  intro f hmean
  have hf0 : (∑ x, f x) = 0 := (bipartiteGraph_mean_zero_iff a ha f).mp hmean
  have hlow := bipartiteGraph_edgeForm_lower a ha f hf0
  calc
    4 * (1 / 2 : ℝ) * ((2 ^ (a - 1) : ℕ) : ℝ) * (∑ x, (f x)^2)
        = 2 * ((2 ^ (a - 1) : ℕ) : ℝ) * (∑ x, (f x)^2) := by ring
    _ ≤ (∑ x, ∑ y, (if (bipartiteGraph a).Adj x y then (f x - f y)^2 else 0)) := hlow

/-- For positive `a`, the lazy bipartite kernel has symmetric chain gap one half. -/
lemma bipartiteGraph_symmetricChainGap (ha : 0 < a) :
    SymmetricChainGap (kernel (bipartiteGraph a)) (1 / 2 : ℝ) := by
  have : Nonempty (Fin (2 ^ a)) := ⟨⟨0, by positivity⟩⟩
  refine symmetricChainGap_of_regular (bipartiteGraph a) (d := ((2 ^ (a - 1) : ℕ) : ℝ))
    (bipartiteGraph_isDegreeRegular a ha) ?_ ?_ (by norm_num) (bipartiteGraph_lazyChainGap a ha)
  · have : (0 : ℝ) < (Fintype.card (Fin (2 ^ a)) : ℝ) := by
      exact_mod_cast (Fintype.card_pos (α := Fin (2 ^ a)))
    exact this
  · have hv : volume (bipartiteGraph a) ≠ 0 := by
      rw [bipartiteGraph_volume a ha]
      positivity
    exact hv

/-- For positive `a`, the regular bipartite kernel has symmetric chain gap twice one half. -/
lemma bipartiteGraph_regularKernelChainGap (ha : 0 < a) :
    SymmetricChainGap (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ))
      (2 * (1 / 2 : ℝ)) := by
  have : Nonempty (Fin (2 ^ a)) := ⟨⟨0, by positivity⟩⟩
  have hdegpos : 0 < ((2 ^ (a - 1) : ℕ) : ℝ) := by positivity
  have hv : volume (bipartiteGraph a) ≠ 0 := by
    rw [bipartiteGraph_volume a ha]
    positivity
  have hcard : 0 < (Fintype.card (Fin (2 ^ a)) : ℝ) := by
    exact_mod_cast (Fintype.card_pos (α := Fin (2 ^ a)))
  have h := symmetricChainGap_regularKernel (bipartiteGraph a)
    (d := ((2 ^ (a - 1) : ℕ) : ℝ)) (bipartiteGraph_isDegreeRegular a ha) hdegpos hcard hv
    (by norm_num) (bipartiteGraph_lazyChainGap a ha)
  exact h

/-- For positive `a`, the regular bipartite kernel has symmetric chain gap one. -/
lemma bipartiteGraph_regularKernelChainGap_one (ha : 0 < a) :
    SymmetricChainGap (regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ)) (1 : ℝ) := by
  have h := bipartiteGraph_regularKernelChainGap a ha
  rw [show (2 * (1 / 2 : ℝ)) = 1 by ring] at h
  exact h

/-- The regular bipartite kernel quadratic form on `bipartiteHalfIndicator` is the negative sum
of its squared values. -/
lemma bipartiteGraph_regularKernel_half_indicator (ha : 0 < a) :
    (∑ x : Fin (2 ^ a), ∑ y : Fin (2 ^ a),
        bipartiteHalfIndicator a x
          * regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ) x y
          * bipartiteHalfIndicator a y)
      = -(∑ x : Fin (2 ^ a), (bipartiteHalfIndicator a x)^2) := by
  have hm : bipartiteHalf a ≤ 2 ^ a := by
    have := bipartiteHalf_lt a ha
    omega
  have hsub : (2 ^ a - bipartiteHalf a : ℕ) = bipartiteHalf a := by
    unfold bipartiteHalf
    have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
      have h1 : 2 ^ (a - 1) * 2 = 2 ^ (a - 1 + 1) := by rw [Nat.pow_succ]
      rw [h1, show a - 1 + 1 = a from by omega]
    have h1 : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by rw [Nat.mul_two]
    omega
  have hcountL : (∑ x : Fin (2 ^ a), if x.val < bipartiteHalf a then (1 : ℝ) else 0)
      = ((2 ^ (a - 1) : ℕ) : ℝ) := sum_ite_val_lt_fin (2 ^ a) (bipartiteHalf a) hm
  have hcountU : (∑ x : Fin (2 ^ a), if bipartiteHalf a ≤ x.val then (1 : ℝ) else 0)
      = ((2 ^ a - bipartiteHalf a : ℕ) : ℝ) := sum_ite_val_ge_fin (2 ^ a) (bipartiteHalf a) hm
  have hLS : bipartiteLowerSum a (bipartiteHalfIndicator a)
      = ((2 ^ (a - 1) : ℕ) : ℝ) := by
    unfold bipartiteLowerSum
    have hmain : ∀ x : Fin (2 ^ a),
        (if x.val < bipartiteHalf a then bipartiteHalfIndicator a x else 0)
          = (if x.val < bipartiteHalf a then (1 : ℝ) else 0) := by
      intro x
      by_cases h : x.val < bipartiteHalf a
      · simp [bipartiteHalfIndicator, h]
      · simp [h]
    rw [Finset.sum_congr rfl (fun x _ => hmain x), hcountL]
  have hUS : bipartiteUpperSum a (bipartiteHalfIndicator a)
      = -((2 ^ (a - 1) : ℕ) : ℝ) := by
    unfold bipartiteUpperSum
    have hmain : ∀ x : Fin (2 ^ a),
        (if bipartiteHalf a ≤ x.val then bipartiteHalfIndicator a x else 0)
          = (if bipartiteHalf a ≤ x.val then (-1 : ℝ) else 0) := by
      intro x
      by_cases h : bipartiteHalf a ≤ x.val
      · have hne : ¬(x.val < bipartiteHalf a) := by omega
        simp [bipartiteHalfIndicator, h, hne]
      · simp [h]
    have hneg : (∑ x : Fin (2 ^ a), (if bipartiteHalf a ≤ x.val then (-1 : ℝ) else 0))
        = -(∑ x : Fin (2 ^ a), (if bipartiteHalf a ≤ x.val then (1 : ℝ) else 0)) := by
      have hmain' : ∀ x : Fin (2 ^ a),
          (if bipartiteHalf a ≤ x.val then (-1 : ℝ) else 0)
            = -(if bipartiteHalf a ≤ x.val then (1 : ℝ) else 0) := by
        intro x
        by_cases h : bipartiteHalf a ≤ x.val
        · simp [h]
        · simp [h]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact hmain' x
    rw [Finset.sum_congr rfl (fun x _ => hmain x), hneg, hcountU, hsub]
    rfl
  have hsq : (∑ x : Fin (2 ^ a), (bipartiteHalfIndicator a x)^2)
      = ((2 ^ a : ℕ) : ℝ) := by
    have hmain : ∀ x : Fin (2 ^ a), (bipartiteHalfIndicator a x)^2 = 1 := by
      intro x
      by_cases h : x.val < bipartiteHalf a
      · simp [bipartiteHalfIndicator, h]
      · simp [bipartiteHalfIndicator, h]
    rw [Finset.sum_congr rfl (fun x _ => hmain x)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpoint : ∀ x y : Fin (2 ^ a),
      bipartiteHalfIndicator a x
          * regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ) x y
          * bipartiteHalfIndicator a y
        = ((2 ^ (a - 1) : ℕ) : ℝ)⁻¹
          * (if (bipartiteGraph a).Adj x y then
              bipartiteHalfIndicator a x * bipartiteHalfIndicator a y
            else 0) := by
    intro x y
    unfold regularKernel
    by_cases hy : (bipartiteGraph a).Adj x y
    · simp [hy]; ring
    · simp [hy]
  have hadj := bipartiteGraph_adj_form a (bipartiteHalfIndicator a)
  calc
    (∑ x : Fin (2 ^ a), ∑ y : Fin (2 ^ a),
        bipartiteHalfIndicator a x
          * regularKernel (bipartiteGraph a) ((2 ^ (a - 1) : ℕ) : ℝ) x y
          * bipartiteHalfIndicator a y)
      = ∑ x : Fin (2 ^ a), ∑ y : Fin (2 ^ a),
          ((2 ^ (a - 1) : ℕ) : ℝ)⁻¹
            * (if (bipartiteGraph a).Adj x y then
                bipartiteHalfIndicator a x * bipartiteHalfIndicator a y
              else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          exact hpoint x y
    _ = ((2 ^ (a - 1) : ℕ) : ℝ)⁻¹
          * (∑ x : Fin (2 ^ a), ∑ y : Fin (2 ^ a),
            (if (bipartiteGraph a).Adj x y then
              bipartiteHalfIndicator a x * bipartiteHalfIndicator a y
            else 0)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = ((2 ^ (a - 1) : ℕ) : ℝ)⁻¹
          * (2 * bipartiteLowerSum a (bipartiteHalfIndicator a)
            * bipartiteUpperSum a (bipartiteHalfIndicator a)) := by
          rw [hadj]
    _ = -((2 ^ a : ℕ) : ℝ) := by
          rw [hLS, hUS]
          have hne : ((2 ^ (a - 1) : ℕ) : ℝ) ≠ 0 := by positivity
          have htwo : (2 : ℝ) * ((2 ^ (a - 1) : ℕ) : ℝ) = ((2 ^ a : ℕ) : ℝ) := by
            have hpow : 2 ^ (a - 1) * 2 = 2 ^ a := by
              have h1 : 2 ^ (a - 1) * 2 = 2 ^ (a - 1 + 1) := by rw [Nat.pow_succ]
              rw [h1, show a - 1 + 1 = a from by omega]
            have hcast : ((2 ^ (a - 1) * 2 : ℕ) : ℝ)
                = ((2 ^ (a - 1) : ℕ) : ℝ) * 2 := by
              rw [Nat.cast_mul]
              norm_num
            rw [← hpow, hcast]
            ring
          calc
            ((2 ^ (a - 1) : ℕ) : ℝ)⁻¹
                * (2 * ((2 ^ (a - 1) : ℕ) : ℝ) * (-((2 ^ (a - 1) : ℕ) : ℝ)))
              = 2 * (((2 ^ (a - 1) : ℕ) : ℝ)⁻¹ * ((2 ^ (a - 1) : ℕ) : ℝ))
                  * (-((2 ^ (a - 1) : ℕ) : ℝ)) := by ring
            _ = 2 * 1 * (-((2 ^ (a - 1) : ℕ) : ℝ)) := by rw [inv_mul_cancel₀ hne]
            _ = -((2 ^ a : ℕ) : ℝ) := by
              calc
                2 * 1 * (-((2 ^ (a - 1) : ℕ) : ℝ))
                    = -(2 * ((2 ^ (a - 1) : ℕ) : ℝ)) := by ring
                _ = -((2 ^ a : ℕ) : ℝ) := by rw [htwo]
    _ = -(∑ x : Fin (2 ^ a), (bipartiteHalfIndicator a x)^2) := by
          rw [hsq]

end BipartiteFamily

section NormalizedChainCheegerEndpoint

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Establishes the normalized chain bridge, gap relation, Cheeger upper bound, and
degenerate-case properties for `G`. -/
theorem normalized_chain_cheeger : NormalizedChainCheeger G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x y
      exact kernel_eq_half_add_normalizedKernel G x y
    · intro x
      exact normalizedKernel_row_sum G x
    · intro x y hv
      exact normalizedKernel_detailed_balance G hv x y
  · refine ⟨?_, ?_⟩
    · intro S hv hsep hm hlt
      exact separatingCut_centeredIndicator G hv hsep hm hlt
    · intro f hv
      exact mean_zero_iff_degree_mean_zero G hv f
  · intro S hv hm hhalf
    let : Nonempty V := volume_ne_zero_nonempty G hv
    refine ⟨centeredIndicator G S, mean_centered G S, ?_, ?_⟩
    · exact variance_pos G S hm hhalf
    · have h := rayleigh G S hm hhalf
      calc
        energy G (centeredIndicator G S) / variance G (centeredIndicator G S)
            ≤ 2 * flow G S / mass G S := h
        _ = 2 * cutConductance G S := by rw [cutConductance]; ring
  · refine ⟨?_, ?_⟩
    · intro x hx
      refine ⟨?_, ?_, ?_⟩
      · intro y
        simp [normalizedKernel, hx]
      · intro y
        exact isolated_normalizedLaplacian_zero G hx y
      · intro hv
        exact isolated_stationary_zero G hv hx
    · intro hv
      refine ⟨?_, ?_⟩
      · intro x y
        exact volume_zero_kernel_stayPut G hv x y
      · intro f
        exact energy_eq_zero_of_volume_zero G hv f

end NormalizedChainCheegerEndpoint

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
