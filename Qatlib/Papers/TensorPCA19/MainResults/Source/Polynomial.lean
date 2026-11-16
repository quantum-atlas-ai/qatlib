/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Qatlib.Papers.TensorPCA19.MainResults.Model.SpectralModel
public import Qatlib.Papers.TensorPCA19.MainResults.Model.TensorPCAConfig
public import Qatlib.Papers.TensorPCA19.MainResults.Source.Detection
public import Qatlib.Papers.TensorPCA19.MainResults.Source.Recovery
public import Qatlib.Papers.TensorPCA19.MainResults.Source.RecoverySampling

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open MeasureTheory
open scoped BigOperators ENNReal

open Qatlib.Papers.TensorPCA19.MainResults

open Qatlib.Papers.TensorPCA19.MainResults.Detection

open Qatlib.Papers.TensorPCA19.MainResults.GaussianSpectralModel

open Qatlib.Papers.TensorPCA19.MainResults.SpectralDecomposition

open Qatlib.Papers.TensorPCA19.MainResults.SpikedTensor

namespace Qatlib.Papers.TensorPCA19.MainResults

section

/-- Substituting the supplied constant gives the stated scalar anti-concentration bound. -/
theorem lemma13_corollary (k : ℕ) (_hk : 0 < k) {δ : ℝ} (_hδ : 0 < δ) (prob C : ℝ)
    (hC : C = 2 * (k : ℝ) + 1) (hanti : prob ≤ C * (δ / (1 - δ)) ^ (2 / (2 * (k : ℝ) + 1))) :
    prob ≤ (2 * (k : ℝ) + 1) * (δ / (1 - δ)) ^ (2 / (2 * (k : ℝ) + 1)) := by
  rw [hC] at hanti
  exact hanti

/-- **Lemma 14** (§5.2, p.30).  If the deviation event `{val < bound · δ}` has
probability at most `O(n_bos) δ^{2/(2 n_bos+1)}` — the anti-concentration input
supplied by Lemma 13 with `k = 2 n_bos + 1` — then with probability at least
`1 − O(n_bos) δ^{2/(2 n_bos+1)}` the value is at least `bound · δ`.  Proved by the
complement/union-bound step (`measure_compl`). -/
theorem lemma14_lower_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (val : Ω → ℝ) (hval : Measurable val)
    (nbos : ℕ) {δ bound C : ℝ} (_hδ : 0 < δ) (_hC : 0 < C) (_hbound : 0 < bound)
    (hanti : (μ {ω | val ω < bound * δ}).toReal ≤
      C * (nbos : ℝ) * δ ^ (2 / (2 * (nbos : ℝ) + 1))) :
    1 - C * (nbos : ℝ) * δ ^ (2 / (2 * (nbos : ℝ) + 1)) ≤
      (μ {ω | bound * δ ≤ val ω}).toReal := by
  have hmeas : MeasurableSet {ω | val ω < bound * δ} :=
    measurableSet_lt hval measurable_const
  have hcompl : {ω | bound * δ ≤ val ω} = {ω | val ω < bound * δ}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  have hfin : μ {ω | val ω < bound * δ} ≠ ∞ := measure_ne_top μ _
  have hle1 : μ {ω | val ω < bound * δ} ≤ 1 := by
    calc μ {ω | val ω < bound * δ} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hcomp : (μ {ω | bound * δ ≤ val ω}).toReal =
      1 - (μ {ω | val ω < bound * δ}).toReal := by
    rw [hcompl, measure_compl hmeas hfin, measure_univ]
    rw [ENNReal.toReal_sub_of_le hle1 (by simp)]
    simp
  rw [hcomp]
  linarith

/-- The quantum input state of Lemma 11 and Eq. (56) (p.29), in unnormalized form:
`x` is the noise fraction, `inputExpectation y` is
`⟨Ψ⁰(y)|E_PE(T′₀)|Ψ⁰(y)⟩` and `signalExpectation` is the all-signal expectation. -/
structure InputStateModel (s : SpikedTensor) where
  /-- Noise fraction `x ∈ (0,1]`. -/
  x : ℝ
  /-- `x > 0`. -/
  x_pos : 0 < x
  /-- `x ≤ 1` (the source takes `x = 1/log N`). -/
  x_le_one : x ≤ 1
  /-- Expectation value of the perturbed input state, as a function of `y ∈ [0,1]`. -/
  inputExpectation : ℝ → ℝ
  /-- All-signal expectation value. -/
  signalExpectation : ℝ
  /-- The all-signal expectation is nonnegative. -/
  signal_nonneg : 0 ≤ signalExpectation

end

end Qatlib.Papers.TensorPCA19.MainResults
