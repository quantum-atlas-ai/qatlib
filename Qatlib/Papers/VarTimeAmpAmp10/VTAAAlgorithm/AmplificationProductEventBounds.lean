/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# Amplification product and event bounds

This module derives stage-time and product-sum estimates from positive base weights,
amplified-weight floors, gain windows, and the amplification time recurrence.
`clause89_frozen_residual_false` also disproves a universal conjunction that imposes these
hypotheses on arbitrary input sequences.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `clause89_ratio_bound`: square-root gain-ratio control of a call multiplier.
* `clause89_event_bounds`: stage and cumulative bounds corresponding to equations (5)–(6).

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw


set_option autoImplicit false

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
set_option warningAsError false
noncomputable section

/-- The universal conjunction of positivity, gain-window, recurrence, and time-bound assertions
for arbitrary sequences is false. -/
lemma clause89_frozen_residual_false :
    ¬ (∀ (m : ℕ) (rs rs' : ℕ → ℝ) (k : ℕ → ℕ) (T : ℕ → ℝ),
      1 ≤ m →
      (∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < rs' j) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ m →
        (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * rs' j ≤ rs j) ∧
      0 ≤ T 0 ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ m →
        T i = (2 * k i + 1 : ℝ) * (T (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ m →
        T i ≤ eq5StageTimeBound m (rs i) (rs' i) (T (i - 1)) i) ∧
      T m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct rs rs' 1 (m + 1) * T 0 + eq6ProductSum rs rs' m)) := by
  intro h
  obtain ⟨h1, _, _, _, _, _, _⟩ :=
    h 1 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (by norm_num)
  exact absurd (h1 1 (by norm_num) (by norm_num)) (lt_irrefl 0)
end
noncomputable section

/-- For `μ ≥ 1`, the squared recurrence correction factor times `1 - 1 / (3 * μ)` is at least
one. -/
lemma clause89_const_factor (μ : ℝ) (hμ : 1 ≤ μ) :
    (1 + 1 / (3 * μ - 1)) ^ 2 * (1 - 1 / (3 * μ)) ≥ 1 := by
  have h3μ : 0 < 3 * μ := by positivity
  have hden : 0 < 3 * μ - 1 := by linarith
  have hαeq : 1 - 1 / (3 * μ) = (3 * μ - 1) / (3 * μ) := by field_simp
  have hceq : 1 + 1 / (3 * μ - 1) = 3 * μ / (3 * μ - 1) := by field_simp; ring
  rw [hαeq, hceq]
  field_simp; nlinarith
end
noncomputable section

/-- For positive base and amplified weights, the gain-window inequality bounds `a` by the
corrected square-root ratio `√p / √q` when `μ ≥ 1`. -/
lemma clause89_ratio_bound (μ a p q : ℝ) (hμ : 1 ≤ μ) (_ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hwin : (1 - 1 / (3 * μ)) * a ^ 2 * q ≤ p) :
    a ≤ (1 + 1 / (3 * μ - 1)) * (Real.sqrt p / Real.sqrt q) := by
  have h3μ : 0 < 3 * μ := by positivity
  have hden : 0 < 3 * μ - 1 := by linarith
  have hαpos : 0 < 1 - 1 / (3 * μ) := by
    have h : (1 - 1 / (3 * μ)) * (3 * μ) = 3 * μ - 1 := by field_simp
    nlinarith [h, h3μ]
  have hcpos : 0 < 1 + 1 / (3 * μ - 1) := by positivity
  have hconst := clause89_const_factor μ hμ
  have hle : a * Real.sqrt q ≤ (1 + 1 / (3 * μ - 1)) * Real.sqrt p := by
    have h2 : 0 ≤ (1 + 1 / (3 * μ - 1)) * Real.sqrt p :=
      mul_nonneg hcpos.le (Real.sqrt_nonneg p)
    refine le_of_sq_le_sq ?_ h2
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hq), Real.sq_sqrt (le_of_lt hp)]
    have hdiv : a ^ 2 * q ≤ p / (1 - 1 / (3 * μ)) :=
      (le_div_iff₀ hαpos).2 (by nlinarith [hwin])
    have hpow : 1 / (1 - 1 / (3 * μ)) ≤ (1 + 1 / (3 * μ - 1)) ^ 2 := by
      field_simp; nlinarith [hconst, hαpos]
    have hpmul : p / (1 - 1 / (3 * μ)) ≤ (1 + 1 / (3 * μ - 1)) ^ 2 * p := by
      have hα : 0 < 1 - 1 / (3 * μ) := hαpos
      have heq : p / (1 - 1 / (3 * μ)) = p * (1 / (1 - 1 / (3 * μ))) := by field_simp
      calc p / (1 - 1 / (3 * μ)) = p * (1 / (1 - 1 / (3 * μ))) := heq
        _ ≤ p * (1 + 1 / (3 * μ - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hp)
        _ = (1 + 1 / (3 * μ - 1)) ^ 2 * p := by ring
    exact le_trans hdiv hpmul
  have hdiv : a ≤ ((1 + 1 / (3 * μ - 1)) * Real.sqrt p) / Real.sqrt q :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hq)).2 hle
  rwa [mul_div_assoc] at hdiv
end
noncomputable section

/-- A nonnegative initial time and the odd-multiplier dyadic recurrence imply nonnegative times
through stage `m`. -/
lemma clause89_T_nonneg (m : ℕ) (k : ℕ → ℕ) (T : ℕ → ℝ) (hT0 : 0 ≤ T 0)
    (hrec : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      T i = (2 * k i + 1 : ℝ) * (T (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))) :
    ∀ i : ℕ, i ≤ m → 0 ≤ T i := by
  intro i
  induction i with
  | zero => exact fun _ => hT0
  | succ i ih =>
    intro hi
    have hrec' := hrec (i + 1) (by omega) (by omega)
    have hprev : 0 ≤ T i := ih (by omega)
    have hkey : T (i + 1) = (2 * k (i + 1) + 1 : ℝ) * (T i + (2 : ℝ) ^ i) := by
      simpa using! hrec'
    rw [hkey]
    positivity
end
noncomputable section

/-- A gain-ratio product over a nonempty half-open interval factors into its first ratio and the
remaining product. -/
lemma clause89_prod_peel (rs rs' : ℕ → ℝ) (i M : ℕ) (hi : i < M) :
    gainRatioProduct rs rs' i M =
      gainRatio (rs i) (rs' i) * gainRatioProduct rs rs' (i + 1) M := by
  have hmem : i ∈ Finset.Ico i M := Finset.mem_Ico.mpr ⟨by omega, hi⟩
  have h : Finset.Ico (i + 1) M = (Finset.Ico i M).erase i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Ico]
    constructor <;> intro hjs <;> omega
  rw [gainRatioProduct, gainRatioProduct, h]
  exact (Finset.mul_prod_erase _ (fun j => gainRatio (rs j) (rs' j)) hmem).symm
end
noncomputable section

/-- A sum over a nonempty half-open interval splits into its first term and the remaining sum. -/
lemma clause89_sum_peel (f : ℕ → ℝ) (i M : ℕ) (hi : i < M) :
    (∑ j ∈ Finset.Ico i M, f j) = f i + ∑ j ∈ Finset.Ico (i + 1) M, f j := by
  have hmem : i ∈ Finset.Ico i M := Finset.mem_Ico.mpr ⟨by omega, hi⟩
  have h : Finset.Ico (i + 1) M = (Finset.Ico i M).erase i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Ico]
    constructor <;> intro hjs <;> omega
  rw [h]
  exact (Finset.add_sum_erase _ _ hmem).symm
end
noncomputable section

/-- Under positive base weights, amplified-weight floors, gain windows, and the time recurrence,
the stage and cumulative product-sum time bounds hold as in equations (5)–(6) of
[Ambainis2012]. -/
lemma clause89_event_bounds (m : ℕ) (rs rs' : ℕ → ℝ) (k : ℕ → ℕ) (T : ℕ → ℝ)
    (hm : 1 ≤ m)
    (hpos : ∀ j : ℕ, 1 ≤ j → j ≤ m → 0 < rs' j)
    (hfloor : ∀ j : ℕ, 1 ≤ j → j ≤ m → 1 / (9 * (m : ℝ)) ≤ rs j)
    (hwin : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      (1 - 1 / (3 * (m : ℝ))) * ((2 * k j + 1 : ℝ) ^ 2) * rs' j ≤ rs j)
    (hT0 : 0 ≤ T 0)
    (hrec : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      T i = (2 * k i + 1 : ℝ) * (T (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))) :
    (∀ i : ℕ, 1 ≤ i → i ≤ m →
      T i ≤ eq5StageTimeBound m (rs i) (rs' i) (T (i - 1)) i) ∧
    T m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
      (gainRatioProduct rs rs' 1 (m + 1) * T 0 + eq6ProductSum rs rs' m) := by
  have hc : 0 < 1 + 1 / (3 * (m : ℝ) - 1) := by
    have hden : 0 < 3 * (m : ℝ) - 1 := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    positivity
  have hc1 : 1 ≤ 1 + 1 / (3 * (m : ℝ) - 1) := by
    have hden : 0 < 3 * (m : ℝ) - 1 := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have : 0 ≤ 1 / (3 * (m : ℝ) - 1) := by positivity
    linarith
  have hT : ∀ i : ℕ, i ≤ m → 0 ≤ T i := clause89_T_nonneg m k T hT0 hrec

  have heq5 : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      T i ≤ eq5StageTimeBound m (rs i) (rs' i) (T (i - 1)) i := by
    intro i hi1 hi2
    have hrs' : 0 < rs' i := hpos i hi1 hi2
    have hrs : 0 < rs i := by
      have h1 : 0 < 1 / (9 * (m : ℝ)) := by
        have hm' : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (by omega : m ≠ 0))
        positivity
      exact lt_of_lt_of_le h1 (hfloor i hi1 hi2)
    have hrec_i := hrec i hi1 hi2
    have hX : 0 ≤ T (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1) := by
      have : 0 ≤ T (i - 1) := hT (i - 1) (by omega)
      positivity
    have hratio : (2 * k i + 1 : ℝ) ≤
        (1 + 1 / (3 * (m : ℝ) - 1)) * (Real.sqrt (rs i) / Real.sqrt (rs' i)) :=
      clause89_ratio_bound (m : ℝ) (2 * k i + 1 : ℝ) (rs i) (rs' i)
        (by exact_mod_cast hm) (by positivity) hrs hrs' (hwin i hi1 hi2)
    have hmul := mul_le_mul_of_nonneg_right hratio hX
    show T i ≤ (1 + 1 / (3 * (m : ℝ) - 1)) *
        (Real.sqrt (rs i) / Real.sqrt (rs' i)) * (T (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1))
    rw [hrec_i]
    exact hmul
  have hg_nonneg : ∀ j : ℕ, 0 ≤ gainRatio (rs j) (rs' j) := by
    intro j
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hP_nonneg : ∀ i : ℕ, 0 ≤ gainRatioProduct rs rs' i (m + 1) := by
    intro i
    exact Finset.prod_nonneg (fun j _ => hg_nonneg j)

  set f : ℕ → ℝ :=
    (fun i => (1 + 1 / (3 * (m : ℝ) - 1)) ^ (m - i + 1) *
      gainRatioProduct rs rs' i (m + 1) * (2 : ℝ) ^ ((i : ℕ) - 1)) with hf
  have hunroll : ∀ d : ℕ, d ≤ m →
      T m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ d *
          gainRatioProduct rs rs' (m + 1 - d) (m + 1) * T (m - d) +
        ∑ i ∈ Finset.Ico (m + 1 - d) (m + 1), f i := by
    intro d
    induction d with
    | zero =>
      intro _
      have hP : gainRatioProduct rs rs' (m + 1) (m + 1) = 1 := by
        simp [gainRatioProduct]
      have hs : (∑ i ∈ Finset.Ico (m + 1) (m + 1), f i) = 0 := by simp
      rw [Nat.sub_zero, Nat.sub_zero, pow_zero, hP, hs, one_mul, one_mul, _root_.add_zero]
    | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      have hidx : m + 1 - (d + 1) = m - d := by omega
      have htd : m - (d + 1) = m - d - 1 := by omega
      have hidx2 : m + 1 - d = m - d + 1 := by omega
      rw [hidx, htd]
      rw [hidx2] at ih'
      have hjlt : m - d < m + 1 := by omega
      have hpeel := clause89_prod_peel rs rs' (m - d) (m + 1) hjlt
      have hstep : (1 + 1 / (3 * (m : ℝ) - 1)) ^ d *
            gainRatioProduct rs rs' (m - d + 1) (m + 1) * T (m - d) ≤
          (1 + 1 / (3 * (m : ℝ) - 1)) ^ (d + 1) *
            gainRatioProduct rs rs' (m - d) (m + 1) * T (m - d - 1) +
          f (m - d) := by
        have hall : T (m - d) ≤ (1 + 1 / (3 * (m : ℝ) - 1)) *
            gainRatio (rs (m - d)) (rs' (m - d)) *
            (T (m - d - 1) + (2 : ℝ) ^ ((m - d : ℕ) - 1)) := by
          simpa [eq5StageTimeBound, gainRatio] using! heq5 (m - d) (by omega) (by omega)
        have hmul := mul_le_mul_of_nonneg_left hall
          (mul_nonneg (pow_nonneg (le_of_lt hc) d) (hP_nonneg (m - d + 1)))
        have hrew : (1 + 1 / (3 * (m : ℝ) - 1)) ^ d *
              gainRatioProduct rs rs' (m - d + 1) (m + 1) *
              ((1 + 1 / (3 * (m : ℝ) - 1)) * gainRatio (rs (m - d)) (rs' (m - d)) *
                (T (m - d - 1) + (2 : ℝ) ^ ((m - d : ℕ) - 1)))
            = (1 + 1 / (3 * (m : ℝ) - 1)) ^ (d + 1) *
                gainRatioProduct rs rs' (m - d) (m + 1) * T (m - d - 1) +
              f (m - d) := by
          have hexp : m - (m - d) + 1 = d + 1 := by omega
          simp only [hf]
          rw [hpeel, hexp]
          have hpow : (1 + 1 / (3 * (m : ℝ) - 1)) ^ (d + 1)
              = (1 + 1 / (3 * (m : ℝ) - 1)) ^ d * (1 + 1 / (3 * (m : ℝ) - 1)) := by ring
          rw [hpow]
          ring
        rw [← hrew]
        exact hmul
      have hpeelsum := clause89_sum_peel f (m - d) (m + 1) hjlt
      rw [hpeelsum]
      have hchain : ((1 + 1 / (3 * (m : ℝ) - 1)) ^ d *
            gainRatioProduct rs rs' (m - d + 1) (m + 1) * T (m - d)) +
          (∑ i ∈ Finset.Ico (m - d + 1) (m + 1), f i) ≤
        ((1 + 1 / (3 * (m : ℝ) - 1)) ^ (d + 1) *
            gainRatioProduct rs rs' (m - d) (m + 1) * T (m - d - 1) + f (m - d)) +
          (∑ i ∈ Finset.Ico (m - d + 1) (m + 1), f i) :=
        add_le_add hstep le_rfl
      exact le_trans (le_trans ih' hchain) (le_of_eq (add_assoc _ _ _))
  have hfinal := hunroll m le_rfl
  have hP1 : m + 1 - m = 1 := by omega
  rw [hP1, Nat.sub_self] at hfinal
  have hsumle : (∑ i ∈ Finset.Ico 1 (m + 1), f i) ≤
      (∑ i ∈ Finset.Ico 1 (m + 1),
        (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
          gainRatioProduct rs rs' i (m + 1) * (2 : ℝ) ^ ((i : ℕ) - 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hi2 : i ≤ m := by have := (Finset.mem_Ico.mp hi).2; omega
    simp only [hf]
    have hpow : (1 + 1 / (3 * (m : ℝ) - 1)) ^ (m - i + 1)
        ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m :=
      pow_le_pow_right₀ hc1 (by omega)
    have h1 : (1 + 1 / (3 * (m : ℝ) - 1)) ^ (m - i + 1) * gainRatioProduct rs rs' i (m + 1)
        ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m * gainRatioProduct rs rs' i (m + 1) :=
      mul_le_mul_of_nonneg_right hpow (hP_nonneg i)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hsum2 : (∑ i ∈ Finset.Ico 1 (m + 1),
        (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
          gainRatioProduct rs rs' i (m + 1) * (2 : ℝ) ^ ((i : ℕ) - 1))
      = (1 + 1 / (3 * (m : ℝ) - 1)) ^ m * eq6ProductSum rs rs' m := by
    simp only [eq6ProductSum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hchain : T m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        gainRatioProduct rs rs' 1 (m + 1) * T 0 +
      (1 + 1 / (3 * (m : ℝ) - 1)) ^ m * eq6ProductSum rs rs' m := by
    have h := add_le_add
      (le_rfl : ((1 + 1 / (3 * (m : ℝ) - 1)) ^ m * gainRatioProduct rs rs' 1 (m + 1) * T 0) ≤
        ((1 + 1 / (3 * (m : ℝ) - 1)) ^ m * gainRatioProduct rs rs' 1 (m + 1) * T 0)) hsumle
    rw [hsum2] at h
    exact le_trans hfinal h
  have hgoal : (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct rs rs' 1 (m + 1) * T 0 + eq6ProductSum rs rs' m)
      = (1 + 1 / (3 * (m : ℝ) - 1)) ^ m * gainRatioProduct rs rs' 1 (m + 1) * T 0 +
        (1 + 1 / (3 * (m : ℝ) - 1)) ^ m * eq6ProductSum rs rs' m := by
    ring
  exact ⟨heq5, by rw [hgoal]; exact hchain⟩
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
