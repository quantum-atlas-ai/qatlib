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
# A refined success bound for amplitude amplification

This module proves a cubic sine lower bound and derives the refined amplitude-amplification
success estimate used in [Ambainis2012]. The theorem `clause88` combines this estimate with
proportionality of the marked components and the exact count of preparation queries.

## Main statements

* `clause88_tight_sin_sq`: A sine-squared lower bound with a cubic correction in the amplified
  mass.
* `clause88`: The windowed success bound, preservation of the marked direction, and
  preparation-query count.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

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

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
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

/-- For every nonnegative real `x`, the sine is at least `x - x³ / 6`. -/
lemma clause88_sin_ge_sub_cube (x : ℝ) (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u => Real.sin u - u + u ^ 3 / 6)
      (Real.cos t - 1 + t ^ 2 / 2) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => Real.sin u) (Real.cos t) t := Real.hasDerivAt_sin t
    have h2 : HasDerivAt (fun u : ℝ => u) (1 : ℝ) t := hasDerivAt_id' t
    have h3 : HasDerivAt (fun u : ℝ => u ^ 3 / 6) (t ^ 2 / 2) t := by
      have h3a : HasDerivAt (fun u : ℝ => u ^ 3) ((3 : ℝ) * t ^ 2) t := by
        convert! (hasDerivAt_id' t).pow 3 using 1
        ring
      convert! h3a.div_const 6 using 1
      field_simp
      ring
    have h123 := (h1.sub h2).add h3
    convert! h123 using 1
  have hmono : Monotone fun u => Real.sin u - u + u ^ 3 / 6 := by
    apply monotone_of_deriv_nonneg
    · intro t
      exact (hd t).differentiableAt
    · intro t
      have hderiv := (hd t).deriv
      rw [hderiv]
      have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
      linarith
  have h0 : (fun u => Real.sin u - u + u ^ 3 / 6) 0 = 0 := by simp
  have hle := hmono hx
  rw [h0] at hle
  have hexpand : (fun u => Real.sin u - u + u ^ 3 / 6) x = Real.sin x - x + x ^ 3 / 6 := rfl
  rw [hexpand] at hle
  linarith
end
noncomputable section

/-- For `0 ≤ θ ≤ π / 2` and `nθ ≤ π / 2`, the amplified sine square is at least `(1 - n² * sin²
θ / 3) * n² * sin² θ`. -/
lemma clause88_tight_sin_sq (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθpi : θ ≤ Real.pi / 2)
    (hwin : (n : ℝ) * θ ≤ Real.pi / 2) :
    Real.sin ((n : ℝ) * θ) ^ 2 ≥
      (1 - (n : ℝ) ^ 2 * Real.sin θ ^ 2 / 3) * ((n : ℝ) ^ 2 * Real.sin θ ^ 2) := by
  set x : ℝ := (n : ℝ) * θ with hxe
  set t : ℝ := (n : ℝ) ^ 2 * Real.sin θ ^ 2 with hte
  have hx0 : 0 ≤ x := by
    rw [hxe]; exact mul_nonneg (Nat.cast_nonneg _) hθ
  have hxpi : x ≤ Real.pi / 2 := by rw [hxe]; exact hwin
  have hsinθ0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos])
  have hsinθsq : Real.sin θ ^ 2 ≤ θ ^ 2 := Real.sin_sq_le_sq
  have htle : t ≤ x ^ 2 := by
    rw [hte, hxe]
    have h1 : (n : ℝ) ^ 2 * Real.sin θ ^ 2 ≤ (n : ℝ) ^ 2 * θ ^ 2 :=
      mul_le_mul_of_nonneg_left hsinθsq (sq_nonneg _)
    nlinarith
  have hx2 : x ^ 2 ≤ 6 := by
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have h1 : x ^ 2 ≤ (Real.pi / 2) ^ 2 := pow_le_pow_left₀ hx0 hxpi 2
    nlinarith
  have hbase : 0 ≤ x - x ^ 3 / 6 := by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
  have hsin_ge : x - x ^ 3 / 6 ≤ Real.sin x := clause88_sin_ge_sub_cube x hx0
  have hsq : (x - x ^ 3 / 6) ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hbase hsin_ge 2
  have hx4 : x ^ 2 - x ^ 4 / 3 ≤ Real.sin x ^ 2 := by
    have hexpand : (x - x ^ 3 / 6) ^ 2 = x ^ 2 - x ^ 4 / 3 + x ^ 6 / 36 := by ring
    have h6 : 0 ≤ x ^ 6 / 36 := by positivity
    nlinarith [hsq, hexpand]
  have htarget : (1 - t / 3) * t = t - t ^ 2 / 3 := by ring
  rw [htarget]
  by_cases hsmall : x ^ 2 ≤ 3 / 2
  · have hmono : t - t ^ 2 / 3 ≤ x ^ 2 - x ^ 4 / 3 := by
      have hfac : t - t ^ 2 / 3 - (x ^ 2 - x ^ 4 / 3)
          = (t - x ^ 2) * (1 - (t + x ^ 2) / 3) := by ring
      have hsum : t + x ^ 2 ≤ 3 := by nlinarith [htle, hsmall]
      have hnonneg : 0 ≤ 1 - (t + x ^ 2) / 3 := by linarith
      nlinarith [hfac, htle, hnonneg]
    exact le_trans hmono hx4
  · have hYmax : t - t ^ 2 / 3 ≤ 3 / 4 := by
      nlinarith [sq_nonneg (t - 3 / 2)]
    have hx_ge : Real.pi / 3 ≤ x := by
      have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hp3 : (Real.pi / 3) ^ 2 ≤ 3 / 2 := by nlinarith
      have h1 : (Real.pi / 3) ^ 2 ≤ x ^ 2 := by
        have h32 : (3 / 2 : ℝ) ≤ x ^ 2 := le_of_not_ge hsmall
        nlinarith [hp3]
      have h2 : Real.pi / 3 ≤ Real.sqrt (x ^ 2) :=
        (Real.le_sqrt (by positivity : 0 ≤ Real.pi / 3) (sq_nonneg x)).mpr h1
      rwa [Real.sqrt_sq hx0] at h2
    have hsin_ge_pi3 : Real.sin (Real.pi / 3) ≤ Real.sin x :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hxpi hx_ge
    have hsq34 : (3 / 4 : ℝ) ≤ Real.sin x ^ 2 := by
      have hpos : 0 ≤ Real.sin (Real.pi / 3) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      have := pow_le_pow_left₀ hpos hsin_ge_pi3 2
      rwa [Real.sq_sin_pi_div_three] at this
    nlinarith [hYmax, hsq34]
end
noncomputable section

/-- Collapse onto a fixed marked set preserves addition of states. -/
lemma clause88_collapse_add {I : Type} [Fintype I] [DecidableEq I] (u v : QState I) (S : Finset I) :
    Collapse (u + v) S = Collapse u S + Collapse v S := by
  funext i
  by_cases h : i ∈ S <;> simp [collapse_apply, h]
end
noncomputable section

/-- Collapse onto a fixed marked set commutes with complex scalar multiplication. -/
lemma clause88_collapse_smul {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (u : QState I)
    (S : Finset I) : Collapse (c • u) S = c • Collapse u S := by
  funext i
  by_cases h : i ∈ S <;> simp [collapse_apply, h, Pi.smul_apply]
end
noncomputable section

/-- Collapse onto a fixed marked set preserves subtraction of states. -/
lemma clause88_collapse_sub {I : Type} [Fintype I] [DecidableEq I] (u v : QState I) (S : Finset I) :
    Collapse (u - v) S = Collapse u S - Collapse v S := by
  funext i
  by_cases h : i ∈ S <;> simp [collapse_apply, h]
end
noncomputable section

/-- Collapsing a state onto the same marked set twice has the same result as collapsing once. -/
lemma clause88_collapse_idem {I : Type} [Fintype I] [DecidableEq I] (u : QState I) (S : Finset I) :
    Collapse (Collapse u S) S = Collapse u S := by
  funext i
  by_cases h : i ∈ S <;> simp [collapse_apply, h]
end
noncomputable section

/-- Coherent amplification holds, and for a unitary preparation with marked mass `0 ≤ δ ≤ ε ≤
1`, `ε > 0`, and `r ≤ tightAAWindow ε`, the amplified mass is at least `tightAASuccess δ r`.
Its marked component is proportional to the original one, and the preparation-query count is
exactly `2 * r + 1`. [Ambainis2012] -/
theorem clause88 :

  CoherentAmplification ∧

  ∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j₀ : I)
    (S : Finset I) (ε δ : ℝ) (r : ℕ),
    A ∈ Matrix.unitaryGroup I ℂ →

    0 < ε → ε ≤ 1 → 0 ≤ δ → δ ≤ ε →
    ((r : ℝ) ≤ tightAAWindow ε) →
    MeasureProb (preparedAAState A j₀) S = δ →
    let out :=
        Run (preparedMark S) (preparedAACircuit A j₀ r)
        (Qatlib.Foundations.PureStateMath.Ket j₀)

    tightAASuccess δ r ≤ MeasureProb out S ∧

    (∃ c : ℂ, Collapse out S = c • Collapse (preparedAAState A j₀) S) ∧

    preparedInputQueries (preparedAAWord j₀ r) = 2 * r + 1 := by
  refine ⟨coherentAmplification_answer, ?_⟩
  intro I _ _ A j₀ S ε δ r hA hε0 hε1 hδ0 hδε hwin hδ
  show tightAASuccess δ r ≤
      MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ r) (Qatlib.Foundations.PureStateMath.Ket j₀)) S ∧
    (∃ c : ℂ, Collapse (Run (preparedMark S) (preparedAACircuit A j₀ r) (Qatlib.Foundations.PureStateMath.Ket j₀)) S =
      c • Collapse (preparedAAState A j₀) S) ∧
    preparedInputQueries (preparedAAWord j₀ r) = 2 * r + 1
  refine ⟨?_, ?_, ?_⟩
  · have hwin' : (r : ℝ) ≤ Real.pi / (4 * Real.arcsin (Real.sqrt ε)) - 1 / 2 := by
      simpa [tightAAWindow] using! hwin
    have h4pos : 0 < 4 * Real.arcsin (Real.sqrt ε) := by
      have hΘpos : 0 < Real.arcsin (Real.sqrt ε) :=
        Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hε0)
      positivity
    have hmoved : (r : ℝ) + 1 / 2 ≤ Real.pi / (4 * Real.arcsin (Real.sqrt ε)) := by
      linarith
    have hcross : ((r : ℝ) + 1 / 2) * (4 * Real.arcsin (Real.sqrt ε)) ≤ Real.pi :=
      (le_div_iff₀ h4pos).mp hmoved
    have hΘwin : (2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt ε) ≤ Real.pi / 2 := by
      have h : ((r : ℝ) + 1 / 2) * (4 * Real.arcsin (Real.sqrt ε))
          = 2 * ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt ε)) := by ring
      nlinarith [h, hcross]
    have hθle : Real.arcsin (Real.sqrt δ) ≤ Real.arcsin (Real.sqrt ε) :=
      Real.arcsin_le_arcsin (Real.sqrt_le_sqrt hδε)
    have hΘ : (2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt δ) ≤ Real.pi / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hθle (by positivity : 0 ≤ 2 * (r : ℝ) + 1)) hΘwin
    have hδ1 : δ ≤ 1 := le_trans hδε hε1
    have hsqrt1 : Real.sqrt δ ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
    have hsinθ : Real.sin (Real.arcsin (Real.sqrt δ)) ^ 2 = δ := by
      rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg δ]) hsqrt1]
      exact Real.sq_sqrt hδ0
    have hcast : ((2 * r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + 1 := by norm_cast
    have hΘ' : ((2 * r + 1 : ℕ) : ℝ) * Real.arcsin (Real.sqrt δ) ≤ Real.pi / 2 := by
      rw [hcast]; exact hΘ
    have hle := clause88_tight_sin_sq (2 * r + 1) (Real.arcsin (Real.sqrt δ))
      (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg δ)) (Real.arcsin_le_pi_div_two _) hΘ'
    rw [hsinθ, hcast] at hle
    have hts : tightAASuccess δ r
        = (1 - (2 * (r : ℝ) + 1) ^ 2 * δ / 3) * ((2 * (r : ℝ) + 1) ^ 2 * δ) := by
      simp only [tightAASuccess]
      ring
    have hrun : MeasureProb (Run (preparedMark S) (preparedAACircuit A j₀ r) (Qatlib.Foundations.PureStateMath.Ket j₀)) S
        = Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt δ)) ^ 2 := by
      have hcore := (coherentAmplification_answer I A hA j₀ S r).1
      have hδ' : MeasureProb (ApplyGate A (Qatlib.Foundations.PureStateMath.Ket j₀)) S = δ := by
        simpa [preparedAAState] using! hδ
      simpa [hδ'] using! hcore
    rw [hts, hrun]
    exact hle
  · by_cases h0 : δ = 0
    · obtain hend := (prepared_aa_endpoint_states A j₀ S r hA).1
      refine ⟨1, ?_⟩
      rw [show Run (preparedMark S) (preparedAACircuit A j₀ r) (Qatlib.Foundations.PureStateMath.Ket j₀) = preparedAAState A j₀
          from hend (hδ.trans h0)]
      exact (one_smul ℂ (Collapse (preparedAAState A j₀) S)).symm
    · by_cases h1 : δ = 1
      · obtain hend := (prepared_aa_endpoint_states A j₀ S r hA).2 (hδ.trans h1)
        refine ⟨((-1 : ℂ) ^ r), ?_⟩
        rw [show Run (preparedMark S) (preparedAACircuit A j₀ r) (Qatlib.Foundations.PureStateMath.Ket j₀)
              = ((-1 : ℂ) ^ r) • preparedAAState A j₀ from hend]
        exact clause88_collapse_smul _ _ _
      · have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm h0)
        have hδlt : δ < 1 := lt_of_le_of_ne (le_trans hδε hε1) h1
        set θ : ℝ := Real.arcsin (Real.sqrt δ) with hθe
        have hθpos : 0 < θ := by
          rw [hθe]; exact Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hδpos)
        have hθlt : θ < Real.pi / 2 := by
          rw [hθe]
          refine Real.arcsin_lt_pi_div_two.mpr ?_
          have h : Real.sqrt δ < Real.sqrt 1 := Real.sqrt_lt_sqrt hδ0 hδlt
          rwa [Real.sqrt_one] at h
        have hsin : Real.sin θ = Real.sqrt δ := by
          rw [hθe]
          exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg δ])
            (by have := Real.sqrt_le_sqrt (le_trans hδε hε1); rwa [Real.sqrt_one] at this)
        have hprob : MeasureProb (preparedAAState A j₀) S = Real.sin θ ^ 2 := by
          rw [hδ, hsin]
          exact (Real.sq_sqrt hδ0).symm
        have hrot := prepared_aa_actual_rotation A j₀ S θ r hA hθpos hθlt hprob
        refine ⟨((Real.sin ((2 * (r : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ), ?_⟩
        rw [hrot, clause88_collapse_add, clause88_collapse_smul, clause88_collapse_smul, clause88_collapse_sub,
          clause88_collapse_idem, sub_self, smul_zero, _root_.zero_add]
  · exact (prepared_aa_separate_access_word A j₀ S r hA).2.2.1
end
end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
