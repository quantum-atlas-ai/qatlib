/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.LindbladSemigroupDefs
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.GibbsMetropolis
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan

/-!
# Lindblad mixing and Metropolis specifications

This module derives KMS chi squared contraction and trace distance mixing for Lindblad
semigroups under self adjointness and a spectral gap hypothesis. It also derives exponential
entropy decay from `EntropyContractionRate` and a linear lower retention bound from
`MlsiEntropyProduction`. `TunableQuerySpec` packages these estimates, while
`OptimizedTunableSpec` packages Metropolis assembly, approximation, and query cost identities.
Background on quantum dynamical semigroups is given in [Lindblad1976].

## Main statements

* `kmsChiSq_contract`: Under KMS self adjointness and a gap bound `γ`, the KMS chi squared
  quantity contracts by `exp (-2 * γ * t)` for nonnegative times and positive definite reference
  density.
* `entropyContraction_exponential`: The small time contraction property `EntropyContractionRate`
  implies relative entropy decay by `exp (-γ * t)` at every nonnegative time for density inputs
  and positive definite reference density.
* `mlsiEntropyProduction_linear`: For nonnegative time with `γ * t ≤ 1`, `MlsiEntropyProduction`
  bounds the evolved relative entropy below by `1 - γ * t` times its initial value.
* `stageB_lindblad_semigroup_clause3`: The Metropolis assembly, approximation, and cost results
  satisfy `OptimizedTunableSpec`.

## References

* [Lindblad, 1976][Lindblad1976]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Qatlib.Concepts.QuantumGibbs.DetailedBalance
open Qatlib.Concepts.QuantumGibbs.RejectionRewind
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal BigOperators Classical

noncomputable section

variable {D : ℕ}

/-- For density operators with positive definite reference `ρ`, the KMS chi squared quantity
equals the squared KMS norm of the centered density ratio. -/
theorem kmsChiSq_eq_centered_norm {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hσ : IsDensityOperator σ) :
    kmsChiSq ρ σ = (kmsNorm ρ (kmsDensityRatio ρ (σ - ρ))) ^ 2 := by
  have h := kmsNorm_densityRatio_error_sq hρ hfull hσ
  unfold kmsChiSq
  linarith

/-- The KMS chi squared quantity is nonnegative for density operators with positive definite
reference state. -/
theorem kmsChiSq_nonneg {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hσ : IsDensityOperator σ) :
    0 ≤ kmsChiSq ρ σ := by
  rw [kmsChiSq_eq_centered_norm hρ hfull hσ]
  positivity

/-- For a positive definite reference density operator, the KMS chi squared quantity is at most
`kmsMinSpectralWeight ρ ^ 2 - 1`. -/
theorem kmsChiSq_le_minSpectralWeight {ρ σ : Operator D}
    (_hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hσ : IsDensityOperator σ) :
    kmsChiSq ρ σ ≤ kmsMinSpectralWeight ρ ^ 2 - 1 := by
  have h := kmsNorm_densityRatio_le_inverse_sqrt hfull hσ
  have hnonneg : 0 ≤ kmsNorm ρ (kmsDensityRatio ρ σ) := Real.sqrt_nonneg _
  have hsq := mul_self_le_mul_self hnonneg h
  unfold kmsChiSq kmsMinSpectralWeight
  nlinarith [hsq]

/-- KMS self adjointness and a gap bound `γ` give decay of the centered density ratio norm by
`exp (-γ * t)` for nonnegative times and density inputs. -/
theorem kmsDensityRatio_centered_norm_le (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    kmsNorm ρ (kmsDensityRatio ρ (lindbladSemigroup G t σ - ρ)) ≤
      Real.exp (-γ * t) * kmsNorm ρ (kmsDensityRatio ρ (σ - ρ)) := by
  let f (u : ℝ) := kmsDensityRatio ρ (lindbladSemigroup G u σ - ρ)
  have hzero := lindbladApply_eq_zero_of_heisenberg_kmsSelfAdjoint G ρ hρ.1 hself
  have hL (u : ℝ) : lindbladApply G (lindbladSemigroup G u σ - ρ) =
      lindbladApply G (lindbladSemigroup G u σ) := by
    change (lindbladMap G) (_ - _) = (lindbladMap G) _
    rw [map_sub]
    change _ - lindbladApply G ρ = _
    rw [hzero, sub_zero]
  have hf (u : ℝ) : HasDerivAt f (gkslHeisenbergMap G (f u)) u := by
    have hd := hasDerivAt_lindbladSemigroup G σ u
    have h :=
        ((kmsDensityRatioMap ρ).restrictScalars ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u (hd.sub_const ρ)
    change HasDerivAt f (kmsDensityRatio ρ (lindbladApply G (lindbladSemigroup G u σ))) u at h
    rw [← hL u, kmsDensityRatio_lindbladApply G hfull hself] at h
    exact h
  have hm (u : ℝ) : Matrix.trace (ρ * f u) = 0 := by
    dsimp only [f]
    rw [trace_kmsDensityRatio hfull, Matrix.trace_sub, trace_lindbladSemigroup, hσ.2, hρ.2,
      sub_self]
  have hn := kmsNorm_decay_of_gap ρ (gkslHeisenbergMap G) γ hgap f hf hm t ht
  have hinit : f 0 = kmsDensityRatio ρ (σ - ρ) := by
    simp only [f, lindbladSemigroup_zero_apply]
  rw [hinit] at hn
  exact hn

/-- Under KMS self adjointness and a gap bound `γ`, the KMS chi squared quantity contracts by
`exp (-2 * γ * t)` for nonnegative times and positive definite reference density. -/
theorem kmsChiSq_contract (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    kmsChiSq ρ (lindbladSemigroup G t σ) ≤ Real.exp (-2 * γ * t) * kmsChiSq ρ σ := by
  have hτ := lindbladSemigroup_isDensityOperator G t ht σ hσ
  have hn := kmsDensityRatio_centered_norm_le G hρ hfull hself γ hgap hσ t ht
  have hc1 := kmsChiSq_eq_centered_norm hρ hfull hτ
  have hc2 := kmsChiSq_eq_centered_norm hρ hfull hσ
  have hexp : (Real.exp (-γ * t)) ^ 2 = Real.exp (-2 * γ * t) := by
    have h := (Real.exp_nat_mul (-γ * t) 2).symm
    have h' : Real.exp (2 * (-γ * t)) = Real.exp (-2 * γ * t) := by
      rw [show 2 * (-γ * t) = -2 * γ * t by ring]
    exact h.trans h'
  calc kmsChiSq ρ (lindbladSemigroup G t σ)
      = (kmsNorm ρ (kmsDensityRatio ρ (lindbladSemigroup G t σ - ρ))) ^ 2 := hc1
    _ ≤ (Real.exp (-γ * t) * kmsNorm ρ (kmsDensityRatio ρ (σ - ρ))) ^ 2 := by
      have hA : 0 ≤ kmsNorm ρ (kmsDensityRatio ρ (lindbladSemigroup G t σ - ρ)) :=
        Real.sqrt_nonneg _
      simpa only [pow_two] using! (mul_self_le_mul_self hA hn)
    _ = Real.exp (-2 * γ * t) * (kmsNorm ρ (kmsDensityRatio ρ (σ - ρ))) ^ 2 := by
      rw [mul_pow, hexp]
    _ = Real.exp (-2 * γ * t) * kmsChiSq ρ σ := by
      exact congrArg (fun z : ℝ => Real.exp (-2 * γ * t) * z) hc2.symm

/-- Under the stated KMS self adjointness and gap hypotheses, trace distance to the positive
definite reference density is at most `exp (-γ * t) * kmsMinSpectralWeight ρ / 2`. -/
theorem traceDistance_le_exp_minSpectralWeight (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) (γ : ℝ)
    (hgap : KmsGapAtLeast ρ (gkslHeisenbergMap G) γ) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    traceDistance (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-γ * t) * kmsMinSpectralWeight ρ / 2 := by
  have h := lindblad_traceDistance_le_inverse_sqrt G hρ hfull hself γ hgap hσ t ht
  simpa [kmsMinSpectralWeight] using! h

/-- KMS self adjointness of the Heisenberg generator with respect to a density operator makes
that density operator stationary. -/
theorem isStationary_of_heisenberg_kmsSelfAdjoint (G : GKSL D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G)) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.IsStationary G ρ :=
  stationary_of_heisenberg_kmsSelfAdjoint G ρ hρ.1 hself

/-- Relative entropy between density operators is nonnegative when the reference density
operator is positive definite. -/
theorem relativeEntropy_nonneg {σ ρ : Operator D}
    (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) :
    0 ≤ relativeEntropy σ ρ := by
  have h := relativeEntropy_eq_qRelativeEnt hσ hρ hfull
  exact ENNReal.toReal_nonneg.trans (le_of_eq h.symm)

/-- The small time entropy contraction hypothesis gives the factor `(1 - γ * h) ^ n` at time `n
* h` for `0 < h ≤ 1` and density inputs. -/
theorem entropyContractionRate_iterate_aux (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (_hρ : IsDensityOperator ρ) (_hfull : ρ.PosDef)
    (hcont : EntropyContractionRate G ρ γ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∀ (n : ℕ) (σ : Operator D), IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ ≤
        (1 - γ * h) ^ n * relativeEntropy σ ρ := by
  have hgh : γ * h ≤ 1 := by
    have := mul_le_mul hcont.2.1 hh1 (by linarith) (by linarith)
    nlinarith [this]
  have hfac : 0 ≤ 1 - γ * h := by linarith
  intro n
  induction n with
  | zero =>
      intro σ hσ
      simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
      intro σ hσ
      have hτ : IsDensityOperator (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
      have hsem : lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
          = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        calc lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
            = lindbladSemigroup G (h + (n : ℝ) * h) σ := by
              congr 1
              push_cast
              ring
          _ = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) :=
            lindbladSemigroup_add G h ((n : ℝ) * h) σ
      rw [hsem]
      have hstep := hcont.2.2 h (lindbladSemigroup G ((n : ℝ) * h) σ) hh hh1 hτ
      have hmul := mul_le_mul_of_nonneg_left (ih σ hσ) hfac
      have hpow : (1 - γ * h) ^ n * (1 - γ * h) = (1 - γ * h) ^ (n + 1) := by
        rw [pow_succ]
      calc relativeEntropy (lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ)) ρ
          ≤ (1 - γ * h) * relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ := hstep
        _ ≤ (1 - γ * h) * ((1 - γ * h) ^ n * relativeEntropy σ ρ) := hmul
        _ = (1 - γ * h) ^ (n + 1) * relativeEntropy σ ρ := by
          have hre : (1 - γ * h) * ((1 - γ * h) ^ n * relativeEntropy σ ρ)
              = ((1 - γ * h) ^ n * (1 - γ * h)) * relativeEntropy σ ρ := by ring
          rw [hre, hpow]

/-- The small time contraction property `EntropyContractionRate` implies relative entropy decay
by `exp (-γ * t)` at every nonnegative time for density inputs and positive definite
reference density. -/
theorem entropyContraction_exponential (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hcont : EntropyContractionRate G ρ γ) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤
      Real.exp (-γ * t) * relativeEntropy σ ρ := by
  by_cases hzero : t = 0
  · subst hzero
    simp [lindbladSemigroup_zero_apply]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hn1 : 1 ≤ ⌈t⌉₊ := Nat.ceil_pos.mpr htpos
    have hnge : t ≤ (⌈t⌉₊ : ℝ) :=
      (Nat.ceil_le (a := t) (n := ⌈t⌉₊)).mp le_rfl
    have hnpos : (0 : ℝ) < ⌈t⌉₊ := by exact_mod_cast hn1
    have hhpos : 0 < t / ⌈t⌉₊ := div_pos htpos hnpos
    have hhle : t / ⌈t⌉₊ ≤ 1 := (div_le_one hnpos).mpr hnge
    have hiter := entropyContractionRate_iterate_aux G ρ γ hρ hfull hcont hhpos hhle
      (⌈t⌉₊) σ hσ
    have hnh : (⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊) = t := by
      field_simp
    rw [hnh] at hiter
    have hgh : γ * (t / ⌈t⌉₊) ≤ 1 := by
      have := mul_le_mul hcont.2.1 hhle (by linarith) (by linarith)
      nlinarith [this]
    have hfac : 0 ≤ 1 - γ * (t / ⌈t⌉₊) := by linarith
    have hcmp : 1 - γ * (t / ⌈t⌉₊) ≤ Real.exp (-(γ * (t / ⌈t⌉₊))) := by
      have := Real.add_one_le_exp (-(γ * (t / ⌈t⌉₊)))
      linarith
    have hpow : (1 - γ * (t / ⌈t⌉₊)) ^ ⌈t⌉₊ ≤ Real.exp (-(γ * (t / ⌈t⌉₊))) ^ ⌈t⌉₊ :=
      pow_le_pow_left₀ hfac hcmp _
    have hexp : Real.exp (-(γ * (t / ⌈t⌉₊))) ^ ⌈t⌉₊ = Real.exp (-γ * t) := by
      have he : (⌈t⌉₊ : ℝ) * (-(γ * (t / ⌈t⌉₊))) = -γ * t := by
        calc (⌈t⌉₊ : ℝ) * (-(γ * (t / ⌈t⌉₊))) = -(γ * ((⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊))) := by ring
          _ = -(γ * t) := by rw [hnh]
          _ = -γ * t := by ring
      have hthis := (Real.exp_nat_mul (-(γ * (t / ⌈t⌉₊))) ⌈t⌉₊).symm
      rw [he] at hthis
      exact hthis
    rw [hexp] at hpow
    have hS0 : 0 ≤ relativeEntropy σ ρ := relativeEntropy_nonneg hσ hρ hfull
    have hmul := mul_le_mul_of_nonneg_right hpow hS0
    calc relativeEntropy (lindbladSemigroup G t σ) ρ
        ≤ (1 - γ * (t / ⌈t⌉₊)) ^ ⌈t⌉₊ * relativeEntropy σ ρ := hiter
      _ ≤ Real.exp (-γ * t) * relativeEntropy σ ρ := hmul

/-- Unit time entropy contraction iterates to the factor `(1 - γ) ^ n` at natural times on
density inputs. -/
theorem entropyContractionStep_iterate_aux (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (_hρ : IsDensityOperator ρ) (_hfull : ρ.PosDef)
    (hcont : EntropyContractionStep G ρ γ) :
    ∀ (n : ℕ) (σ : Operator D), IsDensityOperator σ →
      relativeEntropy (lindbladSemigroup G (n : ℝ) σ) ρ ≤
        (1 - γ) ^ n * relativeEntropy σ ρ := by
  have hfac : 0 ≤ 1 - γ := by linarith [hcont.2.1]
  intro n
  induction n with
  | zero =>
      intro σ hσ
      simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
      intro σ hσ
      have hτ : IsDensityOperator (lindbladSemigroup G (n : ℝ) σ) := by
        exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
      have hsem : lindbladSemigroup G ((n + 1 : ℕ) : ℝ) σ
          = lindbladSemigroup G 1 (lindbladSemigroup G (n : ℝ) σ) := by
        calc lindbladSemigroup G ((n + 1 : ℕ) : ℝ) σ
            = lindbladSemigroup G (1 + (n : ℝ)) σ := by
              congr 1
              push_cast
              ring
          _ = lindbladSemigroup G 1 (lindbladSemigroup G (n : ℝ) σ) :=
            lindbladSemigroup_add G 1 (n : ℝ) σ
      rw [hsem]
      have hstep := hcont.2.2 (lindbladSemigroup G (n : ℝ) σ) hτ
      have hmul := mul_le_mul_of_nonneg_left (ih σ hσ) hfac
      have hpow : (1 - γ) ^ n * (1 - γ) = (1 - γ) ^ (n + 1) := by
        rw [pow_succ]
      calc relativeEntropy (lindbladSemigroup G 1 (lindbladSemigroup G (n : ℝ) σ)) ρ
          ≤ (1 - γ) * relativeEntropy (lindbladSemigroup G (n : ℝ) σ) ρ := hstep
        _ ≤ (1 - γ) * ((1 - γ) ^ n * relativeEntropy σ ρ) := hmul
        _ = (1 - γ) ^ (n + 1) * relativeEntropy σ ρ := by
          have hre : (1 - γ) * ((1 - γ) ^ n * relativeEntropy σ ρ)
              = ((1 - γ) ^ n * (1 - γ)) * relativeEntropy σ ρ := by ring
          rw [hre, hpow]

/-- Unit time entropy contraction and KMS self adjointness give relative entropy decay by `(1 -
γ) ^ ⌊t⌋₊` for nonnegative real times. -/
theorem entropyContractionStep_geometric (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G))
    (hcont : EntropyContractionStep G ρ γ) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤
      (1 - γ) ^ ⌊t⌋₊ * relativeEntropy σ ρ := by
  have hstat := isStationary_of_heisenberg_kmsSelfAdjoint G hρ hself
  have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (a := t) ht
  have hr0 : 0 ≤ t - (⌊t⌋₊ : ℝ) := by linarith
  have hsem : lindbladSemigroup G t σ
      = lindbladSemigroup G ⌊t⌋₊ (lindbladSemigroup G (t - (⌊t⌋₊ : ℝ)) σ) := by
    calc lindbladSemigroup G t σ
        = lindbladSemigroup G ((⌊t⌋₊ : ℝ) + (t - (⌊t⌋₊ : ℝ))) σ := by
          congr 1
          ring
      _ = lindbladSemigroup G ⌊t⌋₊ (lindbladSemigroup G (t - (⌊t⌋₊ : ℝ)) σ) :=
        lindbladSemigroup_add G ⌊t⌋₊ (t - (⌊t⌋₊ : ℝ)) σ
  rw [hsem]
  have hτr : IsDensityOperator (lindbladSemigroup G (t - (⌊t⌋₊ : ℝ)) σ) := by
    exact lindbladSemigroup_isDensityOperator G _ hr0 σ hσ
  have hiter := entropyContractionStep_iterate_aux G ρ γ hρ hfull hcont ⌊t⌋₊ _ hτr
  have hmono := lindbladSemigroup_relativeEntropy_le G hρ hfull hstat hσ _ hr0
  have hbase : 0 ≤ 1 - γ := by linarith [hcont.2.1]
  have hfac : 0 ≤ (1 - γ) ^ ⌊t⌋₊ := pow_nonneg hbase _
  have hmul := mul_le_mul_of_nonneg_left hmono hfac
  calc relativeEntropy (lindbladSemigroup G ⌊t⌋₊ (lindbladSemigroup G (t - (⌊t⌋₊ : ℝ)) σ)) ρ
      ≤ (1 - γ) ^ ⌊t⌋₊ * relativeEntropy (lindbladSemigroup G (t - (⌊t⌋₊ : ℝ)) σ) ρ := hiter
    _ ≤ (1 - γ) ^ ⌊t⌋₊ * relativeEntropy σ ρ := hmul

/-- For `t ≥ 1`, unit time entropy contraction and KMS self adjointness bound relative entropy
by `entropyComparisonConstant γ * exp (-γ * t)` times its initial value. -/
theorem entropyContractionStep_comparison (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hself : KmsSelfAdjoint ρ (gkslHeisenbergMap G))
    (hcont : EntropyContractionStep G ρ γ) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 1 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤
      entropyComparisonConstant γ * Real.exp (-γ * t) * relativeEntropy σ ρ := by
  have hbase : 0 ≤ 1 - γ := by linarith [hcont.2.1]
  have hcmp : 1 - γ ≤ Real.exp (-γ) := by
    have := Real.add_one_le_exp (-γ)
    linarith
  have hgeom := entropyContractionStep_geometric G ρ γ hρ hfull hself hcont σ hσ t
    (by linarith)
  have hpow : (1 - γ) ^ ⌊t⌋₊ ≤ Real.exp (-γ) ^ ⌊t⌋₊ := pow_le_pow_left₀ hbase hcmp _
  have hexp : Real.exp (-γ) ^ ⌊t⌋₊ = Real.exp (-γ * ⌊t⌋₊) := by
    have h := (Real.exp_nat_mul (-γ) ⌊t⌋₊).symm
    have h' : Real.exp ((⌊t⌋₊ : ℝ) * (-γ)) = Real.exp (-γ * ⌊t⌋₊) := by
      rw [show (⌊t⌋₊ : ℝ) * (-γ) = -γ * ⌊t⌋₊ by ring]
    exact h.trans h'
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hneg : (-γ : ℝ) ≤ 0 := by linarith [hcont.1.le]
  have hmul : -γ * (⌊t⌋₊ : ℝ) ≤ -γ * (t - 1) := by
    have hab : t - 1 ≤ (⌊t⌋₊ : ℝ) := by linarith
    simpa only [mul_comm] using! (mul_le_mul_of_nonpos_right hab hneg)
  have hexp2 : Real.exp (-γ * ⌊t⌋₊) ≤ Real.exp (-γ * (t - 1)) :=
    Real.exp_le_exp.mpr hmul
  have hexp3 : Real.exp (-γ * (t - 1)) = entropyComparisonConstant γ * Real.exp (-γ * t) := by
    rw [entropyComparisonConstant]
    have he : -γ * (t - 1) = (-γ * t) + γ := by ring
    rw [he, Real.exp_add]
    ring
  have hS0 : 0 ≤ relativeEntropy σ ρ := relativeEntropy_nonneg hσ hρ hfull
  have h1 := mul_le_mul_of_nonneg_right hpow hS0
  have h2a := mul_le_mul_of_nonneg_right hexp.le hS0
  have h2b := mul_le_mul_of_nonneg_right hexp2 hS0
  have h3 := mul_le_mul_of_nonneg_right (le_of_eq hexp3) hS0
  calc relativeEntropy (lindbladSemigroup G t σ) ρ
      ≤ (1 - γ) ^ ⌊t⌋₊ * relativeEntropy σ ρ := hgeom
    _ ≤ Real.exp (-γ) ^ ⌊t⌋₊ * relativeEntropy σ ρ := h1
    _ ≤ Real.exp (-γ * ⌊t⌋₊) * relativeEntropy σ ρ := h2a
    _ ≤ Real.exp (-γ * (t - 1)) * relativeEntropy σ ρ := h2b
    _ = entropyComparisonConstant γ * Real.exp (-γ * t) * relativeEntropy σ ρ := by
      rw [hexp3]

/-- For `0 ≤ x ≤ 1`, the power `(1 - x) ^ n` is at least `1 - n * x`. -/
theorem one_sub_pow_le (x : ℝ) (n : ℕ) (_hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - n * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
      rw [hcast]
      calc 1 - ((n : ℝ) * x + x) ≤ (1 - (n : ℝ) * x) * (1 - x) := by
            nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]
        _ ≤ (1 - x) ^ n * (1 - x) := mul_le_mul_of_nonneg_right ih (by linarith)
        _ = (1 - x) ^ (n + 1) := by rw [pow_succ]

/-- The small time lower retention property `MlsiEntropyProduction` iterates to a lower relative
entropy bound with factor `(1 - γ * h) ^ n`. -/
theorem mlsiEntropyProduction_iterate_aux (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (_hρ : IsDensityOperator ρ) (_hfull : ρ.PosDef)
    (hmlsi : MlsiEntropyProduction G ρ γ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∀ (n : ℕ) (σ : Operator D), IsDensityOperator σ →
      (1 - γ * h) ^ n * relativeEntropy σ ρ ≤
        relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ := by
  have hgh : γ * h ≤ 1 := by
    have := mul_le_mul hmlsi.2.1 hh1 (by linarith) (by linarith)
    nlinarith [this]
  have hfac : 0 ≤ 1 - γ * h := by linarith
  intro n
  induction n with
  | zero =>
      intro σ hσ
      simp [lindbladSemigroup_zero_apply]
  | succ n ih =>
      intro σ hσ
      have hτ : IsDensityOperator (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        exact lindbladSemigroup_isDensityOperator G _ (by positivity) σ hσ
      have hsem : lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
          = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) := by
        calc lindbladSemigroup G (((n + 1 : ℕ) : ℝ) * h) σ
            = lindbladSemigroup G (h + (n : ℝ) * h) σ := by
              congr 1
              push_cast
              ring
          _ = lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ) :=
            lindbladSemigroup_add G h ((n : ℝ) * h) σ
      rw [hsem]
      have hstep := hmlsi.2.2 h (lindbladSemigroup G ((n : ℝ) * h) σ) hh hh1 hτ
      have hmul := mul_le_mul_of_nonneg_left (ih σ hσ) hfac
      have hpow : (1 - γ * h) ^ n * (1 - γ * h) = (1 - γ * h) ^ (n + 1) := by
        rw [pow_succ]
      calc (1 - γ * h) ^ (n + 1) * relativeEntropy σ ρ
          ≤ (1 - γ * h) * ((1 - γ * h) ^ n * relativeEntropy σ ρ) := by
            have hre : (1 - γ * h) ^ (n + 1) * relativeEntropy σ ρ
                = ((1 - γ * h) ^ n * (1 - γ * h)) * relativeEntropy σ ρ := by rw [hpow]
            rw [hre]
            exact le_of_eq (by ring)
        _ ≤ (1 - γ * h) * relativeEntropy (lindbladSemigroup G ((n : ℝ) * h) σ) ρ := hmul
        _ ≤ relativeEntropy (lindbladSemigroup G h (lindbladSemigroup G ((n : ℝ) * h) σ)) ρ := hstep

/-- For nonnegative time with `γ * t ≤ 1`, `MlsiEntropyProduction` bounds the evolved relative
entropy below by `1 - γ * t` times its initial value. -/
theorem mlsiEntropyProduction_linear (G : GKSL D) (ρ : Operator D) (γ : ℝ)
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef)
    (hmlsi : MlsiEntropyProduction G ρ γ) (σ : Operator D) (hσ : IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) (hγt : γ * t ≤ 1) :
    (1 - γ * t) * relativeEntropy σ ρ ≤ relativeEntropy (lindbladSemigroup G t σ) ρ := by
  by_cases hzero : t = 0
  · subst hzero
    simp [lindbladSemigroup_zero_apply]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
    have hn1 : 1 ≤ ⌈t⌉₊ := Nat.ceil_pos.mpr htpos
    have hnge : t ≤ (⌈t⌉₊ : ℝ) :=
      (Nat.ceil_le (a := t) (n := ⌈t⌉₊)).mp le_rfl
    have hnpos : (0 : ℝ) < ⌈t⌉₊ := by exact_mod_cast hn1
    have hhpos : 0 < t / ⌈t⌉₊ := div_pos htpos hnpos
    have hhle : t / ⌈t⌉₊ ≤ 1 := (div_le_one hnpos).mpr hnge
    have hiter := mlsiEntropyProduction_iterate_aux G ρ γ hρ hfull hmlsi hhpos hhle
      (⌈t⌉₊) σ hσ
    have hnh : (⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊) = t := by
      field_simp
    rw [hnh] at hiter
    have hx : γ * (t / ⌈t⌉₊) ≤ 1 := by
      have := mul_le_mul hmlsi.2.1 hhle (by linarith) (by linarith)
      nlinarith [this]
    have hbern := one_sub_pow_le (γ * (t / ⌈t⌉₊)) ⌈t⌉₊
      (mul_nonneg hmlsi.1.le (le_of_lt hhpos)) hx
    have hnhg : (⌈t⌉₊ : ℝ) * (γ * (t / ⌈t⌉₊)) = γ * t := by
      calc (⌈t⌉₊ : ℝ) * (γ * (t / ⌈t⌉₊)) = γ * ((⌈t⌉₊ : ℝ) * (t / ⌈t⌉₊)) := by ring
        _ = γ * t := by rw [hnh]
    have hS0 : 0 ≤ relativeEntropy σ ρ := relativeEntropy_nonneg hσ hρ hfull
    have hmul := mul_le_mul_of_nonneg_right hbern hS0
    calc (1 - γ * t) * relativeEntropy σ ρ
        = (1 - (⌈t⌉₊ : ℝ) * (γ * (t / ⌈t⌉₊))) * relativeEntropy σ ρ := by
          have hrev : γ * t = (⌈t⌉₊ : ℝ) * (γ * (t / ⌈t⌉₊)) := hnhg.symm
          rw [hrev]
      _ ≤ (1 - γ * (t / ⌈t⌉₊)) ^ ⌈t⌉₊ * relativeEntropy σ ρ := hmul
      _ ≤ relativeEntropy (lindbladSemigroup G t σ) ρ := hiter

/-- The collection of conditional Lindblad stationarity, trace mixing, chi squared contraction,
entropy contraction and comparison, lower retention, and entropy monotonicity estimates. -/
structure TunableQuerySpec : Prop where

  stationarity : ∀ (D : ℕ) (G : GKSL D) {ρ : Operator D},
    IsDensityOperator ρ → KmsSelfAdjoint ρ (gkslHeisenbergMap G) →
      Qatlib.Concepts.LindbladFlow.GkslSemigroup.IsStationary G ρ

  traceMixing : ∀ (D : ℕ) (G : GKSL D) {ρ σ : Operator D} (γ : ℝ),
    IsDensityOperator ρ → ρ.PosDef → KmsSelfAdjoint ρ (gkslHeisenbergMap G) →
    KmsGapAtLeast ρ (gkslHeisenbergMap G) γ → IsDensityOperator σ →
    ∀ t : ℝ, 0 ≤ t →
      traceDistance (lindbladSemigroup G t σ) ρ ≤
        Real.exp (-γ * t) * kmsMinSpectralWeight ρ / 2

  chiSqContraction : ∀ (D : ℕ) (G : GKSL D) {ρ σ : Operator D} (γ : ℝ),
    IsDensityOperator ρ → ρ.PosDef → KmsSelfAdjoint ρ (gkslHeisenbergMap G) →
    KmsGapAtLeast ρ (gkslHeisenbergMap G) γ → IsDensityOperator σ →
    ∀ t : ℝ, 0 ≤ t →
      kmsChiSq ρ (lindbladSemigroup G t σ) ≤ Real.exp (-2 * γ * t) * kmsChiSq ρ σ

  chiSqPrefactor : ∀ (D : ℕ) {ρ σ : Operator D},
    IsDensityOperator ρ → ρ.PosDef → IsDensityOperator σ →
      kmsChiSq ρ σ ≤ kmsMinSpectralWeight ρ ^ 2 - 1

  entropyContraction : ∀ (D : ℕ) (G : GKSL D) (ρ : Operator D) (γ : ℝ),
    IsDensityOperator ρ → ρ.PosDef → EntropyContractionRate G ρ γ →
    ∀ σ : Operator D, IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
      relativeEntropy (lindbladSemigroup G t σ) ρ ≤
        Real.exp (-γ * t) * relativeEntropy σ ρ

  entropyComparison : ∀ (D : ℕ) (G : GKSL D) (ρ : Operator D) (γ : ℝ),
    IsDensityOperator ρ → ρ.PosDef → KmsSelfAdjoint ρ (gkslHeisenbergMap G) →
    EntropyContractionStep G ρ γ → ∀ σ : Operator D, IsDensityOperator σ →
    ∀ t : ℝ, 1 ≤ t →
      relativeEntropy (lindbladSemigroup G t σ) ρ ≤
        entropyComparisonConstant γ * Real.exp (-γ * t) * relativeEntropy σ ρ

  mlsiRetention : ∀ (D : ℕ) (G : GKSL D) (ρ : Operator D) (γ : ℝ),
    IsDensityOperator ρ → ρ.PosDef → MlsiEntropyProduction G ρ γ →
    ∀ σ : Operator D, IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t → γ * t ≤ 1 →
      (1 - γ * t) * relativeEntropy σ ρ ≤ relativeEntropy (lindbladSemigroup G t σ) ρ

  entropyMonotone : ∀ (D : ℕ) (G : GKSL D) {ρ σ : Operator D},
    IsDensityOperator ρ → ρ.PosDef → KmsSelfAdjoint ρ (gkslHeisenbergMap G) →
    IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
      relativeEntropy (lindbladSemigroup G t σ) ρ ≤ relativeEntropy σ ρ

/-- The Lindblad semigroup estimates satisfy the complete proposition `TunableQuerySpec`. -/
theorem stageB_lindblad_semigroup_clause2 : TunableQuerySpec where
  stationarity := fun _ G _ hρ hself =>
    isStationary_of_heisenberg_kmsSelfAdjoint G hρ hself
  traceMixing := fun _ G _ _ γ hρ hfull hself hgap hσ t ht =>
    traceDistance_le_exp_minSpectralWeight G hρ hfull hself γ hgap hσ t ht
  chiSqContraction := fun _ G _ _ γ hρ hfull hself hgap hσ t ht =>
    kmsChiSq_contract G hρ hfull hself γ hgap hσ t ht
  chiSqPrefactor := fun _ _ _ hρ hfull hσ => kmsChiSq_le_minSpectralWeight hρ hfull hσ
  entropyContraction := fun _ G ρ γ hρ hfull hcont σ hσ t ht =>
    entropyContraction_exponential G ρ γ hρ hfull hcont σ hσ t ht
  entropyComparison := fun _ G ρ γ hρ hfull hself hcont σ hσ t ht =>
    entropyContractionStep_comparison G ρ γ hρ hfull hself hcont σ hσ t ht
  mlsiRetention := fun _ G ρ γ hρ hfull hmlsi σ hσ t ht hγt =>
    mlsiEntropyProduction_linear G ρ γ hρ hfull hmlsi σ hσ t ht hγt
  entropyMonotone := fun _ G _ _ hρ hfull hself hσ t ht =>
    lindbladSemigroup_relativeEntropy_le G hρ hfull
      (isStationary_of_heisenberg_kmsSelfAdjoint G hρ hself) hσ t ht

/-- The Temme acceptance map is the sum of its initial energy rows. -/
theorem metropolisAcceptRow_sum {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) :
    temmeAcceptMap E ψ ens β ρ = ∑ i, metropolisAcceptRow E ψ ens β ρ i := by
  unfold temmeAcceptMap metropolisAcceptRow
  rw [Finset.sum_comm]

/-- An acceptance row vanishes when its initial index is not an energy representative. -/
theorem metropolisAcceptFilter {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) (i : Fin D)
    (hni : ¬ isEnergyRep E i) : metropolisAcceptRow E ψ ens β ρ i = 0 := by
  have hterm : ∀ (j : Fin D) (c : Fin ens.count),
      ((if isEnergyRep E i ∧ isEnergyRep E j then (1 : ℝ) else 0) *
          ens.weight c * thermalAcceptance E β i j) •
        (energyPi E ψ j * ens.gate c * energyPi E ψ i * ρ * energyPi E ψ i *
          (ens.gate c)ᴴ * energyPi E ψ j) = 0 := by
    intro j c
    have hguard : (if isEnergyRep E i ∧ isEnergyRep E j then (1 : ℝ) else 0) = 0 := by
      rw [if_neg (by simp [hni])]
    simp only [hguard, zero_mul, zero_smul]
  unfold metropolisAcceptRow
  refine Finset.sum_eq_zero fun j _ => ?_
  refine Finset.sum_eq_zero fun c _ => ?_
  exact hterm j c

/-- A rejection row vanishes when its initial index is not an energy representative. -/
theorem metropolisRejectFilter {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (ρ : Operator D) (i : Fin D)
    (hni : ¬ isEnergyRep E i) : metropolisRejectRow E ψ C β n s ρ i = 0 := by
  have hterm : ∀ (l r : Fin (n + 1) → Fin D),
      (if isEnergyRep E i ∧ (∀ j, isEnergyRep E (l j)) ∧ (∀ j, isEnergyRep E (r j))
        then temmeG E β i n s l r else 0) •
        (temmeD E ψ C i n l * ρ * (temmeD E ψ C i n r)ᴴ) = 0 := by
    intro l r
    have hguard : (if isEnergyRep E i ∧ (∀ j, isEnergyRep E (l j)) ∧ (∀ j, isEnergyRep E (r j))
        then temmeG E β i n s l r else 0) = 0 := by
      rw [if_neg (by simp [hni])]
    rw [hguard, zero_smul]
  unfold metropolisRejectRow
  refine Finset.sum_eq_zero fun l _ => ?_
  refine Finset.sum_eq_zero fun r _ => ?_
  exact hterm l r

/-- The Temme one step map is the sum of its acceptance map and total rejection map. -/
theorem metropolisOneStep_assembly {D : ℕ} (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
    (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) :
    temmeMapFun E ψ ens β ρ = temmeAcceptMap E ψ ens β ρ + temmeBtotal E ψ ens β ρ := rfl

/-- In positive dimension, the Temme Gibbs operator built from an orthonormal energy basis is a
density operator. -/
theorem metropolisGibbsDensity {D : ℕ} (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ψ : Fin D → QState (Fin D))
    (horth : ∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) :
    IsDensityOperator (temmeGibbsState D hD E β ψ) :=
  temmeGibbsState_isDensity hD E β ψ horth

/-- A completely positive trace preserving map satisfying quantum detailed balance with the
stated Gibbs density fixes that density. -/
theorem metropolisGibbsFixedPoint {D : ℕ} (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
    (ψ : Fin D → QState (Fin D))
    (horth : ∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0)
    (T : Operator D →ₗ[ℂ] Operator D) (hcp : CompletelyPositive T) (htp : TracePreserving T)
    (hdb : QuantumDetailedBalance T (temmeGibbsState D hD E β ψ)) :
    T (temmeGibbsState D hD E β ψ) = temmeGibbsState D hD E β ψ := by
  exact quantumDetailedBalanceFixedPoint D ⟨T, hcp, htp⟩ _
    (temmeGibbsState_isDensity hD E β ψ horth) hdb

/-- For two orthogonal projectors and a normalized input fixed by the first, rejection failure
after `n` rounds is at most `1 / (2 * (n + 1))`. -/
theorem metropolisRejectWindow {D : ℕ} (P Q : Operator D) (hPs : P.IsHermitian) (hPi : P * P = P)
    (hQs : Q.IsHermitian) (hQi : Q * Q = Q) (ψ : QState (Fin D)) (hnorm : Qatlib.Foundations.PureStateMath.Inner ψ ψ = 1)
    (hψ : P *ᵥ ψ = ψ) (n : ℕ) : rejectFailProb P Q ψ n ≤ 1 / (2 * (n + 1)) :=
  rejection_failure_bound_all_rounds D P Q hPs hPi hQs hQi ψ hnorm hψ n

/-- For rational energies in `[0, 1]` on a nonempty space, the rational heat bath has positive
total weight and trace norm error at most `4 * (1 / 2) ^ K` from the rational energy Gibbs
density. -/
theorem metropolisRationalWindow :
    ∀ (N K : ℕ) (E : Fin N → ℚ), 0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) →
      ∃ hW : 0 < weightTotal (boltzmannIntegerWeights K E),
        IsDensityOperator (rationalEnergyGibbsDensity E) ∧
        Matrix.traceNorm
          (rationalHeatBathDensity (boltzmannIntegerWeights K E) hW
            - rationalEnergyGibbsDensity E) ≤ 4 * (1 / 2 : ℝ) ^ K :=
  clause28_block2_rationalWindow

/-- The step ledger query count equals `metropolisActualStepQueries M n nStar`. -/
theorem metropolisActualStepCost (D M k n nStar : ℕ) :
    (metropolisStepLedger D M k n nStar).stepQueries = metropolisActualStepQueries M n nStar := rfl

/-- The run ledger query count is `m` times `metropolisActualStepQueries M n nStar`. -/
theorem metropolisActualRunCost (D M k n nStar m : ℕ) :
    (metropolisRunLedger m D M k n nStar).stepQueries = m * metropolisActualStepQueries M n nStar :=
  rfl

/-- The specification cost at dimension two is strictly smaller than the actual step query count
for parameters `M = 4`, `n = 1`, and `nStar = 0`. -/
theorem metropolisSpecCostUnpacked :
    metropolisSpecStepCost 2 < metropolisActualStepQueries 4 1 0 := by
  unfold metropolisSpecStepCost metropolisActualStepQueries qpeWindowQueries
  norm_num

/-- The collection of Metropolis row assembly and filtering identities, conditional Gibbs
stationarity, rejection and rational approximation bounds, and actual query cost identities
and comparison. -/
structure OptimizedTunableSpec : Prop where

  acceptAssembly : ∀ (D : ℕ) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
      (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D),
    temmeAcceptMap E ψ ens β ρ = ∑ i, metropolisAcceptRow E ψ ens β ρ i

  acceptFilter : ∀ (D : ℕ) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
      (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D) (i : Fin D),
    ¬ isEnergyRep E i → metropolisAcceptRow E ψ ens β ρ i = 0

  rejectFilter : ∀ (D : ℕ) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
      (C : Operator D) (β : ℝ) (n : ℕ) (s : Fin n → Bool) (ρ : Operator D) (i : Fin D),
    ¬ isEnergyRep E i → metropolisRejectRow E ψ C β n s ρ i = 0

  oneStepAssembly : ∀ (D : ℕ) (E : Fin D → ℝ) (ψ : Fin D → QState (Fin D))
      (ens : ProposalEnsemble D) (β : ℝ) (ρ : Operator D),
    temmeMapFun E ψ ens β ρ = temmeAcceptMap E ψ ens β ρ + temmeBtotal E ψ ens β ρ

  gibbsDensity : ∀ (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ) (ψ : Fin D → QState (Fin D)),
    (∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
    IsDensityOperator (temmeGibbsState D hD E β ψ)

  gibbsFixedPoint : ∀ (D : ℕ) (hD : 0 < D) (E : Fin D → ℝ) (β : ℝ)
      (ψ : Fin D → QState (Fin D)),
    (∀ i j : Fin D, Qatlib.Foundations.PureStateMath.Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
    ∀ (T : Operator D →ₗ[ℂ] Operator D), CompletelyPositive T → TracePreserving T →
    QuantumDetailedBalance T (temmeGibbsState D hD E β ψ) →
    T (temmeGibbsState D hD E β ψ) = temmeGibbsState D hD E β ψ

  windowError : ∀ (D : ℕ) (P Q : Operator D), P.IsHermitian → P * P = P →
    Q.IsHermitian → Q * Q = Q → ∀ ψ : QState (Fin D), Qatlib.Foundations.PureStateMath.Inner ψ ψ = 1 → P *ᵥ ψ = ψ →
    ∀ n : ℕ, rejectFailProb P Q ψ n ≤ 1 / (2 * (n + 1))

  rationalWindow : ∀ (N K : ℕ) (E : Fin N → ℚ), 0 < N → (∀ i, 0 ≤ E i ∧ E i ≤ 1) →
    ∃ hW : 0 < weightTotal (boltzmannIntegerWeights K E),
      IsDensityOperator (rationalEnergyGibbsDensity E) ∧
      Matrix.traceNorm
        (rationalHeatBathDensity (boltzmannIntegerWeights K E) hW
          - rationalEnergyGibbsDensity E) ≤ 4 * (1 / 2 : ℝ) ^ K

  consumerCost : ∀ (D M k n nStar m : ℕ),
    (metropolisStepLedger D M k n nStar).stepQueries = metropolisActualStepQueries M n nStar ∧
    (metropolisRunLedger m D M k n nStar).stepQueries = m * metropolisActualStepQueries M n nStar

  specCostUnpacked : metropolisSpecStepCost 2 < metropolisActualStepQueries 4 1 0

/-- The Metropolis assembly, approximation, and cost results satisfy `OptimizedTunableSpec`. -/
theorem stageB_lindblad_semigroup_clause3 : OptimizedTunableSpec where
  acceptAssembly := fun _ E ψ ens β ρ => metropolisAcceptRow_sum E ψ ens β ρ
  acceptFilter := fun _ E ψ ens β ρ i hni => metropolisAcceptFilter E ψ ens β ρ i hni
  rejectFilter := fun _ E ψ C β n s ρ i hni => metropolisRejectFilter E ψ C β n s ρ i hni
  oneStepAssembly := fun _ E ψ ens β ρ => metropolisOneStep_assembly E ψ ens β ρ
  gibbsDensity := fun _ hD E β ψ horth => metropolisGibbsDensity hD E β ψ horth
  gibbsFixedPoint := fun _ hD E β ψ horth T hcp htp hdb =>
    metropolisGibbsFixedPoint hD E β ψ horth T hcp htp hdb
  windowError := fun _ P Q hPs hPi hQs hQi ψ hnorm hψ n =>
    metropolisRejectWindow P Q hPs hPi hQs hQi ψ hnorm hψ n
  rationalWindow := fun N K E hN hE => metropolisRationalWindow N K E hN hE
  consumerCost := fun D M k n nStar m =>
    ⟨metropolisActualStepCost D M k n nStar, metropolisActualRunCost D M k n nStar m⟩
  specCostUnpacked := metropolisSpecCostUnpacked

end

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
