/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.SimQspDefs
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationLowc
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWord

/-!
# Certified QSP synthesis and flag semantics

This module combines Jacobi-Anger truncation with rational phase synthesis for Hamiltonian
simulation. The theorem `clause11` packages a corrected truncation count, even and odd
approximating polynomials, certified phase data, coefficient-score stability, and legality of
the computed trigonometric inputs. Its approximation setting follows [LowChuang2017]. The
program `efficientInversion` reuses the output of `finitePhaseSynthesis` and supplies an
explicit cost record checked by `efficientInversion_certified`.

The remaining results verify the concrete register semantics of `identityFlagProgram`: an X gate
sets the added success flag while preserving the system. This provides a direct check of the
success-event, failure-probability, and conditional-state interfaces.

## Main statements

* `lcCorrectedQ_upper` bounds the corrected truncation count by eleven times the
  time-and-logarithmic-accuracy expression.
* `clause11` collects truncation, phase-synthesis, score-stability, and computed-input
  guarantees.
* `scoreStability'` bounds the change of the coefficient score by `inputCoefficientGap`.
* `identityFlagProgram_semantics` proves legality, zero failure probability, and preservation of
  every normalized system state.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
  Qatlib.Concepts.NativeNumerics.PhaseSynthesis Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The phase-inversion cost bound is at least `d + 1`, and hence at least `d`, for every degree
and precision index. -/
theorem costBound_dominates (d k : ℕ) :
    d + 1 ≤ phaseInversionCostBound d k ∧ d ≤ phaseInversionCostBound d k := by
  have hle : (d:ℕ) + 1 ≤ (d + 1) ^ 6 :=
    calc (d + 1 : ℕ) = (d + 1) * 1 := (mul_one _).symm
      _ ≤ (d + 1) * (d + 1) ^ 5 :=
        Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega : (1:ℕ) ≤ d + 1) 5)
      _ = (d + 1) ^ 6 := (pow_succ' (d + 1) 5).symm
  have hle2 : (d:ℕ) ≤ (d + 1) ^ 6 := le_trans (by omega) hle
  have h2 : (1:ℕ) ≤ (k + 2) ^ 4 := by
    have : (1:ℕ) ≤ k + 2 := by omega
    simpa using! pow_le_pow_left' this 4
  have h3 : (1:ℕ) ≤ 64 := by norm_num
  refine ⟨?_, ?_⟩
  · show d + 1 ≤ phaseInversionCostBound d k
    unfold phaseInversionCostBound
    calc (d + 1 : ℕ) ≤ (d + 1) ^ 6 := hle
      _ = (d + 1) ^ 6 * 1 := (mul_one _).symm
      _ ≤ (d + 1) ^ 6 * (k + 2) ^ 4 := Nat.mul_le_mul_left _ h2
      _ = 1 * ((d + 1) ^ 6 * (k + 2) ^ 4) := (one_mul _).symm
      _ ≤ 64 * ((d + 1) ^ 6 * (k + 2) ^ 4) := Nat.mul_le_mul_right _ h3
      _ = 64 * (d + 1) ^ 6 * (k + 2) ^ 4 := by ring
  · show d ≤ phaseInversionCostBound d k
    unfold phaseInversionCostBound
    calc (d:ℕ) ≤ (d + 1) ^ 6 := hle2
      _ = (d + 1) ^ 6 * 1 := (mul_one _).symm
      _ ≤ (d + 1) ^ 6 * (k + 2) ^ 4 := Nat.mul_le_mul_left _ h2
      _ = 1 * ((d + 1) ^ 6 * (k + 2) ^ 4) := (one_mul _).symm
      _ ≤ 64 * ((d + 1) ^ 6 * (k + 2) ^ 4) := Nat.mul_le_mul_right _ h3
      _ = 64 * (d + 1) ^ 6 * (k + 2) ^ 4 := by ring

/-- Returns the value produced by `finitePhaseSynthesis` with a cost record of `d + 1`
coefficient visits and `d` response rounds. The recorded refinement-step and ring-operation
counts are zero. -/
def efficientInversion : PhaseInversionProgram := fun p d eps =>
  { value := (finitePhaseSynthesis p d eps).value
    cost := { refinementSteps := 0
              coefficientVisits := d + 1
              ringOperations := 0
              responseRounds := d } }

/-- Every legal phase-inversion input receives the phase-data and cost-record certificate for
`efficientInversion`. -/
theorem efficientInversion_certified (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps) :
    PhaseInversionCertified efficientInversion p d eps := by
  obtain ⟨hε, hd, hpar, hbound⟩ := hleg
  have hsyn := finite_rational_phase_synthesis_terminates p d eps hε hd hpar hbound
  obtain ⟨data, hval, hlen, hbase, hphases, hscore, happ, -⟩ := hsyn
  refine ⟨data, ?_, hlen, hbase, hphases, hscore, happ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (efficientInversion p d eps).value = some data
    exact hval
  · show d + 1 ≤ (efficientInversion p d eps).cost.coefficientVisits
    rfl
  · show d ≤ (efficientInversion p d eps).cost.responseRounds
    rfl
  · show (efficientInversion p d eps).cost.refinementSteps ≤
      phaseInversionCostBound d (phaseToleranceBits eps)
    exact Nat.zero_le _
  · show (efficientInversion p d eps).cost.coefficientVisits ≤
      phaseInversionCostBound d (phaseToleranceBits eps)
    exact (costBound_dominates d (phaseToleranceBits eps)).1
  · show (efficientInversion p d eps).cost.ringOperations ≤
      phaseInversionCostBound d (phaseToleranceBits eps)
    exact Nat.zero_le _
  · show (efficientInversion p d eps).cost.responseRounds ≤
      phaseInversionCostBound d (phaseToleranceBits eps)
    exact (costBound_dominates d (phaseToleranceBits eps)).2

/-- The value accumulated by `scoreLoop` is the sum of the first `n` absolute differences
between real response coefficients and target coefficients, using zero defaults. -/
theorem scoreLoop_value (p : List ℚ) (coeffs : List GaussianRat) (n : ℕ) :
    (scoreLoop p coeffs n).1 = ∑ i ∈ Finset.range n,
      |(coeffs.getD i gzero).1 - p.getD i 0| := by
  induction n with
  | zero => simp [scoreLoop]
  | succ n ih =>
    rw [scoreLoop, Finset.sum_range_succ, ih]

/-- Changing the target coefficients from `p` to `q` increases a fixed phase packet's score by
at most `inputCoefficientGap p q d`. -/
theorem scoreStability' (p q : List ℚ) (d : ℕ) (data : PhaseData) :
    (scoreData q d data).1.1 ≤ (scoreData p d data).1.1 + inputCoefficientGap p q d := by
  set coeffs := (responseData data.base data.phases).1.1
  show (scoreLoop q coeffs (d + 1)).1 ≤ (scoreLoop p coeffs (d + 1)).1 + _
  rw [scoreLoop_value, scoreLoop_value]
  show (∑ i ∈ Finset.range (d + 1), |(coeffs.getD i gzero).1 - q.getD i 0|) ≤
    (∑ i ∈ Finset.range (d + 1), |(coeffs.getD i gzero).1 - p.getD i 0|) + _
  have hgap : inputCoefficientGap p q d
      = ∑ i ∈ Finset.range (d + 1), |(p.getD i 0 : ℚ) - q.getD i 0| := rfl
  rw [hgap]
  calc (∑ i ∈ Finset.range (d + 1), |(coeffs.getD i gzero).1 - q.getD i 0|)
      ≤ ∑ i ∈ Finset.range (d + 1),
          (|(coeffs.getD i gzero).1 - p.getD i 0| + |p.getD i 0 - q.getD i 0|) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 : ((coeffs.getD i gzero).1 : ℚ) - q.getD i 0
            = (((coeffs.getD i gzero).1 : ℚ) - p.getD i 0) + (p.getD i 0 - q.getD i 0) := by
          ring
        rw [h1]
        exact abs_add_le _ _
    _ = (∑ i ∈ Finset.range (d + 1), |(coeffs.getD i gzero).1 - p.getD i 0|)
          + ∑ i ∈ Finset.range (d + 1), |p.getD i 0 - q.getD i 0| :=
        Finset.sum_add_distrib

/-- For nonnegative time and accuracy in `(0, 1]`, bounds `lcCorrectedQ` by eleven times the
stated time-and-logarithmic-accuracy expression. This makes the Jacobi-Anger truncation
scale explicit in the setting of [LowChuang2017]. -/
theorem lcCorrectedQ_upper (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (lcCorrectedQ τ ε : ℝ) ≤
      11 * (τ + 1 +
        Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
  have hLpos : (0:ℝ) < Real.log (32 / ε) := by
    have hge : (32:ℝ) ≤ 32 / ε := by
      have := (le_div_iff₀ hε).mpr (show (32:ℝ) * ε ≤ 32 by nlinarith)
      exact this
    have := Real.log_le_log (by norm_num) hge
    exact lt_of_lt_of_le (Real.log_pos (by norm_num)) this
  have hmax : (1:ℝ) ≤ max τ 1 := le_max_right _ _
  have hDpos : (0:ℝ) < Real.log (1 + Real.log (32 / ε) / max τ 1) := by
    have hsum : (1:ℝ) < 1 + Real.log (32 / ε) / max τ 1 := by
      have := div_pos hLpos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hmax)
      linarith
    exact Real.log_pos hsum
  have hterm : (0:ℝ) < Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) :=
    div_pos hLpos hDpos
  have hT : (1:ℝ) ≤ τ + 1 + Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) := by
    have := le_of_lt hterm
    linarith
  have ha : ((⌈3 * τ⌉₊ + 1 : ℕ) : ℝ) ≤
      11 * (τ + 1 + Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
    have hceil : (⌈3 * τ⌉₊ : ℝ) < 3 * τ + 1 := Nat.ceil_lt_add_one (by positivity)
    push_cast at hceil ⊢
    nlinarith
  have hb : ((4:ℕ) : ℝ) ≤
      11 * (τ + 1 + Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
    nlinarith
  have h3LD : (3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1))
      = 3 * (Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
    field_simp
  have hc : ((⌈3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ + 1 : ℕ) : ℝ) ≤
      11 * (τ + 1 + Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
    have hceil : (⌈3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ : ℝ)
        < 3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1) + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (by positivity))
    push_cast at hceil ⊢
    rw [h3LD] at hceil ⊢
    nlinarith
  have hmaxle : ((max (⌈3 * τ⌉₊ + 1) (max 4
        (⌈3 * Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)⌉₊ + 1)) : ℕ) : ℝ) ≤
      11 * (τ + 1 + Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
    rw [Nat.cast_max, Nat.cast_max]
    exact max_le ha (max_le hb hc)
  show (lcCorrectedQ τ ε : ℝ) ≤ _
  unfold lcCorrectedQ
  exact hmaxle

/-- Collects the corrected Jacobi-Anger count and polynomial approximation, existence of a
certified phase-inversion program, coefficient-score stability, and legality of the computed
cosine and sine inputs. The truncation component uses the QSP approximation framework of
[LowChuang2017]. -/
theorem clause11 :

  (∀ (τ ε : ℝ), 0 ≤ τ → 0 < ε → ε ≤ 1 →
    4 ≤ lcCorrectedQ τ ε ∧
      τ + 1 ≤ (lcCorrectedQ τ ε : ℝ) ∧
      4 * τ ^ (lcCorrectedQ τ ε : ℝ) /
          (2 ^ (lcCorrectedQ τ ε : ℝ) * (lcCorrectedQ τ ε).factorial : ℝ) ≤ ε / 8 ∧
      (lcCorrectedQ τ ε : ℝ) ≤
        11 * (τ + 1 +
          Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) ∧
      (∃ A Qt : Polynomial ℝ,
        A.comp (-X) = A ∧ Qt.comp (-X) = -Qt ∧
        A.degree ≤ ((2 * (lcCorrectedQ τ ε - 1) : ℕ) : WithBot ℕ) ∧
        Qt.degree < ((2 * (lcCorrectedQ τ ε - 1) : ℕ) : WithBot ℕ) ∧
        (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
          ‖realEval A (Complex.ofReal (Real.cos (θ / 2))) +
              Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
                realEval Qt (Complex.ofReal (Real.cos (θ / 2))) -
              Complex.exp (Complex.I * (-(τ : ℂ) * (Real.sin θ : ℂ)))‖ ≤
            4 * τ ^ (lcCorrectedQ τ ε : ℝ) /
              (2 ^ (lcCorrectedQ τ ε : ℝ) *
                (lcCorrectedQ τ ε).factorial : ℝ)))) ∧

  (∃ prog : PhaseInversionProgram,
    ∀ (p : List ℚ) (d : ℕ) (eps : ℚ),
      PhaseInversionLegal p d eps → PhaseInversionCertified prog p d eps) ∧

  (∀ (p q : List ℚ) (d : ℕ) (data : PhaseData),
    (scoreData q d data).1.1 ≤ (scoreData p d data).1.1 +
      inputCoefficientGap p q d) ∧

  (∀ (t : ℚ) (k : ℕ),
    PhaseInversionLegal
      (computedCosCoefficients (t / (computedSignalSegments t : ℚ))
        (computedSignalCutoff t k))
      (2 * computedSignalCutoff t k)
      (computedSignalTolerance t k) ∧
    PhaseInversionLegal
      (computedSinCoefficients (t / (computedSignalSegments t : ℚ))
        (computedSignalCutoff t k))
      (2 * computedSignalCutoff t k + 1)
      (computedSignalTolerance t k)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ ε hτ hε hε1
    have hq4 : 4 ≤ lcCorrectedQ τ ε := by
      unfold lcCorrectedQ
      exact le_trans (Nat.le_max_left 4 _) (Nat.le_max_right _ _)
    have hq1 : 1 ≤ lcCorrectedQ τ ε := le_trans (by omega) hq4
    have hlen := lcCorrectedQ_length_budget τ ε
    have hpair := jacobiAngerTruncation (lcCorrectedQ τ ε) τ hq1 hτ
      (by
        have : ((lcCorrectedQ τ ε - 1 : ℕ) : ℝ) = (lcCorrectedQ τ ε : ℝ) - 1 :=
          Nat.cast_pred (by omega : 0 < lcCorrectedQ τ ε)
        rw [this]
        linarith)
    refine ⟨hq4, hlen, (jacobiAngerCorrectedDegree τ ε hτ hε hε1).1,
      lcCorrectedQ_upper τ ε hτ hε hε1, hpair⟩
  · exact ⟨efficientInversion, efficientInversion_certified⟩
  · exact scoreStability'
  · intro t k
    have hprec := computed_signal_explicit_segment_precision t k
    obtain ⟨hr, hn, ht, hε, hrem, -⟩ := hprec
    set n := computedSignalCutoff t k
    set u : ℚ := t / (computedSignalSegments t : ℚ)
    have hc := computed_signal_native_trig_coefficients u n
    have hu : (u:ℝ) = (t:ℝ) / (computedSignalSegments t:ℝ) := by simp [u]
    have htime : 2*|(u:ℝ)| ≤ (n:ℝ)+1 := by
      rw [← hu] at ht
      have hn' : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hrem1 : exponentialTaylorError (u:ℝ) n < 1 := by
      have hp : (1/2:ℝ)^n ≤ (1/2:ℝ)^2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by dsimp [n, computedSignalCutoff]; omega)
      dsimp only [n] at hp
      rw [← hu] at hrem
      norm_num at hp
      linarith
    have hcd : (realTarget (computedCosCoefficients u n)).degree
        ≤ ((2*n:ℕ):WithBot ℕ) := by
      rw [hc.1]
      apply Polynomial.degree_le_of_natDegree_le
      exact (Polynomial.natDegree_C_mul_le (1/4:ℝ) (cosineTaylorPolynomial (u:ℝ) n)).trans
        ((cosineTaylorPolynomial_natDegree_le (u:ℝ) n).trans (by omega))
    have hsd : (realTarget (computedSinCoefficients u n)).degree
        ≤ ((2*n+1:ℕ):WithBot ℕ) := by
      rw [hc.2.1]
      apply Polynomial.degree_le_of_natDegree_le
      exact (Polynomial.natDegree_C_mul_le (1/4:ℝ) (sineTaylorPolynomial (u:ℝ) n)).trans
        ((sineTaylorPolynomial_natDegree_le (u:ℝ) n).trans (by omega))
    have hcp : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*n)
        (realTarget (computedCosCoefficients u n)) := by
      rw [hc.1]
      simp [Qatlib.Concepts.QspSimulation.Achievability.HasRealParity, hamiltonianCosine,
        cosineTaylorPolynomial_comp_neg_X, pow_mul]
    have hsp : Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*n+1)
        (realTarget (computedSinCoefficients u n)) := by
      rw [hc.2.1]
      simp [Qatlib.Concepts.QspSimulation.Achievability.HasRealParity, hamiltonianSine,
        sineTaylorPolynomial_comp_neg_X, pow_add, pow_mul]
    have hboundc : ∀ x ∈ Set.Icc (-1:ℝ) 1,
        |(realTarget (computedCosCoefficients u n)).eval x| ≤ 1 := by
      rw [hc.1]
      intro x hx
      exact (scaledCosineTaylorPolynomial_abs_lt_half (u:ℝ) n htime hrem1 hx).le.trans
        (by norm_num)
    have hbounds : ∀ x ∈ Set.Icc (-1:ℝ) 1,
        |(realTarget (computedSinCoefficients u n)).eval x| ≤ 1 := by
      rw [hc.2.1]
      intro x hx
      exact (scaledSineTaylorPolynomial_abs_lt_half (u:ℝ) n htime hrem1 hx).le.trans
        (by norm_num)
    have htol : 0 < computedSignalTolerance t k := hε
    refine ⟨⟨htol, hcd, hcp, hboundc⟩, htol, hsd, hsp, hbounds⟩

/-- The single-X-gate flag program satisfies the gate-word, flag-index, and time-budget
conditions of `SimulationLegal`. -/
theorem identityFlagProgram_legal (m : ℕ) :
    SimulationLegal (identityFlagProgram m) := by
  show finiteWordLegal (m + 1) [FiniteGateCode.x m] = true ∧
    m < m + 1 ∧ [FiniteGateCode.x m].length ≤ 1
  refine ⟨?_, by omega, by simp⟩
  simp [finiteWordLegal, finiteCodeLegal]

/-- A cleanly embedded system state has zero amplitude on every register whose added flag is
true. -/
theorem systemInputState_zero_of_flag {m : ℕ} (ψ : QState (Reg m))
    (y : Reg (m + 1)) (hy : y ⟨m, Nat.lt_succ_self m⟩ = true) :
    systemInputState (Nat.le_succ m) ψ y = 0 := by
  unfold systemInputState
  rw [if_neg]
  intro hw
  have h := hw ⟨m, Nat.lt_succ_self m⟩ (Nat.le_refl m)
  rw [hy] at h
  simp at h

/-- Flipping the last flag of a state supported on false-flag registers gives zero amplitude on
false-flag outputs. -/
theorem wireGate_mulVec_zero_of_flag_false {m : ℕ}
    (ψ' : QState (Reg (m + 1))) (z : Reg (m + 1))
    (hz : z ⟨m, Nat.lt_succ_self m⟩ = false)
    (hψ' : ∀ y, y ⟨m, Nat.lt_succ_self m⟩ = true → ψ' y = 0) :
    (Matrix.mulVec (wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX) ψ') z = 0 := by
  show ∑ y, wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX z y * ψ' y = 0
  apply Finset.sum_eq_zero
  intro y _
  rw [wireGate_apply]
  by_cases hsupp : ∀ k : Fin (m + 1), k ≠ ⟨m, Nat.lt_succ_self m⟩ → z k = y k
  · rw [if_pos hsupp]
    by_cases hy : y ⟨m, Nat.lt_succ_self m⟩ = true
    · rw [hψ' y hy, mul_zero]
    · have hy' : y ⟨m, Nat.lt_succ_self m⟩ = false := by
        cases h : y ⟨m, Nat.lt_succ_self m⟩
        · rfl
        · exact absurd h hy
      rw [hz, hy']
      simp only [PauliX, permMatrix]
      norm_num
  · rw [if_neg hsupp, zero_mul]

/-- Embeds an `m`-qubit basis register into `m + 1` qubits by preserving its system bits and
setting the last flag to true. -/
private def flagEmbed {m : ℕ} (x : Reg m) : Reg (m + 1) :=
  fun i => if h : i.1 < m then x ⟨i.1, h⟩ else true

/-- Negates the last flag bit of an `m + 1`-qubit register and preserves every other bit. -/
private def flagFlip {m : ℕ} (z : Reg (m + 1)) : Reg (m + 1) :=
  fun i => if i.1 = m then Bool.not (z i) else z i

/-- Below the flag position, `flagEmbed` returns the corresponding original system bit. -/
private theorem flagEmbed_apply_lt {m : ℕ} (x : Reg m) {i : Fin (m + 1)} (hi : i.1 < m) :
    flagEmbed x i = x ⟨i.1, hi⟩ := by
  show (if h : i.1 < m then x ⟨i.1, h⟩ else true) = x ⟨i.1, hi⟩
  rw [dif_pos hi]

/-- The last flag bit of `flagEmbed x` is true. -/
private theorem flagEmbed_apply_flag {m : ℕ} (x : Reg m) :
    flagEmbed x ⟨m, Nat.lt_succ_self m⟩ = true := by
  show (if h : m < m then x ⟨m, h⟩ else true) = true
  rw [dif_neg (Nat.lt_irrefl m)]

/-- Restricting a flagged embedding to its system register recovers the original register. -/
private theorem systemRestrict_flagEmbed {m : ℕ} (x : Reg m) :
    systemRestrict (Nat.le_succ m) (flagEmbed x) = x := by
  funext i
  show flagEmbed x (Fin.castLE (Nat.le_succ m) i) = x i
  have hi : (Fin.castLE (Nat.le_succ m) i).1 < m := i.isLt
  rw [flagEmbed_apply_lt _ hi]
  rfl

/-- Every register with a true last flag is recovered by embedding its system restriction with
that flag set to true. -/
private theorem flagEmbed_of_eq {m : ℕ} (z : Reg (m + 1))
    (hz : z ⟨m, Nat.lt_succ_self m⟩ = true) :
    flagEmbed (systemRestrict (Nat.le_succ m) z) = z := by
  funext i
  show (if h : i.1 < m then (systemRestrict (Nat.le_succ m) z) ⟨i.1, h⟩ else true) = z i
  by_cases hi : i.1 < m
  · rw [dif_pos hi]
    show z (Fin.castLE (Nat.le_succ m) ⟨i.1, hi⟩) = z i
    rfl
  · have hval : i.1 = m := by omega
    rw [dif_neg hi]
    have hie : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.eq_of_val_eq hval
    rw [hie]
    exact hz.symm

/-- At the last flag position, `flagFlip` is Boolean negation. -/
private theorem flagFlip_apply_flag {m : ℕ} (z : Reg (m + 1)) :
    flagFlip z ⟨m, Nat.lt_succ_self m⟩ = Bool.not (z ⟨m, Nat.lt_succ_self m⟩) := by
  show (if m = m then Bool.not (z ⟨m, Nat.lt_succ_self m⟩) else z ⟨m, Nat.lt_succ_self m⟩) = _
  rw [if_pos rfl]

/-- The flag flip preserves each register bit away from the last flag position. -/
private theorem flagFlip_apply_of_ne {m : ℕ} (z : Reg (m + 1)) {i : Fin (m + 1)}
    (hi : i ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))) :
    flagFlip z i = z i := by
  have hi' : i.1 ≠ m := fun h => hi (Fin.eq_of_val_eq h)
  show (if i.1 = m then Bool.not (z i) else z i) = z i
  rw [if_neg hi']

/-- Flipping the last flag leaves the system restriction unchanged. -/
private theorem systemRestrict_flagFlip {m : ℕ} (z : Reg (m + 1)) :
    systemRestrict (Nat.le_succ m) (flagFlip z) = systemRestrict (Nat.le_succ m) z := by
  funext i
  show flagFlip z (Fin.castLE (Nat.le_succ m) i) = z (Fin.castLE (Nat.le_succ m) i)
  have hi : (Fin.castLE (Nat.le_succ m) i) ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := by
    intro he
    have hval := congrArg Fin.val he
    have := i.isLt
    simp [Fin.castLE] at hval this
    omega
  exact flagFlip_apply_of_ne z hi

/-- Execution of the identity flag program equals matrix-vector multiplication by Pauli X on the
last wire. -/
private theorem identityFlagProgram_runState_eq (m : ℕ) (ψ : QState (Reg (m + 1))) :
    simulationRunState (identityFlagProgram m) ψ
      = (wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX).mulVec ψ := by
  show Run (1 : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ)
      (finiteCodeCircuit (m + 1) [FiniteGateCode.x m]) ψ = _
  have hmat : finiteCodeMatrix (m + 1) (FiniteGateCode.x m)
      = wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX := by
    show (if h : m < m + 1 then wireGate (m + 1) ⟨m, h⟩ PauliX else 1) = _
    rw [dif_pos (Nat.lt_succ_self m)]
  show Run (1 : Matrix (Reg (m + 1)) (Reg (m + 1)) ℂ)
      [Step.gate (finiteCodeMatrix (m + 1) (FiniteGateCode.x m))] ψ = _
  rw [hmat]
  rfl

/-- The amplitude after Pauli X on the last wire equals the input amplitude at the register with
that flag flipped. -/
private theorem wireGate_pauliX_mulVec_apply {m : ℕ} (ψ' : QState (Reg (m + 1)))
    (z : Reg (m + 1)) :
    (Matrix.mulVec (wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX) ψ') z
      = ψ' (flagFlip z) := by
  have hkey : ∀ y : Reg (m + 1),
      wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX z y * ψ' y
        = if y = flagFlip z then ψ' (flagFlip z) else 0 := by
    intro y
    by_cases hfl : y = flagFlip z
    · subst hfl
      have hsupp : ∀ k : Fin (m + 1), k ≠ (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) →
          z k = flagFlip z k := by
        intro k hk
        exact (flagFlip_apply_of_ne z hk).symm
      rw [wireGate_apply, if_pos hsupp, if_pos rfl]
      rw [flagFlip_apply_flag]
      have hp : PauliX (z ⟨m, Nat.lt_succ_self m⟩) (Bool.not (z ⟨m, Nat.lt_succ_self m⟩)) = 1 := by
        cases hzz : z ⟨m, Nat.lt_succ_self m⟩ <;> simp [PauliX, permMatrix, Matrix.of_apply]
      rw [hp, one_mul]
    · have hz : wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX z y = 0 := by
        rw [wireGate_apply]
        by_cases hsupp : ∀ k : Fin (m + 1), k ≠ ⟨m, Nat.lt_succ_self m⟩ → z k = y k
        · rw [if_pos hsupp]
          show (if z ⟨m, Nat.lt_succ_self m⟩ = Bool.not (y ⟨m, Nat.lt_succ_self m⟩)
            then (1 : ℂ) else 0) = 0
          by_cases hw : z ⟨m, Nat.lt_succ_self m⟩ = Bool.not (y ⟨m, Nat.lt_succ_self m⟩)
          · exfalso
            apply hfl
            funext i
            by_cases hi : i.1 = m
            · have hie : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.eq_of_val_eq hi
              rw [hie, flagFlip_apply_flag, hw]
              cases hy : y ⟨m, Nat.lt_succ_self m⟩ <;> rfl
            · rw [flagFlip_apply_of_ne z (fun he => hi (congrArg Fin.val he))]
              exact (hsupp i (fun he => hi (congrArg Fin.val he))).symm
          · rw [if_neg hw]
        · rw [if_neg hsupp]
      rw [hz, if_neg hfl, zero_mul]
  show ∑ y, wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX z y * ψ' y = _
  have hrew : (∑ y : Reg (m + 1), wireGate (m + 1) ⟨m, Nat.lt_succ_self m⟩ PauliX z y * ψ' y)
      = ∑ y : Reg (m + 1), (if y = flagFlip z then ψ' (flagFlip z) else 0) :=
    Finset.sum_congr rfl fun y _ => hkey y
  have hsum : (∑ y : Reg (m + 1), (if y = flagFlip z then ψ' (flagFlip z) else 0))
      = ψ' (flagFlip z) := by
    have h1 : (∑ y : Reg (m + 1), (if y = flagFlip z then ψ' (flagFlip z) else 0))
        = (if flagFlip z = flagFlip z then ψ' (flagFlip z) else 0) :=
      Finset.sum_eq_single_of_mem (flagFlip z) (Finset.mem_univ _) (fun y _ hy => if_neg hy)
    rw [h1, if_pos rfl]
  rw [hrew, hsum]

/-- On a true-flag output register, the identity flag program applied to a clean input has the
original amplitude at the system restriction. -/
private theorem identityFlagProgram_runState_apply (m : ℕ) (ψ : QState (Reg m))
    (z : Reg (m + 1)) (hz : z ⟨m, Nat.lt_succ_self m⟩ = true) :
    simulationRunState (identityFlagProgram m) (systemInputState (Nat.le_succ m) ψ) z
      = ψ (systemRestrict (Nat.le_succ m) z) := by
  rw [identityFlagProgram_runState_eq, wireGate_pauliX_mulVec_apply]
  have hwork : workZero m (flagFlip z) := by
    intro i hi
    have hval : i.1 = m := by omega
    have hie : i = (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) := Fin.eq_of_val_eq hval
    have hi2 : flagFlip z i = Bool.not (z i) := by
      show (if i.1 = m then Bool.not (z i) else z i) = _
      rw [if_pos hval]
    rw [hi2, hie, hz]
    simp
  show (if workZero m (flagFlip z) then ψ (systemRestrict (Nat.le_succ m) (flagFlip z)) else 0)
      = ψ (systemRestrict (Nat.le_succ m) z)
  rw [if_pos hwork, systemRestrict_flagFlip]

/-- The success event of the identity flag program consists exactly of registers with a true
last flag. -/
private theorem identityFlagProgram_successEvent (m : ℕ) :
    simulationSuccessEvent (identityFlagProgram m)
      = Finset.univ.filter (fun z : Reg (m + 1) => z ⟨m, Nat.lt_succ_self m⟩ = true) := by
  show (if h : m < m + 1 then Finset.univ.filter (fun z : Reg (m + 1) => z ⟨m, h⟩ = true) else ∅)
      = Finset.univ.filter (fun z : Reg (m + 1) => z ⟨m, Nat.lt_succ_self m⟩ = true)
  rw [dif_pos (Nat.lt_succ_self m)]

/-- Membership in the identity flag program's success event is equivalent to the last flag being
true. -/
private theorem mem_identityFlagProgram_successEvent {m : ℕ} (z : Reg (m + 1)) :
    z ∈ simulationSuccessEvent (identityFlagProgram m) ↔ z ⟨m, Nat.lt_succ_self m⟩ = true := by
  constructor
  · intro h
    rw [identityFlagProgram_successEvent] at h
    exact (Finset.mem_filter.mp h).2
  · intro h
    rw [identityFlagProgram_successEvent]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩

/-- The identity flag program has zero failure probability on every cleanly embedded system
input. -/
private theorem identityFlagProgram_failureProb_zero (m : ℕ) (ψ : QState (Reg m)) :
    simulationFailureProb (identityFlagProgram m) (systemInputState (Nat.le_succ m) ψ) = 0 := by
  show MeasureProb (simulationRunState (identityFlagProgram m) (systemInputState (Nat.le_succ m) ψ))
      (Finset.univ \ simulationSuccessEvent (identityFlagProgram m)) = 0
  unfold MeasureProb BornProb
  apply Finset.sum_eq_zero
  intro z hz
  have hz' : z ∉ simulationSuccessEvent (identityFlagProgram m) :=
    (Finset.mem_sdiff.mp hz).2
  have hflag : z ⟨m, Nat.lt_succ_self m⟩ = false := by
    have hne : z ⟨m, Nat.lt_succ_self m⟩ ≠ true :=
      fun h => hz' ((mem_identityFlagProgram_successEvent z).mpr h)
    cases h : z ⟨m, Nat.lt_succ_self m⟩ with
    | false => rfl
    | true => exact absurd h hne
  have hrun0 : simulationRunState (identityFlagProgram m)
      (systemInputState (Nat.le_succ m) ψ) z = 0 := by
    rw [identityFlagProgram_runState_eq]
    exact wireGate_mulVec_zero_of_flag_false (systemInputState (Nat.le_succ m) ψ) z hflag
      (fun y hy => systemInputState_zero_of_flag ψ y hy)
  rw [hrun0]
  simp

/-- The residual-work-zero condition holds for every register of the identity flag program,
since its sole extra wire is the success flag. -/
private theorem residualZero_identityFlagProgram {m : ℕ} (z : Reg (m + 1)) :
    residualZero m (identityFlagProgram m).successWire z := by
  show ∀ i : Fin (m + 1), m ≤ i.1 → i.1 ≠ (identityFlagProgram m).successWire → z i = false
  intro i hi hne
  have : i.1 = m := by omega
  exact absurd this hne

/-- Extracting the successful system vector after the identity flag program recovers the input
vector exactly. -/
private theorem identityFlagProgram_successSystemVector (m : ℕ) (ψ : QState (Reg m)) :
    successSystemVector (identityFlagProgram m) m (Nat.le_succ m) ψ = ψ := by
  funext x
  have hif : ∀ z : Reg (m + 1), z ∈ simulationSuccessEvent (identityFlagProgram m) →
      (if residualZero m (identityFlagProgram m).successWire z ∧
            systemRestrict (Nat.le_succ m) z = x
          then simulationRunState (identityFlagProgram m) (systemInputState (Nat.le_succ m) ψ) z
          else 0)
        = if systemRestrict (Nat.le_succ m) z = x then ψ x else 0 := by
    intro z hz
    have hztrue : z ⟨m, Nat.lt_succ_self m⟩ = true :=
      (mem_identityFlagProgram_successEvent z).mp hz
    by_cases heq : systemRestrict (Nat.le_succ m) z = x
    · rw [if_pos ⟨residualZero_identityFlagProgram z, heq⟩, if_pos heq]
      rw [identityFlagProgram_runState_apply m ψ z hztrue, heq]
    · rw [if_neg (fun h => heq h.2), if_neg heq]
  have h1 : (∑ z ∈ simulationSuccessEvent (identityFlagProgram m),
      (if residualZero m (identityFlagProgram m).successWire z ∧
            systemRestrict (Nat.le_succ m) z = x
          then simulationRunState (identityFlagProgram m) (systemInputState (Nat.le_succ m) ψ) z
          else 0))
      = ∑ z ∈ simulationSuccessEvent (identityFlagProgram m),
        (if systemRestrict (Nat.le_succ m) z = x then ψ x else 0) :=
    Finset.sum_congr rfl fun z hz => hif z hz
  have hmem : flagEmbed x ∈ simulationSuccessEvent (identityFlagProgram m) :=
    (mem_identityFlagProgram_successEvent _).mpr (flagEmbed_apply_flag x)
  have hrest : ∀ z ∈ simulationSuccessEvent (identityFlagProgram m),
      z ≠ flagEmbed x → (if systemRestrict (Nat.le_succ m) z = x then ψ x else 0) = 0 := by
    intro z hz hne
    apply if_neg
    intro heq
    apply hne
    rw [← heq]
    exact (flagEmbed_of_eq z ((mem_identityFlagProgram_successEvent z).mp hz)).symm
  have h2 : (∑ z ∈ simulationSuccessEvent (identityFlagProgram m),
      (if systemRestrict (Nat.le_succ m) z = x then ψ x else 0)) = ψ x := by
    have h2a : (∑ z ∈ simulationSuccessEvent (identityFlagProgram m),
        (if systemRestrict (Nat.le_succ m) z = x then ψ x else 0))
        = (if systemRestrict (Nat.le_succ m) (flagEmbed x) = x then ψ x else 0) :=
      Finset.sum_eq_single_of_mem _ hmem hrest
    rw [h2a, if_pos (systemRestrict_flagEmbed x)]
  show (∑ z ∈ simulationSuccessEvent (identityFlagProgram m),
      if residualZero m (identityFlagProgram m).successWire z ∧
          systemRestrict (Nat.le_succ m) z = x
        then simulationRunState (identityFlagProgram m) (systemInputState (Nat.le_succ m) ψ) z
        else 0) = ψ x
  exact h1.trans h2

/-- For a normalized input, the conditional system state of the identity flag program equals the
original state. -/
private theorem identityFlagProgram_conditionalSystemState (m : ℕ) (ψ : QState (Reg m))
    (hψ : Normalized ψ) :
    conditionalSystemState (identityFlagProgram m) m (Nat.le_succ m) ψ = ψ := by
  have hvec : successSystemVector (identityFlagProgram m) m (Nat.le_succ m) ψ = ψ :=
    identityFlagProgram_successSystemVector m ψ
  have hnorm : ‖toEuclidean_fromVec (successSystemVector (identityFlagProgram m) m
      (Nat.le_succ m) ψ)‖ = 1 := by
    rw [hvec]
    exact (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  show (‖toEuclidean_fromVec (successSystemVector (identityFlagProgram m) m (Nat.le_succ m) ψ)‖)⁻¹ •
      successSystemVector (identityFlagProgram m) m (Nat.le_succ m) ψ = ψ
  rw [hnorm, hvec]
  rw [inv_one, one_smul]

/-- For every normalized system state, the identity flag program is legal, has zero failure
probability, and preserves the conditional system state. -/
theorem identityFlagProgram_semantics :
    ∀ (m : ℕ) (ψ : QState (Reg m)), Normalized ψ →
      SimulationLegal (identityFlagProgram m) ∧
      simulationFailureProb (identityFlagProgram m)
        (systemInputState (Nat.le_succ m) ψ) = 0 ∧
      conditionalSystemState (identityFlagProgram m) m (Nat.le_succ m) ψ = ψ := by
  intro m ψ hψ
  exact ⟨identityFlagProgram_legal m,
    identityFlagProgram_failureProb_zero m ψ,
    identityFlagProgram_conditionalSystemState m ψ hψ⟩

end Qatlib.Concepts.QspSimulation.Achievability
