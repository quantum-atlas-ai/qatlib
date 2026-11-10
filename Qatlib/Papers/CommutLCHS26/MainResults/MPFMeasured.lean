/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MeasuredRounds
import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAAccuracy
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFMeasured

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator
open MPFLongTime MPFMomentSeries
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

def successProbability (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ)
    (m : ℕ) (T ε : ℝ) (ψ : QState I) : ℝ :=
  MeasuredRounds.mass (MPFOAALCU.amplified xs q a (T / segments xs a m T ε))
    (scaleEightFrame (MPFOAALCU.frame a)) (segments xs a m T ε) ψ

def failureProbability (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ)
    (m : ℕ) (T ε : ℝ) (ψ : QState I) : ℝ :=
  ∑ j ∈ Finset.range (segments xs a m T ε),
    MeasuredRounds.firstFailure (MPFOAALCU.amplified xs q a (T / segments xs a m T ε))
      (scaleEightFrame (MPFOAALCU.frame a)) j ψ

def conditionalOutput (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ)
    (m : ℕ) (T ε : ℝ) (ψ : QState I) : Option (QState I) :=
  MeasuredRounds.output (MPFOAALCU.amplified xs q a (T / segments xs a m T ε))
    (scaleEightFrame (MPFOAALCU.frame a)) (segments xs a m T ε) ψ

theorem guarantees (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ψ : QState I) (hψ : Normalized ψ) :
    (1 - ε / 12) ^ 2 ≤ successProbability xs q a m T ε ψ ∧
      failureProbability xs q a m T ε ψ ≤ ε / 6 ∧
      successProbability xs q a m T ε ψ + failureProbability xs q a m T ε ψ = 1 ∧
      0 < successProbability xs q a m T ε ψ ∧
      ∃ φ : QState I, conditionalOutput xs q a m T ε ψ = some φ ∧
        IsNormalizedApplication (NormedSpace.exp (T • ((-Complex.I) • xs.sum))) ψ φ (ε / 6) := by
  let r := segments xs a m T ε
  let U := MPFOAALCU.amplified xs q a (T / r)
  let R := scaleEightFrame (MPFOAALCU.frame (I := I) a)
  let V := NormedSpace.exp (T • ((-Complex.I) • xs.sum))
  have h := MPFOAAAccuracy.slice_encoding xs hxs q hq a ha m hm hmom T ε hε hε1
  have hV : V ∈ unitaryGroup I ℂ := by
    have hv := general_trotter_exp_unitary _ 1 (BCHPerturbation.target_skew xs hxs T)
    simpa only [one_smul] using! hv
  have he : ‖(compress R U R) ^ r - V‖ ≤ ε / 12 :=
    MPFOAAAccuracy.block_power_error xs hxs q hq a ha m hm hmom T ε hε hε1
  have hg : ε / 12 < 1 := by linarith
  have hl := MeasuredRounds.mass_lower U R h.left_isometry r V hV (ε / 12) hg.le he ψ hψ
  have hf :=
      MeasuredRounds.failure_sum_le U h.unitary R h.left_isometry r V hV (ε / 12) hg.le he ψ hψ
  have hc := MeasuredRounds.history_conservation U h.unitary R h.left_isometry r ψ
  rw [measureProb_univ hψ] at hc
  have ho := MeasuredRounds.output_of_error U R h.left_isometry r V hV (ε / 12) hg he ψ hψ
  have heps : 2 * (ε / 12) = ε / 6 := by ring
  exact ⟨hl, by simpa only [heps] using! hf, hc, ho.1, by simpa only [heps] using! ho.2⟩

omit [Fintype K] [DecidableEq K] in

theorem chebyshev_guarantees (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ψ : QState I) (hψ : Normalized ψ) :
    (1 - ε / 12) ^ 2 ≤ successProbability xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε ψ ∧
      failureProbability xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε ψ ≤ ε / 6 ∧
      successProbability xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε ψ +
        failureProbability xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε ψ = 1 ∧
      0 < successProbability xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε ψ ∧
      ∃ φ : QState I, conditionalOutput xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m) m T ε ψ = some φ ∧
        IsNormalizedApplication (NormedSpace.exp (T • ((-Complex.I) • xs.sum))) ψ φ (ε / 6) := by
  apply guarantees xs hxs _ (ChebyshevNodes.node_pos m hm) _ _ m hm _ T ε hε hε1 ψ hψ
  · simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm
  · intro k hk hkm
    exact (ChebyshevNodes.weight_moments m hm k hkm).trans (zero_pow (by omega))

omit [Fintype K] [DecidableEq K] in

theorem chebyshev_selective_output (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ψ : QState I) (hψ : Normalized ψ) :
    ∃ φ : QState I,
      MeasuredRounds.selectiveRun
        (MPFOAALCU.amplified xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m)
          (T / segments xs (ChebyshevNodes.weight m) m T ε))
        (scaleEightFrame (MPFOAALCU.frame (ChebyshevNodes.weight m)))
        (segments xs (ChebyshevNodes.weight m) m T ε) ψ =
          some (scaleEightFrame (MPFOAALCU.frame (ChebyshevNodes.weight m)) *ᵥ φ) ∧
      IsNormalizedApplication (NormedSpace.exp (T • ((-Complex.I) • xs.sum))) ψ φ (ε / 6) := by
  have h := chebyshev_guarantees xs hxs m hm T ε hε hε1 ψ hψ
  obtain ⟨φ, ho, he⟩ := h.2.2.2.2
  have hR := (MPFOAALCU.padded_encoding xs hxs (ChebyshevNodes.node m) (ChebyshevNodes.weight m)
    (by simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm)
    (T / segments xs (ChebyshevNodes.weight m) m T ε)).left_isometry
  refine ⟨φ, ?_, he⟩
  rw [MeasuredRounds.selectiveRun_output _ _ hR, show MeasuredRounds.output _ _ _ _ = some φ from ho,
    Option.map_some]

end Qatlib.Papers.CommutLCHS26.MainResults.MPFMeasured
