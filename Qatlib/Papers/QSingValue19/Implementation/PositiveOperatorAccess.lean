/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSingValue19.Implementation.PositiveOperatorAccessDefs

/-!
# Positive operator access and finite precision preparation

This module proves the spectral and circuit guarantees for positive operator access used in the
implementation setting of [GilyenSuLowWiebe2019]. The theorem
`effect_access_bit_control_and_cost` bounds dyadic eigenvalue truncation error and storage; the
module also verifies unitarity, approximation error, exact ideal action, and resources for
rational weight state preparation.

## Main statements

* `effectAccess_word_resources`: Certifies legality, zero queries, and the explicit gate bound.
* `effect_access_bit_control_and_cost`: Bounds spectral truncation error and mantissa storage.
* `prepareFiniteDigit_error`: Bounds the finite digit preparation error.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Papers.QSingValue19.Implementation

open Matrix Qatlib SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The canonical positive operator access data give a unitary diagonalization of E. -/
theorem effectAccess_spectral (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (hE : E.PosSemidef) :
    E = (effectAccess n E hE).unitary
      * Matrix.diagonal (fun j => ((effectAccess n E hE).eigenvalues j : ℂ))
      * (effectAccess n E hE).unitaryᴴ :=
  (effectAccess n E hE).spectral

/-- Every eigenvalue in the canonical positive operator access data is nonnegative. -/
theorem effectAccess_eigenvalues_nonneg (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (hE : E.PosSemidef) (j : Reg n) :
    0 ≤ (effectAccess n E hE).eigenvalues j :=
  (effectAccess n E hE).eigenvalues_nonneg j

/-- The canonical access word is legal, uses zero queries, has gate count equal to its length,
and has length at most 128(n + 1)²4^n. -/
theorem effectAccess_word_resources (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (hE : E.PosSemidef) :
    reflectionLegal (effectAccess n E hE).word ∧
    QueryCount (reflectionCompile (effectAccess n E hE).word) = 0 ∧
    GateCount (reflectionCompile (effectAccess n E hE).word)
      = (effectAccess n E hE).word.length ∧
    (effectAccess n E hE).word.length ≤ 128*(n+1)^2*4^n :=
  ⟨(effectAccess n E hE).word_legal, (effectAccess n E hE).word_queries,
    (effectAccess n E hE).word_gates, (effectAccess n E hE).word_length⟩

/-- The compiled canonical access word acts as the spectral unitary on states embedded by
`knownFrameEmbed`. -/
theorem effectAccess_word_action (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (hE : E.PosSemidef) (ψ : QState (Reg n)) :
    Run 1 (reflectionCompile (effectAccess n E hE).word) (knownFrameEmbed n ψ)
      = knownFrameEmbed n ((effectAccess n E hE).unitary *ᵥ ψ) :=
  (effectAccess n E hE).word_action ψ

/-- For nonnegative x, reconstructing x from its b digit dyadic mantissa has absolute error at
most 2^(−b). -/
theorem spectrumMantissa_error (b : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    |x - (spectrumMantissa b x : ℝ) / (2 : ℝ)^b| ≤ ((2 : ℝ)⁻¹) ^ b := by
  have h1 : (spectrumMantissa b x : ℝ) ≤ x * (2 : ℝ)^b := by
    have h : (Nat.floor (x * (2 : ℝ)^b) : ℝ) ≤ x * (2 : ℝ)^b :=
      Nat.floor_le (a := x * (2 : ℝ)^b) (mul_nonneg hx (by positivity))
    simpa [spectrumMantissa] using! h
  have h2 : x * (2 : ℝ)^b < (spectrumMantissa b x : ℝ) + 1 := by
    have h : x * (2 : ℝ)^b < (Nat.floor (x * (2 : ℝ)^b) : ℝ) + 1 :=
      Nat.lt_floor_add_one (x * (2 : ℝ)^b)
    simpa [spectrumMantissa] using! h
  have hpow : (0 : ℝ) < (2 : ℝ)^b := by positivity
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h3 : (spectrumMantissa b x : ℝ) / (2 : ℝ)^b ≤ x := by
      rw [div_le_iff₀ hpow]
      nlinarith [h1]
    have hc : 0 ≤ ((2 : ℝ)⁻¹) ^ b := by positivity
    linarith
  · have h2' : x < ((spectrumMantissa b x : ℝ) + 1) / (2 : ℝ)^b := by
      rw [lt_div_iff₀ hpow]
      exact h2
    have hid : ((spectrumMantissa b x : ℝ) + 1) / (2 : ℝ)^b
        = (spectrumMantissa b x : ℝ) / (2 : ℝ)^b + ((2 : ℝ)⁻¹) ^ b := by
      rw [add_div, one_div, inv_pow]
    linarith

/-- For positive operator access data with eigenvalues at most one, constructs the dyadically
truncated operator with norm error at most 2^(−b), mantissas at most 2^b, and the stated
spectrum bit count. -/
theorem effect_access_bit_control_and_cost (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (A : EffectAccess n E) (b : ℕ) (hlam1 : ∀ j, A.eigenvalues j ≤ 1) :
    ∃ E' : Matrix (Reg n) (Reg n) ℂ,
      E' = A.unitary
        * Matrix.diagonal (fun j =>
            (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
        * A.unitaryᴴ ∧
      ‖E - E'‖ ≤ ((2 : ℝ)⁻¹) ^ b ∧
      (∀ j, spectrumMantissa b (A.eigenvalues j) ≤ 2^b) ∧
      effectSpectrumBits n b = (b+1) * Fintype.card (Reg n) := by
  have hV : A.unitary ∈ Matrix.unitaryGroup (Reg n) ℂ := A.unitary_mem
  have hlamnonneg : ∀ j, 0 ≤ A.eigenvalues j := A.eigenvalues_nonneg
  have hspec : E = A.unitary * Matrix.diagonal (fun j => (A.eigenvalues j : ℂ)) * A.unitaryᴴ :=
    A.spectral
  refine ⟨A.unitary
      * Matrix.diagonal (fun j =>
          (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
      * A.unitaryᴴ, rfl, ?_, ?_, rfl⟩
  · have hdiag_eq :
        Matrix.diagonal (fun j => (A.eigenvalues j : ℂ))
            - Matrix.diagonal (fun j =>
                (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
          = Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ)) := by
      rw [Matrix.diagonal_sub]
      congr 1
      funext j
      push_cast
      ring
    have hsub : A.unitary * Matrix.diagonal (fun j => (A.eigenvalues j : ℂ)) * A.unitaryᴴ
          - A.unitary * Matrix.diagonal (fun j =>
              (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
            * A.unitaryᴴ
        = A.unitary * Matrix.diagonal (fun j =>
            ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
              : ℝ) : ℂ)) * A.unitaryᴴ := by
      calc
        (A.unitary * Matrix.diagonal (fun j => (A.eigenvalues j : ℂ))) * A.unitaryᴴ
            - (A.unitary * Matrix.diagonal (fun j =>
                (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ)))
              * A.unitaryᴴ
            = A.unitary * (Matrix.diagonal (fun j => (A.eigenvalues j : ℂ))
                - Matrix.diagonal (fun j =>
                    (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ)))
                * A.unitaryᴴ := by noncomm_ring
        _ = A.unitary * Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ)) * A.unitaryᴴ := by rw [hdiag_eq]
    have hdiff : E - (A.unitary
          * Matrix.diagonal (fun j =>
              (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
          * A.unitaryᴴ)
        = A.unitary * Matrix.diagonal (fun j =>
            ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
              : ℝ) : ℂ)) * A.unitaryᴴ := by
      calc
        E - (A.unitary * Matrix.diagonal (fun j =>
              (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
            * A.unitaryᴴ)
            = (A.unitary * Matrix.diagonal (fun j => (A.eigenvalues j : ℂ)) * A.unitaryᴴ)
              - (A.unitary * Matrix.diagonal (fun j =>
                  (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
                * A.unitaryᴴ) := by
                  exact congrArg (fun Z : Matrix (Reg n) (Reg n) ℂ =>
                    Z - (A.unitary * Matrix.diagonal (fun j =>
                      (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
                      * A.unitaryᴴ)) hspec
        _ = A.unitary * Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ)) * A.unitaryᴴ := hsub
    have hdiag : ‖Matrix.diagonal (fun j =>
          ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
            : ℝ) : ℂ))‖ ≤ ((2 : ℝ)⁻¹) ^ b := by
      rw [Matrix.l2_opNorm_diagonal]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr ?_
      intro j
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact spectrumMantissa_error b (A.eigenvalues j) (hlamnonneg j)
    have hVle : ‖A.unitary‖ ≤ 1 := l2_norm_unitary_le_one hV
    have hVH : ‖A.unitaryᴴ‖ = ‖A.unitary‖ := Matrix.l2_opNorm_conjTranspose A.unitary
    calc
      ‖E - (A.unitary
          * Matrix.diagonal (fun j =>
              (((spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b : ℝ) : ℂ))
          * A.unitaryᴴ)‖
          ≤ ‖A.unitary * Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ)) * A.unitaryᴴ‖ := by
            rw [hdiff]
      _ ≤ ‖A.unitary * Matrix.diagonal (fun j =>
            ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
              : ℝ) : ℂ))‖
            * ‖A.unitaryᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖A.unitary‖ * ‖Matrix.diagonal (fun j =>
            ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
              : ℝ) : ℂ))‖)
            * ‖A.unitaryᴴ‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ((2 : ℝ)⁻¹) ^ b) * 1 := by
        have hA : ‖A.unitary‖ * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ ≤ 1 * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ :=
          mul_le_mul_of_nonneg_right hVle (norm_nonneg _)
        have h1 : ‖A.unitary‖ * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ * ‖A.unitaryᴴ‖
            ≤ 1 * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ * ‖A.unitaryᴴ‖ :=
          mul_le_mul_of_nonneg_right hA (norm_nonneg _)
        have h2 : 1 * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ * ‖A.unitaryᴴ‖
            ≤ 1 * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ * 1 := by
          rw [hVH]
          exact mul_le_mul_of_nonneg_left hVle
            (mul_nonneg (by norm_num) (norm_nonneg _))
        have h3 : 1 * ‖Matrix.diagonal (fun j =>
              ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                : ℝ) : ℂ))‖ * 1 ≤ 1 * ((2 : ℝ)⁻¹) ^ b * 1 := by
          have hc : 1 * ‖Matrix.diagonal (fun j =>
                ((A.eigenvalues j - (spectrumMantissa b (A.eigenvalues j) : ℝ) / (2 : ℝ)^b
                  : ℝ) : ℂ))‖ ≤ 1 * ((2 : ℝ)⁻¹) ^ b :=
            mul_le_mul_of_nonneg_left hdiag (by norm_num)
          nlinarith [hc]
        exact h1.trans (h2.trans h3)
      _ = ((2 : ℝ)⁻¹) ^ b := by ring
  · intro j
    have hle : A.eigenvalues j ≤ 1 := hlam1 j
    have hpow : (0 : ℝ) < (2 : ℝ)^b := by positivity
    have h2 : A.eigenvalues j * (2 : ℝ)^b ≤ (1 : ℝ) * (2 : ℝ)^b := by
      have := mul_le_mul_of_nonneg_right hle (le_of_lt hpow)
      simpa using! this
    have hbound : (spectrumMantissa b (A.eigenvalues j) : ℝ) ≤ (2 : ℝ)^b := by
      calc
        (spectrumMantissa b (A.eigenvalues j) : ℝ)
            = (Nat.floor (A.eigenvalues j * (2 : ℝ)^b) : ℝ) := rfl
        _ ≤ A.eigenvalues j * (2 : ℝ)^b := Nat.floor_le
            (a := A.eigenvalues j * (2 : ℝ)^b)
            (mul_nonneg (hlamnonneg j) (by positivity))
        _ ≤ (1 : ℝ) * (2 : ℝ)^b := h2
        _ = (2 : ℝ)^b := by ring
    exact_mod_cast hbound

/-- For the canonical positive operator access data with eigenvalues at most one, gives the
dyadic spectral approximation, norm error at most 2^(−b), mantissa bounds, and spectrum bit
count. -/
theorem effectAccess_bit_control_and_cost (n : ℕ) (E : Matrix (Reg n) (Reg n) ℂ)
    (hE : E.PosSemidef) (b : ℕ)
    (hlam1 : ∀ j, (effectAccess n E hE).eigenvalues j ≤ 1) :
    ∃ E' : Matrix (Reg n) (Reg n) ℂ,
      E' = (effectAccess n E hE).unitary
        * Matrix.diagonal (fun j =>
            (((spectrumMantissa b ((effectAccess n E hE).eigenvalues j) : ℝ)
              / (2 : ℝ)^b : ℝ) : ℂ))
        * (effectAccess n E hE).unitaryᴴ ∧
      ‖E - E'‖ ≤ ((2 : ℝ)⁻¹) ^ b ∧
      (∀ j, spectrumMantissa b ((effectAccess n E hE).eigenvalues j) ≤ 2^b) ∧
      effectSpectrumBits n b = (b+1) * Fintype.card (Reg n) :=
  effect_access_bit_control_and_cost n E (effectAccess n E hE) b hlam1

/-- Nonnegative rational weights produce a well formed adjoint preparation circuit and a unitary
finite digit preparation matrix. -/
theorem prepareFiniteDigit_wellFormed_unitary {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ)
    (hw : ∀ a, 0 ≤ w a) :
    WellFormedAdjointCircuit (rationalWeightWord w k) ∧
    prepareFiniteDigit w k ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ := by
  obtain ⟨hWF, hU, _⟩ := rational_weight_numerical_word_unitary_and_error n k w hw
  refine ⟨hWF, ?_⟩
  simpa [prepareFiniteDigit] using! hU

/-- For nonnegative rational weights, the finite digit preparation matrix differs from the ideal
matrix by operator norm at most 32n/2^k. -/
theorem prepareFiniteDigit_error {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ)
    (hw : ∀ a, 0 ≤ w a) :
    ‖prepareFiniteDigit w k - prepareIdeal w‖ ≤ 32*(n : ℝ)/2^k := by
  obtain ⟨_, _, hErr⟩ := rational_weight_numerical_word_unitary_and_error n k w hw
  simpa [prepareFiniteDigit, prepareIdeal] using! hErr

/-- For nonnegative rational weights of positive total mass, the ideal unitary maps the
distinguished basis state to the normalized target state. -/
theorem prepareIdeal_exact {n : ℕ} (w : Option (Fin n) → ℚ) (hw : ∀ a, 0 ≤ w a)
    (hZ : 0 < rationalWeightMass w) :
    prepareIdeal w *ᵥ Ket none = prepareTarget w ∧
    Normalized (prepareTarget w) ∧
    prepareIdeal w ∈ Matrix.unitaryGroup (Option (Fin n)) ℂ := by
  obtain ⟨hU, hA, hN⟩ := rational_weight_ideal_preparation_exact n w hw hZ
  refine ⟨?_, hN, hU⟩
  simpa [prepareIdeal, prepareTarget] using! hA

/-- The rational weight preparation word uses zero adjoint model queries and exactly n gates. -/
theorem prepareFiniteDigit_resources {n : ℕ} (w : Option (Fin n) → ℚ) (k : ℕ) :
    adjointQueryCount (rationalWeightWord w k) = 0 ∧
    adjointGateCount (rationalWeightWord w k) = n := by
  have h := weight_fixed_word_counts (rationalWeightGate w k)
  simpa [rationalWeightWord] using! h

end Qatlib.Papers.QSingValue19.Implementation
