/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFOAARobust
import Qatlib.Papers.CommutLCHS26.MainResults.MPFLongTime

/-!
# Accuracy of amplified multi-product blocks

This module turns raw slice error estimates into scale-one block encodings for the amplified
multi-product construction of [AftabAnTrivisa2026]. With the chosen segment count and 0 < ε ≤ 1,
compressed block powers approximate the full-time target within ε/12, and each measured slice
has failure probability at most ε/(6r).

## Main statements

* `slice_encoding`: gives the scale-one encoding for a single slice.
* `block_power_error`: bounds the full-time compressed block error.
* `slice_failure`: bounds the per-slice failure probability.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAAccuracy

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator
open MPFRootProfile MPFRootBound MPFMomentSeries MPFLongTime
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Foundations.PureStateMath

variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

omit [DecidableEq K] in

/-- For the chosen segment count r, the raw multi-product slice error is at most ε/(12πr) under
the stated Hermitian and cancellation hypotheses. -/
theorem raw_slice_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (T ε : ℝ) (hε : 0 < ε) :
    ‖actualMPF xs q a (T / segments xs a m T ε) -
      NormedSpace.exp ((T / segments xs a m T ε) • ((-Complex.I) • xs.sum))‖ ≤
      ε / (12 * Real.pi * (segments xs a m T ε : ℝ)) := by
  let r := segments xs a m T ε
  have hr : 0 < (r : ℝ) := by exact_mod_cast segments_pos xs a m T ε
  have he := actualMPF_root_error xs hxs q hq a ha m hm hmom (T / r)
    (slice_control xs a m hm T ε hε)
  have hb := MPFSegments.accumulated_local (mu xs m * |T|) (∑ j, |a j|) ε m hm
    (mul_nonneg (mu_nonneg xs m hm) (abs_nonneg T))
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) hε
  have he' : ‖actualMPF xs q a (T / r) -
      NormedSpace.exp ((T / r) • ((-Complex.I) • xs.sum))‖ ≤
      (8 / 3 : ℝ) * (∑ j, |a j|) * ((mu xs m * |T|) / (r : ℝ)) ^ (2 * m + 1) := by
    simpa only [abs_div, abs_of_pos hr, ← mul_div_assoc] using! he
  apply he'.trans
  apply (le_div_iff₀ (by positivity : 0 < 12 * Real.pi * (r : ℝ))).mpr
  have hb' := (le_div_iff₀ (by positivity : 0 < 12 * Real.pi)).mp hb
  dsimp only [r, segments] at hb' ⊢
  nlinarith

omit [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K] in

/-- For positive r and ε ≤ 1, the slice budget ε/(12πr) is at most 1/5. -/
theorem slice_budget_small (ε : ℝ) (hε1 : ε ≤ 1) (r : ℕ) (hr : 0 < r) :
    ε / (12 * Real.pi * (r : ℝ)) ≤ 1 / 5 := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  apply (div_le_iff₀ (by positivity : 0 < 12 * Real.pi * (r : ℝ))).mpr
  nlinarith [Real.pi_gt_three]

/-- Under the stated hypotheses and 0 < ε ≤ 1, the amplified slice is a scale-one block encoding
of the exact slice with error ε/(12r). -/
theorem slice_encoding (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    BlockEncoding (NormedSpace.exp ((T / segments xs a m T ε) • ((-Complex.I) • xs.sum)))
      (MPFOAALCU.amplified xs q a (T / segments xs a m T ε))
      (scaleEightFrame (MPFOAALCU.frame a)) (scaleEightFrame (MPFOAALCU.frame a))
      1 (ε / (12 * (segments xs a m T ε : ℝ))) := by
  let r := segments xs a m T ε
  have hr : 0 < r := segments_pos xs a m T ε
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have he := raw_slice_error xs hxs q hq a ha m hm hmom T ε hε
  have h := MPFOAALCU.padded_encoding xs hxs q a ha (T / r)
  have hV := general_trotter_exp_unitary _ 1 (BCHPerturbation.target_skew xs hxs (T / r))
  simp only [one_smul] at hV
  have hb := MPFOAARobust.word_error_pi (MPFOAALCU.mass a) _ _ _ _ hV
    (he.trans (slice_budget_small ε hε1 r hr)) h
  refine ⟨(MPFOAAWord.word_wellFormed _ _ h.left_isometry).evaluate_unitary h.unitary,
    h.left_isometry, h.right_isometry, by norm_num, by positivity, ?_⟩
  rw [one_smul, norm_sub_rev]
  apply hb.trans
  calc
    _ ≤ Real.pi * (ε / (12 * Real.pi * (r : ℝ))) := mul_le_mul_of_nonneg_left he Real.pi_pos.le
    _ = _ := by change Real.pi * (ε / (12 * Real.pi * (r : ℝ))) = ε / (12 * (r : ℝ)); field_simp

/-- The compression of the amplified multi-product operator to its scaled frame. -/
def block (xs : List (Matrix I I ℂ)) (q : K → ℕ) (a : K → ℝ) (t : ℝ) : Matrix I I ℂ :=
  compress (scaleEightFrame (MPFOAALCU.frame a)) (MPFOAALCU.amplified xs q a t)
    (scaleEightFrame (MPFOAALCU.frame a))

/-- The r-th power of the compressed amplified slice approximates the full-time target
exponential within ε/12. -/
theorem block_power_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖block xs q a (T / segments xs a m T ε) ^ segments xs a m T ε -
      NormedSpace.exp (T • ((-Complex.I) • xs.sum))‖ ≤ ε / 12 := by
  let r := segments xs a m T ε
  have hr : 0 < r := segments_pos xs a m T ε
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have h := slice_encoding xs hxs q hq a ha m hm hmom T ε hε hε1
  have hC : ‖block xs q a (T / r)‖ ≤ 1 :=
    (compress_norm_le h.left_isometry h.right_isometry _).trans (unitary_norm_le_one h.unitary)
  have hV := general_trotter_exp_unitary _ 1 (BCHPerturbation.target_skew xs hxs (T / r))
  simp only [one_smul] at hV
  have he : ‖block xs q a (T / r) - NormedSpace.exp ((T / r) • ((-Complex.I) • xs.sum))‖ ≤
      ε / (12 * (r : ℝ)) := by simpa only [one_smul, norm_sub_rev] using! h.error_le
  have hb := (l2_norm_pow_sub_pow_le _ _ hC (unitary_norm_le_one hV) r).trans
    (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg r))
  rw [Qatlib.Papers.CommutLCHS26.QuadratureCmp.RawMPF.target_power _ T r hr] at hb
  exact hb.trans (by apply le_of_eq; field_simp)

/-- For a normalized input, a chosen amplified slice has postselection failure probability at
most ε/(6r). -/
theorem slice_failure (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (q : K → ℕ) (hq : ∀ j, 0 < q j) (a : K → ℝ) (ha : ∑ j, a j = 1)
    (m : ℕ) (hm : 0 < m) (hmom : ∀ k, 0 < k → k < m → coefficientWeight q a k = 0)
    (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ψ : QState I) (hψ : Normalized ψ) :
    1 - postselectionProbability (MPFOAALCU.amplified xs q a (T / segments xs a m T ε))
      (scaleEightFrame (MPFOAALCU.frame a)) (scaleEightFrame (MPFOAALCU.frame a)) ψ ≤
      ε / (6 * (segments xs a m T ε : ℝ)) := by
  let r := segments xs a m T ε
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast segments_pos xs a m T ε
  have h := slice_encoding xs hxs q hq a ha m hm hmom T ε hε hε1
  have hV := general_trotter_exp_unitary _ 1 (BCHPerturbation.target_skew xs hxs (T / r))
  simp only [one_smul] at hV
  have hn : ‖stateVector (NormedSpace.exp ((T / r) • ((-Complex.I) • xs.sum)) *ᵥ ψ)‖ = 1 := by
    rw [IsIsometry.stateVector_norm (show IsIsometry _ from hV.1),
      (normalized_iff_stateVector_norm ψ).mp hψ]
  have hd : ε / (12 * (r : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 12 * (r : ℝ))).mpr
    linarith
  have hp := Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower
    h hψ (by rw [hn]; exact hd)
  rw [hn, div_one] at hp
  have he : ε / (6 * (r : ℝ)) = 2 * (ε / (12 * (r : ℝ))) := by ring
  change 1 - _ ≤ ε / (6 * (r : ℝ))
  rw [he]
  nlinarith [sq_nonneg (ε / (12 * (r : ℝ)))]

omit [Fintype K] [DecidableEq K] in

/-- For the Chebyshev construction, the repeated compressed amplified slice approximates the
full-time target within ε/12. -/
theorem chebyshev_block_error (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖block xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m)
        (T / segments xs (ChebyshevNodes.weight m) m T ε) ^
          segments xs (ChebyshevNodes.weight m) m T ε -
      NormedSpace.exp (T • ((-Complex.I) • xs.sum))‖ ≤ ε / 12 := by
  apply block_power_error xs hxs _ (ChebyshevNodes.node_pos m hm) _ _ m hm _ T ε hε hε1
  · simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm
  · intro k hk hkm
    exact (ChebyshevNodes.weight_moments m hm k hkm).trans (zero_pow (by omega))

omit [Fintype K] [DecidableEq K] in

/-- For a normalized input, the amplified Chebyshev slice has postselection failure probability
at most ε/(6r). -/
theorem chebyshev_slice_failure (xs : List (Matrix I I ℂ)) (hxs : ∀ A ∈ xs, Aᴴ = A)
    (m : ℕ) (hm : 0 < m) (T ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ψ : QState I) (hψ : Normalized ψ) :
    1 - postselectionProbability
      (MPFOAALCU.amplified xs (ChebyshevNodes.node m) (ChebyshevNodes.weight m)
        (T / segments xs (ChebyshevNodes.weight m) m T ε))
      (scaleEightFrame (MPFOAALCU.frame (ChebyshevNodes.weight m)))
      (scaleEightFrame (MPFOAALCU.frame (ChebyshevNodes.weight m))) ψ ≤
      ε / (6 * (segments xs (ChebyshevNodes.weight m) m T ε : ℝ)) := by
  apply slice_failure xs hxs _ (ChebyshevNodes.node_pos m hm) _ _ m hm _ T ε hε hε1 ψ hψ
  · simpa only [mul_zero, pow_zero, div_one] using! ChebyshevNodes.weight_moments m hm 0 hm
  · intro k hk hkm
    exact (ChebyshevNodes.weight_moments m hm k hkm).trans (zero_pow (by omega))

end Qatlib.Papers.CommutLCHS26.MainResults.MPFOAAAccuracy
