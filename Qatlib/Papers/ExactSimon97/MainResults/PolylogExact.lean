/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.AmplifyCore.Theorem4QuadraticSpeedupWithKnownAQuan
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Exact progress at a known inverse-polylogarithmic fraction

Fixed source: [Brassard and Hoyer, 1997][BrassardHoyer1997], Section 6.
This module formalizes the amplification step used after an exact Fourier
readout. Given a preparation with known marked probability `1 / k` on a finite
label space, the executed two-register program has total squared Euclidean norm
one and marked mass one. The bound counts preparation and inverse preparation
calls with one constant fixed before all finite instances.

## Main statements

* `exactSimon_knownFraction_exact_program`: for every nonempty finite label set
  with a nondegenerate known fraction `1 / k`, the exact amplification word has
  unit Euclidean norm, places all output mass on marked labels, and uses at most
  a uniform constant times `log₂ |label set| ^ (exponent / 2)` calls.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.ExactSimon97.MainResults.PolylogExact

open Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification

/-- The coordinate Hilbert basis of a finite complex Euclidean label space. -/
noncomputable abbrev coordinateBasis (N : ℕ) :
    HilbertBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)) :=
  (EuclideanSpace.basisFun (Fin N) ℂ).toHilbertBasis

/-- Integer labels identify Euclidean coordinates with their natural indices. -/
def coordinateLabel (N : ℕ) (i : Fin N) : ℤ := (i.val : ℤ)

/-- The Boolean marking predicate associated with a finite marked label set. -/
def markedPredicate (N : ℕ) (S : Finset (Fin N)) : ℤ → Bool :=
  fun z => decide (z ∈ (S.image fun i : Fin N => (i.val : ℤ)))

/-- The marked orthogonal projection on the coordinate Euclidean space. -/
noncomputable abbrev exactSimonProjection (N : ℕ) (S : Finset (Fin N)) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.goodProjection
    (coordinateBasis N) (coordinateLabel N)
    (markedPredicate N S)

/-- Execute a two-register exact-amplification program from the zeroth basis
vector, with preparation `A` acting on the complex Euclidean label space. -/
noncomputable abbrev exactSimonRun {N : ℕ} (hN : 0 < N) (S : Finset (Fin N))
    (A : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (r : ℝ) (program : List (Fin 6)) :
    EuclideanSpace ℂ (Fin N) × EuclideanSpace ℂ (Fin N) :=
  Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.run A
    (coordinateBasis N ⟨0, hN⟩)
    (exactSimonProjection N S) r program

/-- The marked mass in both Euclidean output registers of `exactSimonRun`. -/
noncomputable abbrev exactSimonGoodMass {N : ℕ} (hN : 0 < N)
    (S : Finset (Fin N))
    (A : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
    (r : ℝ) (program : List (Fin 6)) : ℝ :=
  let output := exactSimonRun hN S A r program
  ‖(exactSimonProjection N S) output.1‖ ^ 2 +
    ‖(exactSimonProjection N S) output.2‖ ^ 2

/-- Convert the known-fraction inverse-square-root cost to the Section-6
polylogarithmic form used by the top-level theorem. -/
private lemma sqrt_fraction_bound (k exponent N : ℝ) (hk : 2 ≤ k)
    (hN : 2 ≤ N) (hbound : k ≤ Real.logb 2 N ^ exponent) :
    Real.sqrt k ≤ Real.logb 2 N ^ (exponent / 2) := by
  have hLpos : (0 : ℝ) < Real.logb 2 N :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hsplit : (Real.logb 2 N ^ exponent) ^ ((1 : ℝ) / 2) =
      Real.logb 2 N ^ (exponent / 2) := by
    rw [(Real.rpow_mul hLpos.le exponent ((1 : ℝ) / 2)).symm]
    congr 1
    field_simp
  rw [← hsplit]
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow (by linarith) hbound (by norm_num)

/-- Exact amplification for Section 6 with a known marked fraction. The ambient
label set has cardinality at least two and `k ≥ 2`. The preparation `A` is a
supplied linear isometry equivalence whose marked mass is `1 / k`. The sum of
squared complex Euclidean norms of the two output registers is one. The
preparation-call constant is uniform across all finite instances. Applying
this to the source's subgroup algorithm requires an exact Fourier preparation
and a suitable efficient marking predicate. -/
theorem exactSimon_knownFraction_exact_program :
    ∃ queryConstant : ℝ, 0 < queryConstant ∧
      ∀ (N k exponent : ℕ) (_hnonempty : Nonempty (Fin N)) (hN : 2 ≤ N)
        (hk : 2 ≤ k) (S : Finset (Fin N))
        (A : EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N))
        (hmass : ‖(exactSimonProjection N S)
            (A (coordinateBasis N ⟨0, by omega⟩))‖ ^ 2 =
          1 / ((k : ℕ) : ℝ))
        (hbound : ((k : ℕ) : ℝ) ≤
            Real.logb 2 ((N : ℕ) : ℝ) ^ ((exponent : ℕ) : ℝ)),
        ∃ (r : ℝ) (program : List (Fin 6)),
          0 ≤ r ∧ r ≤ 1 ∧
          ‖(exactSimonRun (by omega) S A r program).1‖ ^ 2 +
            ‖(exactSimonRun (by omega) S A r program).2‖ ^ 2 = 1 ∧
          exactSimonGoodMass (by omega) S A r program = 1 ∧
          (Qatlib.Concepts.AmplitudeCore.AmplifyCore.ExactAmplification.calls
            program : ℝ) ≤
            queryConstant * Real.logb 2 ((N : ℕ) : ℝ) ^
              (((exponent : ℕ) : ℝ) / 2) := by
  obtain ⟨design, _lower, upper, _lowerPositive, hUpperPositive, instances⟩ :=
    Qatlib.Concepts.AmplitudeCore.AmplifyCore.zoo_amplitude_amplification_known_a_exact
  refine ⟨upper, hUpperPositive,
    fun N k exponent _hnonempty hN hk S A hmass hbound => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le (by omega) hN
  have hpositive : 0 < 1 / ((k : ℕ) : ℝ) := by positivity
  have hlaw := instances (Fin N) (EuclideanSpace ℂ (Fin N))
    (coordinateBasis N) ⟨0, hNpos⟩ (coordinateLabel N) A
    (markedPredicate N S) (1 / ((k : ℕ) : ℝ)) hmass.symm hpositive
  obtain ⟨hr0, hr1, hnorm, hgood, _hlow, hhigh⟩ := hlaw
  have hcost : upper / Real.sqrt ((1 : ℝ) / ((k : ℕ) : ℝ)) =
      upper * Real.sqrt ((k : ℕ) : ℝ) := by
    have hsqrteq : Real.sqrt ((1 : ℝ) / ((k : ℕ) : ℝ)) =
        1 / Real.sqrt ((k : ℕ) : ℝ) := by
      rw [one_div, Real.sqrt_inv, one_div]
    rw [hsqrteq, div_eq_mul_inv, one_div, inv_inv]
  rw [hcost] at hhigh
  have hmono := sqrt_fraction_bound ((k : ℕ) : ℝ) ((exponent : ℕ) : ℝ)
    ((N : ℕ) : ℝ) (by exact_mod_cast hk) (by exact_mod_cast hN) hbound
  exact ⟨(design (1 / ((k : ℕ) : ℝ))).1,
    (design (1 / ((k : ℕ) : ℝ))).2, hr0, hr1, hnorm, hgood,
    hhigh.trans
      (mul_le_mul_of_nonneg_left hmono (le_of_lt hUpperPositive))⟩

end Qatlib.Papers.ExactSimon97.MainResults.PolylogExact
