/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QActiveLearn14.TailedBounds

/-!
# Mixture bounds for quantum reflecting

This module formalizes the mixture estimate behind Theorem 5 of [PaparoEtAl2014]. If a
successful branch is within `η` of the target in total variation and the failure probability is
at most `β ^ k₃`, the output mixture is within `β ^ k₃ + η` of the target.

## Main statements

* `theorem5_quantum_reflecting`: the total-variation mixture estimate.
* `theorem5_distance_le_delta`: a target error from two half-error bounds.
* `theorem5_with_half_constant`: the estimate with failure base one half.

## References

* [Paparo et al., 2014][PaparoEtAl2014]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QActiveLearn14.MixModels

open Qatlib.Papers.QActiveLearn14.TailedBounds
open scoped BigOperators

variable {X : Type*} [Fintype X]

/-- A mixture with success probability at least `1 - β ^ k₃` and successful-branch distance at
most `η` has total-variation distance at most `β ^ k₃ + η` from the target [Paparo et al.,
Theorem 5][PaparoEtAl2014]. -/
theorem theorem5_quantum_reflecting
    (πtilde κ ν σ : X → ℝ) (p β η : ℝ) (k₃ : ℕ)
    (hπ : IsProbability πtilde) (_hν : IsProbability ν)
    (hσ : IsProbability σ)
    (hmix : ∀ x, κ x = p * ν x + (1 - p) * σ x)
    (hsuccess : 1 - β ^ k₃ ≤ p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1)
    (hνclose : tvDist ν πtilde ≤ η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    tvDist κ πtilde ≤ β ^ k₃ + η := by
  have hmixle := tvDist_convex_mix (πtilde := πtilde) hmix hp0 hp1
  have hσ1 : tvDist σ πtilde ≤ 1 := tvDist_le_one hσ hπ
  have hβk0 : 0 ≤ β ^ k₃ := pow_nonneg hβ0 _
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hstep : tvDist κ πtilde ≤ p * η + (1 - p) := by
    calc tvDist κ πtilde ≤ p * tvDist ν πtilde + (1 - p) * tvDist σ πtilde := hmixle
      _ ≤ p * η + (1 - p) * 1 := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hνclose hp0
          · exact mul_le_mul_of_nonneg_left hσ1 h1p
      _ = p * η + (1 - p) := by ring
  have hkey : p * η + (1 - p) = (1 - p) * (1 - η) + η := by ring
  have h1pβ : 1 - p ≤ β ^ k₃ := by linarith
  have h1 : (1 - p) * (1 - η) ≤ β ^ k₃ * (1 - η) :=
    mul_le_mul_of_nonneg_right h1pβ (sub_nonneg.mpr hη1)
  have h2 : β ^ k₃ * (1 - η) ≤ β ^ k₃ := by
    have hmul := mul_le_mul_of_nonneg_left (show (1 - η) ≤ 1 by linarith) hβk0
    simpa using hmul
  rw [hkey] at hstep
  linarith

/-- The mixture is within total-variation distance `δ` when both the failure bound `β ^ k₃` and
the successful-branch error `η` are at most `δ / 2`. -/
theorem theorem5_distance_le_delta
    (πtilde κ ν σ : X → ℝ) (p β η δ : ℝ) (k₃ : ℕ)
    (hπ : IsProbability πtilde) (hν : IsProbability ν)
    (hσ : IsProbability σ)
    (hmix : ∀ x, κ x = p * ν x + (1 - p) * σ x)
    (hsuccess : 1 - β ^ k₃ ≤ p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hνclose : tvDist ν πtilde ≤ η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hβk : β ^ k₃ ≤ δ / 2) (hηδ : η ≤ δ / 2) :
    tvDist κ πtilde ≤ δ := by
  have h := theorem5_quantum_reflecting πtilde κ ν σ p β η k₃ hπ hν hσ hmix
    hsuccess hp0 hp1 hβ0 hβ1 hνclose hη0 hη1
  linarith

/-- A mixture whose failure probability is at most `(1 / 2) ^ k₃` is within `(1 / 2) ^ k₃ + η`
of the target under the stated probability and approximation assumptions. -/
theorem theorem5_with_half_constant
    (πtilde κ ν σ : X → ℝ) (p η : ℝ) (k₃ : ℕ)
    (hπ : IsProbability πtilde) (hν : IsProbability ν) (hσ : IsProbability σ)
    (hmix : ∀ x, κ x = p * ν x + (1 - p) * σ x)
    (hsuccess : 1 - (1 / 2 : ℝ) ^ k₃ ≤ p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hνclose : tvDist ν πtilde ≤ η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    tvDist κ πtilde ≤ (1 / 2 : ℝ) ^ k₃ + η :=
  theorem5_quantum_reflecting πtilde κ ν σ p (1 / 2) η k₃ hπ hν hσ hmix hsuccess
    hp0 hp1 (by norm_num) (by norm_num) hνclose hη0 hη1

end Qatlib.Papers.QActiveLearn14.MixModels
