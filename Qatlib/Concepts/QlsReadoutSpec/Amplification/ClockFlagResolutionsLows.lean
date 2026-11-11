/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.ClockFlagResolutionsStat
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows

/-!
# Clock and flag projector resolutions

Proves `Clause3ClockFlagResolutions` from the clock legality hypotheses. Nested clock projectors
yield orthogonal increments summing to the identity, commuting bad-flag refinements, and
decreasing potential projectors with explicit endpoint values, corresponding to the projector
identities of [LowSu2026].

## Main statements

* `Clause3ClockFlagResolutions_answer`: establishes the clock increment, flag refinement, and
  potential identities.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QlsReadoutSpec.Amplification

namespace Qatlib.Concepts.QlsReadoutSpec.Amplification

open Matrix Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators ComplexOrder

/-- Proves the clock and flag projector resolution contract, including orthogonal increments,
flag refinements, potential order, and endpoint identities; see [Low and Su, Propositions 11
and 12][LowSu2026]. -/
theorem Clause3ClockFlagResolutions_answer : Clause3ClockFlagResolutions := by
  intro H _ _ m P bad hlegal
  obtain ⟨hP, hP0, hPm, hpsd, hbad, hcomm⟩ := hlegal
  have hP_star : ∀ j : Fin (m + 1), star (P j) = P j := fun j => (hP j).isSelfAdjoint
  have hbad_sq : bad * bad = bad := hbad.isIdempotentElem

  have clause2_psd (A B : Matrix H H ℂ) (hA : IsOrthogonalProjector A)
      (hB : IsOrthogonalProjector B) : A * B = B ↔ (A - B).PosSemidef :=
    (Clause2ProjectorOrder_answer H B A hB hA).2.2.2.2.2.1

  have mul_right : ∀ j k : Fin (m + 1), j.val ≤ k.val → P k * P j = P j := by
    intro j k hjk
    exact (clause2_psd (P k) (P j) (hP k) (hP j)).mpr (hpsd j k hjk)
  have mul_left : ∀ j k : Fin (m + 1), j.val ≤ k.val → P j * P k = P j := by
    intro j k hjk
    have h := mul_right j k hjk
    have := congrArg star h
    rwa [star_mul, hP_star j, hP_star k] at this

  have mul_bad : ∀ j, IsOrthogonalProjector (P j * bad) := fun j =>
    IsStarProjection.mul (hP j) hbad (hcomm j)
  have pot_proj : ∀ j, IsOrthogonalProjector (potential (P j) bad) := by
    intro j
    show IsOrthogonalProjector (1 - P j * bad)
    exact (mul_bad j).one_sub

  have bad_prod : ∀ j k : Fin (m + 1), j.val ≤ k.val →
      (P k * bad) * (P j * bad) = P j * bad := by
    intro j k hjk
    have h := mul_right j k hjk
    calc (P k * bad) * (P j * bad)
        = P k * (bad * (P j * bad)) := mul_assoc _ _ _
      _ = P k * ((bad * P j) * bad) := by rw [← mul_assoc bad (P j) bad]
      _ = P k * ((P j * bad) * bad) := by rw [← hcomm j]
      _ = P k * (P j * (bad * bad)) := by rw [mul_assoc (P j) bad bad]
      _ = P k * (P j * bad) := by rw [hbad_sq]
      _ = (P k * P j) * bad := by rw [← mul_assoc (P k) (P j) bad]
      _ = P j * bad := by rw [h]
  have bad_prod' : ∀ j k : Fin (m + 1), j.val ≤ k.val →
      (P j * bad) * (P k * bad) = P j * bad := by
    intro j k hjk
    have h := mul_left j k hjk
    calc (P j * bad) * (P k * bad)
        = P j * (bad * (P k * bad)) := mul_assoc _ _ _
      _ = P j * ((bad * P k) * bad) := by rw [← mul_assoc bad (P k) bad]
      _ = P j * ((P k * bad) * bad) := by rw [← hcomm k]
      _ = P j * (P k * (bad * bad)) := by rw [mul_assoc (P k) bad bad]
      _ = P j * (P k * bad) := by rw [hbad_sq]
      _ = (P j * P k) * bad := by rw [← mul_assoc (P j) (P k) bad]
      _ = P j * bad := by rw [h]

  have D_proj : ∀ j : Fin m,
      IsOrthogonalProjector (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) := by
    intro j
    have hj : (⟨j.val, by omega⟩ : Fin (m + 1)).val ≤
        (⟨j.val + 1, by omega⟩ : Fin (m + 1)).val := by
      show j.val ≤ j.val + 1
      omega
    exact IsStarProjection.sub_of_mul_eq_right (hP ⟨j.val, by omega⟩)
      (hP ⟨j.val + 1, by omega⟩) (mul_right ⟨j.val, by omega⟩ ⟨j.val + 1, by omega⟩ hj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact mul_right j k hjk
    · exact mul_left j k hjk
    · have expand : (1 - P j) * (1 - P k) = 1 - P k - P j + P j * P k := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel
      rw [expand, mul_left j k hjk]
      abel
    · have expand : (1 - P k) * (1 - P j) = 1 - P j - P k + P k * P j := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel
      rw [expand, mul_right j k hjk]
      abel
    · exact IsStarProjection.sub_of_mul_eq_right (hP j) (hP k) (mul_right j k hjk)
    · exact pot_proj j
    · show (1 - P k * bad) * (1 - P j * bad) = 1 - P k * bad
      have expand : (1 - P k * bad) * (1 - P j * bad) =
          1 - P k * bad - P j * bad + (P k * bad) * (P j * bad) := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel
      rw [expand, bad_prod j k hjk]
      abel
    · show (1 - P j * bad) * (1 - P k * bad) = 1 - P k * bad
      have expand : (1 - P j * bad) * (1 - P k * bad) =
          1 - P j * bad - P k * bad + (P j * bad) * (P k * bad) := by
        rw [sub_mul, one_mul, mul_sub, mul_one]
        abel
      rw [expand, bad_prod' j k hjk]
      abel
    · have hdiff : potential (P j) bad - potential (P k) bad = P k * bad - P j * bad := by
        show (1 - P j * bad) - (1 - P k * bad) = P k * bad - P j * bad
        abel
      rw [hdiff]
      exact (clause2_psd (P k * bad) (P j * bad) (mul_bad k) (mul_bad j)).mp
        (bad_prod j k hjk)
  · set f : ℕ → Matrix H H ℂ := fun k => if h : k ≤ m then P ⟨k, by omega⟩ else 1
    have hf_le : ∀ k (hk : k ≤ m), f k = P ⟨k, by omega⟩ := by
      intro k hk
      show (if h : k ≤ m then P ⟨k, by omega⟩ else 1) = P ⟨k, by omega⟩
      exact dif_pos hk
    have hsum_eq : ∑ j : Fin m, (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) =
        ∑ i ∈ Finset.range m, (f (i + 1) - f i) := by
      have step1 : ∑ j : Fin m, (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) =
          ∑ j : Fin m, (f (j.val + 1) - f j.val) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj1 : j.val + 1 ≤ m := Nat.succ_le_of_lt j.isLt
        have hj2 : j.val ≤ m := Nat.le_of_lt j.isLt
        rw [hf_le (j.val + 1) hj1, hf_le j.val hj2]
      have step2 : ∑ j : Fin m, (f (j.val + 1) - f j.val) =
          ∑ i ∈ Finset.range m, (f (i + 1) - f i) :=
        Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i) m
      rw [step1, step2]
    have hfm : f m = 1 := by rw [hf_le m le_rfl]; exact hPm
    have hf0 : f 0 = 0 := by rw [hf_le 0 (by omega)]; exact hP0
    rw [hsum_eq, Finset.sum_range_sub f m, hfm, hf0, sub_zero]
  · intro j
    have hD_comm :
        (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) * bad =
          bad * (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) := by
      rw [sub_mul, mul_sub, hcomm ⟨j.val + 1, by omega⟩, hcomm ⟨j.val, by omega⟩]
    have hD_1_comm :
        (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) * (1 - bad) =
          (1 - bad) * (P ⟨j.val + 1, by omega⟩ - P ⟨j.val, by omega⟩) := by
      conv_lhs => rw [mul_sub, mul_one]
      conv_rhs => rw [sub_mul, one_mul]
      rw [hD_comm]
    exact ⟨D_proj j, hD_comm,
      IsStarProjection.mul (D_proj j) hbad hD_comm,
      IsStarProjection.mul (D_proj j) hbad.one_sub hD_1_comm⟩
  · intro j k hjk
    have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have main : ∀ a b : Fin m, a.val < b.val →
        (P ⟨a.val + 1, by omega⟩ - P ⟨a.val, by omega⟩) *
        (P ⟨b.val + 1, by omega⟩ - P ⟨b.val, by omega⟩) = 0 := by
      intro a b hab
      have hab1 : a.val + 1 ≤ b.val + 1 := by omega
      have hab2 : a.val + 1 ≤ b.val := by omega
      have hab3 : a.val ≤ b.val + 1 := by omega
      have hab4 : a.val ≤ b.val := by omega
      have h1 : P ⟨a.val + 1, by omega⟩ * P ⟨b.val + 1, by omega⟩ =
          P ⟨a.val + 1, by omega⟩ :=
        mul_left ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩ (by
          show (⟨a.val + 1, _⟩ : Fin (m + 1)).val ≤ (⟨b.val + 1, _⟩ : Fin (m + 1)).val
          exact hab1)
      have h2 : P ⟨a.val + 1, by omega⟩ * P ⟨b.val, by omega⟩ =
          P ⟨a.val + 1, by omega⟩ :=
        mul_left ⟨a.val + 1, by omega⟩ ⟨b.val, by omega⟩ (by
          show (⟨a.val + 1, _⟩ : Fin (m + 1)).val ≤ (⟨b.val, _⟩ : Fin (m + 1)).val
          exact hab2)
      have h3 : P ⟨a.val, by omega⟩ * P ⟨b.val + 1, by omega⟩ =
          P ⟨a.val, by omega⟩ :=
        mul_left ⟨a.val, by omega⟩ ⟨b.val + 1, by omega⟩ (by
          show (⟨a.val, _⟩ : Fin (m + 1)).val ≤ (⟨b.val + 1, _⟩ : Fin (m + 1)).val
          exact hab3)
      have h4 : P ⟨a.val, by omega⟩ * P ⟨b.val, by omega⟩ = P ⟨a.val, by omega⟩ :=
        mul_left ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ (by
          show (⟨a.val, _⟩ : Fin (m + 1)).val ≤ (⟨b.val, _⟩ : Fin (m + 1)).val
          exact hab4)
      have expand :
          (P ⟨a.val + 1, by omega⟩ - P ⟨a.val, by omega⟩) *
            (P ⟨b.val + 1, by omega⟩ - P ⟨b.val, by omega⟩) =
          P ⟨a.val + 1, by omega⟩ * P ⟨b.val + 1, by omega⟩ -
            P ⟨a.val + 1, by omega⟩ * P ⟨b.val, by omega⟩ -
            P ⟨a.val, by omega⟩ * P ⟨b.val + 1, by omega⟩ +
            P ⟨a.val, by omega⟩ * P ⟨b.val, by omega⟩ := by
        rw [sub_mul, mul_sub, mul_sub]
        abel
      rw [expand, h1, h2, h3, h4]
      abel
    rcases Nat.lt_or_gt_of_ne hjk' with hlt | hlt
    · exact main j k hlt
    · have h := main k j hlt
      have hstar := congrArg star h
      rw [star_mul, star_zero, (D_proj j).isSelfAdjoint, (D_proj k).isSelfAdjoint] at hstar
      exact hstar
  · intro j
    show 1 - P j * bad = P j * (1 - bad) + (1 - P j)
    rw [mul_sub, mul_one]
    abel
  · show 1 - P 0 * bad = 1
    rw [hP0, zero_mul, sub_zero]
  · show 1 - P ⟨m, by omega⟩ * bad = 1 - bad
    simp only [hPm, one_mul]

end Qatlib.Concepts.QlsReadoutSpec.Amplification
