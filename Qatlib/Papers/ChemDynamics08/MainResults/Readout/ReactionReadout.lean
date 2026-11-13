/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation

/-!
# Reaction region readout

`regionProb` sums squared amplitudes over a reaction region, and `locatedState` records the
region label in an additional register. The module identifies the resulting measurement
probabilities and proves their normalization, together with scalar bounds for sampling error and
amplitude estimation precision.

These constructions support the treatment in [KassalEtAl2008].

## Main statements

* `reaction_region_probability`: identifies the region ancilla probabilities and their sum.
* `amplitude_estimation_error_bound`: bounds amplitude error under a phase-distance hypothesis.

## References

* [Kassal et al., 2008][KassalEtAl2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open scoped BigOperators

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Papers.ChemDynamics08.MainResults.Readout

section Region

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]

/-- The sum of squared amplitudes of `ψ` over basis states whose region label is `i`. -/
noncomputable def regionProb (ψ : QState X) (R : X → ι) (i : ι) : ℝ :=
  Finset.sum (Finset.univ.filter (fun x => R x = i)) (fun x => ‖ψ x‖ ^ 2)

/-- The joint state that attaches the label `R x` to each basis state `x`, preserving its
amplitude. -/
noncomputable def locatedState (ψ : QState X) (R : X → ι) : QState (X × ι) :=
  fun p => if p.2 = R p.1 then ψ p.1 else 0

/-- Measuring region label `i` in the located state gives `regionProb ψ R i`. -/
theorem measureProb_locatedState_region (ψ : QState X) (R : X → ι) (i : ι) :
    MeasureProb (locatedState ψ R) (Finset.univ ×ˢ ({i} : Finset ι)) =
      regionProb ψ R i := by
  unfold MeasureProb regionProb locatedState BornProb
  rw [Finset.sum_product]
  simp only [Finset.mem_singleton, Finset.sum_singleton]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : R x = i
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hi : i = R x => h hi.symm), if_neg h]
    simp

/-- The region probabilities of a normalized state sum to one. -/
theorem sum_regionProb (ψ : QState X) (R : X → ι) (hψ : Normalized ψ) :
    ∑ i, regionProb ψ R i = 1 := by
  unfold regionProb
  calc ∑ i, Finset.sum (Finset.univ.filter (fun x => R x = i)) (fun x => ‖ψ x‖ ^ 2)
      = ∑ i, ∑ x : X, (if R x = i then ‖ψ x‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter]
    _ = ∑ x : X, ∑ i : ι, (if R x = i then ‖ψ x‖ ^ 2 else 0) := Finset.sum_comm
    _ = ∑ x : X, ‖ψ x‖ ^ 2 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single (R x)]
        · simp
        · intro i _ hi
          rw [if_neg (fun h : R x = i => hi h.symm)]
        · intro h
          exact absurd (Finset.mem_univ (R x)) h
    _ = 1 := hψ

/-- Attaching a deterministic region label preserves normalization of the state. -/
theorem locatedState_normalized (ψ : QState X) (R : X → ι) (hψ : Normalized ψ) :
    Normalized (locatedState ψ R) := by
  unfold Normalized
  have hinner : ∀ x : X, ∑ y : ι, ‖locatedState ψ R (x, y)‖ ^ 2 = ‖ψ x‖ ^ 2 := by
    intro x
    rw [Finset.sum_eq_single (R x)]
    · simp [locatedState]
    · intro y _ hy
      simp [locatedState, hy]
    · intro h
      exact absurd (Finset.mem_univ (R x)) h
  calc ∑ p : X × ι, ‖locatedState ψ R p‖ ^ 2
      = ∑ x : X, ∑ y : ι, ‖locatedState ψ R (x, y)‖ ^ 2 := Fintype.sum_prod_type _
    _ = ∑ x : X, ‖ψ x‖ ^ 2 := Finset.sum_congr rfl fun x _ => hinner x
    _ = 1 := hψ

/-- For a normalized state, the region ancilla measurement gives the region probabilities, which
sum to one [KassalEtAl2008]. -/
theorem reaction_region_probability (ψ : QState X) (R : X → ι) (hψ : Normalized ψ) :
    (∀ i : ι, MeasureProb (locatedState ψ R)
        (Finset.univ ×ˢ ({i} : Finset ι)) = regionProb ψ R i) ∧
    (∑ i : ι, regionProb ψ R i = 1) :=
  ⟨fun i => measureProb_locatedState_region ψ R i, sum_regionProb ψ R hψ⟩

end Region

/-- For a probability `p` and positive sample count `M`, the Bernoulli standard error is at most
`1 / (2 * Real.sqrt M)` [KassalEtAl2008]. -/
theorem sampling_standard_error (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : ℕ) (hM : 0 < M) :
    Real.sqrt (p * (1 - p) / (M : ℝ)) ≤ 1 / (2 * Real.sqrt (M : ℝ)) := by
  have hMℝ : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hquad : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  have hnonneg : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hdiv : p * (1 - p) / (M : ℝ) ≤ (1 / 4) / (M : ℝ) :=
    div_le_div_of_nonneg_right hquad hMℝ.le
  have hfour : (1 / 4) / (M : ℝ) = 1 / (4 * (M : ℝ)) := by ring
  rw [hfour] at hdiv
  have hrewrite : (1 : ℝ) / (4 * (M : ℝ)) = (1 / (2 * Real.sqrt (M : ℝ))) ^ 2 := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hMℝ.le]
    norm_num
  calc Real.sqrt (p * (1 - p) / (M : ℝ))
      ≤ Real.sqrt (1 / (4 * (M : ℝ))) := Real.sqrt_le_sqrt hdiv
    _ = 1 / (2 * Real.sqrt (M : ℝ)) := by
        rw [hrewrite, Real.sqrt_sq (by positivity)]

/-- Phase distance at most `1 / M` bounds the amplitude estimate error by `2π / M + π² / M²`
[KassalEtAl2008]. -/
theorem amplitude_estimation_error_bound (M : ℕ) (hM : 0 < M) (φ : ℝ) (z : Fin M)
    (hd : phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ)) :
    |aeEstimate M z - (Real.sin (Real.pi * φ)) ^ 2| ≤
      2 * Real.pi / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 := by
  have hMℝ : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hbase := aeEstimate_error_of_phaseDistance M hM φ z hd
  dsimp only at hbase
  have hsin0 : (0 : ℝ) ≤ (Real.sin (Real.pi * φ)) ^ 2 := sq_nonneg _
  have hsin1 : (Real.sin (Real.pi * φ)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_le_one (Real.pi * φ), Real.neg_one_le_sin (Real.pi * φ)]
  have hprod0 : 0 ≤ (Real.sin (Real.pi * φ)) ^ 2 *
      (1 - (Real.sin (Real.pi * φ)) ^ 2) :=
    mul_nonneg hsin0 (by linarith)
  have hprod1 : (Real.sin (Real.pi * φ)) ^ 2 *
      (1 - (Real.sin (Real.pi * φ)) ^ 2) ≤ 1 := by nlinarith
  have hsqrt : Real.sqrt ((Real.sin (Real.pi * φ)) ^ 2 *
      (1 - (Real.sin (Real.pi * φ)) ^ 2)) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hprod1
    simpa using h
  have hmul := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have hstep : 2 * Real.pi * Real.sqrt ((Real.sin (Real.pi * φ)) ^ 2 *
      (1 - (Real.sin (Real.pi * φ)) ^ 2)) / (M : ℝ) ≤ 2 * Real.pi / (M : ℝ) := by
    have h := div_le_div_of_nonneg_right hmul hMℝ.le
    calc 2 * Real.pi * Real.sqrt ((Real.sin (Real.pi * φ)) ^ 2 *
          (1 - (Real.sin (Real.pi * φ)) ^ 2)) / (M : ℝ)
        ≤ 2 * Real.pi * 1 / (M : ℝ) := h
      _ = 2 * Real.pi / (M : ℝ) := by ring
  linarith

/-- Every positive tolerance exceeds `2π / M + π² / M²` for some positive integer `M`
[KassalEtAl2008]. -/
theorem amplitude_estimation_precision_guarantee (eps : ℝ) (heps : 0 < eps) :
    ∃ M : ℕ, 0 < M ∧
      2 * Real.pi / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 ≤ eps := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((2 * Real.pi + Real.pi ^ 2) / eps))
  have hn1 : (1 : ℝ) ≤ (n : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
  have hnr : (0 : ℝ) < (n : ℝ) := by linarith
  have hn2 : 2 * Real.pi + Real.pi ^ 2 < (n : ℝ) * eps := by
    have h1 : (2 * Real.pi + Real.pi ^ 2) / eps ≤
        max 1 ((2 * Real.pi + Real.pi ^ 2) / eps) := le_max_right _ _
    have h2 : (2 * Real.pi + Real.pi ^ 2) / eps < (n : ℝ) := lt_of_le_of_lt h1 hn
    have := (div_lt_iff₀ heps).mp h2
    linarith
  refine ⟨n, by exact_mod_cast hnr, ?_⟩
  have hsq : Real.pi ^ 2 / (n : ℝ) ^ 2 ≤ Real.pi ^ 2 / (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := hn1
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    have hsimp : (Real.pi ^ 2 / (n : ℝ)) * (n : ℝ) ^ 2 = Real.pi ^ 2 * (n : ℝ) := by
      field_simp
    rw [hsimp]
    nlinarith [Real.pi_pos]
  have hsplit : 2 * Real.pi / (n : ℝ) + Real.pi ^ 2 / (n : ℝ) ^ 2
      ≤ (2 * Real.pi + Real.pi ^ 2) / (n : ℝ) := by
    rw [add_div]
    linarith
  have hfin : (2 * Real.pi + Real.pi ^ 2) / (n : ℝ) ≤ eps := by
    rw [div_le_iff₀ hnr]
    linarith
  linarith

end Qatlib.Papers.ChemDynamics08.MainResults.Readout
