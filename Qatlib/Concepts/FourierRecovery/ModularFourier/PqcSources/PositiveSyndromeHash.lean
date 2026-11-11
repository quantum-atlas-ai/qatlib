/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.FiniteLinearHash
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources.PositiveFourierMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-! Actual full-vector linear hash masses. Zero coefficients and all matrices
are retained in the exact first moment; no rank promise is assumed. -/

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open scoped BigOperators ComplexConjugate Classical

/-- Definition of pqc Linear Syndrome Mass in the Modular Fourier construction. -/
noncomputable def pqcLinearSyndromeMass
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K)) (y : J → K) : ℝ := by
  classical
  exact ∑ v, if finiteLinearMatrixHash M v = y then p.prob v else 0

/-- The actual finite-label construction satisfies `pqc_linear_syndrome_mass_sum` with all displayed hypotheses. -/
theorem pqc_linear_syndrome_mass_sum
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K)) :
    ∑ y, pqcLinearSyndromeMass M p y = 1 := by
  classical
  unfold pqcLinearSyndromeMass
  rw [Finset.sum_comm]
  simpa using p.sum_one

/-- The actual finite-label construction satisfies `pqc_linear_syndrome_mass_nonneg` with all displayed hypotheses. -/
theorem pqc_linear_syndrome_mass_nonneg
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K)) (y : J → K) :
    0 ≤ pqcLinearSyndromeMass M p y := by
  classical
  apply Finset.sum_nonneg
  intro v _
  split <;> simp_all [p.nonneg]

/-- Definition of linear Hash Hom in the Modular Fourier construction. -/
private noncomputable def linearHashHom
    {K I J : Type} [Field K] [Fintype I] (M : Matrix I J K) :
    (I → K) →+ (J → K) where
  toFun := finiteLinearMatrixHash M
  map_zero' := by ext j; simp [finiteLinearMatrixHash]
  map_add' v w := by
    ext j
    simp [finiteLinearMatrixHash, mul_add, Finset.sum_add_distrib]

/-- The actual hash pushforward coefficient is the input coefficient at the
pulled-back character, even when the linear hash is not surjective. -/
theorem pqc_linear_syndrome_fourier_nonneg
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K))
    (hpos : pqcMassHasNonnegativeFourier p.prob) :
    pqcMassHasNonnegativeFourier (pqcLinearSyndromeMass M p) := by
  intro χ
  have heq : pqcMassFourierCoefficient (pqcLinearSyndromeMass M p) χ =
      pqcMassFourierCoefficient p.prob (χ.compAddMonoidHom (linearHashHom M)) := by
    simp only [pqcMassFourierCoefficient, pqcLinearSyndromeMass,
      Complex.ofReal_sum, apply_ite, Complex.ofReal_zero, Finset.sum_mul,
      ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [linearHashHom]
  rw [heq]
  exact hpos _

/-- The actual finite-label construction satisfies `pqc_linear_zero_excess_nonneg` with all displayed hypotheses. -/
theorem pqc_linear_zero_excess_nonneg
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K))
    (hpos : pqcMassHasNonnegativeFourier p.prob) :
    0 ≤ (Fintype.card (J → K) : ℝ)*pqcLinearSyndromeMass M p 0-1 := by
  exact pqc_positive_fourier_mass_nonneg _ (pqc_linear_syndrome_mass_sum M p)
    (pqc_linear_syndrome_fourier_nonneg M p hpos)

/-- The actual finite-label construction satisfies `pqc_linear_syndrome_uniform_deviation` with all displayed hypotheses. -/
theorem pqc_linear_syndrome_uniform_deviation
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K))
    (hpos : pqcMassHasNonnegativeFourier p.prob) (y : J → K) :
    |(Fintype.card (J → K) : ℝ)*pqcLinearSyndromeMass M p y-1| ≤
      (Fintype.card (J → K) : ℝ)*pqcLinearSyndromeMass M p 0-1 := by
  exact pqc_positive_fourier_mass_deviation _ (pqc_linear_syndrome_mass_sum M p)
    (pqc_linear_syndrome_fourier_nonneg M p hpos) y

/-- Small excess implies actual surjectivity, rather than assuming full rank
to obtain the mass estimate. -/
theorem pqc_linear_hash_surjective_of_excess_lt_one
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J K) (p : FinDist (I → K))
    (hpos : pqcMassHasNonnegativeFourier p.prob)
    (hsmall : (Fintype.card (J → K) : ℝ)*pqcLinearSyndromeMass M p 0-1 < 1) :
    Function.Surjective (finiteLinearMatrixHash M) := by
  by_contra h
  change ¬ ∀ y : J → K, ∃ v : I → K, finiteLinearMatrixHash M v = y at h
  push Not at h
  obtain ⟨y, hy⟩ := h
  have hz : pqcLinearSyndromeMass M p y = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    exact if_neg (hy v)
  have hdev := pqc_linear_syndrome_uniform_deviation M p hpos y
  rw [hz] at hdev
  simp only [mul_zero, zero_sub, abs_neg, abs_one] at hdev
  linarith

/-- The actual finite-label construction satisfies `pqc_linear_zero_excess_average` with all displayed hypotheses. -/
theorem pqc_linear_zero_excess_average
    (K I J : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : FinDist (I → K)) :
    finiteHashAverage (fun M : Matrix I J K =>
      (Fintype.card (J → K) : ℝ) * pqcLinearSyndromeMass M p 0 - 1) =
      ((Fintype.card (J → K) : ℝ)-1) * p.prob 0 := by
  classical
  let N : ℝ := Fintype.card (J → K)
  have hn : N ≠ 0 := by dsimp [N]; exact_mod_cast Fintype.card_ne_zero
  have havg_const (c : ℝ) : finiteHashAverage (fun _ : Matrix I J K => c) = c := by
    have hm : (Fintype.card (Matrix I J K) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [finiteHashAverage, hm]
  have hash_zero (M : Matrix I J K) : finiteLinearMatrixHash M (0 : I → K) = 0 := by
    funext j
    simp [finiteLinearMatrixHash]
  have hevent (v : I → K) :
      finiteHashAverage (fun M : Matrix I J K =>
        if finiteLinearMatrixHash M v = 0 then 1 else 0) =
      if v = 0 then 1 else N⁻¹ := by
    by_cases hv : v = 0
    · subst v
      simp only [hash_zero, if_true]
      exact havg_const 1
    · simpa only [hv, if_false, hash_zero, N] using
        finite_linear_matrix_hash_collision K I J v 0 hv
  have hmass : finiteHashAverage (fun M : Matrix I J K => pqcLinearSyndromeMass M p 0) =
      N⁻¹ + (1-N⁻¹)*p.prob 0 := by
    unfold pqcLinearSyndromeMass finiteHashAverage
    rw [Finset.sum_comm, Finset.mul_sum]
    change (∑ v : I → K, finiteHashAverage (fun M : Matrix I J K =>
      if finiteLinearMatrixHash M v = 0 then p.prob v else 0)) = _
    have hterm (v : I → K) :
        finiteHashAverage (fun M : Matrix I J K =>
          if finiteLinearMatrixHash M v = 0 then p.prob v else 0) =
          (if v = 0 then 1 else N⁻¹) * p.prob v := by
      rw [← hevent]
      simp only [finiteHashAverage, mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro M _
      split <;> simp
    simp_rw [hterm]
    have hsplit (v : I → K) :
        (if v = 0 then 1 else N⁻¹)*p.prob v =
        N⁻¹*p.prob v + (if v = 0 then (1-N⁻¹)*p.prob 0 else 0) := by
      by_cases hv : v = 0
      · subst v
        simp only [if_true]
        ring
      · simp [hv]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, p.sum_one]
    simp
  have hlinear (f : Matrix I J K → ℝ) :
      finiteHashAverage (fun M => N*f M-1) = N*finiteHashAverage f-1 := by
    unfold finiteHashAverage
    have hm : (Fintype.card (Matrix I J K) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
  change finiteHashAverage (fun M : Matrix I J K => N*pqcLinearSyndromeMass M p 0-1) = _
  rw [hlinear, hmass]
  dsimp only [N] at hn ⊢
  field_simp
  ring

/-- A single zero-output moment controls the event that any syndrome is bad.
The Fourier condition is on the actual input law, and is transported through
every literal matrix hash. There is no union factor for the output labels. -/
theorem pqc_positive_linear_hash_flatness_probability
    (K I J : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (p : FinDist (I → K)) (hpos : pqcMassHasNonnegativeFourier p.prob)
    (ε : ℝ) (hε : 0 < ε) :
    finiteHashAverage (fun M : Matrix I J K =>
      if ∃ y : J → K, ε < |(Fintype.card (J → K) : ℝ)*pqcLinearSyndromeMass M p y-1|
      then 1 else 0) ≤
        (((Fintype.card (J → K) : ℝ)-1)*p.prob 0)/ε := by
  let N : ℝ := Fintype.card (J → K)
  have hpoint (M : Matrix I J K) :
      ε*(if ∃ y : J → K, ε < |N*pqcLinearSyndromeMass M p y-1| then 1 else 0) ≤
        N*pqcLinearSyndromeMass M p 0-1 := by
    split_ifs with h
    · obtain ⟨y, hy⟩ := h
      have hd := pqc_linear_syndrome_uniform_deviation M p hpos y
      dsimp only [N] at hy ⊢
      simpa only [mul_one] using le_trans (le_of_lt hy) hd
    · simpa only [mul_zero] using pqc_linear_zero_excess_nonneg M p hpos
  have havg := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) (fun M _ => hpoint M))
    (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Matrix I J K)) :
      (0 : ℝ) ≤ Fintype.card (Matrix I J K)))
  change finiteHashAverage (fun M : Matrix I J K =>
      ε*(if ∃ y : J → K, ε < |N*pqcLinearSyndromeMass M p y-1| then 1 else 0)) ≤
      finiteHashAverage (fun M : Matrix I J K => N*pqcLinearSyndromeMass M p 0-1) at havg
  rw [pqc_linear_zero_excess_average] at havg
  have hscale (f : Matrix I J K → ℝ) :
      finiteHashAverage (fun M => ε*f M) = ε*finiteHashAverage f := by
    simp only [finiteHashAverage, ← Finset.mul_sum]
    ring
  rw [hscale] at havg
  apply (le_div_iff₀ hε).2
  simpa only [mul_comm] using havg

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
