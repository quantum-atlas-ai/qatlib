/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationReceipt
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationWeights

/-!
# Exact sampling of normalized dual vectors

This module expresses a nonnegative combination of family output distributions, together with a
point-mass offset, as the scaled law of an exact stopped sampler. `Family.withOffset` prepends a
deterministic output, while `selectorMasses` converts the offset and rational coefficients into
selector masses. These constructions support the sampling components of matrix optimization in
the semidefinite programming setting of [BrandaoSvore2017].

`dual_actual_output` proves that the resulting sampler has probabilities equal to `dualVector`
divided by the positive scale `dualScale`, under positivity of the offset, nonnegativity of the
coefficients, and a positive family size.

## Main statements

* `Family.stopped_real`: the real-valued mixture formula for the stopped sampler.
* `dualVector_sum`: the sum of the vector entries equals `dualScale`.
* `dual_actual_output`: exact realization of the normalized vector by the offset sampler.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Family

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Qatlib
open scoped ENNReal Classical

variable {T D m : ℕ}

namespace Family

/-- The real-valued probability of output `i` from family component `t`. -/
noncomputable def realOutput (F : Family T D m) (t : Fin T) (i : Fin m) : ℝ :=
  (F.output t i).toReal

/-- Every real-valued family output probability is nonnegative. -/
theorem realOutput_nonneg (F : Family T D m) (t : Fin T) (i : Fin m) :
    0 ≤ F.realOutput t i := ENNReal.toReal_nonneg

/-- The real-valued output probabilities of each family component sum to 1. -/
theorem realOutput_sum (F : Family T D m) (t : Fin T) : ∑ i, F.realOutput t i = 1 := by
  change (∑ i, (F.output t i).toReal) = 1
  rw [← ENNReal.toReal_sum (fun i _ => (F.output t).apply_ne_top i)]
  have hs := (F.output t).tsum_coe
  rw [tsum_fintype] at hs
  rw [hs, ENNReal.toReal_one]

/-- Prepends the deterministic program returning `j₀` to the family while retaining its oracle
and state data. -/
def withOffset (F : Family T D m) (j₀ : Fin m) : Family (T+1) D m where
  program := Fin.cons (.ret j₀) F.program
  legal := Fin.cases trivial F.legal
  oracle := F.oracle
  oracle_unitary := F.oracle_unitary
  state := F.state
  density := F.density

/-- The zeroth output distribution of the offset family is the point mass at `j₀`. -/
theorem withOffset_zero (F : Family T D m) (j₀ : Fin m) :
    (F.withOffset j₀).output 0 = PMF.pure j₀ := by
  unfold output
  have hv : (fun i => (((F.withOffset j₀).program 0).leaf (F.withOffset j₀).oracle i).value) =
      (fun _ => j₀) := by
    funext i
    simp [withOffset, Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.leaf,
        Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.leaves]
  rw [hv]
  exact PMF.map_const _ _

/-- At each successor index, the offset family's output distribution equals the corresponding
original component distribution. -/
theorem withOffset_succ (F : Family T D m) (j₀ : Fin m) (t : Fin T) :
    (F.withOffset j₀).output t.succ = F.output t := rfl

/-- For positive total integer weight within the bit capacity, the stopped sampler's real output
probability is the mixture of family probabilities with normalized weights. -/
theorem stopped_real (F : Family T D m) (w : Fin T → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) (i : Fin m) :
    (((F.stopped w b hW hb).map F.value) i).toReal =
      ∑ u, (w u : ℝ) / (weightTotal w : ℝ) * F.realOutput u i := by
  rw [F.stopped_output]
  rw [ENNReal.toReal_sum (fun u _ => ENNReal.mul_ne_top (by finiteness)
    ((F.output u).apply_ne_top i))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast, realOutput]

end Family

/-- The rational selector masses consisting of the leading offset mass `T * a` followed by the
component masses `μ`. -/
def selectorMasses (T : ℕ) (a : ℚ) (μ : Fin T → ℚ) : Fin (T+1) → ℚ :=
  Fin.cons ((T : ℚ) * a) μ

/-- The scale `a + (∑ t, μ t) / T` of the offset mixture vector. -/
noncomputable def dualScale (T : ℕ) (a : ℝ) (μ : Fin T → ℝ) : ℝ :=
  a + (∑ t, μ t) / T

/-- The vector consisting of mass `a` at `j₀` plus the family output mixture weighted by `μ` and
divided by `T`. -/
noncomputable def dualVector (F : Family T D m) (j₀ : Fin m)
    (a : ℝ) (μ : Fin T → ℝ) (i : Fin m) : ℝ :=
  (if i = j₀ then a else 0) + (∑ t, μ t * F.realOutput t i) / T

/-- A nonnegative offset and nonnegative component masses give nonnegative selector masses. -/
theorem selectorMasses_nonneg (a : ℚ) (μ : Fin T → ℚ)
    (ha : 0 ≤ a) (hμ : ∀ t, 0 ≤ μ t) : ∀ u, 0 ≤ selectorMasses T a μ u :=
  Fin.cases (mul_nonneg (Nat.cast_nonneg _) ha) hμ

/-- The real sum of the selector masses is `T * a + ∑ t, μ t`. -/
theorem selectorMasses_sum (a : ℚ) (μ : Fin T → ℚ) :
    (∑ u, (selectorMasses T a μ u : ℝ)) =
      (T : ℝ) * a + ∑ t, (μ t : ℝ) := by
  rw [Fin.sum_univ_succ]
  simp [selectorMasses]

/-- For positive `T` and `a` and nonnegative component masses, `dualScale T a μ` is strictly
positive. -/
theorem dualScale_pos (hT : 0 < T) (a : ℝ) (μ : Fin T → ℝ)
    (ha : 0 < a) (hμ : ∀ t, 0 ≤ μ t) : 0 < dualScale T a μ := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  exact add_pos_of_pos_of_nonneg ha (div_nonneg (Finset.sum_nonneg (fun t _ => hμ t)) hTr.le)

/-- For positive `T` and `a` and nonnegative component masses, the selector masses have strictly
positive real sum. -/
theorem selectorMasses_pos (hT : 0 < T) (a : ℚ) (μ : Fin T → ℚ)
    (ha : 0 < a) (hμ : ∀ t, 0 ≤ μ t) :
    0 < ∑ u, (selectorMasses T a μ u : ℝ) := by
  rw [selectorMasses_sum]
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  exact add_pos_of_pos_of_nonneg (mul_pos hTr har)
    (Finset.sum_nonneg (fun t _ => by exact_mod_cast hμ t))

/-- The entries of `dualVector` sum to `dualScale`. -/
theorem dualVector_sum (F : Family T D m) (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ) :
    (∑ i, dualVector F j₀ a μ i) = dualScale T a μ := by
  classical
  simp only [dualVector, dualScale, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j₀), ← Finset.sum_div,
    Finset.sum_comm]
  simp_rw [← Finset.mul_sum, F.realOutput_sum, mul_one]

/-- For a positive family size, positive rational offset, and nonnegative rational component
masses, the offset stopped sampler realizes `dualVector` as `dualScale` times its real
output law. The scale is positive and equals the sum of the vector entries. -/
theorem dual_actual_output (F : Family T D m) (j₀ : Fin m) (hT : 0 < T)
    (a : ℚ) (μ : Fin T → ℚ) (ha : 0 < a) (hμ : ∀ t, 0 ≤ μ t) :
    let v := selectorMasses T a μ
    let w := intWeights v
    let hW := (intWeights_normalization v (selectorMasses_nonneg a μ ha.le hμ)
      (selectorMasses_pos hT a μ ha hμ)).1
    let F' := F.withOffset j₀
    let L := dualScale T (a : ℝ) (fun t => (μ t : ℝ))
    let p := (F'.stopped w (blockWidth w) hW (blockWidth_capacity w)).map F'.value
    0 < L ∧ (∑ i, dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i) = L ∧
      ∀ i, dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i = L * (p i).toReal := by
  (try dsimp only)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hμr (t : Fin T) : (0 : ℝ) ≤ μ t := by exact_mod_cast hμ t
  have hL := dualScale_pos hT (a : ℝ) (fun t => (μ t : ℝ)) har hμr
  refine ⟨hL, dualVector_sum F j₀ _ _, ?_⟩
  intro i
  rw [Family.stopped_real]
  simp_rw [(intWeights_normalization _ (selectorMasses_nonneg a μ ha.le hμ)
    (selectorMasses_pos hT a μ ha hμ)).2]
  rw [selectorMasses_sum, Fin.sum_univ_succ]
  simp only [selectorMasses, Fin.cons_zero, Fin.cons_succ, Rat.cast_mul, Rat.cast_natCast,
    Family.realOutput, Family.withOffset_zero, PMF.pure_apply, Family.withOffset_succ]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero]
  have hden : (T : ℝ) * a + ∑ t, (μ t : ℝ) ≠ 0 :=
    ne_of_gt (by rw [← selectorMasses_sum]; exact selectorMasses_pos hT a μ ha hμ)
  have hden' : (a : ℝ) * T + ∑ t, (μ t : ℝ) ≠ 0 := by
    simpa only [mul_comm] using hden
  simp only [dualVector, dualScale, Family.realOutput]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  by_cases hi : i = j₀
  · simp only [hi, if_true, mul_one]
    field_simp [hTr.ne', hden, hden']
  · simp only [hi, if_false, mul_zero, zero_add]
    field_simp [hTr.ne', hden, hden']
    ring

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
