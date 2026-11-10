/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalStopComparisonStat
import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayQuan
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.ProjectorCS
namespace Qatlib.Concepts.WalkSearch.ClassicalStop

open Matrix
open scoped Classical BigOperators

private theorem absorbingLaw_zero {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) :
    absorbingLaw P S 0 = fun _ => 1 / (Fintype.card I : ℝ) := by simp [absorbingLaw]

private theorem absorbingLaw_succ {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (K : ℕ) :
    absorbingLaw P S (K + 1) = stepAbsorbingLaw P S (absorbingLaw P S K) := by
  exact Function.iterate_succ_apply' _ _ _

private theorem empty_detection {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (hrow : ∀ i, (∑ j, P i j) = 1) (hsym : ∀ i j, P i j = P j i) (K : ℕ) :
    classicalDetectSuccess P ∅ K = 0 := by
  have hfix : stepAbsorbingLaw P ∅ (fun _ => 1 / (Fintype.card I : ℝ)) =
      fun _ => 1 / (Fintype.card I : ℝ) := by
    funext j
    simp only [stepAbsorbingLaw, absorbingKernel, Finset.notMem_empty, if_false,
      ← Finset.mul_sum]
    have hcol : (∑ i, P i j) = 1 := by simp only [hsym]; exact hrow j
    rw [hcol, mul_one]
  have hlaw : absorbingLaw P ∅ K = fun _ => 1 / (Fintype.card I : ℝ) := by
    induction K with
    | zero => exact absorbingLaw_zero P ∅
    | succ K ih => rw [absorbingLaw_succ, ih]; exact hfix
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hcard : Fintype.card (Unmarked I (∅ : Finset I)) = Fintype.card I := by
    simp [Unmarked]
  unfold classicalDetectSuccess
  rw [hlaw]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  field_simp [hn]
  ring

theorem szegedyClassicalStopComparison : SzegedyClassicalStopComparison := by
  intro I _ _ _ P S δ ε hδ hδ1 hP hε hεp
  constructor
  · intro hS K
    subst S
    exact empty_detection P hP.1.2 hP.2.1 K
  · intro K hK
    have hp := markedFraction_mem_Icc S
    have hε1 : ε ≤ 1 := hεp.trans hp.2
    have hδε : 0 < δ * ε := mul_pos hδ hε
    have hδε1 : δ * ε ≤ 1 := by nlinarith
    have hbase : 0 ≤ 1 - δ * ε / 2 := by linarith
    have hmass := szegedyClassicalAbsorbingMassDecay I P S δ ε K hδ hδ1 hP hε hεp
      (absorbingLaw P S) (absorbingLaw_zero P S)
      (fun t j => by rw [absorbingLaw_succ]; rfl)
    have he : (1 - δ * ε / 2) ^ K ≤ Real.exp (-(δ * ε / 2) * K) := by
      have hb : 1 - δ * ε / 2 ≤ Real.exp (-(δ * ε / 2)) := by
        simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(δ * ε / 2))
      have h := pow_le_pow_left₀ hbase hb K
      rw [← Real.exp_nat_mul] at h
      simpa only [mul_comm] using h
    have hscaled : 500 ≤ δ * ε / 2 * K := by
      have hh := (div_le_iff₀ hδε).mp hK
      nlinarith
    have hexp : Real.exp (-(δ * ε / 2) * K) ≤ Real.exp (-500) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hsmall : Real.exp (-500) ≤ (31 / 32 : ℝ) := by
      rw [Real.exp_neg, ← one_div]
      apply (div_le_iff₀ (Real.exp_pos 500)).mpr
      nlinarith [Real.add_one_le_exp (500 : ℝ)]
    have hbound := hmass.trans (he.trans (hexp.trans hsmall))
    unfold classicalDetectSuccess
    linarith

end Qatlib.Concepts.WalkSearch.ClassicalStop
