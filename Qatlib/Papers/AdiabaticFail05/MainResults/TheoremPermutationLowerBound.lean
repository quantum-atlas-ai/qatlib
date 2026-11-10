/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticFail05.MainResults

open scoped BigOperators
open Finset

theorem theorem2_permutation_lower_bound
    (N ε b hstar T Fct Sum : ℝ)
    (_hN : 1 < N) (_hε0 : 0 < ε) (_hε1 : ε ≤ 1) (_hb : 0 ≤ b)
    (hh : 0 < hstar) (hFct : 0 < Fct) (_hT : 0 ≤ T)
    (hL1 : Sum ≤ 4 * hstar * T * Fct * Real.sqrt (N - 1))
    (hL2 : (ε * Fct / 2) * (b * (ε / 2) * (N - 1) - 2 * Real.sqrt ((ε / 2) * (N - 1))) ≤ Sum) :
    (ε ^ 2 * b / (16 * hstar)) * Real.sqrt (N - 1) - ε * Real.sqrt (ε / 2) / (4 * hstar) ≤ T := by
  have hN1 : 0 < N - 1 := by linarith
  have hs : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.2 hN1
  have hsq1 : Real.sqrt (N - 1) * Real.sqrt (N - 1) = N - 1 := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hN1)
  have hsq2 : Real.sqrt ((ε / 2) * (N - 1)) = Real.sqrt (ε / 2) * Real.sqrt (N - 1) :=
    Real.sqrt_mul (le_of_lt (by positivity : (0 : ℝ) < ε / 2)) (N - 1)

  have hcomb : (ε * Fct / 2) * (b * (ε / 2) * (N - 1) - 2 * Real.sqrt ((ε / 2) * (N - 1)))
      ≤ 4 * hstar * T * Fct * Real.sqrt (N - 1) := by
    linarith [hL1, hL2]
  rw [hsq2] at hcomb

  have hpos : 0 < Fct * Real.sqrt (N - 1) / 4 := div_pos (mul_pos hFct hs) (by norm_num)
  have hmul_eq : (Fct * Real.sqrt (N - 1) / 4)
        * (ε ^ 2 * b * Real.sqrt (N - 1) - 4 * ε * Real.sqrt (ε / 2))
      = (ε * Fct / 2) * (b * (ε / 2) * (N - 1) - 2 * (Real.sqrt (ε / 2) * Real.sqrt (N - 1))) := by
    linear_combination (ε ^ 2 * b * Fct / 4) * hsq1
  have hG : (Fct * Real.sqrt (N - 1) / 4)
        * (ε ^ 2 * b * Real.sqrt (N - 1) - 4 * ε * Real.sqrt (ε / 2))
      ≤ (Fct * Real.sqrt (N - 1) / 4) * (16 * hstar * T) := by
    rw [hmul_eq]
    have hrhs : (Fct * Real.sqrt (N - 1) / 4) * (16 * hstar * T)
        = 4 * hstar * T * Fct * Real.sqrt (N - 1) := by ring
    rw [hrhs]
    exact hcomb

  have hred : ε ^ 2 * b * Real.sqrt (N - 1) - 4 * ε * Real.sqrt (ε / 2) ≤ 16 * hstar * T :=
    le_of_mul_le_mul_left hG hpos

  have hRHS : (ε ^ 2 * b / (16 * hstar)) * Real.sqrt (N - 1) - ε * Real.sqrt (ε / 2) / (4 * hstar)
      = (ε ^ 2 * b * Real.sqrt (N - 1) - 4 * ε * Real.sqrt (ε / 2)) / (16 * hstar) := by
    field_simp [ne_of_gt hh]
    ring
  rw [hRHS]
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hh)]
  nlinarith [hred]

theorem counting_good_sets
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (X ε Fc : ℝ)
    (_hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ X)
    (hX : 0 < X) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (_hFc : 0 ≤ Fc)
    (hcard : (Fintype.card ι : ℝ) = Fc)
    (hsum : (∑ i, g i) = ε * Fc * X) :
    ε / 2 * Fc ≤ ((Finset.univ.filter (fun i => ε / 2 * X ≤ g i)).card : ℝ) := by
  classical
  set M : ℝ := ((Finset.univ.filter (fun i : ι => ε / 2 * X ≤ g i)).card : ℝ) with hMdef

  have hpart := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset ι))
    (p := fun i => ε / 2 * X ≤ g i) (f := g)
  have hgood_le :
      ∑ i ∈ Finset.univ.filter (fun i : ι => ε / 2 * X ≤ g i), g i ≤ M * X := by
    calc ∑ i ∈ Finset.univ.filter (fun i : ι => ε / 2 * X ≤ g i), g i
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : ι => ε / 2 * X ≤ g i), X :=
          Finset.sum_le_sum fun i _ => hg1 i
      _ = M * X := by
          rw [Finset.sum_const, nsmul_eq_mul, hMdef]
  have hbad_le :
      ∑ i ∈ Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i)), g i
        ≤ ((Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i))).card : ℝ) * (ε / 2 * X) := by
    have hb : ∀ i ∈ Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i)), g i ≤ ε / 2 * X := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact le_of_lt (lt_of_not_ge hi)
    calc ∑ i ∈ Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i)), g i
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i)), (ε / 2 * X) :=
          Finset.sum_le_sum hb
      _ = ((Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i))).card : ℝ) * (ε / 2 * X) := by
          rw [Finset.sum_const, nsmul_eq_mul]

  have hcard_split :
      ((Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i))).card : ℝ) = Fc - M := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (p := fun i => ε / 2 * X ≤ g i)
    have h' : ((Finset.univ.filter (fun i : ι => ε / 2 * X ≤ g i)).card
        + (Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i))).card : ℕ)
        = Fintype.card ι := by
      simpa using h
    have hcast : ((Finset.univ.filter (fun i : ι => ε / 2 * X ≤ g i)).card : ℝ)
        + ((Finset.univ.filter (fun i : ι => ¬ (ε / 2 * X ≤ g i))).card : ℝ) = Fc := by
      rw [← Nat.cast_add, h', hcard]
    rw [hMdef]
    linarith

  have hkey : ε * Fc * X ≤ M * X + (Fc - M) * (ε / 2 * X) := by
    rw [← hsum, ← hpart]
    have := add_le_add hgood_le hbad_le
    rwa [hcard_split] at this

  have hdiv : ε * Fc ≤ M + (Fc - M) * (ε / 2) := by
    have hrhs : M * X + (Fc - M) * (ε / 2 * X) = (M + (Fc - M) * (ε / 2)) * X := by ring
    rw [hrhs] at hkey
    exact le_of_mul_le_mul_right hkey hX
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity

  have hε2 : 0 ≤ 1 - ε / 2 := by linarith
  nlinarith [hdiv, hMnn, hε0, hε1, _hFc, hε2]

end Qatlib.Papers.AdiabaticFail05.MainResults
