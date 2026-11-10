/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.Defs
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Matrix

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

namespace Qatlib.Papers.SpinModels08.MainResults.HadamardTest

open Qatlib.Papers.SpinModels08.MainResults

def signOutcome (x : Fin 2) : ℝ := if x = 0 then 1 else -1

def hadamardLaw (μ : ℝ) (hμ : |μ| ≤ 1) : FinDist (Fin 2) where
  prob x := if x = 0 then (1 + μ) / 2 else (1 - μ) / 2
  nonneg x := by
    rw [abs_le] at hμ
    obtain ⟨hlo, hhi⟩ := hμ
    show 0 ≤ (if x = 0 then (1 + μ) / 2 else (1 - μ) / 2)
    by_cases h : x = 0
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  sum_one := by
    show (∑ x : Fin 2, if x = 0 then (1 + μ) / 2 else (1 - μ) / 2) = 1
    rw [Fin.sum_univ_two]
    have h1 : ¬((1 : Fin 2) = 0) := by decide
    rw [if_pos rfl, if_neg h1]
    ring

theorem hadamardLaw_prob_zero (μ : ℝ) (hμ : |μ| ≤ 1) :
    (hadamardLaw μ hμ).prob 0 = (1 + μ) / 2 := by
  show (if (0 : Fin 2) = 0 then (1 + μ) / 2 else (1 - μ) / 2) = (1 + μ) / 2
  exact if_pos rfl

theorem hadamardLaw_prob_one (μ : ℝ) (hμ : |μ| ≤ 1) :
    (hadamardLaw μ hμ).prob 1 = (1 - μ) / 2 := by
  show (if (1 : Fin 2) = 0 then (1 + μ) / 2 else (1 - μ) / 2) = (1 - μ) / 2
  exact if_neg (by decide)

theorem signOutcome_zero : signOutcome 0 = 1 := if_pos rfl

theorem signOutcome_one : signOutcome 1 = -1 := by
  show (if (1 : Fin 2) = 0 then (1 : ℝ) else -1) = -1
  exact if_neg (by decide)

theorem expect_hadamardLaw (μ : ℝ) (hμ : |μ| ≤ 1) :
    (hadamardLaw μ hμ).expect signOutcome = μ := by
  show (∑ x : Fin 2, (if x = 0 then (1 + μ) / 2 else (1 - μ) / 2) * signOutcome x) = μ
  rw [Fin.sum_univ_two, if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0)),
    signOutcome_zero, signOutcome_one]
  ring

theorem weightedSum_eq_avg {K : ℕ} (ω : Fin K → Fin 2) :
    weightedSum (fun _ : Fin K => (1 : ℝ) / K) (fun _ => signOutcome) ω
      = FinDist.avg signOutcome ω := by
  unfold weightedSum FinDist.avg
  rw [← Finset.mul_sum]
  ring

theorem hadamard_hoeffding {K : ℕ} (hK : 0 < K) (μ : ℝ) (hμ : |μ| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    eventMass (independent (fun _ : Fin K => hadamardLaw μ hμ))
        (fun ω => ε ≤ |weightedSum (fun _ : Fin K => (1 : ℝ) / K)
          (fun _ => signOutcome) ω - μ|) ≤
      2 * Real.exp (-(K : ℝ) * ε ^ 2 / 2) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hSval : (∑ i : Fin K, ((1 : ℝ) / K) ^ 2 * ((1 : ℝ) - (-1)) ^ 2)
      = (4 : ℝ) / (K : ℝ) := by
    calc (∑ i : Fin K, ((1 : ℝ) / K) ^ 2 * ((1 : ℝ) - (-1)) ^ 2)
        = ∑ _i : Fin K, (4 : ℝ) / (K : ℝ) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = (K : ℝ) * ((4 : ℝ) / (K : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (4 : ℝ) / (K : ℝ) := by
          field_simp
  have hSpos : 0 < ∑ i : Fin K, ((1 : ℝ) / K) ^ 2 * ((1 : ℝ) - (-1)) ^ 2 := by
    rw [hSval]
    positivity
  have hmain := Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_hoeffding
    (p := fun _ : Fin K => hadamardLaw μ hμ)
    (w := fun _ : Fin K => (1 : ℝ) / K)
    (f := fun _ => signOutcome)
    (a := fun _ : Fin K => -1) (b := fun _ : Fin K => 1) (u := ε)
    (fun _ => by norm_num) (fun i x => by
      fin_cases x <;> simp [signOutcome]) hε hSpos
  have hmean : (independent (fun _ : Fin K => hadamardLaw μ hμ)).expect
      (weightedSum (fun _ : Fin K => (1 : ℝ) / K) (fun _ => signOutcome)) = μ := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    trans ∑ _i : Fin K, (1 : ℝ) / K * μ
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (hadamardLaw μ hμ).expect ((fun _ => signOutcome) i) = μ from
        expect_hadamardLaw μ hμ]
    · rw [show (∑ _i : Fin K, (1 : ℝ) / K * μ) = (K : ℝ) * ((1 : ℝ) / K * μ) from by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
      field_simp
  calc eventMass (independent (fun _ : Fin K => hadamardLaw μ hμ))
        (fun ω => ε ≤ |weightedSum (fun _ : Fin K => (1 : ℝ) / K)
          (fun _ => signOutcome) ω - μ|)
      = eventMass (independent (fun _ : Fin K => hadamardLaw μ hμ))
          (fun ω => ε ≤ |weightedSum (fun _ : Fin K => (1 : ℝ) / K)
            (fun _ => signOutcome) ω
              - (independent (fun _ : Fin K => hadamardLaw μ hμ)).expect
                  (weightedSum (fun _ : Fin K => (1 : ℝ) / K)
                    (fun _ => signOutcome))|) := by
        rw [hmean]
    _ ≤ 2 * Real.exp (-2 * ε ^ 2 /
          (∑ i : Fin K, ((1 : ℝ) / K) ^ 2 * ((1 : ℝ) - (-1)) ^ 2)) := hmain
    _ = 2 * Real.exp (-(K : ℝ) * ε ^ 2 / 2) := by
        rw [hSval]
        congr 1
        field_simp [hKne]
        ring

theorem eq5_statistical_tail_bound {N K : ℕ} (hK : 0 < K)
    (μ : ℝ) (hμ : |μ| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hKeps : 2 * (N : ℝ) ≤ (K : ℝ) * ε ^ 2) :
    1 - 2 * Real.exp (-(N : ℝ)) ≤
      1 - eventMass (independent (fun _ : Fin K => hadamardLaw μ hμ))
        (fun ω => ε ≤ |weightedSum (fun _ : Fin K => (1 : ℝ) / K)
          (fun _ => signOutcome) ω - μ|) := by
  have hb := hadamard_hoeffding hK μ hμ ε hε
  have hexpmono : Real.exp (-(K : ℝ) * ε ^ 2 / 2) ≤ Real.exp (-(N : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hKeps]
  have h2 : 2 * Real.exp (-(K : ℝ) * ε ^ 2 / 2) ≤ 2 * Real.exp (-(N : ℝ)) :=
    mul_le_mul_of_nonneg_left hexpmono (by norm_num)
  linarith

end Qatlib.Papers.SpinModels08.MainResults.HadamardTest
