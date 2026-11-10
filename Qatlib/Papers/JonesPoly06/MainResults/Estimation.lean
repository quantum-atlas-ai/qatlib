/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly06.MainResults.SamplingSigns
import Qatlib.Papers.JonesPoly06.MainResults.ChernoffConcentration
import Qatlib.Papers.JonesPoly06.MainResults.HadamardTest
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

namespace Qatlib.Papers.JonesPoly06.MainResults

def signIndicator : Fin 4 → ℝ := fun i => (signX i + 1) / 2

theorem signIndicator_mem (i : Fin 4) : signIndicator i ∈ Set.Icc (0 : ℝ) 1 := by
  have h := signX_val i
  unfold signIndicator
  constructor <;> rcases h with h | h <;> rw [h] <;> norm_num

theorem expect_signIndicator (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1) :
    (signLaw z hz).expect signIndicator = (z.re + 1) / 2 := by
  unfold signIndicator
  simp only [FinDist.expect, signLaw, Fin.sum_univ_four, signX, signY]
  ring

theorem signLaw_prob_eq_bornMass (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1)
    (i : Fin 4) :
    (signLaw z hz).prob i = bornMass z (signX i) (signY i) := by
  simp only [signLaw, bornMass, signX, signY]
  fin_cases i <;> norm_num <;> ring

theorem Theorem21_sampling (z : ℂ) (hz : z.re ^ 2 + z.im ^ 2 ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (M : ℕ) (hM : 0 < M)
    (hcount : 8 * Real.log 16 / δ ^ 2 ≤ (M : ℝ)) :
    eventMass (independent (fun _ : Fin M => signLaw z hz))
      (fun ω => δ ≤ |weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹)
          (fun (_ : Fin M) (i : Fin 4) => signIndicator i) ω - (z.re + 1) / 2|)
      ≤ 1 / 4 := by
  classical
  have hbase := SourceLemma62 M hM (fun _ : Fin M => signLaw z hz) signIndicator
    (fun i => signIndicator_mem i) δ hδ
  have hexp : (independent (fun _ : Fin M => signLaw z hz)).expect
      (weightedSum (fun _ : Fin M => ((M : ℝ))⁻¹)
        (fun (_ : Fin M) (i : Fin 4) => signIndicator i))
      = (z.re + 1) / 2 := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    have hconst : ∀ i : Fin M,
        ((M : ℝ))⁻¹ * (signLaw z hz).expect signIndicator
          = ((M : ℝ))⁻¹ * ((z.re + 1) / 2) := by
      intro i
      rw [expect_signIndicator]
    refine (Finset.sum_congr rfl (fun i _ => hconst i)).trans ?_
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hexp] at hbase
  refine hbase.trans ?_
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hkey : 2 * Real.log 16 ≤ (M : ℝ) * δ ^ 2 / 4 := by
    have h2 : 8 * Real.log 16 ≤ (M : ℝ) * δ ^ 2 := by
      rw [div_le_iff₀ hδ2] at hcount
      linarith
    linarith
  have hE : -(M : ℝ) * δ ^ 2 / 4 ≤ -(2 * Real.log 16) := by
    nlinarith [hkey]
  have he1 : Real.exp (-(M : ℝ) * δ ^ 2 / 4) ≤ Real.exp (-(2 * Real.log 16)) :=
    Real.exp_le_exp.mpr hE
  have hlog : Real.exp (-(2 * Real.log 16)) = (1 / 256 : ℝ) := by
    have h2l : (2 : ℝ) * Real.log 16 = Real.log 256 := by
      have h := Real.log_pow (16 : ℝ) 2
      norm_num at h
      linarith
    rw [h2l, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 256)]
    norm_num
  nlinarith [he1, hlog]

end Qatlib.Papers.JonesPoly06.MainResults
