/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.SharedInput
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option backward.isDefEq.respectTransparency false

/-!
# Phase Law

The actual source phases are independent across sites, sampled once and retained through every supplied copy.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhaseLaw
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- The actual source phases are independent across sites, sampled once and retained through every supplied copy. -/
def uniformPhaseLaw (A : Type*) [Fintype A] [DecidableEq A] (Q : ℕ) : FinDist (A → Fin (Q+1)) where
  prob _ := ∏ _a : A,(1/(Q+1 : ℕ) : ℝ)
  nonneg _ := Finset.prod_nonneg (fun _ _ => by positivity)
  sum_one := by
    rw [←Fintype.prod_sum (fun (_a : A) (_i : Fin (Q+1)) => (1/(Q+1 : ℕ) : ℝ))]
    apply Finset.prod_eq_one
    intro a _
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_one_div_cancel (by positivity : ((Q+1 : ℕ) : ℝ)≠0)

/-- The real probability masses of the actual source phase law are exactly the coefficients of the same full shared-phase quantum prior. -/
theorem phaseMean_eq_real_law {A : Type*} [Fintype A] [DecidableEq A] (Q : ℕ) (f : (A → Fin (Q+1)) → ℂ) :
    phaseMean Q f=∑ ω,((uniformPhaseLaw A Q).prob ω : ℂ)*f ω := by
  simp only [phaseMean,uniformPhaseLaw,Complex.ofReal_prod,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_natCast]
  apply Finset.sum_congr
  · ext ω
    simp only [Finset.mem_univ]
  · intro ω _
    rfl

/-- Finite averaging over the actual normalized shared-phase law preserves a proved bound for every original phase realization. -/
theorem phase_average_le {A : Type*} [Fintype A] [DecidableEq A] (Q : ℕ) (g : (A → Fin (Q+1)) → ℝ) (B : ℝ)
    (h : ∀ ω,g ω≤B) : (∑ ω,(uniformPhaseLaw A Q).prob ω*g ω)≤B := by
  calc
    _ ≤ ∑ ω,(uniformPhaseLaw A Q).prob ω*B := Finset.sum_le_sum
      (fun ω _ => mul_le_mul_of_nonneg_left (h ω) ((uniformPhaseLaw A Q).nonneg ω))
    _ = B := by rw [←Finset.sum_mul,(uniformPhaseLaw A Q).sum_one,one_mul]

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PhaseLaw
