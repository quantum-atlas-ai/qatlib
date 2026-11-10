/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
import Qatlib.Concepts.LchsSimulation.TimeLchs
import Qatlib.Foundations.OperatorErrors.OperatorError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Real.Sqrt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.HamGrover03.MainResults

private theorem min_two_le_sqrt_two_mul {x : ℝ} (hx : 0 ≤ x) :
    min 2 x ≤ Real.sqrt (2 * x) := by
  rcases le_total x 2 with h | h
  · rw [min_eq_right h]
    exact Real.le_sqrt_of_sq_le (by nlinarith [hx, h])
  · rw [min_eq_left h]
    exact Real.le_sqrt_of_sq_le (by nlinarith)

theorem lemma1_hamiltonian_difference_bound
    {I : Type} [Fintype I] [DecidableEq I]
    (H H' : ℝ → Matrix I I ℂ) (δ : ℝ → ℝ) (T : ℝ)
    (hH : Continuous H) (hH' : Continuous H')
    (hHerm : ∀ u, (H u).IsHermitian) (hHerm' : ∀ u, (H' u).IsHermitian)
    (hT : 0 ≤ T) (hδ : ∀ u, 0 ≤ δ u)
    (hδint : IntervalIntegrable δ volume 0 T)
    (hclose : ∀ u ∈ Set.Icc 0 T, ‖H u - H' u‖ ≤ δ u) :
    ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
        (fun u => Complex.I • H u) 0 T -
      Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
        (fun u => Complex.I • H' u) 0 T‖ ≤
      Real.sqrt (2 * ∫ u in 0..T, δ u) := by

  have hL : Continuous (fun u => H' u - H u) := by fun_prop
  have hLherm : ∀ u, (H' u - H u).IsHermitian := fun u => (hHerm' u).sub (hHerm u)
  have hstab :=
    Qatlib.Concepts.LchsSimulation.TimeLchs.time_dependent_lchs_same_unitary_stability
      I (fun u => H' u - H u) H 0 T 0 1 hL hH hLherm hHerm hT
  have hfun0 :
      (fun u => Complex.I • (H u + (0 : ℝ) • (H' u - H u))) = fun u => Complex.I • H u := by
    funext u; simp
  have hfun1 :
      (fun u => Complex.I • (H u + (1 : ℝ) • (H' u - H u))) = fun u => Complex.I • H' u := by
    funext u
    simp only [one_smul]
    congr 1
    abel
  rw [hfun0, hfun1, abs_of_neg (by norm_num : (0 : ℝ) - 1 < 0)] at hstab
  norm_num at hstab

  have hmono :
      (∫ u in 0..T, ‖H' u - H u‖) ≤ ∫ u in 0..T, δ u := by
    apply intervalIntegral.integral_mono_on hT
      (hL.norm.intervalIntegrable 0 T) hδint
    intro u hu
    rw [norm_sub_rev]
    exact hclose u hu
  have hduhamel :
      ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
          (fun u => Complex.I • H u) 0 T -
        Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
          (fun u => Complex.I • H' u) 0 T‖ ≤
        ∫ u in 0..T, δ u :=
    hstab.trans hmono

  have hunit :=
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
      I H hH hHerm 0 T
  have hunit' :=
    Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.ordered_evolution_hermitian_unitary
      I H' hH' hHerm' 0 T
  have htwo :
      ‖Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
          (fun u => Complex.I • H u) 0 T -
        Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
          (fun u => Complex.I • H' u) 0 T‖ ≤ 2 := by
    have hsub := norm_sub_le
      (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
        (fun u => Complex.I • H u) 0 T)
      (Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution.orderedEvolution
        (fun u => Complex.I • H' u) 0 T)
    have h1 :=
      Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hunit
    have h2 :=
      Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_unitary_le_one hunit'
    linarith
  have hx : 0 ≤ ∫ u in 0..T, δ u :=
    intervalIntegral.integral_nonneg hT (fun u _ => hδ u)
  exact (le_min htwo hduhamel).trans (min_two_le_sqrt_two_mul hx)

end Qatlib.Papers.HamGrover03.MainResults
