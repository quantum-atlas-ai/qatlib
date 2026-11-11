/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomWindowSuccessAndBudgetStat
import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousPreparedSolutionLine

/-!
# Success and word budgets for inhomogeneous LCHS

`inhomogeneousWindowSuccessAndBudget` proves a success-probability and query-word bound for the
compiled inhomogeneous LCHS window. Given a unified approximation within ε of a solution of norm
at least τ and `ε ≤ τ/2`, it proves normalized iteration weights, average marked success at
least 1/8, and separate input and selection word-count bounds of `2*m + 1`. This gives a
concrete finite-grid preparation estimate related to [AnLiuLin2023].

## Main statements

* `inhomogeneousWindowSuccessAndBudget`: the window distribution, success, and word-count
  guarantees.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

/-- Proves `InhomogeneousWindowSuccessAndBudget`: the finite window has normalized weights,
length at most `2*α/τ + 1`, average marked success at least 1/8, and input and selection
word counts each at most `2*m + 1`; see [AnLiuLin2023]. -/
theorem inhomogeneousWindowSuccessAndBudget : InhomogeneousWindowSuccessAndBudget := by
  intro I _ _ L H b s t ε τ K N Mt B P i₀ hL hH hPSD hHerm hst hB hP
    _hprep hK hN _hMt _hε hτ hετ
  (try dsimp only)
  intro hτx he
  let c := inhUnifiedCoeff b s t K N Mt
  let V := inhUnifiedUnitary L H s t K N Mt B P
  let x := orderedForcedSolution (fun u => L u+Complex.I • H u) b s (B *ᵥ Ket i₀) t
  let y := (∑ j, c j • V j) *ᵥ (B *ᵥ Ket i₀)
  have hα := inh_unified_mass_pos b s t K N Mt hst hK hN
  have hV := inh_unified_unitary L H s t K N Mt B P hL hH hPSD hHerm hB hP
  have hm := static_lchs_window_bound (coefficientMass c) τ hα hτ
  refine ⟨(static_lchs_iteration_weight_distribution _ hm.1).2, hm.2, ?_⟩
  intro j₀
  constructor
  · have hnorm : τ/2 ≤ ‖toEuclidean_fromVec y‖ := by
      have hh := abs_norm_sub_norm_le (toEuclidean_fromVec x) (toEuclidean_fromVec y)
      have hdiff : ‖toEuclidean_fromVec x - toEuclidean_fromVec y‖ ≤ ε := by
        rw [norm_sub_rev]
        simpa only [toEuclidean_fromVec, WithLp.toLp_sub] using! he
      have hh' := (le_abs_self _).trans (hh.trans hdiff)
      linarith
    apply static_lchs_window_success_of_initial_mass I (N+N*Mt) c V B j₀ i₀ τ hα hV hB hτ
    rw [static_lchs_label_probability]
    have heq : MeasureProb (staticLchsDataBranch j₀
        (Run (preparedMark (Finset.univ.filter (fun z : Fin (N+N*Mt) × I => z.1 = j₀)))
          (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀,i₀)))) Finset.univ =
        ‖toEuclidean_fromVec (staticLchsDataBranch j₀
          (Run (preparedMark (Finset.univ.filter (fun z : Fin (N+N*Mt) × I => z.1 = j₀)))
            (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀,i₀))))‖^2 := by
      rw [norm_toEuclidean_fromVec_sq]; rfl
    rw [heq, Real.sqrt_sq (norm_nonneg _),
      static_lchs_initial_data_branch_raw I (N+N*Mt) c V B j₀ i₀ hα hV hB]
    simp only [toEuclidean_fromVec, WithLp.toLp_smul, norm_smul, norm_inv,
      Complex.norm_real]
    rw [Real.norm_of_nonneg hα.le]
    change τ/(2*coefficientMass c) ≤ (coefficientMass c)⁻¹ * ‖toEuclidean_fromVec y‖
    calc
      τ/(2*coefficientMass c) = (τ/2)/(coefficientMass c) := by ring
      _ ≤ ‖toEuclidean_fromVec y‖ / coefficientMass c := div_le_div_of_nonneg_right hnorm hα.le
      _ = _ := by ring
  · intro j
    exact static_lchs_window_actual_access_budget I (N+N*Mt) c V B j₀ i₀ hα hV hB _ j

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
