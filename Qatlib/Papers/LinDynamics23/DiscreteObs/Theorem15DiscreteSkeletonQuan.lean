/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.Theorem15DiscreteSkeletonStat
import Qatlib.Papers.LinDynamics23.DiscreteObs.Theorem15DiscreteSkeletonCounterex
import Qatlib.Papers.LinDynamics23.DiscreteObs.DiscreteLchsCost

/-!
# Proof of the discrete LCHS skeleton

`sqrt_label_mass` identifies the square root of a selected-label probability with the Euclidean
norm of its data branch. The theorem `theorem15DiscreteSkeleton` proves the corrected discrete
contract, including normalized output error, compilation counts, and randomized amplification
success under the contract's reconstruction-closeness hypothesis. See [AnChildsLin2026] for the
paper context.

## Main statements

* `sqrt_label_mass`: The square root of the probability mass on a fixed label equals the
  Euclidean norm of the corresponding data branch.
* `theorem15DiscreteSkeleton`: The corrected discrete LCHS skeleton contract holds, including
  output trace-norm error, compilation identities, and the stated amplification-window success
  bound.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The square root of the probability mass on a fixed label equals the Euclidean norm of the
corresponding data branch. -/
private theorem sqrt_label_mass {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
    (j₀ : Fin N) (y : QState (Fin N × I)) :
    Real.sqrt (MeasureProb y (Finset.univ.filter (fun x : Fin N × I => x.1 = j₀))) =
      ‖toEuclidean_fromVec (staticLchsDataBranch j₀ y)‖ := by
  rw [static_lchs_label_probability]
  have he : MeasureProb (staticLchsDataBranch j₀ y) Finset.univ =
      ‖toEuclidean_fromVec (staticLchsDataBranch j₀ y)‖^2 := by
    rw [norm_toEuclidean_fromVec_sq]
    rfl
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- The corrected discrete LCHS skeleton contract holds, including output trace-norm error,
compilation identities, and the stated amplification-window success bound [An et al.,
Theorem 15][AnChildsLin2026]. -/
theorem theorem15DiscreteSkeleton : Theorem15DiscreteSkeleton := by
  intro I _ _ N c V B i₀ E ε hV hB hα _hε
  (try dsimp only)
  intro hτ η hbudget hgap hclose
  let x₀ := B.mulVec (Ket i₀)
  let v := E.mulVec x₀
  let w := (∑ j, c j • V j).mulVec x₀
  let τ := ‖toEuclidean_fromVec v‖
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hclose
  have hcap : τ * min ε 1 ≤ τ := by
    simpa only [mul_one] using! mul_le_mul_of_nonneg_left (min_le_right ε 1) hτ.le
  have hhalf : η ≤ τ / 2 := by
    change η ≤ τ * min ε 1 / 8 at hbudget
    linarith
  have hvec : ‖toEuclidean_fromVec (w - v)‖ ≤ η := by
    simpa only [toEuclidean_fromVec, WithLp.toLp_sub] using! hclose
  have herr : (staticLchsOutputDensity w - staticLchsOutputDensity v).traceNorm ≤
      4 * η / τ := by
    by_cases hz : η = 0
    · have he : toEuclidean_fromVec w = toEuclidean_fromVec v :=
        sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [hz] using! hclose)
          (norm_nonneg _)))
      have hwv : w = v := by
        apply_fun WithLp.ofLp at he
        exact he
      rw [hwv, sub_self]
      simp [hz]
    · exact (static_lchs_output_density_error_of_vector_error v w η τ
        (lt_of_le_of_ne hη0 (Ne.symm hz)) hτ hhalf le_rfl hvec).2
  refine ⟨?_, ?_, ?_⟩
  · intro j₀
    intro _hp
    rw [static_lchs_initial_data_branch_raw I N c V B j₀ i₀ hα hV hB,
      static_lchs_output_density_smul _ _
        (inv_ne_zero (by exact_mod_cast hα.ne'))]
    exact herr
  · intro j₀ k
    obtain ⟨hC, _, _, _, _, _, _, _, hquery, hlen⟩ :=
      static_lchs_actual_expanded_prepare_select_amplification I N c V B j₀ i₀ k hα hV hB
    exact ⟨hC, hquery, hlen⟩
  · intro j₀
    have hm := static_lchs_window_bound (coefficientMass c) τ hα hτ
    refine ⟨hm.1, hm.2, ?_⟩
    apply static_lchs_window_success_of_initial_mass I N c V B j₀ i₀ τ hα hV hB hτ
    rw [sqrt_label_mass]
    have hg := general_discrete_lchs_actual_prepared_output I N c V B i₀ j₀ E η
      hα hV hB hclose hgap
    have hsquare := hg.2.2.2.1
    have hnonneg : 0 ≤ (τ - η) / coefficientMass c := by positivity
    have hnorm : (τ - η) / coefficientMass c ≤
        ‖toEuclidean_fromVec (staticLchsDataBranch j₀
          (Run (preparedMark (Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)))
            (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀, i₀))))‖ := by
      dsimp [τ, v, x₀] at *
      nlinarith [norm_nonneg (toEuclidean_fromVec (staticLchsDataBranch j₀
        (Run (preparedMark (Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)))
          (staticLchsCompile c V B j₀ i₀ 0) (Ket (j₀, i₀)))))]
    refine le_trans ?_ hnorm
    calc
      τ / (2 * coefficientMass c) = (τ / 2) / coefficientMass c := by ring
      _ ≤ (τ - η) / coefficientMass c :=
        div_le_div_of_nonneg_right (by linarith) hα.le

end Qatlib.Papers.LinDynamics23.DiscreteObs
