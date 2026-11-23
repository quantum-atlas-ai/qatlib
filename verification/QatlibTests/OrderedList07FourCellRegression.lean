module

public import Qatlib.Papers.OrderedList07.MainResults.ConcreteLearner

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.OrderedList07FourCellRegression

open Qatlib.Papers.OrderedList07.MainResults
open Qatlib.Concepts.OrderedBayes.BayesRatioCore

/-! The ordinary consumer invokes every delivered endpoint on the concrete four-cell instance. -/

example :
    stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ) =
      (⟨0, by norm_num⟩ : Fin 4) :=
  uniform_four_stage_two_cut

example :
    prefixMass (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ)) =
      (1 / 4 : ℝ) :=
  uniform_four_selected_mass

example :
    (∑ j : Fin 4,
      updateFalse (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) j) = 1 ∧
    (∑ j : Fin 4,
      updateTrue (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) j) = 1 :=
  uniform_four_posterior_normalization

example :
    updateFalse (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) =
      ![(1 / 2 : ℝ), 1 / 6, 1 / 6, 1 / 6] ∧
    updateTrue (fun _ : Fin 4 => (1 / 4 : ℝ))
        (stageTwoCut (n := 4) (by norm_num) (fun _ : Fin 4 => (1 / 4 : ℝ)) (1 / 3 : ℝ))
        (3 / 4 : ℝ) =
      ![(1 / 10 : ℝ), 3 / 10, 3 / 10, 3 / 10] :=
  uniform_four_branch_values

end QatlibTests.OrderedList07FourCellRegression
