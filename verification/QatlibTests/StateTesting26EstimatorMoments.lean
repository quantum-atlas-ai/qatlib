module

import Qatlib.Papers.StateTesting26.MainResults.Moments.EstimatorMoments

open Qatlib.Papers.StateTesting26.MainResults.Model
open Qatlib.Papers.StateTesting26.MainResults.Moments
open scoped Kronecker

noncomputable section

example (τA : Matrix (Fin 2) (Fin 2) ℂ) :
    reducedEstimatorMoment τA (tensorPowerMat τA 2) 3 4 =
      conditionalSecondMoment τA (tensorPowerMat τA 2) 3 4 :=
  reducedEstimatorMoment_eq_conditionalSecondMoment _ _ _ _

example :
    (swapTwo (d := 2) ⊗ₖ swapTwo (d := 3)).traceRight = (3 : ℂ) • swapTwo (d := 2) :=
  traceRight_swapTwo_kronecker_swapTwo 2 3
