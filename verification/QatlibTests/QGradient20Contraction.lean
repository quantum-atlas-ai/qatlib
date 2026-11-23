module

import Qatlib.Papers.QGradient20.FilterBranch.Contraction

open Matrix
open Qatlib.Papers.QGradient20.FilterBranch
open Qatlib.Papers.QGradient20.FilterBranch

namespace QatlibTests.QGradient20Contraction

noncomputable section

def concreteMatrix : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i = j then 1 else 0

def concreteInput : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 2]

def concreteTarget : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![-1, 1]

theorem concrete_inputs_are_distinct : concreteInput ≠ concreteTarget := by
  intro h
  have h0 := congrArg (fun v => v (0 : Fin 2)) h
  norm_num [concreteInput, concreteTarget] at h0

example : ‖successfulAction (I := Fin 2) (0 : Fin 2) concreteMatrix (1 / 3) true‖ ≤ 1 := by
  exact successfulAction_opNorm_le_one (I := Fin 2) (0 : Fin 2) concreteMatrix
    (ξ := 1 / 3) (by norm_num) true

example :
    ‖successfulVector (0 : Fin 2) concreteMatrix (1 / 3) true concreteInput -
      successfulVector (0 : Fin 2) concreteMatrix (1 / 3) true concreteTarget‖ ≤
        ‖concreteInput - concreteTarget‖ := by
  exact successfulAction_lipschitz (I := Fin 2) (0 : Fin 2) concreteMatrix
    (ξ := 1 / 3) (by norm_num) true concreteInput concreteTarget

end

end QatlibTests.QGradient20Contraction
