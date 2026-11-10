/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.UnrestrictedPerturbationCounterexample
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NormNum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix

theorem unrestrictedPerturbationCounterexample_answer :
    UnrestrictedPerturbationCounterexample := by
  change ( (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ).charpoly = Polynomial.X^2) ∧
    ((!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℂ).charpoly = Polynomial.X^2-1) ∧
    frobeniusSq ((!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℂ)-!![0,1;1,0]) = 1 ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.charpoly_fin_two]
  · simp [Matrix.charpoly_fin_two, sub_eq_add_neg]
  · norm_num [frobeniusSq, Fin.sum_univ_two]
  · intro σ
    norm_num [frobeniusSq, Fin.sum_univ_two]
    split_ifs <;> norm_num

end Qatlib.Concepts.WalkFind.WalkSpectrum
