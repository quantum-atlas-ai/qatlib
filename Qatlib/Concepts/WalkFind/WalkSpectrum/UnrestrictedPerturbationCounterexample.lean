/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.UnrestrictedPerturbationCounterexample
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NormNum

/-!
# Counterexample to unrestricted spectral perturbation

`unrestrictedPerturbationCounterexample_answer` verifies the counterexample encoded by
`UnrestrictedPerturbationCounterexample`. It computes characteristic polynomials and squared
Frobenius distance for a nilpotent two-by-two matrix and the coordinate-swap matrix, then
verifies failure of the specified matching bound.

This example explains the role of the normality hypothesis in squared eigenvalue matching
estimates. See [Bhatia1997] for the mathematical background.

## Main statements

* `unrestrictedPerturbationCounterexample_answer`: the explicit two-by-two counterexample.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix

/-- Verifies the characteristic polynomials, squared Frobenius distance, and failure of the
eigenvalue matching inequality for the explicit two-by-two matrices in
`UnrestrictedPerturbationCounterexample`. -/
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
