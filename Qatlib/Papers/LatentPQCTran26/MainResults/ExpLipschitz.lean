/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.QsvtCore.HamiltonianSim.HermitianEvolutionLipschitzGily

/-!
# Lipschitz continuity of Hermitian matrix exponentials

`exp_I_smul_lipschitz` controls the difference of two unitary exponentials by the difference of
their Hermitian generators. This perturbation estimate supplies a matrix-exponential bound for
the latent-circuit development. See [TranEtAl2026] for the paper context.

## Main statements

* `exp_I_smul_lipschitz`: For Hermitian complex matrices `A` and `B`, the norm of `exp (I • A) -
  exp (I • B)` is at most `‖A - B‖`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.LatentPQCTran26.MainResults.ExpLipschitz

/-- For Hermitian complex matrices `A` and `B`, the norm of `exp (I • A) - exp (I • B)` is at
most `‖A - B‖` [TranEtAl2026]. -/
theorem exp_I_smul_lipschitz {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ‖NormedSpace.exp (Complex.I • A) - NormedSpace.exp (Complex.I • B)‖ ≤ ‖A - B‖ := by

  have h := Qatlib.Concepts.QsvtCore.HamiltonianSim.hermitianEvolutionLipschitz_answer
    ι A B hA hB (-1)
  have hscalar : (-Complex.I * ((-1 : ℝ) : ℂ)) = Complex.I := by
    push_cast
    ring

  have hA' : HamiltonianEvolution A (-1) = NormedSpace.exp (Complex.I • A) := by
    unfold HamiltonianEvolution
    rw [hscalar]
  have hB' : HamiltonianEvolution B (-1) = NormedSpace.exp (Complex.I • B) := by
    unfold HamiltonianEvolution
    rw [hscalar]
  rw [hA', hB'] at h
  simpa using h

end Qatlib.Papers.LatentPQCTran26.MainResults.ExpLipschitz
