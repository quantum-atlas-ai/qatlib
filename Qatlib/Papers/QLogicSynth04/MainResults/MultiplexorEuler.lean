/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLogicSynth04.MainResults.QubitRotations

/-!
# Euler decomposition of unitary multiplexors

`theorem6_zyz_multiplexor` applies a Z-Y-Z Euler decomposition separately to each unitary qubit
block. The resulting multiplexor is a product of three rotation multiplexors and a blockwise
scalar phase. See [ShendeBullockMarkov2006] for the paper's setting.

## Main statements

* `theorem6_zyz_multiplexor`: Every finite family of unitary qubit matrices has a blockwise
  Z-Y-Z Euler factorization, followed by a blockwise scalar phase.

## References

* [Shende et al., 2006][ShendeBullockMarkov2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix
open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLogicSynth04.MainResults

/-- Every finite family of unitary qubit matrices has a blockwise Z-Y-Z Euler factorization,
followed by a blockwise scalar phase. See [ShendeBullockMarkov2006]. -/
theorem theorem6_zyz_multiplexor {N : Type*} [Fintype N] [DecidableEq N]
    (U : N → Matrix Bool Bool ℂ) (hU : ∀ j, U j ∈ Matrix.unitaryGroup Bool ℂ) :
    ∃ (α θ β δ : N → ℝ),
      Matrix.blockDiagonal U =
        Matrix.blockDiagonal (fun j => paperRz (α j)) *
          Matrix.blockDiagonal (fun j => paperRy (θ j)) *
          Matrix.blockDiagonal (fun j => paperRz (β j)) *
          Matrix.blockDiagonal (fun j =>
            Complex.exp (((δ j : ℝ) : ℂ) * Complex.I) • (1 : Matrix Bool Bool ℂ)) := by
  let p : N → KnownQubitAngles := fun j => knownQubitAnglesOfUnitary (U j)
  have hp : ∀ j, knownQubitUnitary (p j) = U j := fun j =>
    (knownQubitEuler_explicit_angles_cover_unitaries (U j) (hU j)).1
  refine ⟨fun j => -(p j).alpha, fun j => (p j).theta, fun j => -(p j).beta,
    fun j => (p j).delta, ?_⟩
  have hblk : ∀ j, U j = paperRz (-(p j).alpha) * paperRy ((p j).theta) *
      paperRz (-(p j).beta) *
      (Complex.exp ((((p j).delta : ℝ) : ℂ) * Complex.I) • (1 : Matrix Bool Bool ℂ)) := by
    intro j
    rw [← hp j]
    simp only [knownQubitUnitary, paperRz, paperRy, neg_neg]
    rw [Matrix.mul_smul, mul_one]
  have hUfun : U = fun j => paperRz (-(p j).alpha) * paperRy ((p j).theta) *
      paperRz (-(p j).beta) *
      (Complex.exp ((((p j).delta : ℝ) : ℂ) * Complex.I) • (1 : Matrix Bool Bool ℂ)) :=
    funext hblk
  rw [hUfun]
  rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul]

end Qatlib.Papers.QLogicSynth04.MainResults
