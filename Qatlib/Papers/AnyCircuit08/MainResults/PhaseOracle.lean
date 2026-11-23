/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Qatlib.Papers.AnyCircuit08.MainResults.Basic

/-!
# The phase query in the dispersing-circuit oracle problem

Theorem 9 of [HallgrenHarrow2008] encodes the secret in a Boolean response function.
One phase query multiplies each component of the uniform query state by the sign of the
response. This file gives the Euclidean state and its matrix action.

[arXiv:0805.0007v2](https://arxiv.org/abs/0805.0007v2)
-/

@[expose] public noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.AnyCircuit08.MainResults

open Qatlib.Papers.AnyCircuit08.MainResults

/-- One Boolean phase query, represented by the diagonal matrix of response signs. -/
def phaseOracle {A X : Type} [DecidableEq X] (f : A → X → Bool) (a : A) : Matrix X X ℂ :=
  Matrix.diagonal (oracleSign f a)

/-- The uniform query state before the oracle acts. -/
def uniformQueryState (X : Type) [Fintype X] : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun _ => 1 / (Real.sqrt (Fintype.card X) : ℂ))

/-- The diagonal Boolean phase query is unitary. -/
theorem phaseOracle_mem_unitaryGroup {A X : Type} [Fintype X] [DecidableEq X]
    (f : A → X → Bool) (a : A) : phaseOracle f a ∈ Matrix.unitaryGroup X ℂ := by
  change Matrix.diagonal (oracleSign f a) ∈ unitary (Matrix X X ℂ)
  rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro x
  cases h : f a x <;> simp [oracleSign, h, Unitary.mem_iff]

/-- The unit-modulus eigenvalues of a Boolean phase query give it Euclidean operator norm one
on a nonempty query register. -/
theorem norm_phaseOracle {A X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (f : A → X → Bool) (a : A) : ‖phaseOracle f a‖ = 1 := by
  rw [phaseOracle, Matrix.l2_opNorm_diagonal]
  have hsign (x : X) : ‖oracleSign f a x‖ = 1 := by
    cases h : f a x <;> simp [oracleSign, h]
  obtain ⟨x⟩ := ‹Nonempty X›
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun y => (hsign y).le)
  · rw [← hsign x]
    exact norm_le_pi_norm (oracleSign f a) x

/-- Applying the phase query to the uniform state produces the signed amplitudes from
[HallgrenHarrow2008], Theorem 9. -/
theorem phaseOracle_uniformQueryState {A X : Type} [Fintype X] [DecidableEq X]
    (f : A → X → Bool) (a : A) :
    Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (phaseOracle f a) (uniformQueryState X) =
      WithLp.toLp 2 (oracleState f a) := by
  ext x
  change (WithLp.ofLp
    (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (phaseOracle f a) (uniformQueryState X))) x = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [phaseOracle, uniformQueryState, Matrix.mulVec_diagonal, oracleState, mul_comm]

/-- The signed query state is a unit vector in the Euclidean norm whenever the query register
is nonempty. -/
theorem norm_oracleState {A X : Type} [Fintype X] [Nonempty X] (f : A → X → Bool) (a : A) :
    ‖(WithLp.toLp 2 (oracleState f a) : EuclideanSpace ℂ X)‖ = 1 := by
  have hcard : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos (α := X)
  have hsqrt : 0 < Real.sqrt (Fintype.card X : ℝ) := Real.sqrt_pos.2 hcard
  have hnorm (x : X) : ‖oracleState f a x‖ ^ 2 = 1 / (Fintype.card X : ℝ) := by
    have hsign : ‖oracleSign f a x‖ = 1 := by
      cases h : f a x <;> simp [oracleSign, h]
    rw [oracleState, norm_mul, norm_div, norm_one, hsign, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsqrt, div_pow, one_pow, Real.sq_sqrt hcard.le]
  have hsq : ‖(WithLp.toLp 2 (oracleState f a) : EuclideanSpace ℂ X)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [hnorm, hcard.ne']
  nlinarith [norm_nonneg (WithLp.toLp 2 (oracleState f a) : EuclideanSpace ℂ X)]

end Qatlib.Papers.AnyCircuit08.MainResults
