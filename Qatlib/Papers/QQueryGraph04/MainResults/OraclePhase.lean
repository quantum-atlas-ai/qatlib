/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

/-!
# Euclidean phase-oracle perturbation

The search step of the greedy minimum-finding procedure in [DurrEtAl2006], Section 3, marks
indices that are good for the current selection. A Boolean phase oracle can represent such a
marking predicate once it has been computed. This module compares two such phase queries:
the oracles act by opposite signs exactly where their Boolean strings disagree.
The resulting Euclidean state perturbation has squared norm four times the mass on those
coordinates, and the corresponding matrix perturbation has uniformly bounded L2 operator norm.

The bounds concern a single phase query. The construction of the marking predicate from the
paper's value and type oracles, the greedy loop and its stopping and output semantics, and the
√(dN) query schedule are outside this result.

## Main statements

* `phaseOracle_difference_state_sq`: the exact squared Euclidean norm of the state change.
* `phaseOracle_state_perturbation_bound`: a uniform constant `2` bounds all state perturbations
  by the square root of the differing-coordinate mass.
* `phaseOracle_matrix_perturbation_bound`: the same model has matrix L2 operator perturbation
  norm bounded by a uniform constant.

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.QQueryGraph04.MainResults.OraclePhase

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The unit complex sign used by a Boolean phase oracle. -/
def phaseSign (b : Bool) : ℂ := if b then -1 else 1

/-- The diagonal phase-oracle matrix determined by a Boolean input string. -/
def phaseOracleMatrix (x : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => phaseSign (x i)

/-- The same phase oracle as a continuous linear map on complex Euclidean space. -/
def phaseOracle (x : ι → Bool) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (phaseOracleMatrix x)

/-- The finite set of coordinates at which two Boolean input strings disagree. -/
def differ (x y : ι → Bool) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ y i

/-- The squared Euclidean mass of a state on the coordinates where two oracle inputs differ. -/
def restrictedMass (x y : ι → Bool) (u : EuclideanSpace ℂ ι) : ℝ :=
  ∑ i ∈ differ x y, ‖u i‖ ^ 2

omit [Nonempty ι] in

/-- A phase oracle multiplies each coordinate by the sign selected by its Boolean input. -/
theorem phaseOracle_apply (x : ι → Bool) (u : EuclideanSpace ℂ ι) (i : ι) :
    (phaseOracle x u) i = phaseSign (x i) * u i := by
  have h := congrFun (Matrix.ofLp_toEuclideanCLM (phaseOracleMatrix x) u) i
  simpa only [phaseOracle, phaseOracleMatrix, Matrix.mulVec_diagonal] using h

omit [Nonempty ι] in

/-- Opposite Boolean phases change a Euclidean state exactly by twice its differing-coordinate
part. -/
theorem phaseOracle_difference_state_sq (x y : ι → Bool) (u : EuclideanSpace ℂ ι) :
    ‖phaseOracle x u - phaseOracle y u‖ ^ 2 = 4 * restrictedMass x y u := by
  have hcoord : ∀ i : ι,
      ‖phaseSign (x i) * u i - phaseSign (y i) * u i‖ ^ 2 =
        if x i = y i then 0 else 4 * ‖u i‖ ^ 2 := by
    intro i
    by_cases hxy : x i = y i
    · simp [hxy]
    · have hsign : phaseSign (x i) - phaseSign (y i) = (2 : ℂ) ∨
          phaseSign (x i) - phaseSign (y i) = (-2 : ℂ) := by
        unfold phaseSign
        cases hx : x i <;> cases hy : y i
        · exact absurd (by rw [hx, hy]) hxy
        · exact Or.inl (by norm_num)
        · exact Or.inr (by norm_num)
        · exact absurd (by rw [hx, hy]) hxy
      rcases hsign with h | h
      · have hval : phaseSign (x i) * u i - phaseSign (y i) * u i =
          (2 : ℂ) * u i := by
          have hfactor : phaseSign (x i) * u i - phaseSign (y i) * u i =
              (phaseSign (x i) - phaseSign (y i)) * u i := by ring
          rw [hfactor, h]
        rw [hval, Complex.norm_mul]
        simp [hxy]
        ring
      · have hval : phaseSign (x i) * u i - phaseSign (y i) * u i =
          (-2 : ℂ) * u i := by
          have hfactor : phaseSign (x i) * u i - phaseSign (y i) * u i =
              (phaseSign (x i) - phaseSign (y i)) * u i := by ring
          rw [hfactor, h]
        rw [hval, Complex.norm_mul]
        simp [hxy]
        ring
  simp only [EuclideanSpace.norm_sq_eq, WithLp.ofLp_sub, Pi.sub_apply,
    phaseOracle_apply x u, phaseOracle_apply y u]
  have hfiltered : (∑ i, if x i = y i then (0 : ℝ) else 4 * ‖u i‖ ^ 2) =
      ∑ i ∈ differ x y, 4 * ‖u i‖ ^ 2 := by
    rw [differ, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hxy : x i = y i
    · simp [hxy]
    · simp [hxy]
  rw [Finset.sum_congr rfl fun i _ => hcoord i, hfiltered, ← Finset.mul_sum]
  rfl

omit [Nonempty ι] in

/-- The state perturbation norm itself is exactly twice the differing-coordinate mass norm. -/
theorem phaseOracle_difference_state_norm (x y : ι → Bool) (u : EuclideanSpace ℂ ι) :
    ‖phaseOracle x u - phaseOracle y u‖ =
      2 * Real.sqrt (restrictedMass x y u) := by
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← Real.sqrt_sq (norm_nonneg _), phaseOracle_difference_state_sq,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4]

/-- There is a positive state-perturbation constant, chosen before the pair of Boolean inputs
and the state are quantified. -/
theorem phaseOracle_state_perturbation_bound (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y : ι → Bool) (u : EuclideanSpace ℂ ι),
      ‖phaseOracle x u - phaseOracle y u‖ ≤
        C * Real.sqrt (restrictedMass x y u) := by
  refine ⟨2, by norm_num, fun x y u => ?_⟩
  exact le_of_eq (phaseOracle_difference_state_norm x y u)

/-- There is a positive operator-perturbation constant, chosen before the Boolean input pair is
quantified; the matrix norm is the scoped L2 operator norm. -/
theorem phaseOracle_matrix_perturbation_bound (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ι → Bool,
      ‖phaseOracleMatrix x - phaseOracleMatrix y‖ ≤ C := by
  refine ⟨2, by norm_num, fun x y => ?_⟩
  have hmap : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (phaseOracleMatrix x - phaseOracleMatrix y) :
      EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      phaseOracle x - phaseOracle y := by
    simp [phaseOracle, map_sub]
  rw [← Matrix.l2_opNorm_toEuclideanCLM, hmap]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 2) fun u => ?_
  have hstate := phaseOracle_difference_state_norm x y u
  have hmass : restrictedMass x y u ≤ ‖u‖ ^ 2 := by
    unfold restrictedMass differ
    rw [Finset.sum_filter]
    rw [EuclideanSpace.norm_sq_eq u]
    show (∑ i, if x i ≠ y i then (‖u i‖ ^ 2 : ℝ) else 0) ≤ ∑ i, ‖u i‖ ^ 2
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hxy : x i ≠ y i
    · simp [hxy]
    · simp [hxy]
  calc ‖(phaseOracle x - phaseOracle y) u‖
      = 2 * Real.sqrt (restrictedMass x y u) := hstate
    _ ≤ 2 * Real.sqrt (‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (by norm_num)
    _ = 2 * ‖u‖ := by rw [Real.sqrt_sq (norm_nonneg u)]

end Qatlib.Papers.QQueryGraph04.MainResults.OraclePhase
