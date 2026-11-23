/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkSearch.CollisionSearch.Theorem3Quan
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Constant success from a positive collision-solver exponent

For a nonempty input, a positive failure exponent makes the factor in the
underlying collision-solver bound at least two. The reduction preserves the
failure event, so at most half the uniformly counted seeds fail.  Thus, when a
graph collision exists, the uniform success probability is at least one half;
the constant is chosen before all input and solver quantifiers.

The module also records a diagonal Boolean phase query on complex Euclidean
space. Both its matrix `L2Operator` norm and its continuous linear map norm
are exactly one in every nonzero finite dimension. The success bound uses
an abstract collision solver, independently of this single-query model.
-/

set_option autoImplicit false

open Qatlib.Concepts.WalkSearch.WalkAlgorithms
open Qatlib.Concepts.WalkSearch.CollisionSearch
open scoped Classical
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Qatlib.Papers.QTriangle03.CollisionSearch

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The unit complex sign used to phase-mark a Boolean input. -/
def gcPhaseSign (b : Bool) : ℂ := if b then -1 else 1

/-- The diagonal phase-query matrix determined by a Boolean marking. -/
def gcPhaseOracleMatrix (x : ι → Bool) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => gcPhaseSign (x i)

/-- The graph-collision phase query as an operator on complex Euclidean space. -/
def gcPhaseOracle (x : ι → Bool) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (gcPhaseOracleMatrix x)

/-- Under a positive failure exponent and a collision witness, the graph
collision reduction fails on at most half of the finite solver seeds. -/
theorem gc_failure_count_le_half {n : ℕ} (hn : 0 < n) (G : OGraph n) (f : Fin n → Bool)
    (kcs : KCollisionSolver) (r : ℕ) (he : 1 ≤ kcs.cExp)
    (hw : ∃ t, gcRel G f t = true) :
    letI := kcs.seedFin
    (Finset.univ.filter (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 = none)).card * 2 ≤
      Fintype.card kcs.seed := by
  let := kcs.seedFin
  have h := kcs.finds r (gcRel G f) r 1 0 hw
  have hf : 2 ≤ (n + 1) ^ kcs.cExp := calc
    2 ≤ (n + 1) ^ 1 := by simpa using Nat.succ_le_succ hn
    _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos _) he
  simpa only [gcAlg_none_iff] using (Nat.mul_le_mul_left _ hf).trans h

/-- If a collision exists, at least half of the solver seeds produce one. -/
theorem gc_success_count_at_least_half {n : ℕ} (hn : 0 < n) (G : OGraph n)
    (f : Fin n → Bool) (kcs : KCollisionSolver) (r : ℕ) (he : 1 ≤ kcs.cExp)
    (hw : ∃ t, gcRel G f t = true) :
    letI := kcs.seedFin
    Fintype.card kcs.seed ≤ 2 *
      (Finset.univ.filter
        (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 ≠ none)).card := by
  let := kcs.seedFin
  have hfail := gc_failure_count_le_half hn G f kcs r he hw
  have hpartition :
      (Finset.univ.filter
        (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 = none)).card +
      (Finset.univ.filter
        (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 ≠ none)).card =
      Fintype.card kcs.seed := by
    rw [← Finset.card_univ (α := kcs.seed)]
    exact Finset.card_filter_add_card_filter_not
      (p := fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 = none)
  omega

/-- For every nonempty instance with a collision and positive failure exponent,
the uniform success probability is at least `1/2`. -/
theorem gc_success_probability_ge_half {n : ℕ} (hn : 0 < n) (G : OGraph n)
    (f : Fin n → Bool) (kcs : KCollisionSolver) (r : ℕ) (he : 1 ≤ kcs.cExp)
    (hw : ∃ t, gcRel G f t = true) :
    letI := kcs.seedFin
    (1 / 2 : ℝ) ≤
      ((Finset.univ.filter
        (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 ≠ none)).card : ℝ) /
        Fintype.card kcs.seed := by
  let := kcs.seedFin
  have hcount := gc_success_count_at_least_half hn G f kcs r he hw
  have hnonempty : Nonempty kcs.seed := kcs.seedNe
  have htotal : (0 : ℝ) < Fintype.card kcs.seed :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hnonempty)
  have hcount_real : (Fintype.card kcs.seed : ℝ) ≤
      (2 : ℝ) * ((Finset.univ.filter
        (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 ≠ none)).card : ℝ) := by
    have hraw : (Fintype.card kcs.seed : ℝ) ≤
        (((2 * (Finset.univ.filter
          (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 ≠ none)).card : ℕ) : ℝ)) := by
      exact_mod_cast hcount
    rw [Nat.cast_mul] at hraw
    norm_num at hraw
    exact hraw
  rw [le_div_iff₀ htotal]
  linarith [hcount_real]

/-- The success constant `1/2` is fixed before every graph, marking, solver,
and subset-size quantifier. -/
theorem gc_uniform_success_probability_ge_half :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
      ∀ (n : ℕ) (_ : 0 < n) (G : OGraph n) (f : Fin n → Bool)
        (kcs : KCollisionSolver) (r : ℕ), 1 ≤ kcs.cExp →
        (∃ t, gcRel G f t = true) →
        letI := kcs.seedFin
        C ≤
          ((Finset.univ.filter
            (fun ρ : kcs.seed => (gcAlg G f kcs r ρ).1 ≠ none)).card : ℝ) /
            Fintype.card kcs.seed := by
  refine ⟨1 / 2, by norm_num, by norm_num, fun n hn G f kcs r he hw => ?_⟩
  exact gc_success_probability_ge_half hn G f kcs r he hw

/-- Every Boolean phase-query matrix has sharp `L2Operator` norm one. -/
theorem gcPhaseOracleMatrix_opNorm_eq_one (x : ι → Bool) :
    ‖gcPhaseOracleMatrix x‖ = 1 := by
  rw [gcPhaseOracleMatrix, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    cases hx : x i <;> simp [gcPhaseSign]
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have hcoord := norm_le_pi_norm (fun j => gcPhaseSign (x j)) i
    cases hx : x i <;> simpa [gcPhaseSign, hx] using hcoord

/-- The corresponding operator on complex Euclidean space has norm one. -/
theorem gcPhaseOracle_opNorm_eq_one (x : ι → Bool) :
    ‖gcPhaseOracle x‖ = 1 := by
  rw [gcPhaseOracle, Matrix.l2_opNorm_toEuclideanCLM]
  exact gcPhaseOracleMatrix_opNorm_eq_one x

universe u

/-- The positive norm bound is uniform over the nonempty finite index type and
the Boolean marking. -/
theorem gcPhaseOracle_uniform_opNorm_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι] (x : ι → Bool),
        ‖gcPhaseOracle x‖ ≤ C := by
  refine ⟨1, by norm_num, fun ι _ _ _ x => ?_⟩
  rw [gcPhaseOracle_opNorm_eq_one]

end Qatlib.Papers.QTriangle03.CollisionSearch
