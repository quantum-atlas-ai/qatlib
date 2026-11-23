module

public import Qatlib.Papers.QTriangle03.CollisionSearch.PositiveSuccess

@[expose] public section

/-!
# Concrete graph-collision success and phase-query consumers

The two-vertex complete graph has a genuine graph collision.  A one-seed
solver with positive failure exponent returns a Classical witness whenever one
exists, so the positive-success theorem is instantiated non-vacuously.  The
same two-dimensional Euclidean space also exercises the phase-query norm
bridge on a concrete nonempty basis.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.QTriangle03CollisionSearchRegression

open Qatlib.Concepts.WalkSearch.CollisionSearch
open Qatlib.Concepts.WalkSearch.WalkAlgorithms
open Qatlib.Papers.QTriangle03.CollisionSearch
open scoped Classical Matrix.Norms.L2Operator

/-- A concrete solver with one seed and positive failure exponent that returns
a Classical witness whenever the supplied relation is satisfiable. -/
noncomputable def chooseCollisionSolver : KCollisionSolver := { zeroChargeCollisionSolver with
  cExp := 1
  finds := by
    intro n k r R s u c hR
    simp [zeroChargeCollisionSolver, hR]
    change 0 * (n + 1) ≤ _
    exact (Nat.zero_mul (n + 1)).le.trans (Nat.zero_le _) }

/-- The uniform success ratio of the concrete two-vertex graph-collision
instance. -/
noncomputable def concreteSuccessProbability : ℝ :=
  letI := chooseCollisionSolver.seedFin
  ((Finset.univ.filter
    (fun ρ : chooseCollisionSolver.seed =>
      (gcAlg twoVertexEdgeGraph (fun _ => true) chooseCollisionSolver 1 ρ).1 ≠
        none)).card : ℝ) /
    Fintype.card chooseCollisionSolver.seed

/-- The concrete graph has a graph collision, and the solver has positive
failure exponent. -/
example : (1 / 2 : ℝ) ≤ concreteSuccessProbability := by
  exact gc_success_probability_ge_half (by decide) twoVertexEdgeGraph
    (fun _ => true) chooseCollisionSolver 1 (by decide)
    ⟨id, by simp [gcRel, adjB, twoVertexEdgeGraph]⟩

/-- The uniform top-level constant applies to the same concrete non-degenerate
instance. -/
example : ∃ C : ℝ, 0 < C ∧ C ≤ concreteSuccessProbability := by
  obtain ⟨C, hC, _, hall⟩ := gc_uniform_success_probability_ge_half
  exact ⟨C, hC, hall 2 (by decide) twoVertexEdgeGraph (fun _ => true)
    chooseCollisionSolver 1 (by decide)
    ⟨id, by simp [gcRel, adjB, twoVertexEdgeGraph]⟩⟩

/-- The concrete two-coordinate Boolean phase oracle has matrix `L2Operator`
norm one. -/
example :
    ‖gcPhaseOracleMatrix (ι := Fin 2) (fun i => i == 0)‖ = 1 :=
  gcPhaseOracleMatrix_opNorm_eq_one (fun i => i == 0)

/-- The same phase query is a norm-one operator on complex Euclidean space. -/
example : ‖gcPhaseOracle (ι := Fin 2) (fun i => i == 0)‖ = 1 :=
  gcPhaseOracle_opNorm_eq_one (fun i => i == 0)

/-- The uniform Euclidean operator bound is exercised on the two-dimensional
concrete domain. -/
example : ∃ C : ℝ, 0 < C ∧
    ∀ x : Fin 2 → Bool, ‖gcPhaseOracle x‖ ≤ C := by
  obtain ⟨C, hC, hall⟩ := gcPhaseOracle_uniform_opNorm_bound
  exact ⟨C, hC, hall (Fin 2)⟩

end QatlibTests.QTriangle03CollisionSearchRegression
