module

public import Qatlib.Papers.QQueryGraph04.MainResults.OraclePhase

@[expose] public section

/-!
# Concrete Euclidean consumer for the QQueryGraph04 oracle bridge

The register has one nonempty coordinate, the two oracle inputs disagree there, and the state has
positive mass.  Thus the consumer exercises a nontrivial
phase-oracle perturbation rather than an empty or identically-zero instance.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace QatlibTests.QQueryGraph04OraclePhase

open Qatlib.Papers.QQueryGraph04.MainResults.OraclePhase

private def inputFalse : Fin 1 → Bool := ![false]

private def inputTrue : Fin 1 → Bool := ![true]

private def state : EuclideanSpace ℂ (Fin 1) :=
  WithLp.toLp 2 ![(1 : ℂ)]

/-- The selected concrete state has unit Euclidean norm. -/
example : ‖state‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [state]

/-- The exact squared state perturbation is four times the mass on the differing coordinate. -/
example :
    ‖phaseOracle inputFalse state - phaseOracle inputTrue state‖ ^ 2 = 4 := by
  have hmass : restrictedMass inputFalse inputTrue state = 1 := by
    simp [restrictedMass, differ, inputFalse, inputTrue, state]
  rw [phaseOracle_difference_state_sq, hmass]
  norm_num

/-- The top-level uniform state bound is invoked on the concrete non-degenerate instance. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖phaseOracle inputFalse state - phaseOracle inputTrue state‖ ≤
        C * Real.sqrt (restrictedMass inputFalse inputTrue state) := by
  obtain ⟨C, hC, hbound⟩ :=
    phaseOracle_state_perturbation_bound (ι := Fin 1)
  exact ⟨C, hC, hbound inputFalse inputTrue state⟩

/-- The top-level uniform matrix L2-operator bound is invoked on the same input pair. -/
example :
    ∃ C : ℝ, 0 < C ∧
      ‖phaseOracleMatrix inputFalse - phaseOracleMatrix inputTrue‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    phaseOracle_matrix_perturbation_bound (ι := Fin 1)
  exact ⟨C, hC, hbound inputFalse inputTrue⟩

end QatlibTests.QQueryGraph04OraclePhase
