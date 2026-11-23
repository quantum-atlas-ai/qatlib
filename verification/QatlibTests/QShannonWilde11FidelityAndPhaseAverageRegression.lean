module

import Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.EpsilonBounds
import Qatlib.Papers.QShannonWilde11.MainResults.Appendix.PhaseAverages

set_option autoImplicit false
set_option warningAsError true

open Matrix
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric
open Qatlib.Papers.QShannonWilde11.MainResults.Appendix
open scoped BigOperators ComplexOrder InnerProductSpace RealInnerProductSpace

namespace QatlibTests.QShannonWilde11FidelityAndPhaseAverageRegression

/-- A concrete non-degenerate qubit density matrix. -/
private def rho0 : Dens (Fin 2) :=
  ⟨Matrix.diagonal ![1, 0], by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> simp, by
    simp [Fin.sum_univ_two]⟩

/-- The same matrix packaged as the second input state. -/
private def rho0' : Dens (Fin 2) := rho0

example :
    1 - (1 / 2 : ℝ) ≤ fidelity rho0.val rho0'.val := by
  refine fidelity_ge_one_sub_of_traceNormDiff_le rho0 rho0' (by norm_num) (by norm_num) ?_
  change Matrix.traceNorm (rho0.val - rho0.val) ≤ (1 / 2 : ℝ)
  rw [sub_self, Matrix.traceNorm_zero]
  norm_num

example :
    traceNormDiff rho0.val rho0'.val ≤ 2 * Real.sqrt (1 : ℝ) := by
  refine traceNormDiff_le_of_fidelity_ge_one_sub rho0 rho0' (by norm_num) (by norm_num) ?_
  change 1 - (1 : ℝ) ≤ (rootFidelity rho0.val rho0.val) ^ 2
  rw [sub_self]
  exact sq_nonneg _

/-- The standard real coordinate basis is the concrete jointly diagonal family. -/
private noncomputable def standardFamily : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
  fun i => EuclideanSpace.single i 1

example :
    ∃ γ δ : Fin 2 → ℝ,
      (∀ i, |γ i| = 1 ∧ |δ i| = 1) ∧
        1 - (1 / 4 : ℝ) ≤
          ⟪(Real.sqrt 2)⁻¹ • ∑ i, γ i • standardFamily i,
            (Real.sqrt 2)⁻¹ • ∑ i, δ i • standardFamily i⟫_ℝ := by
  refine exists_phase_average_overlap_joint_diagonal
    (by norm_num) (by norm_num) (1 / 4) standardFamily standardFamily
    EuclideanSpace.orthonormal_single EuclideanSpace.orthonormal_single ?_ ?_
  · intro i j hij
    exact EuclideanSpace.orthonormal_single.inner_eq_zero hij
  · intro i
    have hnorm : ‖standardFamily i‖ = 1 := EuclideanSpace.orthonormal_single.norm_eq_one i
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num

end QatlibTests.QShannonWilde11FidelityAndPhaseAverageRegression
