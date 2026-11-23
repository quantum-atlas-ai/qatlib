module

public import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
public import Qatlib.Papers.AmpTransform14.GeneralUnitary.FlatUnitaryBound

set_option autoImplicit false
noncomputable section

namespace QatlibTests.AmpTransform14GeneralUnitary

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Papers.AmpTransform14.GeneralUnitary
open scoped BigOperators Matrix.Norms.L2Operator

/-- A normalized input supported entirely on the first of two labels. -/
def markedState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![1, 0]

/-- The concrete two-point state is a non-degenerate unit vector. -/
theorem markedState_norm : ‖markedState‖ = 1 := by
  rw [markedState, EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

/-- The two-point Fourier matrix has the flat modulus required by the general bound. -/
theorem qftMatrix_two_flat (i j : Fin 2) :
    ‖QFTMatrix 2 i j‖ = (Real.sqrt (2 : ℝ))⁻¹ := by
  rw [qftMatrix_apply, Complex.norm_mul, norm_primRoot_zpow, mul_one]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]

/-- Applying the flat-unitary theorem to the two-point Fourier transform gives a contraction
and bounds the output probability at zero by the marked fraction. -/
theorem qftMatrix_two_marked_state_bounds :
    ‖QFTMatrix 2‖ ≤ 1 ∧ ‖∑ j, QFTMatrix 2 0 j * markedState j‖ ^ 2 ≤ 1 / 2 := by
  obtain ⟨C, _, hC, hbound⟩ := generalUnitaryFlatBound
  obtain ⟨hop, hprob⟩ :=
    hbound 2 (by norm_num) (QFTMatrix 2) (qftMatrix_unitary (by norm_num))
      qftMatrix_two_flat {0} markedState 0 markedState_norm
  refine ⟨hop, ?_⟩
  simpa [hC, markedState, Real.sq_sqrt (by norm_num : 0 ≤ (1 : ℝ) / 2)] using hprob

end QatlibTests.AmpTransform14GeneralUnitary
