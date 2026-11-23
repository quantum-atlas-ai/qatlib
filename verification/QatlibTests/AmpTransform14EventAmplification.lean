module

public import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
public import Qatlib.Papers.AmpTransform14.GeneralUnitary.EventAmplification

set_option autoImplicit false
noncomputable section

namespace QatlibTests.AmpTransform14EventAmplification

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Papers.AmpTransform14.GeneralUnitary
open scoped BigOperators Matrix.Norms.L2Operator

/-- The primitive second root used by the two-point Fourier matrix is `-1`. -/
theorem primRoot_two_eq : primRoot 2 = (-1 : ℂ) := by
  rw [primRoot]
  change Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 2) = -1
  rw [show 2 * (Real.pi : ℂ) * Complex.I / 2 = (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_pi_mul_I]

/-- The row of the two-point Fourier matrix at frequency one sums to zero. -/
theorem qft_two_row_one : ∑ z, QFTMatrix 2 1 z = 0 := by
  rw [Fin.sum_univ_two]
  simp [QFTMatrix, primRoot_two_eq]

/-- The two-point Fourier matrix has the flat modulus required by the general theorem. -/
theorem qft_two_flat (i j : Fin 2) :
    ‖QFTMatrix 2 i j‖ = (Real.sqrt (2 : ℝ))⁻¹ := by
  rw [qftMatrix_apply, Complex.norm_mul, norm_primRoot_zpow, mul_one]
  simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]

/-- The marked row sum at frequency one and the singleton marked set is nonzero. -/
theorem qft_two_marked : (∑ z ∈ ({0} : Finset (Fin 2)), QFTMatrix 2 1 z) ≠ 0 := by
  rw [Finset.sum_singleton]
  intro hzero
  have hnorm := qft_two_flat 1 0
  rw [hzero, norm_zero] at hnorm
  have hpos : (0 : ℝ) < (Real.sqrt (2 : ℝ))⁻¹ := by positivity
  exact hpos.ne' hnorm.symm

/-- The concrete two-point instance satisfies the amplitude-ratio formula. -/
theorem qft_two_amplitude_ratio :
    amplifiedAmplitude (QFTMatrix 2) ({0} : Finset (Fin 2)) 1 0 1 /
        markedAmplitude (QFTMatrix 2) ({0} : Finset (Fin 2)) 1 =
      - (Real.sqrt (2 : ℝ) : ℂ) / 2 := by
  have h := general_unitary_amplitude_ratio (N := 2) (by norm_num) (QFTMatrix 2)
    ({0} : Finset (Fin 2)) 1 0 1 qft_two_row_one qft_two_marked
  simpa using h

/-- The concrete two-point instance satisfies the probability-ratio formula at the source
floor round count. -/
theorem qft_two_probability_ratio :
    let θ : ℝ := generalUnitaryAngle 2 1
    let k : ℕ := generalUnitaryRounds 2 1
    let a : ℝ := Real.sin ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (1 : ℝ)
    let b : ℝ := Real.cos ((2 * (k : ℝ) + 1) * θ) / Real.sqrt (2 - 1)
    ‖amplifiedAmplitude (QFTMatrix 2) ({0} : Finset (Fin 2)) a b 1‖ ^ 2 =
      (1 / 4) * (((2 : ℝ) ^ 2) / (1 : ℝ) ^ 2) * (Real.tan θ) ^ 2 *
        (Real.sin (2 * (k : ℝ) * θ)) ^ 2 *
          ‖markedAmplitude (QFTMatrix 2) ({0} : Finset (Fin 2)) 1‖ ^ 2 := by
  simpa using general_unitary_probability_ratio 1 1 (by norm_num) (by norm_num)
    (QFTMatrix 2) ({0} : Finset (Fin 2)) (by simp) 1 qft_two_row_one qft_two_marked

/-- The uniform-constant top-level theorem applies to the concrete two-point Fourier matrix and
gives the operator-norm contraction. -/
theorem qft_two_operator_norm : ‖QFTMatrix 2‖ ≤ 1 := by
  obtain ⟨C, _hCpos, _hC, hmain⟩ := general_unitary_event_amplification
  exact (hmain 1 1 (by norm_num) (by norm_num) (QFTMatrix 2)
    (qftMatrix_unitary (by norm_num)) qft_two_flat ({0} : Finset (Fin 2)) (by simp)
    1 qft_two_row_one qft_two_marked).1

end QatlibTests.AmpTransform14EventAmplification
