module

public import Qatlib.Papers.DiracEquation16.HighOrder.ReciprocalCoeffs
public import Qatlib.Papers.DiracEquation16.AutoCorrel.HadamardReadout
public import Qatlib.Papers.DiracEquation16.FilterCore.HeraldedDilation

@[expose] public section

/-!
# Consumer regression for the DiracEquation16 Appendix readout increment

This ordinary-module consumer specializes the new Appendix readout results to concrete
non-degenerate instances:

* the length-seven reciprocal row of Table II satisfies the Suzuki conditions of Eq. (A4) of
  [FillionGourdeauMacLeanLaflamme2017] with a negative coefficient;
* on a one-dimensional system with identity evolution and the basis input `|0⟩`, the
  Hadamard-test expectations read `⟨σₓ⟩ = ⟨σₓ + iσ_y⟩ = 1` and the `σₓ = +1` Born probability
  is one, in both the `Inner` and the EuclideanSpace formulations;
* on a one-qubit register with the concrete Pauli-X evolution, the autocorrelation vanishes and
  the `σₓ = +1` Born probability is exactly `1/2`;
* the heralded dilation `c-Pᵢ` at singular value `aᵢ = 1/2` is unitary with operator norm one,
  its successful branch transports `diag (1, 1/2)`, and the second basis state attains
  the lower bound `aᵢ² = 1/4` on success probability.
-/

set_option autoImplicit false

namespace QatlibTests.DiracEquation16AppendixReadoutRegression

open scoped Matrix BigOperators Kronecker Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.DiracEquation16.HighOrder
open Qatlib.Papers.DiracEquation16.AutoCorrel
open Qatlib.Papers.DiracEquation16.FilterCore

/-- The length-seven Table II row witnesses the Suzuki conditions with a signed reciprocal
carrier. -/
theorem table2_row7_suzuki_witness :
    ∃ c : Fin 7 → ℚ, (∀ i, c i ≠ 0) ∧ (∃ i, c i < 0) ∧ (∑ i, (c i)⁻¹ = 1)
      ∧ (∑ i, (c i)⁻¹ ^ 3 = 0) :=
  ⟨table2Row7Reciprocals, table2Row7Reciprocals_nonzero,
    table2Row7Reciprocals_exists_negative, table2Row7_sum_param_eq_one,
    table2Row7_sum_cube_param_eq_zero⟩

/-- The Eq. (A5) product form for the same row. -/
theorem table2_row7_product_form :
    ∑ i, ∏ j ∈ Finset.univ.erase i, table2Row7Reciprocals j
      = ∏ j, table2Row7Reciprocals j :=
  table2Row7_sum_erase_prod_eq_prod

/-- The identity evolution on a one-dimensional register is unitary. -/
theorem one_unitary_fin1 :
    (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ Matrix.unitaryGroup (Fin 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp

/-- The concrete Pauli-X matrix is unitary. -/
theorem sigmaX_unitary : sigmaX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, Matrix.mul_apply, Fin.sum_univ_two]

/-- The Pauli-X evolution maps the basis state `|0⟩` to `|1⟩`. -/
theorem sigmaX_mulVec_ket0 : sigmaX *ᵥ Ket (0 : Fin 2) = Ket (1 : Fin 2) := by
  funext i
  fin_cases i
  · show (∑ j : Fin 2, sigmaX (0 : Fin 2) j * Ket (0 : Fin 2) j) = (0 : ℂ)
    rw [Fin.sum_univ_two]
    simp [sigmaX, Ket]
  · show (∑ j : Fin 2, sigmaX (1 : Fin 2) j * Ket (0 : Fin 2) j) = (1 : ℂ)
    rw [Fin.sum_univ_two]
    simp [sigmaX, Ket]

/-- The autocorrelation of the identity evolution on `|0⟩` is one. -/
theorem corr_identity_fin1 : corr 1 (Ket (0 : Fin 1)) = 1 := by
  simp [corr, Matrix.one_mulVec, inner_ket_ket]

/-- The autocorrelation of the Pauli-X evolution on `|0⟩` vanishes. -/
theorem corr_sigmaX_fin2 : corr sigmaX (Ket (0 : Fin 2)) = 0 := by
  rw [corr, sigmaX_mulVec_ket0]
  simp [inner_ket_ket]

/-- The `σₓ` expectation on the identity readout equals one. -/
theorem expect_sigmaX_identity_fin1 :
    Inner (corrState 1 (Ket (0 : Fin 1)))
      (ApplyGate (sigmaX ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) (corrState 1 (Ket (0 : Fin 1)))) = 1 := by
  rw [expect_sigmaX, corr_identity_fin1]
  simp

/-- Eq. (D5) on the identity readout: `⟨(σₓ + iσ_y) ⊗ I⟩ = 1` in Euclidean space. -/
theorem readout_euclidean_identity_fin1 :
    inner ℂ (toEuclidean_fromVec (corrState 1 (Ket (0 : Fin 1))))
      ((Matrix.toEuclideanCLM : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin 2 × Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 1)))
        ((sigmaX + Complex.I • sigmaY) ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (toEuclidean_fromVec (corrState 1 (Ket (0 : Fin 1))))) = 1 := by
  rw [expect_readout_euclidean, corr_identity_fin1]

/-- The `σₓ = +1` Born probability on the identity readout equals one. -/
theorem born_sigmaX_plus_identity_fin1 :
    ‖toEuclidean_fromVec ((projSigmaXPlus ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ
        corrState 1 (Ket (0 : Fin 1)))‖ ^ 2 = 1 := by
  rw [born_sigmaX_plus (1 : Matrix (Fin 1) (Fin 1) ℂ) one_unitary_fin1 (Ket (0 : Fin 1))
    (normalized_ket _), corr_identity_fin1]
  norm_num

/-- The readout state on the identity instance is normalized. -/
theorem corrState_norm_identity_fin1 :
    ‖toEuclidean_fromVec (corrState 1 (Ket (0 : Fin 1)))‖ = 1 :=
  corrState_norm 1 one_unitary_fin1 _ (normalized_ket _)

/-- The `σₓ = +1` Born probability after the concrete Pauli-X circuit word equals `1/2`. -/
theorem born_sigmaX_plus_sigmaX_fin2 :
    ‖toEuclidean_fromVec ((projSigmaXPlus ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ
        (autoCorrWord sigmaX *ᵥ TensorState (Ket (0 : Fin 2)) (Ket (0 : Fin 2))))‖ ^ 2 = 2⁻¹ := by
  rw [autoCorrWord_mulVec, born_sigmaX_plus sigmaX sigmaX_unitary (Ket (0 : Fin 2)) (normalized_ket _),
    corr_sigmaX_fin2]
  norm_num

/-- The heralded dilation at singular value `1/2` is unitary. -/
theorem heraldedDilation_half_unitary :
    heraldedDilation (2⁻¹ : ℝ) ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  heraldedDilation_unitary ⟨by norm_num, by norm_num⟩

/-- Its `Matrix.Norms.L2Operator` operator norm is one. -/
theorem heraldedDilation_half_opNorm : ‖heraldedDilation (2⁻¹ : ℝ)‖ = 1 :=
  heraldedDilation_opNorm ⟨by norm_num, by norm_num⟩

/-- The successful branch transports `diag (1, 1/2)` on the concrete input `|1⟩`. -/
theorem heraldedDilation_success_ket1 :
    ∀ i : Fin 2, (heraldedDilation (2⁻¹ : ℝ) *ᵥ dilatedInput (Ket (1 : Fin 2)))
        (Fin.castLE (by norm_num) i)
      = (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else ((2⁻¹ : ℝ) : ℂ)) *ᵥ
        Ket (1 : Fin 2)) i :=
  heraldedDilation_success_apply (Ket (1 : Fin 2))

/-- The postselected success probability on `|1⟩` attains the lower bound `aᵢ² = 1/4`. -/
theorem heraldedDilation_success_probability_ket1 :
    ‖toEuclidean_fromVec (fun k : Fin 4 => if k = 0 ∨ k = 1 then
        (heraldedDilation (2⁻¹ : ℝ) *ᵥ dilatedInput (Ket (1 : Fin 2))) k else 0)‖ ^ 2 =
      (2⁻¹ : ℝ) ^ 2 := by
  rw [heraldedDilation_success_probability ⟨by norm_num, by norm_num⟩ _ (normalized_ket _)]
  simp [Ket]

/-- The success probability is at least `aᵢ² = 1/4`. -/
theorem heraldedDilation_success_ge_quarter :
    (2⁻¹ : ℝ) ^ 2 ≤ ‖toEuclidean_fromVec (fun k : Fin 4 => if k = 0 ∨ k = 1 then
        (heraldedDilation (2⁻¹ : ℝ) *ᵥ dilatedInput (Ket (0 : Fin 2))) k else 0)‖ ^ 2 :=
  heraldedDilation_success_probability_ge ⟨by norm_num, by norm_num⟩ _ (normalized_ket _)

end QatlibTests.DiracEquation16AppendixReadoutRegression
