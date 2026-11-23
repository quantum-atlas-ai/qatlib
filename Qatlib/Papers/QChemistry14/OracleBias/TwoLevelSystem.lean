/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-!
# Two-level subsystem model for the Van Vleck oracle-bias analysis

This module defines the single-subsystem model used in the Van Vleck catastrophe
analysis of [McCleanEtAl2014]: the ground and excited eigenstates on
`EuclideanSpace ℂ (Fin 2)`, the oracle trial state of Eq. (50), the diagonal subsystem
Hamiltonian of Eq. (47) with its exact ℓ² operator norm, and the
single-subsystem overlap and energy identities of Eqs. (50)-(51).

## Main statements

* `trialState`: the normalized trial state `Δ|ψᵍ⟩ + e^{-iθ}√(1-Δ²)|ψᵉ⟩` on
  `EuclideanSpace ℂ (Fin 2)`.
* `norm_trialState`: the trial state is a unit vector whenever `Δ^2 ≤ 1`.
* `inner_trial_ground`: the overlap `⟨ψᵗ|ψᵍ⟩` equals the oracle quality `Δ`.
* `trialState_energy`: the energy expectation equals `Δ^2 * Eg + (1 - Δ^2) * Ee`.
* `subHamiltonianMatrix_norm`: the exact L2 operator norm of the subsystem Hamiltonian is
  `max |Eg| |Ee|`.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

noncomputable section

namespace Qatlib.Papers.QChemistry14.OracleBias

open scoped Matrix.Norms.L2Operator TensorProduct InnerProductSpace

/-- The ground eigenstate `|ψᵍ⟩ = (1, 0)` of the two-level subsystem on
`EuclideanSpace ℂ (Fin 2)`. -/
def ground : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

/-- The excited eigenstate `|ψᵉ⟩ = (0, 1)` of the two-level subsystem on
`EuclideanSpace ℂ (Fin 2)`. -/
def excited : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

/-- The ground state is normalized: `⟨ψᵍ|ψᵍ⟩ = 1`. -/
theorem inner_ground_self : ⟪ground, ground⟫_ℂ = 1 := by
  rw [ground, EuclideanSpace.inner_single_left]; simp

/-- The excited state is normalized: `⟨ψᵉ|ψᵉ⟩ = 1`. -/
theorem inner_excited_excited : ⟪excited, excited⟫_ℂ = 1 := by
  rw [excited, EuclideanSpace.inner_single_left]; simp

/-- The ground and excited states are orthogonal: `⟨ψᵍ|ψᵉ⟩ = 0`. -/
theorem inner_ground_excited : ⟪ground, excited⟫_ℂ = 0 := by
  rw [ground, excited, EuclideanSpace.inner_single_left]; simp

/-- The excited and ground states are orthogonal: `⟨ψᵉ|ψᵍ⟩ = 0`. -/
theorem inner_excited_ground : ⟪excited, ground⟫_ℂ = 0 := by
  rw [excited, ground, EuclideanSpace.inner_single_left]; simp

/-- The relative phase factor `e^{-iθ}` appearing in the excited coefficient. -/
def phase (θ : ℝ) : ℂ := Complex.exp (-Complex.I * ↑θ)

/-- The phase factor is a unit-modulus complex number: `‖e^{-iθ}‖² = 1`. -/
theorem phase_normSq (θ : ℝ) : Complex.normSq (phase θ) = 1 := by
  rw [phase, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (-Complex.I * ↑θ).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero, one_pow]

/-- The squared modulus of the full excited coefficient `e^{-iθ} * √(1 - Δ²)` equals
`1 - Δ²` whenever `Δ² ≤ 1`. -/
theorem excitedCoeff_normSq (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) :
    Complex.normSq (phase θ * ↑(Real.sqrt (1 - Δ ^ 2))) = 1 - Δ ^ 2 := by
  rw [Complex.normSq_mul, phase_normSq, Complex.normSq_ofReal, one_mul]
  rw [Real.mul_self_sqrt (by nlinarith)]

/-- The trial state `Δ|ψᵍ⟩ + e^{-iθ}√(1-Δ²)|ψᵉ⟩` of Eq. (50), normalized in the closed
unit disk `Δ² ≤ 1`. -/
def trialState (Δ θ : ℝ) : EuclideanSpace ℂ (Fin 2) :=
  (↑Δ : ℂ) • ground + (phase θ * ↑(Real.sqrt (1 - Δ ^ 2)) : ℂ) • excited

/-- The ground coordinate of the trial state is the real parameter `Δ`. -/
theorem trialState_apply_zero (Δ θ : ℝ) : trialState Δ θ 0 = ↑Δ := by
  simp [trialState, ground, excited]

/-- The excited coordinate of the trial state is `e^{-iθ}√(1-Δ²)`. -/
theorem trialState_apply_one (Δ θ : ℝ) :
    trialState Δ θ 1 = phase θ * ↑(Real.sqrt (1 - Δ ^ 2)) := by
  simp [trialState, ground, excited]

/-- The ground state has unit Euclidean norm. -/
theorem norm_ground : ‖ground‖ = 1 := by
  have h := EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)
  exact h.norm_eq_one 0

/-- The excited state has unit Euclidean norm. -/
theorem norm_excited : ‖excited‖ = 1 := by
  have h := EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin 2)
  exact h.norm_eq_one 1

/-- The squared Euclidean norm of the trial state equals one: `Δ² + (1 - Δ²) = 1`. -/
theorem sq_norm_trialState (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) : ‖trialState Δ θ‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, trialState_apply_zero, trialState_apply_one,
    Complex.norm_real, ← Complex.normSq_eq_norm_sq, excitedCoeff_normSq Δ θ hΔ, Real.norm_eq_abs]
  have h2 : |Δ| ^ 2 = Δ ^ 2 := by rw [← abs_pow, abs_of_nonneg (sq_nonneg Δ)]
  rw [h2]
  ring

/-- The trial state is a unit vector in `EuclideanSpace ℂ (Fin 2)` for `Δ² ≤ 1`. -/
theorem norm_trialState (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) : ‖trialState Δ θ‖ = 1 := by
  have h := sq_norm_trialState Δ θ hΔ
  rcases sq_eq_one_iff.1 h with h1 | h1
  · exact h1
  · have hnn := norm_nonneg (trialState Δ θ)
    rw [h1] at hnn
    norm_num at hnn

/-- The trial state is a unit vector: `⟨ψᵗ|ψᵗ⟩ = 1` for `Δ^2 ≤ 1`. -/
theorem inner_self_trialState (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) :
    ⟪trialState Δ θ, trialState Δ θ⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_trialState Δ θ hΔ]
  simp

/-- The single-subsystem overlap `⟨ψᵗ|ψᵍ⟩` equals the real oracle quality parameter `Δ`
of Eq. (50). -/
theorem inner_trial_ground (Δ θ : ℝ) : ⟪trialState Δ θ, ground⟫_ℂ = ↑Δ := by
  rw [trialState]
  simp only [inner_add_left, inner_smul_left, inner_ground_self, inner_excited_ground,
    mul_one, mul_zero, add_zero]
  rw [Complex.conj_ofReal]

/-- The single-subsystem overlap `⟨ψᵗ|ψᵉ⟩` equals `e^{iθ}√(1-Δ²)`. -/
theorem inner_trial_excited (Δ θ : ℝ) :
    ⟪trialState Δ θ, excited⟫_ℂ = (starRingEnd ℂ) (phase θ) * ↑(Real.sqrt (1 - Δ ^ 2)) := by
  rw [trialState]
  simp only [inner_add_left, inner_smul_left, inner_ground_excited, inner_excited_excited,
    mul_one, mul_zero, zero_add]
  rw [map_mul, Complex.conj_ofReal]

/-- The diagonal two-level Hamiltonian `diag(Eg, Ee)` written as a complex matrix in the
`{|ψᵍ⟩, |ψᵉ⟩}` basis. -/
def subHamiltonianMatrix (Eg Ee : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![↑Eg, ↑Ee]

/-- The subsystem Hamiltonian `Hᵢ` as a continuous linear map on
`EuclideanSpace ℂ (Fin 2)`, the operator behind Eq. (47). -/
def subHamiltonian (Eg Ee : ℝ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (subHamiltonianMatrix Eg Ee)

/-- The action of the subsystem Hamiltonian on a general vector is coordinatewise
multiplication by `(Eg, Ee)`. -/
theorem subHamiltonian_apply_coord (Eg Ee : ℝ) (x : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    subHamiltonian Eg Ee x i = ![↑Eg, ↑Ee] i * x i := by
  have h := congrFun (Matrix.ofLp_toEuclideanCLM (subHamiltonianMatrix Eg Ee) x) i
  rw [show ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (subHamiltonianMatrix Eg Ee) x).ofLp i)
      = subHamiltonian Eg Ee x i from rfl] at h
  rw [subHamiltonianMatrix, Matrix.mulVec_diagonal] at h
  rw [h]

/-- The ground state is an eigenstate of the subsystem Hamiltonian with eigenvalue `Eg`. -/
theorem subHamiltonian_apply_ground (Eg Ee : ℝ) :
    subHamiltonian Eg Ee ground = (↑Eg : ℂ) • ground := by
  apply PiLp.ext
  intro i
  rw [subHamiltonian_apply_coord]
  simp only [PiLp.smul_apply, smul_eq_mul, ground, PiLp.single_apply]
  fin_cases i <;> simp

/-- The excited state is an eigenstate of the subsystem Hamiltonian with eigenvalue `Ee`. -/
theorem subHamiltonian_apply_excited (Eg Ee : ℝ) :
    subHamiltonian Eg Ee excited = (↑Ee : ℂ) • excited := by
  apply PiLp.ext
  intro i
  rw [subHamiltonian_apply_coord]
  simp only [PiLp.smul_apply, smul_eq_mul, excited, PiLp.single_apply]
  fin_cases i <;> simp

/-- The phase factor is a unit complex number: `e^{-iθ} * conj(e^{-iθ}) = 1`. -/
theorem phase_mul_conj (θ : ℝ) : phase θ * (starRingEnd ℂ) (phase θ) = 1 := by
  rw [Complex.mul_conj, phase_normSq, Complex.ofReal_one]

/-- The trial-state energy expectation equals `Δ^2 * Eg + (1 - Δ^2) * Ee`, Eq. (51). -/
theorem trialState_energy (Δ θ : ℝ) (hΔ : Δ ^ 2 ≤ 1) (Eg Ee : ℝ) :
    ⟪trialState Δ θ, subHamiltonian Eg Ee (trialState Δ θ)⟫_ℂ
      = ((Δ ^ 2 * Eg + (1 - Δ ^ 2) * Ee : ℝ) : ℂ) := by
  have hHt : subHamiltonian Eg Ee (trialState Δ θ)
      = (↑Δ * ↑Eg : ℂ) • ground
        + (phase θ * ↑(Real.sqrt (1 - Δ ^ 2)) * ↑Ee : ℂ) • excited := by
    rw [trialState, map_add, map_smul, map_smul, subHamiltonian_apply_ground,
      subHamiltonian_apply_excited, smul_smul, smul_smul]
  rw [hHt, inner_add_right, inner_smul_right, inner_smul_right, inner_trial_ground,
    inner_trial_excited]
  have e1 : (↑Δ * ↑Eg : ℂ) * ↑Δ = ↑(Δ ^ 2 * Eg) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    ring
  have e2 : (phase θ * ↑(Real.sqrt (1 - Δ ^ 2)) * ↑Ee : ℂ)
      * ((starRingEnd ℂ) (phase θ) * ↑(Real.sqrt (1 - Δ ^ 2)))
      = (((1 - Δ ^ 2 : ℝ) : ℂ) * ↑Ee) := by
    have hsq : (↑(Real.sqrt (1 - Δ ^ 2)) : ℂ) * ↑(Real.sqrt (1 - Δ ^ 2))
        = ((1 - Δ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by nlinarith)]
    have hp : phase θ * (starRingEnd ℂ) (phase θ) = 1 := phase_mul_conj θ
    calc
      (phase θ * ↑(Real.sqrt (1 - Δ ^ 2)) * ↑Ee) *
          ((starRingEnd ℂ) (phase θ) * ↑(Real.sqrt (1 - Δ ^ 2))) =
        (↑Ee * (phase θ * (starRingEnd ℂ) (phase θ))) *
          (↑(Real.sqrt (1 - Δ ^ 2)) * ↑(Real.sqrt (1 - Δ ^ 2))) := by ring
      _ = (↑Ee * 1) * ((1 - Δ ^ 2 : ℝ) : ℂ) := by rw [hp, hsq]
      _ = ((1 - Δ ^ 2 : ℝ) : ℂ) * ↑Ee := by ring
  rw [e1, e2, ← Complex.ofReal_mul, ← Complex.ofReal_add]

/-- The sup norm of a `Fin 2`-indexed family of complex numbers is the maximum of the two
entrywise norms. -/
private theorem pi_norm_fin_two (f : Fin 2 → ℂ) : ‖f‖ = max ‖f 0‖ ‖f 1‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr ?_
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · refine max_le ?_ ?_
    · exact norm_le_pi_norm f (0 : Fin 2)
    · exact norm_le_pi_norm f (1 : Fin 2)

/-- The exact ℓ² operator norm of the diagonal two-level
Hamiltonian is `max |Eg| |Ee|`. -/
theorem subHamiltonianMatrix_norm (Eg Ee : ℝ) :
    ‖subHamiltonianMatrix Eg Ee‖ = max |Eg| |Ee| := by
  rw [subHamiltonianMatrix, Matrix.l2_opNorm_diagonal, pi_norm_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs]

end Qatlib.Papers.QChemistry14.OracleBias
