module

import Qatlib.Papers.QChemistry14.OracleBias.TwoLevelSystem
import Qatlib.Papers.QChemistry14.OracleBias.VanVleckTensor

/-! Regression tests for the tensor-product Van Vleck model of [McCleanEtAl2014] on
concrete non-degenerate instances: oracle quality `Δ = 1/2` (nontrivial, nonzero), phase
`θ = π/3`, subsystem gap `Ee - Eg = 2`, and subsystem count `N = 3`. -/

open scoped Matrix.Norms.L2Operator InnerProductSpace

open Qatlib.Papers.QChemistry14.OracleBias

/-- The exact L2 operator norm of the concrete subsystem Hamiltonian `diag(0, 2)` is `2`. -/
example : ‖subHamiltonianMatrix (0:ℝ) (2:ℝ)‖ = (2:ℝ) := by
  rw [subHamiltonianMatrix_norm]
  norm_num

/-- The single-subsystem trial energy of Eq. (51) at `Δ = 1/2` is `(1/4) * 0 + (3/4) * 2 = 3/2`. -/
example :
    ⟪trialState (1/2 : ℝ) (Real.pi / 3),
        subHamiltonian (0:ℝ) (2:ℝ) (trialState (1/2 : ℝ) (Real.pi / 3))⟫_ℂ
      = ((3/2 : ℝ) : ℂ) := by
  rw [trialState_energy (1/2 : ℝ) (Real.pi / 3) (by norm_num) (0:ℝ) (2:ℝ)]
  congr 1
  norm_num

/-- The `N = 3` trial/ground amplitude equals `(1/2)^3`, not `(1/2)^6`. -/
example :
    ⟪prodTrial (1/2 : ℝ) (Real.pi / 3) 3, prodGround 3⟫_ℂ = (((1/2 : ℝ) : ℂ) ^ 3) :=
  inner_prodTrial_prodGround (1/2 : ℝ) (Real.pi / 3) 3

/-- The absolute `N = 3` amplitude is `|1/2|^3 = 1/8`. -/
example : ‖⟪prodTrial (1/2 : ℝ) (Real.pi / 3) 3, prodGround 3⟫_ℂ‖ = (1/8 : ℝ) := by
  rw [qpe_ground_amplitude]
  norm_num

/-- The Born probability at `N = 3` is `(1/4)^3 = 1/64`. -/
example : ‖⟪prodTrial (1/2 : ℝ) (Real.pi / 3) 3, prodGround 3⟫_ℂ‖ ^ 2 = (1/64 : ℝ) := by
  rw [qpe_ground_born]
  norm_num

/-- The trial energy of the total Hamiltonian at `N = 3` is `3 * (3/4) * 2 = 9/2`. -/
example :
    ⟪prodTrial (1/2 : ℝ) (Real.pi / 3) 3,
        sumHam (0:ℝ) (2:ℝ) 3 (prodTrial (1/2 : ℝ) (Real.pi / 3) 3)⟫_ℂ
      = ((9/2 : ℝ) : ℂ) := by
  rw [tower_energy (1/2 : ℝ) (Real.pi / 3) (by norm_num) (0:ℝ) (2:ℝ) 3]
  congr 1
  norm_num

/-- Both product states are unit vectors at `N = 3`. -/
example : ‖prodTrial (1/2 : ℝ) (Real.pi / 3) 3‖ = 1 ∧ ‖prodGround 3‖ = 1 :=
  ⟨norm_prodTrial (1/2 : ℝ) (Real.pi / 3) (by norm_num) 3, norm_prodGround 3⟩

/-- At `N = 3` and `Eg = 1`, the ground product state has eigenvalue `3`. -/
example : sumHam 1 3 3 (prodGround 3) = (3 : ℂ) • prodGround 3 := by
  rw [sumHam_apply_prodGround]
  norm_num

/-- The bias of Eq. (53) at `N = 3) is `3 * (1 - 1/4) * (3 - 1) = 9/2`. -/
example :
    ⟪prodTrial (1/2 : ℝ) (Real.pi / 3) 3,
        sumHam 1 3 3 (prodTrial (1/2 : ℝ) (Real.pi / 3) 3)⟫_ℂ
      - ⟪prodGround 3, sumHam 1 3 3 (prodGround 3)⟫_ℂ = ((9/2 : ℝ) : ℂ) := by
  rw [tower_bias (1/2 : ℝ) (Real.pi / 3) (by norm_num) 1 3 3]
  congr 1
  norm_num

/-- The Born probability admits a uniform exponential decay constant `C > 0`. -/
example : ∃ C > 0, ∀ n : ℕ,
    ‖⟪prodTrial (1/2 : ℝ) (Real.pi / 3) n, prodGround n⟫_ℂ‖ ^ 2 ≤ Real.exp (-(C * n)) :=
  bornProb_exponential_decay (1/2 : ℝ) (Real.pi / 3) (by norm_num)

/-- The repetition cost admits a uniform exponential lower bound `exp (C * n)` with `C > 0`. -/
example : ∃ C > 0, ∀ n : ℕ,
    Real.exp (C * n) ≤ (‖⟪prodTrial (1/2 : ℝ) (Real.pi / 3) n, prodGround n⟫_ℂ‖ ^ 2)⁻¹ :=
  repetition_growth (1/2 : ℝ) (Real.pi / 3) (by norm_num) (by norm_num)
