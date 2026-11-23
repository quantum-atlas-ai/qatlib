module

public import Qatlib.Papers.CommuteTest05.WalkDetect.RotationDeviation
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Concrete Euclidean consumer for the CommuteTest05 Claim 13 average bound

Two non-degenerate rotation planes are used, each with angle `π / 4`, and the normalized
coefficients `3 / 5` and `4 / 5`. The time horizon `1000` is above the Claim 13 threshold
`100 * ∑ j, ν j ^ 2 / θ j = 400 / π`, so the averaged deviation bound, its uniform constant
form, the scaling identity, and the Hadamard-test detection bound all apply to a genuine
four-dimensional Euclidean instance.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace QatlibTests.CommuteTest05RotationDeviation

open Qatlib.Papers.CommuteTest05.WalkDetect

private def theta (_j : Fin 2) : ℝ := Real.pi / 4

private def nu : Fin 2 → ℝ := ![3 / 5, 4 / 5]

private theorem theta_pos : ∀ j, 0 < theta j := by
  intro j
  simp [theta]
  positivity

private theorem theta_le : ∀ j, theta j ≤ Real.pi / 2 := by
  intro j
  simp [theta]
  linarith [Real.pi_pos]

private theorem nu_norm : ∑ j, nu j ^ 2 = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [nu]

private theorem weighted_sum_eq : (∑ j : Fin 2, nu j ^ 2 / theta j) = 4 / Real.pi := by
  rw [Fin.sum_univ_two]
  simp [nu, theta]
  field_simp
  ring

private theorem horizon : 100 * (∑ j : Fin 2, nu j ^ 2 / theta j) ≤ (1000 : ℝ) := by
  rw [weighted_sum_eq]
  rw [show 100 * (4 / Real.pi) = 400 / Real.pi by ring, div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_three]

/-- The averaged deviation bound of Claim 13 on the concrete two-plane instance. -/
example :
    (48 : ℝ) / 25 ≤
      (1 / (((1000 + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (1000 + 1),
          ‖(planeRotationFun theta)^[t] (rotationState nu) - rotationState nu‖ ^ 2) :=
  averaged_rotation_deviation_ge nu theta 1000 theta_pos theta_le nu_norm horizon

/-- The uniform constant form applies to the same concrete instance. -/
example :
    ∃ C : ℝ, 0 < C ∧
      C ≤ (1 / (((1000 + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (1000 + 1),
          ‖(planeRotationFun theta)^[t] (rotationState nu) - rotationState nu‖ ^ 2) := by
  obtain ⟨C, hCpos, hC⟩ := exists_uniform_rotation_deviation_constant
  exact ⟨C, hCpos, hC (Fin 2) nu theta 1000 theta_pos theta_le nu_norm horizon⟩

/-- The scaling sentence of Claim 13 on the concrete instance, with `ε = 1 / 3`. -/
example :
    (1 / (((1000 + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (1000 + 1),
          ‖(planeRotationFun theta)^[t] (rotationState (Real.sqrt (1 - 1 / 3) • nu)) -
            rotationState (Real.sqrt (1 - 1 / 3) • nu)‖ ^ 2) =
      (1 - 1 / 3) * ((1 / (((1000 + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (1000 + 1),
          ‖(planeRotationFun theta)^[t] (rotationState nu) - rotationState nu‖ ^ 2)) :=
  averaged_rotation_deviation_scale nu theta 1000 (by norm_num) (by norm_num)

/-- The averaged Hadamard-test flag probability of Theorem 15 on the concrete instance. -/
example :
    (12 : ℝ) / 25 ≤
      (1 / (((1000 + 1 : ℕ) : ℝ))) *
        (∑ t ∈ Finset.range (1000 + 1),
          (1 / 4) *
            ‖(planeRotationFun theta)^[t] (rotationState nu) - rotationState nu‖ ^ 2) :=
  averaged_detection_probability_ge nu theta 1000 theta_pos theta_le nu_norm horizon

end QatlibTests.CommuteTest05RotationDeviation
