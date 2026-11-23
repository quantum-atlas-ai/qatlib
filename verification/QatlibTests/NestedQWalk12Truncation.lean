module

public import Qatlib.Papers.NestedQWalk12.CoherentTrunc.OperatorNorm
public import Qatlib.Papers.NestedQWalk12.ErrorBudget.TwoLevelCompose

set_option autoImplicit false
noncomputable section

namespace QatlibTests.NestedQWalk12Truncation

open Matrix
open Qatlib.Foundations.MatrixGeometry.LcuFrame
open Qatlib.Foundations.MatrixGeometry.BranchUnitary
open Qatlib.Papers.NestedQWalk12.CoherentTrunc
open Qatlib.Papers.NestedQWalk12.ErrorBudget
open scoped BigOperators Matrix.Norms.L2Operator

/-- The concrete non-degenerate two-dimensional branch family: the identity on branch zero and
minus the identity on branch one. -/
def family (c : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun _ => if c = 0 then 1 else -1

/-- Both branch matrices are unitary. -/
theorem family_unitary (c : Fin 2) : family c ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (family c)ᴴ * family c = 1
  ext s t
  fin_cases c <;> fin_cases s <;> fin_cases t <;>
    norm_num [family, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.one_apply]

/-- The concrete two-level branch family: minus the identity in every register. -/
def nestedFamily : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun _ _ =>
  Matrix.diagonal fun _ => -1

/-- Every branch of the nested family is unitary. -/
theorem nested_family_unitary (i j : Fin 2) :
    nestedFamily i j ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (nestedFamily i j)ᴴ * nestedFamily i j = 1
  ext s t
  fin_cases s <;> fin_cases t <;>
    norm_num [nestedFamily, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.one_apply]

/-- The real control amplitudes 4/5 and 3/5. -/
def amplitudes : Fin 2 → ℂ := ![4 / 5, 3 / 5]

/-- The amplitudes are normalized. -/
theorem amplitudes_normalized : ∑ i, ‖amplitudes i‖ ^ 2 = 1 := by
  norm_num [amplitudes, Fin.sum_univ_two, norm_div]

/-- A normalized two-dimensional conditional state supported on the second coordinate, so that
the discarded branch sees the nontrivial `-1` eigenvalue. -/
def conditional : Fin 2 → State (Fin 2) := fun _ => ![0, 1]

/-- The conditional states are normalized. -/
theorem conditional_normalized (c : Fin 2) : Normalized (conditional c) := by
  unfold Normalized
  norm_num [conditional, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, norm_div]

/-- The standalone normalized state `![0, 1]` used by the nested instance. -/
theorem state01_normalized : Normalized (![0, 1] : State (Fin 2)) := by
  unfold Normalized
  norm_num [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    norm_div]

/-- The two branches cost one and two queries, respectively. -/
def queries (c : Fin 2) : ℕ := c.val + 1

/-- The discarded mass of the concrete single-level instance is exactly 9/25. -/
theorem tail_example : tailMass amplitudes queries 1 = (9 : ℝ) / 25 := by
  norm_num [tailMass, amplitudes, queries, Fin.sum_univ_two, norm_div]

/-- The weighted inner discarded mass of the concrete nested instance is 9/25. -/
theorem inner_tail_example :
    (∑ i : Fin 2, ‖amplitudes i‖ ^ 2 * tailMass amplitudes queries 1) = 9 / 25 := by
  norm_num [tailMass, amplitudes, queries, Fin.sum_univ_two, norm_div]

/-- The square-root evaluations used below. -/
theorem sqrt_tail : Real.sqrt ((9 : ℝ) / 25) = 3 / 5 := by
  rw [show (9 : ℝ) / 25 = (3 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The explicit-constant error bound instantiated on the concrete non-degenerate instance:
the Euclidean distance between the ideal output and the cutoff-one truncation is at most
`2 * √(9/25) = 6/5`. -/
theorem error_bound_example :
    ‖toHilbert ((controlled (truncated family queries 1) - controlled family) *ᵥ
      coherent amplitudes conditional)‖ ≤ 6 / 5 := by
  have h := truncated_controlled_error_norm family family_unitary amplitudes conditional
    conditional_normalized queries 1
  rw [tail_example, sqrt_tail] at h
  have h2 : (2 : ℝ) * (3 / 5) = 6 / 5 := by norm_num
  rw [h2] at h
  exact h

/-- The uniform-constant theorem applies to the same concrete instance with the constant
existentially quantified outside all universal quantifiers. -/
theorem error_constant_example :
    ∃ C : ℝ, 0 < C ∧
      ‖toHilbert ((controlled (truncated family queries 1) - controlled family) *ᵥ
        coherent amplitudes conditional)‖ ≤ C * (3 / 5) := by
  obtain ⟨C, hC0, hC⟩ := truncated_controlled_error_constant
  refine ⟨C, hC0, ?_⟩
  have h := hC family family_unitary amplitudes conditional conditional_normalized queries 1
  rw [tail_example, sqrt_tail] at h
  exact h

/-- The truncation-error matrix of the concrete instance has true L2 operator norm at most
`2`. -/
theorem operator_norm_example :
    ‖controlled (truncated family queries 1) - controlled family‖ ≤ 2 :=
  truncated_controlled_l2OperatorNorm_le family family_unitary queries 1

/-- The two-level nested overlap bound on the concrete non-degenerate nested instance: the real
overlap is at least `1 - 2 * (9/25) - 2 * √(9/25) = -23/25`. -/
theorem nested_overlap_example :
    (-23 / 25 : ℝ) ≤
      (Inner (controlled (fun i => controlled (nestedFamily i)) *ᵥ
          coherent amplitudes (fun _ => coherent amplitudes (fun _ => ![0, 1])))
        (controlled (truncated (fun i => controlled (truncated (nestedFamily i) queries 1))
              queries 1) *ᵥ
          coherent amplitudes (fun _ => coherent amplitudes (fun _ => ![0, 1])))).re := by
  have h := nested_truncation_overlap nestedFamily nested_family_unitary amplitudes
    amplitudes_normalized (fun _ => amplitudes) (fun _ => amplitudes_normalized)
    (fun _ _ => ![0, 1]) (fun _ _ => state01_normalized) queries 1 (fun _ => queries) 1
  rw [inner_tail_example, tail_example, sqrt_tail] at h
  norm_num at h
  linarith

/-- The uniform-constant form of the two-level nested bound on the concrete instance. -/
theorem nested_constant_example :
    ∃ C : ℝ, 0 < C ∧
      1 - C * ((24 : ℝ) / 25) ≤
        (Inner (controlled (fun i => controlled (nestedFamily i)) *ᵥ
            coherent amplitudes (fun _ => coherent amplitudes (fun _ => ![0, 1])))
          (controlled (truncated (fun i => controlled (truncated (nestedFamily i) queries 1))
                queries 1) *ᵥ
            coherent amplitudes (fun _ => coherent amplitudes (fun _ => ![0, 1])))).re := by
  obtain ⟨C, hC0, hC⟩ := nested_truncation_constant
  refine ⟨C, hC0, ?_⟩
  have h := hC nestedFamily nested_family_unitary amplitudes amplitudes_normalized
    (fun _ => amplitudes) (fun _ => amplitudes_normalized)
    (fun _ _ => ![0, 1]) (fun _ _ => state01_normalized) queries 1 (fun _ => queries) 1
  rw [inner_tail_example, tail_example, sqrt_tail] at h
  norm_num at h
  linarith

/-- The explicit cutoff selected for target `1/100` bounds the discarded mass of the concrete
instance. -/
theorem cutoff_example :
    tailMass amplitudes queries (max 1 (Nat.ceil (meanQueries amplitudes queries / (1 / 100)))) ≤
      (1 : ℝ) / 100 :=
  tailMass_le_ceil_mean_div amplitudes queries (1 / 100) (by norm_num)

end QatlibTests.NestedQWalk12Truncation
