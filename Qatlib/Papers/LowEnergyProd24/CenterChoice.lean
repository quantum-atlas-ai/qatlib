/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.AffineCenter
import Qatlib.Papers.LowEnergyProd24.LocalModel.LocalData

/-!
# Optimal scalar centers for local interactions

The scale `optimalStrength` is twice the largest optimal distance of a local term from the real
scalar identity line. The selected `centers` attain a uniform half-strength bound and yield
`physicalModel`, preserving the original grouped operators and total Hamiltonian. See
[HejaziZiniArrazola2024].

## Main statements

* `centers_strength`: Subtracting the selected scalar center from any local term leaves norm at
  most `optimalStrength h / 2`.
* `optimalStrength_eq_max_inf`: The optimal strength equals twice the maximum, over local terms,
  of the infimum of their distances from real scalar identity matrices.
* `physicalModel`: The physical Hamiltonian obtained by equipping the local data with the
  selected optimal centers and their uniform strength bound.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.CenterChoice
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixGeometry
variable {N R M k d : ℕ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- Twice the uniform optimal radius of the family of local terms relative to real scalar
multiples of the identity. -/
def optimalStrength (h : LocalData N R M k d) : ℝ :=
  2*(AffineCenter.familyRadius h.term (1 : Matrix (Register N) (Register N) ℂ) : ℝ)

/-- The optimal interaction strength is nonnegative. -/
theorem optimalStrength_nonneg (h : LocalData N R M k d) : 0 ≤ optimalStrength h := by
  unfold optimalStrength
  positivity

/-- A choice of real scalar centers giving the uniform optimal radius bound for the family of
local terms. -/
def centers (h : LocalData N R M k d) : Fin R → ℝ :=
  Classical.choose (AffineCenter.exists_uniform_family_centers h.term
    (1 : Matrix (Register N) (Register N) ℂ) (by rw [norm_one]))

/-- Subtracting the selected scalar center from any local term leaves norm at most
`optimalStrength h / 2`. See [HejaziZiniArrazola2024]. -/
theorem centers_strength (h : LocalData N R M k d) (i : Fin R) :
    ‖h.term i-(centers h i : ℂ) • 1‖ ≤ optimalStrength h/2 := by
  have hi := Classical.choose_spec (AffineCenter.exists_uniform_family_centers h.term
    (1 : Matrix (Register N) (Register N) ℂ) (by rw [norm_one])) i
  change ‖h.term i-centers h i • (1 : Matrix (Register N) (Register N) ℂ)‖ ≤ _ at hi
  have he (r : ℝ) : r • (1 : Matrix (Register N) (Register N) ℂ)=(r : ℂ) • 1 := by
    ext a b
    exact Complex.real_smul
  rw [he] at hi
  convert hi using 1
  unfold optimalStrength
  ring

/-- At each site, the sum of the norms of the centered interactions containing that site is at
most `optimalStrength h * d`. See [HejaziZiniArrazola2024]. -/
theorem centered_site_strength (h : LocalData N R M k d) (x : Fin N) :
    (∑ i ∈ (Finset.univ : Finset (Fin R)).filter (fun i => x ∈ h.support i),
      ‖h.term i-(centers h i : ℂ) • 1‖) ≤ optimalStrength h*d := by
  let S := (Finset.univ : Finset (Fin R)).filter (fun i => x ∈ h.support i)
  have hJ := optimalStrength_nonneg h
  calc
    _ ≤ ∑ _i ∈ S, optimalStrength h := by
      apply Finset.sum_le_sum
      intro i hi
      exact (centers_strength h i).trans (by linarith)
    _ = (S.card : ℝ)*optimalStrength h := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ)*optimalStrength h := mul_le_mul_of_nonneg_right (by exact_mod_cast h.degree x) hJ
    _ = _ := mul_comm _ _
/-- The optimal strength equals twice the maximum, over local terms, of the infimum of their
distances from real scalar identity matrices. See [HejaziZiniArrazola2024]. -/
theorem optimalStrength_eq_max_inf (h : LocalData N R M k d) :
    optimalStrength h=2*((Finset.univ : Finset (Fin R)).sup (α := NNReal) (fun i =>
      (⟨sInf (Set.range (fun c : ℝ => ‖h.term i+c • (1 : Matrix (Register N) (Register N) ℂ)‖)),
        AffineCenter.affine_inf_nonneg (h.term i) 1⟩ : NNReal)) : ℝ) := rfl

/-- The physical Hamiltonian obtained by equipping the local data with the selected optimal
centers and their uniform strength bound. -/
def physicalModel (h : LocalData N R M k d) : PhysicalHamiltonian N R M k d (optimalStrength h) :=
  h.realize (optimalStrength h) (centers h) (centers_strength h)

/-- The physical model retains each original grouped Hamiltonian. -/
theorem physicalModel_grouped (h : LocalData N R M k d) (m : Fin M) :
    (physicalModel h).grouped m=h.grouped m := rfl

/-- The physical model retains the original total Hamiltonian. -/
theorem physicalModel_total (h : LocalData N R M k d) : (physicalModel h).total=h.total := rfl

/-- The total Hamiltonian of the original local data is Hermitian. -/
theorem original_total_hermitian (h : LocalData N R M k d) : h.total.IsHermitian :=
    (physicalModel h).total_hermitian
end Qatlib.Papers.LowEnergyProd24.CenterChoice
