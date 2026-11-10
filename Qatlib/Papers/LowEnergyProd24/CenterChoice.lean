/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.AffineCenter
import Qatlib.Papers.LowEnergyProd24.LocalModel.LocalData
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

def optimalStrength (h : LocalData N R M k d) : ℝ :=
  2*(AffineCenter.familyRadius h.term (1 : Matrix (Register N) (Register N) ℂ) : ℝ)

theorem optimalStrength_nonneg (h : LocalData N R M k d) : 0 ≤ optimalStrength h := by
  unfold optimalStrength
  positivity

def centers (h : LocalData N R M k d) : Fin R → ℝ :=
  Classical.choose (AffineCenter.exists_uniform_family_centers h.term
    (1 : Matrix (Register N) (Register N) ℂ) (by rw [norm_one]))

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
theorem optimalStrength_eq_max_inf (h : LocalData N R M k d) :
    optimalStrength h=2*((Finset.univ : Finset (Fin R)).sup (α := NNReal) (fun i =>
      (⟨sInf (Set.range (fun c : ℝ => ‖h.term i+c • (1 : Matrix (Register N) (Register N) ℂ)‖)),
        AffineCenter.affine_inf_nonneg (h.term i) 1⟩ : NNReal)) : ℝ) := rfl

def physicalModel (h : LocalData N R M k d) : PhysicalHamiltonian N R M k d (optimalStrength h) :=
  h.realize (optimalStrength h) (centers h) (centers_strength h)

theorem physicalModel_grouped (h : LocalData N R M k d) (m : Fin M) :
    (physicalModel h).grouped m=h.grouped m := rfl

theorem physicalModel_total (h : LocalData N R M k d) : (physicalModel h).total=h.total := rfl

theorem original_total_hermitian (h : LocalData N R M k d) : h.total.IsHermitian :=
    (physicalModel h).total_hermitian
end Qatlib.Papers.LowEnergyProd24.CenterChoice
