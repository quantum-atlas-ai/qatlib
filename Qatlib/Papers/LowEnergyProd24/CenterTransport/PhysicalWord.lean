/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.LocalModel.Physical
import Qatlib.Papers.LowEnergyProd24.ProductError.GeneratorExpansion
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.InteractionWeight

/-!
# Physical product words and scalar center shifts

This module defines product words and generator coefficients directly from the physical grouped
Hamiltonians. The identities `physical_stage_centered` and `physical_total_centered` separate
scalar center shifts, while `physical_approximate_unitary` and `physical_generator_hasSum`
provide the unitary and series properties of the physical word. See [HejaziZiniArrazola2024].

## Main statements

* `physical_stage_centered`: A physical stage generator is the corresponding centered stage
  generator plus its scalar center shift.
* `physical_approximate_unitary`: The approximate word of physical stage generators is unitary
  for every real time.
* `physical_generator_hasSum`: The physical generator coefficient series multiplied by powers of
  `t` sums to the product generator.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The stage generator `-i * stage.1` times the physical grouped Hamiltonian indexed by
`stage.2`. -/
def stageGenerator (h : PhysicalHamiltonian N R M k d J) (stage : ℝ × Fin M) :=
  ((-stage.1 : ℂ)*Complex.I) • h.grouped stage.2

/-- The skew-Hermitian generator `-i` times the total physical Hamiltonian. -/
def totalGenerator (h : PhysicalHamiltonian N R M k d J) := ((-1 : ℂ)*Complex.I) • h.total

/-- The exponential product word formed from the physical stage generators at time `t`. -/
def approximate (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  word (stages.map (stageGenerator h)) t

/-- The interaction-picture product word relative to the total physical generator. -/
def relative (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  interaction (totalGenerator h) (stages.map (stageGenerator h)) t

/-- The degree-`n` generator coefficient for the list of physical stage generators. -/
def physicalCoefficient (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (n : ℕ) :=
  generatorCoefficient (stages.map (stageGenerator h)) n

/-- The condition that coefficients below degree `p` equal the total generator at degree zero
and vanish at all positive degrees. -/
def lowerOrderCancellation (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (p : ℕ) : Prop :=
  ∀ n < p, physicalCoefficient h stages n=if n=0 then totalGenerator h else 0

/-- The scalar identity contribution `-i * stage.1 * h.groupCenter stage.2` removed when
centering a stage. -/
def stageShift (h : PhysicalHamiltonian N R M k d J) (stage : ℝ × Fin M) :=
  (((-stage.1 : ℂ)*Complex.I)*(h.groupCenter stage.2 : ℂ)) • (1 : Matrix (Register N) (Register N) ℂ)

/-- Every complex scalar multiple of the identity commutes with every matrix. -/
theorem scalar_identity_central (c : ℂ) (A : Matrix (Register N) (Register N) ℂ) : Commute (c • 1) A := by
  change (c • 1)*A=A*(c • 1)
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- The scalar center shift of a physical stage commutes with every matrix. -/
theorem stageShift_central (h : PhysicalHamiltonian N R M k d J) (stage : ℝ × Fin M)
    (A : Matrix (Register N) (Register N) ℂ) : Commute (stageShift h stage) A := scalar_identity_central _ _

/-- A physical stage generator is the corresponding centered stage generator plus its scalar
center shift. -/
theorem physical_stage_centered (h : PhysicalHamiltonian N R M k d J) (stage : ℝ × Fin M) :
    stageGenerator h stage=ProductError.stageGenerator h.normalized stage+stageShift h stage := by
  have hg : h.grouped stage.2=h.normalized.grouped stage.2+(h.groupCenter stage.2 : ℂ) • 1 := by
    rw [h.normalized_grouped]
    abel
  simp only [stageGenerator, hg, smul_add, smul_smul, ProductError.stageGenerator, stageShift]

/-- The total physical Hamiltonian equals its normalized centered total plus the total scalar
center times the identity. -/
theorem physical_total_centered (h : PhysicalHamiltonian N R M k d J) :
    h.total=h.normalized.total+(h.totalCenter : ℂ) • 1 := by
  rw [h.normalized_total]
  abel

/-- Exponentiating the total physical generator at time `t` gives the exact evolution of
`h.total`. -/
theorem physical_total_exp (h : PhysicalHamiltonian N R M k d J) (t : ℝ) :
    NormedSpace.exp (t • totalGenerator h)=evolve h.total t := by
  congr 1
  ext i j
  simp only [totalGenerator, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- Exponentiating a physical stage generator at time `t` gives evolution by its grouped
Hamiltonian for time `stage.1 * t`. -/
theorem physical_stage_exp (h : PhysicalHamiltonian N R M k d J) (stage : ℝ × Fin M) (t : ℝ) :
    NormedSpace.exp (t • stageGenerator h stage)=evolve (h.grouped stage.2) (stage.1*t) := by
  congr 1
  ext i j
  simp only [stageGenerator, Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The approximate word of physical stage generators is unitary for every real time. See
[HejaziZiniArrazola2024]. -/
theorem physical_approximate_unitary (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t ∈ unitary (Matrix (Register N) (Register N) ℂ) := by
  induction stages with
  | nil => exact one_mem _
  | cons stage stages ih =>
    change NormedSpace.exp (t • stageGenerator h stage)*approximate h stages t ∈ _
    rw [physical_stage_exp]
    exact mul_mem (evolve_unitary _ (h.grouped_hermitian stage.2) _) ih

/-- The physical generator coefficient series multiplied by powers of `t` sums to the product
generator. -/
theorem physical_generator_hasSum (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t : ℝ) :
    HasSum (fun n : ℕ => t^n • physicalCoefficient h stages n) (generator (stages.map (stageGenerator h)) t) :=
  generator_hasSum _ _

/-- The list pairing each centered stage generator with its scalar center shift. -/
def stagePairs (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) :=
  stages.map (fun stage => (ProductError.stageGenerator h.normalized stage, stageShift h stage))

/-- The second component of each stage pair commutes with every matrix. -/
theorem stagePairs_central (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) :
    ∀ pair ∈ stagePairs h stages, ∀ A, Commute pair.2 A := by
  intro pair hp A
  obtain ⟨stage, hs, he⟩ := List.mem_map.mp hp
  subst pair
  exact stageShift_central h stage A

/-- Adding the components of each stage pair recovers the list of physical stage generators. -/
theorem stagePairs_physical (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) :
    (stagePairs h stages).map (fun pair => pair.1+pair.2)=stages.map (stageGenerator h) := by
  simp only [stagePairs, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro stage hs
  exact (physical_stage_centered h stage).symm
end Qatlib.Papers.LowEnergyProd24.CenterTransport
