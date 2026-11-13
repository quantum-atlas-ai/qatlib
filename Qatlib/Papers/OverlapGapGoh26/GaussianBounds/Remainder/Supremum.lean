/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.Limit

/-!
# Supremum bounds for the cube remainder

`supCube` is the supremum of the absolute repeated index energy over the Hilbert cube. It is
continuous and attained, controls the absolute difference between binary and cube minimum
energies, and is subextensive in Gaussian probability. These results make the remainder
comparison explicit for the Gaussian model associated with [GohMuller2026].

## Main statements

* `actual_optimum_gap_le_sup`: The binary ground energy minus the cube minimum is nonnegative
  and has absolute value at most `2 * supCube A`.
* `actual_supCube_subextensive`: For fixed `r` and `η > 0`, the probability that `supCube A` is
  at least `ηN` tends to zero as `N` tends to infinity.
* `actual_absolute_optimum_gap_subextensive`: For fixed `r` and `η > 0`, the probability that
  the absolute difference between binary and cube minimum energies exceeds `ηN` tends to zero.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder

/-- The supremum of the absolute repeated index energy over the Hilbert cube. -/
def supCube {q N:ℕ} (A:Tensor q N) : ℝ :=
    sSup ((fun u=>|tensorEnergy (repeated A) u|) '' hilbertCube N)

/-- The absolute repeated index energy is jointly continuous in the tensor and the spin vector. -/
theorem repeated_energy_continuous (q N:ℕ) :
    Continuous (fun p:Tensor q N×(Fin N→ℝ)=>|tensorEnergy (repeated p.1) p.2|) := by
  have hr:Continuous (repeated (q:=q) (N:=N)) := by
    apply continuous_pi
    intro k
    by_cases hk:Function.Injective k <;>simp only [repeated,hk,if_true,if_false] <;>fun_prop
  exact (continuous_tensorEnergy.comp ((hr.comp continuous_fst).prodMk continuous_snd)).abs

/-- The supremum of the absolute repeated index energy on the Hilbert cube is continuous in the
tensor. -/
theorem supCube_continuous (q N:ℕ) : Continuous (supCube (q:=q) (N:=N)) := by
  have hK:IsCompact (hilbertCube N) := isCompact_pi_infinite (fun _ : Fin N=>isCompact_Icc)
  exact hK.continuous_sSup (repeated_energy_continuous q N)

/-- The supremum `supCube A` is attained by a cube vector and bounds the absolute repeated index
energy of every cube vector. -/
theorem supCube_attained {q N:ℕ} (A:Tensor q N) :
    ∃u∈hilbertCube N,supCube A=|tensorEnergy (repeated A) u| ∧
      ∀v∈hilbertCube N,|tensorEnergy (repeated A) v| ≤ supCube A := by
  have hK:IsCompact (hilbertCube N) := isCompact_pi_infinite (fun _ : Fin N=>isCompact_Icc)
  have hne:(hilbertCube N).Nonempty := ⟨fun _=>0,fun _=>by constructor <;>norm_num⟩
  have hc:Continuous (fun u:Fin N→ℝ=>|tensorEnergy (repeated A) u|) :=
    (repeated_energy_continuous q N).comp (continuous_const.prodMk continuous_id)
  obtain ⟨u,hu,he,hmax⟩:=hK.exists_sSup_image_eq_and_ge hne hc.continuousOn
  exact ⟨u,hu,he,fun v hv=>(hmax v hv).trans_eq he.symm⟩

/-- The binary ground energy minus the cube minimum is nonnegative and has absolute value at
most `2 * supCube A`. -/
theorem actual_optimum_gap_le_sup {q N:ℕ} (A:Tensor q N) :
    0 ≤ binaryGround A-cubeOpt A ∧ |binaryGround A-cubeOpt A| ≤ 2*supCube A := by
  obtain ⟨u,hu,he,hmax⟩:=supCube_attained A
  have h:=optimum_gap_bound A (supCube A) hmax
  exact ⟨h.1,by simpa only [abs_of_nonneg h.1] using! h.2⟩

/-- For fixed `r` and `η > 0`, the probability that `supCube A` is at least `ηN` tends to zero
as `N` tends to infinity. -/
theorem actual_supCube_subextensive (r:ℕ) (η:ℝ) (hη:0 < η) :
    Tendsto (fun N:ℕ=>(gaussianTensorLaw r N).real {A|η*(N:ℝ) ≤ supCube A}) atTop (𝓝 0) := by
  have he (N:ℕ) : {A:Tensor (r+1) N|η*(N:ℝ) ≤ supCube A}=
      {A|∃u∈hilbertCube N,η*(N:ℝ) ≤ |tensorEnergy (repeated A) u|} := by
    ext A
    simp only [mem_setOf_eq]
    obtain ⟨u,hu,hmax,hbound⟩:=supCube_attained A
    constructor
    · intro h;exact ⟨u,hu,h.trans_eq hmax⟩
    · rintro ⟨v,hv,h⟩;exact h.trans (hbound v hv)
  simpa only [he,remainderProbability] using! actual_remainder_subextensive r η hη

/-- For fixed `r` and `η > 0`, the probability that the absolute difference between binary and
cube minimum energies exceeds `ηN` tends to zero. See [GohMuller2026]. -/
theorem actual_absolute_optimum_gap_subextensive (r:ℕ) (η:ℝ) (hη:0 < η) :
    Tendsto (fun N:ℕ=>(gaussianTensorLaw r N).real
      {A|η*(N:ℝ) < |binaryGround A-cubeOpt A|}) atTop (𝓝 0) := by
  have he (N:ℕ) : {A:Tensor (r+1) N|η*(N:ℝ) < |binaryGround A-cubeOpt A|}=
      {A|η*(N:ℝ) < binaryGround A-cubeOpt A} := by
    ext A
    simp only [mem_setOf_eq]
    rw [abs_of_nonneg (sub_nonneg.mpr (cubeOpt_le_binaryGround A))]
  simpa only [he] using! actual_optimum_gap_subextensive r η hη
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder
