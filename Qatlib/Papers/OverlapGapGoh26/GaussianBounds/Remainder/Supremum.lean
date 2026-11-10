/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Remainder.Limit
set_option warningAsError false
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

def supCube {q N:ℕ} (A:Tensor q N) : ℝ :=
    sSup ((fun u=>|tensorEnergy (repeated A) u|) '' hilbertCube N)

theorem repeated_energy_continuous (q N:ℕ) :
    Continuous (fun p:Tensor q N×(Fin N→ℝ)=>|tensorEnergy (repeated p.1) p.2|) := by
  have hr:Continuous (repeated (q:=q) (N:=N)) := by
    apply continuous_pi
    intro k
    by_cases hk:Function.Injective k <;>simp only [repeated,hk,if_true,if_false] <;>fun_prop
  exact (continuous_tensorEnergy.comp ((hr.comp continuous_fst).prodMk continuous_snd)).abs

theorem supCube_continuous (q N:ℕ) : Continuous (supCube (q:=q) (N:=N)) := by
  have hK:IsCompact (hilbertCube N) := isCompact_pi_infinite (fun _ : Fin N=>isCompact_Icc)
  exact hK.continuous_sSup (repeated_energy_continuous q N)

theorem supCube_attained {q N:ℕ} (A:Tensor q N) :
    ∃u∈hilbertCube N,supCube A=|tensorEnergy (repeated A) u| ∧
      ∀v∈hilbertCube N,|tensorEnergy (repeated A) v| ≤ supCube A := by
  have hK:IsCompact (hilbertCube N) := isCompact_pi_infinite (fun _ : Fin N=>isCompact_Icc)
  have hne:(hilbertCube N).Nonempty := ⟨fun _=>0,fun _=>by constructor <;>norm_num⟩
  have hc:Continuous (fun u:Fin N→ℝ=>|tensorEnergy (repeated A) u|) :=
    (repeated_energy_continuous q N).comp (continuous_const.prodMk continuous_id)
  obtain ⟨u,hu,he,hmax⟩:=hK.exists_sSup_image_eq_and_ge hne hc.continuousOn
  exact ⟨u,hu,he,fun v hv=>(hmax v hv).trans_eq he.symm⟩

theorem actual_optimum_gap_le_sup {q N:ℕ} (A:Tensor q N) :
    0 ≤ binaryGround A-cubeOpt A ∧ |binaryGround A-cubeOpt A| ≤ 2*supCube A := by
  obtain ⟨u,hu,he,hmax⟩:=supCube_attained A
  have h:=optimum_gap_bound A (supCube A) hmax
  exact ⟨h.1,by simpa only [abs_of_nonneg h.1] using! h.2⟩

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
