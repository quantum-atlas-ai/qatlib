/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.LchsRep.GeneralAnalyticKernelLchsStat
import Qatlib.Concepts.LchsSimulation.LchsRep.GeneralAnalyticLchsKernel


open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.LchsSimulation.LchsRep

open MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

theorem generalAnalyticKernelLchs : GeneralAnalyticKernelLchs := by
  intro I _ _ f L H s t hf hdecay hmass hL hH hPSD hHerm hst
  let F := fun z : ℂ=>orderedEvolution (fun u=>z • L u+Complex.I • H u) s t
  let U := fun k : ℝ=>orderedEvolution (fun u=>Complex.I • (H u+k • L u)) s t
  let w := fun k : ℝ=>f (k:ℂ)/(1-Complex.I*(k:ℂ))
  have hF := time_dependent_lchs_entire_parameter I L H s t hL hH hPSD hHerm hst
  have hb (k : ℝ) : F ((k:ℂ)*Complex.I)=U k := by
    dsimp [F,U]
    congr 1
    funext u
    rw [smul_add,← Complex.coe_smul,smul_smul,mul_comm]
    exact add_comm _ _
  have hUc : Continuous U := by
    have h :=
        hF.1.continuous.comp (Complex.continuous_ofReal.mul (continuous_const (y := Complex.I)))
    change Continuous (fun k : ℝ=>F ((k:ℂ)*Complex.I)) at h
    simpa only [hb] using! h
  have hUu (k : ℝ) : U k∈Matrix.unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u=>H u+k • L u)
      (by fun_prop)
      (fun u=>(hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all k))) s t
  obtain ⟨α,C,hα,hC,hd⟩ := hdecay
  have hw : Integrable w := power_kernel_weight_integrable f α C hα hC hf hd
  have hwc : Continuous w := power_kernel_weight_continuous f hf
  have hwUc : Continuous (fun k : ℝ => w k • U k) := by fun_prop
  have hi : Integrable (fun k : ℝ=>w k • U k) := by
    apply hw.norm.mono' hwUc.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun k=>by
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (l2_norm_unitary_le_one (hUu k)))
  constructor
  · intro i j
    have hwUij : Continuous (fun k : ℝ => w k * U k i j) := by
      have := hUc.matrix_elem i j
      fun_prop
    apply hw.norm.mono' hwUij.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun k=>by
      change ‖w k*U k i j‖≤‖w k‖
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary (hUu k) i j))
  · have he := general_kernel_entire_reproducing f F hf ⟨α,C,hα,hC,hd⟩ hF.1 hF.2
      (by simpa only [hb] using! hi)
    have hFone : F 1=orderedEvolution (fun u=>L u+Complex.I • H u) s t := by simp [F]
    simpa only [hb,hmass,one_smul,hFone] using! he

theorem generalAnalyticKernelLchs_principalPower :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (β : ℝ) (L H : ℝ → Matrix I I ℂ)
    (s t : ℝ),
    0 < β → β < 1 →
    Continuous L → Continuous H →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t →
      (∀ i j : I, Integrable (fun k : ℝ => highKernelG β k *
          (orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t) i j)) ∧
      (∫ k : ℝ, highKernelG β k •
          orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t) =
        orderedEvolution (fun u => L u + Complex.I • H u) s t  := by
  intro I _ _ β L H s t hβ hβ1 hL hH hPSD hHerm hst
  have hn := near_exponential_kernel_analytic_normalization β hβ hβ1
  have he := generalAnalyticKernelLchs I (highKernelF β) L H s t
    (by intro z hz;exact (highKernelF_analyticAt β z hz).differentiableAt.differentiableWithinAt)
    ⟨1,(1/(β*Real.cos (β*Real.pi/2)))^(1/β)/highKernelC β,by norm_num,
      by have hC:=highKernelC_pos β;have hc:=highKernel_cos_pos β hβ hβ1;positivity,
      highKernelF_power_decay β 1 hβ hβ1 (by norm_num)⟩
    hn.2.2.2 hL hH hPSD hHerm hst
  exact he

end Qatlib.Concepts.LchsSimulation.LchsRep
