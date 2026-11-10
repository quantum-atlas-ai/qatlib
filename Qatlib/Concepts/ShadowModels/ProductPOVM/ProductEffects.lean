/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ProductPOVM.PartitionPauli
import Qatlib.Foundations.FiniteStats.BornEstimator.MeasurementScore
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators
open Qatlib.Foundations.FiniteStats.BornEstimator
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.PureStateMath
variable {J Ω : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] {N : ℕ} (sizes : J → ℕ)

def PhysicalProductPOVM (sites : Fin N ≃ Σ j,Fin (sizes j)) (P : POVM Ω (Reg N)) : Prop :=
  ∀ s,∃ a : ℝ,0 ≤ a ∧ ∃ ρ : ∀ j,MState (Reg (sizes j)),P.mats s=a • (partitionState sizes sites ρ).M

theorem normalize_scaled_product (sites : Fin N ≃ Σ j,Fin (sizes j))
    (ρ : ∀ j,MState (Reg (sizes j))) (a : ℝ) (E : HermitianMat (Reg N) ℂ)
    (hE : 0 ≤ E) (hne : E≠0) (he : E=a • (partitionState sizes sites ρ).M) :
    normalizedEffect E hE hne=partitionState sizes sites ρ := by
  have ha : a≠0 := by intro hz;apply hne;rw [he,hz,zero_smul]
  have ht : E.trace=a := by rw [he,HermitianMat.trace_smul,MState.tr,mul_one]
  apply MState.ext_m
  have hm : (normalizedEffect E hE hne).M=(partitionState sizes sites ρ).M := by
    change E.trace⁻¹ • E=_
    rw [ht,he,smul_smul,inv_mul_cancel₀ ha,one_smul]
  exact congrArg HermitianMat.mat hm

theorem physical_product_normalized (sites : Fin N ≃ Σ j,Fin (sizes j)) (P : POVM Ω (Reg N))
    (hP : PhysicalProductPOVM sizes sites P) (s : Ω) (hne : P.mats s≠0) :
    normalizedEffect (P.mats s) (P.nonneg s) hne∈partitionStates sizes sites := by
  obtain ⟨a,_,ρ,he⟩ := hP s
  rw [normalize_scaled_product sizes sites ρ a _ (P.nonneg s) hne he]
  exact ⟨ρ,rfl⟩

theorem normalized_product_physical (sites : Fin N ≃ Σ j,Fin (sizes j)) (P : POVM Ω (Reg N))
    (hP : ∀ s (hne : P.mats s≠0),normalizedEffect (P.mats s) (P.nonneg s) hne∈partitionStates sizes sites) :
    PhysicalProductPOVM sizes sites P := by
  intro s
  by_cases he : P.mats s=0
  · exact ⟨0,le_rfl,fun _ => MState.uniform,by rw [he,zero_smul]⟩
  · obtain ⟨ρ,hρ⟩ := hP s he
    refine ⟨(P.mats s).trace,HermitianMat.trace_nonneg (P.nonneg s),ρ,?_⟩
    have hm := congrArg MState.M hρ
    rw [hm]
    change P.mats s=(P.mats s).trace • ((P.mats s).trace⁻¹ • P.mats s)
    rw [smul_smul,mul_inv_cancel₀ (effect_trace_pos _ (P.nonneg s) he).ne',one_smul]

theorem pauliOrbit_physical_product (sites : Fin N ≃ Σ j,Fin (sizes j))
    (ρ : ∀ j,MState (Reg (sizes j))) : PhysicalProductPOVM sizes sites (pauliOrbitPOVM N (partitionState sizes sites ρ)) := by
  intro q
  refine ⟨(qubitDimension N)⁻¹,inv_nonneg.mpr (qubitDimension_pos N).le,
    fun j => pauliConjugateState (sizes j) (partitionWord sizes sites q j) (ρ j),?_⟩
  change (qubitDimension N)⁻¹ • (pauliConjugateState N q (partitionState sizes sites ρ)).M=_
  rw [partitionState_conjugate]

end Qatlib.Concepts.ShadowModels.ProductPOVM
