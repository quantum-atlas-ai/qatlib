/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroup
import Qatlib.Concepts.GkslBridge.GkslBridge.QuantumMixingSourceBoundsDefs
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDirichlet
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupEntropy
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupKmsMixing
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

open Qatlib.Concepts.LindbladFlow.GkslSemigroup

namespace Qatlib.Concepts.GkslBridge.GkslBridge
open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

def thermalData {D : ℕ} (G : GKSL D) : Qatlib.Concepts.GkslBridge.GkslBridge.GKSLData D (D * D) :=
  ⟨G.ham, G.jumps⟩

theorem generator_eq {D : ℕ} (G : GKSL D) :
    Qatlib.Concepts.GkslBridge.GkslBridge.gkslMap (thermalData G) = lindbladMap G := by
  apply LinearMap.ext
  intro X
  change Qatlib.Concepts.GkslBridge.GkslBridge.gkslMap (thermalData G) X = lindbladApply G X
  simp only [Qatlib.Concepts.GkslBridge.GkslBridge.gkslMap, thermalData, lindbladApply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, Matrix.mul_assoc]

theorem evolve_eq {D : ℕ} (G : GKSL D) (t : ℝ) (X : Operator D) :
    Qatlib.Concepts.GkslBridge.GkslBridge.evolveAt (thermalData G) t X = lindbladSemigroup G t X := by
  letI : NormedAddCommGroup (Operator D) := Matrix.instL2OpNormedAddCommGroup
  letI : NormedSpace ℂ (Operator D) := Matrix.instL2OpNormedSpace
  letI : TopologicalSpace (Operator D) :=
    (inferInstance : NormedAddCommGroup (Operator D)).toUniformSpace.toTopologicalSpace
  letI : Module ℂ (Operator D) := (inferInstance : NormedSpace ℂ (Operator D)).toModule
  let L : Operator D →L[ℂ] Operator D := LinearMap.toContinuousLinearMap (lindbladMap G)
  have hh := (ContinuousLinearMap.apply ℂ (Operator D) X).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((t : ℂ) • L))
  have ht (k : ℕ) :
      (ContinuousLinearMap.apply ℂ (Operator D) X)
          (((k.factorial : ℂ)⁻¹) • ((t : ℂ) • L) ^ k) =
        ((t : ℂ) ^ k / k.factorial) • ((lindbladMap G)^[k]) X := by
    change (((k.factorial : ℂ)⁻¹) • ((t : ℂ) • L) ^ k) X = _
    rw [ContinuousLinearMap.smul_apply]
    have hpow (k : ℕ) : ((t : ℂ) • L) ^ k = (t : ℂ) ^ k • L ^ k := by
      induction k with
      | zero => simp only [pow_zero, one_smul]
      | succ k ih =>
        rw [pow_succ, ih]
        ext Y
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
          map_smul, smul_smul, pow_succ, mul_comm]
    rw [hpow k, ContinuousLinearMap.smul_apply, smul_smul, ContinuousLinearMap.coe_pow']
    change ((k.factorial : ℂ)⁻¹ * (t : ℂ) ^ k) • ((lindbladMap G)^[k]) X = _
    rw [div_eq_mul_inv, mul_comm]
  simp only [ht] at hh
  have heq := hh.unique (lindbladSemigroup_hasSum G t X)
  simpa only [Qatlib.Concepts.GkslBridge.GkslBridge.evolveAt, Qatlib.Concepts.GkslBridge.GkslBridge.gkslCLM,
    generator_eq] using! heq

theorem g1 :
    ∀ (D : ℕ) (G : Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D),
      let T : Qatlib.Concepts.GkslBridge.GkslBridge.GKSLData D (D * D) := ⟨G.ham, G.jumps⟩
      Qatlib.Concepts.GkslBridge.GkslBridge.gkslMap T = Qatlib.Concepts.LindbladFlow.GkslSemigroup.lindbladMap G ∧
      ∀ (t : ℝ) (X : Operator D),
        Qatlib.Concepts.GkslBridge.GkslBridge.evolveAt T t X = Qatlib.Concepts.LindbladFlow.GkslSemigroup.lindbladSemigroup G t X := by
  intro D G
  exact ⟨generator_eq G, evolve_eq G⟩

theorem g2 :
    ∀ (D : ℕ) (G : Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D) (ρ : Operator D),
      IsDensityOperator ρ → ρ.PosDef →
      KmsSelfAdjoint ρ (Qatlib.Concepts.LindbladFlow.GkslSemigroup.gkslHeisenbergMap G) →
      ∀ γ : ℝ, KmsGapAtLeast ρ (Qatlib.Concepts.LindbladFlow.GkslSemigroup.gkslHeisenbergMap G) γ →
      ∀ (σ : Operator D), IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t →
      let T : Qatlib.Concepts.GkslBridge.GkslBridge.GKSLData D (D * D) := ⟨G.ham, G.jumps⟩
      Qatlib.Concepts.LindbladFlow.GkslSemigroup.traceDistance (Qatlib.Concepts.GkslBridge.GkslBridge.evolveAt T t σ) ρ ≤
        Real.exp (-γ * t) * kmsNorm ρ (Qatlib.Concepts.LindbladFlow.GkslSemigroup.kmsDensityRatio ρ (σ - ρ)) / 2 := by
  intro D G ρ hρ hfull hself γ hgap σ hσ t ht
  change traceDistance (Qatlib.Concepts.GkslBridge.GkslBridge.evolveAt (thermalData G) t σ) ρ ≤ _
  rw [evolve_eq]
  exact lindblad_traceDistance_le_of_heisenberg_kmsGap G hρ hfull hself γ hgap hσ t ht

end Qatlib.Concepts.GkslBridge.GkslBridge
