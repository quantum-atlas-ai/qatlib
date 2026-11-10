/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.DirichletForm.KmsDirichlet.KmsInnerProduct
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.SchattenDiamond.DiamondNorm

namespace Qatlib.Concepts.GkslBridge.GkslBridge

open Matrix
open scoped Classical BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

local instance clmSeminormedRing {D : ℕ} :
    SeminormedRing (Operator D →L[ℂ] Operator D) :=
  ContinuousLinearMap.toSeminormedRing

local instance clmNormedAlgebra {D : ℕ} :
    NormedAlgebra ℂ (Operator D →L[ℂ] Operator D) :=
  ContinuousLinearMap.toNormedAlgebra

local instance clmIsTopologicalRing {D : ℕ} :
    IsTopologicalRing (Operator D →L[ℂ] Operator D) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

variable {D : ℕ}

structure GKSLData (D m : ℕ) where

  ham : Operator D

  jumps : Fin m → Operator D

noncomputable def gkslMap {D m : ℕ} (G : GKSLData D m) : Operator D →ₗ[ℂ] Operator D :=
  (-Complex.I : ℂ) • (LinearMap.mulLeft ℂ G.ham - LinearMap.mulRight ℂ G.ham) +
    ∑ a : Fin m,
      ((LinearMap.mulLeft ℂ (G.jumps a)).comp (LinearMap.mulRight ℂ (G.jumps a)ᴴ) -
        (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ ((G.jumps a)ᴴ * G.jumps a) +
          LinearMap.mulRight ℂ ((G.jumps a)ᴴ * G.jumps a)))

noncomputable def gkslCLM {D m : ℕ} (G : GKSLData D m) : Operator D →L[ℂ] Operator D :=
  (gkslMap G).toContinuousLinearMap

noncomputable def evolveAt {D m : ℕ} (G : GKSLData D m) (t : ℝ) (ρ : Operator D) :
    Operator D :=
  NormedSpace.exp ((t : ℂ) • gkslCLM G) ρ

noncomputable def evolveMap {D m : ℕ} (G : GKSLData D m) (t : ℝ) :
    Operator D →ₗ[ℂ] Operator D :=
  (NormedSpace.exp ((t : ℂ) • gkslCLM G) : Operator D →L[ℂ] Operator D).toLinearMap

def gkslStationary {D m : ℕ} (G : GKSLData D m) (ρ : Operator D) : Prop :=
  IsDensityOperator ρ ∧ gkslMap G ρ = 0

noncomputable def thermalMixingTime {D m : ℕ} (G : GKSLData D m) : ℝ :=
  sInf {t : ℝ | ∃ ρstar : Operator D, gkslStationary G ρstar ∧
    ∀ s ∈ Set.Ici t, ∀ ρ : Operator D, IsDensityOperator ρ →
      SchattenOne (evolveAt G s ρ - ρstar) ≤ 1 / 2}

noncomputable def gibbsDensity {D : ℕ} (H : Operator D) (β : ℝ) : Operator D :=
  (Matrix.trace (NormedSpace.exp (-(β) • H)))⁻¹ • NormedSpace.exp (-(β) • H)

def boxWindowFilter (T _w : ℝ) : ℝ → ℝ :=
  fun t => if t ≤ T then 1 else 0

noncomputable def boxFilteredFixedPoint {D m : ℕ} (G : GKSLData D m) (Twindow : ℝ)
    (ρ₀ : Operator D) : Operator D :=
  (Twindow ⁻¹ : ℝ) • ∫ s in 0..Twindow, evolveAt G s ρ₀

def WeakBathDetailedBalance {D m : ℕ} (G : GKSLData D m) (β : ℝ) : Prop :=
  G.ham.IsHermitian ∧ 0 < β ∧ ∀ a : Fin m,
    (G.jumps a)ᴴ * CFC.sqrt (gibbsDensity G.ham β) =
      CFC.sqrt (gibbsDensity G.ham β) * G.jumps a

def ThermalThI1Spec : Prop :=
  ∀ (D m : ℕ) (G : GKSLData D m) (β Twindow t : ℝ) (ρ₀ : Operator D),
    WeakBathDetailedBalance G β → 0 < Twindow → gkslStationary G ρ₀ →
    Twindow ≤ t →
    SchattenOne (boxFilteredFixedPoint G Twindow ρ₀ - gibbsDensity G.ham β) ≤
      4 * Real.sqrt (β / Twindow) * thermalMixingTime G

def gaussianJumpWeights (σt _β : ℝ) : ℝ → ℝ → ℝ :=
  fun Ei Ej => Real.exp (-(Ei - Ej) ^ 2 / (2 * σt ^ 2))

def GaussianMetropolisBath {D m : ℕ} (G : GKSLData D m) (σt β : ℝ) : Prop :=
  (∀ i j : Fin D, i ≠ j → G.ham i j = 0) ∧
    ∀ a : Fin m, ∀ i j : Fin D,
      (G.jumps a) i j = Complex.ofReal
        (gaussianJumpWeights σt β (G.ham i i).re (G.ham j j).re)

def ThermalThI3Spec : Prop :=
  ∀ (D m : ℕ) (G : GKSLData D m) (σt β Twindow t : ℝ) (ρ₀ : Operator D),
    GaussianMetropolisBath G σt β → 0 < σt → 0 < β → 0 < Twindow →
    gkslStationary G ρ₀ → Twindow ≤ t →
    SchattenOne (boxFilteredFixedPoint G Twindow ρ₀ - gibbsDensity G.ham β) ≤
      16 * (β / σt) * thermalMixingTime G

def BlockUnitaryLindbladian {D m : ℕ} (G : GKSLData D m) (_c : ℕ) : Prop :=
  G.ham = 0 ∧ ∀ a : Fin m, ∃ φ ψ : Fin D → ℂ,
    ‖toEuclidean_fromVec φ‖ = 1 ∧ ‖toEuclidean_fromVec ψ‖ = 1 ∧
      ∀ i j : Fin D, (G.jumps a) i j = φ i * (starRingEnd ℂ) (ψ j)

def ThermalThI2Spec : Prop :=
  ∀ (D m : ℕ) (G : GKSLData D m) (c : ℕ) (t ε : ℝ),
    BlockUnitaryLindbladian G c → 1 < t → 0 < ε → ε ≤ 1 / 2 →
    ∃ (sim : Operator D →ₗ[ℂ] Operator D) (calls gates ancilla : ℕ),
      (finiteDiamondDistance sim (evolveMap G t) ≤ ENNReal.ofReal ε) ∧
      (calls ≤ Nat.ceil (16 * t * (Real.logb 2 (1 / ε)) ^ 2)) ∧
      (gates ≤ Nat.ceil (16 * t * ((c : ℝ) + 1) * (Real.logb 2 (1 / ε)) ^ 2)) ∧
      (ancilla ≤ Nat.ceil (4 * Real.logb 2 (1 / ε)))

def purifiedHalfIndex {D : ℕ} (i : Fin (2 * D)) : Fin D :=
  ⟨if i.val < D then i.val else i.val - D,
    by
      by_cases h : i.val < D
      · simp only [if_pos h]
        exact h
      · simp only [if_neg h]
        have h2 := i.isLt
        omega⟩

def hamEnergy {D m : ℕ} (G : GKSLData D m) (i : Fin D) : ℝ :=
  (G.ham i i).re

noncomputable def purifiedProxyDiscriminant {D m : ℕ} (G : GKSLData D m) (σt β : ℝ) :
    Operator (2 * D) :=
  Matrix.of fun i j =>
    if i.val < D then
      if j.val < D then
        Complex.ofReal (gaussianJumpWeights σt β (hamEnergy G (purifiedHalfIndex i))
          (hamEnergy G (purifiedHalfIndex j)))
      else
        Complex.ofReal (Real.exp (-β * hamEnergy G (purifiedHalfIndex i) / 2)) *
          ∑ a : Fin m, G.jumps a (purifiedHalfIndex i) (purifiedHalfIndex j)
    else
      if j.val < D then
        Complex.ofReal (Real.exp (-β * hamEnergy G (purifiedHalfIndex j) / 2)) *
          (starRingEnd ℂ)
            (∑ a : Fin m, G.jumps a (purifiedHalfIndex j) (purifiedHalfIndex i))
      else 0

noncomputable def purifiedGibbsVector {D : ℕ} (H : Operator D) (β : ℝ) :
    Fin (2 * D) → ℂ :=
  fun i => if i.val < D then
    CFC.sqrt (gibbsDensity H β) (purifiedHalfIndex i) (purifiedHalfIndex i) else 0

def ProxySpectralGap {D : ℕ} (Dβ : Operator (2 * D)) (v : Fin (2 * D) → ℂ)
    (lam γ : ℝ) : Prop :=
  Dβ.IsHermitian ∧ ‖toEuclidean_fromVec v‖ = 1 ∧
    (∀ i : Fin (2 * D), (Dβ *ᵥ v) i = (lam : ℂ) * v i) ∧ 0 < γ ∧
    ∀ w : Fin (2 * D) → ℂ, (∑ i, (starRingEnd ℂ) (v i) * w i = 0) →
      ‖toEuclidean_fromVec w‖ = 1 →
      Complex.re (∑ i, (starRingEnd ℂ) (w i) * (Dβ *ᵥ w) i) ≤ lam - γ

def ThermalThI4Spec : Prop :=
  ∀ (D m : ℕ) (G : GKSLData D m) (σt β : ℝ),
    GaussianMetropolisBath G σt β → 0 < σt → 0 < β →
    ∃ lam γ : ℝ, ProxySpectralGap (purifiedProxyDiscriminant G σt β)
        (purifiedGibbsVector G.ham β) lam γ ∧
      ∀ v : Fin (2 * D) → ℂ,
        ‖toEuclidean_fromVec v‖ = 1 →
          (∀ i : Fin (2 * D), (purifiedProxyDiscriminant G σt β *ᵥ v) i =
            (lam : ℂ) * v i) →
          ‖toEuclidean_fromVec v - toEuclidean_fromVec (purifiedGibbsVector G.ham β)‖ ≤
            (β / (σt * γ)) * 4

end Qatlib.Concepts.GkslBridge.GkslBridge
