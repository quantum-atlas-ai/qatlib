/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCoreDefs
import QuantumInfo.Channels.Unbundled
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.MeasuredMetropolisChannel
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.ODE.Gronwall
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.Entropy.DPI
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false

open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Filter
open scoped Topology

noncomputable def lindbladCPTPMap {D : ℕ} (G : GKSL D) (t : ℝ) (ht : 0 ≤ t) :
    CPTPMap (Fin D) (Fin D) where
  toLinearMap := lindbladSemigroupMap G t ht
  cp := lindbladSemigroupMap_cp G t ht
  TP := trace_lindbladSemigroup G t

theorem relativeEntropy_eq_qRelativeEnt {D : ℕ} {σ ρ : Operator D}
    (hσ : IsDensityOperator σ) (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) :
    relativeEntropy σ ρ = (qRelativeEnt
      (Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨σ,hσ⟩)
      (Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨ρ,hρ⟩)).toReal := by
  let s := Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨σ,hσ⟩
  let r := Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨ρ,hρ⟩
  have hf : r.M.NonSingular := HermitianMat.nonSingular_of_posDef hfull
  have hk : r.M.ker ≤ s.M.ker := by
    letI := hf
    rw [HermitianMat.nonSingular_ker_bot]
    exact bot_le
  change relativeEntropy σ ρ = (qRelativeEnt s r).toReal
  simp only [qRelativeEnt, SandwichedRelRentropy, zero_lt_one, hk, ↓reduceIte]
  rfl

theorem lindbladSemigroup_relativeEntropy_le {D : ℕ} (G : GKSL D) {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hfull : ρ.PosDef) (hstationary : IsStationary G ρ)
    (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤ relativeEntropy σ ρ := by
  let r := Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨ρ,hρ⟩
  let s := Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState (Fin D) ⟨σ,hσ⟩
  let Φ := lindbladCPTPMap G t ht
  have hτ := lindbladSemigroup_isDensityOperator G t ht σ hσ
  let τ :=
      Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState
      (Fin D) ⟨lindbladSemigroup G t σ,hτ⟩
  have hsr : Φ r = r := by
    apply MState.ext_m
    change lindbladSemigroup G t ρ = ρ
    exact hstationary t ht
  have hss : Φ s = τ := by
    apply MState.ext_m
    rfl
  have h := sandwichedRenyiEntropy_DPI_eq_one s r Φ
  change qRelativeEnt (Φ s) (Φ r) ≤ qRelativeEnt s r at h
  rw [hsr, hss] at h
  letI : r.M.NonSingular := HermitianMat.nonSingular_of_posDef hfull
  have hn : qRelativeEnt s r ≠ ⊤ := qRelativeEnt_ne_top
  have hr := ENNReal.toReal_mono hn h
  change (qRelativeEnt τ r).toReal ≤ (qRelativeEnt s r).toReal at hr
  rw [← relativeEntropy_eq_qRelativeEnt hτ hρ hfull,
    ← relativeEntropy_eq_qRelativeEnt hσ hρ hfull] at hr
  exact hr

theorem kmsNormalForm_relativeEntropy_le {D : ℕ} (G : GKSL D) {ρ σ : Operator D}
    (hnormal : KMSNormalForm G ρ) (hσ : IsDensityOperator σ) (t : ℝ) (ht : 0 ≤ t) :
    relativeEntropy (lindbladSemigroup G t σ) ρ ≤ relativeEntropy σ ρ :=
  lindbladSemigroup_relativeEntropy_le G hnormal.1 hnormal.2.1
    (stationary_of_kmsNormalForm G ρ hnormal) hσ t ht
end Qatlib.Concepts.LindbladFlow.GkslSemigroup
