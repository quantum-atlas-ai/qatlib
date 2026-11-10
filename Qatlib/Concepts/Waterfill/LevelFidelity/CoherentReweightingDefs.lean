/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Qatlib.Concepts.Waterfill.ExactResampling.ExactResamplingUpperQuan
import Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.Waterfill.ExactResampling

namespace Qatlib.Concepts.Waterfill.LevelFidelity

open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

noncomputable def qlsLambdaTilde {n : ℕ} (κTilde : ℝ) (lam : Fin n → ℝ) : Fin n → ℝ :=
  fun j => max κTilde⁻¹ (lam j)

noncomputable def qlsW {n : ℕ} (b lam : Fin n → ℝ) : Fin n → ℝ :=
  fun j => b j / lam j

noncomputable def qlsWTilde {n : ℕ} (b : Fin n → ℝ) (κTilde : ℝ) (lam : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j => b j / qlsLambdaTilde κTilde lam j

noncomputable def qlsSuccess {n : ℕ} (w wTilde : Fin n → ℝ) : ℝ :=
  (∑ j, w j * wTilde j) / (l2Norm w * l2Norm wTilde)

noncomputable def qlsQueryBudget {n : ℕ} (κTilde : ℝ) (wTilde : Fin n → ℝ) : ℝ :=
  κTilde / l2Norm wTilde

noncomputable def qlsSuccessMass {n : ℕ} (w wTilde : Fin n → ℝ) : ℝ :=
  qlsSuccess w wTilde ^ 2

noncomputable def scheduledSourceCalls (β : ℝ) : ℕ :=
  2 * resamplingExactRounds β + 1

structure MetropolisWeights (n : ℕ) where

  w : Fin n → ℝ

noncomputable def metropolisQueryBudget {n : ℕ} (v : Fin n → ℝ) : ℝ := 1 / l2Norm v

noncomputable def bhspPi {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) : Fin (2 ^ n) → ℝ :=
  fun w => |fHat w|

noncomputable def bhspFlatSigma (n : ℕ) : Fin (2 ^ n) → ℝ :=
  fun _ => (Real.sqrt ((2 : ℝ) ^ n))⁻¹

noncomputable def bhspEps {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : Fin (2 ^ n) → ℝ :=
  fun w => min |fHat w| (γ / Real.sqrt ((2 : ℝ) ^ n))

noncomputable def bhspEpsL1 {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  ∑ w, bhspEps fHat γ w

noncomputable def bhspEpsNorm2 {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  l2Norm (bhspEps fHat γ)

def xorReg {n : ℕ} (x y : Reg n) : Reg n := fun i => x i != y i

noncomputable def influenceAt (n : ℕ) (f : Reg n → Bool) (v : Reg n) : ℝ :=
  ((Finset.univ.filter (fun x : Reg n => f x ≠ f (xorReg x v))).card : ℝ) / (2 : ℝ) ^ n

noncomputable def minInfluence (n : ℕ) (f : Reg n → Bool) : ℝ :=
  ⨅ v : Reg n, influenceAt n f v

noncomputable def shiftTestAccept (n : ℕ) (f : Reg n → Bool) (s v : Reg n) : ℝ :=
  1 - influenceAt n f (xorReg s v)

noncomputable def bhspLevelDot {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  ∑ w, bhspEps fHat γ w * bhspFlatSigma n w

noncomputable def bhspLevelSuccess {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ p : ℝ) : Prop :=
  bhspLevelDot fHat γ ^ 2 = p * bhspEpsNorm2 fHat γ ^ 2

noncomputable def bhspQueryBudget {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  1 / bhspEpsNorm2 fHat γ

noncomputable def bhspProfileMass {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  bhspEpsL1 fHat γ

noncomputable def bhspEnhancedBudget {n : ℕ} (p : ℝ) (fHat : Fin (2 ^ n) → ℝ)
    (γ I : ℝ) : ℝ :=
  (1 / Real.sqrt p) * (1 / bhspEpsNorm2 fHat γ + 1 / Real.sqrt I)

noncomputable def bhspEnhancedCalls {n : ℕ} (p : ℝ) (fHat : Fin (2 ^ n) → ℝ)
    (γ : ℝ) (f : Reg n → Bool) : ℝ :=
  (1 / Real.sqrt p) *
    ((scheduledSourceCalls (bhspEpsNorm2 fHat γ) : ℝ) +
      (scheduledSourceCalls (Real.sqrt (minInfluence n f)) : ℝ))

def HiddenStateDiscipline {m D : ℕ} (π σ : Fin m → ℚ) (γ : ℝ)
    (U : Matrix (Fin m × Fin D) (Fin m × Fin D) ℂ) (j₀ : Fin m × Fin D)
    (ξ : Fin m → QState (Fin D)) : Prop :=
  (∀ i, 0 ≤ π i ∧ 0 ≤ σ i) → 0 ≤ γ →
    (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
    0 < levelMass π σ γ →
    (∀ i, Normalized (ξ i)) →
    U ∈ Matrix.unitaryGroup _ ℂ →
    U *ᵥ Ket j₀ = waterSource π ξ →
      ∃ v : Fin m → ℝ,
        resamplingExactOutput π σ γ U j₀ = resamplingFamily v ξ

def reweightingIntegerBits (m b : ℕ) : ℕ := 2 * m * b

def HasReweightingFixedGateBackend (m D : ℕ) (π σ : Fin m → ℚ) (γ a : ℝ)
    (tableBits : ℕ) (ε : ℝ) : Prop :=
  0 < ε →
    ∃ (w : ℕ) (gs : List FiniteGateCode),
      finiteWordLegal w gs = true ∧
        gs.length ≤
          (16 * m * D + 64) * (Nat.ceil ((1 / ε) ^ 2) + 1) ∧
        w ≤ D + Nat.clog 2 (max 2 m) + reweightingIntegerBits m tableBits + 8

end Qatlib.Concepts.Waterfill.LevelFidelity
