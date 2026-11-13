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

/-!
# Application profiles for coherent reweighting

This module defines the norms, clipped inverse-eigenvalue profiles, overlap quantities, and
query budgets used in coherent reweighting. It also introduces Boolean hidden-shift profiles,
shift influences, and predicates for preservation of hidden-state families and bounded legal
gate words, in the quantum rejection-sampling framework of [OzolsRoettelerRoland2013].

## Main statements

* `qlsWTilde`: define the inverse-eigenvalue profile with a spectral cutoff.
* `bhspEps`: clip Fourier magnitudes at a uniform water level.
* `HiddenStateDiscipline`: state preservation of the hidden-state family by exact resampling.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity

set_option autoImplicit false

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

/-- The Euclidean norm of a finite real vector, defined as the square root of its sum of squared
coordinates. -/
noncomputable def l2Norm {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

/-- Replace each eigenvalue by its maximum with the cutoff `κTilde⁻¹`. -/
noncomputable def qlsLambdaTilde {n : ℕ} (κTilde : ℝ) (lam : Fin n → ℝ) : Fin n → ℝ :=
  fun j => max κTilde⁻¹ (lam j)

/-- The coordinatewise inverse-eigenvalue profile `b j / lam j`. -/
noncomputable def qlsW {n : ℕ} (b lam : Fin n → ℝ) : Fin n → ℝ :=
  fun j => b j / lam j

/-- The inverse-eigenvalue profile obtained by dividing each source coordinate by its cutoff
eigenvalue `qlsLambdaTilde κTilde lam j`. -/
noncomputable def qlsWTilde {n : ℕ} (b : Fin n → ℝ) (κTilde : ℝ) (lam : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j => b j / qlsLambdaTilde κTilde lam j

/-- The dot product of two real profiles divided by the product of their Euclidean norms. -/
noncomputable def qlsSuccess {n : ℕ} (w wTilde : Fin n → ℝ) : ℝ :=
  (∑ j, w j * wTilde j) / (l2Norm w * l2Norm wTilde)

/-- The query-budget expression `κTilde / l2Norm wTilde` for a clipped linear-system profile. -/
noncomputable def qlsQueryBudget {n : ℕ} (κTilde : ℝ) (wTilde : Fin n → ℝ) : ℝ :=
  κTilde / l2Norm wTilde

/-- The square of the normalized profile overlap `qlsSuccess w wTilde`. -/
noncomputable def qlsSuccessMass {n : ℕ} (w wTilde : Fin n → ℝ) : ℝ :=
  qlsSuccess w wTilde ^ 2

/-- The source-call count `2 * resamplingExactRounds β + 1` associated with the exact-resampling
schedule. -/
noncomputable def scheduledSourceCalls (β : ℝ) : ℕ :=
  2 * resamplingExactRounds β + 1

/-- A finite real weight vector for the Metropolis reweighting application. -/
structure MetropolisWeights (n : ℕ) where

  w : Fin n → ℝ

/-- The inverse Euclidean norm of the Metropolis weight vector. -/
noncomputable def metropolisQueryBudget {n : ℕ} (v : Fin n → ℝ) : ℝ := 1 / l2Norm v

/-- The coordinatewise absolute values of the Boolean hidden-shift Fourier coefficients. -/
noncomputable def bhspPi {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) : Fin (2 ^ n) → ℝ :=
  fun w => |fHat w|

/-- The constant target profile with amplitude `1 / Real.sqrt ((2 : ℝ) ^ n)`. -/
noncomputable def bhspFlatSigma (n : ℕ) : Fin (2 ^ n) → ℝ :=
  fun _ => (Real.sqrt ((2 : ℝ) ^ n))⁻¹

/-- Clip each Fourier magnitude at the uniform threshold `γ / Real.sqrt ((2 : ℝ) ^ n)`. -/
noncomputable def bhspEps {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : Fin (2 ^ n) → ℝ :=
  fun w => min |fHat w| (γ / Real.sqrt ((2 : ℝ) ^ n))

/-- The sum of the clipped Boolean hidden-shift profile coordinates. -/
noncomputable def bhspEpsL1 {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  ∑ w, bhspEps fHat γ w

/-- The Euclidean norm of the clipped Boolean hidden-shift profile. -/
noncomputable def bhspEpsNorm2 {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  l2Norm (bhspEps fHat γ)

/-- The coordinatewise Boolean exclusive-or of two registers. -/
def xorReg {n : ℕ} (x y : Reg n) : Reg n := fun i => x i != y i

/-- The fraction of Boolean inputs on which translation by `v` changes the value of `f`. -/
noncomputable def influenceAt (n : ℕ) (f : Reg n → Bool) (v : Reg n) : ℝ :=
  ((Finset.univ.filter (fun x : Reg n => f x ≠ f (xorReg x v))).card : ℝ) / (2 : ℝ) ^ n

/-- The infimum of the influences of `f` over all register shifts, including the all-false
shift. -/
noncomputable def minInfluence (n : ℕ) (f : Reg n → Bool) : ℝ :=
  ⨅ v : Reg n, influenceAt n f v

/-- The shift-test acceptance expression `1 - influenceAt n f (xorReg s v)`. -/
noncomputable def shiftTestAccept (n : ℕ) (f : Reg n → Bool) (s v : Reg n) : ℝ :=
  1 - influenceAt n f (xorReg s v)

/-- The dot product of the clipped Fourier-magnitude profile with the flat target profile. -/
noncomputable def bhspLevelDot {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  ∑ w, bhspEps fHat γ w * bhspFlatSigma n w

/-- The squared flat-target overlap equals `p` times the squared Euclidean norm of the clipped
profile. -/
noncomputable def bhspLevelSuccess {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ p : ℝ) : Prop :=
  bhspLevelDot fHat γ ^ 2 = p * bhspEpsNorm2 fHat γ ^ 2

/-- The inverse Euclidean norm of the clipped Boolean hidden-shift profile. -/
noncomputable def bhspQueryBudget {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  1 / bhspEpsNorm2 fHat γ

/-- The coordinate sum of the clipped Boolean hidden-shift profile, expressed through
`bhspEpsL1`. -/
noncomputable def bhspProfileMass {n : ℕ} (fHat : Fin (2 ^ n) → ℝ) (γ : ℝ) : ℝ :=
  bhspEpsL1 fHat γ

/-- The sum of the inverse clipped-profile norm and inverse square root of `I`, multiplied by `1
/ Real.sqrt p`. -/
noncomputable def bhspEnhancedBudget {n : ℕ} (p : ℝ) (fHat : Fin (2 ^ n) → ℝ)
    (γ I : ℝ) : ℝ :=
  (1 / Real.sqrt p) * (1 / bhspEpsNorm2 fHat γ + 1 / Real.sqrt I)

/-- The combined scheduled source-call counts for the clipped-profile norm and square root of
the minimum influence, scaled by `1 / Real.sqrt p`. -/
noncomputable def bhspEnhancedCalls {n : ℕ} (p : ℝ) (fHat : Fin (2 ^ n) → ℝ)
    (γ : ℝ) (f : Reg n → Bool) : ℝ :=
  (1 / Real.sqrt p) *
    ((scheduledSourceCalls (bhspEpsNorm2 fHat γ) : ℝ) +
      (scheduledSourceCalls (Real.sqrt (minInfluence n f)) : ℝ))

/-- For normalized nonnegative profiles, positive filled mass, and a unitary source preparation,
exact resampling can be expressed using real coefficients and the original normalized hidden
states. -/
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

/-- The integer workspace allowance `2 * m * b` for a table with `m` entries and bit parameter
`b`. -/
def reweightingIntegerBits (m b : ℕ) : ℕ := 2 * m * b

/-- For every positive supplied tolerance, a legal finite gate word exists with the stated
bounds on word length and workspace. -/
def HasReweightingFixedGateBackend (m D : ℕ) (π σ : Fin m → ℚ) (γ a : ℝ)
    (tableBits : ℕ) (ε : ℝ) : Prop :=
  0 < ε →
    ∃ (w : ℕ) (gs : List FiniteGateCode),
      finiteWordLegal w gs = true ∧
        gs.length ≤
          (16 * m * D + 64) * (Nat.ceil ((1 / ε) ^ 2) + 1) ∧
        w ≤ D + Nat.clog 2 (max 2 m) + reweightingIntegerBits m tableBits + 8

end Qatlib.Concepts.Waterfill.LevelFidelity
