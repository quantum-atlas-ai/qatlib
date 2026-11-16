/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
public import Qatlib.Papers.LinearOptics10.StockmeyerSrc.Defs

@[expose] public section


/-! # Actual finite-coin sampler and historical reduction contracts

Fixed source: Aaronson--Arkhipov, arXiv:1011.3245v1. Historical
contracts are preserved for explicit review; their names do not certify
efficient algorithms or source-level complexity theorems.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix Classical
open MeasureTheory
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.CountingClasses.ClassTransport
open Qatlib.Papers.LinearOptics10.StockmeyerSrc
namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc.SamplingModel


/-- The actual finite uniform seed law agrees pointwise with the permanent occupation weight. -/
def SamplesExactly {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (Sam : LoSampler m n) : Prop :=
  ∀ S : FockOccupation m n, loSamplerDist Sam S = bosonWeight A S

/-- The old all-isometry finite-coin exact sampler contract has no machine cost or input encoding. -/
def ExactClassical : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 →
    ∃ Sam : LoSampler m n, SamplesExactly A Sam

/-- The old arbitrary-accuracy finite-coin sampling contract has no uniform cost bound. -/
def ApproxClassical : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), Aᴴ * A = 1 → ∀ ε : ℝ, 0 < ε →
    ∃ Sam : LoSampler m n, loTvDist (loSamplerDist Sam) (bosonWeight A) < ε

/-- The historical name is literally the general counting-class containment predicate; it does not encode a Gaussian estimation problem. -/
def GpeEstimable : Prop := SharpPContainedInBPPNP

/-- The genuine squared magnitude of the matrix permanent as an estimator value. -/
noncomputable def gpeSq : EstimatorProblem where
  Val := fun _ X => Complex.normSq (Matrix.permanent X)

/-- The genuine norm of the matrix permanent as an estimator value. -/
noncomputable def gpeAbs : EstimatorProblem where
  Val := fun _ X => ‖Matrix.permanent X‖

/-- The old reduction compares both estimator values at the same freely chosen reduced matrix; it does not relate that matrix to an original instance. -/
def Multiplicative (P Q : EstimatorProblem) : Prop :=
  ∀ (g : ℕ → ℝ), (∃ c : ℕ, ∀ L : ℕ, g L ≤ (L : ℝ) ^ c + 1) →
    ∃ (d : ℕ → ℕ)
      (red : (x : List Bool) → Matrix (Fin (d x.length)) (Fin (d x.length)) ℂ),
      (∃ c : ℕ, ∀ L : ℕ, d L ≤ L ^ c + 1) ∧
      ∀ (x : List Bool) (y : ℝ),
        |y - Q.Val (d x.length) (red x)|
            ≤ (g x.length - 1) * |Q.Val (d x.length) (red x)| →
          |y - P.Val (d x.length) (red x)|
            ≤ (g x.length - 1) * |P.Val (d x.length) (red x)|

/-- Both directions of the historical same-reduced-matrix comparison predicate. -/
def GpeEquiv : Prop :=
  Multiplicative gpeSq gpeAbs ∧ Multiplicative gpeAbs gpeSq

/-- An actual finite-bit exact sampler exists for the given matrix weight. -/
def BosonExact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∃ Sam : LoSampler m n, SamplesExactly A Sam

/-- For every positive tolerance some finite-bit sampler approximates the given matrix weight. -/
def BosonApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Sam : LoSampler m n,
    loTvDist (loSamplerDist Sam) (bosonWeight A) ≤ ε

/-- An actual exact sampler has zero variation error and therefore meets every positive tolerance. -/
theorem exactToApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    BosonExact A → BosonApprox A := by
  rintro ⟨Sam, hSam⟩ ε hε
  refine ⟨Sam, ?_⟩
  have hzero : loTvDist (loSamplerDist Sam) (bosonWeight A) = 0 := by
    have h : ∀ i : FockOccupation m n, loSamplerDist Sam i - bosonWeight A i = 0 :=
      fun i => by rw [hSam i, sub_self]
    unfold loTvDist
    simp [h]
  rw [hzero]
  exact le_of_lt hε

end Qatlib.Papers.LinearOptics10.StockmeyerSrc.SamplingModel
