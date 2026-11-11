/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.CertaintyMethodSlowdownQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma1RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem3QuadraticSpeedupUnknownAQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Search

/-!
# Certainty branches and generalized amplification projectors

This module separates integral and nonintegral stopping cases for the certainty method of
[BrassardHoyerTapp1998Counting]. `nextCertaintyProgram_success` proves exact marked mass using
ordinary iterations in the integral case and a final phase adjustment in the nonintegral case.

`NextZeroProjector` extends the iterate to any self-adjoint idempotent matrix. The module gives
its action identities, recovers the rank-one iterate, and records access bounds and concrete
stopping-angle examples.

## Main statements

* `nextCertaintyProgram_success`: the two branches of exact amplification.
* `nextIterateGen_action`: the action of the generalized-projector iterate.
* `nextCertainty_prepare_accesses_le`: the preparation-access bound.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option warningAsError false

open scoped BigOperators Classical ENNReal

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace
namespace CountingCertainty

open Qatlib
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The marked squared norm of the first column of `A` for Boolean mask `g`. -/
noncomputable def nextGoodMass {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) : ℝ :=
  ∑ i, Complex.normSq (RankOneReflection.goodPart g (fun i => A i 0) i)

/-- The real ideal iteration count `π / (4 * θ) - 1/2` for reaching the marked direction. -/
noncomputable def nextHalfStep (θ : ℝ) : ℝ := Real.pi / (4 * θ) - 1 / 2

/-- The natural floor of the ideal iteration count `π / (4 * θ) - 1/2`. -/
noncomputable def nextStepFloor (θ : ℝ) : ℕ := Nat.floor (Real.pi / (4 * θ) - 1 / 2)

/-- If the ideal iteration count is the natural number `m`, then `m` ordinary amplification
iterations give marked mass one under the stated normalization and angle assumptions. -/
theorem nextCertainty_integral_success
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin2a : Real.sin θ ^ 2 = nextGoodMass A g)
    (ha0 : 0 < nextGoodMass A g)
    (ha1 : nextGoodMass A g < 1)
    (m : ℕ) (hm : (m : ℝ) = nextHalfStep θ) :
    ∑ i, Complex.normSq (RankOneReflection.goodPart g
        (((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec (fun i => A i 0)) i) = 1 := by
  have hsq := zoo_counting_rankone_known_success_amplification_success_sq
    A g hA θ (le_of_lt hθ0) hθπ hsin2a ha0 ha1 m
  rw [hsq]
  have hangle : (2 * (m : ℝ) + 1) * θ = Real.pi / 2 := by
    have h4θ : (4 : ℝ) * θ ≠ 0 := by positivity
    rw [show (2 * (m : ℝ) + 1) * θ = 2 * (m : ℝ) * θ + θ by ring]
    rw [hm]
    unfold nextHalfStep
    field_simp [h4θ]
    ring
  rw [hangle]
  norm_num

/-- The distinction between an ideal iteration count equal to a natural number and one unequal
to every natural number. -/
inductive NextCertaintyBranch (θ : ℝ) where

  | integral (m : ℕ) (h : (m : ℝ) = nextHalfStep θ) : NextCertaintyBranch θ

  | nonIntegral (h : ∀ m : ℕ, (m : ℝ) ≠ nextHalfStep θ) : NextCertaintyBranch θ

/-- The output state obtained by ordinary iterations in the integral case or by floored ordinary
iterations followed by one phase-adjusted iterate in the nonintegral case. -/
noncomputable def nextCertaintyProgram
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (θ : ℝ) (φ ϕ : ℂ)
    (br : NextCertaintyBranch θ) : Fin (n + 1) → ℂ :=
  match br with
  | .integral m _ =>
      ((RankOneReflection.iterate A g (-1) (-1)) ^ m).mulVec (fun i => A i 0)
  | .nonIntegral _ =>
      (RankOneReflection.iterate A g φ ϕ).mulVec
        (((RankOneReflection.iterate A g (-1) (-1)) ^ nextStepFloor θ).mulVec
          (fun i => A i 0))

/-- If `0 < θ ≤ π/2` and the ideal iteration count is not a natural number, its natural floor is
strictly smaller. -/
theorem nextCertainty_floor_lt (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2)
    (hne : ∀ m : ℕ, (m : ℝ) ≠ nextHalfStep θ) :
    (nextStepFloor θ : ℝ) < nextHalfStep θ := by
  have h4θ : (0 : ℝ) < 4 * θ := by positivity
  have hpi : (2 : ℝ) * θ ≤ Real.pi := by linarith [hθπ]
  have hhalf : (0 : ℝ) ≤ nextHalfStep θ := by
    unfold nextHalfStep
    have hdiv : Real.pi / (4 * θ) ≥ (2 : ℝ) * θ / (4 * θ) :=
      div_le_div_of_nonneg_right hpi (le_of_lt h4θ)
    have hval : (2 : ℝ) * θ / (4 * θ) = 1 / 2 := by field_simp; ring
    linarith
  have hle : (nextStepFloor θ : ℝ) ≤ nextHalfStep θ := by
    simpa [nextStepFloor, nextHalfStep] using Nat.floor_le hhalf
  refine lt_of_le_of_ne hle (fun h => ?_)
  exact hne (Nat.floor (nextHalfStep θ)) (by simpa [nextStepFloor, nextHalfStep] using h)

/-- In the nonintegral stopping case, constructs unit-modulus phases satisfying the slowdown
equations and making `nextCertaintyProgram` have marked mass one. -/
theorem nextCertainty_nonintegral_success
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : Real.sin θ ^ 2 = nextGoodMass A g)
    (hne : ∀ m : ℕ, (m : ℝ) ≠ nextHalfStep θ) :
    ∃ (φ ϕ : ℂ),
        ‖φ‖ = 1 ∧
        ‖ϕ‖ = 1 ∧
        (Real.cos ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
            / Real.sqrt (1 - nextGoodMass A g)) ^ 2
          = 2 * nextGoodMass A g * (1 - Complex.re φ) ∧
        ϕ * (1 - φ) * nextGoodMass A g * (Real.sin
              ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
                / Real.sqrt (nextGoodMass A g))
          = ((1 - φ) * nextGoodMass A g + φ)
              * (Real.cos ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
                / Real.sqrt (1 - nextGoodMass A g)) ∧
        ∑ i, Complex.normSq (RankOneReflection.goodPart g
            (nextCertaintyProgram A g θ φ ϕ (.nonIntegral hne)) i) = 1 := by
  have hfloor : (nextStepFloor θ : ℝ) < nextHalfStep θ :=
    nextCertainty_floor_lt θ hθ0 (le_of_lt hθ1) hne
  have hslow := Qatlib.Concepts.AEMeanReadout.RankOneSubspace.certaintyMethodSlowdown
    n A g hA θ hθ0 hθ1 hmass hfloor
  obtain ⟨φ, ϕ, hφ, hϕ, h1, h2, hmass'⟩ := hslow
  refine ⟨φ, ϕ, hφ, hϕ, ?_, ?_, ?_⟩
  · simpa only [nextHalfStep, nextStepFloor, nextGoodMass] using h1
  · simpa only [nextHalfStep, nextStepFloor, nextGoodMass] using h2
  · simpa only [nextCertaintyProgram, nextStepFloor, nextHalfStep] using hmass'

/-- Under the stated unitary, angle, and marked-mass assumptions, the integral branch succeeds
exactly, and the nonintegral branch possesses unit-modulus phases satisfying the slowdown
equations and giving marked mass one [Brassard et al., Section
2][BrassardHoyerTapp1998Counting]. -/
theorem nextCertaintyProgram_success
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : Real.sin θ ^ 2 = nextGoodMass A g)
    (ha0 : 0 < nextGoodMass A g)
    (ha1 : nextGoodMass A g < 1)
    (φ ϕ : ℂ) :
    (∀ (m : ℕ) (h : (m : ℝ) = nextHalfStep θ),
        ∑ i, Complex.normSq (RankOneReflection.goodPart g
            (nextCertaintyProgram A g θ φ ϕ (.integral m h)) i) = 1) ∧
    (∀ (hne : ∀ m : ℕ, (m : ℝ) ≠ nextHalfStep θ),
        ∃ (φ' ϕ' : ℂ),
            ‖φ'‖ = 1 ∧ ‖ϕ'‖ = 1 ∧
            (Real.cos ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
                / Real.sqrt (1 - nextGoodMass A g)) ^ 2
              = 2 * nextGoodMass A g * (1 - Complex.re φ') ∧
            ϕ' * (1 - φ') * nextGoodMass A g * (Real.sin
                  ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
                    / Real.sqrt (nextGoodMass A g))
              = ((1 - φ') * nextGoodMass A g + φ')
                  * (Real.cos ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
                    / Real.sqrt (1 - nextGoodMass A g)) ∧
            ∑ i, Complex.normSq (RankOneReflection.goodPart g
                (nextCertaintyProgram A g θ φ' ϕ' (.nonIntegral hne)) i) = 1) := by
  refine ⟨?_, ?_⟩
  · intro m h
    simpa only [nextCertaintyProgram] using
      (nextCertainty_integral_success A g hA θ hθ0 (le_of_lt hθ1) hmass ha0 ha1 m h)
  · intro hne
    exact nextCertainty_nonintegral_success A g hA θ hθ0 hθ1 hmass hne

/-- A finite complex matrix equipped with idempotence and self-adjointness proofs. -/
structure NextZeroProjector (I : Type) [Fintype I] [DecidableEq I] where

  toMatrix : Matrix I I ℂ

  idempotent : toMatrix * toMatrix = toMatrix

  selfAdjoint : toMatrix.conjTranspose = toMatrix

/-- The phase-amplification iterate formed from the conjugated projector `P₀`, the marked phase
mask, and an overall minus sign. -/
noncomputable def nextIterateGen
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (g : I → Bool)
    (P₀ : NextZeroProjector I) (φ ϕ : ℂ) : Matrix I I ℂ :=
  -(A * (1 + (φ - 1) • P₀.toMatrix) * A.conjTranspose *
    Matrix.diagonal (fun i => if g i then ϕ else 1))

/-- Conjugating `1 + (φ - 1) • P₀` by `A` with `A * A.conjTranspose = 1` yields the identity
plus the scaled conjugated projector. -/
theorem nextIterateGen_conjugation {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A * A.conjTranspose = 1)
    (P₀ : NextZeroProjector I) (φ : ℂ) :
    A * (1 + (φ - 1) • P₀.toMatrix) * A.conjTranspose
      = 1 + (φ - 1) • (A * P₀.toMatrix * A.conjTranspose) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hA,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Expands the generalized iterate's action into the marked phase action and the contribution
of the conjugated projector. -/
theorem nextIterateGen_action {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A * A.conjTranspose = 1) (g : I → Bool)
    (P₀ : NextZeroProjector I) (φ ϕ : ℂ) (v : I → ℂ) :
    (nextIterateGen A g P₀ φ ϕ).mulVec v
      = -((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec v
          + (φ - 1) • ((A * P₀.toMatrix * A.conjTranspose).mulVec
              ((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec v))) := by
  have hconj := nextIterateGen_conjugation A hA P₀ φ
  unfold nextIterateGen
  rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hconj, Matrix.add_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec]

/-- Given linear-combination formulas for the conjugated projector after the marked phase on
`ψg` and `ψb`, gives the resulting generalized-iterate action on each vector. -/
theorem nextIterateGen_span_invariant
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A * A.conjTranspose = 1) (g : I → Bool)
    (P₀ : NextZeroProjector I) (φ ϕ : ℂ) (ψg ψb : I → ℂ) (c₁ c₂ c₃ c₄ : ℂ)
    (hgood : (A * P₀.toMatrix * A.conjTranspose).mulVec
        ((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψg)
      = c₁ • ψg + c₂ • ψb)
    (hbad : (A * P₀.toMatrix * A.conjTranspose).mulVec
        ((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψb)
      = c₃ • ψg + c₄ • ψb) :
    (nextIterateGen A g P₀ φ ϕ).mulVec ψg
      = -((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψg
          + (φ - 1) • (c₁ • ψg + c₂ • ψb)) ∧
    (nextIterateGen A g P₀ φ ϕ).mulVec ψb
      = -((Matrix.diagonal (fun i => if g i then ϕ else 1)).mulVec ψb
          + (φ - 1) • (c₃ • ψg + c₄ • ψb)) := by
  have hact := nextIterateGen_action A hA g P₀ φ ϕ
  constructor
  · rw [hact, hgood]
  · rw [hact, hbad]

/-- When `P₀` is the zero-coordinate rank-one projector, the generalized iterate equals
`RankOneReflection.iterate`. -/
theorem nextIterateGen_eq_iterate_rank_one
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (P₀ : NextZeroProjector (Fin (n + 1))) (φ ϕ : ℂ)
    (hP : P₀.toMatrix = Matrix.single 0 0 (1 : ℂ)) :
    nextIterateGen A g P₀ φ ϕ = RankOneReflection.iterate A g φ ϕ := by
  simp only [nextIterateGen, RankOneReflection.iterate, hP]

/-- For the zero-coordinate rank-one projector, conjugation by `A` yields the outer product of
its first column with its conjugate. -/
theorem nextIterateGen_rank_one_conjugated
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (P₀ : NextZeroProjector (Fin (n + 1)))
    (hP : P₀.toMatrix = Matrix.single 0 0 (1 : ℂ)) :
    A * P₀.toMatrix * A.conjTranspose
      = Matrix.vecMulVec (fun i => A i 0) (fun j => star (A j 0)) := by
  rw [hP, zoo_counting_conjugate_basis_projector]

/-- The two-dimensional identity projector remains the identity under identity conjugation,
whereas the zero-coordinate rank-one projector gives a different matrix. -/
theorem nextZeroProjector_trivial_counterexample :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        (Matrix.single 0 0 (1 : ℂ))
      ≠ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨by simp, ?_⟩
  intro h
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Matrix.one_apply] at h11

/-- The pair of real and complex phase-cancellation equations for the final slowdown step at
`nextStepFloor θ`. -/
def NextSlowdownEquations {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (g : Fin (n + 1) → Bool) (θ : ℝ) (φ ϕ : ℂ) : Prop :=
  (Real.cos ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
      / Real.sqrt (1 - nextGoodMass A g)) ^ 2
    = 2 * nextGoodMass A g * (1 - Complex.re φ) ∧
  ϕ * (1 - φ) * nextGoodMass A g * (Real.sin
        ((2 * (nextStepFloor θ : ℝ) + 1) * θ) / Real.sqrt (nextGoodMass A g))
    = ((1 - φ) * nextGoodMass A g + φ)
      * (Real.cos ((2 * (nextStepFloor θ : ℝ) + 1) * θ)
        / Real.sqrt (1 - nextGoodMass A g))

/-- The preparation-access count, equal to twice the integral iteration count or twice one plus
the floored count in the nonintegral case. -/
noncomputable def nextCertaintyPrepareAccesses (θ : ℝ) (br : NextCertaintyBranch θ) : ℕ :=
  match br with
  | .integral m _ => 2 * m
  | .nonIntegral _ => 2 * (nextStepFloor θ + 1)

/-- For `0 < θ ≤ π/2`, either certainty branch uses at most `2 * (nextHalfStep θ + 1)`
preparation accesses [Brassard et al., Section 2][BrassardHoyerTapp1998Counting]. -/
theorem nextCertainty_prepare_accesses_le
    (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi / 2) (br : NextCertaintyBranch θ) :
    (nextCertaintyPrepareAccesses θ br : ℝ) ≤ 2 * (nextHalfStep θ + 1) := by
  have hhalf : (0 : ℝ) ≤ nextHalfStep θ := by
    unfold nextHalfStep
    have h4θ : (0 : ℝ) < 4 * θ := by positivity
    have hpi : (2 : ℝ) * θ ≤ Real.pi := by linarith [hθπ]
    have hdiv : Real.pi / (4 * θ) ≥ (2 : ℝ) * θ / (4 * θ) :=
      div_le_div_of_nonneg_right hpi (le_of_lt h4θ)
    have hval : (2 : ℝ) * θ / (4 * θ) = 1 / 2 := by field_simp; ring
    linarith
  cases br with
  | integral m h =>
      rw [nextCertaintyPrepareAccesses]
      push_cast
      have hle : (m : ℝ) ≤ nextHalfStep θ := by rw [h]
      linarith
  | nonIntegral hne =>
      rw [nextCertaintyPrepareAccesses]
      push_cast
      have hle : (nextStepFloor θ : ℝ) ≤ nextHalfStep θ := by
        simpa [nextStepFloor, nextHalfStep] using Nat.floor_le hhalf
      linarith

/-- For marked mass `(sin θ)^2` with `0 < θ ≤ π/4`, constructs finite geometric search with
failure at most any positive tolerance, expected preparation calls at most `150 * sqrt 2 /
sin θ`, and marked successful outputs [BrassardHoyerTapp1998Counting]. -/
theorem nextCertainty_phase_solving_cost
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j₀ : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ4 : θ ≤ Real.pi / 4)
    (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (M T : ℕ),
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
          (geometricSearchSchedule M T)) (fun tr => tr.result = none)
        ≤ ENNReal.ofReal ε ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
          (geometricSearchSchedule M T)) (fun tr => (tr.prepareCalls : ℝ≥0∞))
        ≤ ENNReal.ofReal (150 * Real.sqrt 2 / Real.sin θ) ∧
      ∀ tr ∈ (searchForSchedule A hA j₀ S (fun y => decide (y ∈ S))
          (geometricSearchSchedule M T)).support,
        ∀ y, tr.result = some y → y ∈ S := by
  exact Qatlib.Concepts.AEMeanReadout.RankOneSubspace.theorem3QuadraticSpeedupUnknownA
    I A j₀ S hA θ hθ0 hθ4 hmass ε hε

/-- The two-dimensional source rotation at angle `π/3` used for a concrete certainty example. -/
noncomputable def nextCertaintySource : Matrix (Fin 2) (Fin 2) ℂ :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation (Real.pi / 3)

/-- The Boolean mask marking coordinate zero in `Fin 2`. -/
def nextCertaintyMask : Fin 2 → Bool := fun i => decide (i = 0)

/-- The concrete certainty source has marked mass `1/4` under `nextCertaintyMask`. -/
theorem nextCertaintySource_mass :
    nextGoodMass nextCertaintySource nextCertaintyMask = (1/4 : ℝ) := by
  unfold nextGoodMass
  rw [Fin.sum_univ_two]
  simp [RankOneReflection.goodPart, nextCertaintyMask, nextCertaintySource,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.smallRotation, Matrix.cons_val_zero, Complex.normSq_apply]
  norm_num

/-- At angle `π/6`, the marked mass is `1/4` and the ideal iteration count equals one. -/
theorem nextCertaintySource_angle :
    Real.sin (Real.pi / 6) ^ 2 = (1/4 : ℝ) ∧
    ((1 : ℕ) : ℝ) = nextHalfStep (Real.pi / 6) := by
  constructor
  · rw [Real.sin_pi_div_six]
    norm_num
  · unfold nextHalfStep
    field_simp
    ring

/-- The ideal iteration count at angle `π/4` is `1/2`. -/
theorem nextCertainty_halfstep_pi_div_four :
    nextHalfStep (Real.pi / 4) = (1/2 : ℝ) := by
  unfold nextHalfStep
  field_simp
  ring

/-- The floored iteration count at angle `π/4` is zero. -/
theorem nextCertainty_floor_pi_div_four : nextStepFloor (Real.pi / 4) = 0 := by
  rw [nextStepFloor]
  have hval : Real.pi / (4 * (Real.pi / 4)) - 1 / 2 = (1/2 : ℝ) := by field_simp; ring
  rw [hval]
  exact (Nat.floor_eq_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (by norm_num)

/-- No natural number equals the ideal iteration count at angle `π/4`. -/
theorem nextCertainty_nonintegral_witness :
    ∀ m : ℕ, (m : ℝ) ≠ nextHalfStep (Real.pi / 4) := by
  intro m hm
  rw [nextCertainty_halfstep_pi_div_four] at hm
  have hlt : m < 1 := by
    have h1 : (m : ℝ) < 1 := by linarith
    exact_mod_cast h1
  have hz : m = 0 := by omega
  rw [hz] at hm
  norm_num at hm

end CountingCertainty
end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
