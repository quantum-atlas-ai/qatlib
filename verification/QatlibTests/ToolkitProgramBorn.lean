/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QPrograms.MeasureProg
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-! # Adaptive measurement programs

A one-qubit policy chooses its second measurement from the first outcome. The policy
uses finite instruments and models how measurement choices depend on observed history. The regression checks concrete history masses on a normalized rational
superposition, the Born bridge for a one-round program, total normalization to one, the
zero-weight branch output being the zero operator without any division by zero, and the
separate unnormalized and conditional normalized states. Adaptive trajectories are chained
instruments (`progProbPair`), not i.i.d. draws; loops and termination stay out of scope.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QPrograms.MeasureProg

namespace QatlibTests.ToolkitProgram

/-- The one-qubit NOT gate as a two-by-two complex matrix. -/
def xGate : Operator 2 := !![(0 : ℂ), 1; 1, 0]

/-- The NOT gate is a unitary. -/
theorem xGateUnit : xGate ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h : xGate.conjTranspose * xGate = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, xGate, Fin.sum_univ_two]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact h

/-- A normalized rational superposition with Born weights nine and sixteen twenty-fifths. -/
def psi34 : QState (Fin 2) :=
  fun i => if i = 0 then Complex.ofReal (3 / 5) else Complex.ofReal (4 / 5)

/-- The amplitude of the rational superposition at the zero coordinate. -/
theorem psi340 : psi34 0 = Complex.ofReal (3 / 5) := by simp [psi34]

/-- The amplitude of the rational superposition at coordinate one. -/
theorem psi341 : psi34 1 = Complex.ofReal (4 / 5) := by simp [psi34]

/-- The rational superposition is normalized. -/
theorem psi34Norm : Normalized psi34 := by
  rw [Normalized, Fin.sum_univ_two, psi340, psi341]
  norm_num [Complex.norm_real]

/-- Both amplitudes are real, so conjugation fixes them. -/
theorem psi34Star (i : Fin 2) : (starRingEnd ℂ) (psi34 i) = psi34 i := by
  unfold psi34
  split <;> exact Complex.conj_ofReal _

/-- The density operator of the normalized rational superposition. -/
def rho34 : Operator 2 := outerProduct psi34

/-- The entries of an outer product of amplitudes. -/
theorem rho34Entry (i j : Fin 2) :
    rho34 i j = psi34 i * (starRingEnd ℂ) (psi34 j) := rfl

/-- The rational input is a density operator. -/
theorem rho34Density : IsDensityOperator rho34 :=
  isDensityOperator_outerProduct psi34Norm

/-- The upper-left entry of the rational density operator is nine twenty-fifths. -/
theorem rho34Diag0 : rho34 0 0 = Complex.ofReal (9 / 25) := by
  rw [rho34Entry, psi34Star 0, psi340]
  push_cast
  norm_num

/-- The lower-right entry of the rational density operator is sixteen twenty-fifths. -/
theorem rho34Diag1 : rho34 1 1 = Complex.ofReal (16 / 25) := by
  rw [rho34Entry, psi34Star 1, psi341]
  push_cast
  norm_num

/-- Adaptive two-round policy on one qubit: measure in the computational basis, then measure
again in the computational basis if the first outcome is zero, or after the NOT gate if the
first outcome is one. -/
def adaptPol : List (Fin 2) → Instrument (Fin 2) 2 2
  | [] => projectiveInstrument
  | o :: _ => if o = 1 then measuredInstrument xGate xGateUnit else projectiveInstrument

/-- The initial instrument of the policy is the computational-basis measurement. -/
theorem adaptPolNil : adaptPol [] = projectiveInstrument := rfl

/-- After outcome one the policy measures through the NOT gate. -/
theorem adaptPolOne : adaptPol [1] = measuredInstrument xGate xGateUnit := rfl

/-- After outcome zero the policy measures in the computational basis again. -/
theorem adaptPolZero : adaptPol [0] = projectiveInstrument := by
  simp [adaptPol]

/-- A first-round branch output keeps one diagonal entry of the input. -/
theorem firstBranch (b : Fin 2) (σ : Operator 2) :
    (adaptPol []).branch b σ = Matrix.diagonal fun j => if j = b then σ b b else 0 :=
  conjBranch_projector_apply b σ

/-- The measured instrument weight is the diagonal entry of the conjugated operator. -/
theorem measInstrProb (U : Operator 2) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (σ : Operator 2) (b : Fin 2) :
    instrumentProb (measuredInstrument U hU) σ b = ((U * σ * U.conjTranspose) b b).re := by
  have h : instrumentProb (measuredInstrument U hU) σ b
      = instrumentProb projectiveInstrument (conjBranch U σ) b := rfl
  rw [h, instrumentProb_projective, conjBranch_apply]

/-- History [0, 0]: measuring twice in the computational basis keeps the Born weight of the
zero coordinate. -/
theorem histMass00 : progProb adaptPol rho34 [0, 0] = 9 / 25 := by
  rw [progProbPair, adaptPolZero, instrumentProb_projective, firstBranch 0 rho34,
    rho34Diag0]
  simp

/-- History [0, 1]: the second basis outcome has zero weight after outcome zero. -/
theorem histMass01 : progProb adaptPol rho34 [0, 1] = 0 := by
  rw [progProbPair, adaptPolZero, instrumentProb_projective, firstBranch 0 rho34,
    rho34Diag0]
  simp

/-- History [1, 0]: after outcome one the NOT gate moves the whole remaining weight onto
outcome zero. -/
theorem histMass10 : progProb adaptPol rho34 [1, 0] = 16 / 25 := by
  rw [progProbPair, adaptPolOne, measInstrProb, firstBranch 1 rho34, rho34Diag1]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul_diagonal,
    Matrix.cons_val_one, xGate]

/-- History [1, 1]: the flipped second measurement never lands on outcome one. -/
theorem histMass11 : progProb adaptPol rho34 [1, 1] = 0 := by
  rw [progProbPair, adaptPolOne, measInstrProb, firstBranch 1 rho34, rho34Diag1]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul_diagonal,
    Matrix.cons_val_one, xGate]

/-- A one-round program weight equals the Born probability of the amplitude at the measured
coordinate. -/
theorem roundOneBorn (b : Fin 2) :
    progProb adaptPol rho34 [b] = BornProb psi34 b := by
  have hr : rho34 = outerProduct psi34 := rfl
  rw [progProbOne, adaptPolNil, hr, instrumentProb_projective_pure]

/-- The Born weight of the zero coordinate is nine twenty-fifths. -/
theorem bornMass0 : BornProb psi34 0 = 9 / 25 := by
  rw [BornProb, psi340]
  norm_num [Complex.norm_real]

/-- The zero-round program keeps all mass: the empty history has weight one on the density
input. -/
theorem emptyHistMass : progProb adaptPol rho34 [] = 1 := by
  rw [progProbNil, rho34Density.2]
  rfl

/-- Every single history weight is at most one on a density input. -/
theorem histLeOne : progProb adaptPol rho34 [1, 0] ≤ 1 := by
  have h := progProbLe adaptPol rho34Density.1 [1, 0]
  rwa [rho34Density.2, Complex.one_re] at h

/-- The weights of all four two-round histories sum to one, the Born normalization of the
adaptive program. -/
theorem sumTwoRoundOne :
    ∑ xs : Fin 2 → Fin 2, histProb adaptPol rho34 2 xs = 1 :=
  sumHistProbOne adaptPol 2 rho34Density

/-- The four two-round histories of the adaptive policy carry exactly the listed masses:
a satisfiable instance with two positive and two zero weights. -/
theorem fourHistMass :
    histProb adaptPol rho34 2 ![0, 0] = 9 / 25 ∧
    histProb adaptPol rho34 2 ![0, 1] = 0 ∧
    histProb adaptPol rho34 2 ![1, 0] = 16 / 25 ∧
    histProb adaptPol rho34 2 ![1, 1] = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [histProb, show List.ofFn (![0, 0] : Fin 2 → Fin 2) = [0, 0] by decide]
    exact histMass00
  · rw [histProb, show List.ofFn (![0, 1] : Fin 2 → Fin 2) = [0, 1] by decide]
    exact histMass01
  · rw [histProb, show List.ofFn (![1, 0] : Fin 2 → Fin 2) = [1, 0] by decide]
    exact histMass10
  · rw [histProb, show List.ofFn (![1, 1] : Fin 2 → Fin 2) = [1, 1] by decide]
    exact histMass11

/-- The zero-weight history [1, 1] outputs the zero operator: its branch is never normalized
by dividing through its zero weight. -/
theorem zeroHistOutput : progPost adaptPol rho34 [1, 1] = 0 :=
  (progProbZeroIff adaptPol rho34Density.1 [1, 1]).mp histMass11

/-- The unnormalized branch state of [1, 0] has trace sixteen twenty-fifths, not one. -/
theorem unnormTrace :
    Matrix.trace (progPost adaptPol rho34 [1, 0]) = Complex.ofReal (16 / 25) := by
  rw [progTraceEq adaptPol rho34Density.1 [1, 0], histMass10]

/-- The conditional normalized state of the positive-weight history [1, 0] is a density
operator. -/
theorem condHistDens : IsDensityOperator
    (progCond adaptPol rho34 [1, 0] (by rw [histMass10]; norm_num)) :=
  progCondDensity adaptPol rho34Density [1, 0] (by rw [histMass10]; norm_num)

/-- Rescaling the conditional state by its weight recovers the unnormalized branch state of
[1, 0]. -/
theorem condHistScale (h : 0 < progProb adaptPol rho34 [1, 0]) :
    ((progProb adaptPol rho34 [1, 0] : ℝ) : ℂ) • progCond adaptPol rho34 [1, 0] h
      = progPost adaptPol rho34 [1, 0] :=
  progCondUnnorm adaptPol rho34 [1, 0] h

end QatlibTests.ToolkitProgram
