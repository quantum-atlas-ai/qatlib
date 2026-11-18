/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdaptiveCP.BranchTrace.AdaptiveBranches
public import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument

@[expose] public section

/-!
# Finite measurement programs: branch laws and Born normalization

A straight-line measurement program is a history-dependent policy of finite instruments,
reused from `Qatlib.Concepts.AdaptiveCP.BranchTrace`. The public library proves complete
positivity and trace preservation of the adaptive branch maps (`branch_cp`, `branch_trace`);
this module adds the probability layer on top: every outcome history has a nonnegative,
trace-nonincreasing weight, and the weights of all histories of a fixed length sum to the
input trace, so they normalize to one on density operators. The unnormalized post-measurement
state of a history and its conditional normalized state are separate definitions; conditioning
is stated only under a strictly positive weight, so zero-probability branches are never
normalized through division by zero.

Outside the single-instrument interface: independence of repeated sampling and
product-distribution bridges, loops, termination, expected time, and any fuel-truncated
statement standing in for unbounded program correctness.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.QPrograms.MeasureProg

variable {O : Type} [Fintype O] {D : ℕ}

/-- The branch map of a complete outcome history of a measurement program, starting from the
empty history. -/
def progBranch (policy : List O → Instrument O D D) (os : List O) :
    Operator D →ₗ[ℂ] Operator D :=
  branch policy [] os

/-- The unnormalized post-measurement state of an outcome history: the branch map applied to
the input operator, before any normalization. -/
def progPost (policy : List O → Instrument O D D) (ρ : Operator D) (os : List O) :
    Operator D :=
  progBranch policy os ρ

/-- The probability weight of an outcome history: the real trace of its unnormalized branch
output. -/
def progProb (policy : List O → Instrument O D D) (ρ : Operator D) (os : List O) : ℝ :=
  (Matrix.trace (progPost policy ρ os)).re

/-- The probability weight of the length-`n` history encoded by `xs`. -/
def histProb (policy : List O → Instrument O D D) (ρ : Operator D) (n : ℕ)
    (xs : Fin n → O) : ℝ :=
  progProb policy ρ (List.ofFn xs)

/-- The empty history applies the identity map, so the program without measurements leaves
the input operator unchanged. -/
theorem progBranchNil (policy : List O → Instrument O D D) :
    progBranch policy [] = LinearMap.id := rfl

/-- The weight of the empty history is the real trace of the input operator. -/
theorem progProbNil (policy : List O → Instrument O D D) (ρ : Operator D) :
    progProb policy ρ [] = (Matrix.trace ρ).re := rfl

/-- A one-step history applies the branch of the initial instrument. -/
theorem progBranchOne (policy : List O → Instrument O D D) (o : O) :
    progBranch policy [o] = (policy []).branch o := rfl

/-- The weight of a one-step history is the instrument probability of the initial
instrument. -/
theorem progProbOne (policy : List O → Instrument O D D) (ρ : Operator D) (o : O) :
    progProb policy ρ [o] = instrumentProb (policy []) ρ o := rfl

/-- A two-step history applies the branch chosen by the first outcome to the output of the
initial instrument branch: an adaptive trajectory chains instruments through their
unnormalized outputs and is not a product of independent draws. -/
theorem progProbPair (policy : List O → Instrument O D D) (ρ : Operator D) (o₁ o₂ : O) :
    progProb policy ρ [o₁, o₂] =
      instrumentProb (policy [o₁]) ((policy []).branch o₁ ρ) o₂ := rfl

/-- Every history branch map is completely positive. -/
theorem progBranchCp (policy : List O → Instrument O D D) (os : List O) :
    CompletelyPositive (progBranch policy os) := by
  have h := branch_cp policy [] os.length (fun i : Fin os.length => os[i.val])
  rw [List.ofFn_getElem] at h
  exact h

/-- The unnormalized post-measurement state of a positive semidefinite input is positive
semidefinite. -/
theorem progPostPos (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (os : List O) : (progPost policy ρ os).PosSemidef :=
  (progBranchCp policy os).positive hρ

/-- The probability weight of any outcome history is nonnegative on positive semidefinite
inputs. -/
theorem progProbNonneg (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (os : List O) : 0 ≤ progProb policy ρ os :=
  (RCLike.nonneg_iff.mp (progPostPos policy hρ os).trace_nonneg).1

/-- On a positive semidefinite input, the trace of the unnormalized branch state is the
complex embedding of its probability weight. -/
theorem progTraceEq (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (os : List O) :
    Matrix.trace (progPost policy ρ os) = ((progProb policy ρ os : ℝ) : ℂ) := by
  have himg : (Matrix.trace (progPost policy ρ os)).im = 0 :=
    (RCLike.nonneg_iff.mp (progPostPos policy hρ os).trace_nonneg).2
  exact Complex.ext rfl (by rw [himg, Complex.ofReal_im])

/-- A zero-weight history has the zero operator as its unnormalized branch state, and
conversely. -/
theorem progProbZeroIff (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (os : List O) :
    progProb policy ρ os = 0 ↔ progPost policy ρ os = 0 := by
  constructor
  · intro hz
    apply (Matrix.PosSemidef.trace_eq_zero_iff (progPostPos policy hρ os)).mp
    rw [progTraceEq policy hρ os, hz]
    rfl
  · intro hz
    rw [progProb, hz]
    simp

/-- Summing all length-`n` history branch maps preserves the trace of every input operator,
the total trace-preservation law of the program. -/
theorem progTracePres (policy : List O → Instrument O D D) (n : ℕ) (ρ : Operator D) :
    Matrix.trace (∑ xs : Fin n → O, progBranch policy (List.ofFn xs) ρ) = Matrix.trace ρ :=
  branch_trace policy [] n ρ

/-- The history weights of all length-`n` histories sum to the real trace of the input
operator. -/
theorem sumHistProb (policy : List O → Instrument O D D) (n : ℕ) (ρ : Operator D) :
    ∑ xs : Fin n → O, histProb policy ρ n xs = (Matrix.trace ρ).re := by
  calc ∑ xs : Fin n → O, histProb policy ρ n xs
      = (Matrix.trace (∑ xs : Fin n → O, progBranch policy (List.ofFn xs) ρ)).re := by
          rw [Matrix.trace_sum, Complex.re_sum]
          rfl
    _ = (Matrix.trace ρ).re := congrArg Complex.re (progTracePres policy n ρ)

/-- On a density operator the weights of all length-`n` histories sum to one: the Born
normalization of the whole program. -/
theorem sumHistProbOne (policy : List O → Instrument O D D) (n : ℕ)
    {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    ∑ xs : Fin n → O, histProb policy ρ n xs = 1 := by
  rw [sumHistProb, hρ.2]
  rfl

/-- Each single history weight is at most the total real trace of the input: the
trace-nonincreasing property of one program branch. -/
theorem progProbLe (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : ρ.PosSemidef) (os : List O) :
    progProb policy ρ os ≤ (Matrix.trace ρ).re := by
  have hof : List.ofFn (fun i : Fin os.length => os[i.val]) = os := List.ofFn_getElem
  have hnonneg : ∀ xs : Fin os.length → O, 0 ≤ histProb policy ρ os.length xs :=
    fun xs => progProbNonneg policy hρ (List.ofFn xs)
  have hstep : progProb policy ρ os
      = histProb policy ρ os.length (fun i : Fin os.length => os[i.val]) := by
    rw [histProb, hof]
  calc progProb policy ρ os
      = histProb policy ρ os.length (fun i : Fin os.length => os[i.val]) := hstep
    _ ≤ ∑ xs : Fin os.length → O, histProb policy ρ os.length xs :=
        Finset.single_le_sum (fun xs _ => hnonneg xs) (Finset.mem_univ _)
    _ = (Matrix.trace ρ).re := sumHistProb policy os.length ρ

/-- The conditional normalized state of an outcome history, defined only under a strictly
positive history weight; zero-weight histories are never normalized here. -/
def progCond (policy : List O → Instrument O D D) (ρ : Operator D) (os : List O)
    (_h : 0 < progProb policy ρ os) : Operator D :=
  ((progProb policy ρ os : ℝ) : ℂ)⁻¹ • progPost policy ρ os

/-- Rescaling the conditional state by its weight recovers the unnormalized branch state. -/
theorem progCondUnnorm (policy : List O → Instrument O D D) (ρ : Operator D) (os : List O)
    (h : 0 < progProb policy ρ os) :
    ((progProb policy ρ os : ℝ) : ℂ) • progCond policy ρ os h = progPost policy ρ os := by
  rw [progCond, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast h.ne'

/-- Conditioning a positive-weight history of a density input produces a density operator. -/
theorem progCondDensity (policy : List O → Instrument O D D) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) (os : List O) (h : 0 < progProb policy ρ os) :
    IsDensityOperator (progCond policy ρ os h) := by
  have hpos : (progPost policy ρ os).PosSemidef := progPostPos policy hρ.1 os
  have hinv : (0 : ℂ) ≤ (((progProb policy ρ os : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr h.le)
  have hne : ((progProb policy ρ os : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt h
  refine ⟨Matrix.PosSemidef.smul hpos hinv, ?_⟩
  rw [progCond, Matrix.trace_smul, progTraceEq policy hρ.1 os,
    smul_eq_mul, inv_mul_cancel₀ hne]

end Qatlib.Concepts.QPrograms.MeasureProg
