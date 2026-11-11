/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Backend
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Table
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Search

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

/-! One finite represented phase producer with execution-linked budgets.

Canonical rational inputs, dyadic initialization, the full table, materialized
Cartesian enumeration, every tested score, and all failure paths belong to
one interpreter. Its exact output and original counters refine the pinned
finite producer. Costs are computed from this interpreter's operand trace
under an explicit positive primitive-price model. They are not supplied
fields and are not polynomial preprocessing or host bit-time claims.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- Construction for input Coefficients in the program model. -/
def inputCoefficients (p : List ℚ) : Run (List ℚ) :=
  mapRun (fun x => emit (.inputRat x) x) p

/-- Input reading retains every canonical rational coefficient, including unused tails. -/
@[simp] theorem inputCoefficients_value (p : List ℚ) :
    (inputCoefficients p).value = p := by simp [inputCoefficients]

/-- Construction for replicate Run in the program model. -/
def replicateRun {α : Type} : ℕ → α → Run (List α)
  | 0,_ => pure []
  | n+1,a => do
    let rest ← replicateRun n a
    allocate a rest

/-- Traced replication allocates the original actual initial packet. -/
@[simp] theorem replicateRun_value {α : Type} (n : ℕ) (a : α) :
    (replicateRun n a).value = List.replicate n a := by
  induction n with
  | zero => simp [replicateRun]
  | succ n ih => simp [replicateRun, List.replicate_succ, ih]

/-- Construction for tolerance Bits in the program model. -/
def toleranceBits (eps : ℚ) : Run ℕ :=
  emit (.natural .clog 2 eps.den) (Nat.clog 2 eps.den)

/-- Tolerance-bit extraction uses the original canonical denominator. -/
@[simp] theorem toleranceBits_value (eps : ℚ) :
    (toleranceBits eps).value = phaseToleranceBits eps := by
  simp [toleranceBits, phaseToleranceBits]

/-- Construction for constant in the program model. -/
def constant (degree : ℕ) : Run ℕ := do
  let next ← natAdd degree 1
  let exponent ← natPower 3 degree
  natMul next exponent

/-- The traced sensitivity constant preserves the original exact integer. -/
@[simp] theorem constant_value (degree : ℕ) :
    (constant degree).value = phaseConstant degree := by simp [constant, phaseConstant]

/-- Construction for grid Bits in the program model. -/
def gridBits (degree k : ℕ) : Run ℕ := do
  let sensitivity ← constant degree
  let scaled ← natMul 32 sensitivity
  let logarithm ← emit (.natural .clog 2 scaled) (Nat.clog 2 scaled)
  natAdd k logarithm

/-- The traced grid precision equals the original finite-circle precision. -/
@[simp] theorem gridBits_value (degree k : ℕ) :
    (gridBits degree k).value = phaseGridBits degree k := by simp [gridBits, phaseGridBits]

/-- Construction for backend Bits in the program model. -/
def backendBits (degree k : ℕ) : Run ℕ := do
  let grid ← gridBits degree k
  let first ← natAdd k grid
  let sensitivity ← constant degree
  let scaled ← natMul 4 sensitivity
  let logarithm ← emit (.natural .clog 2 scaled) (Nat.clog 2 scaled)
  natAdd first logarithm

/-- Traced backend precision keeps all original degree and tolerance dependence. -/
@[simp] theorem backendBits_value (degree k : ℕ) :
    (backendBits degree k).value = phaseBackendBits degree k := by
  simp [backendBits, phaseBackendBits]

/-- Construction for produce in the program model. -/
def produce (p : List ℚ) (degree : ℕ) (eps : ℚ) : Run SynthesisResult := do
  let coefficients ← inputCoefficients p
  let d ← emit (.inputNat degree) degree
  let tolerance ← emit (.inputRat eps) eps
  let k ← toleranceBits tolerance
  let threshold ← power (1/2) k
  let phases ← replicateRun d gone
  let initial : PhaseData := ⟨gone,phases⟩
  let initialScore ← score coefficients d initial
  let accepted ← compare initialScore.1.1 threshold
  if accepted then
    pure ⟨some initial,0,0,1,initialScore.1.2,initialScore.2⟩
  else
    let r ← gridBits d k
    let q ← backendBits d k
    let n ← natPower 2 r
    let point ← dyadicPhase r false q
    let rows ← table point n
    let width ← natAdd d 1
    let candidates ← words n width
    let result ← search coefficients d threshold rows.1 candidates
    pure ⟨result.value,1,rows.2,result.tested+1,
      result.responseRounds+initialScore.1.2,result.coefficientVisits+initialScore.2⟩

/-- The entire traced interpreter returns exactly the original packet and all five legacy counters. -/
theorem produce_value (p : List ℚ) (degree : ℕ) (eps : ℚ) :
    (produce p degree eps).value = finitePhaseSynthesis p degree eps := by
  simp only [produce, value_bind, inputCoefficients_value, value_emit,
    toleranceBits_value, power_value, replicateRun_value, score_value, compare_value]
  by_cases hs : (scoreData p degree ⟨gone,List.replicate degree gone⟩).1.1 ≤
      (1/2 : ℚ)^phaseToleranceBits eps
  · simp_all [finitePhaseSynthesis]
  · have hreject : ¬ (scoreData p degree ⟨gone,List.replicate degree gone⟩).1.1 ≤
        ((2 : ℚ)^phaseToleranceBits eps)⁻¹ := by
      simpa only [one_div, inv_pow] using hs
    simp [finitePhaseSynthesis, hreject]

/-- An execution witness identifies the complete result with this original-input interpreter. -/
def Executes (p : List ℚ) (degree : ℕ) (eps : ℚ) (actual : Run SynthesisResult) : Prop :=
  actual = produce p degree eps

/-- A bound must pay the actual trace of the same run, not an independent cost field. -/
def CertifiedBudget (model : PriceModel) (p : List ℚ) (degree : ℕ) (eps : ℚ)
    (actual : Run SynthesisResult) (budget : ℕ) : Prop :=
  Executes p degree eps actual ∧ charge model actual.events ≤ budget

/-- The honest enumerative baseline has its complete trace-derived exact budget. -/
def actualCost (model : PriceModel) (p : List ℚ) (degree : ℕ) (eps : ℚ) : ℕ :=
  charge model (produce p degree eps).events

/-- The baseline certifies its computed complete cost without claiming a polynomial bound. -/
theorem actualCost_certified (model : PriceModel) (p : List ℚ) (degree : ℕ) (eps : ℚ) :
    CertifiedBudget model p degree eps (produce p degree eps) (actualCost model p degree eps) :=
  ⟨rfl, Nat.le_refl _⟩

/-- A certified budget simultaneously fixes the original output and bounds its same-run charge. -/
theorem certifiedBudget_sound (model : PriceModel) (p : List ℚ) (degree : ℕ) (eps : ℚ)
    (actual : Run SynthesisResult) (budget : ℕ)
    (h : CertifiedBudget model p degree eps actual budget) :
    actual.value = finitePhaseSynthesis p degree eps ∧ actualCost model p degree eps ≤ budget := by
  rcases h with ⟨heq,hcost⟩
  subst actual
  exact ⟨produce_value p degree eps,hcost⟩

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
