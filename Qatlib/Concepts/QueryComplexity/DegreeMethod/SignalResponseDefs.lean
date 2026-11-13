/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SignalResponseLowerBound
import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs

/-!
# Definitions for matrix signal responses

This module defines contractive access conditions, matrix response gaps, query thresholds,
and branch-level masses for adaptive signal trees. These notions support hybrid
query bounds in the framework of [BennettEtAl1997].

It also separates forward, backward, and address costs, and supplies scalar-matrix,
branch-distribution, and asymmetric-access examples for the response and ledger theorems.

## Main statements

* `boundedAccessWord_guard`: bounded access gives contractive instruction matrices.
* `compress_norm_eq_of_square_isometry`: square isometric compression preserves norm.
* `responseQueryThreshold_spec`: characterize the natural query threshold by an inequality.
* `asymmetricAccessModel`: distinct gate and read-bit costs for the two access directions.

## References

* [Bennett et al., 1997][BennettEtAl1997]
* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.AdaptiveSignalTree
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

open Matrix
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder ENNReal Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- A gate instruction is contractive when its matrix norm is at most one; forward and backward
oracle instructions satisfy this predicate automatically. -/
noncomputable def GateContraction {H : Type} [Fintype H] [DecidableEq H] :
    AdjointStep H → Prop
  | .gate V => ‖V‖ ≤ 1
  | .forward => True
  | .backward => True

/-- Every gate instruction appearing in the word is contractive. -/
noncomputable def WellFormedGates {H : Type} [Fintype H] [DecidableEq H]
    (word : List (AdjointStep H)) : Prop :=
  ∀ c ∈ word, GateContraction c

/-- The oracle matrix has norm at most one and all gate instructions in the word are
contractive. -/
noncomputable def BoundedAccessWord {H : Type} [Fintype H] [DecidableEq H]
    (O : Matrix H H ℂ) (word : List (AdjointStep H)) : Prop :=
  ‖O‖ ≤ 1 ∧ WellFormedGates word

/-- Every instruction matrix in a bounded access word has norm at most one. -/
theorem boundedAccessWord_guard {H : Type} [Fintype H] [DecidableEq H]
    {O : Matrix H H ℂ} {word : List (AdjointStep H)}
    (h : BoundedAccessWord O word) : ∀ c ∈ word, ‖instructionMatrix O c‖ ≤ 1 := by
  intro c hc
  have hO : ‖O‖ ≤ 1 := h.1
  have hg : GateContraction c := h.2 c hc
  cases c with
  | gate V =>
    simp only [instructionMatrix]
    simpa [GateContraction] using! hg
  | forward =>
    simp only [instructionMatrix]
    exact hO
  | backward =>
    simp only [instructionMatrix, Matrix.l2_opNorm_conjTranspose]
    exact hO

/-- A member of a bounded matrix family together with a word of contractive gates forms a
bounded access word. -/
theorem boundedFamily_accessWord {I : Type} [Fintype I] [DecidableEq I]
    {F : MatrixFamily I} {z : ℝ} {word : List (AdjointStep I)}
    (hF : BoundedMatrixFamily F) (hG : WellFormedGates word) :
    BoundedAccessWord (F z) word :=
  ⟨hF z, hG⟩

/-- The nonnegative target separation remaining after subtracting two error allowances, `max 0
(‖A - B‖ - 2 * eps)`. -/
noncomputable def matrixResponseConstant {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (eps : ℝ) : ℝ :=
  max 0 (‖A - B‖ - 2 * eps)

/-- A square complex isometric matrix is unitary. -/
theorem square_isometry_is_unitary {I : Type} [Fintype I] [DecidableEq I]
    {L : Matrix I I ℂ} (hL : IsIsometry L) : L ∈ Matrix.unitaryGroup I ℂ := by
  have hdet : L.det ≠ 0 := by
    intro hzero
    have hone : (Lᴴ * L).det = 1 := by
      rw [hL]
      exact Matrix.det_one
    have hmul : Lᴴ.det * L.det = 1 := by
      rw [← Matrix.det_mul]
      exact hone
    rw [hzero, mul_zero] at hmul
    exact zero_ne_one hmul
  have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet
  have hLi : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hunit
  have hstar : Lᴴ = L⁻¹ := by
    calc
      Lᴴ = Lᴴ * 1 := (mul_one Lᴴ).symm
      _ = Lᴴ * (L * L⁻¹) := by rw [hLi]
      _ = (Lᴴ * L) * L⁻¹ := (Matrix.mul_assoc Lᴴ L L⁻¹).symm
      _ = 1 * L⁻¹ := by rw [hL]
      _ = L⁻¹ := one_mul L⁻¹
  refine ⟨hL, ?_⟩
  calc
    L * Lᴴ = L * L⁻¹ := by rw [hstar]
    _ = 1 := hLi

/-- Compression on both sides by square isometries preserves the operator norm on a nonempty
index type. -/
theorem compress_norm_eq_of_square_isometry {I : Type} [Fintype I] [DecidableEq I]
    [Nonempty I] (L R X : Matrix I I ℂ) (hL : IsIsometry L) (hR : IsIsometry R) :
    ‖compress L X R‖ = ‖X‖ := by
  have hLU : L ∈ Matrix.unitaryGroup I ℂ := square_isometry_is_unitary hL
  have hRU : R ∈ Matrix.unitaryGroup I ℂ := square_isometry_is_unitary hR
  have hLone : ‖L‖ = 1 := l2_norm_unitary_eq_one hLU
  have hRone : ‖R‖ = 1 := l2_norm_unitary_eq_one hRU
  have hLstar : ‖Lᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hLone
  have hRstar : ‖Rᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hRone
  have hXR : ‖X * R‖ = ‖X‖ := by
    refine le_antisymm ?_ ?_
    · refine le_trans (Matrix.l2_opNorm_mul X R) ?_
      rw [hRone, mul_one]
    · have hRinv : R * Rᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hRU
      calc
        ‖X‖ = ‖X * 1‖ := by rw [mul_one]
        _ = ‖X * (R * Rᴴ)‖ := by rw [hRinv]
        _ = ‖(X * R) * Rᴴ‖ := by rw [Matrix.mul_assoc X R Rᴴ]
        _ ≤ ‖X * R‖ * ‖Rᴴ‖ := Matrix.l2_opNorm_mul (X * R) Rᴴ
        _ = ‖X * R‖ := by rw [hRstar, mul_one]
  have hupp : ‖compress L X R‖ ≤ ‖X‖ := by
    rw [compress, Matrix.mul_assoc Lᴴ X R]
    refine le_trans (Matrix.l2_opNorm_mul Lᴴ (X * R)) ?_
    rw [hLstar, hXR, one_mul]
  have hlow : ‖X‖ ≤ ‖compress L X R‖ := by
    have hLinv : L * Lᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hLU
    have hY : L * (Lᴴ * (X * R)) = X * R := by
      calc
        L * (Lᴴ * (X * R)) = (L * Lᴴ) * (X * R) :=
          (Matrix.mul_assoc L Lᴴ (X * R)).symm
        _ = 1 * (X * R) := by rw [hLinv]
        _ = X * R := one_mul (X * R)
    calc
      ‖X‖ = ‖X * R‖ := hXR.symm
      _ = ‖L * (Lᴴ * (X * R))‖ := by rw [hY]
      _ ≤ ‖L‖ * ‖Lᴴ * (X * R)‖ := Matrix.l2_opNorm_mul L (Lᴴ * (X * R))
      _ = ‖Lᴴ * (X * R)‖ := by rw [hLone, one_mul]
      _ = ‖compress L X R‖ := by rw [compress, Matrix.mul_assoc Lᴴ X R]
  exact le_antisymm hupp hlow

/-- The `Unit`-indexed identity matrix used as the first oracle in the sharpness example. -/
noncomputable def sharpnessOracleOne : Matrix Unit Unit ℂ := ((1 : ℝ) : ℂ) • 1

/-- One half of the `Unit`-indexed identity matrix, used as the second sharpness oracle. -/
noncomputable def sharpnessOracleTwo : Matrix Unit Unit ℂ := ((1 / 2 : ℝ) : ℂ) • 1

/-- Five quarters of the `Unit`-indexed identity matrix, used as the first sharpness target. -/
noncomputable def sharpnessTargetOne : Matrix Unit Unit ℂ := ((5 / 4 : ℝ) : ℂ) • 1

/-- One quarter of the `Unit`-indexed identity matrix, used as the second sharpness target. -/
noncomputable def sharpnessTargetTwo : Matrix Unit Unit ℂ := ((1 / 4 : ℝ) : ℂ) • 1

/-- The approximation tolerance `1 / 4` for the sharpness example. -/
noncomputable def sharpnessEps : ℝ := 1 / 4

/-- The sharpness example's word consisting of one forward oracle access. -/
def sharpnessWord : List (AdjointStep Unit) := [AdjointStep.forward]

/-- The natural ceiling of the real ratio `c / d`. -/
noncomputable def responseQueryThreshold (c d : ℝ) : ℕ :=
  Nat.ceil (c / d)

/-- For `d > 0`, the response query threshold is at most `q` exactly when `q * d ≥ c`. -/
theorem responseQueryThreshold_spec {c d : ℝ} {q : ℕ} (hd : 0 < d) :
    responseQueryThreshold c d ≤ q ↔ (q : ℝ) * d ≥ c := by
  constructor
  · intro h
    have h1 : c / d ≤ (Nat.ceil (c / d) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (c / d) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
    have hmul : (c / d) * d = c := by field_simp
    rw [← hmul]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (le_of_lt hd)
  · intro h
    have hdiv : c / d ≤ (q : ℝ) := (div_le_iff₀ hd).mpr h
    exact Nat.ceil_le.mpr hdiv

/-- The total branch-law weight of paths using exactly `k` queries. -/
def branchLevelMass {H : Type} [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) (k : ℕ) : ℝ :=
  ((law.support.filter (fun e => decide (tree.pathQueries e.1 = k))).map (fun e => e.2)).sum

/-- The total branch-law weight of paths using at most `k` queries. -/
def branchCumulativeMass {H : Type} [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) (k : ℕ) : ℝ :=
  ((law.support.filter (fun e => decide (tree.pathQueries e.1 ≤ k))).map (fun e => e.2)).sum

/-- The total branch-law weight of paths belonging to `S` and using exactly `k` queries. -/
def branchQualifyingLevelMass {H : Type} [Fintype H] [DecidableEq H]
    (tree : AdaptiveSignalTree H) (law : SignalBranchLaw) (S : List (List Bool)) (k : ℕ) : ℝ :=
  ((law.support.filter (fun e =>
      decide (e.1 ∈ S) && decide (tree.pathQueries e.1 = k))).map (fun e => e.2)).sum

/-- The number of forward oracle instructions in an adjoint word. -/
def wordForwardAccesses {I : Type} (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .forward => 1
    | _ => 0)).sum

/-- The number of backward oracle instructions in an adjoint word. -/
def wordBackwardAccesses {I : Type} (word : List (AdjointStep I)) : ℕ :=
  (word.map (fun c => match c with
    | .backward => 1
    | _ => 0)).sum

/-- The address-bit width assigned by `addressBitsFor` to a domain of cardinality `d`. -/
def accessAddressBits (d : ℕ) : ℕ :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs.addressBitsFor d

/-- The total address-bit charge, equal to the number of forward and backward accesses times the
index type's address width. -/
def wordAddressBits {I : Type} [Fintype I] (word : List (AdjointStep I)) : ℕ :=
  (wordForwardAccesses word + wordBackwardAccesses word) * accessAddressBits (Fintype.card I)

/-- The identity oracle for the concrete joint-distribution example. -/
noncomputable def jointInstanceOracleOne : Matrix Unit Unit ℂ := ((1 : ℝ) : ℂ) • 1

/-- The half-identity oracle for the concrete joint-distribution example. -/
noncomputable def jointInstanceOracleTwo : Matrix Unit Unit ℂ := ((1 / 2 : ℝ) : ℂ) • 1

/-- The target equal to five quarters of the identity in the joint-distribution example. -/
noncomputable def jointInstanceTargetOne : Matrix Unit Unit ℂ := ((5 / 4 : ℝ) : ℂ) • 1

/-- The zero-matrix target in the joint-distribution example. -/
noncomputable def jointInstanceTargetTwo : Matrix Unit Unit ℂ := 0

/-- The approximation tolerance `1 / 4` for the joint-distribution example. -/
noncomputable def jointInstanceEps : ℝ := 1 / 4

/-- An adaptive tree whose false-root paths contain one forward query and whose true-root paths
contain two. -/
def jointInstanceTree : AdaptiveSignalTree Unit :=
  .node [] (.node [.forward] .leaf .leaf) (.node [.forward, .forward] .leaf .leaf)

/-- The two qualifying paths `[true, false]` and `[true, true]` of the joint-distribution
example. -/
def jointInstanceQualifying : List (List Bool) := [[true, false], [true, true]]

/-- The weighted paths `[false, false]` and `[true, false]`, each with weight `1 / 2`. -/
noncomputable def jointInstanceSupport : List (List Bool × ℝ) :=
  [([false, false], 1 / 2), ([true, false], 1 / 2)]

/-- The branch law assigning equal weight to the specified one-query and two-query paths. -/
noncomputable def jointInstanceLaw : SignalBranchLaw where
  support := jointInstanceSupport
  nonneg := by
    intro e he
    have he' : e = ([false, false], 1 / 2) ∨ e = ([true, false], 1 / 2) := by
      rw [jointInstanceSupport] at he
      simpa using! he
    rcases he' with h | h <;> subst h <;> norm_num
  total := by
    simp [jointInstanceSupport]
    norm_num

/-- An access model realizing forward access with one gate and backward access with three gates,
with respective read-bit costs one and two. -/
noncomputable def asymmetricAccessModel : OracleAccessModel Unit where
  realize := fun O b =>
    if b then [Step.gate O.conjTranspose, Step.gate (1 : Matrix Unit Unit ℂ),
        Step.gate (1 : Matrix Unit Unit ℂ)]
      else [Step.gate O]
  queryFree := by intro O b; cases b <;> rfl
  readBits := fun _ b => if b then 2 else 1
  forwardRun := by intro O ψ; simp [Run, ApplyGate]
  backwardRun := by intro O ψ; simp [Run, ApplyGate]

/-- The word containing one forward oracle access followed by one backward access. -/
def mixedDirectionWord : List (AdjointStep Unit) :=
  [AdjointStep.forward, AdjointStep.backward]

end Qatlib.Concepts.QueryComplexity.DegreeMethod
