/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAmplification
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationVari
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Qatlib.Concepts.QlsReadoutSpec.ProgramModel.PaidWordSemanticsLows
import Qatlib.Concepts.QlsReadoutSpec.Amplification.ProjectorOrderLows

/-!
# Coherent variable-time frames and source amplification

This module defines `CoherentVtFrame`, nested stopping projectors, and coherent stage operators
for the variable-time amplification framework of [Ambainis2012]. It also supplies paid words,
tagged matrix macros, stage records, and round-selection policies.

The source-reflection analysis gives exact two-component rotation formulas and quantitative
amplification bounds. The Algorithm 2 selection rule satisfies an ideal-gain window, while the
threshold results identify when the separate corrected-gain floor holds and exhibit its failure
at a window endpoint.

## Main statements

* `coherentStage_unitary`: unitarity of a commuting coherent stage.
* `source_rotation_mass`: the exact amplified target mass.
* `alg2Rounds_window`: the selected rounds satisfy the ideal-gain window.
* `source_floor_iff`: characterization of the corrected-gain floor.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

open Matrix
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators

variable {H : Type} [Fintype H] [DecidableEq H]

/-- An increasing family of orthogonal projectors, ordered by the absorption identity `stop j *
stop k = stop j` for `j ≤ k`. -/
def IsNestedStopFamily (m : ℕ) (stop : Fin (m + 1) → Matrix H H ℂ) : Prop :=
  (∀ j, IsOrthogonalProjector (stop j)) ∧
  (∀ j k, j ≤ k → stop j * stop k = stop j)

/-- In a nested stop family, a later stop projector also absorbs an earlier one on the right. -/
theorem nestedStopFamily_mul_rev {m : ℕ} {stop : Fin (m + 1) → Matrix H H ℂ}
    (h : IsNestedStopFamily m stop) {j k : Fin (m + 1)} (hjk : j ≤ k) :
    stop k * stop j = stop j := by
  have h1 : stop j * stop k = stop j := h.2 j k hjk
  have h2 : (stop j * stop k)ᴴ = (stop j)ᴴ := by rw [h1]
  have hstarj : (stop j)ᴴ = stop j := (h.1 j).2
  have hstark : (stop k)ᴴ = stop k := (h.1 k).2
  rw [Matrix.conjTranspose_mul] at h2
  simpa only [hstarj, hstark] using! h2

/-- The difference between a later and an earlier nested stop projector is an orthogonal
projector. -/
theorem nestedStopFamily_inc_orth {m : ℕ} {stop : Fin (m + 1) → Matrix H H ℂ}
    (h : IsNestedStopFamily m stop) {j k : Fin (m + 1)} (hjk : j ≤ k) :
    IsOrthogonalProjector (stop k - stop j) := by
  have hjk' : stop j * stop k = stop j := h.2 j k hjk
  have hkj' : stop k * stop j = stop j := nestedStopFamily_mul_rev h hjk
  have hid : stop j * stop j = stop j := (h.1 j).1
  have hkid : stop k * stop k = stop k := (h.1 k).1
  have hstarj : (stop j)ᴴ = stop j := (h.1 j).2
  have hstark : (stop k)ᴴ = stop k := (h.1 k).2
  constructor
  · show (stop k - stop j) * (stop k - stop j) = stop k - stop j
    simp only [Matrix.sub_mul, Matrix.mul_sub, hid, hkid, hkj', hjk']
    simp
  · show (stop k - stop j)ᴴ = stop k - stop j
    simp only [Matrix.conjTranspose_sub, hstarj, hstark]

/-- An earlier stop projector and the increment to a later stop projector have zero product in
both orders. -/
theorem nestedStopFamily_inc_orthogonal {m : ℕ} {stop : Fin (m + 1) → Matrix H H ℂ}
    (h : IsNestedStopFamily m stop) {j k : Fin (m + 1)} (hjk : j ≤ k) :
    stop j * (stop k - stop j) = 0 ∧ (stop k - stop j) * stop j = 0 := by
  have hjk' : stop j * stop k = stop j := h.2 j k hjk
  have hkj' : stop k * stop j = stop j := nestedStopFamily_mul_rev h hjk
  have hid : stop j * stop j = stop j := (h.1 j).1
  constructor
  · show stop j * (stop k - stop j) = 0
    rw [Matrix.mul_sub, hjk', hid]
    simp
  · show (stop k - stop j) * stop j = 0
    rw [Matrix.sub_mul, hkj', hid]
    simp

/-- The reflection `ReflectionAbout proj` used to mark the target subspace. -/
def targetMark (proj : Matrix H H ℂ) : Matrix H H ℂ := ReflectionAbout proj

/-- The target reflection associated with an orthogonal projector is unitary. -/
theorem targetMark_unitary {proj : Matrix H H ℂ} (hproj : IsOrthogonalProjector proj) :
    targetMark proj ∈ Matrix.unitaryGroup H ℂ := reflectionAbout_unitary hproj

/-- The target reflection associated with an orthogonal projector squares to the identity. -/
theorem targetMark_mul_self {proj : Matrix H H ℂ} (hproj : IsOrthogonalProjector proj) :
    targetMark proj * targetMark proj = 1 := reflectionAbout_mul_self hproj

/-- The target reflection commutes with every matrix that commutes with its defining matrix. -/
theorem targetMark_comm {proj P : Matrix H H ℂ} (h : proj * P = P * proj) :
    targetMark proj * P = P * targetMark proj := by
  have key : ((2 : ℂ) • proj - 1) * P = P * ((2 : ℂ) • proj - 1) := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, h]
  simpa only [targetMark, ReflectionAbout] using! key

/-- The product of two unitary matrices is unitary. -/
theorem unitary_mul {M : Type} [Fintype M] [DecidableEq M] {U V : Matrix M M ℂ}
    (hU : U ∈ Matrix.unitaryGroup M ℂ) (hV : V ∈ Matrix.unitaryGroup M ℂ) :
    U * V ∈ Matrix.unitaryGroup M ℂ := by
  have h1 : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa only [Matrix.star_eq_conjTranspose] using! h
  have h2 : Vᴴ * V = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hV
    simpa only [Matrix.star_eq_conjTranspose] using! h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  calc
    (U * V)ᴴ * (U * V) = Vᴴ * Uᴴ * (U * V) := by rw [Matrix.conjTranspose_mul]
    _ = Vᴴ * (Uᴴ * U) * V := by noncomm_ring
    _ = Vᴴ * (1 * V) := by rw [h1]; noncomm_ring
    _ = Vᴴ * V := by rw [Matrix.one_mul]
    _ = 1 := h2

/-- The stage round obtained by placing `A` between two reflections about `proj`. -/
def stageRound (proj A : Matrix H H ℂ) : Matrix H H ℂ :=
  ReflectionAbout proj * A * ReflectionAbout proj

/-- A stage round is unitary when its target is an orthogonal projector and its base matrix is
unitary. -/
theorem stageRound_unitary {proj A : Matrix H H ℂ}
    (hproj : IsOrthogonalProjector proj) (hA : A ∈ Matrix.unitaryGroup H ℂ) :
    stageRound proj A ∈ Matrix.unitaryGroup H ℂ := by
  have hR : ReflectionAbout proj ∈ Matrix.unitaryGroup H ℂ := reflectionAbout_unitary hproj
  exact unitary_mul (unitary_mul hR hA) hR

/-- A stage round commutes with `P` when both its target matrix and its base matrix commute with
`P`. -/
theorem stageRound_comm {proj A P : Matrix H H ℂ}
    (hprojP : proj * P = P * proj) (hAP : A * P = P * A) :
    stageRound proj A * P = P * stageRound proj A := by
  have hR : ReflectionAbout proj * P = P * ReflectionAbout proj := targetMark_comm hprojP
  unfold stageRound
  calc
    ReflectionAbout proj * A * ReflectionAbout proj * P
        = ReflectionAbout proj * A * (ReflectionAbout proj * P) := by noncomm_ring
    _ = ReflectionAbout proj * A * (P * ReflectionAbout proj) := by rw [hR]
    _ = ReflectionAbout proj * (A * P) * ReflectionAbout proj := by noncomm_ring
    _ = ReflectionAbout proj * (P * A) * ReflectionAbout proj := by rw [hAP]
    _ = (ReflectionAbout proj * P) * A * ReflectionAbout proj := by noncomm_ring
    _ = (P * ReflectionAbout proj) * A * ReflectionAbout proj := by rw [hR]
    _ = P * (ReflectionAbout proj * A * ReflectionAbout proj) := by noncomm_ring

/-- The matrix `P + (1 - P) * W`, which preserves stopped components and applies `W` on the
complementary component. -/
def coherentStage (P W : Matrix H H ℂ) : Matrix H H ℂ :=
  P + (1 - P) * W

/-- The coherent stage fixes the range of an orthogonal stop projector when `W` commutes with
it. -/
theorem coherentStage_mul_stop {P W : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hcomm : W * P = P * W) :
    coherentStage P W * P = P := by
  have hid : P * P = P := hP.1
  unfold coherentStage
  calc
    (P + (1 - P) * W) * P = P * P + (1 - P) * (W * P) := by
      rw [Matrix.add_mul, Matrix.mul_assoc]
    _ = P + (1 - P) * (P * W) := by rw [hid, hcomm]
    _ = P + ((1 - P) * P) * W := by rw [← Matrix.mul_assoc]
    _ = P + 0 * W := by
      have hz : (1 - P) * P = 0 := by
        rw [Matrix.sub_mul, Matrix.one_mul, hid]
        simp
      have hz2 : ((1 - P) * P) * W = 0 := by rw [hz, Matrix.zero_mul]
      rw [hz2, Matrix.zero_mul, _root_.add_zero]
    _ = P := by simp

/-- The coherent stage is unitary when `P` is an orthogonal projector and `W` is a commuting
unitary. -/
theorem coherentStage_unitary {P W : Matrix H H ℂ}
    (hP : IsOrthogonalProjector P) (hW : W ∈ Matrix.unitaryGroup H ℂ)
    (hcomm : W * P = P * W) :
    coherentStage P W ∈ Matrix.unitaryGroup H ℂ := by
  have hid : P * P = P := hP.1
  have hstar : Pᴴ = P := hP.2
  have hW1 : Wᴴ * W = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hW
    simpa only [Matrix.star_eq_conjTranspose] using! h
  have hcompl : (1 - P)ᴴ = 1 - P := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hstar]
  have hcompl' : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hid]
    simp
  have hcompl'' : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hid]
    simp
  have hcomplsq : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.mul_sub, Matrix.mul_one, hcompl']
    simp
  have hcomm' : Wᴴ * P = P * Wᴴ := by
    have h := congrArg Matrix.conjTranspose hcomm
    simpa only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, hstar] using! h.symm
  have hkey : Wᴴ * (1 - P) = (1 - P) * Wᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, hcomm', Matrix.sub_mul, Matrix.one_mul]
  have hA : P * ((1 - P) * W) = 0 := by
    rw [← Matrix.mul_assoc, hcompl'', Matrix.zero_mul]
  have hB : ((1 - P) * Wᴴ) * P = 0 := by
    rw [Matrix.mul_assoc, hcomm', ← Matrix.mul_assoc, hcompl', Matrix.zero_mul]
  have hC : ((1 - P) * Wᴴ) * ((1 - P) * W) = 1 - P := by
    calc
      ((1 - P) * Wᴴ) * ((1 - P) * W) = (1 - P) * (Wᴴ * ((1 - P) * W)) := by
        rw [Matrix.mul_assoc]
      _ = (1 - P) * ((Wᴴ * (1 - P)) * W) := by
        have h : Wᴴ * ((1 - P) * W) = (Wᴴ * (1 - P)) * W := by rw [← Matrix.mul_assoc]
        rw [h]
      _ = (1 - P) * (((1 - P) * Wᴴ) * W) := by rw [hkey]
      _ = (1 - P) * (Wᴴ * W) := by
        have h1 : (1 - P) * (((1 - P) * Wᴴ) * W) = (1 - P) * ((1 - P) * (Wᴴ * W)) := by
          rw [Matrix.mul_assoc]
        have h2 : (1 - P) * ((1 - P) * (Wᴴ * W)) = (1 - P) * (Wᴴ * W) := by
          rw [← Matrix.mul_assoc, hcomplsq]
        rw [h1, h2]
      _ = 1 - P := by rw [hW1, Matrix.mul_one]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  have hconj : (coherentStage P W)ᴴ = P + (1 - P) * Wᴴ := by
    simp only [coherentStage, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hcompl, hkey,
      hstar]
  rw [hconj]
  calc
    (P + (1 - P) * Wᴴ) * (P + (1 - P) * W)
        = P * P + P * ((1 - P) * W) + ((1 - P) * Wᴴ) * P
            + ((1 - P) * Wᴴ) * ((1 - P) * W) := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
          noncomm_ring
    _ = 1 := by
          rw [hid, hA, hB, hC]
          simp only [_root_.add_zero]
          rw [_root_.add_comm, _root_.sub_add_cancel]

/-- The stop projector at the natural-number index underlying a stage in `Fin m`. -/
def stopAt {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}
    (stop : Fin (m + 1) → Matrix H H ℂ) (j : Fin m) : Matrix H H ℂ :=
  stop ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩

/-- A coherent variable-time frame with a target projector, nested stop projectors starting at
zero, and unitary base stages satisfying the required commutation relations. -/
structure CoherentVtFrame (H : Type) [Fintype H] [DecidableEq H] (m : ℕ) where

  target : Matrix H H ℂ

  targetOrth : IsOrthogonalProjector target

  stop : Fin (m + 1) → Matrix H H ℂ

  stopNested : IsNestedStopFamily m stop

  stopZero : stop 0 = 0

  targetCommutes : ∀ j, target * stop j = stop j * target

  base : Fin m → Matrix H H ℂ

  baseUnitary : ∀ j, base j ∈ Matrix.unitaryGroup H ℂ

  baseCommutes : ∀ j, base j * stopAt stop j = stopAt stop j * base j

namespace CoherentVtFrame

variable {m : ℕ}

/-- The stop projector immediately preceding stage `j` in the frame. -/
def stopAt (f : CoherentVtFrame H m) (j : Fin m) : Matrix H H ℂ :=
  Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.stopAt f.stop j

/-- The reflection-conjugated base round at stage `j`. -/
def round (f : CoherentVtFrame H m) (j : Fin m) : Matrix H H ℂ :=
  stageRound f.target (f.base j)

/-- Every base round of a coherent variable-time frame is unitary. -/
theorem round_unitary (f : CoherentVtFrame H m) (j : Fin m) :
    f.round j ∈ Matrix.unitaryGroup H ℂ :=
  stageRound_unitary f.targetOrth (f.baseUnitary j)

/-- The round at stage `j` commutes with its preceding stop projector. -/
theorem round_comm (f : CoherentVtFrame H m) (j : Fin m) :
    f.round j * f.stopAt j = f.stopAt j * f.round j :=
  stageRound_comm (f.targetCommutes (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) (f.baseCommutes j)

/-- The coherent stage that fixes the preceding stopped subspace and performs the round on its
complement. -/
def stageOp (f : CoherentVtFrame H m) (j : Fin m) : Matrix H H ℂ :=
  coherentStage (f.stopAt j) (f.round j)

/-- The stage operator at a natural-number index equipped with a proof that the index is in
range. -/
def stageOpAt (f : CoherentVtFrame H m) (j : ℕ) (hj : j < m) : Matrix H H ℂ :=
  f.stageOp ⟨j, hj⟩

/-- The naturally indexed stage operator is independent of the chosen proof of its index bound. -/
theorem stageOpAt_eq (f : CoherentVtFrame H m) (j : ℕ) (h1 h2 : j < m) :
    f.stageOpAt j h1 = f.stageOpAt j h2 := by
  have hfin : (⟨j, h1⟩ : Fin m) = ⟨j, h2⟩ := Fin.ext rfl
  unfold stageOpAt
  rw [hfin]

/-- Every coherent stage operator of the frame is unitary. -/
theorem stageOp_unitary (f : CoherentVtFrame H m) (j : Fin m) :
    f.stageOp j ∈ Matrix.unitaryGroup H ℂ :=
  coherentStage_unitary (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩))
    (f.round_unitary j) (f.round_comm j)

/-- The stage operator fixes the range of its preceding stop projector. -/
theorem stageOp_mul_stop (f : CoherentVtFrame H m) (j : Fin m) :
    f.stageOp j * f.stopAt j = f.stopAt j :=
  coherentStage_mul_stop (f.stopNested.1 (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)) (f.round_comm j)

/-- The increment between the stop projectors after and before stage `j`. -/
def freshStop (f : CoherentVtFrame H m) (j : Fin m) : Matrix H H ℂ :=
  f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ - f.stopAt j

/-- The fresh stop increment at a stage is an orthogonal projector. -/
theorem freshStop_orth (f : CoherentVtFrame H m) (j : Fin m) :
    IsOrthogonalProjector (f.freshStop j) := by
  have hle : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  simpa [freshStop] using! nestedStopFamily_inc_orth f.stopNested hle

/-- The fresh stop increment and the preceding stop projector have zero product in both orders. -/
theorem freshStop_orthogonal (f : CoherentVtFrame H m) (j : Fin m) :
    f.stopAt j * f.freshStop j = 0 ∧ f.freshStop j * f.stopAt j = 0 := by
  have hle : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (m + 1))
      ≤ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
    simp only [Fin.le_def]
    omega
  simpa [freshStop] using! nestedStopFamily_inc_orthogonal f.stopNested hle

end CoherentVtFrame

/-- The odd visit count `2 * k + 1` for an amplification stage. -/
def stageVisits (k : ℕ) : ℕ := 2 * k + 1

/-- The dyadic cost `2 ^ j` of one visit to stage `j`. -/
def stageVisitTime (j : ℕ) : ℕ := 2 ^ j

/-- The total stage time, given by its visit count times its dyadic visit cost. -/
def stageTime (j k : ℕ) : ℕ := stageVisits k * stageVisitTime j

/-- The count of two flag operations in one round. -/
def roundFlagCount : ℕ := 2

/-- The total flag-operation count, given by two operations per stage visit. -/
def stageFlagCount (k : ℕ) : ℕ := stageVisits k * roundFlagCount

/-- The inverse-stage time, defined to equal the forward-stage time. -/
def stageInverseTime (j k : ℕ) : ℕ := stageTime j k

/-- The inverse-stage flag count, defined to equal the forward-stage flag count. -/
def stageInverseFlagCount (k : ℕ) : ℕ := stageFlagCount k

variable {m : ℕ}

/-- The amplification workspace with a flag register indexed by `Fin 1`. -/
abbrev VtWorkspace (H : Type) : Type := Qatlib.Concepts.QlsReadoutSpec.Amplification.Space H 1

/-- A matrix macro tagged either as a flag operation or as an access to a numbered oracle slot. -/
inductive VtMacro (H : Type) where

  | flag : Matrix (VtWorkspace H) (VtWorkspace H) ℂ → VtMacro H

  | access : ℕ → Matrix (VtWorkspace H) (VtWorkspace H) ℂ → VtMacro H

/-- The matrix carried by a variable-time macro. -/
def VtMacro.matrix {H : Type} : VtMacro H → Matrix (VtWorkspace H) (VtWorkspace H) ℂ
  | .flag U => U
  | .access _ U => U

/-- The oracle slot accessed by a macro, or `none` for a flag operation. -/
def VtMacro.slot {H : Type} : VtMacro H → Option ℕ
  | .flag _ => none
  | .access i _ => some i

/-- The number of accesses to slot `i` in a macro list. -/
def VtMacro.accessCount {H : Type} (i : ℕ) : List (VtMacro H) → ℕ
  | [] => 0
  | .flag _ :: L => VtMacro.accessCount i L
  | .access j _ :: L => (if j = i then 1 else 0) + VtMacro.accessCount i L

/-- The number of flag operations in a macro list. -/
def VtMacro.flagCount {H : Type} : List (VtMacro H) → ℕ
  | [] => 0
  | .flag _ :: L => 1 + VtMacro.flagCount L
  | .access _ _ :: L => VtMacro.flagCount L

/-- The list of matrices obtained by forgetting macro tags. -/
def VtMacro.matrixList {H : Type} :
    List (VtMacro H) → List (Matrix (VtWorkspace H) (VtWorkspace H) ℂ)
  | [] => []
  | .flag U :: L => U :: VtMacro.matrixList L
  | .access _ U :: L => U :: VtMacro.matrixList L

/-- Access counts at a fixed slot add under concatenation of macro lists. -/
theorem VtMacro.accessCount_append {H : Type} (i : ℕ) (L D : List (VtMacro H)) :
    VtMacro.accessCount i (L ++ D) = VtMacro.accessCount i L + VtMacro.accessCount i D := by
  induction L with
  | nil => simp [VtMacro.accessCount]
  | cons a L ih => cases a <;> simp [VtMacro.accessCount, ih, Nat.add_assoc]

/-- Flag-operation counts add under concatenation of macro lists. -/
theorem VtMacro.flagCount_append {H : Type} (L D : List (VtMacro H)) :
    VtMacro.flagCount (L ++ D) = VtMacro.flagCount L + VtMacro.flagCount D := by
  induction L with
  | nil => simp [VtMacro.flagCount]
  | cons a L ih => cases a <;> simp [VtMacro.flagCount, ih, Nat.add_assoc]

/-- Forgetting macro tags preserves list concatenation. -/
theorem VtMacro.matrixList_append {H : Type} (L D : List (VtMacro H)) :
    VtMacro.matrixList (L ++ D) = VtMacro.matrixList L ++ VtMacro.matrixList D := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases a with
    | flag U => simp [VtMacro.matrixList, ih]
    | access i U => simp [VtMacro.matrixList, ih]

namespace CoherentVtFrame

variable {m : ℕ}

/-- The controlled target reflection on the frame's amplification workspace. -/
def flagReflection (f : CoherentVtFrame H m) :
    Matrix (VtWorkspace H) (VtWorkspace H) ℂ :=
  Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (ReflectionAbout f.target) (Finset.univ : Finset (Fin 1))

/-- The frame's controlled target reflection is self-adjoint. -/
theorem flagReflection_conjTranspose (f : CoherentVtFrame H m) :
    f.flagReflectionᴴ = f.flagReflection := by
  unfold flagReflection
  rw [controlled_conjTranspose, reflectionAbout_conjTranspose f.targetOrth]

/-- The frame's controlled target reflection is unitary. -/
theorem flagReflection_unitary (f : CoherentVtFrame H m) :
    f.flagReflection ∈ Matrix.unitaryGroup (VtWorkspace H) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    flagReflection_conjTranspose]
  have h := controlled_mul_conjTranspose (reflectionAbout_unitary f.targetOrth)
    (Finset.univ : Finset (Fin 1))
  rw [controlled_conjTranspose, reflectionAbout_conjTranspose f.targetOrth] at h
  exact h

/-- The paid round consisting of a target reflection, a forward call to stage `j`, and a second
target reflection. -/
def stagePaidRound (f : CoherentVtFrame H m) (j : Fin m) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1 :=
  [Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known f.flagReflection,
   Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call j.val Finset.univ false,
   Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known f.flagReflection]

/-- The inverse paid round with an adjoint oracle call between two target reflections. -/
def stagePaidRoundInverse (f : CoherentVtFrame H m) (j : Fin m) : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1 :=
  [Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known f.flagReflection,
   Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.call j.val Finset.univ true,
   Qatlib.Concepts.QlsReadoutSpec.Amplification.Step.known f.flagReflection]

/-- The paid word formed by repeating a forward stage round the specified number of times. -/
def stagePaidWord (f : CoherentVtFrame H m) (j : Fin m) : ℕ → Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1
  | 0 => []
  | k + 1 => f.stagePaidRound j ++ f.stagePaidWord j k

/-- The paid word formed by repeating the inverse stage round the specified number of times. -/
def stagePaidWordInverse (f : CoherentVtFrame H m) (j : Fin m) : ℕ → Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1
  | 0 => []
  | k + 1 => f.stagePaidWordInverse j k ++ f.stagePaidRoundInverse j

/-- The concatenation of all paid stage words, using `2 * rounds j + 1` visits at each stage. -/
def coherentPaidWord (f : CoherentVtFrame H m) (rounds : Fin m → ℕ) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 1 :=
  ((List.finRange m).map (fun j => f.stagePaidWord j (2 * rounds j + 1))).flatten

/-- The base-oracle family, equal to the frame's base matrices on valid slots and to the
identity elsewhere. -/
def baseOracles (f : CoherentVtFrame H m) : ℕ → Matrix H H ℂ :=
  fun j => if h : j < m then f.base ⟨j, h⟩ else 1

/-- The variable-time amplification program built from the coherent paid word and the full
readout set. -/
def coherentVtProgram (f : CoherentVtFrame H m) (rounds : Fin m → ℕ) :
    VtAmpProgram H :=
  { r := 1, word := f.coherentPaidWord rounds, readout := Finset.univ }

/-- The workspace matrix of a known gate or a controlled forward or adjoint oracle call. -/
def stepMatrixOf (oracles : ℕ → Matrix H H ℂ) (s : Qatlib.Concepts.QlsReadoutSpec.Amplification.Step H 1) :
    Matrix (VtWorkspace H) (VtWorkspace H) ℂ :=
  match s with
  | .known U => U
  | .call i T adj => Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (if adj then (oracles i)ᴴ else oracles i) T

/-- The matrix list for a forward stage round on the amplification workspace. -/
def stageRoundMacros (f : CoherentVtFrame H m) (j : Fin m) :
    List (Matrix (VtWorkspace H) (VtWorkspace H) ℂ) :=
  [f.flagReflection,
   Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (f.baseOracles j.val) (Finset.univ : Finset (Fin 1)),
   f.flagReflection]

/-- The matrix list for an inverse stage round on the amplification workspace. -/
def stageRoundInverseMacros (f : CoherentVtFrame H m) (j : Fin m) :
    List (Matrix (VtWorkspace H) (VtWorkspace H) ℂ) :=
  [f.flagReflection,
   Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (f.baseOracles j.val)ᴴ (Finset.univ : Finset (Fin 1)),
   f.flagReflection]

/-- The matrix list obtained by repeating the forward stage-round list. -/
def stageWordMacros (f : CoherentVtFrame H m) (j : Fin m) :
    ℕ → List (Matrix (VtWorkspace H) (VtWorkspace H) ℂ)
  | 0 => []
  | n + 1 => f.stageRoundMacros j ++ f.stageWordMacros j n

/-- The matrix list obtained by repeating the inverse stage-round list. -/
def stageWordInverseMacros (f : CoherentVtFrame H m) (j : Fin m) :
    ℕ → List (Matrix (VtWorkspace H) (VtWorkspace H) ℂ)
  | 0 => []
  | n + 1 => f.stageWordInverseMacros j n ++ f.stageRoundInverseMacros j

/-- The tagged macro list for one forward stage round, with two flag operations and one access
to slot `j`. -/
def stageMacroRound (f : CoherentVtFrame H m) (j : Fin m) : List (VtMacro H) :=
  [VtMacro.flag f.flagReflection,
   VtMacro.access j.val
     (Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (f.baseOracles j.val) (Finset.univ : Finset (Fin 1))),
   VtMacro.flag f.flagReflection]

/-- The tagged macro list for one inverse stage round, with an adjoint access to slot `j`. -/
def stageMacroRoundInverse (f : CoherentVtFrame H m) (j : Fin m) : List (VtMacro H) :=
  [VtMacro.flag f.flagReflection,
   VtMacro.access j.val
     (Qatlib.Concepts.QlsReadoutSpec.Amplification.controlled (f.baseOracles j.val)ᴴ (Finset.univ : Finset (Fin 1))),
   VtMacro.flag f.flagReflection]

/-- The tagged macro list formed by repeating forward stage rounds. -/
def stageMacroList (f : CoherentVtFrame H m) (j : Fin m) : ℕ → List (VtMacro H)
  | 0 => []
  | n + 1 => f.stageMacroRound j ++ f.stageMacroList j n

/-- The tagged macro list formed by repeating inverse stage rounds. -/
def stageMacroListInverse (f : CoherentVtFrame H m) (j : Fin m) : ℕ → List (VtMacro H)
  | 0 => []
  | n + 1 => f.stageMacroListInverse j n ++ f.stageMacroRoundInverse j

end CoherentVtFrame

/-- The total squared norm of the target-projected state. -/
def successAmplitude (f : CoherentVtFrame H m) (ψ : QState H) : ℝ :=
  MeasureProb (ApplyGate f.target ψ) Finset.univ

/-- The target-projected squared norm is nonnegative. -/
theorem successAmplitude_nonneg (f : CoherentVtFrame H m) (ψ : QState H) :
    0 ≤ successAmplitude f ψ := measureProb_nonneg _ _

namespace CoherentVtFrame

variable {m : ℕ}

/-- The state obtained by applying `n` consecutive coherent stages starting at offset `d`. -/
def stageStateFrom (f : CoherentVtFrame H m) (ψ : QState H) (d n : ℕ)
    (h : d + n ≤ m) : QState H :=
  match n with
  | 0 => ψ
  | n + 1 => ApplyGate (f.stageOp ⟨n + d, by omega⟩)
      (stageStateFrom f ψ d n (by omega))

/-- The state after the first `n` coherent stages. -/
def stageState (f : CoherentVtFrame H m) (ψ : QState H) (n : ℕ) (h : n ≤ m) : QState H :=
  f.stageStateFrom ψ 0 n (by omega)

/-- A record of a stage index, its input and output states, and its reached and fresh stop
matrices. -/
structure StageRecord (H : Type) [Fintype H] [DecidableEq H] where

  stageIndex : ℕ

  inputState : QState H

  outputState : QState H

  reachedStop : Matrix H H ℂ

  freshStop : Matrix H H ℂ

/-- The record of stage `j` in the coherent evolution starting from `ψ`. -/
def stageRecord (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : StageRecord H where
  stageIndex := j.val
  inputState := f.stageState ψ j.val (by omega)
  outputState := f.stageState ψ (j.val + 1) (by omega)
  reachedStop := f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  freshStop := f.freshStop j

/-- The component of `ψ` selected by the stop projector preceding stage `j`. -/
def frozenFragment (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : QState H :=
  ApplyGate (f.stopAt j) ψ

/-- The component of `ψ` complementary to the stop projector preceding stage `j`. -/
def runningFragment (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : QState H :=
  ApplyGate (1 - f.stopAt j) ψ

/-- The component of `ψ` complementary to the stop projector following stage `j`. -/
def runningFragmentAfter (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : QState H :=
  ApplyGate (1 - f.stop ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) ψ

/-- The squared norm of the stopped component of the state after `n` stages. -/
def stoppedMass (f : CoherentVtFrame H m) (ψ : QState H) (n : ℕ) (h : n ≤ m) : ℝ :=
  MeasureProb (ApplyGate (f.stop ⟨n, Nat.lt_succ_of_le h⟩) (f.stageState ψ n h))
    Finset.univ

/-- The target-projected squared norm after all coherent stages. -/
def runSuccess (f : CoherentVtFrame H m) (ψ : QState H) : ℝ :=
  MeasureProb (ApplyGate f.target (f.stageState ψ m (by omega))) Finset.univ

end CoherentVtFrame

/-- The target value `2 / 3` for amplitude amplification. -/
def aaTarget : ℝ := 2 / 3

/-- The natural-number floor of the tight amplitude-amplification window. -/
def aaRounds (p : ℝ) : ℕ := Nat.floor (tightAAWindow p)

/-- The odd amplification multiplier `2 * m + 1`. -/
def aaMultiplier (m : ℕ) : ℕ := 2 * m + 1

/-- The tight amplitude-amplification window is nonnegative for a positive input. -/
theorem tightAAWindow_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ tightAAWindow ε := by
  have hΘpos : 0 < Real.arcsin (Real.sqrt ε) := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hε)
  have h4pos : 0 < 4 * Real.arcsin (Real.sqrt ε) := by positivity
  have hfrac : 1 / 2 ≤ Real.pi / (4 * Real.arcsin (Real.sqrt ε)) := by
    rw [le_div_iff₀ h4pos]
    linarith [Real.arcsin_le_pi_div_two (Real.sqrt ε)]
  unfold tightAAWindow
  linarith

/-- For positive `p`, the chosen round count is at most `tightAAWindow p`. -/
theorem aaRounds_window {p : ℝ} (hp : 0 < p) : (aaRounds p : ℝ) ≤ tightAAWindow p :=
  Nat.floor_le (tightAAWindow_nonneg hp)

/-- A rule selecting a natural round count bounded by the tight amplification window for every
positive input. -/
structure StagePolicy where

  roundsAt : ℝ → ℕ

  roundsAt_window : ∀ p, 0 < p → (roundsAt p : ℝ) ≤ tightAAWindow p

/-- The stage policy obtained by taking the floor of the tight amplification window. -/
def aaPolicy : StagePolicy where
  roundsAt := aaRounds
  roundsAt_window := fun p hp => aaRounds_window hp

/-- The stagewise round schedule obtained by applying a policy to the measured values. -/
def policySchedule (pol : StagePolicy) (measured : Fin m → ℝ) : Fin m → ℕ :=
  fun j => pol.roundsAt (measured j)

/-- The target-projected squared norm after the base operation acts on the current running
component. -/
def baseStageSuccess (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : ℝ :=
  MeasureProb (ApplyGate f.target
    (ApplyGate (f.base j)
      (f.runningFragment (f.stageState ψ j.val (Nat.le_of_lt j.isLt)) j))) Finset.univ

/-- The target-projected squared norm after one reflection-conjugated round acts on the current
running component. -/
def ampStageSuccess (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : ℝ :=
  MeasureProb (ApplyGate f.target
    (ApplyGate (f.round j)
      (f.runningFragment (f.stageState ψ j.val (Nat.le_of_lt j.isLt)) j))) Finset.univ

/-- The amplified stage-success values indexed from one to `m`, extended by zero outside that
range. -/
def measuredRs (f : CoherentVtFrame H m) (ψ : QState H) : ℕ → ℝ :=
  fun j => if h : 1 ≤ j ∧ j ≤ m then ampStageSuccess f ψ ⟨j - 1, by omega⟩ else 0

/-- The base stage-success values indexed from one to `m`, extended by zero outside that range. -/
def measuredRs' (f : CoherentVtFrame H m) (ψ : QState H) : ℕ → ℝ :=
  fun j => if h : 1 ≤ j ∧ j ≤ m then baseStageSuccess f ψ ⟨j - 1, by omega⟩ else 0

/-- The state obtained by applying the matrix `P` to `ψ`. -/
def projGood (P : Matrix H H ℂ) (ψ : QState H) : QState H := ApplyGate P ψ

/-- The total squared norm of `P` applied to `ψ`. -/
def projMass (P : Matrix H H ℂ) (ψ : QState H) : ℝ :=
  MeasureProb (ApplyGate P ψ) Finset.univ

/-- The projected squared norm `projMass P ψ` is nonnegative. -/
theorem projMass_nonneg (P : Matrix H H ℂ) (ψ : QState H) : 0 ≤ projMass P ψ :=
  measureProb_nonneg _ _

/-- The marking matrix `1 - 2 • P`, which negates the range of a projector `P`. -/
def sourceMark (P : Matrix H H ℂ) : Matrix H H ℂ := 1 - (2 : ℂ) • P

/-- Applying the source marking matrix gives `x - 2 • (P *ᵥ x)`. -/
theorem sourceMark_apply (P : Matrix H H ℂ) (x : QState H) :
    ApplyGate (sourceMark P) x = x - (2 : ℂ) • (P *ᵥ x) := by
  simp [sourceMark, ApplyGate, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- The source marking matrix of an orthogonal projector is unitary. -/
theorem sourceMark_unitary {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) :
    sourceMark P ∈ Matrix.unitaryGroup H ℂ := by
  have hR : ReflectionAbout P ∈ Matrix.unitaryGroup H ℂ := reflectionAbout_unitary hP
  have hneg : sourceMark P = -(ReflectionAbout P) := by
    unfold sourceMark ReflectionAbout
    module
  rw [hneg, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_neg, neg_mul_neg]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hR
  exact hR

/-- Gate application agrees with matrix-vector multiplication. -/
private theorem applyGate_eq_mulVec (U : Matrix H H ℂ) (ψ : QState H) :
    ApplyGate U ψ = U *ᵥ ψ := rfl

/-- The state inner product distributes over addition in its second argument. -/
private theorem inner_add_right {I : Type} [Fintype I] [DecidableEq I]
    (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ + χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ + Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Negating the second argument negates the state inner product. -/
private theorem inner_neg_right {I : Type} [Fintype I] [DecidableEq I]
    (ψ φ : QState I) : Qatlib.Foundations.PureStateMath.Inner ψ (-φ) = -Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  rw [inner_apply, inner_apply]
  simp [Pi.neg_apply, Finset.sum_neg_distrib]

/-- The state inner product distributes over subtraction in its second argument. -/
private theorem inner_sub_right {I : Type} [Fintype I] [DecidableEq I]
    (ψ φ χ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (φ - χ) = Qatlib.Foundations.PureStateMath.Inner ψ φ - Qatlib.Foundations.PureStateMath.Inner ψ χ := by
  rw [sub_eq_add_neg, inner_add_right, inner_neg_right]
  ring

/-- For an orthogonal projector, the self inner product of the projected state equals the inner
product of the original and projected states. -/
private theorem inner_projector {I : Type} [Fintype I] [DecidableEq I]
    {P : Matrix I I ℂ} (hP : IsOrthogonalProjector P) (ψ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate P ψ) (ApplyGate P ψ) =
      Qatlib.Foundations.PureStateMath.Inner ψ (ApplyGate P ψ) := by
  have hPP : P.conjTranspose * P = P := by
    have hstar : P.conjTranspose = P := hP.2
    rw [hstar]
    exact hP.1
  simp only [Qatlib.Foundations.PureStateMath.Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hPP,
    Matrix.dotProduct_mulVec]

/-- Moving a matrix from the second argument of the inner product to the first replaces it by
its conjugate transpose. -/
private theorem inner_mulVec_conjTranspose_right' {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (ψ φ : QState I) :
    Qatlib.Foundations.PureStateMath.Inner ψ (A *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner (Aᴴ *ᵥ ψ) φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

/-- The sum of squared coordinate norms equals measurement mass over the full index set. -/
private theorem sum_normSq_univ {I : Type} [Fintype I] [DecidableEq I] (ψ : QState I) :
    ∑ i, ‖ψ i‖ ^ 2 = MeasureProb ψ Finset.univ := by
  unfold MeasureProb BornProb
  simp

/-- Applying an orthogonal projector twice has the same effect as applying it once. -/
theorem projGood_idem {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (ψ : QState H) :
    ApplyGate P (ApplyGate P ψ) = ApplyGate P ψ := by
  have hid : P * P = P := hP.1
  simp [ApplyGate, Matrix.mulVec_mulVec, hid]

/-- An orthogonal projector annihilates the complementary component of a state. -/
theorem projGood_bad {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (ψ : QState H) :
    ApplyGate P (ψ - ApplyGate P ψ) = 0 := by
  have hid : P * P = P := hP.1
  simp [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hid, sub_self]

/-- Matrix-vector multiplication by an orthogonal projector annihilates the complementary
component of a state. -/
theorem projGood_bad_mulVec {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    (ψ : QState H) : P *ᵥ (ψ - ApplyGate P ψ) = 0 := by
  rw [← applyGate_eq_mulVec]
  exact projGood_bad hP ψ

/-- Matrix-vector multiplication by an orthogonal projector fixes the projected component. -/
theorem projGood_idem_mulVec {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    (ψ : QState H) : P *ᵥ (ApplyGate P ψ) = ApplyGate P ψ := by
  rw [← applyGate_eq_mulVec]
  exact projGood_idem hP ψ

/-- The projected and complementary components of a state have zero inner product. -/
theorem inner_good_bad {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (ψ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate P ψ) (ψ - ApplyGate P ψ) = 0 := by
  have hcompl : (1 - P) *ᵥ ψ = ψ - P *ᵥ ψ := by
    have hsum : (1 - P) + P = 1 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> ring
    have h : (1 - P) *ᵥ ψ + P *ᵥ ψ = ψ := by
      rw [← Matrix.add_mulVec, hsum, Matrix.one_mulVec]
    have h2 : ψ - P *ᵥ ψ = (1 - P) *ᵥ ψ + P *ᵥ ψ - P *ᵥ ψ := by rw [h]
    have h3 : (1 - P) *ᵥ ψ + P *ᵥ ψ - P *ᵥ ψ = (1 - P) *ᵥ ψ := by abel
    rw [h3] at h2
    exact h2.symm
  have hstar : (1 - P)ᴴ = 1 - P := by
    have hPstar : Pᴴ = P := hP.2
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPstar]
  have hzero : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hP.1]
    simp
  have hzero' : (1 - P) *ᵥ (P *ᵥ ψ) = 0 := by
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  rw [applyGate_eq_mulVec, ← hcompl, inner_mulVec_conjTranspose_right', hstar, hzero']
  simp [Qatlib.Foundations.PureStateMath.Inner]

/-- The self inner product of the projected state equals its projected mass, embedded in `ℂ`. -/
theorem inner_good_self {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (ψ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner (ApplyGate P ψ) (ApplyGate P ψ) = ((projMass P ψ : ℝ) : ℂ) := by
  unfold projMass
  rw [inner_self, ← Complex.ofReal_sum, ← sum_normSq_univ]

/-- The inner product of a state with its orthogonal projection equals its projected mass,
embedded in `ℂ`. -/
theorem inner_psi_good {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) (ψ : QState H) :
    Qatlib.Foundations.PureStateMath.Inner ψ (ApplyGate P ψ) = ((projMass P ψ : ℝ) : ℂ) := by
  rw [← inner_projector hP ψ, inner_good_self hP ψ]

/-- For a normalized state, the inner product with its complementary component equals one minus
its projected mass. -/
theorem inner_psi_bad {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) :
    Qatlib.Foundations.PureStateMath.Inner ψ (ψ - ApplyGate P ψ) = ((1 - projMass P ψ : ℝ) : ℂ) := by
  rw [inner_sub_right, inner_self_eq_one hψ, inner_psi_good hP ψ]
  push_cast
  ring

/-- Conjugating an outer-product matrix by `A` gives the outer product of the transformed
vector. -/
private theorem outerProduct_conj' (A : Matrix H H ℂ) (φ : QState H) :
    A * outerProduct φ * Aᴴ = outerProduct (A *ᵥ φ) := by
  ext i j
  simp only [outerProduct, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    starRingEnd_apply, Matrix.mulVec, dotProduct]
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  conv_rhs => rw [star_mul]
  ring

/-- Unitary conjugation transports reflection about `σ` to reflection about `A *ᵥ σ`. -/
theorem sourceReflect_conj {A : Matrix H H ℂ} (hA : A ∈ Matrix.unitaryGroup H ℂ)
    (σ : QState H) :
    A * ReflectionAbout (outerProduct σ) * Aᴴ = ReflectionAbout (outerProduct (A *ᵥ σ)) := by
  have hAA : A * Aᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hA
    exact mul_eq_one_comm.mp hA
  show A * ((2 : ℂ) • outerProduct σ - 1) * Aᴴ
      = (2 : ℂ) • outerProduct (A *ᵥ σ) - (1 : Matrix H H ℂ)
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hAA, outerProduct_conj']

/-- The source amplification iterate formed from a conjugated source reflection followed by the
target marking matrix. -/
def sourceIterate (A : Matrix H H ℂ) (σ : QState H) (P : Matrix H H ℂ) : Matrix H H ℂ :=
  A * ReflectionAbout (outerProduct σ) * Aᴴ * sourceMark P

/-- For unitary `A`, the source iterate is reflection about the prepared state followed by
target marking. -/
theorem sourceIterate_eq_prepared {A : Matrix H H ℂ} (hA : A ∈ Matrix.unitaryGroup H ℂ)
    (σ : QState H) (P : Matrix H H ℂ) :
    sourceIterate A σ P = ReflectionAbout (outerProduct (A *ᵥ σ)) * sourceMark P := by
  unfold sourceIterate
  rw [sourceReflect_conj hA σ]

/-- The source iterate is unitary for a unitary preparation matrix, normalized source state, and
orthogonal target projector. -/
theorem sourceIterate_unitary {A : Matrix H H ℂ} (hA : A ∈ Matrix.unitaryGroup H ℂ)
    {σ : QState H} (hσ : Normalized σ) {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P) :
    sourceIterate A σ P ∈ Matrix.unitaryGroup H ℂ := by
  rw [sourceIterate_eq_prepared hA σ]
  exact (Matrix.unitaryGroup H ℂ).mul_mem
    (outerProduct_reflection_unitary (normalized_applyGate hA hσ))
    (sourceMark_unitary hP)

/-- The source marking matrix acts by subtracting twice the projected component. -/
private theorem sourceMark_mulVec (P : Matrix H H ℂ) (x : QState H) :
    sourceMark P *ᵥ x = x - (2 : ℂ) • (P *ᵥ x) := by
  simp [sourceMark, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

/-- Reflection about `P` acts by twice the projected component minus the original vector. -/
private theorem reflectionAbout_mulVec (P : Matrix H H ℂ) (x : QState H) :
    ReflectionAbout P *ᵥ x = (2 : ℂ) • (P *ᵥ x) - x := by
  have h := applyGate_reflectionAbout P x
  rw [applyGate_eq_mulVec] at h
  exact h

/-- The reflection-marking product acts on the given good and bad components by the stated
two-component linear combinations. -/
private theorem reflection_mark_action' (ψ good bad : QState H) (P : Matrix H H ℂ)
    (hsum : good + bad = ψ) (hcb : P *ᵥ bad = 0) (hcg : P *ᵥ good = good)
    (hig hib : ℂ) (higEq : Qatlib.Foundations.PureStateMath.Inner ψ good = hig)
    (hibEq : Qatlib.Foundations.PureStateMath.Inner ψ bad = hib) :
    (ReflectionAbout (outerProduct ψ) * sourceMark P) *ᵥ bad
      = (2 * hib - 1) • bad + (2 * hib) • good ∧
    (ReflectionAbout (outerProduct ψ) * sourceMark P) *ᵥ good
      = (-2 * hig) • bad + (1 - 2 * hig) • good := by
  have hMb : sourceMark P *ᵥ bad = bad := by
    rw [sourceMark_mulVec, hcb, smul_zero, sub_zero]
  have hMg : sourceMark P *ᵥ good = -good := by
    rw [sourceMark_mulVec, hcg]
    module
  constructor
  · rw [← Matrix.mulVec_mulVec, hMb, reflectionAbout_mulVec, outerProduct_mulVec, hibEq,
      ← hsum]
    module
  · rw [← Matrix.mulVec_mulVec, hMg, reflectionAbout_mulVec, outerProduct_mulVec,
      inner_neg_right, higEq, ← hsum]
    module

/-- For a normalized state and orthogonal target projector, the reflection-marking product has
the stated two-component action with coefficients determined by the projected mass. -/
theorem source_two_component {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) :
    let good := ApplyGate P ψ
    let bad := ψ - ApplyGate P ψ
    let a := projMass P ψ
    (ReflectionAbout (outerProduct ψ) * sourceMark P) *ᵥ bad
        = ((1 - 2 * a : ℝ) : ℂ) • bad + ((2 * (1 - a) : ℝ) : ℂ) • good ∧
    (ReflectionAbout (outerProduct ψ) * sourceMark P) *ᵥ good
        = ((-2 * a : ℝ) : ℂ) • bad + ((1 - 2 * a : ℝ) : ℂ) • good := by
  have hsum : ApplyGate P ψ + (ψ - ApplyGate P ψ) = ψ := by abel
  have hcb : P *ᵥ (ψ - ApplyGate P ψ) = 0 := by
    rw [← applyGate_eq_mulVec]
    exact projGood_bad hP ψ
  have hcg : P *ᵥ (ApplyGate P ψ) = ApplyGate P ψ := by
    rw [← applyGate_eq_mulVec]
    exact projGood_idem hP ψ
  have hhig : Qatlib.Foundations.PureStateMath.Inner ψ (ApplyGate P ψ) = ((projMass P ψ : ℝ) : ℂ) :=
    inner_psi_good hP ψ
  have hhib : Qatlib.Foundations.PureStateMath.Inner ψ (ψ - ApplyGate P ψ) = ((1 - projMass P ψ : ℝ) : ℂ) :=
    inner_psi_bad hP hψ
  obtain ⟨hbad, hgood⟩ :=
    reflection_mark_action' ψ (ApplyGate P ψ) (ψ - ApplyGate P ψ) P hsum hcb hcg
      ((projMass P ψ : ℝ) : ℂ) ((1 - projMass P ψ : ℝ) : ℂ) hhig hhib
  refine ⟨?_, ?_⟩
  · rw [hbad]
    push_cast
    module
  · rw [hgood]
    push_cast
    module

/-- The two-component action of the reflection-marking product expressed using `ApplyGate`. -/
theorem source_two_component_applyGate {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) :
    let good := ApplyGate P ψ
    let bad := ψ - ApplyGate P ψ
    let a := projMass P ψ
    ApplyGate (ReflectionAbout (outerProduct ψ) * sourceMark P) bad
        = ((1 - 2 * a : ℝ) : ℂ) • bad + ((2 * (1 - a) : ℝ) : ℂ) • good ∧
    ApplyGate (ReflectionAbout (outerProduct ψ) * sourceMark P) good
        = ((-2 * a : ℝ) : ℂ) • bad + ((1 - 2 * a : ℝ) : ℂ) • good := by
  obtain ⟨hbad, hgood⟩ := source_two_component hP hψ
  refine ⟨?_, ?_⟩ <;> rw [applyGate_eq_mulVec] <;> assumption

/-- Combining two linear combinations of `bad` and `good` gives the prescribed coefficients
whenever the two scalar coefficient identities hold. -/
private theorem two_component_comb {V : Type} [AddCommMonoid V] [Module ℂ V]
    (bad good : V) (r1 r2 c1 c2 c3 c4 α' β' : ℂ)
    (h1 : r1 * c1 + r2 * c3 = α') (h2 : r1 * c2 + r2 * c4 = β') :
    r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good) = α' • bad + β' • good := by
  have hsplit : r1 • (c1 • bad + c2 • good) + r2 • (c3 • bad + c4 • good)
      = (r1 * c1 + r2 * c3) • bad + (r1 * c2 + r2 * c4) • good := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul, add_smul,
      add_smul]
    abel
  rw [hsplit, h1, h2]

/-- The bad-component coefficient recurrence equals the cosine ratio at angle `x + 2 * θ` when
the stated denominators are nonzero. -/
private theorem orbit_coef_bad (θ x : ℝ) (_hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    (Real.cos x / Real.cos θ) * (1 - 2*(Real.sin θ)^2)
      + (Real.sin x / Real.sin θ) * (-2*(Real.sin θ)^2)
      = Real.cos (x + 2*θ) / Real.cos θ := by
  have h1 : 1 - 2*(Real.sin θ)^2 = 2*(Real.cos θ)^2 - 1 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  field_simp
  rw [Real.cos_add, Real.cos_two_mul, Real.sin_two_mul, h1]
  ring

/-- The good-component coefficient recurrence equals the sine ratio at angle `x + 2 * θ` when
the stated denominators are nonzero. -/
private theorem orbit_coef_good (θ x : ℝ) (hs : Real.sin θ ≠ 0) (_hc : Real.cos θ ≠ 0) :
    (Real.cos x / Real.cos θ) * (2*(1 - (Real.sin θ)^2))
      + (Real.sin x / Real.sin θ) * (1 - 2*(Real.sin θ)^2)
      = Real.sin (x + 2*θ) / Real.sin θ := by
  have h1 : 1 - 2*(Real.sin θ)^2 = 2*(Real.cos θ)^2 - 1 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  have h2 : 1 - (Real.sin θ)^2 = (Real.cos θ)^2 := by
    have := Real.sin_sq_add_cos_sq θ
    linarith
  field_simp
  rw [Real.sin_add, Real.cos_two_mul, Real.sin_two_mul, h1, h2]
  ring

/-- The cosine is positive for an angle strictly between zero and `π / 2`. -/
private theorem cos_pos_of_lt_half_pi {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    0 < Real.cos θ := by
  have hsin : 0 < Real.sin (Real.pi / 2 - θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.sin_pi_div_two_sub θ] at hsin
  exact hsin

/-- Starting from a normalized state with target mass `sin² θ`, `k` reflection-marking iterates
give the stated good and bad components at angle `(2 * k + 1) * θ`. -/
theorem source_rotation {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (θ : ℝ) (k : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : projMass P ψ = (Real.sin θ)^2) :
    (ReflectionAbout (outerProduct ψ) * sourceMark P)^k *ᵥ ψ =
      ((Real.cos ((2*(k:ℝ)+1)*θ) / Real.cos θ : ℝ) : ℂ) • (ψ - ApplyGate P ψ) +
      ((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ) • (ApplyGate P ψ) := by
  have hs : Real.sin θ ≠ 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    positivity
  have hc : Real.cos θ ≠ 0 := by
    have := cos_pos_of_lt_half_pi hθ0 hθ1
    positivity
  induction k with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec]
      have h0 : (2*((0:ℕ):ℝ)+1)*θ = θ := by norm_num
      rw [h0, div_self hc, div_self hs]
      module
  | succ k ih =>
      obtain ⟨hbadstep, hgoodstep⟩ := source_two_component hP hψ
      have hang : (2*((k+1 : ℕ):ℝ)+1)*θ = (2*(k:ℝ)+1)*θ + 2*θ := by
        push_cast
        ring
      rw [hang, pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hbadstep, hgoodstep, hprob]
      refine two_component_comb _ _ _ _ _ _ _ _ _ _ ?_ ?_
      · exact_mod_cast orbit_coef_bad θ ((2*(k:ℝ)+1)*θ) hs hc
      · exact_mod_cast orbit_coef_good θ ((2*(k:ℝ)+1)*θ) hs hc

/-- Multiplying a state by a real scalar multiplies the sum of squared coordinate norms by the
scalar's square. -/
private theorem sum_normSq_smul (c : ℝ) (v : QState H) :
    ∑ i, ‖((((c : ℝ) : ℂ) • v) i)‖ ^ 2 = c ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  have hentry : ∀ i : H, ‖((((c : ℝ) : ℂ) • v) i)‖ ^ 2 = c ^ 2 * ‖v i‖ ^ 2 := by
    intro i
    have h1 : (((c : ℝ) : ℂ) • v) i = ((c : ℝ) : ℂ) * v i := rfl
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Finset.sum_congr rfl (fun i _ => hentry i), Finset.mul_sum]

/-- For a normalized state with target mass `sin² θ` and `0 < θ < π / 2`, the target mass after
`k` reflection-marking iterates is `sin² ((2 * k + 1) * θ)`. -/
theorem source_rotation_mass {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (θ : ℝ) (k : ℕ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : projMass P ψ = (Real.sin θ)^2) :
    projMass P ((ReflectionAbout (outerProduct ψ) * sourceMark P)^k *ᵥ ψ)
      = (Real.sin ((2*(k:ℝ)+1)*θ))^2 := by
  have hs : Real.sin θ ≠ 0 := by
    have := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    positivity
  have hrot := source_rotation hP hψ θ k hθ0 hθ1 hprob
  have hgood : ApplyGate P ((ReflectionAbout (outerProduct ψ) * sourceMark P)^k *ᵥ ψ)
      = ((Real.sin ((2*(k:ℝ)+1)*θ) / Real.sin θ : ℝ) : ℂ) • (ApplyGate P ψ) := by
    rw [hrot, applyGate_eq_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, projGood_bad_mulVec hP ψ, smul_zero, _root_.zero_add,
      projGood_idem_mulVec hP ψ]
  unfold projMass at hprob
  rw [projMass, ← sum_normSq_univ, hgood, sum_normSq_smul, sum_normSq_univ, hprob]
  field_simp

/-- Under the stated rotation-window and initial-mass hypotheses, `tightAASuccess δ k` bounds
the amplified target mass from below; this is the formal amplification estimate associated
with [Ambainis2012]. -/
theorem source_lemma1 {P : Matrix H H ℂ} (hP : IsOrthogonalProjector P)
    {ψ : QState H} (hψ : Normalized ψ) (δ : ℝ) (k : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hwin : ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt δ) ≤ Real.pi / 2)
    (hδ : projMass P ψ = δ) :
    tightAASuccess δ k ≤
      projMass P ((ReflectionAbout (outerProduct ψ) * sourceMark P)^k *ᵥ ψ) := by
  set θ := Real.arcsin (Real.sqrt δ) with hθe
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.2 hδ0)
  have hθ1 : θ < Real.pi / 2 := by
    rw [hθe]
    refine Real.arcsin_lt_pi_div_two.mpr ?_
    have h : Real.sqrt δ < Real.sqrt 1 := Real.sqrt_lt_sqrt hδ0.le hδ1
    rwa [Real.sqrt_one] at h
  have hsin : Real.sin θ = Real.sqrt δ := by
    rw [hθe]
    exact Real.sin_arcsin (by linarith [Real.sqrt_nonneg δ])
      (by have := Real.sqrt_le_sqrt hδ1.le; rwa [Real.sqrt_one] at this)
  have hprob : projMass P ψ = (Real.sin θ)^2 := by
    rw [hδ, hsin]
    exact (Real.sq_sqrt hδ0.le).symm
  have hmass := source_rotation_mass hP hψ θ k hθ0 hθ1 hprob
  have hcast : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by norm_cast
  have hwin' : ((2 * k + 1 : ℕ) : ℝ) * θ ≤ Real.pi / 2 := by
    rw [hcast]
    exact hwin
  have hle := clause88_tight_sin_sq (2 * k + 1) θ
    (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg δ)) (Real.arcsin_le_pi_div_two _) hwin'
  rw [hsin, Real.sq_sqrt hδ0.le, hcast] at hle
  have hts : tightAASuccess δ k
      = (1 - (2 * (k : ℝ) + 1) ^ 2 * δ / 3) * ((2 * (k : ℝ) + 1) ^ 2 * δ) := by
    simp only [tightAASuccess]
    ring
  rw [hts]
  rw [hmass]
  exact hle

/-- The ideal quadratic gain `(2 * k + 1)² * p`. -/
def sourceIdealGain (k : ℕ) (p : ℝ) : ℝ := ((2 * (k : ℝ) + 1) ^ 2) * p

/-- The condition that the ideal gain lies between `1 / (9 * m)` and `1 / m`. -/
def sourceAlg2Window (m : ℕ) (k : ℕ) (p : ℝ) : Prop :=
  1 / (9 * (m : ℝ)) ≤ sourceIdealGain k p ∧ sourceIdealGain k p ≤ 1 / (m : ℝ)

/-- Within `sourceAlg2Window`, an upper bound on `tightAASuccess p k` is at least `(1 - 1 / (3 *
m))` times the ideal gain, as used in [Ambainis2012]. -/
theorem source_lemma2_window {m : ℕ} (hm : 1 ≤ m) {k : ℕ} {p rs : ℝ}
    (hwin : sourceAlg2Window m k p) (hbound : tightAASuccess p k ≤ rs) :
    (1 - 1 / (3 * (m : ℝ))) * sourceIdealGain k p ≤ rs := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hts : tightAASuccess p k
      = (1 - (2 * (k : ℝ) + 1) ^ 2 * p / 3) * sourceIdealGain k p := by
    simp only [tightAASuccess, sourceIdealGain]
    ring
  have hsmall : sourceIdealGain k p ≤ 1 / (m : ℝ) := hwin.2
  have hnonneg : 0 ≤ sourceIdealGain k p := by
    have hfloor : 0 ≤ 1 / (9 * (m : ℝ)) := by positivity
    linarith [hwin.1]
  have hloss : 1 - (2 * (k : ℝ) + 1) ^ 2 * p / 3 ≥ 1 - 1 / (3 * (m : ℝ)) := by
    have h' : (2 * (k : ℝ) + 1) ^ 2 * p ≤ 1 / (m : ℝ) := hsmall
    have hdiv : 1 / (m : ℝ) / 3 = 1 / (3 * (m : ℝ)) := by
      field_simp
    have h'' : (2 * (k : ℝ) + 1) ^ 2 * p / 3 ≤ 1 / (m : ℝ) / 3 :=
      div_le_div_of_nonneg_right h' (by norm_num)
    rw [hdiv] at h''
    linarith
  rw [hts] at hbound
  have hmul : (1 - 1 / (3 * (m : ℝ))) * sourceIdealGain k p
      ≤ (1 - (2 * (k : ℝ) + 1) ^ 2 * p / 3) * sourceIdealGain k p :=
    mul_le_mul_of_nonneg_right hloss hnonneg
  linarith

/-- If the corrected ideal gain reaches `1 / (9 * m)` and `tightAASuccess p k ≤ rs`, then `rs`
also reaches that threshold. -/
theorem source_success_floor {m : ℕ} {k : ℕ} {p rs : ℝ}
    (hfloor : (1 - (2 * (k : ℝ) + 1) ^ 2 * p / 3) * sourceIdealGain k p
      ≥ 1 / (9 * (m : ℝ)))
    (hbound : tightAASuccess p k ≤ rs) :
    1 / (9 * (m : ℝ)) ≤ rs := by
  have hts : tightAASuccess p k
      = (1 - (2 * (k : ℝ) + 1) ^ 2 * p / 3) * sourceIdealGain k p := by
    simp only [tightAASuccess, sourceIdealGain]
    ring
  rw [hts] at hbound
  linarith

/-- A round-selection policy satisfying the ideal-gain window for positive probabilities at most
`1 / (9 * m)`. -/
structure SourceAlg2Policy (m : ℕ) where

  roundsAt : ℝ → ℕ

  roundsAt_window : ∀ p, 0 < p → p ≤ 1 / (9 * (m : ℝ)) →
    sourceAlg2Window m (roundsAt p) p

/-- On `[0, 1]`, the inverse sine is bounded above by `(π / 2) * x`. -/
theorem arcsin_le_half_pi_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.arcsin x ≤ (Real.pi / 2) * x := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hs : (Real.pi / 2) * x ≤ Real.pi / 2 := by
    have h1' : (Real.pi / 2) * x ≤ (Real.pi / 2) * 1 :=
      mul_le_mul_of_nonneg_left h1 hpi.le
    rwa [mul_one] at h1'
  have hsin : x ≤ Real.sin ((Real.pi / 2) * x) := by
    have h := Real.mul_le_sin (show 0 ≤ (Real.pi / 2) * x by positivity) hs
    have heq : (2 / Real.pi) * ((Real.pi / 2) * x) = x := by
      field_simp
    rwa [heq] at h
  have ha : Real.arcsin x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.arcsin_nonneg.mpr h0, Real.pi_pos], Real.arcsin_le_pi_div_two x⟩
  have hb : (Real.pi / 2) * x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [mul_nonneg hpi.le h0], hs⟩
  by_contra hcon
  have hlt : (Real.pi / 2) * x < Real.arcsin x := lt_of_not_ge hcon
  have hstrict := Real.strictMonoOn_sin hb ha hlt
  rw [Real.sin_arcsin (by linarith [h0]) h1] at hstrict
  linarith

/-- For `m ≥ 1` and positive `p`, an ideal gain at most `1 / m` keeps the amplified rotation
angle at most `π / 2`. -/
theorem source_rotation_window {m : ℕ} (hm : 1 ≤ m) {k : ℕ} {p : ℝ}
    (hp : 0 < p) (hsmall : sourceIdealGain k p ≤ 1 / (m : ℝ)) :
    ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt p) ≤ Real.pi / 2 := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hn0 : 0 < (2 * (k : ℝ) + 1 : ℝ) := by positivity
  have hsmall' : (2 * (k : ℝ) + 1 : ℝ) ^ 2 * p ≤ 1 / (m : ℝ) := by
    rw [sourceIdealGain] at hsmall
    exact hsmall
  have hnp : (2 * (k : ℝ) + 1 : ℝ) * Real.sqrt p ≤ 1 / Real.sqrt (m : ℝ) := by
    have h1 : Real.sqrt ((2 * (k : ℝ) + 1 : ℝ) ^ 2 * p) ≤ Real.sqrt (1 / (m : ℝ)) :=
      Real.sqrt_le_sqrt hsmall'
    have h2 : Real.sqrt ((2 * (k : ℝ) + 1 : ℝ) ^ 2 * p)
        = (2 * (k : ℝ) + 1 : ℝ) * Real.sqrt p := by
      rw [Real.sqrt_mul (by positivity) p, Real.sqrt_sq (by positivity)]
    have h3 : Real.sqrt (1 / (m : ℝ)) = 1 / Real.sqrt (m : ℝ) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (m : ℝ), Real.sqrt_one]
    rw [h2, h3] at h1
    exact h1
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp' : p ≤ 1 := by
    have h3 : (2 * (k : ℝ) + 1 : ℝ) ^ 2 * p ≤ 1 := by
      have : 1 / (m : ℝ) ≤ 1 := by
        rw [div_le_iff₀ hm0]
        linarith
      linarith
    have h2 : 1 ≤ (2 * (k : ℝ) + 1 : ℝ) ^ 2 := by nlinarith [hn0]
    have h4 : p ≤ (2 * (k : ℝ) + 1 : ℝ) ^ 2 * p := by
      calc p = p * 1 := by ring
        _ ≤ p * (2 * (k : ℝ) + 1 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hp)
        _ = (2 * (k : ℝ) + 1 : ℝ) ^ 2 * p := by ring
    linarith
  have hsqrt1 : Real.sqrt p ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using! hp'⟩
  have h1 : Real.arcsin (Real.sqrt p) ≤ (Real.pi / 2) * Real.sqrt p :=
    arcsin_le_half_pi_mul (Real.sqrt_nonneg _) hsqrt1
  calc ((2 * (k : ℝ) + 1)) * Real.arcsin (Real.sqrt p)
      ≤ ((2 * (k : ℝ) + 1)) * ((Real.pi / 2) * Real.sqrt p) := by
        gcongr
    _ = (Real.pi / 2) * ((2 * (k : ℝ) + 1) * Real.sqrt p) := by ring
    _ ≤ (Real.pi / 2) * (1 / Real.sqrt (m : ℝ)) := by
        have hpi : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        exact mul_le_mul_of_nonneg_left hnp hpi
    _ ≤ Real.pi / 2 := by
      have h2 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := by
        have hs : Real.sqrt 1 ≤ Real.sqrt (m : ℝ) :=
          (Real.sqrt_le_sqrt_iff hm0.le).2 hm1
        simpa using! hs
      have hpi : 0 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
      have hq : 1 / Real.sqrt (m : ℝ) ≤ 1 := by
        rw [div_le_iff₀ (Real.sqrt_pos.2 hm0)]
        simpa using! h2
      have hmul : (Real.pi / 2) * (1 / Real.sqrt (m : ℝ)) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left hq hpi
      simpa using! hmul

namespace CoherentVtFrame

/-- The state prepared by applying base stage `j` to the preceding coherent stage state. -/
def sourcePrepared (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : QState H :=
  ApplyGate (f.base j) (f.stageState ψ j.val (Nat.le_of_lt j.isLt))

/-- The target mass of the state prepared by base stage `j`. -/
def sourceBaseSuccess (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) : ℝ :=
  projMass f.target (f.sourcePrepared ψ j)

/-- The prepared state after `k` source reflection-marking iterates. -/
def sourceAmplified (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) (k : ℕ) : QState H :=
  (ReflectionAbout (outerProduct (f.sourcePrepared ψ j)) * sourceMark f.target)^k
    *ᵥ (f.sourcePrepared ψ j)

/-- The target mass after `k` source reflection-marking iterates at stage `j`. -/
def sourceAmpSuccess (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) (k : ℕ) : ℝ :=
  projMass f.target (f.sourceAmplified ψ j k)

end CoherentVtFrame

/-- Any valid consecutive sequence of coherent stages preserves normalization. -/
theorem normalized_stageStateFrom (f : CoherentVtFrame H m) {ψ : QState H} (hψ : Normalized ψ)
    (d n : ℕ) (h : d + n ≤ m) : Normalized (f.stageStateFrom ψ d n h) := by
  induction n with
  | zero => simpa [CoherentVtFrame.stageStateFrom] using! hψ
  | succ n ih =>
      rw [CoherentVtFrame.stageStateFrom]
      exact normalized_applyGate (f.stageOp_unitary _) (ih (by omega))

/-- A valid prefix of coherent stages preserves normalization. -/
theorem normalized_stageState (f : CoherentVtFrame H m) {ψ : QState H} (hψ : Normalized ψ)
    (n : ℕ) (hn : n ≤ m) : Normalized (f.stageState ψ n hn) :=
  normalized_stageStateFrom f hψ 0 n (by omega)

/-- Base-stage preparation from a normalized initial state produces a normalized state. -/
theorem normalized_sourcePrepared (f : CoherentVtFrame H m) {ψ : QState H} (hψ : Normalized ψ)
    (j : Fin m) : Normalized (f.sourcePrepared ψ j) :=
  normalized_applyGate (f.baseUnitary j)
    (normalized_stageState f hψ j.val (Nat.le_of_lt j.isLt))

/-- The target mass of a base-prepared state is nonnegative. -/
theorem sourceBaseSuccess_nonneg (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    0 ≤ f.sourceBaseSuccess ψ j := projMass_nonneg f.target (f.sourcePrepared ψ j)

/-- The target mass of a source-amplified state is nonnegative. -/
theorem sourceAmpSuccess_nonneg (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) (k : ℕ) :
    0 ≤ f.sourceAmpSuccess ψ j k := projMass_nonneg f.target (f.sourceAmplified ψ j k)

/-- The multiplier lower bound `1 / (3 * sqrt (m * p))` for the Algorithm 2 selection rule. -/
def sourceAlg2Lower (m : ℕ) (p : ℝ) : ℝ := 1 / (3 * Real.sqrt ((m : ℝ) * p))

/-- The positive odd multiplier obtained by rounding the Algorithm 2 lower bound upward through
`Nat.ceil`. -/
def alg2Multiplier (m : ℕ) (p : ℝ) : ℕ :=
  2 * Nat.ceil ((sourceAlg2Lower m p - 1) / 2) + 1

/-- The number of amplification rounds corresponding to `alg2Multiplier m p`. -/
def alg2Rounds (m : ℕ) (p : ℝ) : ℕ := (alg2Multiplier m p - 1) / 2

/-- The affine expression `2 * ((L - 1) / 2) + 1` simplifies to `L`. -/
private theorem lower_id (L : ℝ) : 2 * ((L - 1) / 2) + 1 = L := by
  field_simp
  ring

/-- Taking the natural ceiling of a natural number embedded in `ℝ` returns that number. -/
theorem natCeil_natCast (n : ℕ) : (Nat.ceil (n : ℝ) : ℕ) = n := by
  have h1 : (n : ℝ) ≤ (Nat.ceil (n : ℝ) : ℝ) := Nat.le_ceil (n : ℝ)
  have h2 : (Nat.ceil (n : ℝ) : ℕ) ≤ n := (Nat.ceil_le).mpr (by exact_mod_cast le_rfl)
  exact le_antisymm h2 (by exact_mod_cast h1)

/-- The selected Algorithm 2 multiplier is at least `sourceAlg2Lower m p`. -/
theorem alg2Multiplier_ge_lower (m : ℕ) (p : ℝ) :
    (alg2Multiplier m p : ℝ) ≥ sourceAlg2Lower m p := by
  have h := Nat.le_ceil ((sourceAlg2Lower m p - 1) / 2)
  have hid := lower_id (sourceAlg2Lower m p)
  unfold alg2Multiplier
  push_cast
  linarith

/-- When the lower bound is at least one, the selected odd multiplier is strictly less than that
bound plus two. -/
theorem alg2Multiplier_lt_lower_add_two (m : ℕ) (p : ℝ)
    (hL : 1 ≤ sourceAlg2Lower m p) :
    (alg2Multiplier m p : ℝ) < sourceAlg2Lower m p + 2 := by
  have h0 : 0 ≤ (sourceAlg2Lower m p - 1) / 2 := by linarith
  have h := Nat.ceil_lt_add_one h0
  unfold alg2Multiplier
  push_cast
  linarith

/-- The selected Algorithm 2 multiplier is positive and odd. -/
theorem alg2Multiplier_pos_odd (m : ℕ) (p : ℝ) :
    0 < alg2Multiplier m p ∧ alg2Multiplier m p % 2 = 1 := by
  unfold alg2Multiplier
  omega

/-- The round count `alg2Rounds m p` has odd multiplier exactly `alg2Multiplier m p`. -/
theorem alg2Rounds_eq (m : ℕ) (p : ℝ) :
    (2 * (alg2Rounds m p : ℝ) + 1) = (alg2Multiplier m p : ℝ) := by
  have hodd := alg2Multiplier_pos_odd m p
  have hdiv : alg2Multiplier m p - 1 = 2 * ((alg2Multiplier m p - 1) / 2) := by omega
  calc
    2 * (alg2Rounds m p : ℝ) + 1
        = 2 * (((alg2Multiplier m p - 1) / 2 : ℕ) : ℝ) + 1 := rfl
    _ = ((2 * ((alg2Multiplier m p - 1) / 2 : ℕ) : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_mul]; norm_num
    _ = ((alg2Multiplier m p - 1 : ℕ) : ℝ) + 1 := by
      congr 1
      exact_mod_cast hdiv.symm
    _ = (alg2Multiplier m p : ℝ) := by
      have h2 : (alg2Multiplier m p - 1 : ℕ) + 1 = alg2Multiplier m p := by omega
      have h3 : ((alg2Multiplier m p - 1 : ℕ) : ℝ) + 1
          = (((alg2Multiplier m p - 1 : ℕ) + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [h3, h2]

/-- For `m ≥ 1` and `0 < p ≤ 1 / (9 * m)`, the selected Algorithm 2 rounds satisfy the
ideal-gain window of [Ambainis2012]. -/
theorem alg2Rounds_window {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p)
    (hamp : p ≤ 1 / (9 * (m : ℝ))) :
    sourceAlg2Window m (alg2Rounds m p) p := by
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hMp : 0 < (m : ℝ) * p := mul_pos hM hp
  have hsqrt : 0 < Real.sqrt ((m : ℝ) * p) := Real.sqrt_pos.2 hMp
  have h3 : 0 < 3 * Real.sqrt ((m : ℝ) * p) := by positivity
  have hmp : (m : ℝ) * p ≤ 1 / 9 := by
    have h := mul_le_mul_of_nonneg_left hamp hM.le
    have heq : (m : ℝ) * (1 / (9 * (m : ℝ))) = 1 / 9 := by field_simp
    rw [heq] at h
    exact h
  have hsqrt1 : Real.sqrt ((m : ℝ) * p) ≤ 1 / 3 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    linarith [hmp]
  have hsqsqrt : (Real.sqrt ((m : ℝ) * p)) ^ 2 = (m : ℝ) * p := Real.sq_sqrt hMp.le
  have h3le : 3 * Real.sqrt ((m : ℝ) * p) ≤ 1 := by linarith
  have hL1 : 1 ≤ sourceAlg2Lower m p := by
    unfold sourceAlg2Lower
    rw [le_div_iff₀ h3]
    linarith
  have hnle := alg2Multiplier_ge_lower m p
  have hnlt := alg2Multiplier_lt_lower_add_two m p hL1
  have hL3 : sourceAlg2Lower m p + 2 ≤ 3 * sourceAlg2Lower m p := by linarith
  have hn3 : (alg2Multiplier m p : ℝ) < 3 * sourceAlg2Lower m p := by linarith
  have h3L : 3 * sourceAlg2Lower m p = 1 / Real.sqrt ((m : ℝ) * p) := by
    unfold sourceAlg2Lower
    field_simp
  constructor
  · rw [sourceIdealGain, alg2Rounds_eq]
    have hL2 : sourceAlg2Lower m p ^ 2 * p = 1 / (9 * (m : ℝ)) := by
      unfold sourceAlg2Lower
      field_simp
      nlinarith [hsqsqrt]
    have hL0 : 0 ≤ sourceAlg2Lower m p := by positivity
    have hn0 : 0 ≤ (alg2Multiplier m p : ℝ) := by positivity
    have hsq : (alg2Multiplier m p : ℝ) ^ 2 ≥ sourceAlg2Lower m p ^ 2 := by
      nlinarith [mul_le_mul hnle hnle hL0]
    have hmul : (alg2Multiplier m p : ℝ) ^ 2 * p ≥ sourceAlg2Lower m p ^ 2 * p := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (le_of_lt hp)]
    linarith [hmul, hL2]
  · rw [sourceIdealGain, alg2Rounds_eq]
    have hn3' : (alg2Multiplier m p : ℝ) < 1 / Real.sqrt ((m : ℝ) * p) := by linarith [h3L]
    have hpos : 0 < 1 / Real.sqrt ((m : ℝ) * p) := by positivity
    have hsq : (alg2Multiplier m p : ℝ) ^ 2 < (1 / Real.sqrt ((m : ℝ) * p)) ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_right hn3' hpos]
    have hsq2 : (1 / Real.sqrt ((m : ℝ) * p)) ^ 2 * p = 1 / (m : ℝ) := by
      field_simp
      nlinarith [hsqsqrt]
    have hmul : (alg2Multiplier m p : ℝ) ^ 2 * p < (1 / Real.sqrt ((m : ℝ) * p)) ^ 2 * p := by
      nlinarith [mul_lt_mul_of_pos_right hsq hp]
    linarith [hmul, hsq2]

/-- The selected Algorithm 2 round count is minimal among counts whose ideal gain reaches `1 /
(9 * m)`. -/
theorem alg2Rounds_minimal {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) {k : ℕ}
    (hk : 1 / (9 * (m : ℝ)) ≤ sourceIdealGain k p) :
    alg2Rounds m p ≤ k := by
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hMp : 0 < (m : ℝ) * p := mul_pos hM hp
  have h3 : 0 < 3 * Real.sqrt ((m : ℝ) * p) := by positivity
  have h3sq : (3 * Real.sqrt ((m : ℝ) * p)) ^ 2 = 9 * ((m : ℝ) * p) := by
    calc
      (3 * Real.sqrt ((m : ℝ) * p)) ^ 2 = 9 * (Real.sqrt ((m : ℝ) * p)) ^ 2 := by ring
      _ = 9 * ((m : ℝ) * p) := by rw [Real.sq_sqrt hMp.le]
  have hA : (2 * (k : ℝ) + 1) ^ 2 * p ≥ 1 / (9 * (m : ℝ)) := by
    rw [sourceIdealGain] at hk
    linarith
  have hA2 : 1 / (9 * ((m : ℝ) * p)) ≤ (2 * (k : ℝ) + 1) ^ 2 := by
    have h := (div_le_iff₀ hp).2 hA
    rw [div_div] at h
    convert! h using 1
    ring_nf
  have hsqA : (2 * (k : ℝ) + 1) ^ 2 ≥ (1 / (3 * Real.sqrt ((m : ℝ) * p))) ^ 2 := by
    have hsqsqrt : (Real.sqrt ((m : ℝ) * p)) ^ 2 = (m : ℝ) * p := Real.sq_sqrt hMp.le
    have hsqB : (1 / (3 * Real.sqrt ((m : ℝ) * p))) ^ 2 = 1 / (9 * ((m : ℝ) * p)) := by
      field_simp
      nlinarith [hsqsqrt]
    rw [hsqB]
    exact hA2
  have hA0 : 0 ≤ (2 * (k : ℝ) + 1) := by positivity
  have hB0 : 0 ≤ 1 / (3 * Real.sqrt ((m : ℝ) * p)) := by positivity
  have hfinal : 2 * (k : ℝ) + 1 ≥ 1 / (3 * Real.sqrt ((m : ℝ) * p)) := by
    nlinarith [hsqA]
  have hk' : (2 * (k : ℝ) + 1) ≥ sourceAlg2Lower m p := by
    rw [sourceAlg2Lower]
    have hX : 1 ≤ (2 * (k : ℝ) + 1) * (3 * Real.sqrt ((m : ℝ) * p)) :=
      (div_le_iff₀ h3).1 hfinal
    exact (div_le_iff₀ h3).2 hX
  have hceil : Nat.ceil ((sourceAlg2Lower m p - 1) / 2) ≤ k := by
    apply (Nat.ceil_le).mpr
    have hkR : (2 * (k : ℝ) + 1) ≥ sourceAlg2Lower m p := hk'
    linarith
  have hdiv : alg2Multiplier m p - 1 = 2 * ((alg2Multiplier m p - 1) / 2) := by
    have hodd := alg2Multiplier_pos_odd m p
    omega
  unfold alg2Rounds
  have hmul : alg2Multiplier m p = 2 * Nat.ceil ((sourceAlg2Lower m p - 1) / 2) + 1 := rfl
  omega

/-- For `m ≥ 1` and `0 < p ≤ 1 / (9 * m)`, the selected rounds keep the amplified angle at most
`π / 2`. -/
theorem alg2Rounds_lemma1_window {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p)
    (hamp : p ≤ 1 / (9 * (m : ℝ))) :
    ((2 * (alg2Rounds m p : ℝ) + 1)) * Real.arcsin (Real.sqrt p) ≤ Real.pi / 2 := by
  have hwin := alg2Rounds_window hm hp hamp
  exact source_rotation_window hm hp hwin.2

/-- The smaller quadratic root governing the corrected ideal-gain success threshold. -/
def sourceFloorThreshold (m : ℕ) : ℝ :=
  (3 - Real.sqrt (9 - 4 / (3 * (m : ℝ)))) / 2

/-- The larger quadratic root governing the corrected ideal-gain success threshold. -/
def sourceFloorThreshold' (m : ℕ) : ℝ :=
  (3 + Real.sqrt (9 - 4 / (3 * (m : ℝ)))) / 2

/-- The discriminant `9 - 4 / (3 * m)` is nonnegative for `m ≥ 1`. -/
private theorem floorDisc_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ 9 - 4 / (3 * (m : ℝ)) := by
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h3M : 0 < 3 * (m : ℝ) := by positivity
  have h1 : 4 / (3 * (m : ℝ)) ≤ 9 := by
    rw [div_le_iff₀ h3M]
    nlinarith
  linarith

/-- The two corrected-gain threshold roots sum to three. -/
private theorem floorSum {m : ℕ} (hm : 1 ≤ m) :
    sourceFloorThreshold m + sourceFloorThreshold' m = 3 := by
  unfold sourceFloorThreshold sourceFloorThreshold'
  ring

/-- The two corrected-gain threshold roots have product `1 / (3 * m)`. -/
private theorem floorProd {m : ℕ} (hm : 1 ≤ m) :
    sourceFloorThreshold m * sourceFloorThreshold' m = 1 / (3 * (m : ℝ)) := by
  have hD := floorDisc_nonneg hm
  have h3M : 0 < 3 * (m : ℝ) := by
    have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
    positivity
  unfold sourceFloorThreshold sourceFloorThreshold'
  calc
    ((3 - Real.sqrt (9 - 4 / (3 * (m : ℝ)))) / 2)
        * ((3 + Real.sqrt (9 - 4 / (3 * (m : ℝ)))) / 2)
        = ((3 - Real.sqrt (9 - 4 / (3 * (m : ℝ))))
          * (3 + Real.sqrt (9 - 4 / (3 * (m : ℝ))))) / 4 := by ring
    _ = (9 - (Real.sqrt (9 - 4 / (3 * (m : ℝ)))) ^ 2) / 4 := by ring
    _ = (9 - (9 - 4 / (3 * (m : ℝ)))) / 4 := by rw [Real.sq_sqrt hD]
    _ = 1 / (3 * (m : ℝ)) := by field_simp; ring

/-- For `m ≥ 1`, the smaller root lies strictly between `1 / (9 * m)` and `1 / (3 * m)`, and the
larger root exceeds one. -/
theorem sourceFloorThreshold_bounds {m : ℕ} (hm : 1 ≤ m) :
    1 / (9 * (m : ℝ)) < sourceFloorThreshold m ∧
      sourceFloorThreshold m < 1 / (3 * (m : ℝ)) ∧
      1 < sourceFloorThreshold' m := by
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h3M : 0 < 3 * (m : ℝ) := by positivity
  have hD := floorDisc_nonneg hm
  have hsqrt0 : 0 ≤ Real.sqrt (9 - 4 / (3 * (m : ℝ))) := Real.sqrt_nonneg _
  have hprod := floorProd hm
  have hr2lt : sourceFloorThreshold' m < 3 := by
    unfold sourceFloorThreshold'
    have hDlt : 9 - 4 / (3 * (m : ℝ)) < 9 := by
      have h1 : 0 < 4 / (3 * (m : ℝ)) := by positivity
      linarith
    have hsqrtlt : Real.sqrt (9 - 4 / (3 * (m : ℝ))) < 3 := by
      rw [Real.sqrt_lt' (by norm_num)]
      linarith
    linarith
  have hr2gt1 : 1 < sourceFloorThreshold' m := by
    unfold sourceFloorThreshold'
    linarith
  have hr1pos : 0 < sourceFloorThreshold m := by
    have h1 : 0 < sourceFloorThreshold m * sourceFloorThreshold' m := by
      rw [hprod]
      positivity
    nlinarith
  constructor
  · have hlt : sourceFloorThreshold m * sourceFloorThreshold' m < 3 * sourceFloorThreshold m := by
      have h := mul_lt_mul_of_pos_right hr2lt hr1pos
      nlinarith [h]
    rw [hprod] at hlt
    have h2 := mul_lt_mul_of_pos_right hlt (by positivity : (0 : ℝ) < 3 * (m : ℝ))
    have h3 : (1 / (3 * (m : ℝ))) * (3 * (m : ℝ)) = 1 := by field_simp
    rw [h3] at h2
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 9 * (m : ℝ))]
    nlinarith
  · constructor
    · have hgt : sourceFloorThreshold m * sourceFloorThreshold' m > sourceFloorThreshold m := by
        have h := mul_lt_mul_of_pos_right hr2gt1 hr1pos
        nlinarith [h]
      rw [hprod] at hgt
      linarith
    · exact hr2gt1

/-- The corrected-gain expression equals `1 / (9 * m)` exactly at the two threshold roots. -/
theorem source_floor_roots {m : ℕ} (hm : 1 ≤ m) {g : ℝ} :
    g * (1 - g / 3) = 1 / (9 * (m : ℝ)) ↔
      (g = sourceFloorThreshold m ∨ g = sourceFloorThreshold' m) := by
  have hsum := floorSum hm
  have hprod := floorProd hm
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have h3M : 0 < 3 * (m : ℝ) := by positivity
  have hid : g * (1 - g / 3) - 1 / (9 * (m : ℝ))
      = -(1 / 3) * (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) := by
    calc
      g * (1 - g / 3) - 1 / (9 * (m : ℝ))
          = g - g ^ 2 / 3 - 1 / (9 * (m : ℝ)) := by ring
      _ = -(1 / 3) * (g ^ 2 - 3 * g + 1 / (3 * (m : ℝ))) := by ring
      _ = -(1 / 3) * (g ^ 2 - (sourceFloorThreshold m + sourceFloorThreshold' m) * g
            + sourceFloorThreshold m * sourceFloorThreshold' m) := by
        congr 1
        rw [hsum, hprod]
      _ = -(1 / 3) * ((g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m)) := by ring
      _ = -(1 / 3) * (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) := by ring
  constructor
  · intro h
    have hz : (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) = 0 := by
      have hh := hid
      linarith
    rcases mul_eq_zero.mp hz with hz1 | hz2
    · exact Or.inl (sub_eq_zero.mp hz1)
    · exact Or.inr (sub_eq_zero.mp hz2)
  · rintro (rfl | rfl)
    · have hh := hid
      linarith
    · have hh := hid
      linarith

/-- For `m ≥ 1` and `g ≤ 1 / m`, the corrected-gain lower bound holds exactly when `g` is at
least the smaller threshold root. -/
theorem source_floor_iff {m : ℕ} (hm : 1 ≤ m) {g : ℝ} (hg1 : g ≤ 1 / (m : ℝ)) :
    g * (1 - g / 3) ≥ 1 / (9 * (m : ℝ)) ↔ g ≥ sourceFloorThreshold m := by
  have hsum := floorSum hm
  have hprod := floorProd hm
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have hb := sourceFloorThreshold_bounds hm
  have hid : g * (1 - g / 3) - 1 / (9 * (m : ℝ))
      = -(1 / 3) * (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) := by
    calc
      g * (1 - g / 3) - 1 / (9 * (m : ℝ))
          = g - g ^ 2 / 3 - 1 / (9 * (m : ℝ)) := by ring
      _ = -(1 / 3) * (g ^ 2 - 3 * g + 1 / (3 * (m : ℝ))) := by ring
      _ = -(1 / 3) * (g ^ 2 - (sourceFloorThreshold m + sourceFloorThreshold' m) * g
            + sourceFloorThreshold m * sourceFloorThreshold' m) := by
        congr 1
        rw [hsum, hprod]
      _ = -(1 / 3) * ((g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m)) := by ring
      _ = -(1 / 3) * (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) := by ring
  have hgr2 : g < sourceFloorThreshold' m := by
    have h1 : 1 / (m : ℝ) ≤ 1 := by
      exact (div_le_one (by positivity : (0 : ℝ) < (m : ℝ))).2
        (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ))
    linarith
  constructor
  · intro h
    have hmul : (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) ≤ 0 := by
      have hh := hid
      linarith
    have hneg : g - sourceFloorThreshold' m < 0 := by linarith
    have hpos : 0 ≤ g - sourceFloorThreshold m := by
      by_contra hc
      have hc' : g - sourceFloorThreshold m < 0 := by linarith
      have hpr : 0 < (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) :=
        mul_pos_of_neg_of_neg hc' hneg
      linarith
    linarith
  · intro h
    have hpos : 0 ≤ g - sourceFloorThreshold m := by linarith
    have hneg : g - sourceFloorThreshold' m < 0 := by linarith
    have hmul : (g - sourceFloorThreshold m) * (g - sourceFloorThreshold' m) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpos hneg.le
    have hh := hid
    linarith

/-- At input probability `1 / (9 * m)` with `m ≥ 1`, the Algorithm 2 selection rule chooses zero
rounds. -/
theorem alg2Rounds_at_edge {m : ℕ} (hm : 1 ≤ m) :
    alg2Rounds m (1 / (9 * (m : ℝ))) = 0 := by
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  have h3M : 0 < 3 * (m : ℝ) := by positivity
  have hsq : Real.sqrt ((m : ℝ) * (1 / (9 * (m : ℝ)))) = 1 / 3 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by norm_num)]
    field_simp
    ring
  have hL : sourceAlg2Lower m (1 / (9 * (m : ℝ))) = 1 := by
    unfold sourceAlg2Lower
    rw [hsq]
    field_simp
  have hceil : Nat.ceil ((sourceAlg2Lower m (1 / (9 * (m : ℝ))) - 1) / 2) = 0 := by
    rw [hL]
    norm_num
  have hmul : alg2Multiplier m (1 / (9 * (m : ℝ))) = 1 := by
    unfold alg2Multiplier
    rw [hceil]
  unfold alg2Rounds
  rw [hmul]

/-- At the endpoint input probability `1 / (9 * m)`, the corrected ideal-gain expression for the
selected rounds is strictly below `1 / (9 * m)`. -/
theorem source_floor_gap_at_edge {m : ℕ} (hm : 1 ≤ m) :
    (1 - (2 * (alg2Rounds m (1 / (9 * (m : ℝ))) : ℝ) + 1) ^ 2 * (1 / (9 * (m : ℝ))) / 3)
        * sourceIdealGain (alg2Rounds m (1 / (9 * (m : ℝ)))) (1 / (9 * (m : ℝ)))
      < 1 / (9 * (m : ℝ)) := by
  have hk := alg2Rounds_at_edge hm
  have hM : 0 < (m : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hm
  rw [hk]
  rw [sourceIdealGain]
  have h3M : 0 < 3 * (m : ℝ) := by positivity
  have hpos : 0 < 1 / (9 * (m : ℝ)) := by positivity
  have hone : 1 / (9 * (m : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity : (0 : ℝ) < 9 * (m : ℝ))).2
      (by exact_mod_cast (show (1 : ℕ) ≤ 9 * m by omega) : (1 : ℝ) ≤ 9 * (m : ℝ))
  have hlt : 1 / (9 * (m : ℝ)) / 3 < 1 := by
    have h2 : 1 / (9 * (m : ℝ)) / 3 ≤ 1 / 3 := by gcongr
    linarith
  have hsq : 0 < (1 / (9 * (m : ℝ))) ^ 2 := sq_pos_of_pos hpos
  nlinarith

/-- For `m = 1` and `p = 113 / 1000`, no round count simultaneously satisfies the ideal-gain
window and the stated corrected-gain floor. -/
theorem sourceAlg2_window_floor_incompatible :
    ∀ k : ℕ, ¬ (sourceAlg2Window 1 k (113 / 1000) ∧
      (1 - (2 * (k : ℝ) + 1) ^ 2 * (113 / 1000) / 3) * sourceIdealGain k (113 / 1000)
        ≥ 1 / 9) := by
  intro k
  by_cases hk0 : k = 0
  · intro hcon
    have hfloor := hcon.2
    rw [sourceIdealGain] at hfloor
    simp [hk0] at hfloor
    norm_num at hfloor
  · intro hcon
    have hwin := hcon.1
    have hgain : (2 * (k : ℝ) + 1) ^ 2 * (113 / 1000) > 1 := by
      have hk1n : (1 : ℕ) ≤ k := by omega
      have hk1 : 3 ≤ 2 * (k : ℝ) + 1 := by
        have h3n : (3 : ℕ) ≤ 2 * k + 1 := by omega
        exact_mod_cast h3n
      have hnonneg : 0 ≤ (113 / 1000 : ℝ) := by norm_num
      have hsq : 9 ≤ (2 * (k : ℝ) + 1) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right hsq hnonneg
      linarith
    have hupp := hwin.2
    rw [sourceIdealGain] at hupp
    linarith

/-- The Algorithm 2 policy using `alg2Rounds m`, with its ideal-gain window guarantee for `m ≥
1`. -/
def alg2Policy (m : ℕ) (hm : 1 ≤ m) : SourceAlg2Policy m where
  roundsAt := alg2Rounds m
  roundsAt_window := fun p hp hamp => alg2Rounds_window hm hp hamp

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
