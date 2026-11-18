/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.CssBridge
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# A CSS code consumes signed-stabilizer recovery

A one-qubit CSS code with a positive Z check is transported into the actual
signed-tableau model. Its nonzero X error is corrected by the syndrome decoder
through `Qatlib.Concepts.ErrorCorrection.Recovery.css_stab_recovers`.
The overlapping X/Z error also tests the phase-sensitive operator bridge.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.CssSignedRecoveryRegression

open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open scoped Matrix

/-- The one-qubit CSS code with no X checks and one positive Z check. -/
def fixedZeroCss : CssData (Fin 1) (Fin 0) (Fin 1) where
  hX := 0
  hZ := fun _ _ => 1
  hcompat := by ext i; exact Fin.elim0 i

/-- The same positive Z check as a genuine signed tableau. -/
def fixedZeroTab : Tableau 1 1 :=
  fun _ => ⟨fun _ => false, fun _ => true, 0⟩

/-- The pure Z tableau is Hermitian and self-commuting. -/
theorem fixed_zero_consistent : ConsistentTableau fixedZeroTab := by
  constructor
  · intro a
    left
    rfl
  · intro a b
    have hab : a = b := Subsingleton.elim _ _
    subst b
    rfl

/-- The nonzero Z generator is independent. -/
theorem fixed_zero_independent : IndependentGenerators (tableauGenerators fixedZeroTab) := by
  apply independent_of_row_linearIndependent
  rw [linearIndependent_unique_iff]
  decide

/-- A syndrome bit selects the actual X correction. -/
def fixedZeroProg : StabProg fixedZeroTab where
  corr η := (fun _ => η 0, 0)

/-- CSS fixed-check states transport into the matching signed tableau codespace. -/
theorem fixed_zero_state (f : BooleanVec 1 → ℂ) (hf : f ∈ cssCodespace fixedZeroCss) :
    stateOfFn f ∈ codeSpace fixedZeroTab := by
  apply (mem_codeSpace_iff fixedZeroTab (stateOfFn f)).mpr
  intro a
  have hz := ((mem_cssCodespace_iff' fixedZeroCss f).mp hf).2 0
  have he : (fixedZeroTab a).decode = (rawDiagonalRow (fun _ : Fin 1 => 1) 0).decode := by
    rfl
  rw [he, ← css_z_reindex, css_state_transport]
  exact congrArg stateOfFn hz

/-- The actual X error leaves zero residual after the syndrome-selected X
correction. -/
theorem fixed_zero_residual : stabRes fixedZeroProg ((fun _ => 1), 0) = 0 := by
  decide

/-- A concrete computational basis state in vector coordinates. -/
def basisZero (v : BooleanVec 1) : ℂ := if v = 0 then 1 else 0

/-- The CSS consumer has a concrete nonzero state, so its recovery premise is
satisfiable. -/
theorem basis_zero_mem : basisZero ∈ cssCodespace fixedZeroCss := by
  apply (mem_cssCodespace_iff' fixedZeroCss basisZero).mpr
  constructor
  · intro a
    exact Fin.elim0 a
  · intro j
    ext v
    by_cases hv : v = 0
    · subst v
      simp [fixedZeroCss, cssPauliZ, Matrix.mulVec_diagonal, basisZero, bitDot]
    · simp [fixedZeroCss, cssPauliZ, Matrix.mulVec_diagonal, basisZero, hv]

/-- The concrete zero-basis code vector is nonzero. -/
theorem basis_zero_ne : basisZero ≠ 0 := by
  intro h
  have hzero := congrFun h 0
  simp [basisZero] at hzero

/-- Every state of this CSS code recovers its nonzero X error through the
general signed-stabilizer recovery channel. -/
example (f : BooleanVec 1 → ℂ) (hf : f ∈ cssCodespace fixedZeroCss) :
    stabRecCh fixedZeroTab fixedZeroProg
      (outerProduct ((cssPauliX (fun _ : Fin 1 => 1) * cssPauliZ 0).submatrix
        regToVec regToVec *ᵥ stateOfFn f)) = outerProduct (stateOfFn f) := by
  apply css_stab_recovers fixedZeroTab fixed_zero_consistent fixed_zero_independent
    fixedZeroProg (fun _ => 1) 0
  · rw [fixed_zero_residual]
    exact Submodule.zero_mem _
  · exact fixed_zero_state f hf

/-- An overlapping X/Z support has weight one and retains a nonzero signed
phase, so dropping the phase would change the operator. -/
example : pauliWt (cssSigned (fun _ : Fin 1 => 1) (fun _ => 1)) = 1 ∧
    (cssSigned (fun _ : Fin 1 => 1) (fun _ => 1)).phase ≠ 0 := by
  constructor <;> decide

end QatlibTests.CssSignedRecoveryRegression
