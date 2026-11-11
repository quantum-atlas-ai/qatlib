/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalWordConstruction

/-!
# Access words and lifted fixed-point consumers

This module defines an explicit access alphabet and its matrix interpretation for the
fixed-point search word of [YoderLowChuang2014]. `fixedPointAccessWord` concatenates the access
lists for individual iterates, and separate counting functions record preparation, query, phase,
and phase-bit resources.

The module also supplies the length-three failure factors, dyadic angle rounding, and an LCU
consumer obtained by lifting the public word to a selected register fiber. Success and
conditional output are defined through overlap with the fiber target.

## Main definitions

* `FixedPointAccess`: the access alphabet with phase parameters.
* `fixedPointAccessWord`: the concatenated iterate access list.
* `accessWordMatrix`: the ordered matrix interpretation.
* `dyadicAngle`: rounding to a dyadic angular grid.
* `lcuSuccessProb` and `lcuConditionalOutput`: lifted consumer outputs.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix

/-- The complex phase factor `l3PhaseUnit delta` for the length-three word. -/
noncomputable def l3Unit (delta : ℝ) : ℂ := l3PhaseUnit delta

/-- The phase factor `l3Unit delta` equals `l3PhaseUnit delta`. -/
theorem l3Unit_eq (delta : ℝ) : l3Unit delta = l3PhaseUnit delta := rfl

/-- The real factor `1 - 2 * lam + 2 * lam * cos (l3Phase delta)` in the length-three failure
amplitude. -/
noncomputable def l3FailureFactor (delta lam : ℝ) : ℝ :=
  1 - 2 * lam + 2 * lam * Real.cos (l3Phase delta)

/-- The cube of the length-three width parameter `ylcGamma 3 delta`. -/
noncomputable def l3WidthValue (delta : ℝ) : ℝ := (ylcGamma 3 delta) ^ 3

/-- The access symbols for preparation, inverse preparation, marking, controlled queries, and
good-phase updates, with phase angles and bit counts where applicable. -/
inductive FixedPointAccess where

  | prepA

  | prepAdag

  | markQuery

  | controlQuery (bits : ℕ) (angle : ℝ)

  | goodPhase (bits : ℕ) (angle : ℝ)

/-- Counts preparation and inverse-preparation symbols in an access list. -/
def prepAccessCount : List FixedPointAccess → ℕ
  | [] => 0
  | .prepA :: t => prepAccessCount t + 1
  | .prepAdag :: t => prepAccessCount t + 1
  | _ :: t => prepAccessCount t

/-- Counts marking and controlled-query symbols in an access list. -/
def queryAccessCount : List FixedPointAccess → ℕ
  | [] => 0
  | .markQuery :: t => queryAccessCount t + 1
  | .controlQuery _ _ :: t => queryAccessCount t + 1
  | _ :: t => queryAccessCount t

/-- Counts controlled-query and good-phase symbols in an access list. -/
def phaseAccessCount : List FixedPointAccess → ℕ
  | [] => 0
  | .controlQuery _ _ :: t => phaseAccessCount t + 1
  | .goodPhase _ _ :: t => phaseAccessCount t + 1
  | _ :: t => phaseAccessCount t

/-- Sums the bit-count parameters of the controlled-query and good-phase symbols in an access
list. -/
def phaseBitCount : List FixedPointAccess → ℕ
  | [] => 0
  | .controlQuery b _ :: t => phaseBitCount t + b
  | .goodPhase b _ :: t => phaseBitCount t + b
  | _ :: t => phaseBitCount t

/-- The five-symbol access list for one public iterate, using its scheduled target and source
phases. -/
noncomputable def iterateAccesses (l : ℕ) (delta : ℝ) (bits : ℕ) (i : ℕ) :
    List FixedPointAccess :=
  [ .markQuery,
    .controlQuery bits (-(wordPhase (2 * l + 1) (l - i) (ylcGamma (2 * l + 1) delta))),
    .prepA,
    .goodPhase bits (wordPhase (2 * l + 1) (i + 1) (ylcGamma (2 * l + 1) delta)),
    .prepAdag ]

/-- The concatenation of the access lists for the first `l` public iterates. -/
noncomputable def fixedPointAccessWord (l : ℕ) (delta : ℝ) (bits : ℕ) :
    List FixedPointAccess :=
  (List.range l).flatMap fun i => iterateAccesses l delta bits i

/-- The two-level matrix interpretation of an access symbol, using target reflections for
controlled queries and negative source reflections for good-phase updates. -/
noncomputable def FixedPointAccess.matrix (lam : ℝ) : FixedPointAccess →
    Matrix (Fin 2) (Fin 2) ℂ
  | .prepA => 1
  | .prepAdag => 1
  | .markQuery => 1
  | .controlQuery _ angle => targetReflection angle
  | .goodPhase _ angle => -(stateReflection lam angle)

/-- The matrix interpretation of an access list, multiplying each subsequent operation on the
left. -/
noncomputable def accessWordMatrix (lam : ℝ) : List FixedPointAccess →
    Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | a :: t => accessWordMatrix lam t * a.matrix lam

/-- The nearest-grid angle obtained by rounding to an integer multiple of `2 * π / 2 ^ bits`
using the displayed floor formula. -/
noncomputable def dyadicAngle (bits : ℕ) (angle : ℝ) : ℝ :=
  (2 * Real.pi * ((Int.floor (angle * (2:ℝ) ^ bits / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ)) /
    (2:ℝ) ^ bits

/-- The tensor product of the register basis state at `j₀` and the two-level amplitude state. -/
noncomputable def lcuPrepareState {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (lam : ℝ) : QState (J × Fin 2) :=
  TensorState (Ket j₀) (ampState lam)

/-- The public fixed-point word lifted to the selected register fiber at `j₀`. -/
noncomputable def lcuSelectOperator {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : Matrix (J × Fin 2) (J × Fin 2) ℂ :=
  publicWordFiber j₀ l delta lam

/-- The squared overlap of the LCU output with the fiber target. -/
noncomputable def lcuSuccessProb {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : ℝ :=
  ‖Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
      (lcuSelectOperator j₀ l delta lam *ᵥ lcuPrepareState j₀ lam)‖ ^ 2

/-- The conditional target-direction vector obtained from the LCU preparation and selection
operator. -/
noncomputable def lcuConditionalOutput {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) : QState (J × Fin 2) :=
  conditionalOutput (fiberTarget j₀)
    (lcuSelectOperator j₀ l delta lam *ᵥ lcuPrepareState j₀ lam)

end Qatlib.Papers.FixedPtSearch14.FixedPoint
