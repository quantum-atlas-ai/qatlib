/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionCoefficientData
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionSourceTables

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Actual thermal source tables on the order012 high-cluster collision face

The merged clusters are P0 and P1+P2. All 96 rows and all 15 complex
coordinates are checked against the original six Pauli sources. The
population edge belongs to the second column of the up stack. The full
nonorthonormal fast chart is transported by the existing masked-input bridge.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionSourceTables
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelWordDual
open ThreeLevelGramCertificateCorner ThreeLevelCornerFastChart ThreeLevelCoordinateMetric
open ThreeLevelGramCertificate ThreeLevelCollisionSourceTables

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

def lowReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 8/9, (-2/9), 0;
    0, (-2/9), 5/9, 0;
    0, 0, 0, 5/9]

def lowImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 4/9;
    0, (-2/9), (-4/9), 0]

def highReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    0, 1/9, 2/9, 0;
    0, 2/9, 4/9, 0;
    0, 0, 0, 4/9]

def highImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, (-2/9);
    0, 0, 0, (-4/9);
    0, 2/9, 4/9, 0]

def upLeftReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    (-2/9), 0, 0, 4/9;
    5/9, 0, 0, 0;
    0, 1/9, 2/9, 0],
    !![0, 0, 0, 0;
    0, 14/81, 28/81, 0;
    0, (-8/81), (-16/81), 0;
    4/9, 0, 0, 2/81],
    !![0, 0, 0, 0;
    0, 16/81, 32/81, 0;
    0, (-4/81), (-8/81), 0;
    0, 0, 0, (-8/81)],
    !![0, 0, 0, 0;
    8/9, 0, 0, 0;
    (-2/9), 0, 0, 4/9;
    0, 2/9, 4/9, 0],
    !![0, 0, 0, 0;
    0, (-8/81), (-16/81), 0;
    0, 2/81, 4/81, 0;
    2/9, 0, 0, 4/81],
    !![0, 0, 0, 0;
    0, (-8/81), (-16/81), 0;
    0, 20/81, 40/81, 0;
    0, 0, 0, (-32/81)]]

def upLeftImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, 2/9, 4/9, 0;
    0, 0, 0, 0;
    (-4/9), 0, 0, (-2/9)],
    !![0, 0, 0, 0;
    (-2/9), 0, 0, (-28/81);
    5/9, 0, 0, 16/81;
    0, 1/81, 2/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, (-32/81);
    0, 0, 0, 8/81;
    0, (-4/81), (-8/81), 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 2/9, 4/9, 0;
    (-2/9), 0, 0, (-4/9)],
    !![0, 0, 0, 0;
    8/9, 0, 0, 16/81;
    (-2/9), 0, 0, (-4/81);
    0, 2/81, 4/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 16/81;
    0, 0, 0, (-40/81);
    0, (-16/81), (-32/81), 0]]

def upRightReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, (-2/9), 5/9, 0;
    0, 0, 0, 1/9;
    0, 0, 0, 2/9;
    0, 4/9, 0, 0],
    !![0, 0, 0, 4/9;
    0, 14/81, (-8/81), 0;
    0, 28/81, (-16/81), 0;
    0, 0, 0, 2/81],
    !![0, 0, 0, 0;
    0, 16/81, (-4/81), 0;
    0, 32/81, (-8/81), 0;
    0, 0, 0, (-8/81)],
    !![0, 8/9, (-2/9), 0;
    0, 0, 0, 2/9;
    0, 0, 0, 4/9;
    0, 0, 4/9, 0],
    !![0, 0, 0, 2/9;
    0, (-8/81), 2/81, 0;
    0, (-16/81), 4/81, 0;
    0, 0, 0, 4/81],
    !![0, 0, 0, 0;
    0, (-8/81), 20/81, 0;
    0, (-16/81), 40/81, 0;
    0, 0, 0, (-32/81)]]

def upRightImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 4/9;
    0, (-2/9), 0, 0;
    0, (-4/9), 0, 0;
    0, 0, 0, 2/9],
    !![0, 2/9, (-5/9), 0;
    0, 0, 0, (-1/81);
    0, 0, 0, (-2/81);
    0, 28/81, (-16/81), 0],
    !![0, 0, 0, 0;
    0, 0, 0, 4/81;
    0, 0, 0, 8/81;
    0, 32/81, (-8/81), 0],
    !![0, 0, 0, 2/9;
    0, 0, (-2/9), 0;
    0, 0, (-4/9), 0;
    0, 0, 0, 4/9],
    !![0, (-8/9), 2/9, 0;
    0, 0, 0, (-2/81);
    0, 0, 0, (-4/81);
    0, (-16/81), 4/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 16/81;
    0, 0, 0, 32/81;
    0, (-16/81), 40/81, 0]]

/-- Low parts for the stated finite source data. -/
theorem low_parts : fromParts lowReal lowImag = pZero := by
  rw [pZero, pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, lowReal, lowImag, pOne, Matrix.one_apply] <;> ring

/-- High parts for the stated finite source data. -/
theorem high_parts : fromParts highReal highImag = pOne+pTwo := by
  rw [pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, highReal, highImag, pOne, Matrix.one_apply] <;> ring

/-- Up blocks match for the stated finite source data. -/
theorem up_blocks_match :
    (∀ k, upLeftReal k = blockReal lowReal lowImag highReal highImag k) ∧
    (∀ k, upLeftImag k = blockImag lowReal lowImag highReal highImag k) ∧
    (∀ k, upRightReal k = blockReal highReal highImag lowReal lowImag k) ∧
    (∀ k, upRightImag k = blockImag highReal highImag lowReal lowImag k) := by
  decide +kernel

/-- Up Left parts for the stated finite source data. -/
theorem upLeft_parts (k : Fin 6) :
    fromParts (upLeftReal k) (upLeftImag k) =
      pZero * ThreeLevelWordDual.source k * (pOne+pTwo) := by
  rw [up_blocks_match.1, up_blocks_match.2.1, block_parts, low_parts, high_parts]

/-- Up Right parts for the stated finite source data. -/
theorem upRight_parts (k : Fin 6) :
    fromParts (upRightReal k) (upRightImag k) =
      (pOne+pTwo) * ThreeLevelWordDual.source k * pZero := by
  rw [up_blocks_match.2.2.1, up_blocks_match.2.2.2, block_parts, low_parts, high_parts]

def upColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 1 then edgeZeroTwoReal k else 0) +
    twoSidedReal (upLeftReal k) (upLeftImag k) (upRightReal k) (upRightImag k)
      (maskedInputReal l) (maskedInputImag l)

def upColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 1 then edgeZeroTwoImag k else 0) +
    twoSidedImag (upLeftReal k) (upLeftImag k) (upRightReal k) (upRightImag k)
      (maskedInputReal l) (maskedInputImag l)

def downColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  twoSidedReal (upRightReal k) (upRightImag k) (upLeftReal k) (upLeftImag k)
    (maskedInputReal l) (maskedInputImag l)

def downColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  twoSidedImag (upRightReal k) (upRightImag k) (upLeftReal k) (upLeftImag k)
    (maskedInputReal l) (maskedInputImag l)

/-- Up Column parts for the stated finite source data. -/
theorem upColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (upColumnReal k l) (upColumnImag k l) =
      (if l = 1 then edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 2 else 0) +
      ((pZero * ThreeLevelWordDual.source k * (pOne+pTwo)) * maskedLiteralInput l -
        maskedLiteralInput l * ((pOne+pTwo) * ThreeLevelWordDual.source k * pZero)) := by
  rw [upColumnReal, upColumnImag, fromParts_add, twoSided_parts,
    upLeft_parts, upRight_parts, masked_parts]
  congr 1
  split_ifs
  · exact edgeZeroTwo_parts k
  · ext i j : 2
    simp [fromParts]

/-- Down Column parts for the stated finite source data. -/
theorem downColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (downColumnReal k l) (downColumnImag k l) =
      ((pOne+pTwo) * ThreeLevelWordDual.source k * pZero) * maskedLiteralInput l -
        maskedLiteralInput l * (pZero * ThreeLevelWordDual.source k * (pOne+pTwo)) := by
  rw [downColumnReal, downColumnImag, twoSided_parts, upLeft_parts, upRight_parts,
    masked_parts]

/-- Source row 0 for the stated finite source data. -/
private theorem source_row_0 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 0 l =
      upColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 0 l =
      upColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 0 l =
      downColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 0 l =
      downColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) := by
  decide +kernel

/-- Source row 1 for the stated finite source data. -/
private theorem source_row_1 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 1 l =
      upColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 1 l =
      upColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 1 l =
      downColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 1 l =
      downColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) := by
  decide +kernel

/-- Source row 2 for the stated finite source data. -/
private theorem source_row_2 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 2 l =
      upColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 2 l =
      upColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 2 l =
      downColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 2 l =
      downColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) := by
  decide +kernel

/-- Source row 3 for the stated finite source data. -/
private theorem source_row_3 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 3 l =
      upColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 3 l =
      upColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 3 l =
      downColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 3 l =
      downColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) := by
  decide +kernel

/-- Source row 4 for the stated finite source data. -/
private theorem source_row_4 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 4 l =
      upColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 4 l =
      upColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 4 l =
      downColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 4 l =
      downColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) := by
  decide +kernel

/-- Source row 5 for the stated finite source data. -/
private theorem source_row_5 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 5 l =
      upColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 5 l =
      upColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 5 l =
      downColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 5 l =
      downColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) := by
  decide +kernel

/-- Source row 6 for the stated finite source data. -/
private theorem source_row_6 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 6 l =
      upColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 6 l =
      upColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 6 l =
      downColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 6 l =
      downColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) := by
  decide +kernel

/-- Source row 7 for the stated finite source data. -/
private theorem source_row_7 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 7 l =
      upColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 7 l =
      upColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 7 l =
      downColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 7 l =
      downColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) := by
  decide +kernel

/-- Source row 8 for the stated finite source data. -/
private theorem source_row_8 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 8 l =
      upColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 8 l =
      upColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 8 l =
      downColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 8 l =
      downColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) := by
  decide +kernel

/-- Source row 9 for the stated finite source data. -/
private theorem source_row_9 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 9 l =
      upColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 9 l =
      upColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 9 l =
      downColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 9 l =
      downColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) := by
  decide +kernel

/-- Source row 10 for the stated finite source data. -/
private theorem source_row_10 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 10 l =
      upColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 10 l =
      upColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 10 l =
      downColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 10 l =
      downColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) := by
  decide +kernel

/-- Source row 11 for the stated finite source data. -/
private theorem source_row_11 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 11 l =
      upColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 11 l =
      upColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 11 l =
      downColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 11 l =
      downColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) := by
  decide +kernel

/-- Source row 12 for the stated finite source data. -/
private theorem source_row_12 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 12 l =
      upColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 12 l =
      upColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 12 l =
      downColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 12 l =
      downColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) := by
  decide +kernel

/-- Source row 13 for the stated finite source data. -/
private theorem source_row_13 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 13 l =
      upColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 13 l =
      upColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 13 l =
      downColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 13 l =
      downColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) := by
  decide +kernel

/-- Source row 14 for the stated finite source data. -/
private theorem source_row_14 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 14 l =
      upColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 14 l =
      upColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 14 l =
      downColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 14 l =
      downColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) := by
  decide +kernel

/-- Source row 15 for the stated finite source data. -/
private theorem source_row_15 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 15 l =
      upColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 15 l =
      upColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 15 l =
      downColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 15 l =
      downColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) := by
  decide +kernel

/-- Source row 16 for the stated finite source data. -/
private theorem source_row_16 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 16 l =
      upColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 16 l =
      upColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 16 l =
      downColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 16 l =
      downColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) := by
  decide +kernel

/-- Source row 17 for the stated finite source data. -/
private theorem source_row_17 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 17 l =
      upColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 17 l =
      upColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 17 l =
      downColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 17 l =
      downColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) := by
  decide +kernel

/-- Source row 18 for the stated finite source data. -/
private theorem source_row_18 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 18 l =
      upColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 18 l =
      upColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 18 l =
      downColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 18 l =
      downColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) := by
  decide +kernel

/-- Source row 19 for the stated finite source data. -/
private theorem source_row_19 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 19 l =
      upColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 19 l =
      upColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 19 l =
      downColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 19 l =
      downColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) := by
  decide +kernel

/-- Source row 20 for the stated finite source data. -/
private theorem source_row_20 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 20 l =
      upColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 20 l =
      upColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 20 l =
      downColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 20 l =
      downColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) := by
  decide +kernel

/-- Source row 21 for the stated finite source data. -/
private theorem source_row_21 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 21 l =
      upColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 21 l =
      upColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 21 l =
      downColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 21 l =
      downColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) := by
  decide +kernel

/-- Source row 22 for the stated finite source data. -/
private theorem source_row_22 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 22 l =
      upColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 22 l =
      upColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 22 l =
      downColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 22 l =
      downColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) := by
  decide +kernel

/-- Source row 23 for the stated finite source data. -/
private theorem source_row_23 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 23 l =
      upColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 23 l =
      upColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 23 l =
      downColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 23 l =
      downColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) := by
  decide +kernel

/-- Source row 24 for the stated finite source data. -/
private theorem source_row_24 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 24 l =
      upColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 24 l =
      upColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 24 l =
      downColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 24 l =
      downColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) := by
  decide +kernel

/-- Source row 25 for the stated finite source data. -/
private theorem source_row_25 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 25 l =
      upColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 25 l =
      upColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 25 l =
      downColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 25 l =
      downColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) := by
  decide +kernel

/-- Source row 26 for the stated finite source data. -/
private theorem source_row_26 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 26 l =
      upColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 26 l =
      upColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 26 l =
      downColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 26 l =
      downColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) := by
  decide +kernel

/-- Source row 27 for the stated finite source data. -/
private theorem source_row_27 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 27 l =
      upColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 27 l =
      upColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 27 l =
      downColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 27 l =
      downColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) := by
  decide +kernel

/-- Source row 28 for the stated finite source data. -/
private theorem source_row_28 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 28 l =
      upColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 28 l =
      upColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 28 l =
      downColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 28 l =
      downColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) := by
  decide +kernel

/-- Source row 29 for the stated finite source data. -/
private theorem source_row_29 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 29 l =
      upColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 29 l =
      upColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 29 l =
      downColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 29 l =
      downColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) := by
  decide +kernel

/-- Source row 30 for the stated finite source data. -/
private theorem source_row_30 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 30 l =
      upColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 30 l =
      upColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 30 l =
      downColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 30 l =
      downColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) := by
  decide +kernel

/-- Source row 31 for the stated finite source data. -/
private theorem source_row_31 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 31 l =
      upColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 31 l =
      upColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 31 l =
      downColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 31 l =
      downColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) := by
  decide +kernel

/-- Source row 32 for the stated finite source data. -/
private theorem source_row_32 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 32 l =
      upColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 32 l =
      upColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 32 l =
      downColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 32 l =
      downColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) := by
  decide +kernel

/-- Source row 33 for the stated finite source data. -/
private theorem source_row_33 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 33 l =
      upColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 33 l =
      upColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 33 l =
      downColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 33 l =
      downColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) := by
  decide +kernel

/-- Source row 34 for the stated finite source data. -/
private theorem source_row_34 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 34 l =
      upColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 34 l =
      upColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 34 l =
      downColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 34 l =
      downColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) := by
  decide +kernel

/-- Source row 35 for the stated finite source data. -/
private theorem source_row_35 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 35 l =
      upColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 35 l =
      upColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 35 l =
      downColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 35 l =
      downColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) := by
  decide +kernel

/-- Source row 36 for the stated finite source data. -/
private theorem source_row_36 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 36 l =
      upColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 36 l =
      upColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 36 l =
      downColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 36 l =
      downColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) := by
  decide +kernel

/-- Source row 37 for the stated finite source data. -/
private theorem source_row_37 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 37 l =
      upColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 37 l =
      upColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 37 l =
      downColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 37 l =
      downColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) := by
  decide +kernel

/-- Source row 38 for the stated finite source data. -/
private theorem source_row_38 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 38 l =
      upColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 38 l =
      upColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 38 l =
      downColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 38 l =
      downColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) := by
  decide +kernel

/-- Source row 39 for the stated finite source data. -/
private theorem source_row_39 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 39 l =
      upColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 39 l =
      upColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 39 l =
      downColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 39 l =
      downColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) := by
  decide +kernel

/-- Source row 40 for the stated finite source data. -/
private theorem source_row_40 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 40 l =
      upColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 40 l =
      upColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 40 l =
      downColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 40 l =
      downColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) := by
  decide +kernel

/-- Source row 41 for the stated finite source data. -/
private theorem source_row_41 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 41 l =
      upColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 41 l =
      upColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 41 l =
      downColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 41 l =
      downColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) := by
  decide +kernel

/-- Source row 42 for the stated finite source data. -/
private theorem source_row_42 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 42 l =
      upColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 42 l =
      upColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 42 l =
      downColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 42 l =
      downColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) := by
  decide +kernel

/-- Source row 43 for the stated finite source data. -/
private theorem source_row_43 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 43 l =
      upColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 43 l =
      upColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 43 l =
      downColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 43 l =
      downColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) := by
  decide +kernel

/-- Source row 44 for the stated finite source data. -/
private theorem source_row_44 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 44 l =
      upColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 44 l =
      upColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 44 l =
      downColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 44 l =
      downColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) := by
  decide +kernel

/-- Source row 45 for the stated finite source data. -/
private theorem source_row_45 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 45 l =
      upColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 45 l =
      upColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 45 l =
      downColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 45 l =
      downColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) := by
  decide +kernel

/-- Source row 46 for the stated finite source data. -/
private theorem source_row_46 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 46 l =
      upColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 46 l =
      upColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 46 l =
      downColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 46 l =
      downColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) := by
  decide +kernel

/-- Source row 47 for the stated finite source data. -/
private theorem source_row_47 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 47 l =
      upColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 47 l =
      upColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 47 l =
      downColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 47 l =
      downColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) := by
  decide +kernel

/-- Source row 48 for the stated finite source data. -/
private theorem source_row_48 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 48 l =
      upColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 48 l =
      upColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 48 l =
      downColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 48 l =
      downColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) := by
  decide +kernel

/-- Source row 49 for the stated finite source data. -/
private theorem source_row_49 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 49 l =
      upColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 49 l =
      upColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 49 l =
      downColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 49 l =
      downColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) := by
  decide +kernel

/-- Source row 50 for the stated finite source data. -/
private theorem source_row_50 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 50 l =
      upColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 50 l =
      upColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 50 l =
      downColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 50 l =
      downColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) := by
  decide +kernel

/-- Source row 51 for the stated finite source data. -/
private theorem source_row_51 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 51 l =
      upColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 51 l =
      upColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 51 l =
      downColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 51 l =
      downColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) := by
  decide +kernel

/-- Source row 52 for the stated finite source data. -/
private theorem source_row_52 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 52 l =
      upColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 52 l =
      upColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 52 l =
      downColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 52 l =
      downColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) := by
  decide +kernel

/-- Source row 53 for the stated finite source data. -/
private theorem source_row_53 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 53 l =
      upColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 53 l =
      upColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 53 l =
      downColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 53 l =
      downColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) := by
  decide +kernel

/-- Source row 54 for the stated finite source data. -/
private theorem source_row_54 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 54 l =
      upColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 54 l =
      upColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 54 l =
      downColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 54 l =
      downColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) := by
  decide +kernel

/-- Source row 55 for the stated finite source data. -/
private theorem source_row_55 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 55 l =
      upColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 55 l =
      upColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 55 l =
      downColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 55 l =
      downColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) := by
  decide +kernel

/-- Source row 56 for the stated finite source data. -/
private theorem source_row_56 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 56 l =
      upColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 56 l =
      upColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 56 l =
      downColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 56 l =
      downColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) := by
  decide +kernel

/-- Source row 57 for the stated finite source data. -/
private theorem source_row_57 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 57 l =
      upColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 57 l =
      upColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 57 l =
      downColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 57 l =
      downColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) := by
  decide +kernel

/-- Source row 58 for the stated finite source data. -/
private theorem source_row_58 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 58 l =
      upColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 58 l =
      upColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 58 l =
      downColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 58 l =
      downColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) := by
  decide +kernel

/-- Source row 59 for the stated finite source data. -/
private theorem source_row_59 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 59 l =
      upColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 59 l =
      upColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 59 l =
      downColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 59 l =
      downColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) := by
  decide +kernel

/-- Source row 60 for the stated finite source data. -/
private theorem source_row_60 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 60 l =
      upColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 60 l =
      upColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 60 l =
      downColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 60 l =
      downColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) := by
  decide +kernel

/-- Source row 61 for the stated finite source data. -/
private theorem source_row_61 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 61 l =
      upColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 61 l =
      upColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 61 l =
      downColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 61 l =
      downColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) := by
  decide +kernel

/-- Source row 62 for the stated finite source data. -/
private theorem source_row_62 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 62 l =
      upColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 62 l =
      upColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 62 l =
      downColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 62 l =
      downColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) := by
  decide +kernel

/-- Source row 63 for the stated finite source data. -/
private theorem source_row_63 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 63 l =
      upColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 63 l =
      upColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 63 l =
      downColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 63 l =
      downColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) := by
  decide +kernel

/-- Source row 64 for the stated finite source data. -/
private theorem source_row_64 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 64 l =
      upColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 64 l =
      upColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 64 l =
      downColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 64 l =
      downColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) := by
  decide +kernel

/-- Source row 65 for the stated finite source data. -/
private theorem source_row_65 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 65 l =
      upColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 65 l =
      upColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 65 l =
      downColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 65 l =
      downColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) := by
  decide +kernel

/-- Source row 66 for the stated finite source data. -/
private theorem source_row_66 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 66 l =
      upColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 66 l =
      upColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 66 l =
      downColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 66 l =
      downColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) := by
  decide +kernel

/-- Source row 67 for the stated finite source data. -/
private theorem source_row_67 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 67 l =
      upColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 67 l =
      upColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 67 l =
      downColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 67 l =
      downColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) := by
  decide +kernel

/-- Source row 68 for the stated finite source data. -/
private theorem source_row_68 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 68 l =
      upColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 68 l =
      upColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 68 l =
      downColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 68 l =
      downColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) := by
  decide +kernel

/-- Source row 69 for the stated finite source data. -/
private theorem source_row_69 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 69 l =
      upColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 69 l =
      upColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 69 l =
      downColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 69 l =
      downColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) := by
  decide +kernel

/-- Source row 70 for the stated finite source data. -/
private theorem source_row_70 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 70 l =
      upColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 70 l =
      upColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 70 l =
      downColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 70 l =
      downColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) := by
  decide +kernel

/-- Source row 71 for the stated finite source data. -/
private theorem source_row_71 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 71 l =
      upColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 71 l =
      upColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 71 l =
      downColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 71 l =
      downColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) := by
  decide +kernel

/-- Source row 72 for the stated finite source data. -/
private theorem source_row_72 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 72 l =
      upColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 72 l =
      upColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 72 l =
      downColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 72 l =
      downColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) := by
  decide +kernel

/-- Source row 73 for the stated finite source data. -/
private theorem source_row_73 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 73 l =
      upColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 73 l =
      upColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 73 l =
      downColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 73 l =
      downColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) := by
  decide +kernel

/-- Source row 74 for the stated finite source data. -/
private theorem source_row_74 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 74 l =
      upColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 74 l =
      upColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 74 l =
      downColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 74 l =
      downColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) := by
  decide +kernel

/-- Source row 75 for the stated finite source data. -/
private theorem source_row_75 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 75 l =
      upColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 75 l =
      upColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 75 l =
      downColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 75 l =
      downColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) := by
  decide +kernel

/-- Source row 76 for the stated finite source data. -/
private theorem source_row_76 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 76 l =
      upColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 76 l =
      upColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 76 l =
      downColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 76 l =
      downColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) := by
  decide +kernel

/-- Source row 77 for the stated finite source data. -/
private theorem source_row_77 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 77 l =
      upColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 77 l =
      upColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 77 l =
      downColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 77 l =
      downColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) := by
  decide +kernel

/-- Source row 78 for the stated finite source data. -/
private theorem source_row_78 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 78 l =
      upColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 78 l =
      upColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 78 l =
      downColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 78 l =
      downColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) := by
  decide +kernel

/-- Source row 79 for the stated finite source data. -/
private theorem source_row_79 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 79 l =
      upColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 79 l =
      upColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 79 l =
      downColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 79 l =
      downColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) := by
  decide +kernel

/-- Source row 80 for the stated finite source data. -/
private theorem source_row_80 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 80 l =
      upColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 80 l =
      upColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 80 l =
      downColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 80 l =
      downColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) := by
  decide +kernel

/-- Source row 81 for the stated finite source data. -/
private theorem source_row_81 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 81 l =
      upColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 81 l =
      upColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 81 l =
      downColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 81 l =
      downColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) := by
  decide +kernel

/-- Source row 82 for the stated finite source data. -/
private theorem source_row_82 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 82 l =
      upColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 82 l =
      upColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 82 l =
      downColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 82 l =
      downColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) := by
  decide +kernel

/-- Source row 83 for the stated finite source data. -/
private theorem source_row_83 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 83 l =
      upColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 83 l =
      upColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 83 l =
      downColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 83 l =
      downColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) := by
  decide +kernel

/-- Source row 84 for the stated finite source data. -/
private theorem source_row_84 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 84 l =
      upColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 84 l =
      upColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 84 l =
      downColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 84 l =
      downColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) := by
  decide +kernel

/-- Source row 85 for the stated finite source data. -/
private theorem source_row_85 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 85 l =
      upColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 85 l =
      upColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 85 l =
      downColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 85 l =
      downColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) := by
  decide +kernel

/-- Source row 86 for the stated finite source data. -/
private theorem source_row_86 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 86 l =
      upColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 86 l =
      upColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 86 l =
      downColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 86 l =
      downColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) := by
  decide +kernel

/-- Source row 87 for the stated finite source data. -/
private theorem source_row_87 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 87 l =
      upColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 87 l =
      upColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 87 l =
      downColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 87 l =
      downColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) := by
  decide +kernel

/-- Source row 88 for the stated finite source data. -/
private theorem source_row_88 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 88 l =
      upColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 88 l =
      upColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 88 l =
      downColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 88 l =
      downColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) := by
  decide +kernel

/-- Source row 89 for the stated finite source data. -/
private theorem source_row_89 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 89 l =
      upColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 89 l =
      upColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 89 l =
      downColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 89 l =
      downColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) := by
  decide +kernel

/-- Source row 90 for the stated finite source data. -/
private theorem source_row_90 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 90 l =
      upColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 90 l =
      upColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 90 l =
      downColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 90 l =
      downColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) := by
  decide +kernel

/-- Source row 91 for the stated finite source data. -/
private theorem source_row_91 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 91 l =
      upColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 91 l =
      upColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 91 l =
      downColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 91 l =
      downColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) := by
  decide +kernel

/-- Source row 92 for the stated finite source data. -/
private theorem source_row_92 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 92 l =
      upColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 92 l =
      upColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 92 l =
      downColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 92 l =
      downColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) := by
  decide +kernel

/-- Source row 93 for the stated finite source data. -/
private theorem source_row_93 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 93 l =
      upColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 93 l =
      upColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 93 l =
      downColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 93 l =
      downColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) := by
  decide +kernel

/-- Source row 94 for the stated finite source data. -/
private theorem source_row_94 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 94 l =
      upColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 94 l =
      upColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 94 l =
      downColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 94 l =
      downColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) := by
  decide +kernel

/-- Source row 95 for the stated finite source data. -/
private theorem source_row_95 :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal 95 l =
      upColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag 95 l =
      upColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal 95 l =
      downColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag 95 l =
      downColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) := by
  decide +kernel

/-- Source parts match for the stated finite source data. -/
theorem source_parts_match (a : Fin 96) :
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpReal a l =
      upColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceUpImag a l =
      upColumnImag (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownReal a l =
      downColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelHighCollisionCoefficientTables.faceDownImag a l =
      downColumnImag (sourceIndex a) l (rowIndex a) (columnIndex a)) := by
  fin_cases a
  · exact source_row_0
  · exact source_row_1
  · exact source_row_2
  · exact source_row_3
  · exact source_row_4
  · exact source_row_5
  · exact source_row_6
  · exact source_row_7
  · exact source_row_8
  · exact source_row_9
  · exact source_row_10
  · exact source_row_11
  · exact source_row_12
  · exact source_row_13
  · exact source_row_14
  · exact source_row_15
  · exact source_row_16
  · exact source_row_17
  · exact source_row_18
  · exact source_row_19
  · exact source_row_20
  · exact source_row_21
  · exact source_row_22
  · exact source_row_23
  · exact source_row_24
  · exact source_row_25
  · exact source_row_26
  · exact source_row_27
  · exact source_row_28
  · exact source_row_29
  · exact source_row_30
  · exact source_row_31
  · exact source_row_32
  · exact source_row_33
  · exact source_row_34
  · exact source_row_35
  · exact source_row_36
  · exact source_row_37
  · exact source_row_38
  · exact source_row_39
  · exact source_row_40
  · exact source_row_41
  · exact source_row_42
  · exact source_row_43
  · exact source_row_44
  · exact source_row_45
  · exact source_row_46
  · exact source_row_47
  · exact source_row_48
  · exact source_row_49
  · exact source_row_50
  · exact source_row_51
  · exact source_row_52
  · exact source_row_53
  · exact source_row_54
  · exact source_row_55
  · exact source_row_56
  · exact source_row_57
  · exact source_row_58
  · exact source_row_59
  · exact source_row_60
  · exact source_row_61
  · exact source_row_62
  · exact source_row_63
  · exact source_row_64
  · exact source_row_65
  · exact source_row_66
  · exact source_row_67
  · exact source_row_68
  · exact source_row_69
  · exact source_row_70
  · exact source_row_71
  · exact source_row_72
  · exact source_row_73
  · exact source_row_74
  · exact source_row_75
  · exact source_row_76
  · exact source_row_77
  · exact source_row_78
  · exact source_row_79
  · exact source_row_80
  · exact source_row_81
  · exact source_row_82
  · exact source_row_83
  · exact source_row_84
  · exact source_row_85
  · exact source_row_86
  · exact source_row_87
  · exact source_row_88
  · exact source_row_89
  · exact source_row_90
  · exact source_row_91
  · exact source_row_92
  · exact source_row_93
  · exact source_row_94
  · exact source_row_95

/-- Two Sided edge one stack mul Vec for the stated finite source data. -/
theorem twoSided_edge_one_stack_mulVec (S : Matrix (Fin 96) (Fin 15) ℂ)
    (A B E : Fin 6 → Operator 4)
    (hS : ∀ a l, S a l =
      ((if l = 1 then E (sourceIndex a) else 0) +
      (A (sourceIndex a) * maskedLiteralInput l -
        maskedLiteralInput l * B (sourceIndex a))) (rowIndex a) (columnIndex a))
    (σ : Perm) (c d : ℂ) (Y : Operator 4) (hY : IsFast σ Y) (a : Fin 96) :
    (S *ᵥ fullCoordinates c d Y) a =
      (d • E (sourceIndex a) +
      (A (sourceIndex a) * Y - Y * B (sourceIndex a)))
        (rowIndex a) (columnIndex a) := by
  rw [← twoSided_maskedLiteralInput σ c d Y hY
    (A (sourceIndex a)) (B (sourceIndex a))]
  simp only [Matrix.mulVec, dotProduct, hS, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, fullCoordinates_one]
    ring
  · apply Finset.sum_congr rfl
    intro l _
    ring

/-- Face Up apply for the stated finite source data. -/
theorem faceUp_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelHighCollisionCoefficientTables.faceUp a l =
      ((if l = 1 then edge (Equiv.refl (Fin 3))
          (ThreeLevelWordDual.source (sourceIndex a)) 0 2 else 0) +
        ((pZero * ThreeLevelWordDual.source (sourceIndex a) * (pOne+pTwo)) *
          maskedLiteralInput l - maskedLiteralInput l *
            ((pOne+pTwo) * ThreeLevelWordDual.source (sourceIndex a) * pZero)))
              (rowIndex a) (columnIndex a) := by
  rw [← upColumn_parts]
  simp only [ThreeLevelHighCollisionCoefficientTables.faceUp, fromParts,
    (source_parts_match a).1 l, (source_parts_match a).2.1 l]

/-- Face Down apply for the stated finite source data. -/
theorem faceDown_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelHighCollisionCoefficientTables.faceDown a l =
      (((pOne+pTwo) * ThreeLevelWordDual.source (sourceIndex a) * pZero) *
        maskedLiteralInput l - maskedLiteralInput l *
          (pZero * ThreeLevelWordDual.source (sourceIndex a) * (pOne+pTwo)))
            (rowIndex a) (columnIndex a) := by
  rw [← downColumn_parts]
  simp only [ThreeLevelHighCollisionCoefficientTables.faceDown, fromParts,
    (source_parts_match a).2.2.1 l, (source_parts_match a).2.2.2 l]

/-- Face Up mul Vec for the stated finite source data. -/
theorem faceUp_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelHighCollisionCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      (d • edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source (sourceIndex a)) 0 2 +
        ((pZero * ThreeLevelWordDual.source (sourceIndex a) * (pOne+pTwo)) * Y -
          Y * ((pOne+pTwo) * ThreeLevelWordDual.source (sourceIndex a) * pZero)))
            (rowIndex a) (columnIndex a) :=
  twoSided_edge_one_stack_mulVec ThreeLevelHighCollisionCoefficientTables.faceUp
    (fun k => pZero * ThreeLevelWordDual.source k * (pOne+pTwo))
    (fun k => (pOne+pTwo) * ThreeLevelWordDual.source k * pZero)
    (fun k => edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 2)
    faceUp_apply (Equiv.refl (Fin 3)) c d Y hY a

/-- Face Down mul Vec for the stated finite source data. -/
theorem faceDown_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelHighCollisionCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      (((pOne+pTwo) * ThreeLevelWordDual.source (sourceIndex a) * pZero) * Y -
        Y * (pZero * ThreeLevelWordDual.source (sourceIndex a) * (pOne+pTwo)))
          (rowIndex a) (columnIndex a) :=
  twoSided_stack_mulVec ThreeLevelHighCollisionCoefficientTables.faceDown
    (fun k => (pOne+pTwo) * ThreeLevelWordDual.source k * pZero)
    (fun k => pZero * ThreeLevelWordDual.source k * (pOne+pTwo))
    faceDown_apply (Equiv.refl (Fin 3)) c d Y hY a


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionSourceTables
