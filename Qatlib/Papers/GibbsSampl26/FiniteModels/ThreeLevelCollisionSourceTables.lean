/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionCoefficientTables
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCoordinateMetric

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Actual thermal source tables on the order012 collision face

The two fixed thermal blocks and the separate population edge are checked
against the original six source matrices. The96row checks cover all15
complex coordinates of both nonconstant source stacks. Masked-input
reconstruction retains the complete fast space and the actual metric chart.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators ComplexOrder


open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionSourceTables

open ThreeLevelCluster ThreeLevelInvariant ThreeLevelWordDual
open ThreeLevelGramCertificateCorner ThreeLevelCornerFastChart ThreeLevelCoordinateMetric
open ThreeLevelGramCertificate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

def lowReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    0, 8/9, (-2/9), 0;
    0, (-2/9), 5/9, 0;
    0, 0, 0, 5/9]

def lowImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 4/9;
    0, (-2/9), (-4/9), 0]

def highReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 1/9, 2/9, 0;
    0, 2/9, 4/9, 0;
    0, 0, 0, 4/9]

def highImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, (-2/9);
    0, 0, 0, (-4/9);
    0, 2/9, 4/9, 0]

def zeroReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 8/9, (-2/9), 0;
    0, (-2/9), 5/9, 0;
    0, 0, 0, 5/9]

def zeroImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 4/9;
    0, (-2/9), (-4/9), 0]

def upLeftReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 2/9, 4/9, 0;
    0, 0, 0, 4/9;
    0, 0, 0, 0;
    0, 1/9, 2/9, 0],
    !![0, 0, 0, (-4/9);
    0, 14/81, 28/81, 0;
    0, (-8/81), (-16/81), 0;
    0, 0, 0, 2/81],
    !![0, 0, 0, 0;
    0, 16/81, 32/81, 0;
    0, (-4/81), (-8/81), 0;
    0, 0, 0, (-8/81)],
    !![0, 1/9, 2/9, 0;
    0, 0, 0, 0;
    0, 0, 0, 4/9;
    0, 2/9, 4/9, 0],
    !![0, 0, 0, (-2/9);
    0, (-8/81), (-16/81), 0;
    0, 2/81, 4/81, 0;
    0, 0, 0, 4/81],
    !![0, 0, 0, 0;
    0, (-8/81), (-16/81), 0;
    0, 20/81, 40/81, 0;
    0, 0, 0, (-32/81)]]

def upLeftImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, (-4/9);
    0, 2/9, 4/9, 0;
    0, 0, 0, 0;
    0, 0, 0, (-2/9)],
    !![0, (-2/9), (-4/9), 0;
    0, 0, 0, (-28/81);
    0, 0, 0, 16/81;
    0, 1/81, 2/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, (-32/81);
    0, 0, 0, 8/81;
    0, (-4/81), (-8/81), 0],
    !![0, 0, 0, (-2/9);
    0, 0, 0, 0;
    0, 2/9, 4/9, 0;
    0, 0, 0, (-4/9)],
    !![0, (-1/9), (-2/9), 0;
    0, 0, 0, 16/81;
    0, 0, 0, (-4/81);
    0, 2/81, 4/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 16/81;
    0, 0, 0, (-40/81);
    0, (-16/81), (-32/81), 0]]

def upRightReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    2/9, 0, 0, 1/9;
    4/9, 0, 0, 2/9;
    0, 4/9, 0, 0],
    !![0, 0, 0, 0;
    0, 14/81, (-8/81), 0;
    0, 28/81, (-16/81), 0;
    (-4/9), 0, 0, 2/81],
    !![0, 0, 0, 0;
    0, 16/81, (-4/81), 0;
    0, 32/81, (-8/81), 0;
    0, 0, 0, (-8/81)],
    !![0, 0, 0, 0;
    1/9, 0, 0, 2/9;
    2/9, 0, 0, 4/9;
    0, 0, 4/9, 0],
    !![0, 0, 0, 0;
    0, (-8/81), 2/81, 0;
    0, (-16/81), 4/81, 0;
    (-2/9), 0, 0, 4/81],
    !![0, 0, 0, 0;
    0, (-8/81), 20/81, 0;
    0, (-16/81), 40/81, 0;
    0, 0, 0, (-32/81)]]

def upRightImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, (-2/9), 0, 0;
    0, (-4/9), 0, 0;
    4/9, 0, 0, 2/9],
    !![0, 0, 0, 0;
    2/9, 0, 0, (-1/81);
    4/9, 0, 0, (-2/81);
    0, 28/81, (-16/81), 0],
    !![0, 0, 0, 0;
    0, 0, 0, 4/81;
    0, 0, 0, 8/81;
    0, 32/81, (-8/81), 0],
    !![0, 0, 0, 0;
    0, 0, (-2/9), 0;
    0, 0, (-4/9), 0;
    2/9, 0, 0, 4/9],
    !![0, 0, 0, 0;
    1/9, 0, 0, (-2/81);
    2/9, 0, 0, (-4/81);
    0, (-16/81), 4/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 16/81;
    0, 0, 0, 32/81;
    0, (-16/81), 40/81, 0]]

def edgeZeroTwoReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, 0, 0, 1/3;
    0, 0, 0, (-2/9);
    0, (-1/3), 2/9, 0],
    !![0, 0, 0, 0;
    0, 0, 4/9, 0;
    0, (-4/9), 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 4/9, 0;
    0, (-4/9), 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, (-2/9);
    0, 0, 0, 0;
    0, 2/9, 0, 0],
    !![0, 0, 0, 0;
    0, 0, (-2/9), 0;
    0, 2/9, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, (-4/9), 0;
    0, 4/9, 0, 0;
    0, 0, 0, 0]]

def edgeZeroTwoImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, 4/9, 4/9, 0;
    0, 4/9, 0, 0;
    0, 0, 0, (-4/9)],
    !![0, 0, 0, 0;
    0, 0, 0, (-1/3);
    0, 0, 0, 2/9;
    0, (-1/3), 2/9, 0],
    !![0, 0, 0, 0;
    0, 0, 0, (-4/9);
    0, 0, 0, 0;
    0, (-4/9), 0, 0],
    !![0, 0, 0, 0;
    0, 0, 2/9, 0;
    0, 2/9, 8/9, 0;
    0, 0, 0, (-8/9)],
    !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 0;
    0, 2/9, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, (-8/9);
    0, 0, (-8/9), 0]]

/-- Low parts for the stated finite source data. -/
theorem low_parts :
    fromParts lowReal lowImag = pZero+pOne := by
  rw [pZero, pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, lowReal, lowImag, pOne, Matrix.one_apply] <;> ring

/-- High parts for the stated finite source data. -/
theorem high_parts : fromParts highReal highImag = pTwo := by
  rw [pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, highReal, highImag] <;> ring

/-- Zero parts for the stated finite source data. -/
theorem zero_parts : fromParts zeroReal zeroImag = pZero := by
  rw [pZero, pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, zeroReal, zeroImag, pOne, Matrix.one_apply] <;> ring

def blockReal (Lr Li Rr Ri : Matrix (Fin 4) (Fin 4) ℚ) (k : Fin 6) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  (Lr * sourceReal k - Li * sourceImag k) * Rr -
    (Lr * sourceImag k + Li * sourceReal k) * Ri

def blockImag (Lr Li Rr Ri : Matrix (Fin 4) (Fin 4) ℚ) (k : Fin 6) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  (Lr * sourceReal k - Li * sourceImag k) * Ri +
    (Lr * sourceImag k + Li * sourceReal k) * Rr

/-- Block parts for the stated finite source data. -/
theorem block_parts (Lr Li Rr Ri : Matrix (Fin 4) (Fin 4) ℚ) (k : Fin 6) :
    fromParts (blockReal Lr Li Rr Ri k) (blockImag Lr Li Rr Ri k) =
      fromParts Lr Li * ThreeLevelWordDual.source k * fromParts Rr Ri := by
  rw [← literalSource_eq_source, literalSource, parts_mul, parts_mul]
  rfl

/-- Up blocks match for the stated finite source data. -/
theorem up_blocks_match :
    (∀ k, upLeftReal k = blockReal lowReal lowImag highReal highImag k) ∧
    (∀ k, upLeftImag k = blockImag lowReal lowImag highReal highImag k) ∧
    (∀ k, upRightReal k = blockReal highReal highImag lowReal lowImag k) ∧
    (∀ k, upRightImag k = blockImag highReal highImag lowReal lowImag k) := by
  decide +kernel

/-- Edge blocks match for the stated finite source data. -/
theorem edge_blocks_match :
    (∀ k, edgeZeroTwoReal k =
      blockReal zeroReal zeroImag highReal highImag k -
        blockReal highReal highImag zeroReal zeroImag k) ∧
    (∀ k, edgeZeroTwoImag k =
      blockImag zeroReal zeroImag highReal highImag k -
        blockImag highReal highImag zeroReal zeroImag k) := by
  decide +kernel

/-- Up Left parts for the stated finite source data. -/
theorem upLeft_parts (k : Fin 6) :
    fromParts (upLeftReal k) (upLeftImag k) =
      (pZero+pOne) * ThreeLevelWordDual.source k * pTwo := by
  rw [up_blocks_match.1, up_blocks_match.2.1, block_parts, low_parts, high_parts]

/-- Up Right parts for the stated finite source data. -/
theorem upRight_parts (k : Fin 6) :
    fromParts (upRightReal k) (upRightImag k) =
      pTwo * ThreeLevelWordDual.source k * (pZero+pOne) := by
  rw [up_blocks_match.2.2.1, up_blocks_match.2.2.2, block_parts, low_parts, high_parts]

/-- Edge Zero Two parts for the stated finite source data. -/
theorem edgeZeroTwo_parts (k : Fin 6) :
    fromParts (edgeZeroTwoReal k) (edgeZeroTwoImag k) =
      edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 2 := by
  rw [edge_blocks_match.1, edge_blocks_match.2, fromParts_sub,
    block_parts, block_parts, zero_parts, high_parts]
  rfl

def maskedInputReal (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  if l.val < 2 then 0 else inputMatrixReal l

def maskedInputImag (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  if l.val < 2 then 0 else inputMatrixImag l

def maskedLiteralInput (l : Fin 15) : Operator 4 :=
  if l.val < 2 then 0 else literalInput l

/-- Masked parts for the stated finite source data. -/
theorem masked_parts (l : Fin 15) :
    fromParts (maskedInputReal l) (maskedInputImag l) = maskedLiteralInput l := by
  unfold maskedInputReal maskedInputImag maskedLiteralInput
  split_ifs
  · ext i j : 2
    simp [fromParts]
  · rfl

def twoSidedReal (Lr Li Rr Ri Xr Xi : Matrix (Fin 4) (Fin 4) ℚ) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  Lr*Xr-Li*Xi-(Xr*Rr-Xi*Ri)

def twoSidedImag (Lr Li Rr Ri Xr Xi : Matrix (Fin 4) (Fin 4) ℚ) :
    Matrix (Fin 4) (Fin 4) ℚ :=
  Lr*Xi+Li*Xr-(Xr*Ri+Xi*Rr)

/-- Two Sided parts for the stated finite source data. -/
theorem twoSided_parts (Lr Li Rr Ri Xr Xi : Matrix (Fin 4) (Fin 4) ℚ) :
    fromParts (twoSidedReal Lr Li Rr Ri Xr Xi) (twoSidedImag Lr Li Rr Ri Xr Xi) =
      fromParts Lr Li * fromParts Xr Xi - fromParts Xr Xi * fromParts Rr Ri := by
  rw [parts_mul, parts_mul, ← fromParts_sub]
  rfl

def upColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  twoSidedReal (upLeftReal k) (upLeftImag k) (upRightReal k) (upRightImag k)
    (maskedInputReal l) (maskedInputImag l)

def upColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  twoSidedImag (upLeftReal k) (upLeftImag k) (upRightReal k) (upRightImag k)
    (maskedInputReal l) (maskedInputImag l)

def downColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 0 then edgeZeroTwoReal k else 0) +
    twoSidedReal (upRightReal k) (upRightImag k) (upLeftReal k) (upLeftImag k)
      (maskedInputReal l) (maskedInputImag l)

def downColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 0 then edgeZeroTwoImag k else 0) +
    twoSidedImag (upRightReal k) (upRightImag k) (upLeftReal k) (upLeftImag k)
      (maskedInputReal l) (maskedInputImag l)

/-- Up Column parts for the stated finite source data. -/
theorem upColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (upColumnReal k l) (upColumnImag k l) =
      ((pZero+pOne) * ThreeLevelWordDual.source k * pTwo) * maskedLiteralInput l -
        maskedLiteralInput l * (pTwo * ThreeLevelWordDual.source k * (pZero+pOne)) := by
  rw [upColumnReal, upColumnImag, twoSided_parts, upLeft_parts, upRight_parts,
    masked_parts]

/-- From Parts add for the stated finite source data. -/
theorem fromParts_add {m n : ℕ} (R I S T : Matrix (Fin m) (Fin n) ℚ) :
    fromParts (R+S) (I+T) = fromParts R I + fromParts S T := by
  ext i j
  simp [fromParts]
  ring

/-- Down Column parts for the stated finite source data. -/
theorem downColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (downColumnReal k l) (downColumnImag k l) =
      (if l = 0 then edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 2 else 0) +
      ((pTwo * ThreeLevelWordDual.source k * (pZero+pOne)) * maskedLiteralInput l -
        maskedLiteralInput l * ((pZero+pOne) * ThreeLevelWordDual.source k * pTwo)) := by
  rw [downColumnReal, downColumnImag, fromParts_add, twoSided_parts,
    upLeft_parts, upRight_parts, masked_parts]
  congr 1
  split_ifs
  · exact edgeZeroTwo_parts k
  · ext i j : 2
    simp [fromParts]
/-- Source row 0 for the stated finite source data. -/
private theorem source_row_0 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 0 l =
      upColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 0 l =
      upColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 0 l =
      downColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 0 l =
      downColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) := by
  decide +kernel

/-- Source row 1 for the stated finite source data. -/
private theorem source_row_1 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 1 l =
      upColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 1 l =
      upColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 1 l =
      downColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 1 l =
      downColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) := by
  decide +kernel

/-- Source row 2 for the stated finite source data. -/
private theorem source_row_2 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 2 l =
      upColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 2 l =
      upColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 2 l =
      downColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 2 l =
      downColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) := by
  decide +kernel

/-- Source row 3 for the stated finite source data. -/
private theorem source_row_3 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 3 l =
      upColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 3 l =
      upColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 3 l =
      downColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 3 l =
      downColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) := by
  decide +kernel

/-- Source row 4 for the stated finite source data. -/
private theorem source_row_4 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 4 l =
      upColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 4 l =
      upColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 4 l =
      downColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 4 l =
      downColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) := by
  decide +kernel

/-- Source row 5 for the stated finite source data. -/
private theorem source_row_5 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 5 l =
      upColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 5 l =
      upColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 5 l =
      downColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 5 l =
      downColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) := by
  decide +kernel

/-- Source row 6 for the stated finite source data. -/
private theorem source_row_6 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 6 l =
      upColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 6 l =
      upColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 6 l =
      downColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 6 l =
      downColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) := by
  decide +kernel

/-- Source row 7 for the stated finite source data. -/
private theorem source_row_7 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 7 l =
      upColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 7 l =
      upColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 7 l =
      downColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 7 l =
      downColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) := by
  decide +kernel

/-- Source row 8 for the stated finite source data. -/
private theorem source_row_8 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 8 l =
      upColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 8 l =
      upColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 8 l =
      downColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 8 l =
      downColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) := by
  decide +kernel

/-- Source row 9 for the stated finite source data. -/
private theorem source_row_9 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 9 l =
      upColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 9 l =
      upColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 9 l =
      downColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 9 l =
      downColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) := by
  decide +kernel

/-- Source row 10 for the stated finite source data. -/
private theorem source_row_10 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 10 l =
      upColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 10 l =
      upColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 10 l =
      downColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 10 l =
      downColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) := by
  decide +kernel

/-- Source row 11 for the stated finite source data. -/
private theorem source_row_11 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 11 l =
      upColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 11 l =
      upColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 11 l =
      downColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 11 l =
      downColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) := by
  decide +kernel

/-- Source row 12 for the stated finite source data. -/
private theorem source_row_12 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 12 l =
      upColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 12 l =
      upColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 12 l =
      downColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 12 l =
      downColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) := by
  decide +kernel

/-- Source row 13 for the stated finite source data. -/
private theorem source_row_13 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 13 l =
      upColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 13 l =
      upColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 13 l =
      downColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 13 l =
      downColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) := by
  decide +kernel

/-- Source row 14 for the stated finite source data. -/
private theorem source_row_14 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 14 l =
      upColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 14 l =
      upColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 14 l =
      downColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 14 l =
      downColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) := by
  decide +kernel

/-- Source row 15 for the stated finite source data. -/
private theorem source_row_15 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 15 l =
      upColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 15 l =
      upColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 15 l =
      downColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 15 l =
      downColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) := by
  decide +kernel

/-- Source row 16 for the stated finite source data. -/
private theorem source_row_16 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 16 l =
      upColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 16 l =
      upColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 16 l =
      downColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 16 l =
      downColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) := by
  decide +kernel

/-- Source row 17 for the stated finite source data. -/
private theorem source_row_17 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 17 l =
      upColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 17 l =
      upColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 17 l =
      downColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 17 l =
      downColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) := by
  decide +kernel

/-- Source row 18 for the stated finite source data. -/
private theorem source_row_18 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 18 l =
      upColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 18 l =
      upColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 18 l =
      downColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 18 l =
      downColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) := by
  decide +kernel

/-- Source row 19 for the stated finite source data. -/
private theorem source_row_19 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 19 l =
      upColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 19 l =
      upColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 19 l =
      downColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 19 l =
      downColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) := by
  decide +kernel

/-- Source row 20 for the stated finite source data. -/
private theorem source_row_20 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 20 l =
      upColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 20 l =
      upColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 20 l =
      downColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 20 l =
      downColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) := by
  decide +kernel

/-- Source row 21 for the stated finite source data. -/
private theorem source_row_21 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 21 l =
      upColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 21 l =
      upColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 21 l =
      downColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 21 l =
      downColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) := by
  decide +kernel

/-- Source row 22 for the stated finite source data. -/
private theorem source_row_22 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 22 l =
      upColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 22 l =
      upColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 22 l =
      downColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 22 l =
      downColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) := by
  decide +kernel

/-- Source row 23 for the stated finite source data. -/
private theorem source_row_23 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 23 l =
      upColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 23 l =
      upColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 23 l =
      downColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 23 l =
      downColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) := by
  decide +kernel

/-- Source row 24 for the stated finite source data. -/
private theorem source_row_24 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 24 l =
      upColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 24 l =
      upColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 24 l =
      downColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 24 l =
      downColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) := by
  decide +kernel

/-- Source row 25 for the stated finite source data. -/
private theorem source_row_25 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 25 l =
      upColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 25 l =
      upColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 25 l =
      downColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 25 l =
      downColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) := by
  decide +kernel

/-- Source row 26 for the stated finite source data. -/
private theorem source_row_26 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 26 l =
      upColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 26 l =
      upColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 26 l =
      downColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 26 l =
      downColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) := by
  decide +kernel

/-- Source row 27 for the stated finite source data. -/
private theorem source_row_27 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 27 l =
      upColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 27 l =
      upColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 27 l =
      downColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 27 l =
      downColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) := by
  decide +kernel

/-- Source row 28 for the stated finite source data. -/
private theorem source_row_28 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 28 l =
      upColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 28 l =
      upColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 28 l =
      downColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 28 l =
      downColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) := by
  decide +kernel

/-- Source row 29 for the stated finite source data. -/
private theorem source_row_29 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 29 l =
      upColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 29 l =
      upColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 29 l =
      downColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 29 l =
      downColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) := by
  decide +kernel

/-- Source row 30 for the stated finite source data. -/
private theorem source_row_30 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 30 l =
      upColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 30 l =
      upColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 30 l =
      downColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 30 l =
      downColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) := by
  decide +kernel

/-- Source row 31 for the stated finite source data. -/
private theorem source_row_31 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 31 l =
      upColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 31 l =
      upColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 31 l =
      downColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 31 l =
      downColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) := by
  decide +kernel

/-- Source row 32 for the stated finite source data. -/
private theorem source_row_32 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 32 l =
      upColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 32 l =
      upColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 32 l =
      downColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 32 l =
      downColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) := by
  decide +kernel

/-- Source row 33 for the stated finite source data. -/
private theorem source_row_33 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 33 l =
      upColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 33 l =
      upColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 33 l =
      downColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 33 l =
      downColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) := by
  decide +kernel

/-- Source row 34 for the stated finite source data. -/
private theorem source_row_34 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 34 l =
      upColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 34 l =
      upColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 34 l =
      downColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 34 l =
      downColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) := by
  decide +kernel

/-- Source row 35 for the stated finite source data. -/
private theorem source_row_35 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 35 l =
      upColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 35 l =
      upColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 35 l =
      downColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 35 l =
      downColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) := by
  decide +kernel

/-- Source row 36 for the stated finite source data. -/
private theorem source_row_36 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 36 l =
      upColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 36 l =
      upColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 36 l =
      downColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 36 l =
      downColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) := by
  decide +kernel

/-- Source row 37 for the stated finite source data. -/
private theorem source_row_37 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 37 l =
      upColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 37 l =
      upColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 37 l =
      downColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 37 l =
      downColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) := by
  decide +kernel

/-- Source row 38 for the stated finite source data. -/
private theorem source_row_38 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 38 l =
      upColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 38 l =
      upColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 38 l =
      downColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 38 l =
      downColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) := by
  decide +kernel

/-- Source row 39 for the stated finite source data. -/
private theorem source_row_39 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 39 l =
      upColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 39 l =
      upColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 39 l =
      downColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 39 l =
      downColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) := by
  decide +kernel

/-- Source row 40 for the stated finite source data. -/
private theorem source_row_40 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 40 l =
      upColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 40 l =
      upColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 40 l =
      downColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 40 l =
      downColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) := by
  decide +kernel

/-- Source row 41 for the stated finite source data. -/
private theorem source_row_41 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 41 l =
      upColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 41 l =
      upColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 41 l =
      downColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 41 l =
      downColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) := by
  decide +kernel

/-- Source row 42 for the stated finite source data. -/
private theorem source_row_42 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 42 l =
      upColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 42 l =
      upColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 42 l =
      downColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 42 l =
      downColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) := by
  decide +kernel

/-- Source row 43 for the stated finite source data. -/
private theorem source_row_43 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 43 l =
      upColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 43 l =
      upColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 43 l =
      downColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 43 l =
      downColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) := by
  decide +kernel

/-- Source row 44 for the stated finite source data. -/
private theorem source_row_44 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 44 l =
      upColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 44 l =
      upColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 44 l =
      downColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 44 l =
      downColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) := by
  decide +kernel

/-- Source row 45 for the stated finite source data. -/
private theorem source_row_45 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 45 l =
      upColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 45 l =
      upColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 45 l =
      downColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 45 l =
      downColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) := by
  decide +kernel

/-- Source row 46 for the stated finite source data. -/
private theorem source_row_46 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 46 l =
      upColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 46 l =
      upColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 46 l =
      downColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 46 l =
      downColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) := by
  decide +kernel

/-- Source row 47 for the stated finite source data. -/
private theorem source_row_47 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 47 l =
      upColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 47 l =
      upColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 47 l =
      downColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 47 l =
      downColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) := by
  decide +kernel

/-- Source row 48 for the stated finite source data. -/
private theorem source_row_48 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 48 l =
      upColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 48 l =
      upColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 48 l =
      downColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 48 l =
      downColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) := by
  decide +kernel

/-- Source row 49 for the stated finite source data. -/
private theorem source_row_49 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 49 l =
      upColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 49 l =
      upColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 49 l =
      downColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 49 l =
      downColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) := by
  decide +kernel

/-- Source row 50 for the stated finite source data. -/
private theorem source_row_50 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 50 l =
      upColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 50 l =
      upColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 50 l =
      downColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 50 l =
      downColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) := by
  decide +kernel

/-- Source row 51 for the stated finite source data. -/
private theorem source_row_51 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 51 l =
      upColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 51 l =
      upColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 51 l =
      downColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 51 l =
      downColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) := by
  decide +kernel

/-- Source row 52 for the stated finite source data. -/
private theorem source_row_52 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 52 l =
      upColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 52 l =
      upColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 52 l =
      downColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 52 l =
      downColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) := by
  decide +kernel

/-- Source row 53 for the stated finite source data. -/
private theorem source_row_53 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 53 l =
      upColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 53 l =
      upColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 53 l =
      downColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 53 l =
      downColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) := by
  decide +kernel

/-- Source row 54 for the stated finite source data. -/
private theorem source_row_54 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 54 l =
      upColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 54 l =
      upColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 54 l =
      downColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 54 l =
      downColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) := by
  decide +kernel

/-- Source row 55 for the stated finite source data. -/
private theorem source_row_55 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 55 l =
      upColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 55 l =
      upColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 55 l =
      downColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 55 l =
      downColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) := by
  decide +kernel

/-- Source row 56 for the stated finite source data. -/
private theorem source_row_56 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 56 l =
      upColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 56 l =
      upColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 56 l =
      downColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 56 l =
      downColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) := by
  decide +kernel

/-- Source row 57 for the stated finite source data. -/
private theorem source_row_57 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 57 l =
      upColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 57 l =
      upColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 57 l =
      downColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 57 l =
      downColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) := by
  decide +kernel

/-- Source row 58 for the stated finite source data. -/
private theorem source_row_58 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 58 l =
      upColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 58 l =
      upColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 58 l =
      downColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 58 l =
      downColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) := by
  decide +kernel

/-- Source row 59 for the stated finite source data. -/
private theorem source_row_59 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 59 l =
      upColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 59 l =
      upColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 59 l =
      downColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 59 l =
      downColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) := by
  decide +kernel

/-- Source row 60 for the stated finite source data. -/
private theorem source_row_60 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 60 l =
      upColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 60 l =
      upColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 60 l =
      downColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 60 l =
      downColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) := by
  decide +kernel

/-- Source row 61 for the stated finite source data. -/
private theorem source_row_61 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 61 l =
      upColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 61 l =
      upColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 61 l =
      downColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 61 l =
      downColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) := by
  decide +kernel

/-- Source row 62 for the stated finite source data. -/
private theorem source_row_62 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 62 l =
      upColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 62 l =
      upColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 62 l =
      downColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 62 l =
      downColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) := by
  decide +kernel

/-- Source row 63 for the stated finite source data. -/
private theorem source_row_63 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 63 l =
      upColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 63 l =
      upColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 63 l =
      downColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 63 l =
      downColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) := by
  decide +kernel

/-- Source row 64 for the stated finite source data. -/
private theorem source_row_64 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 64 l =
      upColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 64 l =
      upColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 64 l =
      downColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 64 l =
      downColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) := by
  decide +kernel

/-- Source row 65 for the stated finite source data. -/
private theorem source_row_65 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 65 l =
      upColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 65 l =
      upColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 65 l =
      downColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 65 l =
      downColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) := by
  decide +kernel

/-- Source row 66 for the stated finite source data. -/
private theorem source_row_66 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 66 l =
      upColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 66 l =
      upColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 66 l =
      downColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 66 l =
      downColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) := by
  decide +kernel

/-- Source row 67 for the stated finite source data. -/
private theorem source_row_67 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 67 l =
      upColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 67 l =
      upColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 67 l =
      downColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 67 l =
      downColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) := by
  decide +kernel

/-- Source row 68 for the stated finite source data. -/
private theorem source_row_68 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 68 l =
      upColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 68 l =
      upColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 68 l =
      downColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 68 l =
      downColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) := by
  decide +kernel

/-- Source row 69 for the stated finite source data. -/
private theorem source_row_69 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 69 l =
      upColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 69 l =
      upColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 69 l =
      downColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 69 l =
      downColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) := by
  decide +kernel

/-- Source row 70 for the stated finite source data. -/
private theorem source_row_70 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 70 l =
      upColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 70 l =
      upColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 70 l =
      downColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 70 l =
      downColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) := by
  decide +kernel

/-- Source row 71 for the stated finite source data. -/
private theorem source_row_71 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 71 l =
      upColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 71 l =
      upColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 71 l =
      downColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 71 l =
      downColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) := by
  decide +kernel

/-- Source row 72 for the stated finite source data. -/
private theorem source_row_72 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 72 l =
      upColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 72 l =
      upColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 72 l =
      downColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 72 l =
      downColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) := by
  decide +kernel

/-- Source row 73 for the stated finite source data. -/
private theorem source_row_73 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 73 l =
      upColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 73 l =
      upColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 73 l =
      downColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 73 l =
      downColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) := by
  decide +kernel

/-- Source row 74 for the stated finite source data. -/
private theorem source_row_74 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 74 l =
      upColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 74 l =
      upColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 74 l =
      downColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 74 l =
      downColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) := by
  decide +kernel

/-- Source row 75 for the stated finite source data. -/
private theorem source_row_75 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 75 l =
      upColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 75 l =
      upColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 75 l =
      downColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 75 l =
      downColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) := by
  decide +kernel

/-- Source row 76 for the stated finite source data. -/
private theorem source_row_76 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 76 l =
      upColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 76 l =
      upColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 76 l =
      downColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 76 l =
      downColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) := by
  decide +kernel

/-- Source row 77 for the stated finite source data. -/
private theorem source_row_77 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 77 l =
      upColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 77 l =
      upColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 77 l =
      downColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 77 l =
      downColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) := by
  decide +kernel

/-- Source row 78 for the stated finite source data. -/
private theorem source_row_78 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 78 l =
      upColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 78 l =
      upColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 78 l =
      downColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 78 l =
      downColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) := by
  decide +kernel

/-- Source row 79 for the stated finite source data. -/
private theorem source_row_79 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 79 l =
      upColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 79 l =
      upColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 79 l =
      downColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 79 l =
      downColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) := by
  decide +kernel

/-- Source row 80 for the stated finite source data. -/
private theorem source_row_80 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 80 l =
      upColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 80 l =
      upColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 80 l =
      downColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 80 l =
      downColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) := by
  decide +kernel

/-- Source row 81 for the stated finite source data. -/
private theorem source_row_81 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 81 l =
      upColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 81 l =
      upColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 81 l =
      downColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 81 l =
      downColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) := by
  decide +kernel

/-- Source row 82 for the stated finite source data. -/
private theorem source_row_82 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 82 l =
      upColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 82 l =
      upColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 82 l =
      downColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 82 l =
      downColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) := by
  decide +kernel

/-- Source row 83 for the stated finite source data. -/
private theorem source_row_83 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 83 l =
      upColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 83 l =
      upColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 83 l =
      downColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 83 l =
      downColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) := by
  decide +kernel

/-- Source row 84 for the stated finite source data. -/
private theorem source_row_84 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 84 l =
      upColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 84 l =
      upColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 84 l =
      downColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 84 l =
      downColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) := by
  decide +kernel

/-- Source row 85 for the stated finite source data. -/
private theorem source_row_85 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 85 l =
      upColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 85 l =
      upColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 85 l =
      downColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 85 l =
      downColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) := by
  decide +kernel

/-- Source row 86 for the stated finite source data. -/
private theorem source_row_86 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 86 l =
      upColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 86 l =
      upColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 86 l =
      downColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 86 l =
      downColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) := by
  decide +kernel

/-- Source row 87 for the stated finite source data. -/
private theorem source_row_87 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 87 l =
      upColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 87 l =
      upColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 87 l =
      downColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 87 l =
      downColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) := by
  decide +kernel

/-- Source row 88 for the stated finite source data. -/
private theorem source_row_88 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 88 l =
      upColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 88 l =
      upColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 88 l =
      downColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 88 l =
      downColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) := by
  decide +kernel

/-- Source row 89 for the stated finite source data. -/
private theorem source_row_89 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 89 l =
      upColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 89 l =
      upColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 89 l =
      downColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 89 l =
      downColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) := by
  decide +kernel

/-- Source row 90 for the stated finite source data. -/
private theorem source_row_90 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 90 l =
      upColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 90 l =
      upColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 90 l =
      downColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 90 l =
      downColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) := by
  decide +kernel

/-- Source row 91 for the stated finite source data. -/
private theorem source_row_91 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 91 l =
      upColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 91 l =
      upColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 91 l =
      downColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 91 l =
      downColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) := by
  decide +kernel

/-- Source row 92 for the stated finite source data. -/
private theorem source_row_92 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 92 l =
      upColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 92 l =
      upColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 92 l =
      downColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 92 l =
      downColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) := by
  decide +kernel

/-- Source row 93 for the stated finite source data. -/
private theorem source_row_93 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 93 l =
      upColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 93 l =
      upColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 93 l =
      downColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 93 l =
      downColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) := by
  decide +kernel

/-- Source row 94 for the stated finite source data. -/
private theorem source_row_94 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 94 l =
      upColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 94 l =
      upColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 94 l =
      downColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 94 l =
      downColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) := by
  decide +kernel

/-- Source row 95 for the stated finite source data. -/
private theorem source_row_95 :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal 95 l =
      upColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag 95 l =
      upColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal 95 l =
      downColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag 95 l =
      downColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) := by
  decide +kernel

/-- Source parts match for the stated finite source data. -/
theorem source_parts_match (a : Fin 96) :
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpReal a l =
      upColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceUpImag a l =
      upColumnImag (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownReal a l =
      downColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelCollisionCoefficientTables.faceDownImag a l =
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
/-- Masked Literal Input combination for the stated finite source data. -/
theorem maskedLiteralInput_combination (σ : Perm) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast σ Y) :
    (∑ l, fullCoordinates c d Y l • maskedLiteralInput l) = Y := by
  have hflat : ∀ i j : Fin 4,
      (∑ l, fullCoordinates c d Y l • maskedLiteralInput l) i j =
        (fastInput *ᵥ fullCoordinates c d Y) (flatIndex i j) := by
    intro i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, fastInput, flatInput, maskedLiteralInput,
      Matrix.ite_apply, Matrix.zero_apply, literalInput,
      inputMatrixReal, inputMatrixImag, ThreeLevelGramCertificate.fromParts]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  ext i j : 2
  rw [hflat, fastInput_mulVec_fullCoordinates, flatInput_mulVec_apply,
    literalCombination_of_IsFast σ Y hY]

/-- Two Sided sum for the stated finite source data. -/
theorem twoSided_sum {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (A B : Operator 4) (X : ι → Operator 4) :
    (∑ l, z l • (A * X l - X l * B)) =
      A * (∑ l, z l • X l) - (∑ l, z l • X l) * B := by
  simp only [smul_sub, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, Finset.sum_sub_distrib]

/-- Two Sided masked Literal Input for the stated finite source data. -/
theorem twoSided_maskedLiteralInput (σ : Perm) (c d : ℂ)
    (Y : Operator 4) (hY : IsFast σ Y) (A B : Operator 4) :
    (∑ l, fullCoordinates c d Y l •
      (A * maskedLiteralInput l - maskedLiteralInput l * B)) =
      A * Y - Y * B := by
  rw [twoSided_sum, maskedLiteralInput_combination σ c d Y hY]


/-- Two Sided stack mul Vec for the stated finite source data. -/
theorem twoSided_stack_mulVec (S : Matrix (Fin 96) (Fin 15) ℂ)
    (A B : Fin 6 → Operator 4)
    (hS : ∀ a l, S a l =
      (A (sourceIndex a) * maskedLiteralInput l -
        maskedLiteralInput l * B (sourceIndex a)) (rowIndex a) (columnIndex a))
    (σ : Perm) (c d : ℂ) (Y : Operator 4) (hY : IsFast σ Y) (a : Fin 96) :
    (S *ᵥ fullCoordinates c d Y) a =
      (A (sourceIndex a) * Y - Y * B (sourceIndex a))
        (rowIndex a) (columnIndex a) := by
  rw [← twoSided_maskedLiteralInput σ c d Y hY
    (A (sourceIndex a)) (B (sourceIndex a))]
  simp only [Matrix.mulVec, dotProduct, hS, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Two Sided edge stack mul Vec for the stated finite source data. -/
theorem twoSided_edge_stack_mulVec (S : Matrix (Fin 96) (Fin 15) ℂ)
    (A B E : Fin 6 → Operator 4)
    (hS : ∀ a l, S a l =
      ((if l = 0 then E (sourceIndex a) else 0) +
      (A (sourceIndex a) * maskedLiteralInput l -
        maskedLiteralInput l * B (sourceIndex a))) (rowIndex a) (columnIndex a))
    (σ : Perm) (c d : ℂ) (Y : Operator 4) (hY : IsFast σ Y) (a : Fin 96) :
    (S *ᵥ fullCoordinates c d Y) a =
      (c • E (sourceIndex a) +
      (A (sourceIndex a) * Y - Y * B (sourceIndex a)))
        (rowIndex a) (columnIndex a) := by
  rw [← twoSided_maskedLiteralInput σ c d Y hY
    (A (sourceIndex a)) (B (sourceIndex a))]
  simp only [Matrix.mulVec, dotProduct, hS, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [Matrix.ite_apply, Matrix.zero_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, fullCoordinates_zero]
    ring
  · apply Finset.sum_congr rfl
    intro l _
    ring

/-- Face Up apply for the stated finite source data. -/
theorem faceUp_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelCollisionCoefficientTables.faceUp a l =
      (((pZero+pOne) * ThreeLevelWordDual.source (sourceIndex a) * pTwo) *
        maskedLiteralInput l - maskedLiteralInput l *
          (pTwo * ThreeLevelWordDual.source (sourceIndex a) * (pZero+pOne)))
            (rowIndex a) (columnIndex a) := by
  rw [← upColumn_parts]
  simp only [ThreeLevelCollisionCoefficientTables.faceUp, fromParts,
    (source_parts_match a).1 l, (source_parts_match a).2.1 l]

/-- Face Down apply for the stated finite source data. -/
theorem faceDown_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelCollisionCoefficientTables.faceDown a l =
      ((if l = 0 then edge (Equiv.refl (Fin 3))
          (ThreeLevelWordDual.source (sourceIndex a)) 0 2 else 0) +
        ((pTwo * ThreeLevelWordDual.source (sourceIndex a) * (pZero+pOne)) *
          maskedLiteralInput l - maskedLiteralInput l *
            ((pZero+pOne) * ThreeLevelWordDual.source (sourceIndex a) * pTwo)))
              (rowIndex a) (columnIndex a) := by
  rw [← downColumn_parts]
  simp only [ThreeLevelCollisionCoefficientTables.faceDown, fromParts,
    (source_parts_match a).2.2.1 l, (source_parts_match a).2.2.2 l]

/-- Face Up mul Vec for the stated finite source data. -/
theorem faceUp_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelCollisionCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      (((pZero+pOne) * ThreeLevelWordDual.source (sourceIndex a) * pTwo) * Y -
        Y * (pTwo * ThreeLevelWordDual.source (sourceIndex a) * (pZero+pOne)))
          (rowIndex a) (columnIndex a) :=
  twoSided_stack_mulVec ThreeLevelCollisionCoefficientTables.faceUp
    (fun k => (pZero+pOne) * ThreeLevelWordDual.source k * pTwo)
    (fun k => pTwo * ThreeLevelWordDual.source k * (pZero+pOne))
    faceUp_apply (Equiv.refl (Fin 3)) c d Y hY a

/-- Face Down mul Vec for the stated finite source data. -/
theorem faceDown_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) (a : Fin 96) :
    (ThreeLevelCollisionCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      (c • edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source (sourceIndex a)) 0 2 +
        ((pTwo * ThreeLevelWordDual.source (sourceIndex a) * (pZero+pOne)) * Y -
          Y * ((pZero+pOne) * ThreeLevelWordDual.source (sourceIndex a) * pTwo)))
            (rowIndex a) (columnIndex a) :=
  twoSided_edge_stack_mulVec ThreeLevelCollisionCoefficientTables.faceDown
    (fun k => pTwo * ThreeLevelWordDual.source k * (pZero+pOne))
    (fun k => (pZero+pOne) * ThreeLevelWordDual.source k * pTwo)
    (fun k => edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 2)
    faceDown_apply (Equiv.refl (Fin 3)) c d Y hY a


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionSourceTables
