/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowCoefficientData
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrderCoordinates
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionFace

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Actual six-source tables for the order120 low collision face

All three polynomial source blocks are checked directly against the actual
six Pauli sources. The 96 row checks retain both population columns and all
13 nonorthonormal fast coordinates. No identity-order endpoint coordinate
identification is used.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowSourceTables
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelWordDual
open ThreeLevelGramCertificateCorner ThreeLevelCornerFastChart ThreeLevelCoordinateMetric
open ThreeLevelGramCertificate ThreeLevelCollisionSourceTables ThreeLevelOrder120
open ThreeLevelOrder201 (twoSided_two_edges_stack_mulVec)
open ThreeLevelCollisionFace

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
noncomputable section

def lowReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    0, 1/9, 2/9, 0;
    0, 2/9, 4/9, 0;
    0, 0, 0, 4/9]

def lowImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, (-2/9);
    0, 0, 0, (-4/9);
    0, 2/9, 4/9, 0]

def highReal : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 8/9, (-2/9), 0;
    0, (-2/9), 5/9, 0;
    0, 0, 0, 5/9]

def highImag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 4/9;
    0, (-2/9), (-4/9), 0]

def projector0Real : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

def projector0Imag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

def projector1Real : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 1/9, 2/9, 0;
    0, 2/9, 4/9, 0;
    0, 0, 0, 4/9]

def projector1Imag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, (-2/9);
    0, 0, 0, (-4/9);
    0, 2/9, 4/9, 0]

def projector2Real : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 8/9, (-2/9), 0;
    0, (-2/9), 5/9, 0;
    0, 0, 0, 5/9]

def projector2Imag : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 4/9;
    0, (-2/9), (-4/9), 0]

def upLeftReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
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

def upLeftImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
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

def upRightReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
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

def upRightImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
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

def baseDiagReal : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 2/9, 4/9, 0;
    2/9, 0, 0, 4/9;
    4/9, 0, 0, (-2/9);
    0, 4/9, (-2/9), 0],
    !![0, 0, 0, (-4/9);
    0, (-28/81), (-20/81), 0;
    0, (-20/81), 32/81, 0;
    (-4/9), 0, 0, (-4/81)],
    !![1, 0, 0, 0;
    0, 49/81, (-28/81), 0;
    0, (-28/81), (-65/81), 0;
    0, 0, 0, (-65/81)],
    !![0, 1/9, 2/9, 0;
    1/9, 0, 0, (-2/9);
    2/9, 0, 0, 1/9;
    0, (-2/9), 1/9, 0],
    !![0, 0, 0, (-2/9);
    0, 16/81, 14/81, 0;
    0, 14/81, (-8/81), 0;
    (-2/9), 0, 0, (-8/81)],
    !![1, 0, 0, 0;
    0, (-65/81), (-4/81), 0;
    0, (-4/81), 1/81, 0;
    0, 0, 0, (-17/81)]]

def baseDiagImag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, (-4/9);
    0, 0, (-4/9), 0;
    0, 4/9, 0, 0;
    4/9, 0, 0, 0],
    !![0, (-2/9), (-4/9), 0;
    2/9, 0, 0, (-52/81);
    4/9, 0, 0, (-14/81);
    0, 52/81, 14/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 28/81;
    0, 0, 0, (-16/81);
    0, (-28/81), 16/81, 0],
    !![0, 0, 0, (-2/9);
    0, 0, 2/9, 0;
    0, (-2/9), 0, 0;
    2/9, 0, 0, 0],
    !![0, (-1/9), (-2/9), 0;
    1/9, 0, 0, (-14/81);
    2/9, 0, 0, (-73/81);
    0, 14/81, 73/81, 0],
    !![0, 0, 0, 0;
    0, 0, 0, (-32/81);
    0, 0, 0, 8/81;
    0, 32/81, (-8/81), 0]]

def edge01Real : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 2/9, 4/9, 0;
    (-2/9), 0, 0, 0;
    (-4/9), 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, (-4/9);
    0, 0, 0, 0;
    0, 0, 0, 0;
    4/9, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 1/9, 2/9, 0;
    (-1/9), 0, 0, 0;
    (-2/9), 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, (-2/9);
    0, 0, 0, 0;
    0, 0, 0, 0;
    2/9, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]]

def edge01Imag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, (-4/9);
    0, 0, 0, 0;
    0, 0, 0, 0;
    (-4/9), 0, 0, 0],
    !![0, (-2/9), (-4/9), 0;
    (-2/9), 0, 0, 0;
    (-4/9), 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, (-2/9);
    0, 0, 0, 0;
    0, 0, 0, 0;
    (-2/9), 0, 0, 0],
    !![0, (-1/9), (-2/9), 0;
    (-1/9), 0, 0, 0;
    (-2/9), 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]]

def edge02Real : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, (-2/9), 5/9, 0;
    2/9, 0, 0, 0;
    (-5/9), 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 4/9;
    0, 0, 0, 0;
    0, 0, 0, 0;
    (-4/9), 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 8/9, (-2/9), 0;
    (-8/9), 0, 0, 0;
    2/9, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 2/9;
    0, 0, 0, 0;
    0, 0, 0, 0;
    (-2/9), 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]]

def edge02Imag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 4/9;
    0, 0, 0, 0;
    0, 0, 0, 0;
    4/9, 0, 0, 0],
    !![0, 2/9, (-5/9), 0;
    2/9, 0, 0, 0;
    (-5/9), 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 2/9;
    0, 0, 0, 0;
    0, 0, 0, 0;
    2/9, 0, 0, 0],
    !![0, (-8/9), 2/9, 0;
    (-8/9), 0, 0, 0;
    2/9, 0, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]]

def edge12Real : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, 0, 0, (-1/3);
    0, 0, 0, 2/9;
    0, 1/3, (-2/9), 0],
    !![0, 0, 0, 0;
    0, 0, (-4/9), 0;
    0, 4/9, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, (-4/9), 0;
    0, 4/9, 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 2/9;
    0, 0, 0, 0;
    0, (-2/9), 0, 0],
    !![0, 0, 0, 0;
    0, 0, 2/9, 0;
    0, (-2/9), 0, 0;
    0, 0, 0, 0],
    !![0, 0, 0, 0;
    0, 0, 4/9, 0;
    0, (-4/9), 0, 0;
    0, 0, 0, 0]]

def edge12Imag : Fin 6 → Matrix (Fin 4) (Fin 4) ℚ :=
  ![!![0, 0, 0, 0;
    0, (-4/9), (-4/9), 0;
    0, (-4/9), 0, 0;
    0, 0, 0, 4/9],
    !![0, 0, 0, 0;
    0, 0, 0, 1/3;
    0, 0, 0, (-2/9);
    0, 1/3, (-2/9), 0],
    !![0, 0, 0, 0;
    0, 0, 0, 4/9;
    0, 0, 0, 0;
    0, 4/9, 0, 0],
    !![0, 0, 0, 0;
    0, 0, (-2/9), 0;
    0, (-2/9), (-8/9), 0;
    0, 0, 0, 8/9],
    !![0, 0, 0, 0;
    0, 0, 0, (-2/9);
    0, 0, 0, 0;
    0, (-2/9), 0, 0],
    !![0, 0, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 8/9;
    0, 0, 8/9, 0]]

/-- Low parts for the stated finite source data. -/
theorem low_parts : fromParts lowReal lowImag = mergedLow order120 := by
  simp only [mergedLow, spectralProjectors_order120_zero, spectralProjectors_order120_one]
  rw [pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, lowReal, lowImag, pOne, Matrix.one_apply] <;> ring

/-- High parts for the stated finite source data. -/
theorem high_parts : fromParts highReal highImag = mergedHigh order120 := by
  simp only [mergedHigh, spectralProjectors_order120_two]
  rw [pZero, pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, highReal, highImag, pOne, Matrix.one_apply] <;> ring

/-- Projector0 parts for the stated finite source data. -/
theorem projector0_parts : fromParts projector0Real projector0Imag = spectralProjectors order120 0 := by
  simp only [spectralProjectors_order120_zero]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, projector0Real, projector0Imag, pOne, Matrix.one_apply]

/-- Projector1 parts for the stated finite source data. -/
theorem projector1_parts : fromParts projector1Real projector1Imag = spectralProjectors order120 1 := by
  simp only [spectralProjectors_order120_one]
  rw [pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, projector1Real, projector1Imag, pOne, Matrix.one_apply] <;> ring

/-- Projector2 parts for the stated finite source data. -/
theorem projector2_parts : fromParts projector2Real projector2Imag = spectralProjectors order120 2 := by
  simp only [spectralProjectors_order120_two]
  rw [pZero, pTwo_entries]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [fromParts, projector2Real, projector2Imag, pOne, Matrix.one_apply] <;> ring

/-- Up blocks match for the stated finite source data. -/
theorem up_blocks_match :
    (∀ k, upLeftReal k = blockReal lowReal lowImag highReal highImag k) ∧
    (∀ k, upLeftImag k = blockImag lowReal lowImag highReal highImag k) ∧
    (∀ k, upRightReal k = blockReal highReal highImag lowReal lowImag k) ∧
    (∀ k, upRightImag k = blockImag highReal highImag lowReal lowImag k) := by
  decide +kernel

/-- Base blocks match for the stated finite source data. -/
theorem base_blocks_match :
    (∀ k, baseDiagReal k = blockReal lowReal lowImag lowReal lowImag k +
      blockReal highReal highImag highReal highImag k) ∧
    (∀ k, baseDiagImag k = blockImag lowReal lowImag lowReal lowImag k +
      blockImag highReal highImag highReal highImag k) := by
  decide +kernel

/-- Up Left parts for the stated finite source data. -/
theorem upLeft_parts (k : Fin 6) :
    fromParts (upLeftReal k) (upLeftImag k) =
      mergedLow order120 * ThreeLevelWordDual.source k * mergedHigh order120 := by
  rw [up_blocks_match.1, up_blocks_match.2.1, block_parts, low_parts, high_parts]

/-- Up Right parts for the stated finite source data. -/
theorem upRight_parts (k : Fin 6) :
    fromParts (upRightReal k) (upRightImag k) =
      mergedHigh order120 * ThreeLevelWordDual.source k * mergedLow order120 := by
  rw [up_blocks_match.2.2.1, up_blocks_match.2.2.2, block_parts, low_parts, high_parts]

/-- Base Diag parts for the stated finite source data. -/
theorem baseDiag_parts (k : Fin 6) :
    fromParts (baseDiagReal k) (baseDiagImag k) =
      faceDiagonal order120 (ThreeLevelWordDual.source k) := by
  rw [base_blocks_match.1, base_blocks_match.2, fromParts_add, block_parts,
    block_parts, low_parts, high_parts]
  rfl

/-- Edge01 blocks match for the stated finite source data. -/
theorem edge01_blocks_match :
    (∀ k, edge01Real k =
      blockReal projector0Real projector0Imag projector1Real projector1Imag k -
      blockReal projector1Real projector1Imag projector0Real projector0Imag k) ∧
    (∀ k, edge01Imag k =
      blockImag projector0Real projector0Imag projector1Real projector1Imag k -
      blockImag projector1Real projector1Imag projector0Real projector0Imag k) := by
  decide +kernel

/-- Edge01 parts for the stated finite source data. -/
theorem edge01_parts (k : Fin 6) :
    fromParts (edge01Real k) (edge01Imag k) =
      edge order120 (ThreeLevelWordDual.source k) 0 1 := by
  rw [edge01_blocks_match.1, edge01_blocks_match.2, fromParts_sub,
    block_parts, block_parts, projector0_parts, projector1_parts]
  rfl

/-- Edge02 blocks match for the stated finite source data. -/
theorem edge02_blocks_match :
    (∀ k, edge02Real k =
      blockReal projector0Real projector0Imag projector2Real projector2Imag k -
      blockReal projector2Real projector2Imag projector0Real projector0Imag k) ∧
    (∀ k, edge02Imag k =
      blockImag projector0Real projector0Imag projector2Real projector2Imag k -
      blockImag projector2Real projector2Imag projector0Real projector0Imag k) := by
  decide +kernel

/-- Edge02 parts for the stated finite source data. -/
theorem edge02_parts (k : Fin 6) :
    fromParts (edge02Real k) (edge02Imag k) =
      edge order120 (ThreeLevelWordDual.source k) 0 2 := by
  rw [edge02_blocks_match.1, edge02_blocks_match.2, fromParts_sub,
    block_parts, block_parts, projector0_parts, projector2_parts]
  rfl

/-- Edge12 blocks match for the stated finite source data. -/
theorem edge12_blocks_match :
    (∀ k, edge12Real k =
      blockReal projector1Real projector1Imag projector2Real projector2Imag k -
      blockReal projector2Real projector2Imag projector1Real projector1Imag k) ∧
    (∀ k, edge12Imag k =
      blockImag projector1Real projector1Imag projector2Real projector2Imag k -
      blockImag projector2Real projector2Imag projector1Real projector1Imag k) := by
  decide +kernel

/-- Edge12 parts for the stated finite source data. -/
theorem edge12_parts (k : Fin 6) :
    fromParts (edge12Real k) (edge12Imag k) =
      edge order120 (ThreeLevelWordDual.source k) 1 2 := by
  rw [edge12_blocks_match.1, edge12_blocks_match.2, fromParts_sub,
    block_parts, block_parts, projector1_parts, projector2_parts]
  rfl

def baseEdgeZeroReal (k : Fin 6) : Matrix (Fin 4) (Fin 4) ℚ :=
  edge01Real k

def baseEdgeZeroImag (k : Fin 6) : Matrix (Fin 4) (Fin 4) ℚ :=
  edge01Imag k

/-- Base Edge Zero parts for the stated finite source data. -/
theorem baseEdgeZero_parts (k : Fin 6) :
    fromParts (baseEdgeZeroReal k) (baseEdgeZeroImag k) =
      edge order120 (ThreeLevelWordDual.source k) 0 1 := by
  exact edge01_parts k

def baseEdgeOneReal (k : Fin 6) : Matrix (Fin 4) (Fin 4) ℚ :=
  edge12Real k + edge02Real k

def baseEdgeOneImag (k : Fin 6) : Matrix (Fin 4) (Fin 4) ℚ :=
  edge12Imag k + edge02Imag k

/-- Base Edge One parts for the stated finite source data. -/
theorem baseEdgeOne_parts (k : Fin 6) :
    fromParts (baseEdgeOneReal k) (baseEdgeOneImag k) =
      edge order120 (ThreeLevelWordDual.source k) 1 2 + edge order120 (ThreeLevelWordDual.source k) 0 2 := by
  rw [baseEdgeOneReal, baseEdgeOneImag, fromParts_add, edge12_parts, edge02_parts]

/-- Parts ite zero for the stated finite source data. -/
private theorem parts_ite_zero (p : Prop) [Decidable p]
    (R I : Matrix (Fin 4) (Fin 4) ℚ) :
    fromParts (if p then R else 0) (if p then I else 0) =
      if p then fromParts R I else 0 := by
  split_ifs
  · rfl
  · ext i j
    simp [fromParts]

def baseColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 0 then baseEdgeZeroReal k else 0) +
    (if l = 1 then baseEdgeOneReal k else 0) +
    twoSidedReal (baseDiagReal k) (baseDiagImag k) (baseDiagReal k) (baseDiagImag k)
      (maskedInputReal l) (maskedInputImag l)

def baseColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 0 then baseEdgeZeroImag k else 0) +
    (if l = 1 then baseEdgeOneImag k else 0) +
    twoSidedImag (baseDiagReal k) (baseDiagImag k) (baseDiagReal k) (baseDiagImag k)
      (maskedInputReal l) (maskedInputImag l)

/-- Base Column parts for the stated finite source data. -/
theorem baseColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (baseColumnReal k l) (baseColumnImag k l) =
      (if l = 0 then edge order120 (ThreeLevelWordDual.source k) 0 1 else 0) +
      (if l = 1 then edge order120 (ThreeLevelWordDual.source k) 1 2 + edge order120 (ThreeLevelWordDual.source k) 0 2 else 0) +
      ((faceDiagonal order120 (ThreeLevelWordDual.source k)) * maskedLiteralInput l -
        maskedLiteralInput l * (faceDiagonal order120 (ThreeLevelWordDual.source k))) := by
  rw [baseColumnReal, baseColumnImag, fromParts_add, fromParts_add, parts_ite_zero, parts_ite_zero, baseEdgeZero_parts, baseEdgeOne_parts, twoSided_parts, baseDiag_parts, masked_parts]

def upColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  twoSidedReal (upLeftReal k) (upLeftImag k) (upRightReal k) (upRightImag k)
      (maskedInputReal l) (maskedInputImag l)

def upColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  twoSidedImag (upLeftReal k) (upLeftImag k) (upRightReal k) (upRightImag k)
      (maskedInputReal l) (maskedInputImag l)

/-- Up Column parts for the stated finite source data. -/
theorem upColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (upColumnReal k l) (upColumnImag k l) =
      ((mergedLow order120 * ThreeLevelWordDual.source k * mergedHigh order120) * maskedLiteralInput l -
        maskedLiteralInput l * (mergedHigh order120 * ThreeLevelWordDual.source k * mergedLow order120)) := by
  rw [upColumnReal, upColumnImag, twoSided_parts, upLeft_parts, upRight_parts, masked_parts]

def downColumnReal (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 0 then edge02Real k else 0) +
    twoSidedReal (upRightReal k) (upRightImag k) (upLeftReal k) (upLeftImag k)
      (maskedInputReal l) (maskedInputImag l)

def downColumnImag (k : Fin 6) (l : Fin 15) : Matrix (Fin 4) (Fin 4) ℚ :=
  (if l = 0 then edge02Imag k else 0) +
    twoSidedImag (upRightReal k) (upRightImag k) (upLeftReal k) (upLeftImag k)
      (maskedInputReal l) (maskedInputImag l)

/-- Down Column parts for the stated finite source data. -/
theorem downColumn_parts (k : Fin 6) (l : Fin 15) :
    fromParts (downColumnReal k l) (downColumnImag k l) =
      (if l = 0 then edge order120 (ThreeLevelWordDual.source k) 0 2 else 0) +
      ((mergedHigh order120 * ThreeLevelWordDual.source k * mergedLow order120) * maskedLiteralInput l -
        maskedLiteralInput l * (mergedLow order120 * ThreeLevelWordDual.source k * mergedHigh order120)) := by
  rw [downColumnReal, downColumnImag, fromParts_add, parts_ite_zero, edge02_parts, twoSided_parts, upRight_parts, upLeft_parts, masked_parts]

/-- Source row 0 for the stated finite source data. -/
private theorem source_row_0 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 0 l =
      baseColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 0 l =
      baseColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 0 l =
      upColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 0 l =
      upColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 0 l =
      downColumnReal (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 0 l =
      downColumnImag (sourceIndex 0) l (rowIndex 0) (columnIndex 0)) := by
  decide +kernel


/-- Source row 1 for the stated finite source data. -/
private theorem source_row_1 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 1 l =
      baseColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 1 l =
      baseColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 1 l =
      upColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 1 l =
      upColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 1 l =
      downColumnReal (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 1 l =
      downColumnImag (sourceIndex 1) l (rowIndex 1) (columnIndex 1)) := by
  decide +kernel


/-- Source row 2 for the stated finite source data. -/
private theorem source_row_2 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 2 l =
      baseColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 2 l =
      baseColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 2 l =
      upColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 2 l =
      upColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 2 l =
      downColumnReal (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 2 l =
      downColumnImag (sourceIndex 2) l (rowIndex 2) (columnIndex 2)) := by
  decide +kernel


/-- Source row 3 for the stated finite source data. -/
private theorem source_row_3 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 3 l =
      baseColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 3 l =
      baseColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 3 l =
      upColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 3 l =
      upColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 3 l =
      downColumnReal (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 3 l =
      downColumnImag (sourceIndex 3) l (rowIndex 3) (columnIndex 3)) := by
  decide +kernel


/-- Source row 4 for the stated finite source data. -/
private theorem source_row_4 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 4 l =
      baseColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 4 l =
      baseColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 4 l =
      upColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 4 l =
      upColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 4 l =
      downColumnReal (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 4 l =
      downColumnImag (sourceIndex 4) l (rowIndex 4) (columnIndex 4)) := by
  decide +kernel


/-- Source row 5 for the stated finite source data. -/
private theorem source_row_5 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 5 l =
      baseColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 5 l =
      baseColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 5 l =
      upColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 5 l =
      upColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 5 l =
      downColumnReal (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 5 l =
      downColumnImag (sourceIndex 5) l (rowIndex 5) (columnIndex 5)) := by
  decide +kernel


/-- Source row 6 for the stated finite source data. -/
private theorem source_row_6 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 6 l =
      baseColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 6 l =
      baseColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 6 l =
      upColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 6 l =
      upColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 6 l =
      downColumnReal (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 6 l =
      downColumnImag (sourceIndex 6) l (rowIndex 6) (columnIndex 6)) := by
  decide +kernel


/-- Source row 7 for the stated finite source data. -/
private theorem source_row_7 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 7 l =
      baseColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 7 l =
      baseColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 7 l =
      upColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 7 l =
      upColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 7 l =
      downColumnReal (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 7 l =
      downColumnImag (sourceIndex 7) l (rowIndex 7) (columnIndex 7)) := by
  decide +kernel


/-- Source row 8 for the stated finite source data. -/
private theorem source_row_8 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 8 l =
      baseColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 8 l =
      baseColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 8 l =
      upColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 8 l =
      upColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 8 l =
      downColumnReal (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 8 l =
      downColumnImag (sourceIndex 8) l (rowIndex 8) (columnIndex 8)) := by
  decide +kernel


/-- Source row 9 for the stated finite source data. -/
private theorem source_row_9 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 9 l =
      baseColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 9 l =
      baseColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 9 l =
      upColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 9 l =
      upColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 9 l =
      downColumnReal (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 9 l =
      downColumnImag (sourceIndex 9) l (rowIndex 9) (columnIndex 9)) := by
  decide +kernel


/-- Source row 10 for the stated finite source data. -/
private theorem source_row_10 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 10 l =
      baseColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 10 l =
      baseColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 10 l =
      upColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 10 l =
      upColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 10 l =
      downColumnReal (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 10 l =
      downColumnImag (sourceIndex 10) l (rowIndex 10) (columnIndex 10)) := by
  decide +kernel


/-- Source row 11 for the stated finite source data. -/
private theorem source_row_11 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 11 l =
      baseColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 11 l =
      baseColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 11 l =
      upColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 11 l =
      upColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 11 l =
      downColumnReal (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 11 l =
      downColumnImag (sourceIndex 11) l (rowIndex 11) (columnIndex 11)) := by
  decide +kernel


/-- Source row 12 for the stated finite source data. -/
private theorem source_row_12 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 12 l =
      baseColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 12 l =
      baseColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 12 l =
      upColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 12 l =
      upColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 12 l =
      downColumnReal (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 12 l =
      downColumnImag (sourceIndex 12) l (rowIndex 12) (columnIndex 12)) := by
  decide +kernel


/-- Source row 13 for the stated finite source data. -/
private theorem source_row_13 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 13 l =
      baseColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 13 l =
      baseColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 13 l =
      upColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 13 l =
      upColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 13 l =
      downColumnReal (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 13 l =
      downColumnImag (sourceIndex 13) l (rowIndex 13) (columnIndex 13)) := by
  decide +kernel


/-- Source row 14 for the stated finite source data. -/
private theorem source_row_14 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 14 l =
      baseColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 14 l =
      baseColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 14 l =
      upColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 14 l =
      upColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 14 l =
      downColumnReal (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 14 l =
      downColumnImag (sourceIndex 14) l (rowIndex 14) (columnIndex 14)) := by
  decide +kernel


/-- Source row 15 for the stated finite source data. -/
private theorem source_row_15 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 15 l =
      baseColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 15 l =
      baseColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 15 l =
      upColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 15 l =
      upColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 15 l =
      downColumnReal (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 15 l =
      downColumnImag (sourceIndex 15) l (rowIndex 15) (columnIndex 15)) := by
  decide +kernel


/-- Source row 16 for the stated finite source data. -/
private theorem source_row_16 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 16 l =
      baseColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 16 l =
      baseColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 16 l =
      upColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 16 l =
      upColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 16 l =
      downColumnReal (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 16 l =
      downColumnImag (sourceIndex 16) l (rowIndex 16) (columnIndex 16)) := by
  decide +kernel


/-- Source row 17 for the stated finite source data. -/
private theorem source_row_17 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 17 l =
      baseColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 17 l =
      baseColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 17 l =
      upColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 17 l =
      upColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 17 l =
      downColumnReal (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 17 l =
      downColumnImag (sourceIndex 17) l (rowIndex 17) (columnIndex 17)) := by
  decide +kernel


/-- Source row 18 for the stated finite source data. -/
private theorem source_row_18 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 18 l =
      baseColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 18 l =
      baseColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 18 l =
      upColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 18 l =
      upColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 18 l =
      downColumnReal (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 18 l =
      downColumnImag (sourceIndex 18) l (rowIndex 18) (columnIndex 18)) := by
  decide +kernel


/-- Source row 19 for the stated finite source data. -/
private theorem source_row_19 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 19 l =
      baseColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 19 l =
      baseColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 19 l =
      upColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 19 l =
      upColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 19 l =
      downColumnReal (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 19 l =
      downColumnImag (sourceIndex 19) l (rowIndex 19) (columnIndex 19)) := by
  decide +kernel


/-- Source row 20 for the stated finite source data. -/
private theorem source_row_20 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 20 l =
      baseColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 20 l =
      baseColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 20 l =
      upColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 20 l =
      upColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 20 l =
      downColumnReal (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 20 l =
      downColumnImag (sourceIndex 20) l (rowIndex 20) (columnIndex 20)) := by
  decide +kernel


/-- Source row 21 for the stated finite source data. -/
private theorem source_row_21 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 21 l =
      baseColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 21 l =
      baseColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 21 l =
      upColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 21 l =
      upColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 21 l =
      downColumnReal (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 21 l =
      downColumnImag (sourceIndex 21) l (rowIndex 21) (columnIndex 21)) := by
  decide +kernel


/-- Source row 22 for the stated finite source data. -/
private theorem source_row_22 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 22 l =
      baseColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 22 l =
      baseColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 22 l =
      upColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 22 l =
      upColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 22 l =
      downColumnReal (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 22 l =
      downColumnImag (sourceIndex 22) l (rowIndex 22) (columnIndex 22)) := by
  decide +kernel


/-- Source row 23 for the stated finite source data. -/
private theorem source_row_23 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 23 l =
      baseColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 23 l =
      baseColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 23 l =
      upColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 23 l =
      upColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 23 l =
      downColumnReal (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 23 l =
      downColumnImag (sourceIndex 23) l (rowIndex 23) (columnIndex 23)) := by
  decide +kernel


/-- Source row 24 for the stated finite source data. -/
private theorem source_row_24 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 24 l =
      baseColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 24 l =
      baseColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 24 l =
      upColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 24 l =
      upColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 24 l =
      downColumnReal (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 24 l =
      downColumnImag (sourceIndex 24) l (rowIndex 24) (columnIndex 24)) := by
  decide +kernel


/-- Source row 25 for the stated finite source data. -/
private theorem source_row_25 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 25 l =
      baseColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 25 l =
      baseColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 25 l =
      upColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 25 l =
      upColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 25 l =
      downColumnReal (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 25 l =
      downColumnImag (sourceIndex 25) l (rowIndex 25) (columnIndex 25)) := by
  decide +kernel


/-- Source row 26 for the stated finite source data. -/
private theorem source_row_26 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 26 l =
      baseColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 26 l =
      baseColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 26 l =
      upColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 26 l =
      upColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 26 l =
      downColumnReal (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 26 l =
      downColumnImag (sourceIndex 26) l (rowIndex 26) (columnIndex 26)) := by
  decide +kernel


/-- Source row 27 for the stated finite source data. -/
private theorem source_row_27 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 27 l =
      baseColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 27 l =
      baseColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 27 l =
      upColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 27 l =
      upColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 27 l =
      downColumnReal (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 27 l =
      downColumnImag (sourceIndex 27) l (rowIndex 27) (columnIndex 27)) := by
  decide +kernel


/-- Source row 28 for the stated finite source data. -/
private theorem source_row_28 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 28 l =
      baseColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 28 l =
      baseColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 28 l =
      upColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 28 l =
      upColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 28 l =
      downColumnReal (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 28 l =
      downColumnImag (sourceIndex 28) l (rowIndex 28) (columnIndex 28)) := by
  decide +kernel


/-- Source row 29 for the stated finite source data. -/
private theorem source_row_29 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 29 l =
      baseColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 29 l =
      baseColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 29 l =
      upColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 29 l =
      upColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 29 l =
      downColumnReal (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 29 l =
      downColumnImag (sourceIndex 29) l (rowIndex 29) (columnIndex 29)) := by
  decide +kernel


/-- Source row 30 for the stated finite source data. -/
private theorem source_row_30 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 30 l =
      baseColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 30 l =
      baseColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 30 l =
      upColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 30 l =
      upColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 30 l =
      downColumnReal (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 30 l =
      downColumnImag (sourceIndex 30) l (rowIndex 30) (columnIndex 30)) := by
  decide +kernel


/-- Source row 31 for the stated finite source data. -/
private theorem source_row_31 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 31 l =
      baseColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 31 l =
      baseColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 31 l =
      upColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 31 l =
      upColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 31 l =
      downColumnReal (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 31 l =
      downColumnImag (sourceIndex 31) l (rowIndex 31) (columnIndex 31)) := by
  decide +kernel


/-- Source row 32 for the stated finite source data. -/
private theorem source_row_32 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 32 l =
      baseColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 32 l =
      baseColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 32 l =
      upColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 32 l =
      upColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 32 l =
      downColumnReal (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 32 l =
      downColumnImag (sourceIndex 32) l (rowIndex 32) (columnIndex 32)) := by
  decide +kernel


/-- Source row 33 for the stated finite source data. -/
private theorem source_row_33 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 33 l =
      baseColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 33 l =
      baseColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 33 l =
      upColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 33 l =
      upColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 33 l =
      downColumnReal (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 33 l =
      downColumnImag (sourceIndex 33) l (rowIndex 33) (columnIndex 33)) := by
  decide +kernel


/-- Source row 34 for the stated finite source data. -/
private theorem source_row_34 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 34 l =
      baseColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 34 l =
      baseColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 34 l =
      upColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 34 l =
      upColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 34 l =
      downColumnReal (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 34 l =
      downColumnImag (sourceIndex 34) l (rowIndex 34) (columnIndex 34)) := by
  decide +kernel


/-- Source row 35 for the stated finite source data. -/
private theorem source_row_35 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 35 l =
      baseColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 35 l =
      baseColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 35 l =
      upColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 35 l =
      upColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 35 l =
      downColumnReal (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 35 l =
      downColumnImag (sourceIndex 35) l (rowIndex 35) (columnIndex 35)) := by
  decide +kernel


/-- Source row 36 for the stated finite source data. -/
private theorem source_row_36 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 36 l =
      baseColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 36 l =
      baseColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 36 l =
      upColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 36 l =
      upColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 36 l =
      downColumnReal (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 36 l =
      downColumnImag (sourceIndex 36) l (rowIndex 36) (columnIndex 36)) := by
  decide +kernel


/-- Source row 37 for the stated finite source data. -/
private theorem source_row_37 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 37 l =
      baseColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 37 l =
      baseColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 37 l =
      upColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 37 l =
      upColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 37 l =
      downColumnReal (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 37 l =
      downColumnImag (sourceIndex 37) l (rowIndex 37) (columnIndex 37)) := by
  decide +kernel


/-- Source row 38 for the stated finite source data. -/
private theorem source_row_38 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 38 l =
      baseColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 38 l =
      baseColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 38 l =
      upColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 38 l =
      upColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 38 l =
      downColumnReal (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 38 l =
      downColumnImag (sourceIndex 38) l (rowIndex 38) (columnIndex 38)) := by
  decide +kernel


/-- Source row 39 for the stated finite source data. -/
private theorem source_row_39 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 39 l =
      baseColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 39 l =
      baseColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 39 l =
      upColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 39 l =
      upColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 39 l =
      downColumnReal (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 39 l =
      downColumnImag (sourceIndex 39) l (rowIndex 39) (columnIndex 39)) := by
  decide +kernel


/-- Source row 40 for the stated finite source data. -/
private theorem source_row_40 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 40 l =
      baseColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 40 l =
      baseColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 40 l =
      upColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 40 l =
      upColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 40 l =
      downColumnReal (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 40 l =
      downColumnImag (sourceIndex 40) l (rowIndex 40) (columnIndex 40)) := by
  decide +kernel


/-- Source row 41 for the stated finite source data. -/
private theorem source_row_41 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 41 l =
      baseColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 41 l =
      baseColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 41 l =
      upColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 41 l =
      upColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 41 l =
      downColumnReal (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 41 l =
      downColumnImag (sourceIndex 41) l (rowIndex 41) (columnIndex 41)) := by
  decide +kernel


/-- Source row 42 for the stated finite source data. -/
private theorem source_row_42 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 42 l =
      baseColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 42 l =
      baseColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 42 l =
      upColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 42 l =
      upColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 42 l =
      downColumnReal (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 42 l =
      downColumnImag (sourceIndex 42) l (rowIndex 42) (columnIndex 42)) := by
  decide +kernel


/-- Source row 43 for the stated finite source data. -/
private theorem source_row_43 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 43 l =
      baseColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 43 l =
      baseColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 43 l =
      upColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 43 l =
      upColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 43 l =
      downColumnReal (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 43 l =
      downColumnImag (sourceIndex 43) l (rowIndex 43) (columnIndex 43)) := by
  decide +kernel


/-- Source row 44 for the stated finite source data. -/
private theorem source_row_44 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 44 l =
      baseColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 44 l =
      baseColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 44 l =
      upColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 44 l =
      upColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 44 l =
      downColumnReal (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 44 l =
      downColumnImag (sourceIndex 44) l (rowIndex 44) (columnIndex 44)) := by
  decide +kernel


/-- Source row 45 for the stated finite source data. -/
private theorem source_row_45 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 45 l =
      baseColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 45 l =
      baseColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 45 l =
      upColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 45 l =
      upColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 45 l =
      downColumnReal (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 45 l =
      downColumnImag (sourceIndex 45) l (rowIndex 45) (columnIndex 45)) := by
  decide +kernel


/-- Source row 46 for the stated finite source data. -/
private theorem source_row_46 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 46 l =
      baseColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 46 l =
      baseColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 46 l =
      upColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 46 l =
      upColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 46 l =
      downColumnReal (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 46 l =
      downColumnImag (sourceIndex 46) l (rowIndex 46) (columnIndex 46)) := by
  decide +kernel


/-- Source row 47 for the stated finite source data. -/
private theorem source_row_47 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 47 l =
      baseColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 47 l =
      baseColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 47 l =
      upColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 47 l =
      upColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 47 l =
      downColumnReal (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 47 l =
      downColumnImag (sourceIndex 47) l (rowIndex 47) (columnIndex 47)) := by
  decide +kernel


/-- Source row 48 for the stated finite source data. -/
private theorem source_row_48 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 48 l =
      baseColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 48 l =
      baseColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 48 l =
      upColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 48 l =
      upColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 48 l =
      downColumnReal (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 48 l =
      downColumnImag (sourceIndex 48) l (rowIndex 48) (columnIndex 48)) := by
  decide +kernel


/-- Source row 49 for the stated finite source data. -/
private theorem source_row_49 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 49 l =
      baseColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 49 l =
      baseColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 49 l =
      upColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 49 l =
      upColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 49 l =
      downColumnReal (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 49 l =
      downColumnImag (sourceIndex 49) l (rowIndex 49) (columnIndex 49)) := by
  decide +kernel


/-- Source row 50 for the stated finite source data. -/
private theorem source_row_50 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 50 l =
      baseColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 50 l =
      baseColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 50 l =
      upColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 50 l =
      upColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 50 l =
      downColumnReal (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 50 l =
      downColumnImag (sourceIndex 50) l (rowIndex 50) (columnIndex 50)) := by
  decide +kernel


/-- Source row 51 for the stated finite source data. -/
private theorem source_row_51 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 51 l =
      baseColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 51 l =
      baseColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 51 l =
      upColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 51 l =
      upColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 51 l =
      downColumnReal (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 51 l =
      downColumnImag (sourceIndex 51) l (rowIndex 51) (columnIndex 51)) := by
  decide +kernel


/-- Source row 52 for the stated finite source data. -/
private theorem source_row_52 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 52 l =
      baseColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 52 l =
      baseColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 52 l =
      upColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 52 l =
      upColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 52 l =
      downColumnReal (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 52 l =
      downColumnImag (sourceIndex 52) l (rowIndex 52) (columnIndex 52)) := by
  decide +kernel


/-- Source row 53 for the stated finite source data. -/
private theorem source_row_53 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 53 l =
      baseColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 53 l =
      baseColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 53 l =
      upColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 53 l =
      upColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 53 l =
      downColumnReal (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 53 l =
      downColumnImag (sourceIndex 53) l (rowIndex 53) (columnIndex 53)) := by
  decide +kernel


/-- Source row 54 for the stated finite source data. -/
private theorem source_row_54 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 54 l =
      baseColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 54 l =
      baseColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 54 l =
      upColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 54 l =
      upColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 54 l =
      downColumnReal (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 54 l =
      downColumnImag (sourceIndex 54) l (rowIndex 54) (columnIndex 54)) := by
  decide +kernel


/-- Source row 55 for the stated finite source data. -/
private theorem source_row_55 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 55 l =
      baseColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 55 l =
      baseColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 55 l =
      upColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 55 l =
      upColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 55 l =
      downColumnReal (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 55 l =
      downColumnImag (sourceIndex 55) l (rowIndex 55) (columnIndex 55)) := by
  decide +kernel


/-- Source row 56 for the stated finite source data. -/
private theorem source_row_56 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 56 l =
      baseColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 56 l =
      baseColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 56 l =
      upColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 56 l =
      upColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 56 l =
      downColumnReal (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 56 l =
      downColumnImag (sourceIndex 56) l (rowIndex 56) (columnIndex 56)) := by
  decide +kernel


/-- Source row 57 for the stated finite source data. -/
private theorem source_row_57 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 57 l =
      baseColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 57 l =
      baseColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 57 l =
      upColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 57 l =
      upColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 57 l =
      downColumnReal (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 57 l =
      downColumnImag (sourceIndex 57) l (rowIndex 57) (columnIndex 57)) := by
  decide +kernel


/-- Source row 58 for the stated finite source data. -/
private theorem source_row_58 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 58 l =
      baseColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 58 l =
      baseColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 58 l =
      upColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 58 l =
      upColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 58 l =
      downColumnReal (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 58 l =
      downColumnImag (sourceIndex 58) l (rowIndex 58) (columnIndex 58)) := by
  decide +kernel


/-- Source row 59 for the stated finite source data. -/
private theorem source_row_59 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 59 l =
      baseColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 59 l =
      baseColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 59 l =
      upColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 59 l =
      upColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 59 l =
      downColumnReal (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 59 l =
      downColumnImag (sourceIndex 59) l (rowIndex 59) (columnIndex 59)) := by
  decide +kernel


/-- Source row 60 for the stated finite source data. -/
private theorem source_row_60 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 60 l =
      baseColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 60 l =
      baseColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 60 l =
      upColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 60 l =
      upColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 60 l =
      downColumnReal (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 60 l =
      downColumnImag (sourceIndex 60) l (rowIndex 60) (columnIndex 60)) := by
  decide +kernel


/-- Source row 61 for the stated finite source data. -/
private theorem source_row_61 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 61 l =
      baseColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 61 l =
      baseColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 61 l =
      upColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 61 l =
      upColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 61 l =
      downColumnReal (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 61 l =
      downColumnImag (sourceIndex 61) l (rowIndex 61) (columnIndex 61)) := by
  decide +kernel


/-- Source row 62 for the stated finite source data. -/
private theorem source_row_62 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 62 l =
      baseColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 62 l =
      baseColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 62 l =
      upColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 62 l =
      upColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 62 l =
      downColumnReal (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 62 l =
      downColumnImag (sourceIndex 62) l (rowIndex 62) (columnIndex 62)) := by
  decide +kernel


/-- Source row 63 for the stated finite source data. -/
private theorem source_row_63 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 63 l =
      baseColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 63 l =
      baseColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 63 l =
      upColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 63 l =
      upColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 63 l =
      downColumnReal (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 63 l =
      downColumnImag (sourceIndex 63) l (rowIndex 63) (columnIndex 63)) := by
  decide +kernel


/-- Source row 64 for the stated finite source data. -/
private theorem source_row_64 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 64 l =
      baseColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 64 l =
      baseColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 64 l =
      upColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 64 l =
      upColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 64 l =
      downColumnReal (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 64 l =
      downColumnImag (sourceIndex 64) l (rowIndex 64) (columnIndex 64)) := by
  decide +kernel


/-- Source row 65 for the stated finite source data. -/
private theorem source_row_65 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 65 l =
      baseColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 65 l =
      baseColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 65 l =
      upColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 65 l =
      upColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 65 l =
      downColumnReal (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 65 l =
      downColumnImag (sourceIndex 65) l (rowIndex 65) (columnIndex 65)) := by
  decide +kernel


/-- Source row 66 for the stated finite source data. -/
private theorem source_row_66 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 66 l =
      baseColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 66 l =
      baseColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 66 l =
      upColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 66 l =
      upColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 66 l =
      downColumnReal (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 66 l =
      downColumnImag (sourceIndex 66) l (rowIndex 66) (columnIndex 66)) := by
  decide +kernel


/-- Source row 67 for the stated finite source data. -/
private theorem source_row_67 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 67 l =
      baseColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 67 l =
      baseColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 67 l =
      upColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 67 l =
      upColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 67 l =
      downColumnReal (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 67 l =
      downColumnImag (sourceIndex 67) l (rowIndex 67) (columnIndex 67)) := by
  decide +kernel


/-- Source row 68 for the stated finite source data. -/
private theorem source_row_68 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 68 l =
      baseColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 68 l =
      baseColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 68 l =
      upColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 68 l =
      upColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 68 l =
      downColumnReal (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 68 l =
      downColumnImag (sourceIndex 68) l (rowIndex 68) (columnIndex 68)) := by
  decide +kernel


/-- Source row 69 for the stated finite source data. -/
private theorem source_row_69 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 69 l =
      baseColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 69 l =
      baseColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 69 l =
      upColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 69 l =
      upColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 69 l =
      downColumnReal (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 69 l =
      downColumnImag (sourceIndex 69) l (rowIndex 69) (columnIndex 69)) := by
  decide +kernel


/-- Source row 70 for the stated finite source data. -/
private theorem source_row_70 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 70 l =
      baseColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 70 l =
      baseColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 70 l =
      upColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 70 l =
      upColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 70 l =
      downColumnReal (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 70 l =
      downColumnImag (sourceIndex 70) l (rowIndex 70) (columnIndex 70)) := by
  decide +kernel


/-- Source row 71 for the stated finite source data. -/
private theorem source_row_71 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 71 l =
      baseColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 71 l =
      baseColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 71 l =
      upColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 71 l =
      upColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 71 l =
      downColumnReal (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 71 l =
      downColumnImag (sourceIndex 71) l (rowIndex 71) (columnIndex 71)) := by
  decide +kernel


/-- Source row 72 for the stated finite source data. -/
private theorem source_row_72 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 72 l =
      baseColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 72 l =
      baseColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 72 l =
      upColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 72 l =
      upColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 72 l =
      downColumnReal (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 72 l =
      downColumnImag (sourceIndex 72) l (rowIndex 72) (columnIndex 72)) := by
  decide +kernel


/-- Source row 73 for the stated finite source data. -/
private theorem source_row_73 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 73 l =
      baseColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 73 l =
      baseColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 73 l =
      upColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 73 l =
      upColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 73 l =
      downColumnReal (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 73 l =
      downColumnImag (sourceIndex 73) l (rowIndex 73) (columnIndex 73)) := by
  decide +kernel


/-- Source row 74 for the stated finite source data. -/
private theorem source_row_74 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 74 l =
      baseColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 74 l =
      baseColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 74 l =
      upColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 74 l =
      upColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 74 l =
      downColumnReal (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 74 l =
      downColumnImag (sourceIndex 74) l (rowIndex 74) (columnIndex 74)) := by
  decide +kernel


/-- Source row 75 for the stated finite source data. -/
private theorem source_row_75 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 75 l =
      baseColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 75 l =
      baseColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 75 l =
      upColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 75 l =
      upColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 75 l =
      downColumnReal (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 75 l =
      downColumnImag (sourceIndex 75) l (rowIndex 75) (columnIndex 75)) := by
  decide +kernel


/-- Source row 76 for the stated finite source data. -/
private theorem source_row_76 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 76 l =
      baseColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 76 l =
      baseColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 76 l =
      upColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 76 l =
      upColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 76 l =
      downColumnReal (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 76 l =
      downColumnImag (sourceIndex 76) l (rowIndex 76) (columnIndex 76)) := by
  decide +kernel


/-- Source row 77 for the stated finite source data. -/
private theorem source_row_77 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 77 l =
      baseColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 77 l =
      baseColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 77 l =
      upColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 77 l =
      upColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 77 l =
      downColumnReal (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 77 l =
      downColumnImag (sourceIndex 77) l (rowIndex 77) (columnIndex 77)) := by
  decide +kernel


/-- Source row 78 for the stated finite source data. -/
private theorem source_row_78 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 78 l =
      baseColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 78 l =
      baseColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 78 l =
      upColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 78 l =
      upColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 78 l =
      downColumnReal (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 78 l =
      downColumnImag (sourceIndex 78) l (rowIndex 78) (columnIndex 78)) := by
  decide +kernel


/-- Source row 79 for the stated finite source data. -/
private theorem source_row_79 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 79 l =
      baseColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 79 l =
      baseColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 79 l =
      upColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 79 l =
      upColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 79 l =
      downColumnReal (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 79 l =
      downColumnImag (sourceIndex 79) l (rowIndex 79) (columnIndex 79)) := by
  decide +kernel


/-- Source row 80 for the stated finite source data. -/
private theorem source_row_80 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 80 l =
      baseColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 80 l =
      baseColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 80 l =
      upColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 80 l =
      upColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 80 l =
      downColumnReal (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 80 l =
      downColumnImag (sourceIndex 80) l (rowIndex 80) (columnIndex 80)) := by
  decide +kernel


/-- Source row 81 for the stated finite source data. -/
private theorem source_row_81 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 81 l =
      baseColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 81 l =
      baseColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 81 l =
      upColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 81 l =
      upColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 81 l =
      downColumnReal (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 81 l =
      downColumnImag (sourceIndex 81) l (rowIndex 81) (columnIndex 81)) := by
  decide +kernel


/-- Source row 82 for the stated finite source data. -/
private theorem source_row_82 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 82 l =
      baseColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 82 l =
      baseColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 82 l =
      upColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 82 l =
      upColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 82 l =
      downColumnReal (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 82 l =
      downColumnImag (sourceIndex 82) l (rowIndex 82) (columnIndex 82)) := by
  decide +kernel


/-- Source row 83 for the stated finite source data. -/
private theorem source_row_83 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 83 l =
      baseColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 83 l =
      baseColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 83 l =
      upColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 83 l =
      upColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 83 l =
      downColumnReal (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 83 l =
      downColumnImag (sourceIndex 83) l (rowIndex 83) (columnIndex 83)) := by
  decide +kernel


/-- Source row 84 for the stated finite source data. -/
private theorem source_row_84 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 84 l =
      baseColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 84 l =
      baseColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 84 l =
      upColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 84 l =
      upColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 84 l =
      downColumnReal (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 84 l =
      downColumnImag (sourceIndex 84) l (rowIndex 84) (columnIndex 84)) := by
  decide +kernel


/-- Source row 85 for the stated finite source data. -/
private theorem source_row_85 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 85 l =
      baseColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 85 l =
      baseColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 85 l =
      upColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 85 l =
      upColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 85 l =
      downColumnReal (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 85 l =
      downColumnImag (sourceIndex 85) l (rowIndex 85) (columnIndex 85)) := by
  decide +kernel


/-- Source row 86 for the stated finite source data. -/
private theorem source_row_86 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 86 l =
      baseColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 86 l =
      baseColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 86 l =
      upColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 86 l =
      upColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 86 l =
      downColumnReal (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 86 l =
      downColumnImag (sourceIndex 86) l (rowIndex 86) (columnIndex 86)) := by
  decide +kernel


/-- Source row 87 for the stated finite source data. -/
private theorem source_row_87 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 87 l =
      baseColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 87 l =
      baseColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 87 l =
      upColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 87 l =
      upColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 87 l =
      downColumnReal (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 87 l =
      downColumnImag (sourceIndex 87) l (rowIndex 87) (columnIndex 87)) := by
  decide +kernel


/-- Source row 88 for the stated finite source data. -/
private theorem source_row_88 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 88 l =
      baseColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 88 l =
      baseColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 88 l =
      upColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 88 l =
      upColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 88 l =
      downColumnReal (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 88 l =
      downColumnImag (sourceIndex 88) l (rowIndex 88) (columnIndex 88)) := by
  decide +kernel


/-- Source row 89 for the stated finite source data. -/
private theorem source_row_89 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 89 l =
      baseColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 89 l =
      baseColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 89 l =
      upColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 89 l =
      upColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 89 l =
      downColumnReal (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 89 l =
      downColumnImag (sourceIndex 89) l (rowIndex 89) (columnIndex 89)) := by
  decide +kernel


/-- Source row 90 for the stated finite source data. -/
private theorem source_row_90 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 90 l =
      baseColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 90 l =
      baseColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 90 l =
      upColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 90 l =
      upColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 90 l =
      downColumnReal (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 90 l =
      downColumnImag (sourceIndex 90) l (rowIndex 90) (columnIndex 90)) := by
  decide +kernel


/-- Source row 91 for the stated finite source data. -/
private theorem source_row_91 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 91 l =
      baseColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 91 l =
      baseColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 91 l =
      upColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 91 l =
      upColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 91 l =
      downColumnReal (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 91 l =
      downColumnImag (sourceIndex 91) l (rowIndex 91) (columnIndex 91)) := by
  decide +kernel


/-- Source row 92 for the stated finite source data. -/
private theorem source_row_92 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 92 l =
      baseColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 92 l =
      baseColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 92 l =
      upColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 92 l =
      upColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 92 l =
      downColumnReal (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 92 l =
      downColumnImag (sourceIndex 92) l (rowIndex 92) (columnIndex 92)) := by
  decide +kernel


/-- Source row 93 for the stated finite source data. -/
private theorem source_row_93 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 93 l =
      baseColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 93 l =
      baseColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 93 l =
      upColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 93 l =
      upColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 93 l =
      downColumnReal (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 93 l =
      downColumnImag (sourceIndex 93) l (rowIndex 93) (columnIndex 93)) := by
  decide +kernel


/-- Source row 94 for the stated finite source data. -/
private theorem source_row_94 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 94 l =
      baseColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 94 l =
      baseColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 94 l =
      upColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 94 l =
      upColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 94 l =
      downColumnReal (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 94 l =
      downColumnImag (sourceIndex 94) l (rowIndex 94) (columnIndex 94)) := by
  decide +kernel


/-- Source row 95 for the stated finite source data. -/
private theorem source_row_95 :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal 95 l =
      baseColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag 95 l =
      baseColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal 95 l =
      upColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag 95 l =
      upColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal 95 l =
      downColumnReal (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag 95 l =
      downColumnImag (sourceIndex 95) l (rowIndex 95) (columnIndex 95)) := by
  decide +kernel


/-- Source parts match for the stated finite source data. -/
theorem source_parts_match (a : Fin 96) :
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseReal a l =
      baseColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceBaseImag a l =
      baseColumnImag (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpReal a l =
      upColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceUpImag a l =
      upColumnImag (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownReal a l =
      downColumnReal (sourceIndex a) l (rowIndex a) (columnIndex a)) ∧
    (∀ l, ThreeLevelOrder120LowCoefficientTables.faceDownImag a l =
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

/-- Face Base apply for the stated finite source data. -/
theorem faceBase_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelOrder120LowCoefficientTables.faceBase a l =
      ((if l = 0 then edge order120 (ThreeLevelWordDual.source (sourceIndex a)) 0 1 else 0) +
      (if l = 1 then edge order120 (ThreeLevelWordDual.source (sourceIndex a)) 1 2 + edge order120 (ThreeLevelWordDual.source (sourceIndex a)) 0 2 else 0) +
      ((faceDiagonal order120 (ThreeLevelWordDual.source (sourceIndex a))) * maskedLiteralInput l -
        maskedLiteralInput l * (faceDiagonal order120 (ThreeLevelWordDual.source (sourceIndex a))))) (rowIndex a) (columnIndex a) := by
  rw [← baseColumn_parts]
  simp only [ThreeLevelOrder120LowCoefficientTables.faceBase, fromParts,
    (source_parts_match a).1 l, (source_parts_match a).2.1 l]

/-- Face Base mul Vec for the stated finite source data. -/
theorem faceBase_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (ThreeLevelOrder120LowCoefficientTables.faceBase *ᵥ fullCoordinates c d Y) a =
      sourceBase order120 c d Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  twoSided_two_edges_stack_mulVec ThreeLevelOrder120LowCoefficientTables.faceBase
    (fun k => faceDiagonal order120 (ThreeLevelWordDual.source k))
    (fun k => faceDiagonal order120 (ThreeLevelWordDual.source k))
    (fun k => edge order120 (ThreeLevelWordDual.source k) 0 1)
    (fun k => edge order120 (ThreeLevelWordDual.source k) 1 2 + edge order120 (ThreeLevelWordDual.source k) 0 2)
    faceBase_apply order120 c d Y hY a

/-- Face Up apply for the stated finite source data. -/
theorem faceUp_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelOrder120LowCoefficientTables.faceUp a l =
      (((mergedLow order120 * ThreeLevelWordDual.source (sourceIndex a) * mergedHigh order120) * maskedLiteralInput l -
        maskedLiteralInput l * (mergedHigh order120 * ThreeLevelWordDual.source (sourceIndex a) * mergedLow order120))) (rowIndex a) (columnIndex a) := by
  rw [← upColumn_parts]
  simp only [ThreeLevelOrder120LowCoefficientTables.faceUp, fromParts,
    (source_parts_match a).2.2.1 l, (source_parts_match a).2.2.2.1 l]

/-- Face Up mul Vec for the stated finite source data. -/
theorem faceUp_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (ThreeLevelOrder120LowCoefficientTables.faceUp *ᵥ fullCoordinates c d Y) a =
      sourceUp order120 Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  twoSided_stack_mulVec ThreeLevelOrder120LowCoefficientTables.faceUp
    (fun k => mergedLow order120 * ThreeLevelWordDual.source k * mergedHigh order120)
    (fun k => mergedHigh order120 * ThreeLevelWordDual.source k * mergedLow order120)
    faceUp_apply order120 c d Y hY a

/-- Face Down apply for the stated finite source data. -/
theorem faceDown_apply (a : Fin 96) (l : Fin 15) :
    ThreeLevelOrder120LowCoefficientTables.faceDown a l =
      ((if l = 0 then edge order120 (ThreeLevelWordDual.source (sourceIndex a)) 0 2 else 0) +
      ((mergedHigh order120 * ThreeLevelWordDual.source (sourceIndex a) * mergedLow order120) * maskedLiteralInput l -
        maskedLiteralInput l * (mergedLow order120 * ThreeLevelWordDual.source (sourceIndex a) * mergedHigh order120))) (rowIndex a) (columnIndex a) := by
  rw [← downColumn_parts]
  simp only [ThreeLevelOrder120LowCoefficientTables.faceDown, fromParts,
    (source_parts_match a).2.2.2.2.1 l, (source_parts_match a).2.2.2.2.2 l]

/-- Face Down mul Vec for the stated finite source data. -/
theorem faceDown_mulVec (c d : ℂ) (Y : Operator 4)
    (hY : IsFast order120 Y) (a : Fin 96) :
    (ThreeLevelOrder120LowCoefficientTables.faceDown *ᵥ fullCoordinates c d Y) a =
      sourceDown order120 c Y (sourceIndex a) (rowIndex a) (columnIndex a) :=
  twoSided_edge_stack_mulVec ThreeLevelOrder120LowCoefficientTables.faceDown
    (fun k => mergedHigh order120 * ThreeLevelWordDual.source k * mergedLow order120)
    (fun k => mergedLow order120 * ThreeLevelWordDual.source k * mergedHigh order120)
    (fun k => edge order120 (ThreeLevelWordDual.source k) 0 2)
    faceDown_apply order120 c d Y hY a


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowSourceTables
