/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkSpectra04.WalkDefinition.SzegedyDefOneQuantizedWalkStat
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QWalkSpectra04.WalkDefinition

theorem szegedyDefOneQuantizedWalk : SzegedyDefOneQuantizedWalk := by
  intro I J _ _ _ _ c r
  refine ⟨rfl, ?_⟩
  intro K _ _ P
  have hB : paperFrameB P = SzegedyIsometryB P := by
    ext ⟨a,b⟩ j
    exact (szegedyIsometryB_apply P a b j).symm
  have hA : paperFrameA P = SzegedyIsometry P := rfl
  have hR : paperDiffusionR P = SwapGate * paperDiffusionC P * SwapGate := by
    ext ⟨a,i⟩ ⟨b,j⟩
    rw [paperDiffusionR, paperDiffusionC, hA, hB,
      swapGate_mul_mul_swapGate, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Prod.swap_prod_mk, Matrix.conjTranspose_apply,
      szegedyIsometry_apply_pair, szegedyIsometryB_apply]
  have href : (2:ℂ) • paperDiffusionR P - 1 =
      SwapGate * ((2:ℂ) • paperDiffusionC P - 1) * SwapGate := by
    rw [hR, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, swapGate_mul_self]
  rw [paperMu, href]
  rfl

end Qatlib.Papers.QWalkSpectra04.WalkDefinition
