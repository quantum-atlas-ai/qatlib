/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingCoreDefs
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-!
# Composable constructors for the public CSS model

Chain-compatible boundary matrices, X/Z duality, and independent sums all
produce the same `Qatlib.Concepts.CodingDecoding.CssTesters.CssCode.CssData`
consumed by distance and recovery components.
No constructor assigns an unproved distance or decoder complexity.
-/

namespace Qatlib.Concepts.ErrorCorrection.CssBuild

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters
open scoped Matrix

/-- Compatible boundary maps give CSS checks on the middle chain group. -/
def ofComplex {ι κX κZ : Type*} [Fintype ι]
    (d₁ : Matrix κX ι (ZMod 2)) (d₂ : Matrix ι κZ (ZMod 2))
    (h : d₁ * d₂ = 0) : CssData ι κX κZ where
  hX := d₁
  hZ := d₂ᵀ
  hcompat := by simpa only [Matrix.transpose_transpose] using h

/-- Exchanging the two check families gives the X/Z-dual CSS code. -/
def dual {ι κX κZ : Type*} [Fintype ι] (c : CssData ι κX κZ) : CssData ι κZ κX where
  hX := c.hZ
  hZ := c.hX
  hcompat := by
    have h := congrArg Matrix.transpose c.hcompat
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h

/-- Applying X/Z duality twice returns the same CSS data. -/
theorem dual_dual {ι κX κZ : Type*} [Fintype ι] (c : CssData ι κX κZ) :
    dual (dual c) = c := by cases c; rfl

/-- X/Z duality preserves the encoded-qubit count, including redundant checks. -/
theorem dual_encoded {ι κX κZ : Type*} [Fintype ι]
    (c : CssData ι κX κZ) : (dual c).encodedQubits = c.encodedQubits := by
  simp only [CssData.encodedQubits, dual, Nat.sub_sub, Nat.add_comm]

/-- X/Z duality preserves the extended logical distance. -/
theorem dual_distance {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]
    (c : CssData ι κX κZ) : cssDistance (dual c) = cssDistance c := by
  simp only [cssDistance, dual]
  exact min_comm _ _

/-- Independent CSS codes combine by block-diagonal checks on disjoint coordinates. -/
def directSum {ι κX κZ ι' κX' κZ' : Type*} [Fintype ι] [Fintype ι']
    (c : CssData ι κX κZ) (d : CssData ι' κX' κZ') :
    CssData (ι ⊕ ι') (κX ⊕ κX') (κZ ⊕ κZ') where
  hX := Matrix.fromBlocks c.hX 0 0 d.hX
  hZ := Matrix.fromBlocks c.hZ 0 0 d.hZ
  hcompat := by
    simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, c.hcompat, d.hcompat,
      Matrix.fromBlocks_zero]

/-- A direct-sum code reports the two component syndromes without mixing coordinates. -/
theorem sum_syndrome {ι κX κZ ι' κX' κZ' : Type*} [Fintype ι] [Fintype ι']
    (c : CssData ι κX κZ) (d : CssData ι' κX' κZ')
    (e : PauliLabel ι) (f : PauliLabel ι') :
    pauliSyndrome (directSum c d) (Sum.elim e.1 f.1, Sum.elim e.2 f.2) =
      (Sum.elim (pauliSyndrome c e).1 (pauliSyndrome d f).1,
       Sum.elim (pauliSyndrome c e).2 (pauliSyndrome d f).2) := by
  simp [pauliSyndrome, directSum, Matrix.fromBlocks_mulVec, Function.comp_def]

end Qatlib.Concepts.ErrorCorrection.CssBuild
