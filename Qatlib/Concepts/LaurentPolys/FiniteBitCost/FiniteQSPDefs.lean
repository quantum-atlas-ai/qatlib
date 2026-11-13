/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Matrices defining the polynomial-to-QSP bridge

This module defines the normalized coefficient factors, polynomial-pair matrices, diagonal
matrices, and recursive words used by the QSP bridge. `rhwQSPBridgeGammas` forms a symmetric
coefficient list from phases, while `rhwQSPBridgeOperator` forms the corresponding symmetric
phase-and-signal recursion. These identities connect polynomial constructions with the quantum
signal processing framework [LowChuang2017].

## Main statements

* `rhwQSPBridgePair`: the matrix built from a nonlinear Fourier polynomial pair.
* `rhwQSPBridgeWord`: the recursive matrix word.
* `rhwQSPBridgeOperator`: the symmetric QSP recursion.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Qatlib

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LaurentPolys.FiniteBitCost
open Polynomial Matrix

/-- The complex two-by-two matrix with rows `(a, b)` and `(c, d)`, indexed by `Bool`. -/
noncomputable def rhwQSPBridgeMatrix (a b c d : ℂ) : Matrix Bool Bool ℂ :=
  fun i j => if i then (if j then d else c) else (if j then b else a)

/-- The bridge diagonal matrix with entries `w` and `w⁻¹`. -/
noncomputable def rhwQSPBridgeDiagonal (w : ℂ) : Matrix Bool Bool ℂ := rhwQSPBridgeMatrix w 0 0 w⁻¹

/-- The matrix with rows `(1, γ)` and `(-star γ, 1)`, scaled by `1 / sqrt (1 + normSq γ)`. -/
noncomputable def rhwQSPBridgeFactor (γ : ℂ) : Matrix Bool Bool ℂ :=
  let c : ℂ := (((Real.sqrt (1+Complex.normSq γ))⁻¹:ℝ):ℂ)
  rhwQSPBridgeMatrix c (c*γ) (-c*star γ) c

/-- The bridge matrix built from the evaluations of the nonlinear Fourier polynomial pair
`nlftSU2 gs` and their conjugates. -/
noncomputable def rhwQSPBridgePair (gs : List ℂ) (z : ℂ) : Matrix Bool Bool ℂ :=
  let p := nlftSU2 gs
  rhwQSPBridgeMatrix (star (p.1.eval z)) (p.2.eval z) (-star (p.2.eval z)) (p.1.eval z)

/-- The recursive product of bridge factors and signal diagonals, terminating in the inverse
signal diagonal for the empty list. -/
noncomputable def rhwQSPBridgeWord (w : ℂ) : List ℂ → Matrix Bool Bool ℂ
  | [] => rhwQSPBridgeDiagonal w⁻¹
  | g::gs => rhwQSPBridgeFactor g*rhwQSPBridgeDiagonal w*rhwQSPBridgeWord w gs

/-- The diagonal phase matrix with entries `exp (i*φ)` and `exp (-i*φ)`. -/
noncomputable def rhwQSPBridgePhase (φ : ℝ) : Matrix Bool Bool ℂ :=
  rhwQSPBridgeMatrix (Complex.exp ((φ:ℂ)*Complex.I)) 0 0 (Complex.exp (-(φ:ℂ)*Complex.I))

/-- The symmetric signal matrix with diagonal entries `x` and off-diagonal entries `i * sqrt (1
- x^2)`. -/
noncomputable def rhwQSPBridgeSignal (x : ℝ) : Matrix Bool Bool ℂ :=
  rhwQSPBridgeMatrix (x:ℂ) (Complex.I*(Real.sqrt (1-x^2):ℂ)) (Complex.I*(Real.sqrt (1-x^2):ℂ)) (x:ℂ)

/-- The complex bridge coefficient `i * tan φ` associated with phase `φ`. -/
noncomputable def rhwQSPBridgeCoefficient (φ : ℝ) : ℂ := Complex.I*(Real.tan φ:ℂ)

/-- The symmetric list of bridge coefficients formed by starting at phase `ψ 0` and adding the
next coefficient at both ends at each step. -/
noncomputable def rhwQSPBridgeGammas (ψ : ℕ → ℝ) : ℕ → List ℂ
  | 0 => [rhwQSPBridgeCoefficient (ψ 0)]
  | d+1 => rhwQSPBridgeCoefficient (ψ (d+1)) :: (rhwQSPBridgeGammas ψ d ++ [rhwQSPBridgeCoefficient (ψ (d+1))])

/-- The symmetric QSP recursion starting with phase `ψ 0` and enclosing each previous operator
between signal matrices and the next phase matrices. -/
noncomputable def rhwQSPBridgeOperator (ψ : ℕ → ℝ) (x : ℝ) : ℕ → Matrix Bool Bool ℂ
  | 0 => rhwQSPBridgePhase (ψ 0)
  | d+1 => rhwQSPBridgePhase (ψ (d+1))*rhwQSPBridgeSignal x*rhwQSPBridgeOperator ψ x d*rhwQSPBridgeSignal x*rhwQSPBridgePhase (ψ (d+1))

/-- The matrix of the nonlinear Fourier polynomial pair with its second polynomial evaluation
multiplied by `(z^d)⁻¹`. -/
noncomputable def rhwQSPBridgeCentered (d : ℕ) (gs : List ℂ) (z : ℂ) : Matrix Bool Bool ℂ :=
  let p := nlftSU2 gs
  let b := (z^d)⁻¹*p.2.eval z
  rhwQSPBridgeMatrix (star (p.1.eval z)) b (-star b) (p.1.eval z)

end Qatlib.Concepts.LaurentPolys.FiniteBitCost
