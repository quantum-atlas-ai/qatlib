/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLogicSynth04.MainResults.QubitRotations

/-!
# Algebra of controlled rotation multiplexors

This module identifies scalar identity multiplexors with diagonal matrices and defines the
controlled bit flip `cnotSelect`. The identity `demux_single_rotation` decomposes a two-branch
rotation multiplexor into two controlled bit flips and rotations at the half-sum and
half-difference angles. See [ShendeBullockMarkov2006] for the paper's setting.

## Main statements

* `theorem3_recognize_diagonal`: A block diagonal family of scalar identity matrices is the
  diagonal matrix carrying the same scalar on each target coordinate.
* `theorem4_demux_ry`: The two-branch `paperRy` multiplexor factors into two controlled bit
  flips and `paperRy` rotations at the half-difference and half-sum angles.

## References

* [Shende et al., 2006][ShendeBullockMarkov2006]
-/

set_option backward.isDefEq.respectTransparency false

open scoped Matrix
open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLogicSynth04.MainResults

/-- A block diagonal family of scalar identity matrices is the diagonal matrix carrying the same
scalar on each target coordinate. See [ShendeBullockMarkov2006]. -/
theorem theorem3_recognize_diagonal {N : Type*} [Fintype N] [DecidableEq N] (d : N → ℂ) :
    Matrix.blockDiagonal (fun j : N => d j • (1 : Matrix Bool Bool ℂ)) =
      Matrix.diagonal (fun p : Bool × N => d p.2) := by
  simp only [Matrix.smul_one_eq_diagonal, Matrix.blockDiagonal_diagonal]

/-- The controlled bit flip that applies `bitFlip` when the selector is true and the identity
otherwise. -/
def cnotSelect : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.blockDiagonal (fun s : Bool => if s then bitFlip else 1)

/-- For an additive rotation family reversed by bit-flip conjugation, a two-branch multiplexor
factors into two controlled bit flips and rotations at the half-difference and half-sum
angles. See [ShendeBullockMarkov2006]. -/
theorem demux_single_rotation (R : ℝ → Matrix Bool Bool ℂ)
    (hadd : ∀ a b : ℝ, R a * R b = R (a + b))
    (hflip : ∀ θ : ℝ, bitFlip * R θ * bitFlip = R (-θ))
    (θ₀ θ₁ : ℝ) :
    Matrix.blockDiagonal (fun s : Bool => R (if s then θ₁ else θ₀)) =
      cnotSelect * Matrix.blockDiagonal (fun _ : Bool => R ((θ₀ - θ₁)/2)) *
        cnotSelect * Matrix.blockDiagonal (fun _ : Bool => R ((θ₀ + θ₁)/2)) := by
  simp only [cnotSelect]
  rw [← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  apply congrArg Matrix.blockDiagonal
  funext s
  cases s
  · simp only [Bool.false_eq_true, if_false, one_mul, mul_one]
    rw [hadd]
    congr 1
    ring
  · simp only [if_true]
    rw [hflip, hadd]
    congr 1
    ring

/-- The two-branch `paperRz` multiplexor factors into two controlled bit flips and `paperRz`
rotations at the half-difference and half-sum angles. See [ShendeBullockMarkov2006]. -/
theorem theorem4_demux_rz (θ₀ θ₁ : ℝ) :
    Matrix.blockDiagonal (fun s : Bool => paperRz (if s then θ₁ else θ₀)) =
      cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRz ((θ₀ - θ₁)/2)) *
        cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRz ((θ₀ + θ₁)/2)) :=
  demux_single_rotation paperRz paperRz_mul bitFlip_mul_paperRz θ₀ θ₁

/-- The two-branch `paperRy` multiplexor factors into two controlled bit flips and `paperRy`
rotations at the half-difference and half-sum angles. See [ShendeBullockMarkov2006]. -/
theorem theorem4_demux_ry (θ₀ θ₁ : ℝ) :
    Matrix.blockDiagonal (fun s : Bool => paperRy (if s then θ₁ else θ₀)) =
      cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRy ((θ₀ - θ₁)/2)) *
        cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRy ((θ₀ + θ₁)/2)) :=
  demux_single_rotation paperRy paperRy_mul bitFlip_mul_paperRy θ₀ θ₁

end Qatlib.Papers.QLogicSynth04.MainResults
