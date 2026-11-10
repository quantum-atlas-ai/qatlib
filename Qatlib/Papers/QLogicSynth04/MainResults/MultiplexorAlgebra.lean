/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLogicSynth04.MainResults.QubitRotations
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix
open Matrix
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLogicSynth04.MainResults

theorem theorem3_recognize_diagonal {N : Type*} [Fintype N] [DecidableEq N] (d : N → ℂ) :
    Matrix.blockDiagonal (fun j : N => d j • (1 : Matrix Bool Bool ℂ)) =
      Matrix.diagonal (fun p : Bool × N => d p.2) := by
  simp only [Matrix.smul_one_eq_diagonal, Matrix.blockDiagonal_diagonal]

def cnotSelect : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.blockDiagonal (fun s : Bool => if s then bitFlip else 1)

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

theorem theorem4_demux_rz (θ₀ θ₁ : ℝ) :
    Matrix.blockDiagonal (fun s : Bool => paperRz (if s then θ₁ else θ₀)) =
      cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRz ((θ₀ - θ₁)/2)) *
        cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRz ((θ₀ + θ₁)/2)) :=
  demux_single_rotation paperRz paperRz_mul bitFlip_mul_paperRz θ₀ θ₁

theorem theorem4_demux_ry (θ₀ θ₁ : ℝ) :
    Matrix.blockDiagonal (fun s : Bool => paperRy (if s then θ₁ else θ₀)) =
      cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRy ((θ₀ - θ₁)/2)) *
        cnotSelect * Matrix.blockDiagonal (fun _ : Bool => paperRy ((θ₀ + θ₁)/2)) :=
  demux_single_rotation paperRy paperRy_mul bitFlip_mul_paperRy θ₀ θ₁

end Qatlib.Papers.QLogicSynth04.MainResults
