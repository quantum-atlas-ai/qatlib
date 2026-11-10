/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

open Matrix
open scoped Classical BigOperators

noncomputable def eigenPhase (φ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * φ)

variable (I : Type) [Fintype I] [DecidableEq I]

noncomputable def eigenphaseControlledGate (U : Matrix I I ℂ) :
    Matrix (I × Bool) (I × Bool) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then (if q.2 = true then U else 1) p.1 q.1 else 0

noncomputable def hadamardTestGate (U : Matrix I I ℂ) :
    Matrix (I × Bool) (I × Bool) ℂ :=
  TensorGate (1 : Matrix I I ℂ) Hadamard * eigenphaseControlledGate I U *
    TensorGate (1 : Matrix I I ℂ) Hadamard

variable {I}

noncomputable def hadamardTestBitState (lam : ℂ) : QState Bool :=
  fun b => if b then (1 - lam) / 2 else (1 + lam) / 2

noncomputable def hadamardBitDist (φ : ℝ) : FinDist Bool where
  prob b := BornProb (hadamardTestBitState (eigenPhase φ)) b
  nonneg b := bornProb_nonneg _ _
  sum_one := by
    have hnorm : ‖eigenPhase φ‖ = 1 := by
      have h : eigenPhase φ = Complex.exp ((Complex.ofReal (2 * Real.pi * φ)) * Complex.I) := by
        unfold eigenPhase
        rw [show (2 * Real.pi * Complex.I * φ) = (Complex.ofReal (2 * Real.pi * φ)) * Complex.I by
          push_cast
          field_simp]
      rw [h, Complex.norm_exp_ofReal_mul_I]
    have hns : Complex.normSq (eigenPhase φ) = 1 := by
      have h := Complex.normSq_eq_norm_sq (eigenPhase φ)
      rw [hnorm] at h
      simpa using h
    have hsum : Complex.normSq (1 + eigenPhase φ) + Complex.normSq (1 - eigenPhase φ) = 4 := by
      rw [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_one, hns, one_mul,
        Complex.conj_re]
      ring
    show ∑ b : Bool, BornProb (hadamardTestBitState (eigenPhase φ)) b = 1
    rw [Fintype.sum_bool]
    have key : ∀ z w : ℂ,
        ‖z / 2‖ ^ 2 + ‖w / 2‖ ^ 2 = (Complex.normSq z + Complex.normSq w) / 4 := by
      intro z w
      have h2 : Complex.normSq (2 : ℂ) = 4 := by
        rw [Complex.normSq_eq_norm_sq]
        norm_num
      rw [norm_div, norm_div, div_pow, div_pow]
      simp only [← Complex.normSq_eq_norm_sq, h2]
      ring
    have hf : BornProb (hadamardTestBitState (eigenPhase φ)) false
        = ‖(1 + eigenPhase φ) / 2‖ ^ 2 := rfl
    have ht : BornProb (hadamardTestBitState (eigenPhase φ)) true
        = ‖(1 - eigenPhase φ) / 2‖ ^ 2 := rfl
    rw [hf, ht, key]
    linarith

noncomputable def eigenphaseSampleLaw (φ : ℝ) (s : ℕ) : FinDist (Fin (s + s) → Bool) :=
  independentSampleLaw (fun j : Fin (s + s) =>
    if (j : ℕ) < s then hadamardBitDist φ else hadamardBitDist (φ + 1 / 4))

noncomputable def eigenphaseDecode (s : ℕ) (ω : Fin (s + s) → Bool) : ℝ :=
  Complex.arg ((1 - 2 * ((∑ j : Fin s, (if ω (Fin.castAdd s j) then (1 : ℝ) else 0)) / (s : ℝ)))
      + (2 * ((∑ j : Fin s, (if ω (Fin.natAdd s j) then (1 : ℝ) else 0)) / (s : ℝ)) - 1)
        * Complex.I) / (2 * Real.pi)

end Qatlib.Concepts.HspRecovery.KitaevReadout
