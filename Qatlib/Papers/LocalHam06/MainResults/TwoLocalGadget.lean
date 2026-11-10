/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocalHam06.MainResults.QmaCompletenessPhysical
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Classical BigOperators Kronecker
open Matrix
open Qatlib.Papers.LocalHam06.MainResults

namespace Qatlib.Papers.LocalHam06.MainResults.TwoLocalGadget

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

set_option autoImplicit false

def matInner {I : Type*} [Fintype I] (v w : I → ℂ) : ℂ :=
  ∑ i, starRingEnd ℂ (v i) * w i

def matRayleigh {I : Type*} [Fintype I] (B : Matrix I I ℂ) (v : I → ℂ) : ℝ :=
  (matInner v (B.mulVec v)).re

def MatIsEigenvalue {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (μ : ℝ) : Prop :=
  ∃ v : I → ℂ, v ≠ 0 ∧ H.mulVec v = (μ : ℂ) • v

theorem matInner_add_right {I : Type*} [Fintype I] (v x y : I → ℂ) :
    matInner v (x + y) = matInner v x + matInner v y := by
  simp [matInner, mul_add, Finset.sum_add_distrib]

theorem matInner_zero_left {I : Type*} [Fintype I] (w : I → ℂ) :
    matInner (0 : I → ℂ) w = 0 := by
  simp [matInner]

theorem matRayleigh_zero {I : Type*} [Fintype I] (v : I → ℂ) :
    matRayleigh (0 : Matrix I I ℂ) v = 0 := by
  simp [matRayleigh, matInner]

theorem matRayleigh_add {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) (v : I → ℂ) :
    matRayleigh (A + B) v = matRayleigh A v + matRayleigh B v := by
  unfold matRayleigh
  rw [Matrix.add_mulVec, matInner_add_right, Complex.add_re]

theorem matInner_re_comm {I : Type*} [Fintype I] (v w : I → ℂ) :
    (matInner v w).re = (matInner w v).re := by
  unfold matInner
  rw [Complex.re_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end Qatlib.Papers.LocalHam06.MainResults.TwoLocalGadget
