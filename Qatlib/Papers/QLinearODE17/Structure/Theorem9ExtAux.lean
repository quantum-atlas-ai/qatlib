/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.Structure.Theorem9AltAux
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Papers.QLinearODE17.StructureCore
open Qatlib

variable {N : Type} [Fintype N] [DecidableEq N]

theorem taylor_measure_probability_clipped (ψ φ : QState N) (S : Finset N) (a δ : ℝ)
    (ha : a ≤ Real.sqrt (MeasureProb ψ S))
    (herr : ‖stateVector φ - stateVector ψ‖ ≤ δ) :
    (max 0 (a - δ)) ^ 2 ≤ MeasureProb φ S := by
  have hperturb := taylor_measure_sqrt_sub_le ψ φ S δ herr
  have hbound : max 0 (a - δ) ≤ Real.sqrt (MeasureProb φ S) :=
    max_le (Real.sqrt_nonneg _) (by linarith)
  have hs := pow_le_pow_left₀ (le_max_left 0 (a - δ)) hbound 2
  rwa [Real.sq_sqrt (measureProb_nonneg φ S)] at hs

theorem taylor_joint_probability_clipped (ψ φ : QState N) (S : Finset N)
    (a δ P P₀ : ℝ) (hP₀ : 0 ≤ P₀) (hP : P₀ ≤ P)
    (ha : a ≤ Real.sqrt (MeasureProb ψ S))
    (herr : ‖stateVector φ - stateVector ψ‖ ≤ δ) :
    P₀ * (max 0 (a - δ)) ^ 2 ≤ P * MeasureProb φ S := by
  calc
    _ ≤ P₀ * MeasureProb φ S :=
      mul_le_mul_of_nonneg_left (taylor_measure_probability_clipped ψ φ S a δ ha herr) hP₀
    _ ≤ _ := mul_le_mul_of_nonneg_right hP (measureProb_nonneg φ S)

end Qatlib.Papers.QLinearODE17.StructureCore
