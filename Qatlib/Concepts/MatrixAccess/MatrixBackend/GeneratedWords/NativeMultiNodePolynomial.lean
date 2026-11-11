/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NeumannResolvent
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.DefectPolynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.CopyEvolution.Discriminate

/-! The finite Neumann polynomial preserves label-diagonal matrices. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators

variable {J H : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

omit [Fintype J] [Fintype H] [DecidableEq H] in
/-- The finite construction in `NativeMultiNodePolynomial` satisfies `select_sub_family` under the displayed hypotheses. -/
private theorem select_sub_family (U V : J → Matrix H H ℂ) :
    select U - select V = select (fun j => U j - V j) := by
  ext ⟨j, h⟩ ⟨k, h'⟩
  by_cases hj : j = k <;> simp [select, hj]

omit [Fintype J] [Fintype H] [DecidableEq H] in
/-- The finite construction in `NativeMultiNodePolynomial` satisfies `select_sum_family` under the displayed hypotheses. -/
private theorem select_sum_family {K : Type} (s : Finset K) (U : K → J → Matrix H H ℂ) :
    (∑ k ∈ s, select (U k)) = select (fun j => ∑ k ∈ s, U k j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext ⟨j, h⟩ ⟨k, h'⟩
    by_cases hj : j = k <;> simp [select, hj]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, ih]
    ext ⟨j, h⟩ ⟨l, h'⟩
    by_cases hj : j = l <;> simp [select, hj]

/-- The finite construction in `NativeMultiNodePolynomial` satisfies `select_pow_family` under the displayed hypotheses. -/
private theorem select_pow_family (U : J → Matrix H H ℂ) (n : ℕ) :
    (select U)^n = select (fun j => (U j)^n) := by
  induction n with
  | zero => simpa using (parallel_select_one (J := J) (H := H)).symm
  | succ n ih =>
    rw [pow_succ, ih, parallel_select_mul]
    apply congrArg select
    funext j
    rw [pow_succ]

/-- The actual left-defect polynomial acts separately on each label sector.
No nonempty label or data type, normality, or invertibility is required. -/
theorem leftDefectNeumann_select (U : J → Matrix H H ℂ) (b : ℕ) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (select U) b = select (fun j => Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann (U j) b) := by
  unfold Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Neumann.leftDefectNeumann
  have hdef : 1 - select U * (select U)ᴴ =
      select (fun j => 1 - U j * (U j)ᴴ) := by
    rw [parallel_select_adjoint, parallel_select_mul,
      ← parallel_select_one (J := J) (H := H), select_sub_family]
  rw [hdef]
  simp only [parallel_select_adjoint, select_pow_family,
    select_sum_family, parallel_select_mul]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
