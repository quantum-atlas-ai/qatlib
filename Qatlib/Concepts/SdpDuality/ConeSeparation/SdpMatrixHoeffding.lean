/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum

/-!
# Refutation of the SDP matrix Hoeffding contract

This module proves `not_sdpMatrixHoeffding` using a one-dimensional matrix family taking the
values `1` and `-1` on two outcomes. The matrices are Hermitian contractions with zero summed
mean, yet the deviation event has probability one, contradicting the specialized diagnostic
contract.

The contract belongs to the concentration interfaces used for quantum SDP algorithms;
[BrandaoSvore2017] provides the algorithmic setting.

## Main statements

* `not_sdpMatrixHoeffding`: refutation of `SdpMatrixHoeffding`.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SdpMmwSolver.OracleError

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.ConeSeparation
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The diagnostic contract `SdpMatrixHoeffding` is false. -/
theorem not_sdpMatrixHoeffding : ¬ SdpMatrixHoeffding := by
  intro h
  let Z : Fin 2 → Fin 1 → Operator 1 := fun s _ => if s = 0 then 1 else -1
  have hh : ∀ s i, (Z s i).IsHermitian := by
    intro s i
    dsimp [Z]
    split_ifs
    · exact Matrix.isHermitian_one
    · exact Matrix.isHermitian_one.neg
  have hb : ∀ s i, ‖Z s i‖ ≤ (1 : ℝ) := by
    intro s i
    dsimp [Z]
    split_ifs <;> simp
  have hm : ∀ i, (∑ s, Z s i) = 0 := by
    intro i
    simp [Z, Fin.sum_univ_two]
  have he : ∀ s : Fin 2, (1 : ℝ) ≤ ‖(1 : ℝ)⁻¹ • (∑ i, Z s i)‖ := by
    intro s
    dsimp [Z]
    split_ifs <;> simp
  have hp : sdpEventProbability (fun s : Fin 2 =>
      (1 : ℝ) ≤ ‖(1 : ℝ)⁻¹ • (∑ i, Z s i)‖) = 1 := by
    unfold sdpEventProbability
    rw [Finset.filter_eq_self.mpr (fun s _ => he s)]
    norm_num
  have hf := h 1 1 2 Z 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hh hb hm
  simp only [Nat.cast_one] at hf
  rw [hp] at hf
  norm_num at hf

end Qatlib.Concepts.SdpDuality.ConeSeparation
