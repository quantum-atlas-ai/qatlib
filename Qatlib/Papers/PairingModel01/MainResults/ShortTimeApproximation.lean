/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PairingModel01.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PairingModel01.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
  (Operator HamiltonianEvolution hamiltonianEvolution_unitary)
open Qatlib.Concepts.TrotterFormula.LieStrang (pfComm pfLie)

noncomputable def shortTimeProduct (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (τ : ℝ) :
    Operator (2 ^ N) :=
  HamiltonianEvolution (pairingH0 N ε) τ * HamiltonianEvolution (pairingHI N V) τ

theorem eq2_short_time_step (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (τ : ℝ) :
    ‖HamiltonianEvolution (pairingH0 N ε) τ * HamiltonianEvolution (pairingHI N V) τ
        - HamiltonianEvolution (pairingHp N ε V) τ‖
      ≤ τ ^ 2 / 2 * ‖pfComm (pairingH0 N ε) (pairingHI N V)‖ := by
  have h := Qatlib.Concepts.TrotterFormula.LieStrang.product_formula_lie_two_term
    (2 ^ N) (pairingHI N V) (pairingH0 N ε) τ
    (pairingHI_isHermitian N V) (pairingH0_isHermitian N ε)
  have h' : ‖pfLie (pairingHI N V) (pairingH0 N ε) τ
        - HamiltonianEvolution (pairingH0 N ε + pairingHI N V) τ‖
      ≤ τ ^ 2 / 2 * ‖pfComm (pairingH0 N ε) (pairingHI N V)‖ := by
    rw [add_comm (pairingHI N V) (pairingH0 N ε)] at h
    exact h
  unfold pairingHp
  simpa [pfLie] using! h'

theorem eq2_paper_form (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) (τ : ℝ) :
    ‖shortTimeProduct N ε V τ - HamiltonianEvolution (pairingHp N ε V) τ‖
      ≤ τ ^ 2 / 2 * ‖pfComm (pairingH0 N ε) (pairingHI N V)‖ := by
  simpa [shortTimeProduct] using! eq2_short_time_step N ε V τ

theorem eq2_error_bound_quadratic (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ) :
    ∀ τ : ℝ, ‖shortTimeProduct N ε V τ - HamiltonianEvolution (pairingHp N ε V) τ‖
      ≤ (‖pfComm (pairingH0 N ε) (pairingHI N V)‖ / 2 + 1) * τ ^ 2 := by
  intro τ
  have h := eq2_paper_form N ε V τ
  have hsq : (0 : ℝ) ≤ τ ^ 2 := sq_nonneg τ
  have hc : (0 : ℝ) ≤ ‖pfComm (pairingH0 N ε) (pairingHI N V)‖ := norm_nonneg _
  nlinarith [h, hsq, hc]

theorem shortTimeProduct_mem_unitaryGroup (N : ℕ) (ε : Fin N → ℝ) (V : Fin N → Fin N → ℝ)
    (τ : ℝ) : shortTimeProduct N ε V τ ∈ Matrix.unitaryGroup (Fin (2 ^ N)) ℂ :=
  mul_mem (hamiltonianEvolution_unitary (pairingH0_isHermitian N ε) τ)
    (hamiltonianEvolution_unitary (pairingHI_isHermitian N V) τ)

end Qatlib.Papers.PairingModel01.MainResults
