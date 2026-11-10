/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BlackBoxHam09.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {N : ℕ}

theorem loglogSafe_nonneg (N : ℕ) : 0 ≤ loglogSafe N := by
  unfold loglogSafe
  exact le_trans zero_le_one (le_max_left _ _)

theorem corollary3_eq_theorem2 {δ : ℝ} :
    theorem2QueryExpr 1 N (Real.pi / 2) δ =
      Real.rpow (Real.pi / 2) (4 / 3) * corollary3QueryExpr N δ := by
  unfold theorem2QueryExpr corollary3QueryExpr
  rw [mul_one]
  have hmul : Real.rpow (loglogSafe N * (Real.pi / 2)) (4 / 3) =
      Real.rpow (loglogSafe N) (4 / 3) * Real.rpow (Real.pi / 2) (4 / 3) :=
    Real.mul_rpow (loglogSafe_nonneg N) (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  rw [hmul]
  ring

theorem corollary3_query_pos {δ : ℝ} (hN : 0 < N) (hδ : 0 < δ) :
    0 < corollary3QueryExpr N δ := by
  unfold corollary3QueryExpr
  have h1 : 0 < Real.rpow (N : ℝ) (2 / 3) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  have hL : 0 < loglogSafe N := by
    unfold loglogSafe
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h2 : 0 < Real.rpow (loglogSafe N) (4 / 3) :=
    Real.rpow_pos_of_pos hL _
  have h3 : 0 < Real.rpow δ (-(1 / 3)) := Real.rpow_pos_of_pos hδ _
  positivity

theorem corollary3_query_transfer [Inhabited (Fin N)] {L : ℕ} {δ c q : ℝ}
    (hc : 0 < c) (BB : BlackBox (Bool × Fin N) N L)
    (hsim : SimulableWithin BB (Real.pi / 2) δ q)
    (hq : q ≤ c * theorem2QueryExpr 1 N (Real.pi / 2) δ) :
    SimulableWithin BB (Real.pi / 2) δ
      ((c * Real.rpow (Real.pi / 2) (4 / 3)) * corollary3QueryExpr N δ) := by
  refine simulableWithin_mono le_rfl ?_ hsim
  calc q ≤ c * theorem2QueryExpr 1 N (Real.pi / 2) δ := hq
    _ = (c * Real.rpow (Real.pi / 2) (4 / 3)) * corollary3QueryExpr N δ := by
        rw [corollary3_eq_theorem2]
        ring

theorem corollary3_unitary_implementation
    (U : Matrix (Fin N) (Fin N) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hN : 0 < N) [Inhabited (Fin N)] {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {c q : ℝ} (hc : 0 < c) {L : ℕ} (BB : BlackBox (Bool × Fin N) N L)
    (henc : BlockEncodes BB U)
    (hsim : SimulableWithin BB (Real.pi / 2) δ q)
    (hq : q ≤ c * theorem2QueryExpr 1 N (Real.pi / 2) δ) :
    0 < corollary3QueryExpr N δ ∧
      SimulableWithin BB (Real.pi / 2) δ
        ((c * Real.rpow (Real.pi / 2) (4 / 3)) * corollary3QueryExpr N δ) :=
  ⟨corollary3_query_pos hN hδ0, corollary3_query_transfer hc BB hsim hq⟩

end Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse
