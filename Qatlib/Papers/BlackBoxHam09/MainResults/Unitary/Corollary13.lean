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

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Unitary

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

theorem corollary13_eq_theorem9 {N : ℕ} {Υ δ : ℝ} :
    theorem9QueryExpr 1 Υ N (Real.pi / 2) δ =
      Real.rpow (Real.pi / 2) (3 / 2) * corollary13QueryExpr N Υ δ := by
  unfold theorem9QueryExpr corollary13QueryExpr
  rw [one_mul]
  ring

theorem corollary13_sqrt_delta_le {N : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcond : Real.pi / 2 < δ * (N : ℝ)) :
    Real.sqrt δ ≤ δ * (N : ℝ) := by
  have hs1 : Real.sqrt δ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hδ1
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  linarith

theorem corollary13_query_pos {N : ℕ} {Υ δ : ℝ} (hN : 0 < N) (hΥpos : 0 < Υ)
    (hδ : 0 < δ) :
    0 < corollary13QueryExpr N Υ δ := by
  unfold corollary13QueryExpr
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have h1 : 0 < Real.sqrt (Υ * (N : ℝ) / δ) :=
    Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.rpow (logSafe N) (7 / 4) :=
    Real.rpow_pos_of_pos (by unfold logSafe; positivity) _
  positivity

theorem corollary13_query_transfer {N : ℕ} [Inhabited (Fin N)] {L : ℕ}
    {Υ δ c q : ℝ} (hc : 0 < c) (BB : BlackBox (Bool × Fin N) N L)
    (hsim : SimulableWithin BB (Real.pi / 2) δ q)
    (hq : q ≤ c * theorem9QueryExpr 1 Υ N (Real.pi / 2) δ) :
    SimulableWithin BB (Real.pi / 2) δ
      ((c * Real.rpow (Real.pi / 2) (3 / 2)) * corollary13QueryExpr N Υ δ) := by
  refine simulableWithin_mono le_rfl ?_ hsim
  calc q ≤ c * theorem9QueryExpr 1 Υ N (Real.pi / 2) δ := hq
    _ = (c * Real.rpow (Real.pi / 2) (3 / 2)) * corollary13QueryExpr N Υ δ := by
        rw [corollary13_eq_theorem9]
        ring

theorem corollary13_unitary_implementation
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hN : 0 < N) [Inhabited (Fin N)] {Υ δ : ℝ}
    (hΥN : Υ ≤ (N : ℝ)) (hΥpos : 0 < Υ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hcond : Real.pi / 2 < δ * (N : ℝ))
    {c q : ℝ} (hc : 0 < c) {L : ℕ} (BB : BlackBox (Bool × Fin N) N L)
    (henc : BlockEncodes BB U) (hbreak : breakNorm BB.H ≤ Υ)
    (hsim : SimulableWithin BB (Real.pi / 2) δ q)
    (hq : q ≤ c * theorem9QueryExpr 1 Υ N (Real.pi / 2) δ) :
    Real.sqrt δ ≤ δ * (N : ℝ) ∧ 0 < corollary13QueryExpr N Υ δ ∧
      SimulableWithin BB (Real.pi / 2) δ
        ((c * Real.rpow (Real.pi / 2) (3 / 2)) * corollary13QueryExpr N Υ δ) :=
  ⟨corollary13_sqrt_delta_le hδ0 hδ1 hcond, corollary13_query_pos hN hΥpos hδ0,
    corollary13_query_transfer hc BB hsim hq⟩

end Qatlib.Papers.BlackBoxHam09.MainResults.Unitary
