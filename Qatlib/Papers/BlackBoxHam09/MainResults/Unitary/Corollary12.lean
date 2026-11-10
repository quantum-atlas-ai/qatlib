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

theorem corollary12_eq_lemma8 {N : ℕ} {Λ1 Λmax δ : ℝ} :
    lemma8QueryExpr 1 Λ1 Λmax N (Real.pi / 2) δ =
      Real.rpow (Real.pi / 2) (3 / 2) * corollary12QueryExpr N Λ1 Λmax δ := by
  unfold lemma8QueryExpr corollary12QueryExpr
  rw [mul_one]

theorem corollary12_sqrt_delta_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.sqrt δ ≤ Real.pi / 2 := by
  have hs1 : Real.sqrt δ ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hδ1
  have hpi : (1 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.two_le_pi]
  linarith

theorem corollary12_query_pos {N : ℕ} {Λ1 Λmax δ : ℝ} (hN : 0 < N) (hΛ1 : 0 < Λ1)
    (hΛmax : 0 < Λmax) (hδ : 0 < δ) :
    0 < corollary12QueryExpr N Λ1 Λmax δ := by
  unfold corollary12QueryExpr
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  exact Real.sqrt_pos.mpr (by positivity)

theorem corollary12_query_transfer {N : ℕ} [Inhabited (Fin N)] {L : ℕ}
    {Λ1 Λmax δ c q : ℝ} (hc : 0 < c) (BB : BlackBox (Bool × Fin N) N L)
    (hsim : SimulableWithin BB (Real.pi / 2) δ q)
    (hq : q ≤ c * lemma8QueryExpr 1 Λ1 Λmax N (Real.pi / 2) δ) :
    SimulableWithin BB (Real.pi / 2) δ
      ((c * Real.rpow (Real.pi / 2) (3 / 2)) * corollary12QueryExpr N Λ1 Λmax δ) := by
  refine simulableWithin_mono le_rfl ?_ hsim
  calc q ≤ c * lemma8QueryExpr 1 Λ1 Λmax N (Real.pi / 2) δ := hq
    _ = (c * Real.rpow (Real.pi / 2) (3 / 2)) * corollary12QueryExpr N Λ1 Λmax δ := by
        rw [corollary12_eq_lemma8]
        ring

theorem corollary12_unitary_implementation
    {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hN : 0 < N) [Inhabited (Fin N)] {Λ1 Λmax δ : ℝ}
    (hΛ1 : unitaryColSumBound U Λ1) (hΛmax : unitaryMaxEntry U ≤ Λmax)
    (hΛ1pos : 0 < Λ1) (hΛmax0 : 0 < Λmax)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {c q : ℝ} (hc : 0 < c) {L : ℕ} (BB : BlackBox (Bool × Fin N) N L)
    (henc : BlockEncodes BB U)
    (hsim : SimulableWithin BB (Real.pi / 2) δ q)
    (hq : q ≤ c * lemma8QueryExpr 1 Λ1 Λmax N (Real.pi / 2) δ) :
    Real.sqrt δ ≤ Real.pi / 2 ∧ 0 < corollary12QueryExpr N Λ1 Λmax δ ∧
      SimulableWithin BB (Real.pi / 2) δ
        ((c * Real.rpow (Real.pi / 2) (3 / 2)) * corollary12QueryExpr N Λ1 Λmax δ) :=
  ⟨corollary12_sqrt_delta_le hδ0 hδ1, corollary12_query_pos hN hΛ1pos hΛmax0 hδ0,
    corollary12_query_transfer hc BB hsim hq⟩

end Qatlib.Papers.BlackBoxHam09.MainResults.Unitary
