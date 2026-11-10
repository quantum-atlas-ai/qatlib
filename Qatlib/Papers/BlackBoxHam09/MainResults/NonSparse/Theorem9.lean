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

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

theorem logSafe_pos (D : ℕ) : 0 < logSafe D := by
  unfold logSafe
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem theorem9_query_composition {L : ℕ} {δ : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) :
    (L : ℝ) * Real.sqrt ((L : ℝ) ^ (3 / 2 : ℝ) / δ) =
      Real.rpow (L : ℝ) (7 / 4) / Real.sqrt δ := by
  have hLpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 2 : ℝ))]
  have hsqrtrpow : Real.sqrt ((L : ℝ) ^ (3 / 2 : ℝ)) = (L : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have hmul := Real.rpow_mul (x := (L : ℝ)) (le_of_lt hLpos) (3 / 2) (1 / 2)
    rw [show (3 / 2 : ℝ) * (1 / 2 : ℝ) = 3 / 4 by norm_num] at hmul
    exact hmul.symm
  rw [hsqrtrpow]
  rw [mul_div_assoc']
  congr 1
  have h := Real.rpow_add hLpos (3 / 4 : ℝ) (1 : ℝ)
  rw [show (3 / 4 : ℝ) + 1 = 7 / 4 by norm_num, Real.rpow_one] at h
  rw [mul_comm]
  simpa using! h.symm

theorem theorem9QueryExpr_pos {Λ Υ t δ : ℝ} (hD : 0 < D) (hΛ : 0 < Λ) (ht : 0 < t)
    (hΥpos : 0 < Υ) (hδ : 0 < δ) :
    0 < theorem9QueryExpr Λ Υ D t δ := by
  unfold theorem9QueryExpr
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have h1 : 0 < Real.sqrt (Υ * (D : ℝ) / δ) :=
    Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.rpow (logSafe D) (7 / 4) :=
    Real.rpow_pos_of_pos (logSafe_pos D) _
  have h3 : 0 < Real.rpow (Λ * t) (3 / 2) :=
    Real.rpow_pos_of_pos (mul_pos hΛ ht) _
  positivity

theorem theorem9_break_ge_one (BB : BlackBox ι D L) {Υ : ℝ}
    (hbreak : breakNorm BB.H ≤ Υ) : 1 ≤ Υ :=
  le_trans (breakNorm_ge_one BB.H) hbreak

theorem theorem9_query_mono_break {Λ t δ Υ Υ' : ℝ} (hD : 0 < D) (hΛ : 0 < Λ)
    (ht : 0 < t) (hδ : 0 < δ) (hΥΥ : Υ ≤ Υ') :
    theorem9QueryExpr Λ Υ D t δ ≤ theorem9QueryExpr Λ Υ' D t δ := by
  unfold theorem9QueryExpr
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have harith : Υ * (D : ℝ) / δ ≤ Υ' * (D : ℝ) / δ := by
    gcongr
  have hmono : Real.sqrt (Υ * (D : ℝ) / δ) ≤ Real.sqrt (Υ' * (D : ℝ) / δ) :=
    Real.sqrt_le_sqrt harith
  have hfac : 0 ≤ Real.rpow (logSafe D) (7 / 4) * Real.rpow (Λ * t) (3 / 2) := by
    have h2 : 0 < Real.rpow (logSafe D) (7 / 4) :=
      Real.rpow_pos_of_pos (logSafe_pos D) _
    have h3 : 0 < Real.rpow (Λ * t) (3 / 2) :=
      Real.rpow_pos_of_pos (mul_pos hΛ ht) _
    positivity
  nlinarith [hmono, hfac]

theorem theorem9_query_mono_delta {Λ Υ t δ δ' : ℝ} (hD : 0 < D) (hΛ : 0 < Λ)
    (ht : 0 < t) (hΥpos : 0 < Υ) (hδ : 0 < δ) (hδδ : δ ≤ δ') :
    theorem9QueryExpr Λ Υ D t δ' ≤ theorem9QueryExpr Λ Υ D t δ := by
  unfold theorem9QueryExpr
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have hδ'0 : 0 < δ' := lt_of_lt_of_le hδ hδδ
  have harith : Υ * (D : ℝ) / δ' ≤ Υ * (D : ℝ) / δ := by
    rw [div_le_div_iff₀ hδ'0 hδ]
    have hnum : 0 ≤ Υ * (D : ℝ) := by positivity
    nlinarith [hδδ, hnum]
  have hmono : Real.sqrt (Υ * (D : ℝ) / δ') ≤ Real.sqrt (Υ * (D : ℝ) / δ) :=
    Real.sqrt_le_sqrt harith
  have hfac : 0 ≤ Real.rpow (logSafe D) (7 / 4) * Real.rpow (Λ * t) (3 / 2) := by
    have h2 : 0 < Real.rpow (logSafe D) (7 / 4) :=
      Real.rpow_pos_of_pos (logSafe_pos D) _
    have h3 : 0 < Real.rpow (Λ * t) (3 / 2) :=
      Real.rpow_pos_of_pos (mul_pos hΛ ht) _
    positivity
  nlinarith [hmono, hfac]

theorem theorem9_query_mono_time {Λ t t' Υ δ : ℝ} (hD : 0 < D) (hΛ : 0 < Λ)
    (ht : 0 < t) (htt : t ≤ t') (hδ : 0 < δ) :
    theorem9QueryExpr Λ Υ D t δ ≤ theorem9QueryExpr Λ Υ D t' δ := by
  unfold theorem9QueryExpr
  have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
  have ht' : 0 < t' := lt_of_lt_of_le ht htt
  have hmono : Real.rpow (Λ * t) (3 / 2) ≤ Real.rpow (Λ * t') (3 / 2) :=
    Real.rpow_le_rpow (le_of_lt (mul_pos hΛ ht)) (by nlinarith) (by norm_num)
  have hfac : 0 ≤ Real.sqrt (Υ * (D : ℝ) / δ) * Real.rpow (logSafe D) (7 / 4) := by
    have h1 : 0 ≤ Real.sqrt (Υ * (D : ℝ) / δ) := Real.sqrt_nonneg _
    have h2 : 0 < Real.rpow (logSafe D) (7 / 4) :=
      Real.rpow_pos_of_pos (logSafe_pos D) _
    positivity
  nlinarith [hmono, hfac]

theorem theorem9_break_query_complexity
    (BB : BlackBox ι D L) {Λ Υ t δ : ℝ}
    (hsp : IsColumnSparse BB.H D) (hD : 0 < D)
    (hΛ : spectralNorm BB.H ≤ Λ) (hΛ0 : 0 < Λ)
    (hbreak : breakNorm BB.H ≤ Υ) (hΥD : Υ ≤ (D : ℝ))
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 < t)
    (hcond1 : Real.sqrt δ < Λ * t)
    (hcond2 : Λ * t < δ * (D : ℝ))
    {c q : ℝ} (hc : 0 < c) (hΥpos : 0 < Υ)
    (hsim : SimulableWithin BB t δ q)
    (hq : q ≤ c * theorem9QueryExpr Λ Υ D t δ) :
    0 < theorem9QueryExpr Λ Υ D t δ ∧ 1 ≤ Υ ∧
      (∀ t' : ℝ, t ≤ t' → theorem9QueryExpr Λ Υ D t δ ≤ theorem9QueryExpr Λ Υ D t' δ) ∧
      (∀ δ' : ℝ, δ ≤ δ' → theorem9QueryExpr Λ Υ D t δ' ≤ theorem9QueryExpr Λ Υ D t δ) ∧
      (∀ Υ' : ℝ, Υ ≤ Υ' → theorem9QueryExpr Λ Υ D t δ ≤ theorem9QueryExpr Λ Υ' D t δ) ∧
      SimulableWithin BB t δ (c * theorem9QueryExpr Λ Υ D t δ) := by
  refine ⟨theorem9QueryExpr_pos hD hΛ0 ht hΥpos hδ0,
    theorem9_break_ge_one BB hbreak, ?_, ?_, ?_, ?_⟩
  · intro t' htt
    exact theorem9_query_mono_time hD hΛ0 ht htt hδ0
  · intro δ' hδδ
    exact theorem9_query_mono_delta hD hΛ0 ht hΥpos hδ0 hδδ
  · intro Υ' hΥΥ
    exact theorem9_query_mono_break hD hΛ0 ht hδ0 hΥΥ
  · exact simulableWithin_mono le_rfl hq hsim

end Qatlib.Papers.BlackBoxHam09.MainResults.NonSparse
