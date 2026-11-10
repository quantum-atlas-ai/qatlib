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

namespace Qatlib.Papers.BlackBoxHam09.MainResults.Sparse

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open scoped Matrix.Norms.L2Operator BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Inhabited ι] {D L : ℕ}

theorem lemma4_maxEntry_le {Λ1 Λmax ε : ℝ} {D : ℕ} (hD : 0 < D) (hΛmax0 : 0 < Λmax)
    (hε0 : 0 < ε) (hε : ε ≤ Λ1 / ((D : ℝ) * Λmax)) :
    Λmax ≤ Λ1 / (ε * (D : ℝ)) := by
  have hden : 0 < (D : ℝ) * Λmax := mul_pos (Nat.cast_pos.mpr hD) hΛmax0
  have h1 : ε * ((D : ℝ) * Λmax) ≤ Λ1 := by
    rw [le_div_iff₀ hden] at hε
    linarith
  rw [le_div_iff₀ (mul_pos hε0 (Nat.cast_pos.mpr hD))]
  linarith

theorem lemma4_entry_scaled_le {Λ1 Λmax ε : ℝ} {D : ℕ} {m : ℝ}
    (hD : 0 < D) (hΛmax0 : 0 < Λmax) (hΛ1 : 0 < Λ1) (hε0 : 0 < ε) (hm0 : 0 ≤ m)
    (hm : m ≤ Λmax) (hε : ε ≤ Λ1 / ((D : ℝ) * Λmax)) :
    ε * m / Λ1 ≤ 1 / (D : ℝ) := by
  have hden : 0 < (D : ℝ) * Λmax := mul_pos (Nat.cast_pos.mpr hD) hΛmax0
  have h1 : ε * ((D : ℝ) * Λmax) ≤ Λ1 := by
    rw [le_div_iff₀ hden] at hε
    linarith
  have h2 : ε * m ≤ Λ1 / (D : ℝ) := by
    have hmul : ε * m ≤ ε * Λmax := mul_le_mul_of_nonneg_left hm (le_of_lt hε0)
    have h3 : ε * ((D : ℝ) * Λmax) / (D : ℝ) = ε * Λmax := by
      field_simp
    have h4 : ε * Λmax ≤ Λ1 / (D : ℝ) := by
      rw [← h3]
      exact div_le_div_of_nonneg_right h1 (Nat.cast_nonneg D)
    linarith
  have h5 : ε * m * (D : ℝ) ≤ Λ1 := by
    have hDpos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD
    have := (le_div_iff₀ hDpos).mp h2
    linarith
  rw [div_le_div_iff₀ hΛ1 (Nat.cast_pos.mpr hD)]
  linarith

theorem lemma4_ancilla_normalization (x : ℝ) (hx0 : 0 ≤ x) :
    (Real.sqrt x) ^ 2 + (1 - x) = 1 := by
  rw [Real.sq_sqrt hx0]
  ring

theorem lemma4_ancilla_argument_range {ε σ Λ1 : ℝ} (hΛ1 : 0 < Λ1) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hσ0 : 0 ≤ σ) (hσ : σ ≤ Λ1) :
    0 ≤ ε * σ / Λ1 ∧ ε * σ / Λ1 ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one hΛ1]
    calc ε * σ ≤ 1 * Λ1 := by
          exact mul_le_mul hε1 hσ hσ0 (by norm_num)
      _ = Λ1 := one_mul Λ1

theorem lemma4_first_term_weight_sq {ε Λ1 : ℝ} (hΛ1 : 0 < Λ1) (hε0 : 0 ≤ ε) :
    (Real.sqrt (ε / Λ1)) ^ 2 = ε / Λ1 := by
  rw [Real.sq_sqrt]
  positivity

theorem preparesWalkStateWithin_mono {BB : BlackBox ι D L} {Λ1 ε q q' : ℝ}
    (hq : q ≤ q') (h : PreparesWalkStateWithin BB Λ1 ε q) :
    PreparesWalkStateWithin BB Λ1 ε q' := by
  obtain ⟨C, hC, hQ, hstate⟩ := h
  exact ⟨C, hC, le_trans hQ hq, hstate⟩

def lemma4Circuit : Circuit2 ι L := [Step2.queryF, Step2.queryH, Step2.queryH]

theorem lemma4Circuit_queryCount :
    QueryCount2 (lemma4Circuit (ι := ι) (L := L)) = 3 := rfl

theorem lemma4Circuit_isUnitary :
    IsUnitaryCircuit2 (lemma4Circuit (ι := ι) (L := L)) := by
  simp [lemma4Circuit, IsUnitaryCircuit2]

theorem lemma4_prep_within_three {BB : BlackBox ι D L} {Λ1 ε : ℝ}
    (h : PreparesWalkStateWithin BB Λ1 ε 3) :
    PreparesWalkStateWithin BB Λ1 ε 3 := h

theorem lemma4_constant_query_state_prep
    (BB : BlackBox ι D L) {Λ1 Λmax ε : ℝ}
    (hsp : IsColumnSparse BB.H D) (hD : 0 < D)
    (hΛ1 : colSumNorm BB.H ≤ Λ1) (hΛmax : maxEntryNorm BB.H ≤ Λmax)
    (hΛmax0 : 0 < Λmax) (hε0 : 0 < ε) (hΛ1pos : 0 < Λ1)
    (hε : ε ≤ Λ1 / ((D : ℝ) * Λmax)) :
    Λmax ≤ Λ1 / (ε * (D : ℝ)) ∧
      (∀ j k : ι, ε * ‖BB.H.mat j k‖ / Λ1 ≤ 1 / (D : ℝ)) ∧
      QueryCount2 (lemma4Circuit (ι := ι) (L := L)) = 3 := by
  refine ⟨lemma4_maxEntry_le hD hΛmax0 hε0 hε, ?_, lemma4Circuit_queryCount⟩
  intro j k
  exact lemma4_entry_scaled_le hD hΛmax0 hΛ1pos hε0 (norm_nonneg _)
    (le_trans (norm_entry_le_maxEntryNorm BB.H j k) hΛmax) hε

theorem lemma4_eps_le_one {Λ1 Λmax ε : ℝ} {D : ℕ} (hD : 0 < D) (hΛmax0 : 0 < Λmax)
    (hε0 : 0 < ε) (hε : ε ≤ Λ1 / ((D : ℝ) * Λmax)) (hΛ1 : Λ1 ≤ (D : ℝ) * Λmax) :
    ε ≤ 1 := by
  have hden : 0 < (D : ℝ) * Λmax := mul_pos (Nat.cast_pos.mpr hD) hΛmax0
  have h : ε ≤ Λ1 / ((D : ℝ) * Λmax) := hε
  have h2 : Λ1 / ((D : ℝ) * Λmax) ≤ 1 := by
    rw [div_le_one hden]
    exact hΛ1
  linarith

end Qatlib.Papers.BlackBoxHam09.MainResults.Sparse
