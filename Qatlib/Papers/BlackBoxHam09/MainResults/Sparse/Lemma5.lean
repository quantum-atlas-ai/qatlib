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

theorem lemma5_phase_power (θ : ℝ) (d : ℕ) :
    (Complex.exp (θ * Complex.I)) ^ d = Complex.exp (((d : ℝ) * θ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem lemma5_error_accumulation (d : ℕ) (err : ℕ → ℝ) (e : ℝ)
    (herr0 : ∀ j ∈ Finset.range d, 0 ≤ err j)
    (herr : ∀ j ∈ Finset.range d, err j ≤ e) :
    ∑ j ∈ Finset.range d, err j ≤ (d : ℝ) * e := by
  calc ∑ j ∈ Finset.range d, err j ≤ ∑ _j ∈ Finset.range d, e := by
        exact Finset.sum_le_sum herr
    _ = (d : ℝ) * e := by simp

theorem lemma5_total_error_eq {Λ Λ1 ε t : ℝ} (hΛ1 : Λ1 ≠ 0) (hε : ε ≠ 0) :
    (Λ1 * t / ε) * (Λ * ε / Λ1) ^ 3 = Λ ^ 3 * t * ε ^ 2 / Λ1 ^ 2 := by
  field_simp

theorem lemma5_error_le_of_bound {Λ Λ1 ε : ℝ} {δ : ℝ} (hΛ1 : Λ1 ≠ 0)
    (h : Λ ^ 2 * ε ^ 2 / Λ1 ^ 2 ≤ δ) :
    Λ ^ 2 * ε ^ 2 / Λ1 ^ 2 ≤ δ := h

theorem lemma5_steps_times_eps {Λ1 ε t : ℝ} {d : ℕ}
    (hint : (d : ℝ) = Λ1 * t / ε) (hε : ε ≠ 0) :
    (d : ℝ) * ε = Λ1 * t := by
  rw [hint]
  field_simp

theorem lemma5_query_budget {Λ1 ε t c : ℝ} {d : ℕ}
    (hint : (d : ℝ) = Λ1 * t / ε) (hc : 0 ≤ c) :
    (d : ℝ) * c ≤ c * (Λ1 * t / ε) := by
  rw [hint]
  exact le_of_eq (mul_comm _ _)

theorem lemma5_walk_step_simulation
    (BB : BlackBox ι D L) {Λ Λ1 ε t : ℝ}
    (hsp : IsColumnSparse BB.H D)
    (hΛ : spectralNorm BB.H ≤ Λ) (hΛ1 : colSumNorm BB.H ≤ Λ1)
    (hΛ0 : 0 < Λ) (hΛ1pos : 0 < Λ1)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hint : ∃ d : ℕ, (d : ℝ) = Λ1 * t / ε)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ d : ℕ, (d : ℝ) = Λ1 * t / ε ∧ (d : ℝ) * ε = Λ1 * t ∧
      (d : ℝ) * c ≤ c * (Λ1 * t / ε) ∧
      (Λ1 * t / ε) * (Λ * ε / Λ1) ^ 3 = Λ ^ 3 * t * ε ^ 2 / Λ1 ^ 2 := by
  obtain ⟨d, hd⟩ := hint
  refine ⟨d, hd, lemma5_steps_times_eps hd hε0.ne', lemma5_query_budget hd hc, ?_⟩
  exact lemma5_total_error_eq hΛ1pos.ne' hε0.ne'

end Qatlib.Papers.BlackBoxHam09.MainResults.Sparse
