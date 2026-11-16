/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DynamicProg24.MainResults.SourceModel
public import Mathlib.Tactic.NormNum

@[expose] public section


set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DynamicProg24.MainResults.SourceChecks

open Qatlib.Papers.DynamicProg24.MainResults
open scoped BigOperators

/-- The tensor-power expression used in the legacy polynomial contract. -/
def kronPow {n : ℕ} (d : ℕ) (ρ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ :=
  fun f g => ∏ k, ρ (f k) (g k)

/-- A positive tensor power vanishes on the zero matrix in dimension one. -/
theorem kron_one_zero : kronPow 1 (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  ext f g
  simp [kronPow]

/-- The constant polynomial one has no linear tensor lift on all matrices at degree one. -/
theorem no_const_lift :
    ¬ ∃ N : Matrix (Fin 1 → Fin 1) (Fin 1 → Fin 1) ℂ →ₗ[ℂ]
        Matrix (Fin 1) (Fin 1) ℂ,
      ∀ ρ : Matrix (Fin 1) (Fin 1) ℂ, N (kronPow 1 ρ) = 1 := by
  rintro ⟨N, hN⟩
  have h := hN 0
  rw [kron_one_zero, map_zero] at h
  have hc := congrFun (congrFun h 0) 0
  norm_num at hc

/-- The DME target is impossible when the requested decrement exceeds the positive input bound. -/
theorem dme_negative_target (τ ρ : Matrix (Fin 1) (Fin 1) ℂ) :
    ¬ traceDistance τ ρ ≤ (1 : ℝ) - 8 / 4 := by
  have hp := traceDistance_nonneg τ ρ
  norm_num
  linarith

end Qatlib.Papers.DynamicProg24.MainResults.SourceChecks
