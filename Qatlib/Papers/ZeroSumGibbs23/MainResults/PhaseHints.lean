/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel
public import Mathlib.Algebra.Order.Floor.Defs

@[expose] public section


/-!
# PhaseHints deterministic core

This module preserves closed algebraic and finite-dimensional source results
from arXiv:2301.03763v1. It does not assert a circuit implementation, concentration
bound, or end-to-end algorithmic complexity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.PhaseHints
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model
variable {m n N : ℕ}

/-- Invariants 1 and 2 of Section 4 (p.11) for the overestimating hint `q` at the
start of a phase: `q ≥ p_τ` entrywise, `q_j ∈ [δ/n, 1]`, and `‖q‖₁ = ρ` (at most).
Invariant 2 — that `q` keeps dominating `p_{τ+s}` throughout the phase — is the
content of Lemma 3 and enters through the `K`-iteration success event. -/
structure HintInvariant (n : ℕ) (pτ q : Fin n → ℝ) (δ ρ : ℝ) : Prop where
  dominates : ∀ j, pτ j ≤ q j
  lower : ∀ j, δ / (n : ℝ) ≤ q j
  upper : ∀ j, q j ≤ 1
  mass : l1Norm q ≤ ρ

/-- A hint satisfying Invariant 1 has nonnegative entries. -/
theorem HintInvariant.nonneg {pτ q : Fin n → ℝ} {δ ρ : ℝ} (H : HintInvariant n pτ q δ ρ)
    (hδ : 0 ≤ δ) (j : Fin n) : 0 ≤ q j :=
  le_trans (div_nonneg hδ (Nat.cast_nonneg n)) (H.lower j)

/-- The phase length `⌈1/η⌉` is positive; used to instantiate `K` in Corollary 1
and Lemma 4. -/
theorem phase_pos (η : ℝ) (hη : 0 < η) : 0 < Nat.ceil (1 / η) :=
  Nat.ceil_pos.mpr (by positivity)

end Qatlib.Papers.ZeroSumGibbs23.MainResults.PhaseHints
