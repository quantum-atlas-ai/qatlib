/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Historical smooth-limit model and its genuine elementary algebra

Fixed actual source: arXiv1011.3489v2. The old four-log proxy and
pointwise near-linear predicate are preserved for full-contract auditing.
Neither is an asymptotic source query-complexity theorem.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QDynamics10.MainResults.SmoothModel

/-- The exact historical four-fold logarithm proxy, retained without claiming a global iterated-logarithm comparison. -/
def logStar (n : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 (Nat.log 2 (Nat.log 2 n + 1) + 1) + 1) + 1

/-- The historical pointwise cost predicate, retained for the full old-contract counterexample;
it does not encode the source asymptotic statement or its multiplicative constant. -/
def NearLinear (Q n nH M d : ℕ) (Υbar Δt ε : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ k : ℕ, 1 ≤ k ∧ (1 : ℝ) / (2 * (k : ℝ)) ≤ δ ∧
      (Q : ℝ) ≤ ((n : ℝ) * (logStar n : ℝ) + (nH : ℝ)) * (M : ℝ) * ((d : ℝ) ^ 4)
        * Υbar * Δt * ((d : ℝ) ^ 2 * Υbar * Δt / ε) ^ δ

/-- `(d²)·(d²) = d⁴`: the regrouping used in (19) (`M d²` from Eq. (17) times the `d²` of
the exponent base gives `M d⁴`). -/
theorem squareProduct (d : ℕ) : ((d : ℝ) ^ 2) * ((d : ℝ) ^ 2) = (d : ℝ) ^ 4 := by
  ring

/-- Exponent selection: for every `δ > 0` there is `k ≥ 1` with `1/(2k) ≤ δ`. This is the
elementary content of taking `k → ∞` in Corollary 3; the paper's concrete choice is
Eq. (73). -/
theorem smallExponent (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ (1 : ℝ) / (2 * (k : ℝ)) ≤ δ := by
  refine ⟨Nat.ceil (1 / (2 * δ)) + 1, by omega, ?_⟩
  have hceil : 1 / (2 * δ) ≤ ((Nat.ceil (1 / (2 * δ)) : ℕ) : ℝ) := Nat.le_ceil _
  have hpos : (0 : ℝ) < 2 * δ := by positivity
  have hk1 : (1 : ℝ) ≤ ((Nat.ceil (1 / (2 * δ)) + 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ Nat.ceil (1 / (2 * δ)) + 1 := by omega
    exact_mod_cast this
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((Nat.ceil (1 / (2 * δ)) + 1 : ℕ) : ℝ))]
  -- goal: `1 ≤ δ * (2 * k)`; from `k ≥ 1/(2δ)`.
  have hk : 1 / (2 * δ) ≤ ((Nat.ceil (1 / (2 * δ)) + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hthis := mul_le_mul_of_nonneg_left hk (le_of_lt hpos)
  have hcancel : 2 * δ * (1 / (2 * δ)) = 1 := by
    field_simp
  rw [hcancel] at hthis
  nlinarith [hthis]


end Qatlib.Papers.QDynamics10.MainResults.SmoothModel
