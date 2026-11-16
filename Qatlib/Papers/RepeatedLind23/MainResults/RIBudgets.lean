/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.RepeatedLind23.MainResults.SourceModel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-!
# Repeated-interaction budgets and second-order maps

The definitions preserve the legacy second-order truncation. Only algebraic
budget properties are proved. A corresponding GKSL generator, time-dependent
interaction scaling, and a norm remainder estimate are required before any
RI--Lindblad correspondence claim can be made.
-/

set_option autoImplicit false
noncomputable section
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Papers.RepeatedLind23.MainResults
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker
namespace Qatlib.Papers.RepeatedLind23.MainResults.RIBudgets

/-- Eq. (26) right-hand side: `(t²/ε)·(‖L‖²_{1→1} + m·max_n γ_n⁴)`. -/
def iterBudget {D m : ℕ} (hm : 0 < m) (G : GKSL D) (γ : Fin m → ℝ)
    (t ε : ℝ) : ℝ :=
  (t ^ 2 / ε) * ((lindbladOneNorm G) ^ 2 + (m : ℝ) * maxGamma4 hm γ)

/-- Eq. (27) right-hand side: `(t²/ε)·(m‖L‖²_{1→1} + m²·max_n γ_n⁴)`. -/
def mapBudget {D m : ℕ} (hm : 0 < m) (G : GKSL D) (γ : Fin m → ℝ)
    (t ε : ℝ) : ℝ :=
  (t ^ 2 / ε) * ((m : ℝ) * (lindbladOneNorm G) ^ 2 + (m : ℝ) ^ 2 * maxGamma4 hm γ)

/-- Eq. (26) ⟹ Eq. (27): multiplying the iteration bound by `m` gives the bound
on the total number `κ = mν` of repeated interactions.

This is the algebraic step the paper states after Eq. (26) ("This then implies
that the total number of RI maps `κ = mν` ... has the following upper bound",
Eq. (27)). It is proved here in full generality: if `ν ≤ C·(t²/ε)(‖L‖² +
m·max_n γ_n⁴)` with `C > 0`, then `m·ν ≤ C·(t²/ε)(m‖L‖² + m²·max_n γ_n⁴)`. -/
theorem map_count_bound
    {D m : ℕ} (hm : 0 < m) (G : GKSL D) (γ : Fin m → ℝ) (t ε C ν : ℝ)
    (_hC : 0 < C) (_hν : 0 < ν)
    (h : ν ≤ C * iterBudget hm G γ t ε) :
    (m : ℝ) * ν ≤ C * mapBudget hm G γ t ε := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmul : (m : ℝ) * ν ≤ (m : ℝ) * (C * iterBudget hm G γ t ε) :=
    mul_le_mul_of_nonneg_left h hm0
  refine le_trans hmul (le_of_eq ?_)
  unfold mapBudget iterBudget
  ring

/-- The commutator `[A,B] = AB − BA` of two square matrices. -/
def commutator {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A * B - B * A

/-- Corollary 2.2: the second-order truncation in `τ` of the repeated-interaction
step of Definition 1 / Eq. (5). Expanding `e^{-iτH}(ρ_S ⊗ ρ_E)e^{iτH}` to second
order in `τ` and tracing out the bath gives

`ρ_S − iτ·Tr_E[H, ρ_S ⊗ ρ_E] − (τ²/2)·Tr_E[H, [H, ρ_S ⊗ ρ_E]]`. -/
def secondStep {D dE : ℕ}
    (H : Matrix (Fin D × Fin dE) (Fin D × Fin dE) ℂ)
    (ρE : Matrix (Fin dE) (Fin dE) ℂ) (τ : ℝ) (ρS : Operator D) : Operator D :=
  ρS - (Complex.I * (τ : ℂ)) • (commutator H (ρS ⊗ₖ ρE)).traceRight
    - (((τ : ℂ) ^ 2 / 2) • (commutator H (commutator H (ρS ⊗ₖ ρE))).traceRight)

/-- Corollary 2.2: one pass through the `m` second-order truncated RI steps at
interaction time `τ` (the analogue of `riPass` for `secondStep`). -/
def secondPass {D dE m : ℕ}
    (H : Fin m → Matrix (Fin D × Fin dE) (Fin D × Fin dE) ℂ)
    (ρE : Fin m → Matrix (Fin dE) (Fin dE) ℂ) (τ : ℝ) (ρS : Operator D) : Operator D :=
  (List.ofFn (fun n => secondStep (H n) (ρE n) τ)).foldl
    (fun ρ f => f ρ) ρS

/-- Corollary 2.2: the `ν`-fold composition of the second-order truncated map
(the analogue of `riComposite`). -/
def secondComposite {D dE m : ℕ}
    (H : Fin m → Matrix (Fin D × Fin dE) (Fin D × Fin dE) ℂ)
    (ρE : Fin m → Matrix (Fin dE) (Fin dE) ℂ) (t : ℝ) (ν : ℕ)
    (ρS : Operator D) : Operator D :=
  (secondPass H ρE (t / (ν : ℝ)))^[ν] ρS

/-- The induced Schatten `1→1` distance between the Lindblad semigroup and the
second-order truncated repeated-interaction composite of Corollary 2.2. -/
def secondError {D dE m : ℕ} (G : GKSL D)
    (H : Fin m → Matrix (Fin D × Fin dE) (Fin D × Fin dE) ℂ)
    (ρE : Fin m → Matrix (Fin dE) (Fin dE) ℂ) (t : ℝ) (ν : ℕ) : ℝ :=
  inducedOneNorm (fun ρ => lindbladSemigroup G t ρ - secondComposite H ρE t ν ρ)

/-- Eq. (28) right-hand side: `t²/(mν)·‖H₀‖² + ‖L‖²_{1→1}·t²/ν`. -/
def secondBudget {D : ℕ} (H0 : Operator D) (G : GKSL D) (m ν : ℕ) (t : ℝ) : ℝ :=
  t ^ 2 / ((m : ℝ) * (ν : ℝ)) * ‖H0‖ ^ 2 + (lindbladOneNorm G) ^ 2 * t ^ 2 / (ν : ℝ)

/-- The second-order error budget of Eq. (28) is nonnegative at positive time,
positive iteration count and positive `m`. -/
theorem second_nonneg {D : ℕ} (H0 : Operator D) (G : GKSL D)
    {m ν : ℕ} (hm : 0 < m) (hν : 0 < ν) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ secondBudget H0 G m ν t := by
  unfold secondBudget
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hν0 : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  have ht2 : 0 ≤ t ^ 2 := pow_nonneg ht 2
  have h1 : 0 ≤ t ^ 2 / ((m : ℝ) * (ν : ℝ)) * ‖H0‖ ^ 2 :=
    mul_nonneg (div_nonneg ht2 (le_of_lt (mul_pos hm0 hν0))) (sq_nonneg ‖H0‖)
  have h2 : 0 ≤ (lindbladOneNorm G) ^ 2 * t ^ 2 / (ν : ℝ) :=
    div_nonneg (mul_nonneg (sq_nonneg _) ht2) (le_of_lt hν0)
  linarith

end Qatlib.Papers.RepeatedLind23.MainResults.RIBudgets
