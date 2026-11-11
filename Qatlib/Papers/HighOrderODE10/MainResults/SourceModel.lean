/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# HighOrderODE10 — source model for Berry's high-order ODE algorithm

Fixed source: Dominic W. Berry, *High-order quantum algorithm for solving
linear differential equations*, arXiv:1010.2745v2 (28 Jan 2014).

This module records the numerical-analysis vocabulary shared by the six active
claims of the block `MainResults`.  The paper works with operator norms of a
block matrix `𝓐` built from the linear multistep method (Eq. (27)) and with the
scalar error/stability recursions of Hairer--Wanner's Chapter V.  The paper
layer formalises those quantities as real-valued *source quantities* (norm
proxies) that satisfy the exact inequalities displayed in the paper; the
mapping is recorded in each definition and theorem docstring.  The underlying
frozen/Dev layer has no formalisation of stiff-ODE matrix analysis, so the
model below is deliberately self-contained and does not silently import a
stronger assumption than the paper's own displayed bounds.

Conventions:

* coefficients are indexed by `ℕ` through `alphaAt`/`betaAt`, with the
  convention `α_j = 0` for `j > k`;
* `sourceBlockBound` is the right-hand side of Eq. (34);
* `sourceKappaV` is `κ_V = ‖V‖·‖V⁻¹‖` (condition number of the
  diagonalising matrix), Eq. (19).

This module contains only ordinary definitions and structures checked by the
kernel; it introduces no custom logical assumptions and no compiler-level
escape mechanisms.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HighOrderODE10.MainResults

open Finset
open scoped BigOperators

/-- A fixed linear `k`-step multistep method of Eq. (9):

`∑_{ℓ=0}^{k} α_ℓ x_{j+ℓ} = h ∑_{ℓ=0}^{k} β_ℓ (A x_{j+ℓ} + b)`.

`order` is the paper's order `p` (`ρ(e^h) - hσ(e^h) = O(h^{p+1})`, Eq. (13));
`hk` records that the method is at least one step, as required by the
`j ≥ k` rows of Eq. (27). -/
structure SourceMultistepMethod where
  /-- Number of steps `k`. -/
  k : ℕ
  /-- A method has at least one step (`k ≥ 1`). -/
  hk : 0 < k
  /-- Coefficients `α_0, …, α_k` of Eq. (9). -/
  alpha : Fin (k + 1) → ℝ
  /-- Coefficients `β_0, …, β_k` of Eq. (9). -/
  beta : Fin (k + 1) → ℝ
  /-- The order `p` of the method (Eq. (13)). -/
  order : ℕ

/-- `α_j` of the method, with `α_j = 0` for an out-of-range index. -/
def alphaAt (m : SourceMultistepMethod) (j : ℕ) : ℝ :=
  if h : j ≤ m.k then m.alpha ⟨j, Nat.lt_succ_of_le h⟩ else 0

/-- `β_j` of the method, with `β_j = 0` for an out-of-range index. -/
def betaAt (m : SourceMultistepMethod) (j : ℕ) : ℝ :=
  if h : j ≤ m.k then m.beta ⟨j, Nat.lt_succ_of_le h⟩ else 0

/-- The coefficient index paired with the `ℓ`-th block of Eq. (34):
`ℓ = 0 ↦ k`, `ℓ = 1 ↦ k − 1`, `ℓ ≥ 2 ↦ ℓ`. -/
def sourceCoefIndex (m : SourceMultistepMethod) (ℓ : ℕ) : ℕ :=
  if ℓ = 0 then m.k else if ℓ = 1 then m.k - 1 else ℓ

/-- The right-hand side of Eq. (34): a bound on the operator norm of the
`ℓ`-th block-diagonal piece `𝓐^{ℓ}` (Eq. (31)), in terms of the method
coefficients, the step `h` and `M = ‖A‖`.  For `ℓ = 0` the paper's bound is
`max (1) (|α_k| + |β_k| h M)`; for `ℓ = 1` it is
`max (1 + hM) (|α_{k-1}| + |β_{k-1}| h M)`; for `1 < ℓ ≤ k` it is
`|α_ℓ| + |β_ℓ| h M`.  The `max` against `0` in the general branch is
harmless because the second argument is nonnegative. -/
def sourceBlockBound (m : SourceMultistepMethod) (h M : ℝ) (ℓ : ℕ) : ℝ :=
  max (if ℓ = 0 then 1 else if ℓ = 1 then 1 + h * M else 0)
    (|alphaAt m (sourceCoefIndex m ℓ)| +
      |betaAt m (sourceCoefIndex m ℓ)| * h * M)

/-- Uniform upper bound for one block of Eq. (34) when `0 ≤ h` and `hM ≤ 1`:
`2 + |α| + |β|`.  This is the constant used by Lemma 5 to conclude
`‖𝓐‖ = O(1)`. -/
def sourceBlockCap (m : SourceMultistepMethod) (ℓ : ℕ) : ℝ :=
  2 + |alphaAt m (sourceCoefIndex m ℓ)| + |betaAt m (sourceCoefIndex m ℓ)|

/-- The `O(1)` constant of Lemma 5:
`∑_{ℓ=0}^{k} (2 + |α_ℓ| + |β_ℓ|)`, which depends only on the method. -/
def sourceNormCap (m : SourceMultistepMethod) : ℝ :=
  ∑ ℓ ∈ range (m.k + 1), sourceBlockCap m ℓ

/-- The condition number `κ_V = ‖V‖·‖V⁻¹‖` of Eq. (19) (paper: the condition
number of the diagonalising matrix `V`).  It is stored as a real number; the
model never needs the individual factors `‖V‖`, `‖V⁻¹‖`. -/
def sourceKappaV (normV normVinv : ℝ) : ℝ := normV * normVinv

/-- The right-hand side of Lemma 6 / Theorem 7: `O(N_t κ_V)`. -/
def sourceConditionBound (Nt kappaV : ℝ) : ℝ := Nt * kappaV

/-- The leading expression inside the big-O of Lemma 4, Eq. (19):
`κ_V² (‖x_init‖ + ‖b‖/‖A‖) [κ_V (h‖A‖)² + m (h‖A‖)^{p+1}]`.  Kept as a
definitions so the claim's statement and its asymptotic reading agree. -/
def sourceGlobalErrorExpr (kappaV h M xinitNorm bNorm : ℝ) (p m : ℕ) : ℝ :=
  kappaV ^ 2 * (xinitNorm + bNorm / M) *
    (kappaV * (h * M) ^ 2 + (m : ℝ) * (h * M) ^ (p + 1))

/-- Oracle-call ledger for the state preparation of Lemma 8 (Eq. (56)):
the `b`-register, the `x_in`-register and the time-superposition register. -/
structure SourcePrepLedger where
  /-- Calls charged to preparing the `b` superposition. -/
  bCalls : ℕ
  /-- Calls charged to preparing the `x_in` superposition. -/
  xinCalls : ℕ
  /-- Calls charged to preparing the uniform time superposition. -/
  timeCalls : ℕ

/-- Total number of oracle calls of the three-register preparation. -/
def SourcePrepLedger.total (L : SourcePrepLedger) : ℕ :=
  L.bCalls + L.xinCalls + L.timeCalls

/-- The state-preparation cost of Lemma 8, `O(√s + log N_t)`. -/
def sourcePrepCostExpr (s Nt : ℝ) : ℝ := Real.sqrt s + Real.log Nt

/-- The main-query-cost expression of Theorem 9, Eq. (59), without the
polylogarithmic factor: `log(N_x) s^{9/2} (‖A‖Δt)^{2+2/p} κ_V^5
(‖x_in‖ + ‖b‖/‖A‖) / ε^2`. -/
def sourceMainCostExpr (Nx s M Δt kappaV xinNorm bNorm ε p : ℝ) : ℝ :=
  Real.log Nx * s ^ (9 / 2 : ℝ) * (M * Δt) ^ (2 + 2 / p) * kappaV ^ 5 *
    (xinNorm + bNorm / M) / ε ^ 2

end Qatlib.Papers.HighOrderODE10.MainResults
