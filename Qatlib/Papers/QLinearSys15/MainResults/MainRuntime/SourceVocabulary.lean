/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source vocabulary for `QLinearSys15` §2.1 (HHL main result)

Fixed source: A. W. Harrow, *Review of Quantum Algorithms for Systems of Linear
Equations*, arXiv:1501.00008v1, §2.1, PDF p. 2 (txt lines 31–39):

> The main result is that `|x⟩` and `‖x'‖` can be produced, both up to error
> `ε`, in time `poly(κ, s, ε⁻¹, log(N), T_A, T_B)`. More precisely, the
> following run-times are known:
>   `Õ(κT_B + log(N) s² κ² T_A / ε)`  [5]  (1a)
>   `Õ(κT_B + log(N) s² κ T_A / ε³)`  [1]  (1b)

The hypotheses of §2.1 are: `A` Hermitian with all eigenvalues in
`[−1, −1/κ] ∪ [1/κ, 1]`, at most `s` nonzero entries per row, a quantum
algorithm for the (nonzero entries of the) `i`-th row in time `T_A`, `‖b‖ = 1`,
and a state-preparation algorithm for `|b⟩` in time `T_B`. `x' = A⁻¹|b⟩` and
`x = x'/‖x'‖`.

This module fixes the cost model:

* `LinearSystemProblem` — the source instance and its access parameters;
* `QlsOutput` / `CostedQlsSolver` / `ProducesSolution` — "produce `|x⟩` and `‖x'‖`
  up to error `ε` at a stated cost";
* `hhlRuntimeA`, `hhlRuntimeB` — the two displayed run-times (1a), (1b);
* `hhlPolyBoundA`, `hhlPolyBoundB` — the same quantities written as explicit
  sums of monomials in `(κ, s, ε⁻¹, log N, T_A, T_B)`, i.e. the "poly(…)" form;
* `polyLogFactor` — the `Õ` factor as an explicit power of `log₂(N+2)+1`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSys15.MainResults.MainRuntime

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

/-! ## 1. The source run-times (1a) and (1b) -/

/-- The run-time (1a) of [5] (HHL 2009):
`Õ(κT_B + log(N) s² κ² T_A / ε)`, with the `Õ` polylog factor kept separate. -/
def hhlRuntimeA (κ s logN TA TB ε : ℝ) : ℝ :=
  κ * TB + logN * s ^ 2 * κ ^ 2 * TA / ε

/-- The run-time (1b) of [1] (Ambainis 2010):
`Õ(κT_B + log(N) s² κ T_A / ε³)`. -/
def hhlRuntimeB (κ s logN TA TB ε : ℝ) : ℝ :=
  κ * TB + logN * s ^ 2 * κ * TA / ε ^ 3

/-- The `poly(κ, s, ε⁻¹, log N, T_A, T_B)` form of (1a): an explicit sum of
monomials in the six source parameters. -/
def hhlPolyBoundA (κ s invε logN TA TB : ℝ) : ℝ :=
  κ * TB + logN * s ^ 2 * κ ^ 2 * TA * invε

/-- The `poly(κ, s, ε⁻¹, log N, T_A, T_B)` form of (1b). -/
def hhlPolyBoundB (κ s invε logN TA TB : ℝ) : ℝ :=
  κ * TB + logN * s ^ 2 * κ * TA * invε ^ 3

/-- Run-time (1a) is the explicit polynomial template at `invε = ε⁻¹`. -/
theorem hhl_runtimeA_poly_form (κ s logN TA TB ε : ℝ) (hε : ε ≠ 0) :
    hhlRuntimeA κ s logN TA TB ε = hhlPolyBoundA κ s ε⁻¹ logN TA TB := by
  unfold hhlRuntimeA hhlPolyBoundA
  field_simp [hε]

/-- Run-time (1b) is the explicit polynomial template at `invε = ε⁻¹`. -/
theorem hhl_runtimeB_poly_form (κ s logN TA TB ε : ℝ) (hε : ε ≠ 0) :
    hhlRuntimeB κ s logN TA TB ε = hhlPolyBoundB κ s ε⁻¹ logN TA TB := by
  unfold hhlRuntimeB hhlPolyBoundB
  field_simp [hε]

/-- The `Õ` polylog factor: `(log₂(N+2) + 1)^d`. It is a monomial in
`log N`, hence polynomial in the source parameters. -/
def polyLogFactor (N d : ℕ) : ℝ := ((Nat.log 2 (N + 2) : ℝ) + 1) ^ d

/-- The polylog factor is nonnegative. -/
theorem polyLogFactor_nonneg (N d : ℕ) : 0 ≤ polyLogFactor N d := by
  unfold polyLogFactor
  positivity

/-! ## 2. The source instance and its access parameters -/

/-- The §2.1 linear-system instance and access model: Hermitian `A` with
spectrum in `[1/κ, 1]`, `s`-sparsity, row access in time `T_A`, state
preparation of `|b⟩` in time `T_B`, and `‖b‖ = 1`. -/
structure LinearSystemProblem where
  /-- The dimension `N`. -/
  N : ℕ
  /-- `N ≥ 1`. -/
  N_pos : 0 < N
  /-- The Hermitian matrix `A`. -/
  A : Matrix (Fin N) (Fin N) ℂ
  /-- `A` is Hermitian. -/
  hermitian : Aᴴ = A
  /-- The condition number `κ`. -/
  kappa : ℝ
  /-- `κ > 0`. -/
  kappa_pos : 0 < kappa
  /-- `‖Av‖ ≥ ‖v‖/κ` for all `v`: the lower spectrum bound. -/
  spectrum_lower : ∀ v : Fin N → ℂ, v ≠ 0 → (1 / kappa) * ‖v‖ ≤ ‖A *ᵥ v‖
  /-- `‖Av‖ ≤ ‖v‖` for all `v`: the upper spectrum bound. -/
  spectrum_upper : ∀ v : Fin N → ℂ, ‖A *ᵥ v‖ ≤ ‖v‖
  /-- The sparsity `s`. -/
  sparsity : ℝ
  /-- `s > 0`. -/
  sparsity_pos : 0 < sparsity
  /-- The nonzero entries of each row. -/
  rowNonzeros : Fin N → List (Fin N × ℂ)
  /-- Each row has at most `s` nonzero entries. -/
  rowNonzero_le : ∀ i : Fin N, ((rowNonzeros i).length : ℝ) ≤ sparsity
  /-- The row-access time `T_A`. -/
  TA : ℝ
  /-- `T_A > 0`. -/
  TA_pos : 0 < TA
  /-- The state-preparation time `T_B`. -/
  TB : ℝ
  /-- `T_B > 0`. -/
  TB_pos : 0 < TB
  /-- The right-hand side `b`. -/
  b : Fin N → ℂ
  /-- `‖b‖ = 1`. -/
  b_norm : ‖b‖ = 1

/-- The exact source solution `x' = A⁻¹ b`. -/
def LinearSystemProblem.solution (P : LinearSystemProblem) : Fin P.N → ℂ :=
  P.A⁻¹ *ᵥ P.b

/-- The normalized source solution `x = x'/‖x'‖`, as a state amplitude. -/
def LinearSystemProblem.targetAmplitude (P : LinearSystemProblem) (i : Fin P.N) : ℂ :=
  P.solution i / ((‖P.solution‖ : ℝ) : ℂ)

/-! ## 3. The solver output and its cost -/

/-- One run of a linear-system solver at accuracy `ε`: the produced state and
the classical estimate of `‖x'‖`. -/
structure QlsOutput (P : LinearSystemProblem) where
  /-- The produced state `|x⟩`. -/
  state : QState (Fin P.N)
  /-- The classical estimate of `‖x'‖`. -/
  normEstimate : ℝ

/-- A costed solver for one instance: its output and its run-time as functions
of the target accuracy. -/
structure CostedQlsSolver (P : LinearSystemProblem) where
  /-- The output produced at accuracy `ε`. -/
  output : ℝ → QlsOutput P
  /-- The run-time at accuracy `ε`. -/
  cost : ℝ → ℝ

/-- **"Produce `|x⟩` and `‖x'‖` up to error `ε`."** The produced state is
within `ε` in `ℓ²` of the normalized source solution, and the classical
estimate of `‖x'‖` is within `ε`. -/
def ProducesSolution (P : LinearSystemProblem) (S : CostedQlsSolver P) (ε : ℝ) : Prop :=
  (∑ i : Fin P.N, ‖(S.output ε).state i - P.targetAmplitude i‖ ^ 2) ≤ ε ^ 2 ∧
    |(S.output ε).normEstimate - ‖P.solution‖| ≤ ε

end Qatlib.Papers.QLinearSys15.MainResults.MainRuntime
