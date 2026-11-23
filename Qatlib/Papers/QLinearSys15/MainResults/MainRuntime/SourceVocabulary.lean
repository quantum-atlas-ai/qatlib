/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

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
algorithm for the (nonzero entries of the) `i`-th row in time `T_A`, `‖b‖₂ = 1`,
and a state-preparation algorithm for `|b⟩` in time `T_B`. `x' = A⁻¹|b⟩` and
`x = x'/‖x'‖₂`. The access times are annotations for the source cost model.

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
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
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

/-- The §2.1 linear system with Hermitian `A` and spectrum in
`[−1, −1/κ] ∪ [1/κ, 1]`, exact sparse row lists, and `‖b‖₂ = 1`.
The costs `T_A` and `T_B` annotate row access and state preparation. -/
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
  /-- Every nonzero vector satisfies the Euclidean lower bound `‖Av‖₂ ≥ ‖v‖₂/κ`. -/
  spectrum_lower : ∀ v : Fin N → ℂ, v ≠ 0 →
    (1 / kappa) * ‖toEuclidean_fromVec v‖ ≤ ‖toEuclidean_fromVec (A *ᵥ v)‖
  /-- Every vector satisfies the Euclidean upper bound `‖Av‖₂ ≤ ‖v‖₂`. -/
  spectrum_upper : ∀ v : Fin N → ℂ, ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ ‖toEuclidean_fromVec v‖
  /-- The sparsity `s`. -/
  sparsity : ℝ
  /-- `s > 0`. -/
  sparsity_pos : 0 < sparsity
  /-- The column indices and values of the nonzero entries of each row, in access order. -/
  rowNonzeros : Fin N → List (Fin N × ℂ)
  /-- The list contains exactly the nonzero entries of the corresponding matrix row. -/
  rowNonzeros_spec : ∀ i j a, (j, a) ∈ rowNonzeros i ↔ A i j ≠ 0 ∧ a = A i j
  /-- A column occurs at most once in its row list. -/
  rowNonzeros_nodup : ∀ i, ((rowNonzeros i).map Prod.fst).Nodup
  /-- Each row list has length at most `s`. -/
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
  /-- The Euclidean norm of the right-hand side is one. -/
  b_norm : ‖toEuclidean_fromVec b‖ = 1

/-- The right-hand side has total Born mass one. -/
theorem LinearSystemProblem.b_normalized (P : LinearSystemProblem) : Normalized P.b :=
  (normalized_iff_norm_toEuclidean_fromVec _).mpr P.b_norm

/-- The size of the actual nonzero support equals the length of the row list. -/
theorem LinearSystemProblem.row_support_card (P : LinearSystemProblem) (i : Fin P.N) :
    (Finset.univ.filter fun j => P.A i j ≠ 0).card = (P.rowNonzeros i).length := by
  classical
  have support_eq : (Finset.univ.filter fun j => P.A i j ≠ 0) =
      ((P.rowNonzeros i).map Prod.fst).toFinset := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map]
    constructor
    · intro hj
      exact ⟨(j, P.A i j), (P.rowNonzeros_spec i j _).mpr ⟨hj, rfl⟩, rfl⟩
    · rintro ⟨⟨k, a⟩, ha, rfl⟩
      exact ((P.rowNonzeros_spec i k a).mp ha).1
  rw [support_eq, List.toFinset_card_of_nodup (P.rowNonzeros_nodup i), List.length_map]

/-- Each matrix row has at most the declared number of nonzero entries. -/
theorem LinearSystemProblem.row_support_card_le (P : LinearSystemProblem) (i : Fin P.N) :
    ((Finset.univ.filter fun j => P.A i j ≠ 0).card : ℝ) ≤ P.sparsity := by
  rw [P.row_support_card i]
  exact P.rowNonzero_le i

/-- The positive Euclidean lower bound makes the square matrix invertible. -/
theorem LinearSystemProblem.isUnit_matrix (P : LinearSystemProblem) : IsUnit P.A := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  by_contra h
  have hsub : v - w ≠ 0 := sub_ne_zero.mpr h
  have hnorm : 0 < ‖toEuclidean_fromVec (v - w)‖ := by
    apply norm_pos_iff.mpr
    intro hz
    exact hsub (congrArg WithLp.ofLp hz)
  have hlower := P.spectrum_lower (v - w) hsub
  rw [Matrix.mulVec_sub, hvw, sub_self] at hlower
  change (1 / P.kappa) * ‖toEuclidean_fromVec (v - w)‖ ≤
    ‖(0 : EuclideanSpace ℂ (Fin P.N))‖ at hlower
  rw [norm_zero] at hlower
  exact (not_lt_of_ge hlower) (mul_pos (one_div_pos.mpr P.kappa_pos) hnorm)

/-- The exact source solution `x' = A⁻¹ b`. -/
def LinearSystemProblem.solution (P : LinearSystemProblem) : Fin P.N → ℂ :=
  P.A⁻¹ *ᵥ P.b

/-- Applying the source matrix to the exact solution recovers the right-hand side. -/
theorem LinearSystemProblem.mulVec_solution (P : LinearSystemProblem) : P.A *ᵥ P.solution = P.b := by
  have hdet := P.A.isUnit_iff_isUnit_det.mp P.isUnit_matrix
  rw [solution, Matrix.mulVec_mulVec, P.A.mul_nonsing_inv hdet, Matrix.one_mulVec]

/-- The exact solution is nonzero because the right-hand side is normalized. -/
theorem LinearSystemProblem.solution_ne_zero (P : LinearSystemProblem) : P.solution ≠ 0 := by
  intro hz
  have hb : P.b = 0 := by rw [← P.mulVec_solution, hz, Matrix.mulVec_zero]
  have hnorm := P.b_norm
  rw [hb] at hnorm
  change ‖(0 : EuclideanSpace ℂ (Fin P.N))‖ = 1 at hnorm
  simp at hnorm

/-- The source solution `x = x'/‖x'‖₂`, as a state amplitude. -/
def LinearSystemProblem.targetAmplitude (P : LinearSystemProblem) (i : Fin P.N) : ℂ :=
  P.solution i / (‖toEuclidean_fromVec P.solution‖ : ℂ)

/-- The normalized solution has total Born mass one. -/
theorem LinearSystemProblem.targetAmplitude_normalized (P : LinearSystemProblem) :
    Normalized P.targetAmplitude := by
  let v := toEuclidean_fromVec P.solution
  have hnorm : ‖v‖ ≠ 0 := by
    intro h
    exact P.solution_ne_zero (congrArg WithLp.ofLp (norm_eq_zero.mp h))
  have htarget : toEuclidean_fromVec P.targetAmplitude = (‖v‖ : ℂ)⁻¹ • v := by
    apply PiLp.ext
    intro i
    change P.solution i / (‖v‖ : ℂ) = (‖v‖ : ℂ)⁻¹ * P.solution i
    rw [div_eq_inv_mul]
  rw [normalized_iff_norm_toEuclidean_fromVec, htarget, norm_smul, norm_inv,
    Complex.norm_of_nonneg (norm_nonneg v), inv_mul_cancel₀ hnorm]

/-! ## 3. The solver output and its cost -/

/-- One solver output with a normalized state and a classical estimate of `‖x'‖₂`. -/
structure QlsOutput (P : LinearSystemProblem) where
  /-- The produced state `|x⟩`. -/
  state : QState (Fin P.N)
  /-- The produced state has total Born mass one. -/
  state_normalized : Normalized state
  /-- The classical estimate of `‖x'‖₂`. -/
  normEstimate : ℝ

/-- A costed solver for one instance: its output and its run-time as functions
of the target accuracy. -/
structure CostedQlsSolver (P : LinearSystemProblem) where
  /-- The output produced at accuracy `ε`. -/
  output : ℝ → QlsOutput P
  /-- The run-time at accuracy `ε`. -/
  cost : ℝ → ℝ

/-- **"Produce `|x⟩` and `‖x'‖₂` up to error `ε`."** The produced state is
within `ε` in `ℓ²` of the normalized source solution, and the classical
estimate of `‖x'‖₂` is within `ε`. -/
def ProducesSolution (P : LinearSystemProblem) (S : CostedQlsSolver P) (ε : ℝ) : Prop :=
  ‖toEuclidean_fromVec ((S.output ε).state - P.targetAmplitude)‖ ≤ ε ∧
    |(S.output ε).normEstimate - ‖toEuclidean_fromVec P.solution‖| ≤ ε

end Qatlib.Papers.QLinearSys15.MainResults.MainRuntime
