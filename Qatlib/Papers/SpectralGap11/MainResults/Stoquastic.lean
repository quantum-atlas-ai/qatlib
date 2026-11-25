/-
Copyright (c) 2026 qatlas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum
public import Qatlib.Papers.SpectralGap11.MainResults.Optimality

@[expose] public section


/-!
# SpectralGap11 reviewed Stoquastic

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.SpectralGap11.MainResults

/-- The stoquastic family `H_x = -|x⟩⟨x| - c·A` of Theorem 3, Eq. (21)
(arXiv:1110.2494v3, p. 6), with `A` the (real symmetric) lattice adjacency
matrix and `c` the constant coupling. -/
noncomputable def sourceStoquastic {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (c : ℝ)
    (x : Fin M) : Matrix (Fin M) (Fin M) ℝ :=
  -Matrix.of (fun i j => if i = x ∧ j = x then (1 : ℝ) else 0) - c • A

/-- The model predicate of Theorem 3: the stoquastic family `{H_x}` of Eq. (21)
admits no black-box spectral gap amplification. Recorded abstractly because the
black-box model is not formalised in the shared libraries. -/
structure NoSpectralGapAmplification (M : ℕ) : Prop where
  /-- The dimension `M` is positive. -/
  positive : 0 < M


/-- The legacy existential admits a zero adjacency matrix in dimension one.
Its positivity predicate does not express a query lower bound. -/
theorem source_theorem3 :
    ∃ (M : ℕ) (_A : Matrix (Fin M) (Fin M) ℝ) (c Δ : ℝ),
      0 < M ∧ 0 < c ∧ 0 < Δ ∧
      (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        C₁ / Real.sqrt M ≤ Δ ∧ Δ ≤ C₂ / Real.sqrt M) ∧
      NoSpectralGapAmplification M := by
  refine ⟨1, 0, 1, 1, by norm_num, by norm_num, by norm_num, ?_, ⟨by norm_num⟩⟩
  exact ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Qatlib.Papers.SpectralGap11.MainResults

section

/-!
## A finite stoquastic sparse obstruction

Theorem 3 of [BoixoSomma2012SpectralGap], arXiv:1110.2494v3, pp. 6-7,
excludes asymptotic amplification for a five-dimensional lattice family whose
gap scales as `Θ(M^{-1/2})`, using the SEARCH lower bound `Ω(√M)`.  This
module records two separate pieces of partial support.  `diagonalStoquastic`
is a stoquastic one-sparse diagonal family with exact gap `1/M`.  That scaling
is not the paper's lattice scaling.  `ConditionalSqrtBudget` is only the
algebraic comparison `Δ' ≤ κ √Δ` under an external query lower bound and a
constant implementation budget.  The two pieces are not combined into an
oracle obstruction, and a finite scalar tuple is not a Theorem 3 witness.
-/



set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults
open Qatlib.Papers.SpectralGap11.MainResults

open Matrix

noncomputable section

variable {M : ℕ}

/-- The basis vector at a marked word. -/
def markedBasis (x : Fin M) : Fin M → ℝ :=
  fun i => if i = x then 1 else 0

/-- A normalized diagonal search Hamiltonian with marked ground state. -/
def diagonalStoquastic (x : Fin M) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.diagonal (fun i => if i = x then 0 else (M : ℝ)⁻¹)

/-- Off-diagonal nonpositivity, the finite real form of stoquasticity. -/
def Stoquastic (A : Matrix (Fin M) (Fin M) ℝ) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

/-- Every row has at most one nonzero entry. -/
def OneSparse (A : Matrix (Fin M) (Fin M) ℝ) : Prop :=
  ∀ i j k, A i j ≠ 0 → A i k ≠ 0 → j = k

/-- The diagonal family is stoquastic. -/
theorem diagonalStoquastic_stoquastic (x : Fin M) :
    Stoquastic (diagonalStoquastic x) := by
  intro i j hij
  simp [diagonalStoquastic, hij]

/-- The diagonal family is one-sparse. -/
theorem diagonalStoquastic_oneSparse (x : Fin M) :
    OneSparse (diagonalStoquastic x) := by
  intro i j k hij hik
  have hji : i = j := by
    by_contra hne
    apply hij
    simp [diagonalStoquastic, hne]
  have hki : i = k := by
    by_contra hne
    apply hik
    simp [diagonalStoquastic, hne]
  exact hji.symm.trans hki

/-- The marked basis vector is a zero eigenvector. -/
theorem diagonalStoquastic_ground (x : Fin M) :
    diagonalStoquastic x *ᵥ markedBasis x = 0 := by
  funext i
  by_cases hix : i = x
  · simp [diagonalStoquastic, markedBasis, Matrix.mulVec_diagonal, hix]
  · simp [diagonalStoquastic, markedBasis, Matrix.mulVec_diagonal, hix]

/-- Every unmarked basis vector has the exact positive eigenvalue `1/M`. -/
theorem diagonalStoquastic_excited (x y : Fin M) (hxy : y ≠ x) :
    diagonalStoquastic x *ᵥ markedBasis y =
      (M : ℝ)⁻¹ • markedBasis y := by
  funext i
  by_cases hix : i = x
  · subst i
    simp [diagonalStoquastic, markedBasis, Matrix.mulVec_diagonal, Ne.symm hxy]
  · by_cases hiy : i = y
    · subst i
      simp [diagonalStoquastic, markedBasis, Matrix.mulVec_diagonal, hix]
    · simp [diagonalStoquastic, markedBasis, Matrix.mulVec_diagonal, hix, hiy]

/-- The marked basis vector is nonzero. -/
theorem markedBasis_ne_zero (x : Fin M) : markedBasis x ≠ 0 := by
  intro h
  have hx := congrFun h x
  simp [markedBasis] at hx

/-- The finite witness has a positive, non-degenerate gap whenever `M > 0`. -/
theorem diagonalStoquastic_gap (x : Fin M) (hM : 0 < M) :
    0 < (M : ℝ)⁻¹ ∧
      diagonalStoquastic x *ᵥ markedBasis x = 0 ∧
      ∀ y, y ≠ x →
        diagonalStoquastic x *ᵥ markedBasis y =
          (M : ℝ)⁻¹ • markedBasis y := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨inv_pos.mpr hMr, diagonalStoquastic_ground x, ?_⟩
  intro y hy
  exact diagonalStoquastic_excited x y hy

/-- An external SEARCH lower bound and a constant implementation budget imply
the square-root comparison.  The inequalities do not mention a Hamiltonian. -/
theorem conditional_sqrt_upper (Δ Δ' κ q : ℝ)
    (hgap : 0 < Δ) (hamp : 0 ≤ Δ')
    (hsearch : 1 ≤ q * Real.sqrt Δ)
    (hbudget : Δ' * q ≤ κ) :
    Δ' ≤ κ * Real.sqrt Δ := by
  have hsqrt : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hgap
  have hleft : Δ' ≤ Δ' * (q * Real.sqrt Δ) := by
    have h := mul_le_mul_of_nonneg_left hsearch hamp
    simpa using h
  calc
    Δ' ≤ Δ' * (q * Real.sqrt Δ) := hleft
    _ = (Δ' * q) * Real.sqrt Δ := by ring
    _ ≤ κ * Real.sqrt Δ :=
      mul_le_mul_of_nonneg_right hbudget hsqrt.le

/-- The conditional algebraic hypotheses of the square-root comparison.

`search_lower` is an assumption about an external query lower bound.  It is
not derived from `diagonalStoquastic`, and it does not encode the paper's
relation `Δ = Θ(M^{-1/2})` against an `Ω(√M)` SEARCH bound. -/
structure ConditionalSqrtBudget (Δ Δ' κ q : ℝ) : Prop where
  /-- The input gap is positive. -/
  gap_pos : 0 < Δ
  /-- The candidate amplified gap is nonnegative. -/
  amp_nonneg : 0 ≤ Δ'
  /-- The query count is nonnegative. -/
  query_nonneg : 0 ≤ q
  /-- An external SEARCH lower bound in normalized units. -/
  search_lower : 1 ≤ q * Real.sqrt Δ
  /-- The implementation constant is positive. -/
  constant_pos : 0 < κ
  /-- The constant-cost evolution budget. -/
  query_budget : Δ' * q ≤ κ

/-- The algebraic comparison implied by `ConditionalSqrtBudget`. -/
theorem conditional_sqrt_budget (Δ Δ' κ q : ℝ)
    (hmodel : ConditionalSqrtBudget Δ Δ' κ q) :
    Δ' ≤ κ * Real.sqrt Δ := by
  exact conditional_sqrt_upper Δ Δ' κ q hmodel.gap_pos hmodel.amp_nonneg
    hmodel.search_lower hmodel.query_budget

end

end Qatlib.Papers.SpectralGap11.MainResults

end
