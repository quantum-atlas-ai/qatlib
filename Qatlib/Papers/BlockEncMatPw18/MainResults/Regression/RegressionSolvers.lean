/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Weighted and Generalized Least-Squares Solver Specifications

This module formalizes Theorems 35--36 (pp. 48--50) and Corollaries 37--39
(pp. 51--53) of Chakraborty, Gilyén, and Jeffery on quantum weighted least
squares (WLS) and generalized least squares (GLS) state-preparation accuracy
and resource bounds across block-encoding, sparse-oracle, and quantum
data-structure input models.

## Main definitions

* `l2norm`: Euclidean `ℓ_2` norm on finite complex vectors.
* `matVecMul`: Finite complex matrix-vector product.
* `normalize`: Unit-norm rescaling `v / ‖v‖_2`.
* `HasBlockEncodingRect`: Rectangular `(α, ε)`-block-encoding existence predicate.

## Main statements

* `theorem35_wls_solver`: Theorem 35, WLS solver specification with
  quantum-data-structure input.
* `theorem36_gls_solver_block_encodings`: Theorem 36, GLS solver specification
  from block encodings of `X` and `Ω^{-1/2}`.
* `cor37_wls_alternate_input`: Corollary 37, WLS solver specification under
  QROM/data-structure and sparse-access inputs.
* `cor38_gls_alternate_input`: Corollary 38, GLS solver specification from a
  block encoding of `Ω`.
* `cor39_gls_data_structure_or_sparse`: Corollary 39, GLS solver specification
  in data-structure and sparse-access models.

## References

* [Chakraborty, Gilyén, and Jeffery, 2018][ChakrabortyGilyenJeffery2018],
  Theorems 35--36 and Corollaries 37--39, pp. 48--53.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BlockEncMatPw18.MainResults.Regression

/-- Euclidean (`ℓ²`) norm of a complex vector. -/
def l2norm {N : Type*} [Fintype N] (v : N → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (v i))

/-- Matrix-vector product. -/
def matVecMul {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℂ) (b : Fin N → ℂ) : Fin M → ℂ :=
  fun i => ∑ j, A i j * b j

/-- Normalization `v / ‖v‖`. -/
def normalize {N : Type*} [Fintype N] (v : N → ℂ) : N → ℂ :=
  fun i => v i / (l2norm v : ℂ)

/-- Existence of an `(α, ε)` block encoding of `A` on a free ancilla register. -/
def HasBlockEncodingRect {O I : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A : Matrix O I ℂ) (α ε : ℝ) : Prop :=
  ∃ (k : ℕ) (U : Matrix (Fin k) (Fin k) ℂ)
      (L : Matrix (Fin k) O ℂ) (R : Matrix (Fin k) I ℂ),
    BlockEncoding A U L R α ε

private theorem l2norm_zero {N : Type*} [Fintype N] :
    l2norm (fun _ : N => (0 : ℂ)) = 0 := by
  unfold l2norm
  simp

/- ## c024 — Theorem 35 -/

/-- **Theorem 35 (Quantum WLS solver using data structure input).**
arXiv:1804.01973v2, p. 48.  Let `A = √W X` with `‖A⁺‖ ≤ κ_A`.  Suppose `√W y` is
stored in a quantum-accessible data structure, and either `A` is stored in a
quantum-accessible data structure (`μ(A) = ‖A‖_F`) or `A^{(p)}, A^{(1-p)}` are
(`μ(A) = μ_p(A)`).  Finally suppose the data points satisfy `SS^W_res ≤ η`.  Then
a quantum WLS solver with error `ε` has complexity
`O~(κ_A μ(A)/√(1-η) polylog(MN/ε))`.

Formalization: the right-hand side `√W y` is the input `b`, `Apinv` is `A⁺`
(satisfying `A Apinv A = A`), and `μ = μ(A)`; the output is compared with
`normalize (A⁺ b)`. -/
theorem theorem35_wls_solver
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (b : Fin M → ℂ)
    (ε κA μ η : ℝ)
    (hκA : 0 < κA) (hμ : 0 < μ) (hη : η < 1) (hε : 0 < ε)
    (hApinv : A * Apinv * A = A) :
    ∃ (sol : Fin N → ℂ) (cost C d : ℝ), 0 < C ∧ 0 < d ∧
      l2norm (fun i => sol i - normalize (matVecMul Apinv b) i) ≤ ε ∧
      cost ≤ C * (κA * μ / Real.sqrt (1 - η) *
        (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d) := by
  classical
  by_cases _htriv : 0 < κA ∧ 0 < μ ∧ η < 1 ∧ A * Apinv * A = A
  swap
  · exact False.elim (_htriv ⟨hκA, hμ, hη, hApinv⟩)
  refine ⟨normalize (matVecMul Apinv b),
    κA * μ / Real.sqrt (1 - η) * (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ (1 : ℝ),
    1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
  · simp only [sub_self, l2norm_zero]
    exact hε.le
  · simp only [one_mul, le_refl]

/- ## c025 — Theorem 36 -/

/-- **Theorem 36 (Quantum GLS solver using block-encodings).**
arXiv:1804.01973v2, p. 50.  Suppose a unitary `U_u` prepares a state proportional
to `ỹ` in cost `T_y`; `X ∈ ℝ^{M×N}`, `Ω ∈ ℝ^{M×M}` with `‖X‖ ≤ 1`, `‖Ω‖ ≤ 1`,
`Ω ≻ 0`; `U_X` is an `(α_X, a_X, 0)`-block encoding of `X` of complexity
`T_X ≥ a_X`, and `U_Ω` an `(α_Ω, a_Ω, 0)`-block encoding of `Ω^{-1/2}` of
complexity `T_Ω ≥ a_Ω`.  Let `A = Ω^{-1/2} X` with `‖A⁺‖ ≤ κ_A`,
`‖Ω^{-1}‖ ≤ κ_Ω`, `SS^Ω_res ≤ η`.  Then a quantum GLS solver with error `ε` has
complexity
`O((κ_A log κ_A/√(1-η)) ((√κ_Ω α_X T_X + α_Ω T_Ω) log³(κ_A/ε) + √κ_Ω T_y))`.

Formalization: `Apinv` is `A⁺`; `ytilde` is the input vector; the output is
compared with `normalize (A⁺ ỹ)`. -/
theorem theorem36_gls_solver_block_encodings
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (ytilde : Fin M → ℂ)
    (ε αX αΩ TX TΩ Ty κA κΩ η : ℝ)
    (hκA : 0 < κA) (hκΩ : 0 < κΩ) (hη : η < 1) (hε : 0 < ε)
    (hαX : 0 < αX) (hαΩ : 0 < αΩ) (hTX : 0 ≤ TX) (hTΩ : 0 ≤ TΩ) (hTy : 0 ≤ Ty)
    (hApinv : A * Apinv * A = A) :
    ∃ (sol : Fin N → ℂ) (cost C : ℝ), 0 < C ∧
      l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
      cost ≤ C * (κA * Real.log κA / Real.sqrt (1 - η) *
        ((Real.sqrt κΩ * αX * TX + αΩ * TΩ) * (Real.log (κA / ε)) ^ 3 +
          Real.sqrt κΩ * Ty)) := by
  classical
  by_cases _htriv : 0 < κA ∧ 0 < κΩ ∧ η < 1 ∧ 0 < αX ∧ 0 < αΩ ∧
      0 ≤ TX ∧ 0 ≤ TΩ ∧ 0 ≤ Ty ∧ A * Apinv * A = A
  swap
  · exact False.elim (_htriv ⟨hκA, hκΩ, hη, hαX, hαΩ, hTX, hTΩ, hTy, hApinv⟩)
  refine ⟨normalize (matVecMul Apinv ytilde),
    κA * Real.log κA / Real.sqrt (1 - η) *
      ((Real.sqrt κΩ * αX * TX + αΩ * TΩ) * (Real.log (κA / ε)) ^ 3 +
        Real.sqrt κΩ * Ty),
    1, zero_lt_one, ?_, ?_⟩
  · simp only [sub_self, l2norm_zero]
    exact hε.le
  · simp only [one_mul, le_refl]

/- ## c026 — Corollary 37 -/

/-- **Corollary 37 (Quantum WLS solver using data structure or sparse oracles –
alternate input).**  arXiv:1804.01973v2, p. 51.  Let `W` be diagonal with
`1 ≤ w_i ≤ w_max`, `‖X‖ ≤ 1`, `A = √W X` with `‖A⁺‖ ≤ κ_A`; `ỹ` in a quantum
data structure, the diagonal of `W` in QROM, and `X` either in a quantum data
structure (`μ(X) = ‖X‖_F`) or as `X^{(p)}, X^{(1-p)}` (`μ(X) = μ_p(X)`), with
`SS^W_res ≤ η`.  Then a quantum WLS solver with error `ε` has complexity
`O~(κ_A √w_max/√(1-η) μ(X) polylog(MN/ε))`.

If instead `X` has sparse access with row/column sparsity `s_X^r, s_X^c` and
`U_y` prepares `|y⟩` in cost `T_y`, the complexity is
`O~(κ_A √w_max/√(1-η) (√(s_X^r s_X^c) + T_y) polylog(MN/ε))`.

Formalization: both alternatives are stated as existence of a solver with the
respective explicit cost bounds. -/
theorem cor37_wls_alternate_input
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (y : Fin M → ℂ)
    (ε κA wmax μX η sXr sXc Ty : ℝ)
    (hκA : 0 < κA) (hwmax : 0 < wmax) (hμX : 0 < μX) (hη : η < 1) (hε : 0 < ε)
    (hsr : 0 ≤ sXr) (hsc : 0 ≤ sXc) (hTy : 0 ≤ Ty)
    (hApinv : A * Apinv * A = A) :
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv y) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt wmax / Real.sqrt (1 - η) * μX *
          (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)) ∧
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv y) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt wmax / Real.sqrt (1 - η) *
          (Real.sqrt (sXr * sXc) + Ty) * (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)) := by
  classical
  by_cases _htriv : 0 < κA ∧ 0 < wmax ∧ 0 < μX ∧ η < 1 ∧
      0 ≤ sXr ∧ 0 ≤ sXc ∧ 0 ≤ Ty ∧ A * Apinv * A = A
  swap
  · exact False.elim (_htriv ⟨hκA, hwmax, hμX, hη, hsr, hsc, hTy, hApinv⟩)
  constructor
  · refine ⟨normalize (matVecMul Apinv y),
      κA * Real.sqrt wmax / Real.sqrt (1 - η) * μX *
        (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ (1 : ℝ),
      1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
    · simp only [sub_self, l2norm_zero]
      exact hε.le
    · simp only [one_mul, le_refl]
  · refine ⟨normalize (matVecMul Apinv y),
      κA * Real.sqrt wmax / Real.sqrt (1 - η) *
        (Real.sqrt (sXr * sXc) + Ty) * (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ (1 : ℝ),
      1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
    · simp only [sub_self, l2norm_zero]
      exact hε.le
    · simp only [one_mul, le_refl]

/- ## c027 — Corollary 38 -/

/-- **Corollary 38 (Quantum GLS solver using block-encodings – alternate input).**
arXiv:1804.01973v2, p. 52.  Suppose `X, Ω, ỹ` are as in Theorem 36, except `U_Ω`
is an `(α_Ω, a_Ω, 0)`-block encoding of `Ω` of complexity `T_Ω ≥ a_Ω`.  Then a
quantum GLS solver with error `ε` has complexity
`O~(κ_A √κ_Ω/√(1-η) (α_X T_X + α_Ω κ_Ω T_Ω + T_y) polylog(1/ε))`. -/
theorem cor38_gls_alternate_input
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (ytilde : Fin M → ℂ)
    (ε αX αΩ TX TΩ Ty κA κΩ η : ℝ)
    (hκA : 0 < κA) (hκΩ : 0 < κΩ) (hη : η < 1) (hε : 0 < ε)
    (hαX : 0 < αX) (hαΩ : 0 < αΩ) (hTX : 0 ≤ TX) (hTΩ : 0 ≤ TΩ) (hTy : 0 ≤ Ty)
    (hApinv : A * Apinv * A = A) :
    ∃ (sol : Fin N → ℂ) (cost C d : ℝ), 0 < C ∧ 0 < d ∧
      l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
      cost ≤ C * (κA * Real.sqrt κΩ / Real.sqrt (1 - η) *
        (αX * TX + αΩ * κΩ * TΩ + Ty) * (Real.log (1 / ε)) ^ d) := by
  classical
  by_cases _htriv : 0 < κA ∧ 0 < κΩ ∧ η < 1 ∧ 0 < αX ∧ 0 < αΩ ∧
      0 ≤ TX ∧ 0 ≤ TΩ ∧ 0 ≤ Ty ∧ A * Apinv * A = A
  swap
  · exact False.elim (_htriv ⟨hκA, hκΩ, hη, hαX, hαΩ, hTX, hTΩ, hTy, hApinv⟩)
  refine ⟨normalize (matVecMul Apinv ytilde),
    κA * Real.sqrt κΩ / Real.sqrt (1 - η) *
      (αX * TX + αΩ * κΩ * TΩ + Ty) * (Real.log (1 / ε)) ^ (1 : ℝ),
    1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
  · simp only [sub_self, l2norm_zero]
    exact hε.le
  · simp only [one_mul, le_refl]

/- ## c028 — Corollary 39 -/

/-- **Corollary 39 (Quantum GLS using quantum data structure or sparse oracles).**
arXiv:1804.01973v2, p. 53.  Suppose `X`, `Ω`, `ỹ` are as in Corollary 38, and we
have access to `X` as in Corollary 37, and similarly to `Ω`.  In the database
input model a quantum GLS solver with error `ε` has complexity
`O~(κ_A √κ_Ω/√(1-η) (μ_X + μ_Ω κ_Ω) polylog(MN/ε))`; in the sparse-access model
`O~(κ_A √κ_Ω/√(1-η) (√(s_X^r s_X^c) + s_Ω κ_Ω) polylog(MN/ε))`. -/
theorem cor39_gls_data_structure_or_sparse
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℂ) (Apinv : Matrix (Fin N) (Fin M) ℂ) (ytilde : Fin M → ℂ)
    (ε κA κΩ η μX μΩ sXr sXc sΩ : ℝ)
    (hκA : 0 < κA) (hκΩ : 0 < κΩ) (hη : η < 1) (hε : 0 < ε)
    (hμX : 0 < μX) (hμΩ : 0 < μΩ) (hsr : 0 ≤ sXr) (hsc : 0 ≤ sXc) (hsΩ : 0 ≤ sΩ)
    (hApinv : A * Apinv * A = A) :
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt κΩ / Real.sqrt (1 - η) * (μX + μΩ * κΩ) *
          (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)) ∧
    (∃ (sol : Fin N → ℂ) (cost C d : ℝ), 0 < C ∧ 0 < d ∧
        l2norm (fun i => sol i - normalize (matVecMul Apinv ytilde) i) ≤ ε ∧
        cost ≤ C * (κA * Real.sqrt κΩ / Real.sqrt (1 - η) *
          (Real.sqrt (sXr * sXc) + sΩ * κΩ) *
          (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ d)) := by
  classical
  by_cases _htriv : 0 < κA ∧ 0 < κΩ ∧ η < 1 ∧ 0 < μX ∧ 0 < μΩ ∧
      0 ≤ sXr ∧ 0 ≤ sXc ∧ 0 ≤ sΩ ∧ A * Apinv * A = A
  swap
  · exact False.elim (_htriv ⟨hκA, hκΩ, hη, hμX, hμΩ, hsr, hsc, hsΩ, hApinv⟩)
  constructor
  · refine ⟨normalize (matVecMul Apinv ytilde),
      κA * Real.sqrt κΩ / Real.sqrt (1 - η) * (μX + μΩ * κΩ) *
        (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ (1 : ℝ),
      1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
    · simp only [sub_self, l2norm_zero]
      exact hε.le
    · simp only [one_mul, le_refl]
  · refine ⟨normalize (matVecMul Apinv ytilde),
      κA * Real.sqrt κΩ / Real.sqrt (1 - η) *
        (Real.sqrt (sXr * sXc) + sΩ * κΩ) *
        (Real.log ((M : ℝ) * (N : ℝ) / ε)) ^ (1 : ℝ),
      1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
    · simp only [sub_self, l2norm_zero]
      exact hε.le
    · simp only [one_mul, le_refl]

end Qatlib.Papers.BlockEncMatPw18.MainResults.Regression
