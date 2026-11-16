/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MatrixFunc24.MainResults.SourceModel
public import Mathlib.RingTheory.Polynomial.Chebyshev

@[expose] public section


/-!
# Closed algebraic results for MatrixFunc24

This module preserves the proved coefficient, matrix, counting, and recorded-data
results of the retired source, and proves the coefficient-importance estimator
identity. Complexity classifications and sampling deviation bounds remain separate.
The fixed paper is arXiv:2410.13937v2.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Polynomial Matrix
open Polynomial Matrix
open Qatlib.Papers.MatrixFunc24.MainResults.SourceModel

namespace Qatlib.Papers.MatrixFunc24.MainResults.Chebyshev

/-- **Lemma 48 (bound on the coefficients of Chebyshev polynomials).**
For every `n` and every coefficient index `k`, the absolute value of the `k`-th
coefficient of the Chebyshev polynomial of the first kind `T_n` is at most
`4^n`.  Source: arXiv:2410.13937v2, Lemma 48, Eq. (67), p. 33. -/
theorem chebyshev_coeff_abs_le : ∀ (n k : ℕ),
    |(Chebyshev.T ℝ (n : ℤ)).coeff k| ≤ (4 : ℝ) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    rcases n with _ | _ | n
    · -- T_0 = 1
      simp only [Nat.cast_zero, Chebyshev.T_zero, Polynomial.coeff_one]
      split_ifs <;> norm_num
    · -- T_1 = X
      have h1 : Chebyshev.T ℝ ((1 : ℕ) : ℤ) = (X : ℝ[X]) := by
        simp
      rw [h1, Polynomial.coeff_X]
      split_ifs <;> norm_num
    · -- T_{n+2} = 2 X T_{n+1} - T_n
      have hrec : Chebyshev.T ℝ (((n + 2 : ℕ) : ℤ)) =
          (2 : ℝ[X]) * X * Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ)) -
            Chebyshev.T ℝ ((n : ℕ) : ℤ) := by
        simp
      have hcoeff :
          (((2 : ℝ[X]) * X * Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).coeff k) =
            2 * ((X * Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).coeff k) := by
        rw [mul_assoc]
        have h2 : (2 : ℝ[X]) = Polynomial.C (2 : ℝ) := by
          simp [Polynomial.C_ofNat]
        rw [h2, Polynomial.coeff_C_mul]
      rw [hrec, Polynomial.coeff_sub, hcoeff]
      have hpow : (0 : ℝ) < (4 : ℝ) ^ n := pow_pos (by norm_num) n
      have h16 : (4 : ℝ) ^ (n + 2) = 16 * (4 : ℝ) ^ n := by
        rw [pow_succ, pow_succ]; ring
      rcases k with _ | m
      · -- coefficient 0: the shifted term vanishes
        rw [Polynomial.coeff_X_mul_zero]
        have hb := ih n (by omega) 0
        simp only [mul_zero, zero_sub]
        rw [abs_neg]
        calc |(Chebyshev.T ℝ ((n : ℕ) : ℤ)).coeff 0| ≤ (4 : ℝ) ^ n := hb
          _ ≤ (4 : ℝ) ^ (n + 2) := by rw [h16]; nlinarith
      · -- coefficient m+1: two shifted coefficients
        rw [Polynomial.coeff_X_mul]
        have hb1 := ih (n + 1) (by omega) m
        have hb2 := ih n (by omega) (m + 1)
        have h4 : (4 : ℝ) ^ (n + 1) = 4 * (4 : ℝ) ^ n := by rw [pow_succ, mul_comm]
        calc |2 * (Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).coeff m -
                (Chebyshev.T ℝ ((n : ℕ) : ℤ)).coeff (m + 1)|
            ≤ |2 * (Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).coeff m| +
                |(Chebyshev.T ℝ ((n : ℕ) : ℤ)).coeff (m + 1)| := abs_sub _ _
          _ = 2 * |(Chebyshev.T ℝ (((n + 1 : ℕ) : ℤ))).coeff m| +
                |(Chebyshev.T ℝ ((n : ℕ) : ℤ)).coeff (m + 1)| := by
                rw [abs_mul]; norm_num
          _ ≤ 2 * (4 : ℝ) ^ (n + 1) + (4 : ℝ) ^ n := by linarith
          _ ≤ (4 : ℝ) ^ (n + 2) := by rw [h16, h4]; nlinarith

end Qatlib.Papers.MatrixFunc24.MainResults.Chebyshev

namespace Qatlib.Papers.MatrixFunc24.MainResults.PauliAlgebra

/-- The single-qubit identity, `Fin 2`-indexed. -/
def I2 : Matrix (Fin 2) (Fin 2) ℂ := 1

/-- The Pauli `X` matrix. -/
def X2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Y` matrix. -/
def Y2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Pauli `Z` matrix. -/
def Z2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The single-qubit computational basis matrix element `|x⟩⟨y|`. -/
def basis1 (x y : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => (if i = x then 1 else 0) * (if j = y then 1 else 0)

/-! ## Lemma 54, Eq. (77): single-qubit decomposition

Source: p. 34, Eq. (77).  These four identities are the inductive building block
of the general `|i⟩⟨j|` decomposition, and are proved here by direct matrix
evaluation. -/

/-- Eq. (77), first identity: `|0⟩⟨0| = (1 + Z)/2`. -/
theorem basis1_zero_zero : basis1 0 0 = (1 / 2 : ℂ) • (I2 + Z2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basis1, I2, Z2]; ring

/-- Eq. (77), second identity: `|1⟩⟨1| = (1 - Z)/2`. -/
theorem basis1_one_one : basis1 1 1 = (1 / 2 : ℂ) • (I2 - Z2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basis1, I2, Z2]; ring

/-- Eq. (77), third identity: `|0⟩⟨1| = (X + iY)/2`. -/
theorem basis1_zero_one : basis1 0 1 = (1 / 2 : ℂ) • (X2 + Complex.I • Y2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basis1, X2, Y2, Complex.I_mul_I]; ring

/-- Eq. (77), fourth identity: `|1⟩⟨0| = (X - iY)/2`. -/
theorem basis1_one_zero : basis1 1 0 = (1 / 2 : ℂ) • (X2 - Complex.I • Y2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basis1, X2, Y2, Complex.I_mul_I]; ring

/-- The standard Hadamard matrix on `Fin 2`. -/
def Hadamard2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹;
     (Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹]

/-- **Lemma 55, corrected Hadamard identity.**  The standard Hadamard gate is
`(X + Z)/√2`; this is the identity that is actually true and is proved here.
(Source p. 35 writes `(1 + X)/√2`, apparently a typo for `(X + Z)/√2`.) -/
theorem lemma55_hadamard_corrected :
    Hadamard2 = ((Real.sqrt 2)⁻¹ : ℝ) • (X2 + Z2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hadamard2, X2, Z2]

/-- The source's scaled identity-plus-X expression equals the scaled all-ones matrix. -/
theorem lemma55_hadamard_literal_source_formula :
    ((Real.sqrt 2)⁻¹ : ℝ) • (I2 + X2) =
      (fun (_ _ : Fin 2) => ((Real.sqrt 2)⁻¹ : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [I2, X2]

/-- **Lemma 57 (Pauli norm is multiplicative).**  For coefficient families `a`
and `b` of two Pauli decompositions, the tensor-product coefficient family
`(ℓ,k) ↦ a ℓ * b k` has Pauli norm `λ_A · λ_B`.  Source: Eq. (81)–(83), p. 35. -/
theorem lemma57_pauliNorm_tensor_mul {ι κ : Type} [Fintype ι] [Fintype κ]
    (a : ι → ℂ) (b : κ → ℂ) :
    pauliNorm (fun p : ι × κ => a p.1 * b p.2) = pauliNorm a * pauliNorm b := by
  unfold pauliNorm
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [norm_mul]

/-- The two-qubit operator `|10⟩⟨01|`, entrywise on `Bool × Bool` (first factor
the left qubit). -/
def ket10bra01 : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun i j => (if i = (true, false) then 1 else 0) * (if j = (false, true) then 1 else 0)

/-- A `Bool`-indexed computational basis matrix `|x⟩⟨y|` (the two-qubit factors). -/
def basisBool (x y : Bool) : Matrix Bool Bool ℂ :=
  fun i j => (if i = x then 1 else 0) * (if j = y then 1 else 0)

/-- The clock transition matrix is the tensor product of its two computational basis factors. -/
theorem lemma58_ket10bra01_pauli_weight_one :
    ket10bra01 =
      (fun i j : Bool × Bool =>
        basisBool true false i.1 j.1 * basisBool false true i.2 j.2) := by
  ext i j
  rcases i with ⟨i1, i2⟩
  rcases j with ⟨j1, j2⟩
  cases i1 <;> cases i2 <;> cases j1 <;> cases j2 <;>
    simp [ket10bra01, basisBool]

/-- A supplied surjective binary normal-form map bounds the number of represented elements. -/
theorem lemma53_pauli_subgroup_card_le {G : Type*} [Fintype G]
    (L : ℕ) (index : Bool × (Fin L → Bool) → G)
    (hsurj : Function.Surjective index) :
    Fintype.card G ≤ 2 ^ (L + 1) := by
  -- Source: Lemma 53, Eq. (75), p. 34.  Eq. (75) exhibits every group element
  -- as `(-1)^{k₀} ∏ P_i^{k_i}`, i.e. as the image of `(k₀, k₁, …, k_L) ∈
  -- Bool × (Fin L → Bool)`; the cardinal bound is then the cardinal of the
  -- indexing set.
  calc Fintype.card G ≤ Fintype.card (Bool × (Fin L → Bool)) :=
        Fintype.card_le_of_surjective index hsurj
    _ = 2 ^ (L + 1) := by
        simp [Fintype.card_prod, pow_succ]
        ring

/-- Normalized coefficient-magnitude importance sampling has the original matrix sum as expectation. -/
theorem lemma60_importance_sampling_unbiased {ι N : Type} [Fintype ι]
    [_instFintypeN : Fintype N] [_instDecidableEqN : DecidableEq N] (a : ι → ℂ) (P : ι → MatrixN N)
    (hlam : pauliNorm a ≠ 0) (hnz : ∀ l, a l ≠ 0) :
    (∑ l, ((‖a l‖ / pauliNorm a : ℝ) : ℂ) •
        (((a l / (‖a l‖ : ℝ)) * (pauliNorm a : ℂ)) • P l))
      = ∑ l, a l • P l := by
  apply Finset.sum_congr rfl
  intro l _
  rw [smul_smul]
  congr 1
  have hn : (‖a l‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr (hnz l))
  have hl : (pauliNorm a : ℂ) ≠ 0 := by exact_mod_cast hlam
  push_cast
  field_simp


end Qatlib.Papers.MatrixFunc24.MainResults.PauliAlgebra

namespace Qatlib.Papers.MatrixFunc24.MainResults.Summary

/-- The four function families of Table 1. -/
inductive FunctionKind where
  /-- `x^m` (Section 4.1). -/
  | monomial
  /-- `T_m(x)` (Section 4.2). -/
  | chebyshev
  /-- `1/x` (Section 4.3). -/
  | inverse
  /-- `e^{iAt}` (Section 4.4). -/
  | timeEvolution
  deriving DecidableEq, Repr

/-- One row of Table 1: which problem variants are `BQP`-complete and what the
classically easy regime is. -/
structure TableRow where
  /-- The function family. -/
  fn : FunctionKind
  /-- The entry problem is `BQP`-complete in the sparse access model. -/
  entrySparseComplete : Bool
  /-- The entry problem is `BQP`-complete in the Pauli access model. -/
  entryPauliComplete : Bool
  /-- The local-measurement problem is `BQP`-complete. -/
  localMeasurementComplete : Bool
  /-- The classical regime, recorded as the paper's condition (doc string). -/
  classicalRegime : String

/-- Table 1 of the paper (p. 5). -/
def table1 : List TableRow :=
  [ { fn := FunctionKind.monomial, entrySparseComplete := true,
      entryPauliComplete := true, localMeasurementComplete := true,
      classicalRegime := "‖A‖ ≤ 1 - η; ‖A‖₁ ≤ 1; super-sparse; L = O(log log N)" },
    { fn := FunctionKind.chebyshev, entrySparseComplete := true,
      entryPauliComplete := true, localMeasurementComplete := true,
      classicalRegime := "s = O(1), m = O(log log N); suppressed norm; `1/ε = Ω(1)` hardness" },
    { fn := FunctionKind.inverse, entrySparseComplete := true,
      entryPauliComplete := true, localMeasurementComplete := true,
      classicalRegime := "κ_A, s = O(1); ‖A‖₁, λ_A ≤ 1/poly log N' still hard" },
    { fn := FunctionKind.timeEvolution, entrySparseComplete := true,
      entryPauliComplete := true, localMeasurementComplete := true,
      classicalRegime := "‖A‖₁ t, λ_A t = O(log log N); constant-time, O(1)-sparse" } ]

/-- Table 1 has one row per function family. -/
theorem table1_length : table1.length = 4 := by
  simp [table1]

/-- Both access-model flags in each recorded table row are true. -/
theorem table1_all_complete :
    table1.all (fun r => r.entrySparseComplete && r.entryPauliComplete) = true := by
  simp [table1]

end Qatlib.Papers.MatrixFunc24.MainResults.Summary
