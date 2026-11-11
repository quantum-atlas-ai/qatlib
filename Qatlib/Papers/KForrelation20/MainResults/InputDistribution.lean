/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false

/-!
# The `(δ, k)`-Forrelation input distribution

Bansal–Sinha, *$k$-Forrelation optimally separates quantum and classical query
complexity*, fixed arXiv:2008.07003v3, §1.1 (equations (1.1)–(1.3)) and §3
(Figure 1 and Theorem 3.1, pages 15–16).

Figure 1 samples the `1`-distribution by rounding `ϕ(U) ⊞ ϕ(V)` to `{±1}` and the
`0`-distribution uniformly.  Theorem 3.1 shows that the two sides are supported on
the promise regions of `(δ, k)`-Forrelation with probability `1 − 4/(δ²N)` and at
least `6δ` respectively.  This file records the real `k`-Forrelation function (1.1),
its `k = 2` quadratic form (1.2), and the computation behind the `p₀` half of
Theorem 3.1: the `0`-distribution is uniform on `{±1}^{kN}`, the first moment of
`forr_k` vanishes, the second moment is `‖A‖_F²/N² ≤ 1/N`, and Chebyshev's
inequality gives `p₀(forr_δ,k is a 1-input) ≤ 4/(δ²N)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.KForrelation20.MainResults

/-- Boolean bits read as the paper's `z ∈ {±1}`: `true ↦ 1`, `false ↦ −1`. -/
def toSign (b : Bool) : ℝ := if b then 1 else -1

/-- Flipping a sign bit negates the corresponding `±1` value. -/
theorem toSign_not (b : Bool) : toSign (!b) = -toSign b := by
  cases b <;> simp [toSign]

/-- Every sign is a unit: `(±1)² = 1`. -/
theorem toSign_sq (b : Bool) : toSign b ^ 2 = 1 := by
  cases b <;> norm_num [toSign]

/-- The real `k`-Forrelation function (1.1) for an `N × N` matrix `H` and blocks
`z = (z₁, …, z_k)`:
`forr_k(z) = (1/N) Σ_{(i₁,…,i_k)} z₁(i₁) H_{i₁i₂} z₂(i₂) ⋯ H_{i_{k−1}i_k} z_k(i_k)`.

The normalised Hadamard matrix of the paper is a special case of a matrix with
orthonormal columns; the statements below only use that hypothesis. -/
def forrK {N : ℕ} (k : ℕ) (H : Matrix (Fin N) (Fin N) ℝ) (z : Fin k → Fin N → Bool) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin k → Fin N,
    (∏ j : Fin k, toSign (z j (i j))) *
      (∏ j : Fin k, if h : (j : ℕ) + 1 < k then H (i j) (i ⟨(j : ℕ) + 1, h⟩) else 1)

/-- Pair the two blocks of a `Fin 2`-indexed family of sign strings. -/
def finTwoArrowEquiv (α : Type) : (Fin 2 → α) ≃ α × α where
  toFun f := (f 0, f 1)
  invFun p := fun i => if i = 0 then p.1 else p.2
  left_inv f := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    simp

/-- Equation (1.2) for `k = 2`: the `k`-Forrelation sum collapses to the quadratic
form `forr₂(z) = (1/N) Σ_{i,j} z₁(i) H_{ij} z₂(j)`. -/
theorem forrK_two {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (z : Fin 2 → Fin N → Bool) :
    forrK 2 H z = (N : ℝ)⁻¹ *
      ∑ p : Fin N × Fin N, toSign (z 0 p.1) * H p.1 p.2 * toSign (z 1 p.2) := by
  set g : (Fin 2 → Fin N) → ℝ := fun i =>
    (∏ j : Fin 2, toSign (z j (i j))) *
      (∏ j : Fin 2, if h : (j : ℕ) + 1 < 2 then H (i j) (i ⟨(j : ℕ) + 1, h⟩) else 1)
  have hunfold : forrK 2 H z = (N : ℝ)⁻¹ * ∑ i, g i := rfl
  rw [hunfold]
  congr 1
  trans ∑ p : Fin N × Fin N, g ((finTwoArrowEquiv (Fin N)).symm p)
  · exact (Equiv.sum_comp (finTwoArrowEquiv (Fin N)).symm g).symm
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
      simp [g, finTwoArrowEquiv, Fin.prod_univ_two]
      ring))

/-- Orthogonality of the sign characters on the cube: averaging `z_i z_r` over the
uniform distribution on `{±1}^N` gives `2^N` when `i = r` and vanishes otherwise. -/
theorem sum_toSign_mul {N : ℕ} (i r : Fin N) :
    ∑ x : Fin N → Bool, toSign (x i) * toSign (x r) = if i = r then (2 : ℝ) ^ N else 0 := by
  by_cases h : i = r
  · subst h
    have h1 : ∀ x : Fin N → Bool, toSign (x i) * toSign (x i) = 1 := by
      intro x
      rw [← pow_two, toSign_sq]
    simp only [h1, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp [Fintype.card_fin, Fintype.card_bool]
  · have hne : r ≠ i := Ne.symm h
    let flip : (Fin N → Bool) → (Fin N → Bool) := fun x => Function.update x i (!x i)
    have hflip_flip : ∀ x, flip (flip x) = x := by
      intro x
      funext t
      by_cases ht : t = i
      · subst ht
        simp [flip]
      · simp [flip, Function.update_of_ne ht]
    have hflip_same : ∀ x, flip x i = !x i := by
      intro x
      simp [flip]
    have hflip_other : ∀ x, flip x r = x r := by
      intro x
      simp [flip, Function.update_of_ne hne]
    let e : (Fin N → Bool) ≃ (Fin N → Bool) :=
      { toFun := flip, invFun := flip, left_inv := hflip_flip, right_inv := hflip_flip }
    have hsum : ∑ x : Fin N → Bool, toSign (x i) * toSign (x r)
        = ∑ x : Fin N → Bool, toSign (flip x i) * toSign (flip x r) := by
      simpa [e] using
        (Equiv.sum_comp e (fun x : Fin N → Bool => toSign (x i) * toSign (x r))).symm
    have hneg : ∑ x : Fin N → Bool, toSign (flip x i) * toSign (flip x r)
        = -∑ x : Fin N → Bool, toSign (x i) * toSign (x r) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [hflip_same x, hflip_other x, toSign_not]
      ring
    rw [if_neg h]
    linarith [hsum, hneg]

/-- Level-one orthogonality on the cube: `Σ_x (Σ_i c_i x_i)² = 2^N Σ_i c_i²`. -/
theorem cube_sum_sq {N : ℕ} (c : Fin N → ℝ) :
    ∑ x : Fin N → Bool, (∑ i, c i * toSign (x i)) ^ 2 = (2 : ℝ) ^ N * ∑ i, c i ^ 2 := by
  have hexp : ∀ x : Fin N → Bool, (∑ i, c i * toSign (x i)) ^ 2
      = ∑ i, ∑ r, (c i * c r) * (toSign (x i) * toSign (x r)) := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun r _ => by ring))
  simp only [hexp]
  calc ∑ x : Fin N → Bool, ∑ i, ∑ r, (c i * c r) * (toSign (x i) * toSign (x r))
      = ∑ i, ∑ x : Fin N → Bool, ∑ r, (c i * c r) * (toSign (x i) * toSign (x r)) :=
        Finset.sum_comm
    _ = ∑ i, ∑ r, ∑ x : Fin N → Bool, (c i * c r) * (toSign (x i) * toSign (x r)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ i, ∑ r, (c i * c r) * (∑ x : Fin N → Bool, toSign (x i) * toSign (x r)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun r _ => ?_))
        exact (Finset.mul_sum _ _ _).symm
    _ = ∑ i, ∑ r, (c i * c r) * (if i = r then (2 : ℝ) ^ N else 0) := by
        simp only [sum_toSign_mul]
    _ = ∑ i, (c i * c i) * (2 : ℝ) ^ N := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_eq_single i]
        · simp
        · intro r _ hr
          simp [show i ≠ r from fun h => hr h.symm]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
    _ = (2 : ℝ) ^ N * ∑ i, c i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

/-- Second moment of the level-`2` Forrelation quadratic form.  For any matrix `A`
and independent uniform sign strings `x, y ∈ {±1}^N`,
`E[((Σ_{ij} A_{ij} x_i y_j))²] = Σ_{ij} A_{ij}²`; this is the computation
`E_{p₀}[forr_k(Z)²] = ‖A‖_F² / N² ≤ 1/N` of the proof of Theorem 3.1, page 16. -/
theorem second_moment {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    ∑ p : (Fin N → Bool) × (Fin N → Bool),
        (∑ i, ∑ j, A i j * toSign (p.1 i) * toSign (p.2 j)) ^ 2
      = (2 : ℝ) ^ N * (2 : ℝ) ^ N * ∑ i, ∑ j, A i j ^ 2 := by
  rw [Fintype.sum_prod_type]
  have hsplit : ∀ y : Fin N → Bool, ∀ x : Fin N → Bool,
      (∑ i, ∑ j, A i j * toSign (x i) * toSign (y j))
        = ∑ i, (∑ j, A i j * toSign (y j)) * toSign (x i) := by
    intro y x
    refine Finset.sum_congr rfl (fun i _ => ?_)
    calc ∑ j, A i j * toSign (x i) * toSign (y j)
        = ∑ j, (A i j * toSign (y j)) * toSign (x i) :=
          Finset.sum_congr rfl (fun j _ => by ring)
      _ = (∑ j, A i j * toSign (y j)) * toSign (x i) := (Finset.sum_mul ..).symm
  have hx : ∀ y : Fin N → Bool,
      ∑ x : Fin N → Bool, (∑ i, ∑ j, A i j * toSign (x i) * toSign (y j)) ^ 2
        = (2 : ℝ) ^ N * ∑ i, (∑ j, A i j * toSign (y j)) ^ 2 := by
    intro y
    simp only [hsplit y]
    exact cube_sum_sq (fun i : Fin N => ∑ j, A i j * toSign (y j))
  calc ∑ x : Fin N → Bool, ∑ y : Fin N → Bool,
          (∑ i, ∑ j, A i j * toSign (x i) * toSign (y j)) ^ 2
      = ∑ y : Fin N → Bool, ∑ x : Fin N → Bool,
          (∑ i, ∑ j, A i j * toSign (x i) * toSign (y j)) ^ 2 := Finset.sum_comm
    _ = ∑ y : Fin N → Bool, (2 : ℝ) ^ N * ∑ i, (∑ j, A i j * toSign (y j)) ^ 2 := by
          simp only [hx]
    _ = (2 : ℝ) ^ N * ∑ y : Fin N → Bool, ∑ i, (∑ j, A i j * toSign (y j)) ^ 2 := by
          rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ N * ∑ i, ∑ y : Fin N → Bool, (∑ j, A i j * toSign (y j)) ^ 2 := by
          rw [Finset.sum_comm]
    _ = (2 : ℝ) ^ N * ∑ i, ((2 : ℝ) ^ N * ∑ j, A i j ^ 2) := by
          simp only [cube_sum_sq]
    _ = (2 : ℝ) ^ N * (2 : ℝ) ^ N * ∑ i, ∑ j, A i j ^ 2 := by
          rw [← Finset.mul_sum, mul_assoc]

/-- Chebyshev's inequality on a finite probability space: the number of points where
`|f|` is at least `ε` is at most `Σ f² / ε²`. -/
theorem card_filter_le_sum_sq {α : Type} [Fintype α] (f : α → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ((Finset.univ.filter (fun x => ε ≤ |f x|)).card : ℝ) ≤ (∑ x, f x ^ 2) / ε ^ 2 := by
  set s : Finset α := Finset.univ.filter (fun x : α => ε ≤ |f x|)
  have hle : ∀ x ∈ s, ε ^ 2 ≤ f x ^ 2 := by
    intro x hx
    have hx' : ε ≤ |f x| := (Finset.mem_filter.mp hx).2
    have h2 : ε ^ 2 ≤ |f x| ^ 2 := pow_le_pow_left₀ hε.le hx' 2
    rwa [sq_abs] at h2
  have h1 : (s.card : ℝ) * ε ^ 2 ≤ s.sum (fun x => f x ^ 2) := by
    have := Finset.card_nsmul_le_sum s (fun x => f x ^ 2) (ε ^ 2) hle
    simpa [nsmul_eq_mul] using this
  have h2 : s.sum (fun x => f x ^ 2) ≤ ∑ x, f x ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) ?_
    intro x _ _
    positivity
  exact (le_div_iff₀ (by positivity)).mpr (le_trans h1 h2)

/-- The squared Frobenius norm of a matrix with orthonormal columns is its dimension:
`Σ_{ij} H_{ij}² = N` when `Hᵀ H = 1`. -/
theorem frobenius_sq_of_orthonormal_columns {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hH : Hᵀ * H = 1) : ∑ i, ∑ j, H i j ^ 2 = (N : ℝ) := by
  have hcol : ∀ j : Fin N, ∑ i, H i j ^ 2 = 1 := by
    intro j
    have h := congrFun (congrFun hH j) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    simpa [pow_two] using h
  rw [Finset.sum_comm]
  simp [hcol]

/-- Theorem 3.1, `p₀` half, at `k = 2`.  Under the uniform distribution `p₀` on the
pair of blocks `(z₁, z₂) ∈ {±1}^{2N}`, the probability that `(δ, 2)`-Forrelation is
*not* a `0`-input, i.e. `|forr₂(z)| ≥ δ/2`, is at most `4/(δ²N)`; equivalently
`p₀(forr_{δ,2} outputs 0) ≥ 1 − 4/(δ²N)`, matching the `p₀` half of Theorem 3.1.

The proof is the paper's: the first moment vanishes and the second moment is
`‖H‖_F²/N² = 1/N`, so Chebyshev's inequality gives the bound.  The `p₁` half of
Theorem 3.1 (the `6δ` lower bound) needs Lemma 4.6 and is not included here. -/
theorem theorem3_1_p0_two {N : ℕ} (hN : 0 < N) (H : Matrix (Fin N) (Fin N) ℝ)
    (hH : Hᵀ * H = 1) {δ : ℝ} (hδ : 0 < δ) :
    ((Finset.univ.filter (fun p : (Fin N → Bool) × (Fin N → Bool) =>
        δ / 2 ≤ |(N : ℝ)⁻¹ * ∑ i, ∑ j, H i j * toSign (p.1 i) * toSign (p.2 j)|)).card : ℝ)
      ≤ 4 * (2 : ℝ) ^ (2 * N) / (δ ^ 2 * N) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hFrob := frobenius_sq_of_orthonormal_columns H hH
  have hfrob2 : ∑ i, ∑ j, ((N : ℝ)⁻¹ * H i j) ^ 2 = ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) := by
    have hstep : ∀ i, ∑ j, ((N : ℝ)⁻¹ * H i j) ^ 2 = ((N : ℝ)⁻¹) ^ 2 * ∑ j, H i j ^ 2 := by
      intro i
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    simp only [hstep]
    rw [← Finset.mul_sum, hFrob]
  have hcongr : ∀ p : (Fin N → Bool) × (Fin N → Bool),
      ((N : ℝ)⁻¹ * ∑ i, ∑ j, H i j * toSign (p.1 i) * toSign (p.2 j)) ^ 2
        = (∑ i, ∑ j, ((N : ℝ)⁻¹ * H i j) * toSign (p.1 i) * toSign (p.2 j)) ^ 2 := by
    intro p
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hsq : ∑ p : (Fin N → Bool) × (Fin N → Bool),
        ((N : ℝ)⁻¹ * ∑ i, ∑ j, H i j * toSign (p.1 i) * toSign (p.2 j)) ^ 2
      = (2 : ℝ) ^ (2 * N) / (N : ℝ) := by
    simp only [hcongr]
    rw [second_moment (fun i j => (N : ℝ)⁻¹ * H i j), hfrob2]
    rw [show (2 : ℝ) ^ (2 * N) = (2 : ℝ) ^ N * (2 : ℝ) ^ N by
      rw [← pow_add]
      ring]
    field_simp
  calc ((Finset.univ.filter (fun p : (Fin N → Bool) × (Fin N → Bool) =>
          δ / 2 ≤ |(N : ℝ)⁻¹ * ∑ i, ∑ j, H i j * toSign (p.1 i) * toSign (p.2 j)|)).card : ℝ)
      ≤ (∑ p : (Fin N → Bool) × (Fin N → Bool),
          ((N : ℝ)⁻¹ * ∑ i, ∑ j, H i j * toSign (p.1 i) * toSign (p.2 j)) ^ 2) /
            (δ / 2) ^ 2 :=
        card_filter_le_sum_sq _ (by positivity)
    _ = 4 * (2 : ℝ) ^ (2 * N) / (δ ^ 2 * N) := by
        rw [hsq]
        field_simp
        norm_num

end Qatlib.Papers.KForrelation20.MainResults
