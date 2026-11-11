/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.UnitaryLearn09.MainResults.MeasureRotate

set_option backward.isDefEq.respectTransparency false

/-!
# UnitaryLearn09 — optimal estimation form and the `F_est` formula

Fixed source: Bisio–Chiribella–D'Ariano–Facchini–Perinotti,
*Optimal quantum learning of a unitary transformation*, arXiv:0903.0543v2
(PDF SHA-256 7740f8bf94c88b19a046c4c627cda8edf148bf92fe178c381fd20bceede57048),
Sec. III A Eqs. (17)–(25) and Lemma 2.

For each irreducible block `K` of the decomposition of `U^{⊗N}` the paper builds
two vectors of the multiplicity-space Choi module:

* the stored-state vector `|α_K⟩ = ⊕_j √(p_j/d_j)|I_{m_K^{(j)}}⟩⟩` (Eq. (18)),
  which is exactly the block of the optimal input state of Lemma 2;
* the estimation-POVM vector `|β_K⟩ = ⊕_j √d_j |I_{m_K^{(j)}}⟩⟩` of Theorem 1.

The estimation-based retrieving strategy has Choi operator
`R_est = ⊕_K (I_K^{⊗2} ⊗ |β_K⟩⟨β_K|)/d_K`, and Eq. (25) computes its fidelity as
`F_est = ∑_K |⟨α_K|β_K⟩|²/d²`.  The key scalar input is
`⟨α_K|β_K⟩ = ∑_{j∈P_KK} m_K^{(j)} √p_j`, which is what this file proves.

The vectors live in the direct sum `⊕_j (ℂ^{m_j} ⊗ ℂ^{m_j})`, modelled as the
sigma type `Σ j, Fin m_j × Fin m_j` of matrix coordinates.  The `|I_j⟩⟩` are the
column-stack vectorizations of the multiplicity-space identities; their overlap
`⟨⟨I_j|I_j⟩⟩ = m_j` is the Hilbert–Schmidt trace `m_j`.

The Schur decomposition that produces the block data from `U^{⊗N}`, and the
optimality bound `F ≤ F_est` of Eqs. (22)–(24), are not formalized here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.UnitaryLearn09.MainResults

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Index set of the direct sum `⊕_j (ℂ^{m_j} ⊗ ℂ^{m_j})`: a block label `j`
together with the pair of multiplicity-space coordinates `(a, b)`. -/
abbrev blockIdx (m : J → ℕ) : Type _ := Σ j : J, Fin (m j) × Fin (m j)

/-- Lemma 2 / Eq. (18): the stored-state block vector
`α_j = √(p_j/d_j) |I_j⟩⟩`, i.e. the entries `√(p_j/d_j) · δ_{ab}`. -/
def alphaBlock (p : J → ℝ) (d m : J → ℕ) : blockIdx m → ℂ :=
  fun x => ((Real.sqrt (p x.1 / (d x.1 : ℝ)) : ℝ) : ℂ) * (if x.2.1 = x.2.2 then 1 else 0)

/-- Theorem 1: the estimation-POVM block vector `β_j = √d_j |I_j⟩⟩`, i.e. the
entries `√d_j · δ_{ab}`. -/
def betaBlock (d m : J → ℕ) : blockIdx m → ℂ :=
  fun x => ((Real.sqrt (d x.1 : ℝ) : ℝ) : ℂ) * (if x.2.1 = x.2.2 then 1 else 0)

omit [Fintype J] [DecidableEq J] in
/-- The overlap `⟨⟨I_j|I_j⟩⟩` of the vectorized `m_j × m_j` identity with itself
is its Hilbert–Schmidt trace, i.e. `m_j`. -/
theorem identityBlock_overlap (m : J → ℕ) (j : J) :
    (∑ a : Fin (m j), ∑ b : Fin (m j),
        (if a = b then (1 : ℂ) else 0)) = (m j : ℂ) := by
  rw [Finset.sum_comm]
  simp

omit [DecidableEq J] in
/-- The per-block inner product `⟨α_K|β_K⟩ = ∑_{j} m_j √p_j` of Eq. (25): the
overlap of the stored-state vector and the estimation-POVM vector.  This is the
scalar that turns the estimation strategy's fidelity into `F_est`. -/
theorem inner_alpha_beta {p : J → ℝ} {d m : J → ℕ}
    (hd : ∀ j, 0 < d j) (hp : ∀ j, 0 ≤ p j) :
    (star (alphaBlock p d m)) ⬝ᵥ (betaBlock d m) =
      ∑ j : J, (m j : ℂ) * (Real.sqrt (p j) : ℂ) := by
  rw [dotProduct, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  have step : ∀ a b : Fin (m j),
      star (alphaBlock p d m ⟨j, a, b⟩) * betaBlock d m ⟨j, a, b⟩
        = ((Real.sqrt (p j) : ℝ) : ℂ) * (if a = b then (1 : ℂ) else 0) := by
    intro a b
    have hdj : (0 : ℝ) < (d j : ℝ) := by exact_mod_cast hd j
    have hsqrt : ((Real.sqrt (p j / (d j : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt (d j : ℝ)) : ℂ) = ((Real.sqrt (p j) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_inj,
        ← Real.sqrt_mul (div_nonneg (hp j) (le_of_lt hdj))]
      congr 1
      field_simp
    by_cases h : a = b
    · subst h
      simp only [alphaBlock, betaBlock, if_true, mul_one,
        Complex.star_def, Complex.conj_ofReal]
      exact hsqrt
    · simp only [alphaBlock, betaBlock, h, if_false, mul_zero, star_zero]
  simp only [Pi.star_apply, step]
  have hfac : (∑ x : Fin (m j), ∑ x_1 : Fin (m j),
        ((Real.sqrt (p j) : ℝ) : ℂ) * (if x = x_1 then (1 : ℂ) else 0))
      = ((Real.sqrt (p j) : ℝ) : ℂ) *
          (∑ x : Fin (m j), ∑ x_1 : Fin (m j),
            (if x = x_1 then (1 : ℂ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  rw [hfac, identityBlock_overlap m j]
  ring

/-- The estimation fidelity of a single irreducible block, `|⟨α_K|β_K⟩|²/d²`
(Eq. (25) term), written as a real number. -/
def blockEstFidelity (p : J → ℝ) (d m : J → ℕ) (D : ℕ) : ℝ :=
  ‖(star (alphaBlock p d m)) ⬝ᵥ (betaBlock d m)‖ ^ 2 / (D : ℝ) ^ 2

omit [DecidableEq J] in
/-- Eq. (25): the per-block estimation fidelity is
`(∑_j m_j √p_j)² / d²`.  This is the `F_est` term that the optimal
measure-and-rotate strategy attains. -/
theorem blockEstFidelity_eq {p : J → ℝ} {d m : J → ℕ}
    (hd : ∀ j, 0 < d j) (hp : ∀ j, 0 ≤ p j) (D : ℕ) :
    blockEstFidelity p d m D =
      (∑ j : J, (m j : ℝ) * Real.sqrt (p j)) ^ 2 / (D : ℝ) ^ 2 := by
  unfold blockEstFidelity
  rw [inner_alpha_beta hd hp]
  congr 1
  have hreal : (∑ j : J, (m j : ℂ) * (Real.sqrt (p j) : ℂ))
      = ((∑ j : J, (m j : ℝ) * Real.sqrt (p j) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The PSD upper bound of Eqs. (22)–(23)

The estimation fidelity of *any* retrieving strategy is bounded by a Cauchy–Schwarz
argument that exploits the positivity of the block operators `R_{KK}`.  Abstractly,
if `R = ∑_i |w_i⟩⟨w_i|` is a positive semidefinite operator (every PSD matrix admits
such a rank-one decomposition) and `v = ∑_j v_j` is a vector split into `j`-blocks,
then the quadratic form is sub-multiplicative over the splitting:

  `⟨v|R|v⟩ = ∑_i |⟨w_i, v⟩|² ≤ (∑_j √(⟨v_j|R|v_j⟩))²`.

This is exactly the "first bound, using the positivity of `R_{KK}`" of Eq. (23), the
step that turns the bilinear fidelity `(22)` into the squared sum `(23)`.
-/

/-- The `ℓ²` coordinates of a vector against a rank-one decomposition:
`coord w y = (⟨w_0, y⟩, …, ⟨w_{m-1}, y⟩) : ℓ²(Fin m, ℂ)`.  Its squared norm is the
quadratic form of the PSD operator `∑_i |w_i⟩⟨w_i|`. -/
def coord {ι : Type*} [Fintype ι] {m : ℕ} (w : Fin m → ι → ℂ) (y : ι → ℂ) :
    EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 (fun i => (star (w i)) ⬝ᵥ y)

/-- Definitional unfolding: the `i`-th coordinate of `coord w y` is `⟨w_i, y⟩`. -/
@[simp] lemma coord_apply {ι : Type*} [Fintype ι] {m : ℕ} (w : Fin m → ι → ℂ) (y : ι → ℂ)
    (i : Fin m) : coord w y i = (star (w i)) ⬝ᵥ y := rfl

/-- `coord` is additive over a finite sum of vectors (the maps `y ↦ ⟨w_i, y⟩` are
linear, so the coordinates of a sum are the sums of coordinates). -/
lemma coord_sum {ι κ : Type*} [Fintype ι] [Fintype κ] {m : ℕ}
    (w : Fin m → ι → ℂ) (v : κ → ι → ℂ) :
    coord w (∑ j, v j) = ∑ j, coord w (v j) := by
  have h : (coord w (∑ j, v j)).ofLp = (∑ j, coord w (v j)).ofLp := by
    funext i
    simp only [coord, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
    exact dotProduct_sum (star (w i)) (Finset.univ : Finset κ) v
  exact WithLp.ofLp_injective (p := 2) h

/-- The squared norm of `coord w y` is the quadratic form `∑_i |⟨w_i, y⟩|²` of the
PSD operator `R = ∑_i |w_i⟩⟨w_i|`, i.e. `⟨y|R|y⟩`. -/
lemma norm_coord_sq {ι : Type*} [Fintype ι] {m : ℕ} (w : Fin m → ι → ℂ) (y : ι → ℂ) :
    ‖coord w y‖ ^ 2 = ∑ i : Fin m, Complex.normSq ((star (w i)) ⬝ᵥ y) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coord_apply, Complex.normSq_eq_norm_sq]

/-- **Eqs. (22)–(23), the positivity bound.**  For a PSD operator `R = ∑_i |w_i⟩⟨w_i|`
and a vector `v = ∑_j v_j` split into blocks, the bilinear quadratic form is bounded
by the square of the sum of the per-block square roots:

  `⟨v|R|v⟩ = ∑_i |⟨w_i, v⟩|² ≤ (∑_j √(⟨v_j|R|v_j⟩))²`.

This is a direct consequence of the triangle inequality in `ℓ²`, whose squared norm
`‖coord w y‖²` equals the quadratic form `⟨y|R|y⟩`. -/
theorem psd_quadForm_le {ι κ : Type*} [Fintype ι] [Fintype κ] {m : ℕ}
    (w : Fin m → ι → ℂ) (v : κ → ι → ℂ) :
    (∑ i : Fin m, Complex.normSq ((star (w i)) ⬝ᵥ (∑ j, v j)))
      ≤ (∑ j : κ, Real.sqrt (∑ i : Fin m, Complex.normSq ((star (w i)) ⬝ᵥ (v j)))) ^ 2 := by
  rw [← norm_coord_sq w (∑ j, v j), coord_sum]
  have hRHS : (∑ j : κ, Real.sqrt (∑ i : Fin m, Complex.normSq ((star (w i)) ⬝ᵥ (v j))))
      = ∑ j : κ, ‖coord w (v j)‖ := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← norm_coord_sq w (v j), Real.sqrt_sq (norm_nonneg _)]
  rw [hRHS]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2

end Qatlib.Papers.UnitaryLearn09.MainResults
