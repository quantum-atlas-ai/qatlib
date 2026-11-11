/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport.Basic

/-!
# Two-level unitary elimination

The matrix `elemOp` embeds a two-by-two block into selected coordinates and uses identity rows
elsewhere. The condition `IsUnitaryBlock` guarantees that this embedding is unitary when the
coordinate indices are distinct.

The normalization `twoLevelNorm` produces a block that clears one of two selected column
entries. When those entries are not both zero, the operation is unitary and fixes the complement
of any set containing the two selected coordinates, supporting the elimination argument in
[Jordan2008].

## Main statements

* `elemOp_mem_unitaryGroup`: a unitary two-by-two block yields a unitary embedded operation.
* `twoLevelBlock_isUnitary`: the normalized elimination coefficients satisfy the unitary block
  conditions.
* `exists_halfSupport_kill_entry`: a unitary fixing the complement of the supplied support
  clears the selected entry.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

variable {m : ℕ}

/-- The four row-orthonormality equations for the two-by-two complex matrix with rows `(a, b)`
and `(c, d)`. -/
def IsUnitaryBlock (a b c d : ℂ) : Prop :=
  a * star a + b * star b = 1 ∧
    c * star c + d * star d = 1 ∧
    a * star c + b * star d = 0 ∧
    c * star a + d * star b = 0

/-- The matrix inserting the coefficients `a`, `b`, `c`, and `d` in rows and columns `i` and
`j`, with identity rows elsewhere; row `i` takes precedence when the indices coincide. -/
def elemOp (i j : Fin m) (a b c d : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun r s =>
    if r = i then (if s = i then a else if s = j then b else 0)
    else if r = j then (if s = i then c else if s = j then d else 0)
    else if r = s then 1 else 0

/-- Row `i` of `elemOp` has coefficient `a` at column `i`, coefficient `b` at column `j` when
distinct from `i`, and zero elsewhere. -/
lemma elemOp_row_i (i j : Fin m) (a b c d : ℂ) (s : Fin m) :
    elemOp i j a b c d i s = (if s = i then a else if s = j then b else 0) := by
  unfold elemOp
  simp [Matrix.of_apply]

/-- For distinct selected indices, row `j` of `elemOp` has coefficients `c` and `d` in columns
`i` and `j` and is zero elsewhere. -/
lemma elemOp_row_j (i j : Fin m) (hij : i ≠ j) (a b c d : ℂ) (s : Fin m) :
    elemOp i j a b c d j s = (if s = i then c else if s = j then d else 0) := by
  unfold elemOp
  simp only [Matrix.of_apply]
  rw [if_neg (Ne.symm hij)]
  simp

/-- Every row outside the two selected indices agrees with the corresponding identity row. -/
lemma elemOp_row_other (i j r : Fin m) (hr : r ≠ i) (hrj : r ≠ j) (a b c d : ℂ)
    (s : Fin m) :
    elemOp i j a b c d r s = (if r = s then 1 else 0) := by
  unfold elemOp
  simp only [Matrix.of_apply]
  rw [if_neg hr, if_neg hrj]

/-- A finite sum supported at two distinct indices, with the stated values `x` and `y`, equals
`x + y`. -/
private lemma sum_two_terms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (f : ι → ℂ) (x y : ℂ)
    (hf : ∀ s, f s = (if s = i then x else 0) + (if s = j then y else 0)) :
    ∑ s, f s = x + y := by
  rw [Finset.sum_congr rfl (fun s _ => hf s), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- Left multiplication by `elemOp` replaces row `i` by `a` times row `i` plus `b` times row
`j`. -/
lemma elemOp_mul_apply_i (U : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m)
    (hij : i ≠ j) (a b c d : ℂ) (k : Fin m) :
    (elemOp i j a b c d * U) i k = a * U i k + b * U j k := by
  rw [Matrix.mul_apply]
  refine sum_two_terms i j hij
    (fun s => elemOp i j a b c d i s * U s k) (a * U i k) (b * U j k) (fun s => ?_)
  simp only [elemOp_row_i]
  by_cases hsi : s = i
  · rw [hsi]
    simp [hij, Ne.symm hij]
  · by_cases hsj : s = j
    · rw [hsj]
      simp [hij, Ne.symm hij]
    · simp [hsi, hsj]

/-- Left multiplication by `elemOp` replaces row `j` by `c` times row `i` plus `d` times row
`j`. -/
lemma elemOp_mul_apply_j (U : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m)
    (hij : i ≠ j) (a b c d : ℂ) (k : Fin m) :
    (elemOp i j a b c d * U) j k = c * U i k + d * U j k := by
  rw [Matrix.mul_apply]
  refine sum_two_terms i j hij
    (fun s => elemOp i j a b c d j s * U s k) (c * U i k) (d * U j k) (fun s => ?_)
  simp only [elemOp_row_j i j hij]
  by_cases hsi : s = i
  · rw [hsi]
    simp [hij, Ne.symm hij]
  · by_cases hsj : s = j
    · rw [hsj]
      simp [hij, Ne.symm hij]
    · simp [hsi, hsj]

/-- Left multiplication by `elemOp` leaves every row outside the two selected indices unchanged. -/
lemma elemOp_mul_apply_other (U : Matrix (Fin m) (Fin m) ℂ) (i j r : Fin m)
    (hij : i ≠ j) (hr : r ≠ i) (hrj : r ≠ j) (a b c d : ℂ) (k : Fin m) :
    (elemOp i j a b c d * U) r k = U r k := by
  rw [Matrix.mul_apply]
  have hterm : ∀ s : Fin m,
      elemOp i j a b c d r s * U s k = (if r = s then U r k else 0) := by
    intro s
    rw [elemOp_row_other i j r hr hrj]
    by_cases hsr : r = s
    · rw [hsr]
      simp
    · simp [hsr]
  rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_ite_eq]
  simp

/-- The sum of entries of row `i` times their conjugates is `a * star a + b * star b`. -/
private lemma elemOp_sum_ii (i j : Fin m) (hij : i ≠ j) (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d i s * star (elemOp i j a b c d i s) =
      a * star a + b * star b := by
  refine sum_two_terms i j hij
    (fun s => elemOp i j a b c d i s * star (elemOp i j a b c d i s))
    (a * star a) (b * star b) (fun s => ?_)
  simp only [elemOp_row_i]
  by_cases hsi : s = i
  · rw [hsi]
    simp [hij, Ne.symm hij]
  · by_cases hsj : s = j
    · rw [hsj]
      simp [hij, Ne.symm hij]
    · simp [hsi, hsj]

/-- The sum of row `i` entries times conjugates of row `j` entries is `a * star c + b * star d`. -/
private lemma elemOp_sum_ij (i j : Fin m) (hij : i ≠ j) (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d i s * star (elemOp i j a b c d j s) =
      a * star c + b * star d := by
  refine sum_two_terms i j hij
    (fun s => elemOp i j a b c d i s * star (elemOp i j a b c d j s))
    (a * star c) (b * star d) (fun s => ?_)
  simp only [elemOp_row_i, elemOp_row_j i j hij]
  by_cases hsi : s = i
  · rw [hsi]
    simp [hij, Ne.symm hij]
  · by_cases hsj : s = j
    · rw [hsj]
      simp [hij, Ne.symm hij]
    · simp [hsi, hsj]

/-- The sum of row `j` entries times conjugates of row `i` entries is `c * star a + d * star b`. -/
private lemma elemOp_sum_ji (i j : Fin m) (hij : i ≠ j) (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d j s * star (elemOp i j a b c d i s) =
      c * star a + d * star b := by
  refine sum_two_terms i j hij
    (fun s => elemOp i j a b c d j s * star (elemOp i j a b c d i s))
    (c * star a) (d * star b) (fun s => ?_)
  simp only [elemOp_row_j i j hij, elemOp_row_i]
  by_cases hsi : s = i
  · rw [hsi]
    simp [hij, Ne.symm hij]
  · by_cases hsj : s = j
    · rw [hsj]
      simp [hij, Ne.symm hij]
    · simp [hsi, hsj]

/-- The sum of entries of row `j` times their conjugates is `c * star c + d * star d`. -/
private lemma elemOp_sum_jj (i j : Fin m) (hij : i ≠ j) (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d j s * star (elemOp i j a b c d j s) =
      c * star c + d * star d := by
  refine sum_two_terms i j hij
    (fun s => elemOp i j a b c d j s * star (elemOp i j a b c d j s))
    (c * star c) (d * star d) (fun s => ?_)
  simp only [elemOp_row_j i j hij]
  by_cases hsi : s = i
  · rw [hsi]
    simp [hij, Ne.symm hij]
  · by_cases hsj : s = j
    · rw [hsj]
      simp [hij, Ne.symm hij]
    · simp [hsi, hsj]

/-- An identity row outside the selected indices has sum of squared absolute values equal to
one. -/
private lemma elemOp_sum_std_same (i j p : Fin m) (hpi : p ≠ i) (hpj : p ≠ j)
    (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d p s * star (elemOp i j a b c d p s) = 1 := by
  have h : ∀ s, elemOp i j a b c d p s * star (elemOp i j a b c d p s)
      = (if p = s then (1 : ℂ) else 0) := by
    intro s
    rw [elemOp_row_other i j p hpi hpj]
    by_cases hps : p = s
    · rw [hps]
      simp
    · simp [hps]
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_eq]
  simp

/-- Pairing an identity row at `p` with the conjugate of row `q` extracts the conjugate of entry
`(q, p)`. -/
private lemma elemOp_sum_std_any (i j p q : Fin m) (hpi : p ≠ i) (hpj : p ≠ j)
    (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d p s * star (elemOp i j a b c d q s) =
      star (elemOp i j a b c d q p) := by
  have h : ∀ s, elemOp i j a b c d p s * star (elemOp i j a b c d q s)
      = (if p = s then star (elemOp i j a b c d q p) else 0) := by
    intro s
    rw [elemOp_row_other i j p hpi hpj]
    by_cases hps : p = s
    · rw [hps]
      simp
    · simp [hps]
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_eq]
  simp

/-- A row outside the selected indices has zero conjugate pairing with any distinct row. -/
private lemma elemOp_sum_std_other (i j p q : Fin m) (hij : i ≠ j) (hpi : p ≠ i)
    (hpj : p ≠ j) (hpq : p ≠ q) (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d p s * star (elemOp i j a b c d q s) = 0 := by
  have h : ∀ s, elemOp i j a b c d p s * star (elemOp i j a b c d q s)
      = (if p = s then star (elemOp i j a b c d q p) else 0) := by
    intro s
    rw [elemOp_row_other i j p hpi hpj]
    by_cases hps : p = s
    · rw [hps]
      simp
    · simp [hps]
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_eq]
  simp
  have hqp : elemOp i j a b c d q p = 0 := by
    by_cases hqi : q = i
    · rw [hqi]
      rw [elemOp_row_i]
      simp [hpi, hpj]
    · by_cases hqj : q = j
      · rw [hqj]
        rw [elemOp_row_j i j hij]
        simp [hpi, hpj]
      · rw [elemOp_row_other i j q hqi hqj]
        simp [Ne.symm hpq]
  simp [hqp]

/-- Row `i` has zero conjugate pairing with an identity row outside the selected indices. -/
private lemma elemOp_sum_i_std (i j q : Fin m) (hqi : q ≠ i) (hqj : q ≠ j)
    (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d i s * star (elemOp i j a b c d q s) = 0 := by
  have h : ∀ s, elemOp i j a b c d i s * star (elemOp i j a b c d q s)
      = (if s = q then elemOp i j a b c d i q else 0) := by
    intro s
    rw [elemOp_row_other i j q hqi hqj]
    by_cases hsq : s = q
    · rw [hsq]
      simp
    · have hqs : ¬ q = s := fun h => hsq h.symm
      rw [if_neg hqs, if_neg hsq]
      simp
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_eq']
  rw [elemOp_row_i]
  simp [hqi, hqj, Ne.symm hqi, Ne.symm hqj]

/-- For distinct selected indices, row `j` has zero conjugate pairing with an identity row
outside those indices. -/
private lemma elemOp_sum_j_std (i j q : Fin m) (hij : i ≠ j) (hqi : q ≠ i) (hqj : q ≠ j)
    (a b c d : ℂ) :
    ∑ s, elemOp i j a b c d j s * star (elemOp i j a b c d q s) = 0 := by
  have h : ∀ s, elemOp i j a b c d j s * star (elemOp i j a b c d q s)
      = (if s = q then elemOp i j a b c d j q else 0) := by
    intro s
    rw [elemOp_row_other i j q hqi hqj]
    by_cases hsq : s = q
    · rw [hsq]
      simp
    · have hqs : ¬ q = s := fun h => hsq h.symm
      rw [if_neg hqs, if_neg hsq]
      simp
  rw [Finset.sum_congr rfl (fun s _ => h s), Finset.sum_ite_eq']
  rw [elemOp_row_j i j hij]
  simp [hqi, hqj, Ne.symm hqi, Ne.symm hqj]

/-- For distinct indices, embedding a block satisfying `IsUnitaryBlock` gives a matrix in the
unitary group [Jordan2008]. -/
theorem elemOp_mem_unitaryGroup (i j : Fin m) (hij : i ≠ j) {a b c d : ℂ}
    (h : IsUnitaryBlock a b c d) :
    elemOp i j a b c d ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext p q
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, Matrix.one_apply]
  by_cases hpi : p = i
  · rw [hpi]
    by_cases hqi : q = i
    · rw [hqi]
      rw [elemOp_sum_ii i j hij, h.1]
      simp
    · by_cases hqj : q = j
      · rw [hqj]
        rw [elemOp_sum_ij i j hij, h.2.2.1]
        simp [hij, Ne.symm hij]
      · rw [elemOp_sum_i_std i j q hqi hqj]
        simp [hqi, Ne.symm hqi]
  · by_cases hpj : p = j
    · rw [hpj]
      by_cases hqi : q = i
      · rw [hqi]
        rw [elemOp_sum_ji i j hij, h.2.2.2]
        simp [hij, Ne.symm hij]
      · by_cases hqj : q = j
        · rw [hqj]
          rw [elemOp_sum_jj i j hij, h.2.1]
          simp
        · rw [elemOp_sum_j_std i j q hij hqi hqj]
          simp [hqj, Ne.symm hqj]
    · by_cases hqi : q = i
      · rw [hqi]
        have hzero : elemOp i j a b c d i p = 0 := by
          rw [elemOp_row_i]
          simp [hpi, hpj]
        rw [elemOp_sum_std_any i j p i hpi hpj, hzero, star_zero]
        simp [hpi, Ne.symm hpi]
      · by_cases hqj : q = j
        · rw [hqj]
          have hzero : elemOp i j a b c d j p = 0 := by
            rw [elemOp_row_j i j hij]
            simp [hpi, hpj]
          rw [elemOp_sum_std_any i j p j hpi hpj, hzero, star_zero]
          simp [hpj, Ne.symm hpj]
        · by_cases hpq : p = q
          · rw [hpq]
            rw [elemOp_sum_std_same i j q hqi hqj]
            simp
          · rw [elemOp_sum_std_other i j p q hij hpi hpj hpq]
            simp [hpq]

/-- The nonnegative real number `√(normSq α + normSq β)`, viewed as a complex number. -/
def twoLevelNorm (α β : ℂ) : ℂ :=
  (Real.sqrt (Complex.normSq α + Complex.normSq β) : ℂ)

/-- The square of `twoLevelNorm α β` is the complex cast of `normSq α + normSq β`. -/
lemma twoLevelNorm_mul_self (α β : ℂ) :
    twoLevelNorm α β * twoLevelNorm α β =
      ((Complex.normSq α + Complex.normSq β : ℝ) : ℂ) := by
  unfold twoLevelNorm
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt
    (add_nonneg (Complex.normSq_nonneg α) (Complex.normSq_nonneg β))]

/-- The two-level normalization is nonzero if at least one of its two inputs is nonzero. -/
lemma twoLevelNorm_ne_zero {α β : ℂ} (h : α ≠ 0 ∨ β ≠ 0) :
    twoLevelNorm α β ≠ 0 := by
  unfold twoLevelNorm
  have hsum : 0 < Complex.normSq α + Complex.normSq β := by
    rcases h with h | h
    · have hpos := Complex.normSq_pos.mpr h
      have hβ := Complex.normSq_nonneg β
      linarith
    · have hpos := Complex.normSq_pos.mpr h
      have hα := Complex.normSq_nonneg α
      linarith
  intro h0
  exact (Real.sqrt_ne_zero'.mpr hsum) (Complex.ofReal_eq_zero.mp h0)

/-- The product of a complex number and its conjugate is its real squared norm, viewed as a
complex number. -/
private lemma mul_star_eq_normSq (z : ℂ) :
    z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
  ring

/-- If `α` and `β` are not both zero, the block with rows `(star α, star β)` and `(β, -α)`,
divided by `twoLevelNorm α β`, satisfies `IsUnitaryBlock` [Jordan2008]. -/
lemma twoLevelBlock_isUnitary {α β : ℂ} (h : α ≠ 0 ∨ β ≠ 0) :
    IsUnitaryBlock (star α / twoLevelNorm α β) (star β / twoLevelNorm α β)
      (β / twoLevelNorm α β) (-α / twoLevelNorm α β) := by
  set N := twoLevelNorm α β with hNdef
  have hN : N ≠ 0 := twoLevelNorm_ne_zero h
  have hNc : star N = N := by
    show star (twoLevelNorm α β) = twoLevelNorm α β
    unfold twoLevelNorm
    rw [Complex.star_def, Complex.conj_ofReal]
  have hα : α * star α = ((Complex.normSq α : ℝ) : ℂ) := mul_star_eq_normSq α
  have hβ : β * star β = ((Complex.normSq β : ℝ) : ℂ) := mul_star_eq_normSq β
  have hα' : star α * α = ((Complex.normSq α : ℝ) : ℂ) := by rw [mul_comm, hα]
  have hβ' : star β * β = ((Complex.normSq β : ℝ) : ℂ) := by rw [mul_comm, hβ]
  have hpos : (0 : ℝ) < Complex.normSq α + Complex.normSq β := by
    rcases h with h | h
    · have hp := Complex.normSq_pos.mpr h
      have hb := Complex.normSq_nonneg β
      linarith
    · have hp := Complex.normSq_pos.mpr h
      have ha := Complex.normSq_nonneg α
      linarith
  have hsum : ((Complex.normSq α : ℝ) : ℂ) + ((Complex.normSq β : ℝ) : ℂ) =
      ((Complex.normSq α + Complex.normSq β : ℝ) : ℂ) := by
    exact (Complex.ofReal_add _ _).symm
  have hSne : ((Complex.normSq α : ℝ) : ℂ) + ((Complex.normSq β : ℝ) : ℂ) ≠ 0 := by
    rw [hsum]
    exact_mod_cast hpos.ne'
  have hSne2 : ((Complex.normSq β : ℝ) : ℂ) + ((Complex.normSq α : ℝ) : ℂ) ≠ 0 := by
    rw [add_comm]
    exact hSne
  have hN2 : N * N = ((Complex.normSq α + Complex.normSq β : ℝ) : ℂ) :=
    twoLevelNorm_mul_self α β
  have hN2a : N * N = ((Complex.normSq α : ℝ) : ℂ) + ((Complex.normSq β : ℝ) : ℂ) := by
    rw [hN2]; exact hsum.symm
  have hN2b : N * N = ((Complex.normSq β : ℝ) : ℂ) + ((Complex.normSq α : ℝ) : ℂ) := by
    rw [hN2a]
    exact add_comm _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : star α / N * star (star α / N) = (star α * α) / (N * N) := by
      rw [star_div₀, hNc, star_star, div_mul_div_comm]
    have e2 : star β / N * star (star β / N) = (star β * β) / (N * N) := by
      rw [star_div₀, hNc, star_star, div_mul_div_comm]
    rw [e1, e2, ← add_div, hα', hβ', hN2a, div_self hSne]
  · have e1 : β / N * star (β / N) = (β * star β) / (N * N) := by
      rw [star_div₀, hNc, div_mul_div_comm]
    have e2 : (-α) / N * star ((-α) / N) = (α * star α) / (N * N) := by
      rw [star_div₀, hNc, star_neg, div_mul_div_comm]
      rw [show (-α) * (-star α) = α * star α by ring]
    rw [e1, e2, ← add_div, hβ, hα, hN2b, div_self hSne2]
  · have e1 : star α / N * star (β / N) = (star α * star β) / (N * N) := by
      rw [star_div₀, hNc, div_mul_div_comm]
    have e2 : star β / N * star ((-α) / N) = (-(star β * star α)) / (N * N) := by
      rw [star_div₀, hNc, star_neg, div_mul_div_comm]
      rw [show star β * (-star α) = -(star β * star α) by ring]
    rw [e1, e2, ← add_div]
    have hz : star α * star β + -(star β * star α) = 0 := by ring
    rw [hz, zero_div]
  · have e1 : β / N * star (star α / N) = (β * α) / (N * N) := by
      rw [star_div₀, hNc, star_star, div_mul_div_comm]
    have e2 : (-α) / N * star (star β / N) = (-(α * β)) / (N * N) := by
      rw [star_div₀, hNc, star_star, div_mul_div_comm]
      rw [show (-α) * β = -(α * β) by ring]
    rw [e1, e2, ← add_div]
    have hz : β * α + -(α * β) = 0 := by ring
    rw [hz, zero_div]

/-- The normalized two-row elimination block makes entry `(j, k)` of its product with `U` vanish
for distinct `i` and `j`, including when the two selected entries both vanish [Jordan2008]. -/
lemma elemOp_twoLevel_zero (U : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m)
    (hij : i ≠ j) (k : Fin m) :
    (elemOp i j (star (U i k) / twoLevelNorm (U i k) (U j k))
        (star (U j k) / twoLevelNorm (U i k) (U j k))
        (U j k / twoLevelNorm (U i k) (U j k))
        (-(U i k) / twoLevelNorm (U i k) (U j k)) * U) j k = 0 := by
  by_cases hz : U i k = 0 ∧ U j k = 0
  · rw [elemOp_mul_apply_j U i j hij, hz.1, hz.2]
    simp
  · have hz' : U i k ≠ 0 ∨ U j k ≠ 0 := by
      rcases not_and_or.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hN := twoLevelNorm_ne_zero hz'
    rw [elemOp_mul_apply_j U i j hij]
    field_simp [hN]
    ring

/-- If the two selected entries are not both zero and both row indices lie in `S`, the
normalized elimination matrix is unitary and fixes the complement of `S` [Jordan2008]. -/
lemma elemOp_twoLevel_fixes (U : Matrix (Fin m) (Fin m) ℂ) {S : Finset (Fin m)}
    {i j : Fin m} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) {k : Fin m}
    (hne : U i k ≠ 0 ∨ U j k ≠ 0) :
    FixesComplement S
        (elemOp i j (star (U i k) / twoLevelNorm (U i k) (U j k))
          (star (U j k) / twoLevelNorm (U i k) (U j k))
          (U j k / twoLevelNorm (U i k) (U j k))
          (-(U i k) / twoLevelNorm (U i k) (U j k))) := by
  refine ⟨elemOp_mem_unitaryGroup i j hij (twoLevelBlock_isUnitary hne), ?_⟩
  intro p q hpq
  by_cases hpS : p ∈ S
  · have hqS : q ∉ S := by
      rcases hpq with hp | hq
      · exact fun _ => hp hpS
      · exact hq
    have hqi : q ≠ i := fun h => hqS (h.symm ▸ hi)
    have hqj : q ≠ j := fun h => hqS (h.symm ▸ hj)
    by_cases hpi : p = i
    · rw [hpi]
      rw [elemOp_row_i]
      simp [hqi, hqj, Ne.symm hqi, Ne.symm hqj]
    · by_cases hpj : p = j
      · rw [hpj]
        rw [elemOp_row_j i j hij]
        simp [hqi, hqj, Ne.symm hqi, Ne.symm hqj]
      · rw [elemOp_row_other i j p hpi hpj]
  · have hpi : p ≠ i := fun h => hpS (h.symm ▸ hi)
    have hpj : p ≠ j := fun h => hpS (h.symm ▸ hj)
    rw [elemOp_row_other i j p hpi hpj]

/-- If two distinct row indices lie in `S` and their selected column entries are not both zero,
there exists a unitary fixing the complement of `S` that clears the second selected entry
[Jordan2008]. -/
theorem exists_halfSupport_kill_entry (U : Matrix (Fin m) (Fin m) ℂ)
    {S : Finset (Fin m)} {i j : Fin m} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S)
    {k : Fin m} (hne : U i k ≠ 0 ∨ U j k ≠ 0) :
    ∃ W : Matrix (Fin m) (Fin m) ℂ, FixesComplement S W ∧ (W * U) j k = 0 :=
  ⟨_, elemOp_twoLevel_fixes U hij hi hj hne, elemOp_twoLevel_zero U i j hij k⟩

end Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
