/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinSysDense17.MainResults.SourceTheorem3
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# QLinSysDense17 — QSVE mathematical cores

Fixed source: L. Wossnig, Z. Zhao, A. Prakash, *A quantum linear system
algorithm for dense matrices*, arXiv:1704.06174v2 (3 May 2017).

This module formalises the mathematical cores behind the two active claims,
complementing the runtime ledger of `SourceTheorem3.lean` with verified
operator-level content:

* the Kerenidis-Prakash amplitude-encoding frames of Lemma 2.1: the explicit
  isometries `kpLeft`/`kpRight` over `ℝ` (the paper states Lemma 2 over
  `ℝ^{m×n}`; over `ℂ` the corner identity carries `Aᴴ` instead of `A`) with
  the factorisation `kpLeftᵀ · kpRight = A / ‖A‖_F` (`kp_corner`);
* the quantum-walk action of Lemma 2.3 / Eq. (3): the product of reflections
  `kpWalk = (2MMᵀ − I)(2NNᵀ − I)` maps `N v` to
  `(2σ/‖A‖_F) · M u − N v` for a singular-vector pair (`kpWalk_mulVec`);
* the rotation-angle identity of Eq. (4): the Rayleigh quotient
  `⟨N v, W N v⟩ = 2σ²/‖A‖_F² − 1` and the half-angle encoding
  `cos(θ/2) = σ/‖A‖_F` (`kpWalk_dotProduct`, `kpWalk_half_angle`);
* the eigenvalue-sign recovery of Algorithm 2 / Theorem 3's proof: the
  comparison `|lam + 2/κ| ≤ |lam|` decides the sign of every eigenvalue in
  `[−1, −1/κ] ∪ [1/κ, 1]` (`abs_shift_le_iff`, `sign_recovered_shift`);
* the Appendix Eq. (9)–(11) error mechanism: an orthogonal-register
  (Parseval-type) decomposition of the final-state error with the
  `cκ`-Lipschitz filter bound `‖|ψ̄⟩ − |ψ⟩‖ ≤ cκδ‖A‖_F`
  (`orthogonal_weighted_norm_sq`, `qsve_state_error_le`);
* the post-selection repetition bound of the runtime ledger: success
  probability `≥ 1/κ²`, so `κ²` repetitions suffice
  (`postselection_success_ge`, `postselection_repetitions_le`);
* the dense `√n` scaling behind the abstract's claim: for every complex
  matrix, `‖A‖_F ≤ √n · ‖A‖₂` (`frobNormC_le_sqrt_card_mul_opNorm`), which
  upgrades the hypothesis `‖A‖_F ≤ C√n` of `dense_runtime_le_sqrtn` to a
  theorem under a spectral-norm bound (`dense_runtime_le_sqrtn_matrix`).
-/

namespace Qatlib.Papers.QLinSysDense17.MainResults

set_option autoImplicit false

open Matrix
open scoped InnerProductSpace

/-! ## The amplitude-encoding frames of Lemma 2.1 -/

section KP

variable {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]

/-- Squared ℓ² norm of row `o` of a real matrix. -/
def rowNormSq (A : Matrix O I ℝ) (o : O) : ℝ := ∑ i, (A o i) ^ 2

/-- Squared Frobenius norm `‖A‖_F²` of a real matrix. -/
def frobNormSq (A : Matrix O I ℝ) : ℝ := ∑ o, rowNormSq A o

/-- Frobenius norm `‖A‖_F` of a real matrix. -/
noncomputable def frobNorm (A : Matrix O I ℝ) : ℝ := Real.sqrt (frobNormSq A)

/-- Row norms are nonnegative. -/
theorem rowNormSq_nonneg (A : Matrix O I ℝ) (o : O) : 0 ≤ rowNormSq A o :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `‖A‖_F²` is nonnegative. -/
theorem frobNormSq_nonneg (A : Matrix O I ℝ) : 0 ≤ frobNormSq A :=
  Finset.sum_nonneg fun o _ => rowNormSq_nonneg A o

/-- `‖A‖_F` is nonnegative. -/
theorem frobNorm_nonneg (A : Matrix O I ℝ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

/-- A zero row-norm square forces every entry of the row to vanish. -/
theorem rowNormSq_eq_zero_entry (A : Matrix O I ℝ) (o : O)
    (h : rowNormSq A o = 0) (i : I) : A o i = 0 := by
  have hmem := Finset.sum_eq_zero_iff_of_nonneg (f := fun i => (A o i) ^ 2)
    (fun i _ => sq_nonneg _) |>.mp h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hmem

/-- Collapse of a first-register indicator sum over the product index. -/
private theorem sum_prod_ite_left (F : O × I → ℝ) (o : O) :
    ∑ p : O × I, (if p.1 = o then F p else 0) = ∑ j : I, F (o, j) := by
  rw [Fintype.sum_prod_type]
  show (∑ u : O, ∑ j : I, (if u = o then F (u, j) else 0)) = _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simpa using Finset.sum_ite_eq' o (fun u => F (u, j))

/-- Collapse of a second-register indicator sum over the product index. -/
private theorem sum_prod_ite_right (F : O × I → ℝ) (i : I) :
    ∑ p : O × I, (if p.2 = i then F p else 0) = ∑ u : O, F (u, i) := by
  rw [Fintype.sum_prod_type]
  show (∑ u : O, ∑ j : I, (if j = i then F (u, j) else 0)) = _
  refine Finset.sum_congr rfl fun u _ => ?_
  simpa using Finset.sum_ite_eq' i (fun j => F (u, j))

/-- The KP left frame `M` of Lemma 2.1: `|o⟩ ↦ |o, A_o⟩`, the amplitude
encoding of the rows of `A` by normalized row vectors. A zero row is encoded
by the total-division zero vector. -/
noncomputable def kpLeft (A : Matrix O I ℝ) : Matrix (O × I) O ℝ :=
  fun p o => if p.1 = o then A p.1 p.2 / Real.sqrt (rowNormSq A p.1) else 0

/-- The KP right frame `N` of Lemma 2.1: `|i⟩ ↦ |A_F, i⟩`, the amplitude
encoding of the vector of row norms over the Frobenius norm. -/
noncomputable def kpRight (A : Matrix O I ℝ) : Matrix (O × I) I ℝ :=
  fun p i => if p.2 = i then Real.sqrt (rowNormSq A p.1) / frobNorm A else 0

/-- Lemma 2.1, part 1 (isometry of `M`): if no row of `A` vanishes then
`kpLeft A` has orthonormal columns, `Mᵀ M = 1`. -/
theorem kpLeft_isometry (A : Matrix O I ℝ) (hrow : ∀ o, rowNormSq A o ≠ 0) :
    (kpLeft A)ᵀ * kpLeft A = 1 := by
  ext o o'
  by_cases h : o = o'
  · subst o'
    have hcollapse : ((kpLeft A)ᵀ * kpLeft A) o o = ∑ j : I,
        (A o j / Real.sqrt (rowNormSq A o))
          * (A o j / Real.sqrt (rowNormSq A o)) := by
      have hval : ∀ p : O × I, ∀ x : O,
          (if p.1 = x then A p.1 p.2 / Real.sqrt (rowNormSq A p.1) else 0)
            * (if p.1 = x then A p.1 p.2 / Real.sqrt (rowNormSq A p.1) else 0)
            = if p.1 = x then (A p.1 p.2 / Real.sqrt (rowNormSq A p.1))
                * (A p.1 p.2 / Real.sqrt (rowNormSq A p.1)) else 0 := by
        intro p x
        by_cases hp : p.1 = x
        · simp [hp]
        · simp [hp]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, kpLeft, hval]
      rw [sum_prod_ite_left (fun p => (A p.1 p.2 / Real.sqrt (rowNormSq A p.1))
        * (A p.1 p.2 / Real.sqrt (rowNormSq A p.1))) o]
    rw [hcollapse]
    have hterm : ∀ j : I, (A o j / Real.sqrt (rowNormSq A o))
        * (A o j / Real.sqrt (rowNormSq A o))
        = (A o j) ^ 2 / (Real.sqrt (rowNormSq A o)) ^ 2 := fun j => by
      rw [div_mul_div_comm, ← pow_two, ← pow_two]
    have hrw : ∑ j, (A o j) ^ 2 = rowNormSq A o := rfl
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div,
      Real.sq_sqrt (rowNormSq_nonneg A o), hrw, div_self (hrow o),
      Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, kpLeft]
    have hzero : ∀ p : O × I,
        (if p.1 = o then A p.1 p.2 / Real.sqrt (rowNormSq A p.1) else 0)
          * (if p.1 = o' then A p.1 p.2 / Real.sqrt (rowNormSq A p.1) else 0) = 0 := by
      intro p
      by_cases h1 : p.1 = o
      · rw [if_pos h1, if_neg (fun hc => h (h1.symm.trans hc)), mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hzero p), Finset.sum_const_zero]

/-- Lemma 2.1, part 1 (isometry of `N`): if `‖A‖_F ≠ 0` then `kpRight A`
has orthonormal columns, `Nᵀ N = 1`. -/
theorem kpRight_isometry (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0) :
    (kpRight A)ᵀ * kpRight A = 1 := by
  ext i i'
  by_cases h : i = i'
  · subst i'
    have hcollapse : ((kpRight A)ᵀ * kpRight A) i i = ∑ u : O,
        (Real.sqrt (rowNormSq A u) / frobNorm A)
          * (Real.sqrt (rowNormSq A u) / frobNorm A) := by
      have hval : ∀ p : O × I, ∀ x : I,
          (if p.2 = x then Real.sqrt (rowNormSq A p.1) / frobNorm A else 0)
            * (if p.2 = x then Real.sqrt (rowNormSq A p.1) / frobNorm A else 0)
            = if p.2 = x then (Real.sqrt (rowNormSq A p.1) / frobNorm A)
                * (Real.sqrt (rowNormSq A p.1) / frobNorm A) else 0 := by
        intro p x
        by_cases hp : p.2 = x
        · simp [hp]
        · simp [hp]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, kpRight, hval]
      rw [sum_prod_ite_right (fun p => (Real.sqrt (rowNormSq A p.1) / frobNorm A)
        * (Real.sqrt (rowNormSq A p.1) / frobNorm A)) i]
    rw [hcollapse]
    have hterm : ∀ u : O, (Real.sqrt (rowNormSq A u) / frobNorm A)
        * (Real.sqrt (rowNormSq A u) / frobNorm A)
        = (rowNormSq A u) / (frobNorm A) ^ 2 := fun u => by
      rw [div_mul_div_comm, ← pow_two, ← pow_two, Real.sq_sqrt (rowNormSq_nonneg A u)]
    have hrw : ∑ u, rowNormSq A u = frobNormSq A := rfl
    have hsq : frobNorm A ^ 2 = frobNormSq A := by
      unfold frobNorm
      exact Real.sq_sqrt (frobNormSq_nonneg A)
    have hFs : frobNormSq A ≠ 0 := by
      intro hz
      apply hF
      unfold frobNorm
      rw [hz, Real.sqrt_zero]
    rw [Finset.sum_congr rfl (fun u _ => hterm u), ← Finset.sum_div, hrw, hsq,
      div_self hFs, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, kpRight]
    have hzero : ∀ p : O × I,
        (if p.2 = i then Real.sqrt (rowNormSq A p.1) / frobNorm A else 0)
          * (if p.2 = i' then Real.sqrt (rowNormSq A p.1) / frobNorm A else 0) = 0 := by
      intro p
      by_cases h1 : p.2 = i
      · rw [if_pos h1, if_neg (fun hc => h (h1.symm.trans hc)), mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hzero p), Finset.sum_const_zero]

/-- Lemma 2.1, part 1 (factorisation): the corner `Mᵀ N` of the two frames
recovers `A` scaled by the inverse Frobenius norm,
`Mᵀ N = ‖A‖_F⁻¹ • A`. -/
theorem kp_corner (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0) :
    (kpLeft A)ᵀ * kpRight A = (frobNorm A)⁻¹ • A := by
  ext o i
  simp only [Matrix.mul_apply, Matrix.transpose_apply, kpLeft, kpRight,
    Matrix.smul_apply, smul_eq_mul, inv_mul_eq_div]
  rw [Finset.sum_eq_single (o, i)]
  · have hf : (if (o, i).1 = o then A (o, i).1 (o, i).2 / Real.sqrt (rowNormSq A (o, i).1)
          else 0)
          * (if (o, i).2 = i then Real.sqrt (rowNormSq A (o, i).1) / frobNorm A else 0)
        = A o i / Real.sqrt (rowNormSq A o)
          * (Real.sqrt (rowNormSq A o) / frobNorm A) := by
      simp
    rw [hf]
    by_cases hr : rowNormSq A o = 0
    · have hAo : A o i = 0 := rowNormSq_eq_zero_entry A o hr i
      have hrt : Real.sqrt (rowNormSq A o) = 0 := by rw [hr]; exact Real.sqrt_zero
      simp [hAo, hrt]
    · have hc : Real.sqrt (rowNormSq A o) ≠ 0 := by
        intro hz
        exact hr (by rw [← Real.sq_sqrt (rowNormSq_nonneg A o), hz, pow_two, zero_mul])
      field_simp
  · intro p _ hp
    by_cases h1 : p.1 = o
    · by_cases h2 : p.2 = i
      · exact absurd (Prod.ext h1 h2) hp
      · simp [h2]
    · simp [h1]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- `Mᵀ N = ‖A‖_F⁻¹ • A` restated in division form. -/
theorem corner_eq_scaled (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0) :
    (frobNorm A)⁻¹ • A = (kpLeft A)ᵀ * kpRight A := (kp_corner A hF).symm

end KP

/-! ## The reflection walk of Lemma 2.3 and Eq. (3)–(4) -/

section Walk

variable {O I : Type} [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]

/-- The left reflection `2MMᵀ − I` of Lemma 2.3. -/
noncomputable def kpReflectL (A : Matrix O I ℝ) : Matrix (O × I) (O × I) ℝ :=
  (2 : ℝ) • (kpLeft A * (kpLeft A)ᵀ) - 1

/-- The right reflection `2NNᵀ − I` of Lemma 2.3. -/
noncomputable def kpReflectR (A : Matrix O I ℝ) : Matrix (O × I) (O × I) ℝ :=
  (2 : ℝ) • (kpRight A * (kpRight A)ᵀ) - 1

/-- The QSVE walk unitary `W = (2MMᵀ − I)(2NNᵀ − I)` of Lemma 2.3. -/
noncomputable def kpWalk (A : Matrix O I ℝ) : Matrix (O × I) (O × I) ℝ :=
  kpReflectL A * kpReflectR A

/-- The scaled-singular-vector identity: for `A v = σ • u` the corner maps
`v` to `(σ/‖A‖_F) • u`. -/
private theorem corner_mulVec (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0)
    (v : I → ℝ) (u : O → ℝ) (σ : ℝ) (hsv : A *ᵥ v = σ • u) :
    ((kpLeft A)ᵀ * kpRight A) *ᵥ v = (σ / frobNorm A) • u := by
  have hfold2 : (σ / frobNorm A) • u = ((frobNorm A)⁻¹ * σ) • u := by
    rw [div_eq_mul_inv, mul_comm]
  rw [← corner_eq_scaled A hF, Matrix.smul_mulVec, hsv, smul_smul, ← hfold2]

/-- The right reflection fixes the range of `N` at the matrix level:
`R_R · N = N`, because `Nᵀ N = 1`. -/
private theorem kpReflectR_mul (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0) :
    kpReflectR A * kpRight A = kpRight A := by
  have hN : (kpRight A)ᵀ * kpRight A = 1 := kpRight_isometry A hF
  have h2X : (2 : ℝ) • kpRight A = kpRight A + kpRight A := by
    have h2 : (2 : ℝ) = 1 + 1 := by norm_num
    rw [h2, add_smul, one_smul]
  calc kpReflectR A * kpRight A
      = ((2 : ℝ) • (kpRight A * (kpRight A)ᵀ)
          - (1 : Matrix (O × I) (O × I) ℝ)) * kpRight A := rfl
    _ = (2 : ℝ) • ((kpRight A * (kpRight A)ᵀ) * kpRight A) - kpRight A := by
        rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = (2 : ℝ) • (kpRight A * ((kpRight A)ᵀ * kpRight A)) - kpRight A := by
        rw [Matrix.mul_assoc]
    _ = (2 : ℝ) • (kpRight A * (1 : Matrix I I ℝ)) - kpRight A := by rw [hN]
    _ = (2 : ℝ) • kpRight A - kpRight A := by rw [Matrix.mul_one]
    _ = kpRight A + kpRight A - kpRight A := by rw [h2X]
    _ = kpRight A := by abel

/-- The right reflection fixes the range of `N`: for every `v`,
`R_R (N v) = N v`, because `Nᵀ N = 1`. -/
theorem kpReflectR_mulVec (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0) (v : I → ℝ) :
    kpReflectR A *ᵥ (kpRight A *ᵥ v) = kpRight A *ᵥ v := by
  rw [Matrix.mulVec_mulVec, kpReflectR_mul A hF]

/-- Eq. (3) of the source: for a singular-vector pair `A v = σ • u`, the
walk unitary acts on the encoded right singular vector as
`W (N v) = (2σ/‖A‖_F) • (M u) − N v`. -/
theorem kpWalk_mulVec (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0)
    (v : I → ℝ) (u : O → ℝ) (σ : ℝ) (hsv : A *ᵥ v = σ • u) :
    kpWalk A *ᵥ (kpRight A *ᵥ v)
      = (2 * σ / frobNorm A) • (kpLeft A *ᵥ u) - kpRight A *ᵥ v := by
  have hcv := corner_mulVec A hF v u σ hsv
  have hfold : (2 : ℝ) * (σ / frobNorm A) = 2 * σ / frobNorm A := by field_simp
  rw [Matrix.mulVec_mulVec]
  simp only [kpWalk, Matrix.mul_assoc, kpReflectR_mul A hF]
  simp only [kpReflectL, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.sub_mulVec, Matrix.smul_mulVec]
  rw [← Matrix.mulVec_mulVec, hcv, Matrix.mulVec_smul, smul_smul, hfold]

/-- Dot-product reassociation used for the Rayleigh quotient of the walk. -/
private theorem mulVec_dot_mulVec {P Q : Type} [Fintype P] [Fintype Q]
    (M : Matrix O P ℝ) (N : Matrix O Q ℝ) (u : P → ℝ) (v : Q → ℝ) :
    (M *ᵥ u) ⬝ᵥ (N *ᵥ v) = u ⬝ᵥ ((Mᵀ * N) *ᵥ v) := by
  have hM : M *ᵥ u = u ᵥ* Mᵀ := by
    rw [← Matrix.transpose_transpose M, Matrix.mulVec_transpose,
      Matrix.transpose_transpose]
  calc (M *ᵥ u) ⬝ᵥ (N *ᵥ v)
      = (M *ᵥ u) ᵥ* N ⬝ᵥ v := dotProduct_mulVec _ _ _
    _ = (u ᵥ* Mᵀ) ᵥ* N ⬝ᵥ v := by rw [hM]
    _ = u ᵥ* (Mᵀ * N) ⬝ᵥ v := by rw [Matrix.vecMul_vecMul]
    _ = u ⬝ᵥ (Mᵀ * N) *ᵥ v := (dotProduct_mulVec _ _ _).symm

/-- Eq. (4) of the source: the Rayleigh quotient of the walk on the encoded
right singular vector is `⟨N v, W N v⟩ = 2σ²/‖A‖_F² − 1` for a normalised
singular-vector pair `A v = σ • u` with `‖u‖ = ‖v‖ = 1`. -/
theorem kpWalk_dotProduct (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0)
    (v : I → ℝ) (u : O → ℝ) (σ : ℝ) (hsv : A *ᵥ v = σ • u)
    (hv : v ⬝ᵥ v = 1) (hu : u ⬝ᵥ u = 1) :
    (kpRight A *ᵥ v) ⬝ᵥ (kpWalk A *ᵥ (kpRight A *ᵥ v))
      = 2 * σ ^ 2 / frobNorm A ^ 2 - 1 := by
  have hcv := corner_mulVec A hF v u σ hsv
  have hN : (kpRight A)ᵀ * kpRight A = 1 := kpRight_isometry A hF
  rw [kpWalk_mulVec A hF v u σ hsv]
  have hmn : (kpLeft A *ᵥ u) ⬝ᵥ (kpRight A *ᵥ v) = σ / frobNorm A := by
    rw [mulVec_dot_mulVec, hcv, dotProduct_smul, hu, smul_eq_mul, mul_one]
  have h1 : (kpRight A *ᵥ v) ⬝ᵥ ((2 * σ / frobNorm A) • (kpLeft A *ᵥ u))
      = (2 * σ / frobNorm A) * (σ / frobNorm A) := by
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm, hmn]
  have h2 : (kpRight A *ᵥ v) ⬝ᵥ (kpRight A *ᵥ v) = 1 := by
    rw [mulVec_dot_mulVec, hN, Matrix.one_mulVec, hv]
  rw [dotProduct_sub, h1, h2]
  field_simp

/-- Lemma 2.3's half-angle encoding: with `0 ≤ σ ≤ ‖A‖_F`, the walk angle
`θ = 2 · arccos(σ/‖A‖_F)` satisfies both `⟨N v, W N v⟩ = cos θ` and
`cos(θ/2) = σ/‖A‖_F`, the relation `σ = ‖A‖_F · cos(θᵢ/2)` by which
Algorithm 1 estimates singular values. -/
theorem kpWalk_half_angle (A : Matrix O I ℝ) (hF : frobNorm A ≠ 0)
    (v : I → ℝ) (u : O → ℝ) (σ : ℝ) (hsv : A *ᵥ v = σ • u)
    (hv : v ⬝ᵥ v = 1) (hu : u ⬝ᵥ u = 1) (hσ : 0 ≤ σ) (hσF : σ ≤ frobNorm A) :
    ∃ θ : ℝ, (kpRight A *ᵥ v) ⬝ᵥ (kpWalk A *ᵥ (kpRight A *ᵥ v)) = Real.cos θ
      ∧ Real.cos (θ / 2) = σ / frobNorm A := by
  have hFnn : 0 ≤ frobNorm A := frobNorm_nonneg A
  have hFpos : 0 < frobNorm A := lt_of_le_of_ne hFnn (Ne.symm hF)
  have hx : 0 ≤ σ / frobNorm A := div_nonneg hσ hFnn
  have hxneg : (-1 : ℝ) ≤ σ / frobNorm A := by linarith
  have hx1 : σ / frobNorm A ≤ 1 := (div_le_one hFpos).mpr hσF
  refine ⟨2 * Real.arccos (σ / frobNorm A), ?_, ?_⟩
  · rw [kpWalk_dotProduct A hF v u σ hsv hv hu, Real.cos_two_mul,
    Real.cos_arccos hxneg hx1]
    field_simp
  · rw [show 2 * Real.arccos (σ / frobNorm A) / 2 = Real.arccos (σ / frobNorm A) by ring,
    Real.cos_arccos hxneg hx1]

end Walk

/-! ## Eigenvalue-sign recovery (Theorem 3, proof part 1) -/

section Sign

/-- The comparison behind Algorithm 2's sign flag: for `μ > 0`,
`|lam + μ| ≤ |lam|` holds exactly for `lam ≤ −μ/2`. -/
theorem abs_shift_le_iff (μ lam : ℝ) (hμ : 0 < μ) : |lam + μ| ≤ |lam| ↔ lam ≤ -μ / 2 := by
  have hkey : |lam + μ| ≤ |lam| ↔ (lam + μ) ^ 2 ≤ lam ^ 2 := by
    rw [← sq_le_sq]
  constructor
  · intro h
    have hs : (lam + μ) ^ 2 ≤ lam ^ 2 := hkey.mp h
    have hexp : 2 * μ * lam + μ ^ 2 ≤ 0 := by nlinarith [hs, hμ]
    nlinarith [hexp, hμ]
  · intro h
    have hexp : 2 * μ * lam + μ ^ 2 ≤ 0 := by nlinarith [h, hμ]
    exact hkey.mpr (by nlinarith [hexp])

/-- Positive eigenvalues are never flagged: for `lam ≥ 0` and `μ ≥ 0`,
`|lam| + μ = |lam + μ|`. -/
theorem abs_shift_of_nonneg (μ lam : ℝ) (hμ : 0 ≤ μ) (hlam : 0 ≤ lam) :
    |lam| + μ = |lam + μ| := by
  rw [abs_of_nonneg hlam, abs_of_nonneg (by positivity : (0:ℝ) ≤ lam + μ)]

/-- The perfect-estimate sign recovery of Theorem 3's proof: for a promise
eigenvalue `lam` with `1/κ ≤ |lam| ≤ 1` (i.e. `lam ∈ [−1, −1/κ] ∪ [1/κ, 1]`)
and condition number `κ ≥ 1`, the Algorithm-2 comparison with shift `μ = 2/κ`
recovers the sign: `|lam + 2/κ| ≤ |lam| ↔ lam ≤ 0`. -/
theorem sign_recovered_shift (κ lam : ℝ) (hκ : 1 ≤ κ)
    (hlo : 1 / κ ≤ |lam|) (hhi : |lam| ≤ 1) :
    |lam + 2 / κ| ≤ |lam| ↔ lam ≤ 0 := by
  have hμ : 0 < 2 / κ := by positivity
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  constructor
  · intro h
    by_contra hlam
    push_neg at hlam
    have hge : 1 / κ ≤ lam := by
      by_contra hc
      push_neg at hc
      rw [abs_of_pos hlam] at hlo
      linarith
    have h1 : |lam| + 2 / κ = |lam + 2 / κ| := abs_shift_of_nonneg _ _ hμ.le hlam.le
    rw [← h1] at h
    have h3 : (0:ℝ) ≤ |lam| := abs_nonneg lam
    linarith
  · intro hlam
    have hneg : lam ≤ -1 / κ := by
      by_contra hc
      push_neg at hc
      rcases lt_or_ge lam 0 with h0 | h0
      · rw [abs_of_neg h0] at hlo
        have hneg1 : (-1:ℝ) / κ = -(1 / κ) := by ring
        exact absurd (by linarith [hneg1] : lam ≤ -1 / κ) (not_le.2 hc)
      · have hlam0 : lam = 0 := le_antisymm hlam h0
        rw [hlam0, abs_zero] at hlo
        have : (0:ℝ) < 1 / κ := div_pos one_pos hkpos
        linarith
    refine (abs_shift_le_iff (2 / κ) lam hμ).mpr ?_
    have hsplit : -(2 / κ) / 2 = -1 / κ := by field_simp
    rw [hsplit]
    exact hneg

end Sign

/-! ## Appendix Eqs. (9)–(11): the orthogonal-register error decomposition -/

section Appendix

/-- Appendix Eq. (9), Parseval form: for an orthogonal family `w`, the
squared norm of the weighted sum decomposes as
`‖∑ βᵢ • wᵢ‖² = ∑ ‖βᵢ • wᵢ‖²`.  In the source the family is
`wᵢ = |vᵢ⟩|h(λ̄ᵢ)⟩ − |vᵢ⟩|h(λᵢ)⟩`, orthogonal because the eigenvector
registers `|vᵢ⟩` are orthonormal. -/
theorem orthogonal_weighted_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι] (w : ι → E)
    (hw : ∀ i j, i ≠ j → ⟪w i, w j⟫_ℂ = 0) (β : ι → ℂ) :
    ‖∑ i, β i • w i‖ ^ 2 = ∑ i, ‖β i • w i‖ ^ 2 := by
  have hdiag : ∀ i : ι,
      ⟪β i • w i, ∑ j, β j • w j⟫_ℂ = ((‖β i • w i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [inner_sum, Finset.sum_eq_single i]
    · have hx : ⟪β i • w i, β i • w i⟫_ℂ = ((‖β i • w i‖ : ℝ) : ℂ) ^ 2 :=
        inner_self_eq_norm_sq_to_K _
      rw [hx, Complex.ofReal_pow]
    · intro j _ hj
      rw [inner_smul_left, inner_smul_right, hw i j (Ne.symm hj)]
      simp
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  have hfull : ⟪∑ i, β i • w i, ∑ j, β j • w j⟫_ℂ
      = ((∑ i, ‖β i • w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_inner, Finset.sum_congr rfl (fun i _ => hdiag i), Complex.ofReal_sum]
  have hK : ⟪∑ i, β i • w i, ∑ j, β j • w j⟫_ℂ
      = ((‖∑ i, β i • w i‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  rw [hfull, ← Complex.ofReal_pow] at hK
  exact (Complex.ofReal_injective hK).symm

/-- Appendix Eq. (11): if every register difference `wᵢ` has norm at most
`L` and the amplitudes `β` are normalised (`∑ |βᵢ|² = 1`), then the
state-sum error obeys `‖∑ βᵢ • wᵢ‖ ≤ L`.  Combined with the `cκ`-Lipschitz
bound of Lemma 3 and the QSVE eigenvalue error `|λ̄ᵢ − λᵢ| ≤ δ‖A‖_F`, this
gives `‖|ψ̄⟩ − |ψ⟩‖ ≤ cκδ‖A‖_F` for the Appendix states
`|ψ⟩ = ∑ᵢ βᵢ|vᵢ⟩|h(λᵢ)⟩`. -/
theorem qsve_state_error_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι] (w : ι → E)
    (hw : ∀ i j, i ≠ j → ⟪w i, w j⟫_ℂ = 0) (β : ι → ℂ)
    (hβ : ∑ i, ‖β i‖ ^ 2 = 1) {L : ℝ} (hL : 0 ≤ L) (hwle : ∀ i, ‖w i‖ ≤ L) :
    ‖∑ i, β i • w i‖ ≤ L := by
  have hsq := orthogonal_weighted_norm_sq w hw β
  have hbound : ∑ i, ‖β i • w i‖ ^ 2 ≤ L ^ 2 := by
    have hterm : ∀ i, ‖β i • w i‖ ^ 2 ≤ ‖β i‖ ^ 2 * L ^ 2 := by
      intro i
      have h1 : ‖β i • w i‖ ≤ ‖β i‖ * L := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hwle i) (norm_nonneg _)
      have hnn1 : (0:ℝ) ≤ ‖β i • w i‖ := norm_nonneg _
      have hnn2 : (0:ℝ) ≤ ‖β i‖ * L := mul_nonneg (norm_nonneg _) hL
      calc ‖β i • w i‖ ^ 2 ≤ (‖β i‖ * L) ^ 2 := by nlinarith [h1, hnn1, hnn2]
        _ = ‖β i‖ ^ 2 * L ^ 2 := by rw [mul_pow]
    calc ∑ i, ‖β i • w i‖ ^ 2
        ≤ ∑ i, ‖β i‖ ^ 2 * L ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, ‖β i‖ ^ 2) * L ^ 2 := by rw [Finset.sum_mul]
      _ = L ^ 2 := by rw [hβ, one_mul]
  have hfin : (‖∑ i, β i • w i‖ : ℝ) ^ 2 ≤ L ^ 2 := by
    rw [hsq]
    exact hbound
  rw [← abs_of_nonneg (norm_nonneg _)]
  exact abs_le_of_sq_le_sq hfin hL

end Appendix

/-! ## Post-selection repetitions (Theorem 3, runtime ledger part) -/

section Postselect

/-- Algorithm 2, step 4 analysis: post-selecting the ancilla on `|0⟩` with
amplitudes `γ/λᵢ` succeeds with probability `∑ |βᵢ|² (γ/λᵢ)²`, which is at
least `γ²` whenever every inverted eigenvalue satisfies `0 < λᵢ ≤ 1`. -/
theorem postselection_success_ge {ι : Type} [Fintype ι] (γ : ℝ) (hγ : 0 ≤ γ)
    (β lam : ι → ℝ) (hβ : ∑ i, β i ^ 2 = 1) (hpos : ∀ i, 0 < lam i)
    (hle : ∀ i, lam i ≤ 1) :
    γ ^ 2 ≤ ∑ i, β i ^ 2 * (γ / lam i) ^ 2 := by
  have hterm : ∀ i, (β i) ^ 2 * γ ^ 2 ≤ (β i) ^ 2 * (γ / lam i) ^ 2 := by
    intro i
    have hq : (0:ℝ) ≤ γ / lam i := div_nonneg hγ (hpos i).le
    have hle' : γ ≤ γ / lam i := by
      rw [le_div_iff₀ (hpos i)]
      have hmul := mul_le_mul_of_nonneg_left (hle i) hγ
      linarith [hmul, mul_one γ]
    have hsq : γ ^ 2 ≤ (γ / lam i) ^ 2 := by nlinarith [hq, hle']
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  calc ∑ i, β i ^ 2 * (γ / lam i) ^ 2
      ≥ ∑ i, (β i) ^ 2 * γ ^ 2 := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, β i ^ 2) * γ ^ 2 := by rw [Finset.sum_mul]
    _ = γ ^ 2 := by rw [hβ, one_mul]

/-- The `κ²` repetition bound of Theorem 3's runtime derivation: with the
rotation amplitude `γ = 1/κ` and all inverted eigenvalues in `[1/κ, 1]`,
the post-selection success probability is at least `1/κ²`, so the expected
number of repetitions is at most `κ²`. -/
theorem postselection_repetitions_le {ι : Type} [Fintype ι] (κ : ℝ) (hκ : 1 ≤ κ)
    (β lam : ι → ℝ) (hβ : ∑ i, β i ^ 2 = 1) (hlo : ∀ i, 1 / κ ≤ lam i)
    (hle : ∀ i, lam i ≤ 1) :
    (∑ i, β i ^ 2 * ((1 / κ) / lam i) ^ 2)⁻¹ ≤ κ ^ 2 := by
  have hkpos : (0:ℝ) < κ := lt_of_lt_of_le zero_lt_one hκ
  have hg : (0:ℝ) ≤ 1 / κ := by positivity
  have hpos : ∀ i, (0:ℝ) < lam i := fun i =>
    lt_of_lt_of_le (div_pos one_pos hkpos) (hlo i)
  have hp := postselection_success_ge (1 / κ) hg β lam hβ hpos hle
  have hpos2 : (0:ℝ) < (1 / κ) ^ 2 := by positivity
  have hp0 : (0:ℝ) < ∑ i, β i ^ 2 * ((1 / κ) / lam i) ^ 2 :=
    lt_of_lt_of_le hpos2 hp
  have hk2pos : (0:ℝ) < κ ^ 2 := by positivity
  have hq1 : (1 / κ) ^ 2 * κ ^ 2 = 1 := by field_simp
  have hpnn : (0:ℝ) ≤ ∑ i, β i ^ 2 * ((1 / κ) / lam i) ^ 2 - (1 / κ) ^ 2 := by
    linarith [hp]
  have hknn : (0:ℝ) ≤ κ ^ 2 := hk2pos.le
  rw [inv_le_iff_one_le_mul₀' hp0]
  nlinarith [hpnn, hknn, hq1]

end Postselect

/-! ## The dense `√n` scaling of the abstract (claim c002) -/

section Dense

open scoped Matrix.Norms.L2Operator

variable {O I : Type} [Fintype O] [Fintype I] [DecidableEq I]

/-- Squared Frobenius norm of a complex matrix. -/
noncomputable def frobNormSqC (A : Matrix O I ℂ) : ℝ := ∑ o, ∑ i, ‖A o i‖ ^ 2

/-- Frobenius norm of a complex matrix. -/
noncomputable def frobNormC (A : Matrix O I ℂ) : ℝ := Real.sqrt (frobNormSqC A)

/-- Each column of `A` has squared norm at most `‖A‖²`, because the column
is `A` applied to the `j`-th standard basis vector of the Euclidean space. -/
private theorem column_norm_le_opNorm (A : Matrix O I ℂ) (j : I) :
    ∑ o, ‖A o j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  classical
  set x : EuclideanSpace ℂ I := PiLp.single 2 j (1 : ℂ) with hx
  have hnorme : ‖x‖ = 1 := by
    rw [hx, PiLp.norm_single, norm_one]
  have h1 : ‖(EuclideanSpace.equiv O ℂ).symm (A *ᵥ x)‖ ≤ ‖A‖ := by
    have h := A.l2_opNorm_mulVec x
    rwa [hnorme, mul_one] at h
  have h2 : ‖(EuclideanSpace.equiv O ℂ).symm (A *ᵥ x)‖ ^ 2 = ∑ o, ‖A o j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun o _ => ?_
    have hentry : (A *ᵥ x) o = A o j := by
      rw [hx]
      simp [Matrix.mulVec, dotProduct]
    show ‖((EuclideanSpace.equiv O ℂ).symm (A *ᵥ x)) o‖ ^ 2 = ‖A o j‖ ^ 2
    rw [PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply, hentry]
  rw [← h2]
  have ha : (0:ℝ) ≤ ‖(EuclideanSpace.equiv O ℂ).symm (A *ᵥ x)‖ := norm_nonneg _
  have hb : (0:ℝ) ≤ ‖A‖ := norm_nonneg A
  nlinarith [h1, ha, hb]

/-- The Frobenius-versus-operator-norm bound behind the abstract's dense
`√n` scaling: every complex `m × n` matrix satisfies
`‖A‖_F ≤ √n · ‖A‖₂`, where `n` is the number of columns. Combined with a
spectral-norm bound this is the statement `‖A‖_F = O(√n)` used for the
runtime comparison of the abstract. -/
theorem frobNormC_le_sqrt_card_mul_opNorm (A : Matrix O I ℂ) :
    frobNormC A ≤ Real.sqrt ((Fintype.card I : ℝ)) * ‖A‖ := by
  have hsq : frobNormSqC A ≤ (Fintype.card I : ℝ) * ‖A‖ ^ 2 := by
    calc frobNormSqC A = ∑ i, ∑ o, ‖A o i‖ ^ 2 := by
          unfold frobNormSqC
          exact Finset.sum_comm
      _ ≤ ∑ i : I, ‖A‖ ^ 2 := Finset.sum_le_sum fun i _ => column_norm_le_opNorm A i
      _ = (Fintype.card I : ℝ) * ‖A‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsplit : Real.sqrt ((Fintype.card I : ℝ) * ‖A‖ ^ 2)
      = Real.sqrt ((Fintype.card I : ℝ)) * ‖A‖ := by
    rw [Real.sqrt_mul (Nat.cast_nonneg (Fintype.card I)), Real.sqrt_sq (norm_nonneg A)]
  unfold frobNormC
  calc Real.sqrt (frobNormSqC A) ≤ Real.sqrt ((Fintype.card I : ℝ) * ‖A‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((Fintype.card I : ℝ)) * ‖A‖ := hsplit

/-- Corollary of the √n bound: for a square complex matrix with spectral
norm at most `C`, the Theorem-3 ledger on the Frobenius norm is bounded by
`C` times the `√n`-scaled ledger — the dense-runtime statement of the
abstract, now as a theorem instead of a hypothesis. -/
theorem dense_runtime_le_sqrtn_matrix (κ pl ε C : ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hpl : 0 ≤ pl) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) :
    denseQLSARuntime κ (frobNormC A) pl ε
      ≤ C * denseQLSARuntime κ (Real.sqrt ((n : ℝ))) pl ε := by
  have hcard : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
  have hF : frobNormC A ≤ C * Real.sqrt ((n : ℝ)) := by
    have h1 := frobNormC_le_sqrt_card_mul_opNorm A
    rw [hcard] at h1
    calc frobNormC A ≤ Real.sqrt ((n : ℝ)) * ‖A‖ := h1
      _ ≤ Real.sqrt ((n : ℝ)) * C := mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg _)
      _ = C * Real.sqrt ((n : ℝ)) := by ring
  exact dense_runtime_le_sqrtn κ (frobNormC A) pl ε C (n : ℝ) hpl hε hC hF

end Dense

/-! ## Claim-level core bundles -/

section Bundles

open scoped Matrix.Norms.L2Operator

/-- **Claim c001, mathematical cores** — the operator-level content of
Theorem 3's proof: (1) the KP frames of Lemma 2.1 are isometries with corner
`Mᵀ N = A/‖A‖_F`; (2) Eq. (3): `W (N v) = (2σ/‖A‖_F) M u − N v` for a
singular-vector pair; (3) Eq. (4) with the half-angle encoding
`cos(θ/2) = σ/‖A‖_F`; (4) the sign-recovery comparison on the promise
interval; (5) the post-selection `κ²` repetition bound. The full runtime
`O(κ²·polylog(n)·‖A‖_F/ε)` additionally needs the query/circuit model for
the data structure and phase estimation, which the library does not provide
(recorded as a substantive gap). -/
theorem theorem3_core_content {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hrow : ∀ o, rowNormSq A o ≠ 0) (hF : frobNorm A ≠ 0)
    (v : Fin n → ℝ) (u : Fin n → ℝ) (σ : ℝ) (hsv : A *ᵥ v = σ • u)
    (hv : v ⬝ᵥ v = 1) (hu : u ⬝ᵥ u = 1) (hσ : 0 ≤ σ) (hσF : σ ≤ frobNorm A)
    (κ lam : ℝ) (hκ : 1 ≤ κ) (hlo : 1 / κ ≤ |lam|) (hhi : |lam| ≤ 1)
    (β : Fin n → ℝ) (lams : Fin n → ℝ) (hβ : ∑ i, β i ^ 2 = 1)
    (hlo' : ∀ i, 1 / κ ≤ lams i) (hle' : ∀ i, lams i ≤ 1) :
    (kpLeft A)ᵀ * kpLeft A = 1 ∧ (kpRight A)ᵀ * kpRight A = 1
      ∧ (kpLeft A)ᵀ * kpRight A = (frobNorm A)⁻¹ • A
      ∧ kpWalk A *ᵥ (kpRight A *ᵥ v)
        = (2 * σ / frobNorm A) • (kpLeft A *ᵥ u) - kpRight A *ᵥ v
      ∧ (kpRight A *ᵥ v) ⬝ᵥ (kpWalk A *ᵥ (kpRight A *ᵥ v))
        = 2 * σ ^ 2 / frobNorm A ^ 2 - 1
      ∧ (∃ θ : ℝ, (kpRight A *ᵥ v) ⬝ᵥ (kpWalk A *ᵥ (kpRight A *ᵥ v)) = Real.cos θ
        ∧ Real.cos (θ / 2) = σ / frobNorm A)
      ∧ (|lam + 2 / κ| ≤ |lam| ↔ lam ≤ 0)
      ∧ (∑ i, β i ^ 2 * ((1 / κ) / lams i) ^ 2)⁻¹ ≤ κ ^ 2 :=
  ⟨kpLeft_isometry A hrow, kpRight_isometry A hF, kp_corner A hF,
    kpWalk_mulVec A hF v u σ hsv,
    kpWalk_dotProduct A hF v u σ hsv hv hu,
    kpWalk_half_angle A hF v u σ hsv hv hu hσ hσF,
    sign_recovered_shift κ lam hκ hlo hhi,
    postselection_repetitions_le κ hκ β lams hβ hlo' hle'⟩

/-- **Claim c002, mathematical cores** — the sparsity-independent scaling
content of the abstract: (1) the Frobenius-versus-operator bound
`‖A‖_F ≤ √n·‖A‖₂`; (2) the derived dense-runtime bound: under a spectral
norm bound `C`, the Theorem-3 ledger on `‖A‖_F` is at most `C` times the
`√n`-scaled ledger; (3) the factor-`√n` identity marking the quadratic
improvement over the `n`-scaling of the sparse QLSA of [3]. -/
theorem abstract_core_content (κ pl ε C n : ℝ) {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hnn : 0 ≤ n) (hpl : 0 ≤ pl) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) :
    frobNormC A ≤ Real.sqrt ((Fintype.card (Fin d) : ℝ)) * ‖A‖
      ∧ denseQLSARuntime κ (frobNormC A) pl ε
        ≤ C * denseQLSARuntime κ (Real.sqrt ((d : ℝ))) pl ε
      ∧ denseQLSARuntime κ (Real.sqrt n) pl ε * Real.sqrt n
        = denseQLSARuntime κ n pl ε :=
  ⟨frobNormC_le_sqrt_card_mul_opNorm A,
    dense_runtime_le_sqrtn_matrix κ pl ε C A hpl hε hC hA,
    dense_runtime_sqrtn_factor κ pl ε n hnn⟩

end Bundles

end Qatlib.Papers.QLinSysDense17.MainResults
