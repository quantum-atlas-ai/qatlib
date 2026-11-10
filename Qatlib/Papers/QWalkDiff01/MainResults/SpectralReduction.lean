/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkDiff01.MainResults.LimitingDistribution
import Qatlib.Papers.QWalkDiff01.MainResults.Defs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.QWalkDiff01.MainResults

def revFin (n : ℕ) (j : Fin (2*n+1)) : Fin (2*n+1) := ⟨2*n - j.val, by omega⟩

@[simp] lemma revFin_val (n : ℕ) (j : Fin (2*n+1)) : (revFin n j).val = 2*n - j.val := rfl

lemma revFin_involutive (n : ℕ) (j : Fin (2*n+1)) : revFin n (revFin n j) = j := by
  ext
  simp [revFin]
  omega

lemma revFin_zero (n : ℕ) : revFin n 0 = ⟨2*n, by omega⟩ := by
  ext
  simp [revFin]

def upShift (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun j k => if j.val + 1 = k.val then 1 else 0

def downShift (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun j k => if k.val + 1 = j.val then 1 else 0

lemma downShift_eq_transpose (m : ℕ) : downShift m = (upShift m)ᵀ := by
  ext j k
  simp [upShift, downShift, eq_comm]

lemma upShift_eq_transpose_downShift (m : ℕ) : (upShift m)ᵀ = downShift m :=
  (downShift_eq_transpose m).symm

lemma downShift_transpose (m : ℕ) : (downShift m)ᵀ = upShift m := by
  rw [downShift_eq_transpose, Matrix.transpose_transpose]

lemma upShift_mulVec (m : ℕ) (v : Fin m → ℝ) (j : Fin m) :
    (upShift m *ᵥ v) j = if h : j.val + 1 < m then v ⟨j.val + 1, h⟩ else 0 := by
  unfold Matrix.mulVec dotProduct upShift
  by_cases h : j.val + 1 < m
  · rw [dif_pos h, Finset.sum_eq_single (⟨j.val + 1, h⟩ : Fin m)]
    · simp
    · intro b _ hb
      have hne : j.val + 1 ≠ b.val := by
        intro he
        exact hb (Fin.ext he.symm)
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h, Finset.sum_eq_zero]
    intro x _
    have hne : j.val + 1 ≠ x.val := by
      intro he
      exact h (he ▸ x.isLt)
    simp [hne]

lemma downShift_mulVec (m : ℕ) (v : Fin m → ℝ) (j : Fin m) :
    (downShift m *ᵥ v) j = if h : 0 < j.val then v ⟨j.val - 1, by omega⟩ else 0 := by
  unfold Matrix.mulVec dotProduct downShift
  by_cases h : 0 < j.val
  · have hlt : j.val - 1 < m := by have := j.isLt; omega
    rw [dif_pos h, Finset.sum_eq_single (⟨j.val - 1, hlt⟩ : Fin m)]
    · have hv : (⟨j.val - 1, hlt⟩ : Fin m).val + 1 = j.val := by
        simp
        omega
      simp [hv]
    · intro b _ hb
      have hne : b.val + 1 ≠ j.val := by
        intro he
        exact hb (Fin.ext (by simp; omega))
      simp [hne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h, Finset.sum_eq_zero]
    intro x _
    have hne : x.val + 1 ≠ j.val := by omega
    simp [hne]

def gapDiag (n : ℕ) (γ : ℝ) (j : Fin (2*n+1)) : ℝ :=
  if j.val = 0 ∨ j.val = n ∨ j.val = 2*n then 2*γ else 3*γ

theorem reducedHamiltonian_shift_decomp (n : ℕ) (γ : ℝ) :
    reducedHamiltonian n γ =
      Matrix.diagonal (gapDiag n γ) +
        (-Real.sqrt 2 * γ) • (upShift (2*n+1) + downShift (2*n+1)) := by
  ext i j
  unfold reducedHamiltonian gapDiag upShift downShift
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    by_cases h1 : i.val + 1 = j.val
    · have h2 : j.val + 1 ≠ i.val := by omega
      simp [hij, h1, h2]
    · by_cases h2 : j.val + 1 = i.val
      · simp [hij, h1, h2]
      · simp [hij, h1, h2]

lemma reducedHamiltonian_mulVec (n : ℕ) (γ : ℝ) (v : Fin (2*n+1) → ℝ) (j : Fin (2*n+1)) :
    (reducedHamiltonian n γ *ᵥ v) j = gapDiag n γ j * v j +
      (-Real.sqrt 2 * γ) * ((if h : j.val + 1 < 2*n+1 then v ⟨j.val + 1, h⟩ else 0)
        + (if h : 0 < j.val then v ⟨j.val - 1, by omega⟩ else 0)) := by
  rw [reducedHamiltonian_shift_decomp]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    Matrix.mulVec_diagonal, upShift_mulVec, downShift_mulVec, smul_eq_mul]

lemma gapDiag_rev (n : ℕ) (γ : ℝ) (j : Fin (2*n+1)) :
    gapDiag n γ (revFin n j) = gapDiag n γ j := by
  unfold gapDiag
  have hj : j.val ≤ 2*n := by have := j.isLt; omega
  have hv : (revFin n j).val = 2*n - j.val := rfl
  rw [hv]
  have hiff : (2*n - j.val = 0 ∨ 2*n - j.val = n ∨ 2*n - j.val = 2*n)
      ↔ (j.val = 0 ∨ j.val = n ∨ j.val = 2*n) := by
    constructor
    · rintro (h | h | h) <;> omega
    · rintro (h | h | h) <;> omega
  rw [if_congr hiff rfl rfl]

lemma reducedHamiltonian_isHermitian (n : ℕ) (γ : ℝ) :
    (reducedHamiltonian n γ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
    reducedHamiltonian_transpose]

lemma swap_up_down (n : ℕ) (v : Fin (2*n+1) → ℝ) (j : Fin (2*n+1)) :
    (if h : (revFin n j).val + 1 < 2*n+1 then v ⟨(revFin n j).val + 1, h⟩ else 0)
      = (if h : 0 < j.val then v (revFin n ⟨j.val - 1, by omega⟩) else 0) := by
  by_cases hj : 0 < j.val
  · have hlt : j.val ≤ 2*n := by have := j.isLt; omega
    have hc : (revFin n j).val + 1 < 2*n+1 := by
      simp only [revFin_val]; omega
    rw [dif_pos hc, dif_pos hj]
    congr 1
    ext
    simp only [revFin_val]
    omega
  · have hc : ¬ ((revFin n j).val + 1 < 2*n+1) := by
      simp only [revFin_val]; omega
    rw [dif_neg hc, dif_neg hj]

lemma swap_down_up (n : ℕ) (v : Fin (2*n+1) → ℝ) (j : Fin (2*n+1)) :
    (if h : 0 < (revFin n j).val then v ⟨(revFin n j).val - 1, by omega⟩ else 0)
      = (if h : j.val + 1 < 2*n+1 then v (revFin n ⟨j.val + 1, h⟩) else 0) := by
  by_cases hj : j.val + 1 < 2*n+1
  · have hc : 0 < (revFin n j).val := by
      simp only [revFin_val]; omega
    rw [dif_pos hc, dif_pos hj]
    congr 1
  · have hlt : j.val ≤ 2*n := by have := j.isLt; omega
    have hc : ¬ (0 < (revFin n j).val) := by
      simp only [revFin_val]; omega
    rw [dif_neg hc, dif_neg hj]

lemma reducedHamiltonian_mulVec_rev (n : ℕ) (γ : ℝ) (v : Fin (2*n+1) → ℝ) :
    reducedHamiltonian n γ *ᵥ (fun j => v (revFin n j)) =
      fun j => (reducedHamiltonian n γ *ᵥ v) (revFin n j) := by
  funext j
  rw [reducedHamiltonian_mulVec, reducedHamiltonian_mulVec]
  rw [swap_up_down, swap_down_up, gapDiag_rev]
  ring

lemma eq_zero_of_row {n : ℕ} {γ : ℝ} (hγ : γ ≠ 0) {μ : ℝ} {v : Fin (2*n+1) → ℝ}
    (hv : reducedHamiltonian n γ *ᵥ v = μ • v) (h0 : v 0 = 0) : v = 0 := by
  have hcoef : (-Real.sqrt 2 * γ) ≠ 0 := by
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    exact mul_ne_zero (neg_ne_zero.mpr h2) hγ
  have key : ∀ k : ℕ, ∀ hk : k < 2*n+1, v ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simpa using h0
      · set j' : Fin (2*n+1) := ⟨k-1, by omega⟩ with hj'
        have hval : j'.val = k - 1 := rfl
        have hrow := congrFun hv j'
        rw [reducedHamiltonian_mulVec, Pi.smul_apply, smul_eq_mul] at hrow
        have hdown : (if h : 0 < j'.val then v ⟨j'.val - 1, by omega⟩ else 0) = 0 := by
          split_ifs with hh
          · exact ih (j'.val - 1) (by omega) (by omega)
          · rfl
        have hmid : v j' = 0 := ih j'.val (by omega) (by omega)
        have hcond : j'.val + 1 < 2*n+1 := by omega
        rw [hmid, hdown, add_zero] at hrow
        simp only [mul_zero, zero_add] at hrow
        rw [dif_pos hcond] at hrow
        have hlast : v ⟨j'.val + 1, hcond⟩ = 0 := by
          rcases mul_eq_zero.mp hrow with h1 | h2
          · exact absurd h1 hcoef
          · exact h2
        have e : (⟨j'.val+1, hcond⟩ : Fin (2*n+1)) = ⟨k, hk⟩ := by
          ext
          simp only [hval]
          omega
        rwa [e] at hlast
  funext j
  exact key j.val j.isLt

lemma eigenspace_subsingleton {n : ℕ} {γ : ℝ} (hγ : γ ≠ 0) {μ : ℝ}
    {v w : Fin (2*n+1) → ℝ} (hv : reducedHamiltonian n γ *ᵥ v = μ • v)
    (hw : reducedHamiltonian n γ *ᵥ w = μ • w) (hv0 : v ≠ 0) : ∃ c : ℝ, w = c • v := by
  have h0 : v 0 ≠ 0 := by
    intro h
    exact hv0 (eq_zero_of_row hγ hv h)
  have hlin : reducedHamiltonian n γ *ᵥ (w - (w 0 / v 0) • v) =
      μ • (w - (w 0 / v 0) • v) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hw, hv]
    module
  have hz : (w - (w 0 / v 0) • v) 0 = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hzero := eq_zero_of_row hγ hlin hz
  refine ⟨w 0 / v 0, ?_⟩
  funext j
  have h := congrFun hzero j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  simpa only [Pi.smul_apply, smul_eq_mul] using sub_eq_zero.mp h

lemma eigenvector_rev {n : ℕ} {γ : ℝ} (hγ : γ ≠ 0) {μ : ℝ} {v : Fin (2*n+1) → ℝ}
    (hv : reducedHamiltonian n γ *ᵥ v = μ • v) (hv0 : v ≠ 0) :
    ∃ c : ℝ, v ⟨2*n, by omega⟩ = c * v 0 ∧ c * c = 1 := by
  have hrev : reducedHamiltonian n γ *ᵥ (fun j => v (revFin n j)) =
      μ • (fun j => v (revFin n j)) := by
    rw [reducedHamiltonian_mulVec_rev]
    funext j
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hv (revFin n j)
  obtain ⟨c, hc⟩ := eigenspace_subsingleton hγ hv hrev hv0
  have h2 : ∀ j, v (revFin n j) = c * v j := by
    intro j
    have := congrFun hc j
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  have hv0' : v 0 ≠ 0 := by
    intro hzero
    exact hv0 (eq_zero_of_row hγ hv hzero)
  refine ⟨c, ?_, ?_⟩
  · have h := h2 0
    rwa [revFin_zero] at h
  · have h1 := h2 (revFin n 0)
    rw [revFin_involutive] at h1
    have e : v 0 = (c * c) * v 0 := by
      calc v 0 = c * v (revFin n 0) := h1
        _ = c * (c * v 0) := by rw [h2 0]
        _ = (c * c) * v 0 := by ring
    have : (c * c) * v 0 = 1 * v 0 := by
      rw [one_mul]
      exact e.symm
    exact mul_right_cancel₀ hv0' this

lemma basis_ne_zero (n : ℕ) (γ : ℝ) (r : Fin (2*n+1)) :
    (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) ≠ 0 := by
  intro h
  have h1 : ‖((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)‖ = 1 :=
    ((reducedHamiltonian_isHermitian n γ).eigenvectorBasis).orthonormal.1 r
  have h2 : ((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r) = 0 := by
    have hc := congrArg (WithLp.toLp 2) h
    simpa using hc
  rw [h2] at h1
  simp at h1

lemma basis_second_eq (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) (r : Fin (2*n+1)) :
    ∃ c : ℝ, (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) ⟨2*n, by omega⟩
      = c * (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0 ∧ c * c = 1 :=
  eigenvector_rev hγ ((reducedHamiltonian_isHermitian n γ).mulVec_eigenvectorBasis r)
    (basis_ne_zero n γ r)

lemma basis_term_fourth (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) (r : Fin (2*n+1)) :
    ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0 *
      (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) ⟨2*n, by omega⟩) ^ 2
    = ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 4 := by
  obtain ⟨c, hc, hcc⟩ := basis_second_eq n γ hγ r
  rw [hc]
  have : ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0 *
      (c * (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0)) ^ 2
      = (c * c) * ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 4 := by ring
  rw [this, hcc, one_mul]

lemma basis_parseval (n : ℕ) (γ : ℝ) :
    ∑ r : Fin (2*n+1), ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 2 = 1 := by
  have h := OrthonormalBasis.sum_sq_inner_right
    ((reducedHamiltonian_isHermitian n γ).eigenvectorBasis)
    (EuclideanSpace.single (0 : Fin (2*n+1)) (1 : ℝ))
  simpa [EuclideanSpace.inner_single_right] using h

theorem sum_fourth_pow_lower_bound (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    (1 : ℝ) / (2*n+1) ≤
      ∑ r : Fin (2*n+1),
        ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0 *
         (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) ⟨2*n, by omega⟩) ^ 2 := by
  have hterm : ∀ r : Fin (2*n+1),
      ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0 *
       (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) ⟨2*n, by omega⟩) ^ 2
      = ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 4 :=
    fun r => basis_term_fourth n γ hγ r
  simp only [hterm]
  have hsum := basis_parseval n γ
  have hjen := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset (Fin (2*n+1))))
    (f := fun r : Fin (2*n+1) => ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 2)
    (by intro i _; positivity) 1
  simp only [Finset.card_univ, Fintype.card_fin, pow_one,
    one_add_one_eq_two] at hjen
  have h2 : (1:ℝ) / (2*n+1) ≤
      ∑ r : Fin (2*n+1),
        (((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 2) ^ 2 := by
    simpa [hsum] using hjen
  have h2' : (∑ r : Fin (2*n+1),
        (((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 2) ^ 2)
      = ∑ r : Fin (2*n+1),
        ((⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0) ^ 4 := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    ring
  rw [h2'] at h2
  exact h2

theorem eigenbasis_parity (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) (r : Fin (2*n+1)) :
    |⟪(reducedHamiltonian_isHermitian n γ).eigenvectorBasis r,
        EuclideanSpace.single (0 : Fin (2*n+1)) (1:ℝ)⟫_ℝ|
      = |⟪(reducedHamiltonian_isHermitian n γ).eigenvectorBasis r,
        EuclideanSpace.single (⟨2*n, by omega⟩ : Fin (2*n+1)) (1:ℝ)⟫_ℝ| := by
  have h := basis_second_eq n γ hγ r
  obtain ⟨c, hc, hcc⟩ := h
  have e1 : ⟪(reducedHamiltonian_isHermitian n γ).eigenvectorBasis r,
      EuclideanSpace.single (0 : Fin (2*n+1)) (1:ℝ)⟫_ℝ
      = (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) 0 := by
    rw [EuclideanSpace.inner_single_right]
    simp
  have e2 : ⟪(reducedHamiltonian_isHermitian n γ).eigenvectorBasis r,
      EuclideanSpace.single (⟨2*n, by omega⟩ : Fin (2*n+1)) (1:ℝ)⟫_ℝ
      = (⇑((reducedHamiltonian_isHermitian n γ).eigenvectorBasis r)) ⟨2*n, by omega⟩ := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [e1, e2, hc, abs_mul]
  have hc1 : |c| = 1 := by
    have h2 : |c| * |c| = 1 := by
      have := congrArg abs hcc
      simpa [abs_mul] using this
    nlinarith [abs_nonneg c]
  rw [hc1, one_mul]

theorem reducedHamiltonian_rightRoot_lower_bound (n : ℕ) (γ : ℝ) (hγ : γ ≠ 0) :
    1 / ((2 * n + 1 : ℕ) : ℝ) ≤
      limitingDistribution (reducedHamiltonian_isHermitian n γ).eigenvectorBasis
        (EuclideanSpace.single (0 : Fin (2*n+1)) (1:ℝ))
        (EuclideanSpace.single (⟨2*n, by omega⟩ : Fin (2*n+1)) (1:ℝ)) := by
  refine limitingDistribution_rightRoot_lower_bound n _ _ _ ?_ (eigenbasis_parity n γ hγ)
  simp

end Qatlib.Papers.QWalkDiff01.MainResults
