/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StringRewrite07.MainResults.Source
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StringRewrite07.MainResults

open Matrix

def lineAdj (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then 1 else 0

theorem lineAdj_isSymm (n : ℕ) : (lineAdj n).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [lineAdj, or_comm]

def lastIdx (n : ℕ) : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

def firstIdx (n : ℕ) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩

theorem mulVec_basisVec_apply {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (j i : Fin (n + 1)) :
    (P *ᵥ basisVec j) i = P i j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j]
  · simp [basisVec]
  · intro k _ hk
    simp [basisVec, Pi.single_eq_of_ne hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

def orbitLM {ι : Type} [Fintype ι] {n : ℕ} (a : Fin (n + 1) → ι → ℝ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v := ∑ k, v k • a k
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp]
theorem orbitLM_apply {ι : Type} [Fintype ι] {n : ℕ} (a : Fin (n + 1) → ι → ℝ)
    (v : Fin (n + 1) → ℝ) :
    orbitLM a v = ∑ k, v k • a k := rfl

theorem orbitLM_basisVec {ι : Type} [Fintype ι] {n : ℕ} (a : Fin (n + 1) → ι → ℝ)
    (k : Fin (n + 1)) :
    orbitLM a (basisVec k) = a k := by
  rw [orbitLM_apply, Finset.sum_eq_single k]
  · simp [basisVec]
  · intro j _ hj
    simp [basisVec, Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem mulVec_orbitLM {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix ι ι ℝ) (a : Fin (n + 1) → ι → ℝ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (haH : ∀ k, H *ᵥ a k = ∑ j, P j k • a j) (v : Fin (n + 1) → ℝ) :
    H *ᵥ orbitLM a v = orbitLM a (P *ᵥ v) := by
  rw [orbitLM_apply]
  calc H *ᵥ ∑ k, v k • a k
      = ∑ k, v k • (H *ᵥ a k) := by
        rw [Matrix.mulVec_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Matrix.mulVec_smul]
    _ = ∑ k, v k • (∑ j, P j k • a j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [haH]
    _ = ∑ k, ∑ j, v k • (P j k • a j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.smul_sum]
    _ = ∑ k, ∑ j, (v k * P j k) • a j := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul]
    _ = ∑ j, ∑ k, (P j k * v k) • a j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_comm]
    _ = ∑ j, (∑ k, P j k * v k) • a j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_smul]
    _ = ∑ j, (P *ᵥ v) j • a j := by
        simp only [Matrix.mulVec, dotProduct]

theorem mulVec_pow_orbitLM {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix ι ι ℝ) (a : Fin (n + 1) → ι → ℝ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (haH : ∀ k, H *ᵥ a k = ∑ j, P j k • a j) (m : ℕ) (v : Fin (n + 1) → ℝ) :
    (H ^ m) *ᵥ orbitLM a v = orbitLM a ((P ^ m) *ᵥ v) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      calc (H ^ (m + 1)) *ᵥ orbitLM a v
          = (H ^ m * H) *ᵥ orbitLM a v := by rw [pow_succ]
        _ = (H ^ m) *ᵥ (H *ᵥ orbitLM a v) := by rw [← Matrix.mulVec_mulVec]
        _ = (H ^ m) *ᵥ orbitLM a (P *ᵥ v) := by rw [mulVec_orbitLM H a P haH]
        _ = orbitLM a ((P ^ m) *ᵥ (P *ᵥ v)) := ih (P *ᵥ v)
        _ = orbitLM a ((P ^ m * P) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
        _ = orbitLM a ((P ^ (m + 1)) *ᵥ v) := by rw [pow_succ]

theorem dot_orbitLM_left {ι : Type} [Fintype ι] {n : ℕ} (a : Fin (n + 1) → ι → ℝ)
    (ha : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0) (i : Fin (n + 1))
    (v : Fin (n + 1) → ℝ) :
    a i ⬝ᵥ orbitLM a v = v i := by
  rw [orbitLM_apply, dotProduct_sum]
  have hexp : ∀ k : Fin (n + 1), a i ⬝ᵥ (v k • a k) = v k * (if i = k then 1 else 0) := by
    intro k
    rw [dotProduct_smul, ha]
    simp
  calc ∑ k, a i ⬝ᵥ (v k • a k)
      = ∑ k, v k * (if i = k then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        exact hexp k
    _ = v i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro k _ hk
          have hik : i ≠ k := fun h => hk h.symm
          simp [hik]
        · intro h
          exact absurd (Finset.mem_univ i) h

theorem dot_orbitLM_right {ι : Type} [Fintype ι] {n : ℕ} (a : Fin (n + 1) → ι → ℝ)
    (w : ι → ℝ) (v : Fin (n + 1) → ℝ) :
    orbitLM a v ⬝ᵥ w = ∑ j, v j * (a j ⬝ᵥ w) := by
  rw [orbitLM_apply, sum_dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_dotProduct]
  simp

theorem offOrbit_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (a : Fin (n + 1) → ι → ℝ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (haH : ∀ k, H *ᵥ a k = ∑ j, P j k • a j)
    (w : ι → ℝ) (hw : ∀ k, w ⬝ᵥ a k = 0) (m : ℕ) :
    a (firstIdx n) ⬝ᵥ ((H ^ m) *ᵥ w) = 0 := by
  have hsym : (H ^ m).IsSymm := hH.pow m
  rw [dot_mulVec_comm hsym, dotProduct_comm]
  have hpow : (H ^ m) *ᵥ a (firstIdx n)
      = orbitLM a ((P ^ m) *ᵥ basisVec (firstIdx n)) := by
    rw [← orbitLM_basisVec a (firstIdx n), mulVec_pow_orbitLM H a P haH m]
  rw [hpow, dot_orbitLM_right]
  apply Finset.sum_eq_zero
  intro j _
  rw [dotProduct_comm, hw j, mul_zero]

theorem hamPowerMatrixEntry {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (a : Fin (n + 1) → ι → ℝ)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (ha : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0)
    (haH : ∀ k, H *ᵥ a k = ∑ j, P j k • a j)
    (w : ι → ℝ) (hw : ∀ k, w ⬝ᵥ a k = 0) (c : ℝ) (m : ℕ) :
    a (firstIdx n) ⬝ᵥ ((H ^ m) *ᵥ (c • a (lastIdx n) + w))
      = c * ((P ^ m) (firstIdx n) (lastIdx n)) := by
  have hsplit : (H ^ m) *ᵥ (c • a (lastIdx n) + w)
      = c • ((H ^ m) *ᵥ a (lastIdx n)) + (H ^ m) *ᵥ w := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hsplit, dotProduct_add, dotProduct_smul]
  have h1 : a (firstIdx n) ⬝ᵥ ((H ^ m) *ᵥ a (lastIdx n))
      = (P ^ m) (firstIdx n) (lastIdx n) := by
    have hpow : (H ^ m) *ᵥ a (lastIdx n)
        = orbitLM a ((P ^ m) *ᵥ basisVec (lastIdx n)) := by
      rw [← orbitLM_basisVec a (lastIdx n), mulVec_pow_orbitLM H a P haH m]
    rw [hpow, dot_orbitLM_left a ha]
    exact mulVec_basisVec_apply (P ^ m) (lastIdx n) (firstIdx n)
  have h2 : a (firstIdx n) ⬝ᵥ ((H ^ m) *ᵥ w) = 0 := offOrbit_orthogonal H hH a P haH w hw m
  rw [h1, h2]
  simp

theorem hamPower_lineAdj {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (H : Matrix ι ι ℝ) (hH : H.IsSymm) (a : Fin (n + 1) → ι → ℝ)
    (ha : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0)
    (haH : ∀ k, H *ᵥ a k = ∑ j, lineAdj n j k • a j)
    (w : ι → ℝ) (hw : ∀ k, w ⬝ᵥ a k = 0) (c : ℝ) (m : ℕ) :
    a (firstIdx n) ⬝ᵥ ((H ^ m) *ᵥ (c • a (lastIdx n) + w))
      = c * ((lineAdj n ^ m) (firstIdx n) (lastIdx n)) :=
  hamPowerMatrixEntry H hH a (lineAdj n) ha haH w hw c m

theorem overlap_eq_coefficient {ι : Type} [Fintype ι] {n : ℕ}
    (a : Fin (n + 1) → ι → ℝ)
    (ha : ∀ i j, a i ⬝ᵥ a j = if i = j then 1 else 0)
    (w : ι → ℝ) (hw : ∀ k, w ⬝ᵥ a k = 0) (c : ℝ) :
    a (lastIdx n) ⬝ᵥ (c • a (lastIdx n) + w) = c := by
  rw [dotProduct_add, dotProduct_smul]
  have hwlast : a (lastIdx n) ⬝ᵥ w = 0 := by
    rw [dotProduct_comm]; exact hw (lastIdx n)
  have hself : a (lastIdx n) ⬝ᵥ a (lastIdx n) = 1 := by
    rw [ha]; simp
  rw [hwlast, hself]
  simp

end Qatlib.Papers.StringRewrite07.MainResults
