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

def gateSector {σ : Type} [Fintype σ] (sector : σ → Option (Fin 4)) (g : Fin 4) :
    Finset σ :=
  Finset.univ.filter (fun i => sector i = some g)

def restSector {σ : Type} [Fintype σ] (sector : σ → Option (Fin 4)) : Finset σ :=
  Finset.univ.filter (fun i => sector i = none)

theorem mem_gateSector {σ : Type} [Fintype σ] {sector : σ → Option (Fin 4)} {i : σ}
    {g : Fin 4} : i ∈ gateSector sector g ↔ sector i = some g := by
  simp [gateSector]

theorem mem_restSector {σ : Type} [Fintype σ] {sector : σ → Option (Fin 4)} {i : σ} :
    i ∈ restSector sector ↔ sector i = none := by
  simp [restSector]

theorem disjoint_gateSector {σ : Type} [Fintype σ] {sector : σ → Option (Fin 4)}
    {g g' : Fin 4} (h : g ≠ g') : Disjoint (gateSector sector g) (gateSector sector g') := by
  refine Finset.disjoint_left.mpr (fun i hi hi' => ?_)
  rw [mem_gateSector] at hi hi'
  rw [hi] at hi'
  exact h (Option.some.inj hi')

theorem disjoint_gateSector_rest {σ : Type} [Fintype σ] {sector : σ → Option (Fin 4)}
    (g : Fin 4) : Disjoint (gateSector sector g) (restSector sector) := by
  refine Finset.disjoint_left.mpr (fun i hi hi' => ?_)
  rw [mem_gateSector] at hi
  rw [mem_restSector] at hi'
  rw [hi] at hi'
  exact Option.some_ne_none g hi'

theorem gateSector_eq_filter {σ : Type} [Fintype σ] (sector : σ → Option (Fin 4))
    (g : Fin 4) : gateSector sector g = Finset.univ.filter (fun i => sector i = some g) := rfl

def execOp {σ : Type} [DecidableEq σ] (sector : σ → Option (Fin 4))
    (AT AS AH : Matrix σ σ ℝ) : Matrix σ σ ℝ :=
  fun i j =>
    if sector i = some 0 then (if sector j = some 0 then AT i j else 0)
    else if sector i = some 1 then (if sector j = some 1 then AS i j else 0)
    else if sector i = some 2 then (if sector j = some 2 then AH i j else 0)
    else if sector i = some 3 then 0
    else (if i = j then 1 else 0)

def HamEntry (x : ℝ) : Prop :=
  x = 0 ∨ x = (Real.sqrt 2)⁻¹ ∨ x = -(Real.sqrt 2)⁻¹

def ExecEntry (x : ℝ) : Prop :=
  x = 0 ∨ x = 1 ∨ x = (Real.sqrt 2)⁻¹ ∨ x = -(Real.sqrt 2)⁻¹

theorem execEntry_one : ExecEntry 1 := Or.inr (Or.inl rfl)

theorem execEntry_of_ham {x : ℝ} (h : HamEntry x) : ExecEntry x := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem execOp_entries {σ : Type} [DecidableEq σ] (sector : σ → Option (Fin 4))
    (AT AS AH : Matrix σ σ ℝ) (hT : ∀ i j, HamEntry (AT i j))
    (hS : ∀ i j, HamEntry (AS i j)) (hH : ∀ i j, HamEntry (AH i j))
    (i j : σ) : ExecEntry (execOp sector AT AS AH i j) := by
  unfold execOp
  by_cases h0 : sector i = some 0
  · rw [if_pos h0]
    by_cases h0' : sector j = some 0
    · rw [if_pos h0']; exact execEntry_of_ham (hT i j)
    · rw [if_neg h0']; exact Or.inl rfl
  · rw [if_neg h0]
    by_cases h1 : sector i = some 1
    · rw [if_pos h1]
      by_cases h1' : sector j = some 1
      · rw [if_pos h1']; exact execEntry_of_ham (hS i j)
      · rw [if_neg h1']; exact Or.inl rfl
    · rw [if_neg h1]
      by_cases h2 : sector i = some 2
      · rw [if_pos h2]
        by_cases h2' : sector j = some 2
        · rw [if_pos h2']; exact execEntry_of_ham (hH i j)
        · rw [if_neg h2']; exact Or.inl rfl
      · rw [if_neg h2]
        by_cases h3 : sector i = some 3
        · rw [if_pos h3]; exact Or.inl rfl
        · rw [if_neg h3]
          by_cases hij : i = j
          · rw [if_pos hij]; exact execEntry_one
          · rw [if_neg hij]; exact Or.inl rfl

theorem execOp_apply_sector_zero {σ : Type} [DecidableEq σ] (sector : σ → Option (Fin 4))
    (AT AS AH : Matrix σ σ ℝ) {i : σ} (hi : sector i = some 0) (j : σ) :
    execOp sector AT AS AH i j = if sector j = some 0 then AT i j else 0 := by
  unfold execOp
  rw [if_pos hi]

theorem execOp_apply_sector_three {σ : Type} [DecidableEq σ] (sector : σ → Option (Fin 4))
    (AT AS AH : Matrix σ σ ℝ) {i : σ} (hi : sector i = some 3) (j : σ) :
    execOp sector AT AS AH i j = 0 := by
  unfold execOp
  rw [if_neg (by rw [hi]; simp), if_neg (by rw [hi]; simp),
    if_neg (by rw [hi]; simp), if_pos hi]

theorem execOp_apply_rest {σ : Type} [DecidableEq σ] (sector : σ → Option (Fin 4))
    (AT AS AH : Matrix σ σ ℝ) {i : σ} (hi : sector i = none) (j : σ) :
    execOp sector AT AS AH i j = if i = j then 1 else 0 := by
  unfold execOp
  rw [if_neg (by rw [hi]; simp), if_neg (by rw [hi]; simp),
    if_neg (by rw [hi]; simp), if_neg (by rw [hi]; simp)]

def IsPermMatrix {σ : Type} [Fintype σ] (C : Matrix σ σ ℝ) : Prop :=
  (∀ i, ∃ j, C i j = 1 ∧ ∀ k, C i k = 1 → k = j) ∧ (∀ i j, C i j = 0 ∨ C i j = 1)

theorem perm_mul_apply {σ : Type} [Fintype σ] [DecidableEq σ] {C : Matrix σ σ ℝ}
    (hC : IsPermMatrix C) (M : Matrix σ σ ℝ) (i j : σ) :
    (C * M) i j = M (Classical.choose (hC.1 i)) j := by
  obtain ⟨j₀, hj₀, huniq⟩ := hC.1 i
  have hchoose : Classical.choose (hC.1 i) = j₀ :=
    huniq _ (Classical.choose_spec (hC.1 i)).1
  rw [hchoose, Matrix.mul_apply, Finset.sum_eq_single j₀]
  · rw [hj₀, one_mul]
  · intro b _ hb
    have hne : C i b ≠ 1 := fun h1 => hb (huniq b h1)
    have hz : C i b = 0 := by
      rcases hC.2 i b with h0 | h1
      · exact h0
      · exact absurd h1 hne
    rw [hz, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

theorem permMul_entries {σ : Type} [Fintype σ] [DecidableEq σ] {C X : Matrix σ σ ℝ}
    (hC : IsPermMatrix C) (hX : ∀ i j, ExecEntry (X i j)) :
    ∀ i j, ExecEntry ((C * X) i j) := by
  intro i j
  rw [perm_mul_apply hC]
  exact hX _ _

def IsZeroOne (x : ℝ) : Prop := x = 0 ∨ x = 1

def IsAdjMatrix {σ : Type} (A : Matrix σ σ ℝ) : Prop :=
  A.IsSymm ∧ (∀ i j, IsZeroOne (A i j)) ∧ (∀ i, A i i = 0)

theorem add_transpose_isAdjMatrix {σ : Type} [Fintype σ] [DecidableEq σ]
    (V : Matrix σ σ ℝ) (h01 : ∀ i j, IsZeroOne (V i j))
    (hnorev : ∀ i j, V i j = 1 → V j i = 0) :
    IsAdjMatrix (V + V.transpose) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    simp only [Matrix.add_apply, Matrix.transpose_apply]
    rw [add_comm]
  · intro i j
    rw [Matrix.add_apply, Matrix.transpose_apply]
    rcases h01 i j with hij | hij
    · rcases h01 j i with hji | hji
      · rw [hij, hji]; exact Or.inl (by norm_num)
      · rw [hij, hji]; exact Or.inr (by norm_num)
    · have hji : V j i = 0 := hnorev i j hij
      rw [hij, hji]; exact Or.inr (by norm_num)
  · intro i
    rw [Matrix.add_apply, Matrix.transpose_apply]
    have hVV : V i i ≠ 1 := fun h => by rw [hnorev i i h] at h; exact zero_ne_one h
    have h0 : V i i = 0 := by
      rcases h01 i i with h | h
      · exact h
      · exact absurd h hVV
    rw [h0]; norm_num

def replaceRel {σ : Type} (A : Matrix σ σ ℝ) (a b : σ) : Prop := A a b = 1

theorem replaceRel_symm {σ : Type} {A : Matrix σ σ ℝ} (hA : IsAdjMatrix A)
    {a b : σ} (h : replaceRel A a b) : replaceRel A b a := by
  have hsym : A b a = A a b := Matrix.IsSymm.ext_iff.mp hA.1 a b
  rw [replaceRel] at h ⊢
  rw [hsym]; exact h

theorem replaceRel_irrefl {σ : Type} {A : Matrix σ σ ℝ} (hA : IsAdjMatrix A) (a : σ) :
    ¬ replaceRel A a a := by
  intro h
  rw [replaceRel] at h
  rw [hA.2.2 a] at h
  exact zero_ne_one h

end Qatlib.Papers.StringRewrite07.MainResults
