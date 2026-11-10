/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GraphIsom13.GiCost

def encBits (N : ℕ) : ℕ := Nat.clog 2 N

def encSize (N : ℕ) : ℕ := 2 ^ encBits N

abbrev IntStr (N : ℕ) := Fin N → Fin (encSize N)

def sigmaMat {N : ℕ} (s : IntStr N) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => if (i.val : ℤ) = ((s j).val : ℤ) then 1 else 0

def cost1 {N : ℕ} (s : IntStr N) : ℕ :=
  ∑ i : Fin N, ∑ a ∈ Finset.Icc N (encSize N - 1), if (s i).val = a then 1 else 0

def cost2 {N : ℕ} (s : IntStr N) : ℕ :=
  ∑ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2),
    if s p.1 = s p.2 then 1 else 0

def cost3 {N : ℕ} (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (s : IntStr N) : ℕ :=
  ∑ i : Fin N, ∑ j : Fin N,
    Int.natAbs (((sigmaMat s * G.adjMatrix ℤ * (sigmaMat s)ᵀ) - G'.adjMatrix ℤ) i j)

def cost {N : ℕ} (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (s : IntStr N) : ℕ :=
  cost1 s + cost2 s + cost3 G G' s

theorem cost1_eq_zero_iff {N : ℕ} (s : IntStr N) :
    cost1 s = 0 ↔ ∀ i, (s i).val < N := by
  unfold cost1
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  constructor
  · intro h i
    by_contra hi
    have hi' : N ≤ (s i).val := not_lt.mp hi
    have hmem : (s i).val ∈ Finset.Icc N (encSize N - 1) := by
      rw [Finset.mem_Icc]
      exact ⟨hi', by have := (s i).isLt; omega⟩
    have hz := h i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Nat.zero_le _)] at hz
    have := hz (s i).val hmem
    simp at this
  · intro h i _
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Nat.zero_le _)]
    intro a ha
    rw [Finset.mem_Icc] at ha
    have := h i
    have hne : (s i).val ≠ a := by omega
    simp [hne]

theorem cost2_eq_zero_iff {N : ℕ} (s : IntStr N) :
    cost2 s = 0 ↔ ∀ i j, s i = s j → i = j := by
  unfold cost2
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  constructor
  · intro h i j hij
    by_cases hlt : i < j
    · have hmem : (i, j) ∈ (Finset.univ : Finset (Fin N × Fin N)).filter
          (fun p => p.1 < p.2) := by simp [hlt]
      have := h (i, j) hmem
      simp [hij] at this
    · by_cases hlt2 : j < i
      · have hmem : (j, i) ∈ (Finset.univ : Finset (Fin N × Fin N)).filter
            (fun p => p.1 < p.2) := by simp [hlt2]
        have := h (j, i) hmem
        have hji : s j = s i := hij.symm
        simp [hji] at this
      · exact le_antisymm (le_of_not_gt hlt2) (le_of_not_gt hlt)
  · intro h p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hlt⟩ := hp
    have hne : s p.1 ≠ s p.2 := by
      intro heq
      exact absurd (h p.1 p.2 heq) (ne_of_lt hlt)
    simp [hne]

theorem cost3_eq_zero_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (s : IntStr N) :
    cost3 G G' s = 0 ↔ sigmaMat s * G.adjMatrix ℤ * (sigmaMat s)ᵀ = G'.adjMatrix ℤ := by
  unfold cost3
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  constructor
  · intro h
    ext i j
    have hz := h i (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)] at hz
    have hz2 := hz j (Finset.mem_univ _)
    rw [Int.natAbs_eq_zero, Matrix.sub_apply, sub_eq_zero] at hz2
    exact hz2
  · intro h i _
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)]
    intro j _
    rw [show ((sigmaMat s * G.adjMatrix ℤ * (sigmaMat s)ᵀ) - G'.adjMatrix ℤ) i j = 0 by
      rw [h]; simp]
    simp

theorem permMatrix_mul_adj_mul_transpose_apply {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin N) (Fin N) ℤ) (i j : Fin N) :
    (σ.permMatrix ℤ * A * (σ.permMatrix ℤ)ᵀ) i j = A (σ i) (σ j) := by
  rw [Matrix.transpose_permMatrix]
  simp only [Equiv.Perm.permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem transpose_permMatrix_conj_apply {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin N) (Fin N) ℤ) (i j : Fin N) :
    ((σ.permMatrix ℤ)ᵀ * A * ((σ.permMatrix ℤ)ᵀ)ᵀ) i j = A (σ.symm i) (σ.symm j) := by
  have h2 : ((σ.permMatrix ℤ)ᵀ)ᵀ = σ.permMatrix ℤ := Matrix.transpose_transpose _
  rw [h2]
  have h1 : (σ.permMatrix ℤ)ᵀ = Equiv.Perm.permMatrix ℤ σ.symm := by
    rw [Matrix.transpose_permMatrix]
    rfl
  have h4 : σ.permMatrix ℤ = (Equiv.Perm.permMatrix ℤ σ.symm)ᵀ := by
    rw [Matrix.transpose_permMatrix]
    rfl
  rw [h1, h4]
  exact permMatrix_mul_adj_mul_transpose_apply σ.symm A i j

def MatIso {N : ℕ} (A A' : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  ∃ σ : Equiv.Perm (Fin N), A' = σ.permMatrix ℤ * A * (σ.permMatrix ℤ)ᵀ

theorem adjMatrix_eq_one_iff {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (i j : Fin N) : G.adjMatrix ℤ i j = 1 ↔ G.Adj i j := by
  rw [SimpleGraph.adjMatrix_apply]
  split <;> simp_all

theorem transpose_permMatrix_conj_adjMatrix {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (f : G ≃g G') :
    (Equiv.Perm.permMatrix ℤ f.toEquiv)ᵀ * G.adjMatrix ℤ
        * ((Equiv.Perm.permMatrix ℤ f.toEquiv)ᵀ)ᵀ = G'.adjMatrix ℤ := by
  ext i j
  rw [transpose_permMatrix_conj_apply, SimpleGraph.adjMatrix_apply,
    SimpleGraph.adjMatrix_apply]
  have hiff : G.Adj (f.toEquiv.symm i) (f.toEquiv.symm j) ↔ G'.Adj i j :=
    f.symm.map_rel_iff
  by_cases h : G'.Adj i j
  · have h' : G.Adj (f.toEquiv.symm i) (f.toEquiv.symm j) := hiff.mpr h
    rw [if_pos h', if_pos h]
  · have h' : ¬ G.Adj (f.toEquiv.symm i) (f.toEquiv.symm j) := by
      rw [hiff]; exact h
    rw [if_neg h', if_neg h]

theorem matIso_adjMatrix_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    MatIso (G.adjMatrix ℤ) (G'.adjMatrix ℤ) ↔ Nonempty (G ≃g G') := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨σ.symm, ?_⟩⟩
    intro a b
    rw [← adjMatrix_eq_one_iff G a b,
      ← adjMatrix_eq_one_iff G' (σ.symm a) (σ.symm b),
      hσ, permMatrix_mul_adj_mul_transpose_apply]
    simp
  · rintro ⟨f⟩
    refine ⟨f.toEquiv.symm, ?_⟩
    have h1 : Equiv.Perm.permMatrix ℤ f.toEquiv.symm
        = (Equiv.Perm.permMatrix ℤ f.toEquiv)ᵀ := by
      rw [Matrix.transpose_permMatrix]
      rfl
    rw [h1, Matrix.transpose_transpose]
    exact (transpose_permMatrix_conj_adjMatrix G G' f).symm

def permOf {N : ℕ} (s : IntStr N) (h1 : ∀ i, (s i).val < N)
    (h2 : ∀ i j, s i = s j → i = j) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (fun i => (⟨(s i).val, h1 i⟩ : Fin N)) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro i j hij
    apply h2
    apply Fin.ext
    simpa [Fin.mk.injEq] using hij

theorem conj_transpose_permMatrix_eq {N : ℕ} (σ : Equiv.Perm (Fin N))
    (A : Matrix (Fin N) (Fin N) ℤ) :
    (σ.permMatrix ℤ)ᵀ * A * ((σ.permMatrix ℤ)ᵀ)ᵀ
      = (Equiv.Perm.permMatrix ℤ σ.symm) * A * ((Equiv.Perm.permMatrix ℤ σ.symm))ᵀ := by
  ext i j
  simp only [transpose_permMatrix_conj_apply, permMatrix_mul_adj_mul_transpose_apply]

theorem sigmaMat_eq_transpose_permMatrix {N : ℕ} (s : IntStr N)
    (h1 : ∀ i, (s i).val < N) (h2 : ∀ i j, s i = s j → i = j) :
    sigmaMat s = ((permOf s h1 h2).permMatrix ℤ)ᵀ := by
  ext i j
  rw [Matrix.transpose_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  simp only [Option.mem_some_iff]
  unfold sigmaMat
  have hval : (permOf s h1 h2 j).val = (s j).val := by simp [permOf]
  by_cases hk : permOf s h1 h2 j = i
  · have hv : (i.val : ℤ) = ((s j).val : ℤ) := by
      have hival : i.val = (s j).val := by rw [← hk, hval]
      exact_mod_cast hival
    rw [if_pos hv, if_pos hk]
  · have hne : (i.val : ℤ) ≠ ((s j).val : ℤ) := by
      intro hv
      apply hk
      apply Fin.ext
      have hv' : i.val = (s j).val := by exact_mod_cast hv
      rw [hval]
      exact hv'.symm
    rw [if_neg hne, if_neg hk]

theorem gi_cop_zero_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    (∃ s : IntStr N, cost G G' s = 0) ↔ Nonempty (G ≃g G') := by
  constructor
  · rintro ⟨s, hs⟩
    unfold cost at hs
    have h3 : cost3 G G' s = 0 := by omega
    have h12 : cost1 s + cost2 s = 0 := by omega
    have h1 : cost1 s = 0 := by omega
    have h2 : cost2 s = 0 := by omega
    have h1' := (cost1_eq_zero_iff s).mp h1
    have h2' := (cost2_eq_zero_iff s).mp h2
    have hmat := (cost3_eq_zero_iff G G' s).mp h3
    have hsig := sigmaMat_eq_transpose_permMatrix s h1' h2'
    have hmat' : G'.adjMatrix ℤ
        = (Equiv.Perm.permMatrix ℤ (permOf s h1' h2').symm) * G.adjMatrix ℤ
          * ((Equiv.Perm.permMatrix ℤ (permOf s h1' h2').symm))ᵀ := by
      rw [← hmat, hsig]
      exact conj_transpose_permMatrix_eq _ _
    exact (matIso_adjMatrix_iff G G').mp ⟨(permOf s h1' h2').symm, hmat'⟩
  · rintro ⟨f⟩
    let σ : Equiv.Perm (Fin N) := f.toEquiv
    let s : IntStr N := fun i =>
      ⟨(σ i).val, lt_of_lt_of_le (σ i).isLt (Nat.le_pow_clog (by norm_num) N)⟩
    have h1 : ∀ i, (s i).val < N := fun i => (σ i).isLt
    have h2 : ∀ i j, s i = s j → i = j := by
      intro i j hij
      have hv : (s i).val = (s j).val := by rw [hij]
      have : σ i = σ j := Fin.ext hv
      exact σ.injective this
    have hperm : permOf s h1 h2 = σ := by
      ext i
      simp [permOf, s]
    refine ⟨s, ?_⟩
    unfold cost
    have hc1 : cost1 s = 0 := (cost1_eq_zero_iff s).mpr h1
    have hc2 : cost2 s = 0 := (cost2_eq_zero_iff s).mpr h2
    have hc3 : cost3 G G' s = 0 := by
      rw [cost3_eq_zero_iff]
      have hsig := sigmaMat_eq_transpose_permMatrix s h1 h2
      rw [hsig, hperm]
      exact transpose_permMatrix_conj_adjMatrix G G' f
    rw [hc1, hc2, hc3]

theorem gi_cop_witness {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] (s : IntStr N)
    (hs : cost G G' s = 0) :
    ∃ π : Equiv.Perm (Fin N),
      sigmaMat s = (π.permMatrix ℤ)ᵀ ∧
      G'.adjMatrix ℤ = (π.permMatrix ℤ)ᵀ * G.adjMatrix ℤ * (π.permMatrix ℤ) := by
  unfold cost at hs
  have h3 : cost3 G G' s = 0 := by omega
  have h1 : cost1 s = 0 := by omega
  have h2 : cost2 s = 0 := by omega
  have h1' := (cost1_eq_zero_iff s).mp h1
  have h2' := (cost2_eq_zero_iff s).mp h2
  have hmat := (cost3_eq_zero_iff G G' s).mp h3
  refine ⟨permOf s h1' h2', sigmaMat_eq_transpose_permMatrix s h1' h2', ?_⟩
  rw [← hmat, sigmaMat_eq_transpose_permMatrix s h1' h2']
  simp

theorem gi_cop_positive_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    (∀ s : IntStr N, 0 < cost G G' s) ↔ ¬ Nonempty (G ≃g G') := by
  constructor
  · intro h hne
    obtain ⟨s, hs⟩ := (gi_cop_zero_iff G G').mpr hne
    exact absurd hs (Nat.ne_of_gt (h s))
  · intro hne s
    exact Nat.pos_of_ne_zero fun hzero => hne ((gi_cop_zero_iff G G').mp ⟨s, hzero⟩)

end Qatlib.Papers.GraphIsom13.GiCost
