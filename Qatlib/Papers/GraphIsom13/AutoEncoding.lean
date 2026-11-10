/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Mathlib.SetTheory.Cardinal.Finite
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GraphIsom13.AutoEncoding

open Qatlib.Papers.GraphIsom13.GiCost

def permToStr {N : ℕ} (π : Equiv.Perm (Fin N)) : IntStr N :=
  fun i => ⟨(π i).val, lt_of_lt_of_le (π i).isLt (Nat.le_pow_clog (by norm_num) N)⟩

def strToPerm {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (s : IntStr N) (h : cost G G s = 0) : Equiv.Perm (Fin N) :=
  permOf s
    ((cost1_eq_zero_iff s).mp (by have h' := h; unfold cost at h'; omega))
    ((cost2_eq_zero_iff s).mp (by have h' := h; unfold cost at h'; omega))

def IsAut {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (π : Equiv.Perm (Fin N)) : Prop :=
  ∀ i j, G.Adj i j ↔ G.Adj (π i) (π j)

section ZeroCost

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

theorem strToPerm_isAut (s : IntStr N) (h : cost G G s = 0) :
    IsAut G (strToPerm G s h) := by
  intro i j
  have h1 : cost1 s = 0 := by have h' := h; unfold cost at h'; omega
  have h2 : cost2 s = 0 := by have h' := h; unfold cost at h'; omega
  have h3 : cost3 G G s = 0 := by have h' := h; unfold cost at h'; omega
  have h1' := (cost1_eq_zero_iff s).mp h1
  have h2' := (cost2_eq_zero_iff s).mp h2
  have hmat := (cost3_eq_zero_iff G G s).mp h3
  have hsig := sigmaMat_eq_transpose_permMatrix s h1' h2'
  have hperm : permOf s h1' h2' = strToPerm G s h := by
    apply Equiv.ext
    intro i
    exact Fin.ext rfl
  have hmatEq : G.adjMatrix ℤ
      = ((strToPerm G s h).permMatrix ℤ)ᵀ * G.adjMatrix ℤ
        * (((strToPerm G s h).permMatrix ℤ)ᵀ)ᵀ := by
    have h1 : ((strToPerm G s h).permMatrix ℤ)ᵀ = sigmaMat s := by
      rw [← hperm, ← hsig]
    rw [h1]
    exact hmat.symm
  have hA : ∀ i j, G.adjMatrix ℤ ((strToPerm G s h).symm i) ((strToPerm G s h).symm j)
      = G.adjMatrix ℤ i j := by
    intro i j
    have h := congrFun (congrFun hmatEq i) j
    rw [transpose_permMatrix_conj_apply] at h
    exact h.symm
  have hA' : G.adjMatrix ℤ ((strToPerm G s h) i) ((strToPerm G s h) j)
      = G.adjMatrix ℤ i j := by
    have h := hA ((strToPerm G s h) i) ((strToPerm G s h) j)
    simpa using h.symm
  rw [← adjMatrix_eq_one_iff G i j,
    ← adjMatrix_eq_one_iff G ((strToPerm G s h) i) ((strToPerm G s h) j), hA']

theorem permToStr_cost_zero (π : Equiv.Perm (Fin N)) (hπ : IsAut G π) :
    cost G G (permToStr π) = 0 := by
  let f : G ≃g G :=
    { toEquiv := π
      map_rel_iff' := fun {a b} => (hπ a b).symm }
  have h1 : ∀ i, (permToStr π i).val < N := fun i => (π i).isLt
  have h2 : ∀ i j, permToStr π i = permToStr π j → i = j := by
    intro i j hij
    have hv : (permToStr π i).val = (permToStr π j).val := by rw [hij]
    have hπij : π i = π j := Fin.ext hv
    exact π.injective hπij
  have hperm : permOf (permToStr π) h1 h2 = π := by
    apply Equiv.ext
    intro i
    exact Fin.ext rfl
  have hc1 : cost1 (permToStr π) = 0 := (cost1_eq_zero_iff _).mpr h1
  have hc2 : cost2 (permToStr π) = 0 := (cost2_eq_zero_iff _).mpr h2
  have hc3 : cost3 G G (permToStr π) = 0 := by
    rw [cost3_eq_zero_iff]
    have hsig := sigmaMat_eq_transpose_permMatrix (permToStr π) h1 h2
    rw [hsig, hperm]
    exact transpose_permMatrix_conj_adjMatrix G G f
  unfold cost
  rw [hc1, hc2, hc3]

theorem permToStr_strToPerm (s : IntStr N) (h : cost G G s = 0) :
    permToStr (strToPerm G s h) = s := by
  ext i
  simp [permToStr, strToPerm, permOf]

theorem strToPerm_permToStr (π : Equiv.Perm (Fin N)) (hπ : IsAut G π) :
    strToPerm G (permToStr π) (permToStr_cost_zero G π hπ) = π := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  simp [strToPerm, permToStr, permOf]

def zeroCostAutEquiv :
    {s : IntStr N // cost G G s = 0} ≃ {π : Equiv.Perm (Fin N) // IsAut G π} where
  toFun s := ⟨strToPerm G s.1 s.2, strToPerm_isAut G s.1 s.2⟩
  invFun π := ⟨permToStr π.1, permToStr_cost_zero G π.1 π.2⟩
  left_inv s := by
    apply Subtype.ext
    exact permToStr_strToPerm G s.1 s.2
  right_inv π := by
    apply Subtype.ext
    exact strToPerm_permToStr G π.1 π.2

theorem automorphism_card_zero_strings :
    Nat.card {π : Equiv.Perm (Fin N) // IsAut G π}
      = Nat.card {s : IntStr N // cost G G s = 0} :=
  (Nat.card_congr (zeroCostAutEquiv G)).symm

end ZeroCost

end Qatlib.Papers.GraphIsom13.AutoEncoding
