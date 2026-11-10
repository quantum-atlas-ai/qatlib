/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Sigma.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Fin.Basic
import Mathlib.Order.RelIso.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.TermCongr
import Qatlib.Papers.UnitaryDigraph.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace Qatlib.Papers.UnitaryDigraph.MainResults.Complete

open Qatlib.Papers.UnitaryDigraph.MainResults.Defs
open Matrix

def ones (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun _ _ => 1

def shift (n : ℕ) : ℂ := (-1 + Complex.I) / (n : ℂ)

def completeMat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (if i = j then (1 : ℂ) else 0) + shift n

@[simp] theorem completeMat_apply (n : ℕ) (i j : Fin n) :
    completeMat n i j = (if i = j then (1 : ℂ) else 0) + shift n := rfl

theorem star_shift (n : ℕ) : star (shift n) = (-1 - Complex.I) / (n : ℂ) := by
  simp only [shift, Complex.star_def, star_div₀, star_add, star_neg, star_one,
    Complex.conj_I, star_natCast]
  ring

theorem star_completeMat_apply (n : ℕ) (i j : Fin n) :
    (star (completeMat n)) i j = (if i = j then (1 : ℂ) else 0) + star (shift n) := by
  simp only [Matrix.star_apply, completeMat]
  rw [star_add]
  congr 1
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ (j = i) := fun hh => h hh.symm
    simp [h, h']

theorem shift_key (n : ℕ) (hn : 0 < n) :
    shift n + star (shift n) + (n : ℂ) * (shift n * star (shift n)) = 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  rw [star_shift, shift]
  field_simp
  rw [Complex.ext_iff]
  constructor <;> norm_num

theorem completeMat_unitary (n : ℕ) (hn : 0 < n) :
    completeMat n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a c
  simp only [Matrix.mul_apply, Matrix.one_apply, completeMat_apply, star_completeMat_apply,
    star_shift]
  have hexp : ∀ j : Fin n,
      ((if a = j then (1 : ℂ) else 0) + shift n)
        * ((if j = c then (1 : ℂ) else 0) + (-1 - Complex.I) / (n : ℂ)) =
      (if a = j then (1 : ℂ) else 0) * (if j = c then (1 : ℂ) else 0)
        + (if a = j then (1 : ℂ) else 0) * ((-1 - Complex.I) / (n : ℂ))
        + shift n * (if j = c then (1 : ℂ) else 0)
        + shift n * ((-1 - Complex.I) / (n : ℂ)) := by
    intro j; ring
  simp only [hexp, Finset.sum_add_distrib]
  have h11 : ∑ j : Fin n, (if a = j then (1 : ℂ) else 0) * (if j = c then (1 : ℂ) else 0)
      = if a = c then 1 else 0 := by
    by_cases hac : a = c
    · subst hac; simp
    · have hz : ∀ j : Fin n, (if a = j then (1 : ℂ) else 0) * (if j = c then 1 else 0) = 0 := by
        intro j
        by_cases ha : a = j <;> by_cases hc : j = c <;> simp_all
      simp [hz, hac]
  have hsum1 : ∑ j : Fin n, (if a = j then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_ite_eq]; simp
  have h12 : ∑ j : Fin n, (if a = j then (1 : ℂ) else 0) * ((-1 - Complex.I) / (n : ℂ))
      = (-1 - Complex.I) / (n : ℂ) := by
    rw [← Finset.sum_mul, hsum1, one_mul]
  have h13 : ∑ j : Fin n, shift n * (if j = c then (1 : ℂ) else 0) = shift n := by
    rw [← Finset.mul_sum]
    have hsum2 : ∑ j : Fin n, (if j = c then (1 : ℂ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']; simp
    rw [hsum2, mul_one]
  have h14 : ∑ _j : Fin n, shift n * ((-1 - Complex.I) / (n : ℂ))
      = (n : ℂ) * (shift n * ((-1 - Complex.I) / (n : ℂ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [h11, h12, h13, h14]
  have hkey := shift_key n hn
  rw [star_shift] at hkey
  by_cases hac : a = c <;> simp [hac] <;> linear_combination hkey

theorem completeMat_ne_zero (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    completeMat n i j ≠ 0 := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  by_cases hij : i = j
  · subst hij
    have hdiag : (1 : ℂ) + shift n ≠ 0 := by
      intro h
      have h2 : (1 + shift n) * (n : ℂ) = 0 := by rw [h, zero_mul]
      rw [shift] at h2
      field_simp at h2
      have him : ((n : ℂ) + (-1 + Complex.I)).im = 0 := by rw [h2]; simp
      simp at him
    simpa [completeMat] using hdiag
  · have hoff : shift n ≠ 0 := by
      intro h
      have h2 : shift n * (n : ℂ) = 0 := by rw [h, zero_mul]
      rw [shift] at h2
      field_simp at h2
      have him : ((-1 : ℂ) + Complex.I).im = 0 := by rw [h2]; simp
      simp at him
    simpa [completeMat, hij] using hoff

theorem lemma3 (n : ℕ) (hn : 0 < n) :
    IsUnitaryDigraph (Digraph.complete (Fin n)) := by
  refine ⟨completeMat n, completeMat_unitary n hn, ?_⟩
  intro i j
  constructor
  · intro _; trivial
  · intro _; exact completeMat_ne_zero n hn i j

variable {V : Type} [Fintype V] [DecidableEq V]
variable {o : Type} [Fintype o] [DecidableEq o]

theorem isUnitaryDigraph_of_fiber_complete (D : Defs.Digraph V) (r c : V → o)
    (hAdj : ∀ i j, D.Adj i j ↔ r i = c j)
    (hcard : ∀ k, Nat.card {i : V // r i = k} = Nat.card {j : V // c j = k}) :
    IsUnitaryDigraph D := by
  classical
  let d : o → ℕ := fun k => Nat.card {i : V // r i = k}
  let rE : ∀ k, {i : V // r i = k} ≃ Fin (d k) := fun k =>
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := {i : V // r i = k})).symm
  let cE : ∀ k, {j : V // c j = k} ≃ Fin (d k) := fun k =>
    (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := {j : V // c j = k})).symm).trans
      (Fin.castOrderIso (hcard k).symm).toEquiv
  let W : Matrix (Σ k, Fin (d k)) (Σ k, Fin (d k)) ℂ :=
    Matrix.blockDiagonal' (fun k => completeMat (d k))
  let ρ : V ≃ Σ k, Fin (d k) :=
    (Equiv.sigmaFiberEquiv r).symm.trans (Equiv.sigmaCongrRight rE)
  let κ : V ≃ Σ k, Fin (d k) :=
    (Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight cE)
  let U : Matrix V V ℂ := W.submatrix ρ κ
  refine ⟨U, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    have hstar : star U = (star W).submatrix κ ρ := rfl
    have hW : W * star W = 1 := by
      have hblocks : (fun k => completeMat (d k) * star (completeMat (d k)))
          = (fun _ => (1 : Matrix (Fin (d _)) (Fin (d _)) ℂ)) := by
        funext k
        by_cases hk : d k = 0
        · rw [hk]
          ext i j
          exact Fin.elim0 i
        · exact Matrix.mem_unitaryGroup_iff.mp (completeMat_unitary (d k) (Nat.pos_of_ne_zero hk))
      have hstarW : star W
          = Matrix.blockDiagonal' (fun k => star (completeMat (d k))) := by
        rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
        rfl
      rw [hstarW, ← Matrix.blockDiagonal'_mul, hblocks]
      exact Matrix.blockDiagonal'_one
    calc U * star U = W.submatrix ρ κ * (star W).submatrix κ ρ := by rw [hstar]
      _ = (W * star W).submatrix ρ ρ := Matrix.submatrix_mul_equiv W (star W) ρ κ ρ
      _ = (1 : Matrix (Σ k, Fin (d k)) (Σ k, Fin (d k)) ℂ).submatrix ρ ρ := by rw [hW]
      _ = 1 := Matrix.submatrix_one_equiv ρ
  · intro i j
    rw [hAdj]
    have hρ : (ρ i).1 = r i := rfl
    have hκ : (κ j).1 = c j := rfl
    have hcond : ((ρ i).1 = (κ j).1) ↔ (r i = c j) := by
      rw [hρ, hκ]
    show U i j ≠ 0 ↔ r i = c j
    show Matrix.blockDiagonal' (fun k => completeMat (d k)) (ρ i) (κ j) ≠ 0 ↔ r i = c j
    rw [Matrix.blockDiagonal'_apply]
    by_cases h : (ρ i).1 = (κ j).1
    · rw [dif_pos h]
      haveI : Nonempty {i' : V // r i' = (ρ i).1} := ⟨⟨i, hρ.symm⟩⟩
      have hpos : 0 < d (ρ i).1 := Nat.card_pos
      refine ⟨fun _ => hcond.mp h, fun _ => completeMat_ne_zero (d (ρ i).1) hpos _ _⟩
    · rw [dif_neg h]
      exact ⟨fun h0 => absurd rfl h0, fun hc _ => h (hcond.mpr hc)⟩

end Qatlib.Papers.UnitaryDigraph.MainResults.Complete
