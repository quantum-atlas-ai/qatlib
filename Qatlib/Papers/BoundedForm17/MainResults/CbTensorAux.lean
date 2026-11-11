/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbFormsAux
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option backward.isDefEq.respectTransparency false

/-!
# CbTensorAux — shared tensor cb-norm machinery for arXiv:1711.07285v3

Support lemmas used by the paper-level developments of Arunachalam–Briët–Palazuelos,
*Quantum Query Algorithms are Completely Bounded Forms* (fixed arXiv:1711.07285v3):

* the defining supremum of `tensorCbNorm` is nonnegative and bounded above by the
  entrywise `l1` mass, so a member of the defining set bounds the cb-norm;
* permutation invariance of a pairwise-commuting ordered matrix word
  (`matProdFin_comp_perm`), the paper's commutativity reordering step;
* the set defining `formCbNorm` is nonempty for a symmetric tensor.

Nothing here assumes Christensen–Sinclair or any factorization certificate.
-/
set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.QueryComplexity.CbDegreeBridge


namespace Qatlib.Papers.BoundedForm17.MainResults.CbTensorAux

variable {κ : Type} [Fintype κ] {s : ℕ}

/-! ## The defining supremum of `tensorCbNorm` -/

/-- The completely bounded norm of a tensor is nonnegative. -/
theorem tensorCbNorm_nonneg (T : RealTensor κ s) : 0 ≤ tensorCbNorm T := by
  refine Real.sSup_nonneg fun r hr => ?_
  obtain ⟨d, A, hA, rfl⟩ := hr
  exact norm_nonneg _

/-- The defining supremum of `tensorCbNorm` is bounded above by the entrywise `l1` mass
(each contraction family produces an amplified evaluation of norm at most `∑ i, |T i|`). -/
theorem tensorCbNorm_bddAbove (T : RealTensor κ s) :
    BddAbove {r : ℝ | ∃ (d : ℕ) (A : Fin s → κ → Matrix (Fin d) (Fin d) ℂ),
      (∀ j i, ‖A j i‖ ≤ 1) ∧
        r = ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖} := by
  refine ⟨∑ i : Fin s → κ, |T i|, ?_⟩
  rintro r ⟨d, A, hA, rfl⟩
  calc ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖
      ≤ ∑ i : Fin s → κ, ‖(T i : ℂ) • matProdFin s (fun j => A j (i j))‖ :=
        norm_sum_le Finset.univ _
    _ ≤ ∑ i : Fin s → κ, |T i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc ‖(T i : ℂ) • matProdFin s (fun j => A j (i j))‖
            = ‖(T i : ℂ)‖ * ‖matProdFin s (fun j => A j (i j))‖ := norm_smul _ _
          _ ≤ ‖(T i : ℂ)‖ * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              refine le_trans (l2_opNorm_matProdFin_le (fun j => A j (i j))) ?_
              calc (∏ j, ‖A j (i j)‖) ≤ ∏ _j : Fin s, (1 : ℝ) :=
                    Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => hA j (i j)
                _ = 1 := by simp
          _ = |T i| := by rw [mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Membership in the defining set of `tensorCbNorm` gives the norm bound. -/
theorem norm_le_tensorCbNorm {d : ℕ} (T : RealTensor κ s)
    (A : Fin s → κ → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ j i, ‖A j i‖ ≤ 1) :
    ‖∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j))‖ ≤ tensorCbNorm T :=
  le_csSup (tensorCbNorm_bddAbove T) ⟨d, A, hA, rfl⟩

/-! ## Permutation invariance of a commuting matrix word -/

/-- Reindexing a `Fin k`-indexed family by a permutation does not change its ordered
product when the family is pairwise commuting. -/
theorem matProdFin_comp_perm {m : Type} [Fintype m] [DecidableEq m] {k : ℕ}
    (M : Fin k → Matrix m m ℂ) (hM : ∀ i j, M i * M j = M j * M i)
    (ρ : Equiv.Perm (Fin k)) :
    matProdFin k (fun j => M (ρ j)) = matProdFin k M := by
  have hpair : ∀ l : List (Fin k), l.Pairwise (Function.onFun Commute M) := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [List.pairwise_cons]
        exact ⟨fun b _ => hM a b, ih⟩
  rw [matProdFin, matProdFin, show (fun j => M (ρ j)) = M ∘ ρ from rfl, ← List.map_map]
  refine List.Perm.prod_eq' ((Equiv.Perm.map_finRange_perm ρ).map M) ?_
  exact (hpair _).map M (fun a b h => h)

/-- Scaling a tensor scales its cb-norm at most by the absolute value of the scalar. -/
theorem tensorCbNorm_constMul_le (c : ℝ) (T : RealTensor κ s) :
    tensorCbNorm (fun i => c * T i) ≤ |c| * tensorCbNorm T := by
  have hbdd := tensorCbNorm_bddAbove T
  refine csSup_le ?_ fun r hr => ?_
  · exact ⟨_, 1, fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ),
      fun _ _ => by simp, rfl⟩
  · obtain ⟨d, A, hA, rfl⟩ := hr
    show ‖∑ i : Fin s → κ, ((c * T i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j))‖
        ≤ |c| * tensorCbNorm T
    have hsmul : ∑ i : Fin s → κ, ((c * T i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j))
        = ((c : ℝ) : ℂ) • ∑ i : Fin s → κ, (T i : ℂ) • matProdFin s (fun j => A j (i j)) := by
      have hterm : ∀ i : Fin s → κ,
          ((c * T i : ℝ) : ℂ) • matProdFin s (fun j => A j (i j))
            = ((c : ℝ) : ℂ) • ((T i : ℂ) • matProdFin s (fun j => A j (i j))) := by
        intro i
        rw [Complex.ofReal_mul, smul_smul]
      rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.smul_sum]
    rw [hsmul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (le_csSup hbdd ⟨d, A, hA, rfl⟩) (abs_nonneg c)

/-- The set defining `formCbNorm` is bounded below by zero. -/
theorem formCbNorm_set_bddBelow (T : RealTensor κ s) :
    BddBelow {c : ℝ | ∃ D : Equiv.Perm (Fin s) → RealTensor κ s,
      (∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ)) ∧
        c = ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ)} := by
  refine ⟨0, ?_⟩
  rintro c ⟨D, -, rfl⟩
  exact Finset.sum_nonneg fun σ _ => tensorCbNorm_nonneg _

/-- A symmetric tensor is a fixed point of every permutation of its slots. -/
theorem isSymmTensor_apply (T : RealTensor κ s) (hT : IsSymmTensor T)
    (i : Fin s → κ) (σ : Equiv.Perm (Fin s)) : T (i ∘ σ) = T i := by
  have h := congrFun (hT σ) i
  simpa [permTensor] using h

/-- The set defining `formCbNorm` is nonempty for a symmetric tensor: the constant
decomposition `T^σ = (s!)⁻¹ • T` reproduces `T`. -/
theorem formCbNorm_set_nonempty (T : RealTensor κ s) (hT : IsSymmTensor T) :
    {c : ℝ | ∃ D : Equiv.Perm (Fin s) → RealTensor κ s,
      (∀ i : Fin s → κ, T i = ∑ σ : Equiv.Perm (Fin s), D σ (i ∘ σ)) ∧
        c = ∑ σ : Equiv.Perm (Fin s), tensorCbNorm (D σ)}.Nonempty := by
  have hfac : (Nat.factorial s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos s).ne'
  refine ⟨∑ _σ : Equiv.Perm (Fin s), tensorCbNorm (fun i => (Nat.factorial s : ℝ)⁻¹ * T i),
    fun _ => fun i => (Nat.factorial s : ℝ)⁻¹ * T i, ?_, rfl⟩
  intro i
  have hsum : ∑ _σ : Equiv.Perm (Fin s), ((Nat.factorial s : ℝ)⁻¹ * T i)
      = T i := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  calc T i = ∑ _σ : Equiv.Perm (Fin s), ((Nat.factorial s : ℝ)⁻¹ * T i) := hsum.symm
    _ = ∑ σ : Equiv.Perm (Fin s), (Nat.factorial s : ℝ)⁻¹ * T (i ∘ σ) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [isSymmTensor_apply T hT i σ]

/-- The reindexing equivalence `i ↦ i ∘ σ` on `Fin s → κ`. -/
def compEquiv (σ : Equiv.Perm (Fin s)) : (Fin s → κ) ≃ (Fin s → κ) where
  toFun i := i ∘ σ
  invFun j := j ∘ σ.symm
  left_inv i := by funext k; simp
  right_inv j := by funext k; simp

end Qatlib.Papers.BoundedForm17.MainResults.CbTensorAux
