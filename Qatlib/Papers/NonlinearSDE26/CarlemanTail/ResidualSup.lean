/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CarlemanError17.MainResults.Core.SourceModel

@[expose] public section

/-!
# The Carleman residual in the coordinate supremum norm

The transfer block and the maximum absolute row-sum norm of
arXiv:1711.02552 are used to verify the supremum-norm instance of
arXiv:2603.12398v1, Lemma 4, for real quadratic systems.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open Qatlib.Papers.CarlemanError17.MainResults.Core

namespace Qatlib.Papers.NonlinearSDE26.CarlemanTail

/-- The tensor power of the input vector, on length-`k` tuples of coordinates. -/
def kronPowVec {n : ℕ} (x : TP n 1 → ℝ) (k : ℕ) : TP n k → ℝ :=
  fun p => ∏ j : Fin k, x (fun _ : Fin 1 => p j)

/-- The vector supremum in its nonempty-index form. -/
private theorem vecSup_eq_sup' {I : Type} [Fintype I] [Nonempty I] (x : I → ℝ) :
    vecSup x = Finset.univ.sup' Finset.univ_nonempty (fun i => |x i|) := by
  classical
  rw [vecSup, dite_eq_left (inferInstance : Nonempty I)]

/-- Every absolute coordinate is at most the vector supremum. -/
private theorem abs_le_vecSup {I : Type} [Fintype I] [Nonempty I] (x : I → ℝ) (i : I) :
    |x i| ≤ vecSup x := by
  rw [vecSup_eq_sup']
  exact Finset.le_sup' (fun j => |x j|) (Finset.mem_univ i)

/-- Coordinate supremum norms multiply on the tensor powers in Eq. (21). -/
theorem vecSup_kronPowVec {n : ℕ} (hn : 0 < n) (x : TP n 1 → ℝ) (k : ℕ) :
    vecSup (kronPowVec x k) = vecSup x ^ k := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply le_antisymm
  · rw [vecSup_eq_sup', Finset.sup'_le_iff]
    intro p _
    rw [kronPowVec, Finset.abs_prod]
    calc
      _ ≤ ∏ _j : Fin k, vecSup x := Finset.prod_le_prod₀
        (fun _ _ => abs_nonneg _) (fun _ _ => abs_le_vecSup x _)
      _ = _ := by simp
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := TP n 1))
        (fun i => |x i|)
    have hmax : vecSup x = |x i| := (vecSup_eq_sup' x).trans hi
    let p : TP n k := fun _ => i 0
    have he : (fun _ : Fin 1 => i 0) = i := by
      funext j
      rw [Subsingleton.elim j 0]
    calc
      vecSup x ^ k = |kronPowVec x k p| := by
        rw [hmax, kronPowVec, Finset.abs_prod]
        simp only [p, he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ vecSup (kronPowVec x k) := abs_le_vecSup _ p

/-- The absolute row-sum norm is compatible with the vector supremum. -/
private theorem vecSup_mulVec_le {I J : Type} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (A : Matrix I J ℝ) (v : J → ℝ) :
    vecSup (A *ᵥ v) ≤ matSup A * vecSup v := by
  rw [vecSup_eq_sup', Finset.sup'_le_iff]
  intro i _
  have hv : 0 ≤ vecSup v :=
    (abs_nonneg _).trans (abs_le_vecSup v (Classical.choice inferInstance))
  calc
    |(A *ᵥ v) i| ≤ ∑ j, |A i j| * |v j| := by
      simpa only [Matrix.mulVec, dotProduct, abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun j => A i j * v j) Finset.univ)
    _ ≤ ∑ j, |A i j| * vecSup v := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (abs_le_vecSup v j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * vecSup v := (Finset.sum_mul ..).symm
    _ ≤ matSup A * vecSup v := by
      apply mul_le_mul_of_nonneg_right _ hv
      rw [matSup_def A (inferInstance : Nonempty I)]
      exact Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i)

/-- Lemma 4, Eq. (16), for the coordinate supremum norm on the first
omitted block of a truncation. -/
theorem carleman_residual_sup_bound {n N : ℕ} (hn : 0 < n)
    (F : (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) (x : TP n 1 → ℝ) :
    vecSup (transfer F N 1 *ᵥ kronPowVec x (N + 1)) ≤
      (N : ℝ) * matSup (F 2) * vecSup x ^ (N + 1) := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases N with _ | N
  · simp [transfer, vecSup_eq_sup']
  · have hx : 0 ≤ vecSup x :=
      (abs_nonneg _).trans (abs_le_vecSup x (fun _ => ⟨0, hn⟩))
    exact (vecSup_mulVec_le _ _).trans (by
      rw [vecSup_kronPowVec hn]
      exact mul_le_mul_of_nonneg_right (prop_three_three hn F _ (Nat.succ_pos N) 1) (pow_nonneg hx _))

/-- The same residual bound applies at each time and to each realized trajectory. -/
theorem pathwise_carleman_residual_sup_bound {Ω : Type} {n N : ℕ} (hn : 0 < n)
    (F : ℝ → (j : ℕ) → Matrix (TP n 1) (TP n j) ℝ) (x : Ω → ℝ → TP n 1 → ℝ) :
    ∀ ω t, vecSup (transfer (F t) N 1 *ᵥ kronPowVec (x ω t) (N + 1)) ≤
      (N : ℝ) * matSup (F t 2) * vecSup (x ω t) ^ (N + 1) :=
  fun ω t => carleman_residual_sup_bound hn (F t) (x ω t)

end Qatlib.Papers.NonlinearSDE26.CarlemanTail
