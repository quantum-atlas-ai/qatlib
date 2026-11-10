/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem2PathsReduction
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.GraphLift

open Finset Matrix
open Qatlib.Papers.BQPMixSparse06.MainResults

def absEntry (a : ℤ) : ℤ := if a = 0 then 0 else 1

def absMat {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  A.map absEntry

def outerLift {N : ℕ} (u v : Fin 2 → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  fun p q => u p.1 * v q.1 * A p.2 q.2

theorem blockConvert_entry_decomp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (i j : Fin N) (s t : Fin 2) :
    blockConvert A (s, i) (t, j) =
      phiMinus s * (A i j : ℝ) * phiMinus t +
        phiPlus s * (absEntry (A i j) : ℝ) * phiPlus t := by
  rcases hA i j with h | h | h
  · fin_cases s <;> fin_cases t <;>
      simp [h, blockConvert, gammaBlock, phiMinus, phiPlus, absEntry] <;>
      nlinarith [hsq_sqrt_two]
  · fin_cases s <;> fin_cases t <;>
      simp [h, blockConvert, gammaBlock, phiMinus, phiPlus, absEntry]
  · fin_cases s <;> fin_cases t <;>
      simp [h, blockConvert, gammaBlock, phiMinus, phiPlus, absEntry] <;>
      nlinarith [hsq_sqrt_two]

theorem blockConvert_decomp {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) :
    blockConvert A =
      outerLift phiMinus phiMinus (realCast A) +
        outerLift phiPlus phiPlus (realCast (absMat A)) := by
  ext p q
  obtain ⟨s, i⟩ := p
  obtain ⟨t, j⟩ := q
  simp only [Matrix.add_apply, outerLift, realCast, absMat, Matrix.map_apply]
  rw [blockConvert_entry_decomp A hA i j s t]
  ring

theorem lift_automorphism {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) :
    pairFlip * blockConvert A * pairFlip = blockConvert A :=
  pairFlip_conj_blockConvert A hA

theorem blockConvert_row_card {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (s : Fin 2) (i : Fin N) :
    (univ.filter (fun q : Fin 2 × Fin N => blockConvert A (s, i) q ≠ 0)).card =
      (univ.filter (fun j : Fin N => A i j ≠ 0)).card := by
  classical
  have hAnz : ∀ j : Fin N, A i j = 0 ∨ A i j = 1 ∨ A i j = -1 := by
    intro j
    rcases hA i j with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hpair : (∑ q ∈ (univ : Finset (Fin 2 × Fin N)),
        (if blockConvert A (s, i) q ≠ 0 then (1:ℕ) else 0)) =
      ∑ j : Fin N, ∑ t : Fin 2,
        (if blockConvert A (s, i) (t, j) ≠ 0 then (1:ℕ) else 0) := by
    rw [Fintype.sum_prod_type (γ := ℕ)]
    exact Finset.sum_comm
  have hL : (univ.filter (fun q : Fin 2 × Fin N => blockConvert A (s, i) q ≠ 0)).card =
      ∑ j, (if A i j = 0 then (0:ℕ) else 1) := by
    rw [Finset.card_filter (p := fun q : Fin 2 × Fin N => blockConvert A (s, i) q ≠ 0)
      (s := (univ : Finset (Fin 2 × Fin N)))]
    rw [hpair]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [blockConvert]
    have hcf : (∑ x : Fin 2, (if gammaBlock (A i j) s x ≠ 0 then (1:ℕ) else 0)) =
        (univ.filter (fun t : Fin 2 => gammaBlock (A i j) s t ≠ 0)).card := by
      simpa using (Finset.card_filter
        (p := fun t : Fin 2 => gammaBlock (A i j) s t ≠ 0)
        (s := (univ : Finset (Fin 2)))).symm
    exact hcf.trans (gammaBlock_row_nz (A i j) (hAnz j) s)
  have hR : (univ.filter (fun j : Fin N => A i j ≠ 0)).card =
      ∑ j, (if A i j = 0 then (0:ℕ) else 1) := by
    rw [Finset.card_filter (p := fun j : Fin N => A i j ≠ 0)
      (s := (univ : Finset (Fin N)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : A i j = 0 <;> simp [h]
  rw [hL, hR]

end Qatlib.Papers.BQPMixSparse06.GraphLift
