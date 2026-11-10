/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Defs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset Matrix

def doubledPathDiff {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) (j : Fin N) :
    ℝ := M (0, j) (0, j) - M (0, j) (1, j)

def flipFin (s : Fin 2) : Fin 2 := if s = 0 then 1 else 0

def flipBit {N : ℕ} (p : Fin 2 × Fin N) : Fin 2 × Fin N := (flipFin p.1, p.2)

lemma flipFin_involutive (s : Fin 2) : flipFin (flipFin s) = s := by
  fin_cases s <;> simp [flipFin]

lemma flipBit_involutive {N : ℕ} (p : Fin 2 × Fin N) : flipBit (flipBit p) = p := by
  obtain ⟨s, i⟩ := p
  simp [flipBit, flipFin_involutive]

lemma flipBit_one {N : ℕ} (j : Fin N) : flipBit ((1 : Fin 2), j) = (0, j) := by
  simp [flipBit, flipFin]

lemma flipBit_injective {N : ℕ} : Function.Injective (flipBit : Fin 2 × Fin N → _) := by
  intro p q h
  have := congrArg flipBit h
  simpa [flipBit_involutive] using this

def pairFlip {N : ℕ} : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ :=
  fun p q => if q = flipBit p then 1 else 0

@[simp] theorem pairFlip_mul_pairFlip {N : ℕ} :
    pairFlip * pairFlip = (1 : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) := by
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (flipBit p)]
  · simp [pairFlip, flipBit_involutive p, eq_comm]
  · intro k _ hk
    simp [pairFlip, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pairFlip_conj_apply {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (p q : Fin 2 × Fin N) :
    ((pairFlip * M * pairFlip : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)) p q =
      M (flipBit p) (flipBit q) := by
  have h1 : ∀ k, ((pairFlip * M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)) p k =
      M (flipBit p) k := by
    intro k
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (flipBit p)]
    · simp [pairFlip]
    · intro l _ hl
      simp [pairFlip, hl]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [h1]
  rw [Finset.sum_eq_single (flipBit q)]
  · simp [pairFlip, flipBit_involutive q]
  · intro k _ hk
    have hq : q ≠ flipBit k := by
      intro h
      have h2 := congrArg flipBit h
      simp [flipBit_involutive] at h2
      exact hk h2.symm
    simp [pairFlip, hq]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma gammaBlock_flip (a : ℤ) (ha : a = 0 ∨ a = 1 ∨ a = -1) (s t : Fin 2) :
    gammaBlock a (flipFin s) (flipFin t) = gammaBlock a s t := by
  rcases ha with rfl | rfl | rfl
  · simp [gammaBlock]
  · fin_cases s <;> fin_cases t <;> simp [gammaBlock, Matrix.one_apply, flipFin]
  · fin_cases s <;> fin_cases t <;> simp [gammaBlock, flipFin]

theorem pairFlip_conj_blockConvert {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) :
    pairFlip * blockConvert A * pairFlip = blockConvert A := by
  ext p q
  rw [pairFlip_conj_apply]
  simp only [blockConvert, flipBit]
  have hA' : A p.2 q.2 = 0 ∨ A p.2 q.2 = 1 ∨ A p.2 q.2 = -1 := by
    rcases hA p.2 q.2 with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  exact gammaBlock_flip (A p.2 q.2) hA' p.1 q.1

theorem pairFlip_sandwich_mul {N : ℕ}
    (X Y : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ) :
    (pairFlip * X * pairFlip) * (pairFlip * Y * pairFlip) =
      pairFlip * (X * Y) * pairFlip := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc pairFlip pairFlip (Y * pairFlip)]
  rw [pairFlip_mul_pairFlip, Matrix.one_mul]

theorem pairFlip_conj_pow {N : ℕ} (M : Matrix (Fin 2 × Fin N) (Fin 2 × Fin N) ℝ)
    (m : ℕ) : (pairFlip * M * pairFlip) ^ m = pairFlip * M ^ m * pairFlip := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, pairFlip_mul_pairFlip]
  | succ m ih => rw [pow_succ, ih, pow_succ, pairFlip_sandwich_mul]

theorem blockConvert_pow_diag_eq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (m : ℕ) (j : Fin N) :
    ((blockConvert A) ^ m) ((1 : Fin 2), j) ((1 : Fin 2), j) =
      ((blockConvert A) ^ m) (0, j) (0, j) := by
  conv_lhs =>
    rw [← pairFlip_conj_blockConvert A hA, pairFlip_conj_pow, pairFlip_conj_apply,
      flipBit_one]

theorem gammaBlock_symm (a : ℤ) (s t : Fin 2) : gammaBlock a s t = gammaBlock a t s := by
  by_cases h0 : a = 0
  · rw [h0]
    simp [gammaBlock]
  · by_cases h1 : a = 1
    · rw [h1]
      fin_cases s <;> fin_cases t <;> simp [gammaBlock, Matrix.one_apply]
    · have hσ : gammaBlock a = !![0, 1; 1, 0] := by
        simp [gammaBlock, h0, h1]
      rw [hσ]
      fin_cases s <;> fin_cases t <;> simp

theorem blockConvert_symm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hAsym : ∀ i j, A i j = A j i) (p q : Fin 2 × Fin N) :
    blockConvert A p q = blockConvert A q p := by
  simp only [blockConvert]
  rw [hAsym q.2 p.2]
  exact gammaBlock_symm (A p.2 q.2) p.1 q.1

theorem blockConvert_transpose {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hAsym : ∀ i j, A i j = A j i) :
    (blockConvert A)ᵀ = blockConvert A := by
  ext p q
  rw [Matrix.transpose_apply]
  exact (blockConvert_symm A hAsym p q).symm

theorem blockConvert_pow_symm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hAsym : ∀ i j, A i j = A j i) (m : ℕ) (p q : Fin 2 × Fin N) :
    ((blockConvert A) ^ m) p q = ((blockConvert A) ^ m) q p := by
  have h : (((blockConvert A) ^ m))ᵀ = (blockConvert A) ^ m := by
    rw [Matrix.transpose_pow, blockConvert_transpose A hAsym]
  have := congrFun (congrFun h p) q
  rw [Matrix.transpose_apply] at this
  exact this.symm

theorem blockConvert_mulVec_lift {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (v : Fin N → ℝ) :
    blockConvert A *ᵥ liftVec phiMinus v = liftVec phiMinus (realCast A *ᵥ v) := by
  funext p
  simp only [blockConvert, liftVec, Matrix.mulVec, realCast, Matrix.map_apply, dotProduct]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hAi : ∀ i : Fin N, A p.2 i = 0 ∨ A p.2 i = 1 ∨ A p.2 i = -1 := by
    intro i
    rcases hA p.2 i with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hinner : ∀ i : Fin N,
      (∑ s : Fin 2, gammaBlock (A p.2 i) p.1 s * (v i * phiMinus s)) =
        (A p.2 i : ℝ) * v i * phiMinus p.1 := by
    intro i
    have hg := gammaBlock_mulVec_phiMinus (A p.2 i) (hAi i) p.1
    calc (∑ s : Fin 2, gammaBlock (A p.2 i) p.1 s * (v i * phiMinus s))
        = v i * (∑ s : Fin 2, gammaBlock (A p.2 i) p.1 s * phiMinus s) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = v i * ((A p.2 i : ℝ) * phiMinus p.1) := by rw [hg]
      _ = (A p.2 i : ℝ) * v i * phiMinus p.1 := by ring
  simp only [hinner]
  rw [Finset.sum_mul]

theorem blockConvert_pow_mulVec_lift {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (m : ℕ) (v : Fin N → ℝ) :
    (blockConvert A) ^ m *ᵥ liftVec phiMinus v =
      liftVec phiMinus (((realCast A) ^ m) *ᵥ v) := by
  induction m generalizing v with
  | zero => simp [liftVec]
  | succ m ih =>
      calc (blockConvert A) ^ (m + 1) *ᵥ liftVec phiMinus v
          = ((blockConvert A) ^ m * blockConvert A) *ᵥ liftVec phiMinus v := by
            rw [pow_succ]
        _ = (blockConvert A) ^ m *ᵥ (blockConvert A *ᵥ liftVec phiMinus v) := by
            rw [← Matrix.mulVec_mulVec]
        _ = (blockConvert A) ^ m *ᵥ liftVec phiMinus (realCast A *ᵥ v) := by
            rw [blockConvert_mulVec_lift A hA]
        _ = liftVec phiMinus (((realCast A) ^ m) *ᵥ (realCast A *ᵥ v)) :=
            ih (realCast A *ᵥ v)
        _ = liftVec phiMinus (((realCast A) ^ m * realCast A) *ᵥ v) := by
            rw [← Matrix.mulVec_mulVec]
        _ = liftVec phiMinus (((realCast A) ^ (m + 1)) *ᵥ v) := by
            rw [pow_succ]

theorem dot_psiMinus_lift {N : ℕ} (w : Fin N → ℝ) (j : Fin N) :
    dot (psiMinus j) (liftVec phiMinus w) = w j := by
  have hpp : (∑ s : Fin 2, phiMinus s * phiMinus s) = 1 := by
    simp [Fin.sum_univ_two, phiMinus, hsq_sqrt_two]
    norm_num
  have hmain : ∀ u : Fin N → ℝ,
      dot (liftVec phiMinus u) (liftVec phiMinus w) = ∑ i, u i * w i := by
    intro u
    unfold dot liftVec
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hinner : ∀ i : Fin N,
        (∑ s : Fin 2, u i * phiMinus s * (w i * phiMinus s)) = u i * w i := by
      intro i
      rw [show (∑ s : Fin 2, u i * phiMinus s * (w i * phiMinus s))
          = (u i * w i) * (∑ s : Fin 2, phiMinus s * phiMinus s) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring]
      rw [hpp, mul_one]
    simp only [hinner]
  have hpsi : psiMinus j = liftVec phiMinus (Pi.single j (1 : ℝ) : Fin N → ℝ) := rfl
  rw [hpsi, hmain]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eq12_diagonal_entry {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) (m : ℕ) (j : Fin N) :
    ((realCast A) ^ m) j j = dot (psiMinus j) ((blockConvert A) ^ m *ᵥ psiMinus j) := by
  have h := blockConvert_pow_mulVec_lift A hA m (Pi.single j (1 : ℝ))
  have hstep : (blockConvert A) ^ m *ᵥ psiMinus j =
      liftVec phiMinus (((realCast A) ^ m) *ᵥ (Pi.single j (1 : ℝ))) := h
  rw [hstep, dot_psiMinus_lift, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

theorem theorem2_path_difference {N : ℕ} (A : Matrix (Fin N) (Fin N) ℤ)
    (hA : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1)
    (hAsym : ∀ i j, A i j = A j i) (m : ℕ) (j : Fin N) :
    ((realCast A) ^ m) j j = doubledPathDiff ((blockConvert A) ^ m) j := by
  show ((realCast A) ^ m) j j =
    ((blockConvert A) ^ m) (0, j) (0, j) - ((blockConvert A) ^ m) (0, j) (1, j)
  rw [← phiMinus_bilinear_eq ((blockConvert A) ^ m) j
    (blockConvert_pow_symm A hAsym m (0, j) (1, j))
    (blockConvert_pow_diag_eq A hA m j).symm]
  exact eq12_diagonal_entry A hA m j

end Qatlib.Papers.BQPMixSparse06.MainResults
