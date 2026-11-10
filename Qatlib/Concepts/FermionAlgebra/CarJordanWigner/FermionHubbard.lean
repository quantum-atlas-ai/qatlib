/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.FermionDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 512000

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.FermionAlgebra.CarJordanWigner

private noncomputable def hubbardHamiltonian {n : ℕ} (t μ U : ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  ((hubbardJWTerms (n := n) t μ U).map fun term => term.1 • term.2).sum

private def hubbardTermCount (n : ℕ) : ℕ := n + 2 * (fermionPairs n).length

private noncomputable def hubbardTermVec {n : ℕ} (t μ U : ℂ) :
    Fin (hubbardTermCount n) → Matrix (Reg n) (Reg n) ℂ :=
  fun j =>
    let e : ℂ × Matrix (Reg n) (Reg n) ℂ :=
      (hubbardJWTerms (n := n) t μ U).getD j.val (0, 0)
    e.1 • e.2

private def hubbardCoeffSqBound (t μ U : ℂ) : ℝ :=
  max (Complex.normSq t) (max (Complex.normSq μ) (Complex.normSq U))

private noncomputable def hubbardWord {n : ℕ} (t μ U : ℂ) (τ : ℝ) (r : ℕ) :
    List (Matrix (Reg n) (Reg n) ℂ × ℕ) :=
  (List.replicate r
    (List.ofFn fun j : Fin (hubbardTermCount n) =>
      (HamiltonianEvolution (hubbardTermVec t μ U j) (τ / (r : ℝ)), j.val))).flatten

private noncomputable def wordInterp {n : ℕ} (word : List (Matrix (Reg n) (Reg n) ℂ × ℕ)) :
    Matrix (Reg n) (Reg n) ℂ :=
  word.foldl (fun V e => e.1 * V) 1

theorem upd_self {n : ℕ} (x : Reg n) (i : Fin n) (b : Bool) :
    Function.update x i b i = b := by
  rw [Function.update_apply, if_pos rfl]

theorem upd_eq_self {n : ℕ} {x : Reg n} {i : Fin n} {b : Bool} (h : x i = b) :
    Function.update x i b = x :=
  ((Function.eq_update_iff).mpr ⟨h, fun _ _ => rfl⟩).symm

theorem upd_upd_self {n : ℕ} (x : Reg n) (i : Fin n) (a b : Bool) :
    Function.update (Function.update x i a) i b = Function.update x i b :=
  Function.update_idem a b x

theorem neg_one_pow_mul_self (m : ℕ) : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
  rw [← pow_add, show m + m = 2 * m by ring, pow_mul]
  norm_num

theorem jwSign_eq {n : ℕ} (i : Fin n) (x : Reg n) :
    jwSign i x = (-1 : ℂ) ^ (∑ k : Fin n, if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0) := by
  unfold jwSign
  congr 1
  have himg : ((Finset.univ : Finset (Fin i)).image
      (fun j : Fin i => (Fin.castLE (Nat.le_of_lt i.isLt) j : Fin n)))
      = Finset.univ.filter (fun k : Fin n => (k : ℕ) < (i : ℕ)) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact j.isLt
    · intro hk
      exact ⟨⟨(k : ℕ), hk⟩, rfl⟩
  calc (∑ j : Fin i, if x (Fin.castLE (Nat.le_of_lt i.isLt) j) then 1 else 0)
      = ∑ k ∈ (Finset.univ : Finset (Fin i)).image
          (fun j : Fin i => (Fin.castLE (Nat.le_of_lt i.isLt) j : Fin n)),
          (if x k then 1 else 0) :=
        (Finset.sum_image
          (f := fun k : Fin n => (if x k then 1 else 0))
          (g := fun j : Fin i => (Fin.castLE (Nat.le_of_lt i.isLt) j : Fin n))
          ((Fin.castLE_injective (Nat.le_of_lt i.isLt)).injOn)).symm
    _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < (i : ℕ)),
          (if x k then 1 else 0) := by rw [himg]
    _ = ∑ k : Fin n, (if (k : ℕ) < (i : ℕ) then (if x k then 1 else 0) else 0) := by
        rw [Finset.sum_filter]

theorem jwSign_sq {n : ℕ} (i : Fin n) (x : Reg n) :
    jwSign i x * jwSign i x = 1 := by
  rw [jwSign_eq, neg_one_pow_mul_self]

private theorem jwSign_real {n : ℕ} (i : Fin n) (x : Reg n) :
    (starRingEnd ℂ) (jwSign i x) = jwSign i x := by
  rw [jwSign_eq, map_pow]
  congr 1
  simp

theorem ann_apply {n : ℕ} (i : Fin n) (y x : Reg n) :
    annihilation i y x = if x i ∧ y = Function.update x i false then jwSign i x else 0 := rfl

theorem cre_apply {n : ℕ} (i : Fin n) (y x : Reg n) :
    creation i y x = if ¬ x i ∧ y = Function.update x i true then jwSign i y else 0 := rfl

theorem num_apply {n : ℕ} (i : Fin n) (y x : Reg n) :
    numberOp i y x = if x = y ∧ x i then 1 else 0 := rfl

theorem creation_eq_conjTranspose {n : ℕ} (i : Fin n) :
    creation i = (annihilation i)ᴴ := by
  ext y x
  rw [Matrix.conjTranspose_apply, ann_apply, cre_apply]
  simp only [RCLike.star_def]
  by_cases hyi : y i = true
  · by_cases hx : x = Function.update y i false
    · have hxi : x i = false := by rw [hx, upd_self]
      have hyx : y = Function.update x i true := by rw [hx, upd_upd_self, upd_eq_self hyi]
      rw [if_pos ⟨by simp [hxi], hyx⟩, if_pos ⟨hyi, hx⟩, jwSign_real]
    · have hLneg : ¬(¬ x i ∧ y = Function.update x i true) := by
        rintro ⟨hne, hy'⟩
        by_cases hxi : x i = true
        · exact hne hxi
        · refine hx ?_
          rw [hy', upd_upd_self, upd_eq_self (by simpa using! hxi)]
      rw [if_neg hLneg, if_neg (fun h => hx h.2), map_zero]
  · rw [if_neg (fun h => hyi (by rw [h.2, upd_self])), if_neg (fun h => hyi h.1), map_zero]

theorem numberOp_eq {n : ℕ} (i : Fin n) :
    numberOp i = creation i * annihilation i := by
  ext y x
  rw [num_apply, Matrix.mul_apply]
  by_cases hxi : x i = true
  · rw [Finset.sum_eq_single (Function.update x i false)]
    · have hcondA : x i ∧ (Function.update x i false) = Function.update x i false :=
        ⟨hxi, rfl⟩
      rw [ann_apply i (Function.update x i false) x, if_pos hcondA,
        cre_apply i y _]
      have hzi : ¬ (Function.update x i false) i = true := by rw [upd_self]; simp
      by_cases hy : y = Function.update (Function.update x i false) i true
      · have hyx : y = x := by rw [hy, upd_upd_self, upd_eq_self hxi]
        have hcondL : x = y ∧ x i := ⟨hyx.symm, hxi⟩
        have hcondR : ¬ (Function.update x i false) i = true
            ∧ y = Function.update (Function.update x i false) i true := ⟨hzi, hy⟩
        rw [if_pos hcondL, if_pos hcondR, hyx, jwSign_sq]
      · have hcondR : ¬ (¬ (Function.update x i false) i = true
            ∧ y = Function.update (Function.update x i false) i true) :=
          fun h => hy h.2
        have hcondL : ¬ (x = y ∧ x i) := by
          intro h
          exact hy (by rw [← h.1, upd_upd_self, upd_eq_self hxi])
        rw [if_neg hcondR, zero_mul, if_neg hcondL]
    · intro z _ hz
      rw [ann_apply i z x, if_neg (fun h => hz h.2), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hsum : ∑ z : Reg n, creation i y z * annihilation i z x = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [ann_apply i z x, if_neg (fun h => absurd h.1 (by simp [hxi])), mul_zero]
    rw [hsum, if_neg (fun h => absurd h.2 (by simp [hxi]))]

theorem numberOp_idem {n : ℕ} (i : Fin n) :
    numberOp i * numberOp i = numberOp i := by
  ext y x
  rw [Matrix.mul_apply]
  by_cases hxi : x i = true
  · rw [Finset.sum_eq_single x]
    · rw [num_apply i x x]
      have hx : (if x = x ∧ x i then (1 : ℂ) else 0) = 1 := by
        rw [if_pos ⟨rfl, hxi⟩]
      rw [hx, mul_one]
    · intro z _ hz
      rw [num_apply i z x, if_neg (fun h => hz h.1.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hsum : ∑ z : Reg n, numberOp i y z * numberOp i z x = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [num_apply i z x, if_neg (fun h => absurd h.2 (by simp [hxi])), mul_zero]
    rw [hsum, num_apply i y x, if_neg (fun h => absurd h.2 (by simp [hxi]))]

private theorem relabel_one {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) :
    relabelGate e (1 : Matrix I I ℂ) = 1 :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_one

private theorem relabel_mul {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) (A B : Matrix I I ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_mul A B

private theorem relabel_smul {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) (c : ℂ) (A : Matrix I I ℂ) :
    relabelGate e (c • A) = c • relabelGate e A := by
  show Matrix.reindex e e (c • A) = c • Matrix.reindex e e A
  ext i j
  simp [Matrix.reindex_apply]

private theorem relabel_sum {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) {m : ℕ} (A : Fin m → Matrix I I ℂ) :
    relabelGate e (∑ j, A j) = ∑ j, relabelGate e (A j) := by
  show Matrix.reindex e e (∑ j, A j) = ∑ j, Matrix.reindex e e (A j)
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sum_apply]

private theorem relabel_sub {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) (A B : Matrix I I ℂ) :
    relabelGate e (A - B) = relabelGate e A - relabelGate e B :=
  (Matrix.reindexAlgEquiv ℂ ℂ e).map_sub A B

private theorem relabel_exp {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) (X : Matrix I I ℂ) :
    relabelGate e (NormedSpace.exp X) = NormedSpace.exp (relabelGate e X) := by
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap.continuous_of_finiteDimensional X

private theorem relabel_evolution {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) (H : Matrix I I ℂ) (τ : ℝ) :
    relabelGate e (HamiltonianEvolution H τ) = HamiltonianEvolution (relabelGate e H) τ := by
  unfold HamiltonianEvolution
  rw [relabel_exp, relabel_smul]

private theorem relabel_hermitian {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) {H : Matrix I I ℂ} (hH : H.IsHermitian) :
    (relabelGate e H).IsHermitian := by
  show (Matrix.reindex e e H)ᴴ = Matrix.reindex e e H
  rw [Matrix.conjTranspose_reindex, hH]

private theorem relabel_foldl {I K : Type*} [Fintype I] [DecidableEq I]
    [Fintype K] [DecidableEq K] (e : I ≃ K) :
    ∀ (w : List (Matrix I I ℂ × ℕ)) (V : Matrix I I ℂ),
      relabelGate e (w.foldl (fun W p => p.1 * W) V)
        = (w.map fun p => (relabelGate e p.1, p.2)).foldl (fun W p => p.1 * W)
            (relabelGate e V) := by
  intro w
  induction w with
  | nil => intro V; rfl
  | cons p ws ih =>
      intro V
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (p.1 * V), relabel_mul]

private theorem relabel_wordInterp {D n : ℕ} (e : Reg n ≃ Fin D)
    (w : List (Matrix (Reg n) (Reg n) ℂ × ℕ)) :
    relabelGate e (wordInterp w) = pfInterpret (w.map fun p => (relabelGate e p.1, p.2)) := by
  have h := relabel_foldl e w 1
  rw [relabel_one] at h
  exact h

private theorem numberOp_mul_apply {n : ℕ} (i j : Fin n) (y x : Reg n) :
    (numberOp i * numberOp j) y x = if x = y ∧ x i ∧ x j then (1 : ℂ) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hxj : x j = true
  · rw [Finset.sum_eq_single x]
    · rw [num_apply i y x, num_apply j x x]
      by_cases hxi : x i = true
      · have hc2 : x = x ∧ x j := ⟨rfl, hxj⟩
        rw [if_pos hc2, mul_one]
        by_cases hxy : x = y
        · have hc1 : x = y ∧ x i := ⟨hxy, hxi⟩
          have hcr : x = y ∧ x i ∧ x j := ⟨hxy, hxi, hxj⟩
          rw [if_pos hc1, if_pos hcr]
        · have hn1 : ¬(x = y ∧ x i) := fun h => hxy h.1
          have hnr : ¬(x = y ∧ x i ∧ x j) := fun h => hxy h.1
          rw [if_neg hn1, if_neg hnr]
      · have hc2 : x = x ∧ x j := ⟨rfl, hxj⟩
        have hn1 : ¬(x = y ∧ x i) := fun h => hxi h.2
        have hnr : ¬(x = y ∧ x i ∧ x j) := fun h => hxi h.2.1
        rw [if_neg hn1, if_pos hc2, mul_one, if_neg hnr]
    · intro z _ hz
      rw [num_apply j z x, if_neg (fun h => hz h.1.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hsum : ∑ z : Reg n, numberOp i y z * numberOp j z x = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [num_apply j z x, if_neg (fun h => hxj h.2), mul_zero]
    rw [hsum, if_neg (fun h => hxj h.2.2)]

private theorem numberOp_mul_comm {n : ℕ} (i j : Fin n) :
    numberOp i * numberOp j = numberOp j * numberOp i := by
  ext y x
  rw [numberOp_mul_apply, numberOp_mul_apply]
  by_cases h : x = y ∧ x i ∧ x j
  · rw [if_pos h, if_pos ⟨h.1, h.2.2, h.2.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.2, h'.2.1⟩)]

private theorem flatMap_length_le {α β : Type*} (f : α → List β) (K : ℕ)
    (hK : ∀ a, (f a).length ≤ K) :
    ∀ l : List α, (l.flatMap f).length ≤ l.length * K := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      have h1 : ((a :: l).flatMap f).length = (f a).length + (l.flatMap f).length := by
        rw [List.flatMap_cons, List.length_append]
      have h2 : (a :: l).length * K = l.length * K + K := by
        show (l.length + 1) * K = l.length * K + K
        rw [Nat.add_mul, Nat.one_mul]
      have h3 : (f a).length ≤ K := hK a
      rw [h1, h2]
      omega

private theorem fermionPairs_length_le (n : ℕ) : (fermionPairs n).length ≤ n * n := by
  have h := flatMap_length_le (fun i : Fin n =>
      (List.finRange n).filterMap fun j => if i < j then some (i, j) else none) n
    (fun _ => le_trans (List.length_filterMap_le _ _) (List.length_finRange).le)
    (List.finRange n)
  show ((List.finRange n).flatMap fun i : Fin n =>
      (List.finRange n).filterMap fun j => if i < j then some (i, j) else none).length ≤ n * n
  rwa [List.length_finRange] at h

private theorem hubbardTermCount_le (n : ℕ) : hubbardTermCount n ≤ 2 * (n + 1) * (n + 1) := by
  have h1 : (fermionPairs n).length ≤ n * n := fermionPairs_length_le n
  have h2 : 2 * (n + 1) * (n + 1) = 2 * (n * n) + 4 * n + 2 := by ring
  have h3 : hubbardTermCount n = n + 2 * (fermionPairs n).length := rfl
  rw [h2, h3]
  omega

private theorem hubbardJWTerms_length {n : ℕ} (t μ U : ℂ) :
    (hubbardJWTerms (n := n) t μ U).length = hubbardTermCount n := by
  simp only [hubbardJWTerms, List.length_append, List.length_map, List.length_finRange,
    hubbardTermCount]
  omega

private theorem sum_getD {α β : Type*} [AddCommMonoid β] (F : α → β) (d : α) :
    ∀ l : List α, ∑ j : Fin l.length, F (l.getD (j : ℕ) d) = (l.map F).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, List.getD_cons_zero,
        Fin.val_succ, List.getD_cons_succ, List.map_cons, List.sum_cons]
      exact congrArg _ ih
private def finCastEq {m k : ℕ} (h : m = k) : Fin m ≃ Fin k where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun j := ⟨j.val, h.symm ▸ j.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem hubbardHamiltonian_sum {n : ℕ} (t μ U : ℂ) :
    hubbardHamiltonian (n := n) t μ U
      = ∑ j : Fin (hubbardTermCount n), hubbardTermVec (n := n) t μ U j := by
  have hlen : (hubbardJWTerms (n := n) t μ U).length = hubbardTermCount n :=
    hubbardJWTerms_length t μ U
  have key := sum_getD (fun term : ℂ × Matrix (Reg n) (Reg n) ℂ => term.1 • term.2) (0, 0)
    (hubbardJWTerms (n := n) t μ U)
  rw [hubbardHamiltonian, ← key]
  exact Fintype.sum_equiv (finCastEq hlen)
    (fun j : Fin (hubbardJWTerms (n := n) t μ U).length =>
      ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1
        • ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2)
    (fun j : Fin (hubbardTermCount n) => hubbardTermVec (n := n) t μ U j)
    (fun _ => rfl)

private theorem numberOp_herm {n : ℕ} (i : Fin n) : (numberOp i).IsHermitian := by
  show (numberOp i)ᴴ = numberOp i
  ext y x
  rw [Matrix.conjTranspose_apply, num_apply i x y, num_apply i y x]
  simp only [RCLike.star_def]
  by_cases h : y = x ∧ y i
  · have hl : (if y = x ∧ y i then (1 : ℂ) else 0) = 1 := if_pos h
    rw [hl, map_one, if_pos ⟨h.1.symm, by rw [← h.1]; exact h.2⟩]
  · have hl : (if y = x ∧ y i then (1 : ℂ) else 0) = 0 := if_neg h
    rw [hl, map_zero, if_neg (fun h' => h ⟨h'.1.symm, by rw [← h'.1]; exact h'.2⟩)]

private theorem cre_conjTranspose {n : ℕ} (i : Fin n) :
    (creation i)ᴴ = annihilation i := by
  rw [creation_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

private theorem numberOp_mul_herm {n : ℕ} (i j : Fin n) :
    (numberOp i * numberOp j).IsHermitian := by
  show (numberOp i * numberOp j)ᴴ = numberOp i * numberOp j
  rw [Matrix.conjTranspose_mul, (numberOp_herm i).eq, (numberOp_herm j).eq,
    numberOp_mul_comm]

private theorem hop_herm {n : ℕ} (i j : Fin n) :
    (creation i * annihilation j + creation j * annihilation i).IsHermitian := by
  show (creation i * annihilation j + creation j * annihilation i)ᴴ
      = creation i * annihilation j + creation j * annihilation i
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ← creation_eq_conjTranspose j, cre_conjTranspose i, ← creation_eq_conjTranspose i,
    cre_conjTranspose j, add_comm]

private theorem isSelfAdjoint_of_im_zero {c : ℂ} (h : c.im = 0) : IsSelfAdjoint c := by
  show (starRingEnd ℂ) c = c
  exact Complex.conj_eq_iff_im.mpr h

private theorem mem_terms_cases {n : ℕ} (t μ U : ℂ) {c : ℂ}
    {M : Matrix (Reg n) (Reg n) ℂ} (h : (c, M) ∈ hubbardJWTerms (n := n) t μ U) :
    (∃ i : Fin n, c = μ ∧ M = numberOp i)
      ∨ (∃ i j : Fin n, c = U ∧ M = numberOp i * numberOp j)
      ∨ ∃ i j : Fin n, c = t
          ∧ M = creation i * annihilation j + creation j * annihilation i := by
  rw [hubbardJWTerms] at h
  rcases List.mem_append.mp h with h1 | h4
  · rcases List.mem_append.mp h1 with hA | hB
    · rw [List.mem_map] at hA
      obtain ⟨i, _, hA⟩ := hA
      cases hA
      exact Or.inl ⟨i, rfl, rfl⟩
    · rw [List.mem_map] at hB
      obtain ⟨p, _, hB⟩ := hB
      cases hB
      exact Or.inr (Or.inl ⟨p.1, p.2, rfl, rfl⟩)
  · rw [List.mem_map] at h4
    obtain ⟨p, _, h4⟩ := h4
    cases h4
    exact Or.inr (Or.inr ⟨p.1, p.2, rfl, rfl⟩)

private theorem getD_mem' {α : Type*} (l : List α) (d : α) {n : ℕ} (h : n < l.length) :
    l.getD n d ∈ l := by
  rw [List.getD_eq_getElem l d h]
  exact List.getElem_mem h

private theorem term_mem {n : ℕ} (t μ U : ℂ) (j : Fin (hubbardTermCount n)) :
    (hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0) ∈ hubbardJWTerms (n := n) t μ U :=
  getD_mem' _ _ (by rw [hubbardJWTerms_length]; exact j.isLt)

private theorem term_herm {n : ℕ} (t μ U : ℂ) (ht : t.im = 0) (hμ : μ.im = 0)
    (hU : U.im = 0) (j : Fin (hubbardTermCount n)) :
    (hubbardTermVec (n := n) t μ U j).IsHermitian := by
  have hmem := term_mem t μ U j
  show (((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1
      • ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2).IsHermitian
  rcases mem_terms_cases t μ U hmem with ⟨i, hci, hMi⟩ | ⟨i, j', hci, hMi⟩
    | ⟨i, j', hci, hMi⟩
  · have hc : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1 = μ := hci
    have hM : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2 = numberOp i := hMi
    rw [hc, hM]; exact (numberOp_herm i).smul (isSelfAdjoint_of_im_zero hμ)
  · have hc : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1 = U := hci
    have hM : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2
        = numberOp i * numberOp j' := hMi
    rw [hc, hM]; exact (numberOp_mul_herm i j').smul (isSelfAdjoint_of_im_zero hU)
  · have hc : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1 = t := hci
    have hM : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2
        = creation i * annihilation j' + creation j' * annihilation i := hMi
    rw [hc, hM]; exact (hop_herm i j').smul (isSelfAdjoint_of_im_zero ht)

private theorem sum_smul_herm_list {n : ℕ} :
    ∀ l : List (ℂ × Matrix (Reg n) (Reg n) ℂ),
      (∀ p ∈ l, (p.1 • p.2).IsHermitian) →
      ((l.map fun term : ℂ × Matrix (Reg n) (Reg n) ℂ => term.1 • term.2).sum).IsHermitian := by
  intro l
  induction l with
  | nil => intro _; show (0 : Matrix (Reg n) (Reg n) ℂ).IsHermitian; simp [Matrix.IsHermitian]
  | cons p l ih =>
      intro hall
      show (p.1 • p.2
          + ((l.map fun term : ℂ × Matrix (Reg n) (Reg n) ℂ => term.1 • term.2).sum)).IsHermitian
      exact (hall p (by simp)).add (ih (fun q hq => hall q (by simp [hq])))

private theorem hubbardHamiltonian_herm {n : ℕ} (t μ U : ℂ) (ht : t.im = 0) (hμ : μ.im = 0)
    (hU : U.im = 0) : (hubbardHamiltonian (n := n) t μ U).IsHermitian := by
  rw [hubbardHamiltonian]
  refine sum_smul_herm_list _ fun p hp => ?_
  rcases mem_terms_cases t μ U hp with ⟨i, hci, hMi⟩ | ⟨i, j', hci, hMi⟩
    | ⟨i, j', hci, hMi⟩
  · rw [hci, hMi]; exact (numberOp_herm i).smul (isSelfAdjoint_of_im_zero hμ)
  · rw [hci, hMi]; exact (numberOp_mul_herm i j').smul (isSelfAdjoint_of_im_zero hU)
  · rw [hci, hMi]; exact (hop_herm i j').smul (isSelfAdjoint_of_im_zero ht)

private theorem numberOp_norm_le {n : ℕ} (i : Fin n) : ‖numberOp i‖ ≤ 1 := by
  have h1 : ‖numberOp i‖ * ‖numberOp i‖ = ‖numberOp i‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, (numberOp_herm i).eq, numberOp_idem i]
  have h2 : 0 ≤ ‖numberOp i‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖numberOp i‖ - 1)]

private theorem ann_norm_le {n : ℕ} (i : Fin n) : ‖annihilation i‖ ≤ 1 := by
  have h1 : ‖annihilation i‖ * ‖annihilation i‖ = ‖numberOp i‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← creation_eq_conjTranspose i,
      numberOp_eq i]
  have h2 : 0 ≤ ‖annihilation i‖ := norm_nonneg _
  have h3 : ‖numberOp i‖ ≤ 1 := numberOp_norm_le i
  nlinarith [sq_nonneg (‖annihilation i‖ - 1)]

private theorem cre_norm_le {n : ℕ} (i : Fin n) : ‖creation i‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_conjTranspose (creation i), cre_conjTranspose]
  exact ann_norm_le i

private theorem hop_norm_le {n : ℕ} (i j : Fin n) :
    ‖creation i * annihilation j + creation j * annihilation i‖ ≤ 2 := by
  have h1 : ‖creation i * annihilation j‖ ≤ 1 := by
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    have hxy : ‖creation i‖ * ‖annihilation j‖ ≤ 1 * 1 :=
      mul_le_mul (cre_norm_le i) (ann_norm_le j) (norm_nonneg _) (by norm_num)
    linarith
  have h2 : ‖creation j * annihilation i‖ ≤ 1 := by
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    have hxy : ‖creation j‖ * ‖annihilation i‖ ≤ 1 * 1 :=
      mul_le_mul (cre_norm_le j) (ann_norm_le i) (norm_nonneg _) (by norm_num)
    linarith
  have h3 := norm_add_le (creation i * annihilation j) (creation j * annihilation i)
  linarith

private theorem nummul_norm_le {n : ℕ} (i j : Fin n) :
    ‖numberOp i * numberOp j‖ ≤ 2 := by
  refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
  have hxy : ‖numberOp i‖ * ‖numberOp j‖ ≤ 1 * 1 :=
    mul_le_mul (numberOp_norm_le i) (numberOp_norm_le j) (norm_nonneg _) (by norm_num)
  linarith

private theorem norm_sq_eq {c : ℂ} : ‖c‖ * ‖c‖ = Complex.normSq c := by
  rw [Complex.normSq_eq_norm_sq, pow_two]

private theorem coeff_sq_le {t μ U c : ℂ} (h : c = t ∨ c = μ ∨ c = U) :
    ‖c‖ * ‖c‖ ≤ hubbardCoeffSqBound t μ U := by
  rcases h with rfl | rfl | rfl
  · rw [norm_sq_eq]; exact le_max_left _ _
  · rw [norm_sq_eq]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [norm_sq_eq]; exact le_trans (le_max_right _ _) (le_max_right _ _)

private theorem term_norm_pair {n : ℕ} (t μ U : ℂ) (j k : Fin (hubbardTermCount n)) :
    ‖hubbardTermVec (n := n) t μ U j‖ * ‖hubbardTermVec (n := n) t μ U k‖
      ≤ 4 * hubbardCoeffSqBound t μ U := by
  have hdecomp : ∀ j : Fin (hubbardTermCount n), ∃ c : ℂ, ∃ M : Matrix (Reg n) (Reg n) ℂ,
      hubbardTermVec (n := n) t μ U j = c • M ∧ (c = t ∨ c = μ ∨ c = U) ∧ ‖M‖ ≤ 2 := by
    intro j
    have hmem := term_mem t μ U j
    rcases mem_terms_cases t μ U hmem with ⟨i, hci, hMi⟩ | ⟨i, j', hci, hMi⟩
      | ⟨i, j', hci, hMi⟩
    · refine ⟨μ, numberOp i, ?_, Or.inr (Or.inl rfl), le_trans (numberOp_norm_le i) (by norm_num)⟩
      have hc : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1 = μ := hci
      have hM : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2 = numberOp i := hMi
      show ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1
          • ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2 = μ • numberOp i
      rw [hc, hM]
    · refine ⟨U, numberOp i * numberOp j', ?_, Or.inr (Or.inr rfl), nummul_norm_le i j'⟩
      have hc : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1 = U := hci
      have hM : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2
          = numberOp i * numberOp j' := hMi
      show ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1
          • ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2
          = U • (numberOp i * numberOp j')
      rw [hc, hM]
    · refine ⟨t, creation i * annihilation j' + creation j' * annihilation i, ?_, Or.inl rfl,
        hop_norm_le i j'⟩
      have hc : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1 = t := hci
      have hM : ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2
          = creation i * annihilation j' + creation j' * annihilation i := hMi
      show ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).1
          • ((hubbardJWTerms (n := n) t μ U).getD (j : ℕ) (0, 0)).2
          = t • (creation i * annihilation j' + creation j' * annihilation i)
      rw [hc, hM]
  obtain ⟨c, M, hjm, hc, hM⟩ := hdecomp j
  obtain ⟨c', M', hkm, hc', hM'⟩ := hdecomp k
  rw [hjm, hkm, norm_smul, norm_smul]
  have hs := coeff_sq_le hc
  have hs' := coeff_sq_le hc'
  have h0 : 0 ≤ ‖c‖ := norm_nonneg _
  have h0' : 0 ≤ ‖c'‖ := norm_nonneg _
  have hxy : ‖c‖ * ‖c'‖ ≤ hubbardCoeffSqBound t μ U := by
    nlinarith [sq_nonneg (‖c‖ - ‖c'‖), hs, hs']
  have h1 : ‖c‖ * ‖M‖ ≤ ‖c‖ * 2 := mul_le_mul_of_nonneg_left hM h0
  have h1' : ‖c'‖ * ‖M'‖ ≤ ‖c'‖ * 2 := mul_le_mul_of_nonneg_left hM' h0'
  have h2 : (‖c‖ * ‖M‖) * (‖c'‖ * ‖M'‖) ≤ ‖c‖ * 2 * (‖c'‖ * 2) :=
    mul_le_mul h1 h1' (mul_nonneg h0' (norm_nonneg M')) (mul_nonneg h0 (by norm_num))
  have h3 : ‖c‖ * 2 * (‖c'‖ * 2) = 4 * (‖c‖ * ‖c'‖) := by ring
  refine le_trans h2 ?_
  rw [h3]
  exact mul_le_mul_of_nonneg_left hxy (by norm_num)

private theorem pfComm_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) : ‖pfComm A B‖ ≤ 2 * (‖A‖ * ‖B‖) := by
  have h1 := norm_sub_le (A * B) (B * A)
  have h2 := Matrix.l2_opNorm_mul A B
  have h3 := Matrix.l2_opNorm_mul B A
  show ‖A * B - B * A‖ ≤ 2 * (‖A‖ * ‖B‖)
  nlinarith

private theorem pfCommSum_pair_le {D m : ℕ} (G : Fin m → Operator D) (C : ℝ)
    (h : ∀ j k, ‖pfComm (G j) (G k)‖ ≤ C) :
    2 * pfCommutatorSum G ≤ C * (m : ℝ) ^ 2 := by
  have hdiag : ∀ j : Fin m, ‖pfComm (G j) (G j)‖ = 0 := by
    intro j
    show ‖G j * G j - G j * G j‖ = 0
    rw [sub_self, norm_zero]
  have hsym : ∀ j k : Fin m, ‖pfComm (G j) (G k)‖ = ‖pfComm (G k) (G j)‖ := by
    intro j k
    show ‖G j * G k - G k * G j‖ = ‖G k * G j - G j * G k‖
    have hswap : (G k * G j - G j * G k : Operator D) = -(G j * G k - G k * G j) :=
      (neg_sub (G j * G k) (G k * G j)).symm
    rw [hswap, norm_neg]
  have hsplit : ∀ j k : Fin m, ‖pfComm (G j) (G k)‖
      = (if j < k then ‖pfComm (G j) (G k)‖ else 0) + (if k < j then ‖pfComm (G j) (G k)‖ else 0)
        + (if j = k then ‖pfComm (G j) (G k)‖ else 0) := by
    intro j k
    rcases lt_trichotomy j k with hlt | heq | hgt
    · rw [if_pos hlt, if_neg (lt_asymm hlt), if_neg (ne_of_lt hlt), add_zero, add_zero]
    · subst heq
      rw [hdiag j, if_neg (lt_irrefl j)]
      simp
    · rw [if_neg (lt_asymm hgt), if_pos hgt, if_neg (ne_of_gt hgt), zero_add, add_zero]
  have hS3 : ∑ j, ∑ k, (if j = k then ‖pfComm (G j) (G k)‖ else 0) = 0 := by
    have hinner : ∀ j : Fin m, ∑ k, (if j = k then ‖pfComm (G j) (G k)‖ else 0)
        = ‖pfComm (G j) (G j)‖ := by
      intro j
      rw [Finset.sum_ite_eq Finset.univ j (fun k => ‖pfComm (G j) (G k)‖)]
      simp
    rw [Finset.sum_congr rfl fun j _ => hinner j]
    simp [hdiag]
  have hS2 : ∑ j, ∑ k, (if k < j then ‖pfComm (G j) (G k)‖ else 0) = pfCommutatorSum G := by
    have hp : ∀ j k : Fin m, (if k < j then ‖pfComm (G j) (G k)‖ else 0)
        = (if k < j then ‖pfComm (G k) (G j)‖ else 0) := by
      intro j k
      by_cases h : k < j
      · rw [if_pos h, if_pos h, hsym j k]
      · rw [if_neg h, if_neg h]
    calc ∑ j, ∑ k, (if k < j then ‖pfComm (G j) (G k)‖ else 0)
        = ∑ j, ∑ k, (if k < j then ‖pfComm (G k) (G j)‖ else 0) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hp j k
      _ = pfCommutatorSum G := by rw [Finset.sum_comm]; rfl
  have hdist : ∀ (f g h : Fin m → Fin m → ℝ),
      (∑ j, ∑ k, f j k) + (∑ j, ∑ k, g j k) + (∑ j, ∑ k, h j k)
        = ∑ j, ∑ k, (f j k + g j k + h j k) := by
    intro f g h
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have h2S : pfCommutatorSum G + pfCommutatorSum G = ∑ j, ∑ k, ‖pfComm (G j) (G k)‖ := by
    have hA : pfCommutatorSum G
        = ∑ j, ∑ k, (if j < k then ‖pfComm (G j) (G k)‖ else 0) := rfl
    nth_rewrite 1 [hA]
    rw [← hS2]
    rw [show ((∑ j, ∑ k, (if j < k then ‖pfComm (G j) (G k)‖ else 0))
        + ∑ j, ∑ k, (if k < j then ‖pfComm (G j) (G k)‖ else 0) : ℝ)
        = ((∑ j, ∑ k, (if j < k then ‖pfComm (G j) (G k)‖ else 0))
          + ∑ j, ∑ k, (if k < j then ‖pfComm (G j) (G k)‖ else 0))
        + ∑ j, ∑ k, (if j = k then ‖pfComm (G j) (G k)‖ else 0) from by
      rw [hS3]; ring]
    rw [hdist (fun j k => (if j < k then ‖pfComm (G j) (G k)‖ else 0))
      (fun j k => (if k < j then ‖pfComm (G j) (G k)‖ else 0))
      (fun j k => (if j = k then ‖pfComm (G j) (G k)‖ else 0))]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => (hsplit j k).symm
  have hbound : (∑ j, ∑ k, ‖pfComm (G j) (G k)‖ : ℝ) ≤ C * (m : ℝ) ^ 2 := by
    calc (∑ j, ∑ k, ‖pfComm (G j) (G k)‖ : ℝ)
        ≤ ∑ j : Fin m, ∑ k : Fin m, C :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h j k
      _ = (m : ℝ) * ((m : ℝ) * C) := by simp
      _ = C * (m : ℝ) ^ 2 := by ring
  nlinarith [h2S, hbound]

private theorem hubbardWord_length {n : ℕ} (t μ U : ℂ) (τ : ℝ) (r : ℕ) :
    (hubbardWord (n := n) t μ U τ r).length = r * hubbardTermCount n := by
  rw [hubbardWord, List.length_flatten, List.map_replicate, List.sum_replicate,
    Nat.nsmul_eq_mul, List.length_ofFn]

private theorem map_relabel_hubbardWord {n : ℕ} (t μ U : ℂ) (τ : ℝ) (r : ℕ)
    (e : Reg n ≃ Fin (2 ^ n)) :
    (hubbardWord (n := n) t μ U τ r).map (fun p => (relabelGate e p.1, p.2))
      = pfFamilyWord (fun j => relabelGate e (hubbardTermVec (n := n) t μ U j)) τ r := by
  have hfun : (fun j : Fin (hubbardTermCount n) =>
        (fun p => (relabelGate e p.1, p.2))
          (HamiltonianEvolution (hubbardTermVec (n := n) t μ U j) (τ / (r : ℝ)), (j : ℕ)))
      = fun j : Fin (hubbardTermCount n) =>
        (HamiltonianEvolution (relabelGate e (hubbardTermVec (n := n) t μ U j)) (τ / (r : ℝ)),
          (j : ℕ)) := by
    funext j
    show (relabelGate e (HamiltonianEvolution (hubbardTermVec (n := n) t μ U j) (τ / (r : ℝ))),
        (j : ℕ))
      = (HamiltonianEvolution (relabelGate e (hubbardTermVec (n := n) t μ U j)) (τ / (r : ℝ)),
        (j : ℕ))
    rw [relabel_evolution]
  rw [hubbardWord, List.map_flatten, List.map_replicate, List.map_ofFn, Function.comp_def,
    hfun, pfFamilyWord]

private theorem relabel_wordInterp_hubbardWord {n : ℕ} (t μ U : ℂ) (τ : ℝ) (r : ℕ)
    (e : Reg n ≃ Fin (2 ^ n)) :
    relabelGate e (wordInterp (hubbardWord (n := n) t μ U τ r))
      = pfFamily (fun j => relabelGate e (hubbardTermVec (n := n) t μ U j)) τ r := by
  rw [relabel_wordInterp, map_relabel_hubbardWord, pfFamily]

private theorem sum_relabel_terms {n : ℕ} (t μ U : ℂ) (e : Reg n ≃ Fin (2 ^ n)) :
    ∑ j : Fin (hubbardTermCount n), relabelGate e (hubbardTermVec (n := n) t μ U j)
      = relabelGate e (hubbardHamiltonian (n := n) t μ U) := by
  rw [hubbardHamiltonian_sum, relabel_sum]

private theorem filter_none_length {α : Type*} (p : α → Bool) :
    ∀ {l : List α}, (∀ a ∈ l, p a = false) → (l.filter p).length = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
      intro h
      rw [List.filter_cons_of_neg (by simp [h a (by simp)])]
      exact ih (fun b hb => h b (by simp [hb]))

private theorem filter_val_length {M : Type*} :
    ∀ (m : ℕ) (X : Fin m → M) (v : Fin m → ℕ), Function.Injective v → ∀ j : Fin m,
      ((List.ofFn fun k : Fin m => (X k, v k)).filter
        fun e => decide (e.2 = v j)).length = 1 := by
  intro m
  induction m with
  | zero => intro X v _ j; exact j.elim0
  | succ m ih =>
      intro X v hv j
      rw [List.ofFn_succ]
      induction j using Fin.cases with
      | zero =>
          rw [List.filter_cons_of_pos (by simp), List.length_cons]
          have hnil : (List.filter (fun e => decide (e.2 = v (0 : Fin (m + 1))))
              (List.ofFn fun i : Fin m => (X ((i : Fin m).succ : Fin (m + 1)),
                v ((i : Fin m).succ : Fin (m + 1))))).length = 0 := by
            apply filter_none_length
            intro a ha
            rw [List.mem_ofFn] at ha
            obtain ⟨k, rfl⟩ := ha
            have hvk : ¬(v ((k : Fin m).succ : Fin (m + 1)) = v (0 : Fin (m + 1))) := by
              intro hh
              have h2 := hv hh
              simp at h2
            simp [hvk]
          linarith
      | succ j' =>
          rw [List.filter_cons_of_neg (by
            intro hcontra
            simp only [decide_eq_true_eq] at hcontra
            have h2 := hv hcontra
            have h3 := congrArg Fin.val h2
            simp only [Fin.val_zero, Fin.val_succ] at h3
            omega)]
          exact ih (fun k => X ((k : Fin m).succ : Fin (m + 1)))
            (fun k => v ((k : Fin m).succ : Fin (m + 1)))
            (hv.comp (Fin.succ_injective m)) j'

private theorem filter_flatten_replicate_length {α : Type*} (p : α → Bool) (b : List α) :
    ∀ r : ℕ, ((List.replicate r b).flatten.filter p).length = r * (b.filter p).length := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.flatten_cons, List.filter_append, List.length_append, ih]
      ring

private theorem hubbardWord_filter_length {n : ℕ} (t μ U : ℂ) (τ : ℝ) (r : ℕ)
    (j : Fin (hubbardTermCount n)) :
    ((hubbardWord (n := n) t μ U τ r).filter fun e => decide (e.2 = (j : ℕ))).length = r := by
  have h1 := filter_flatten_replicate_length
    (fun e => decide (e.2 = (j : ℕ)))
    (List.ofFn fun k : Fin (hubbardTermCount n) =>
      (HamiltonianEvolution (hubbardTermVec (n := n) t μ U k) (τ / (r : ℝ)), (k : ℕ))) r
  rw [hubbardWord, h1, filter_val_length _ (fun k =>
      HamiltonianEvolution (hubbardTermVec (n := n) t μ U k) (τ / (r : ℝ)))
    (fun k => (k : ℕ)) Fin.val_injective j]
  simp

private theorem hubbardWord_mem {n : ℕ} (t μ U : ℂ) (τ : ℝ) (r : ℕ)
    {E : Matrix (Reg n) (Reg n) ℂ × ℕ} (he : E ∈ hubbardWord (n := n) t μ U τ r) :
    ∃ j : Fin (hubbardTermCount n),
      E.1 = HamiltonianEvolution (hubbardTermVec (n := n) t μ U j) (τ / (r : ℝ)) := by
  rw [hubbardWord, List.mem_flatten] at he
  obtain ⟨seg, hseg, heseg⟩ := he
  rw [List.mem_replicate] at hseg
  obtain ⟨_, hseg⟩ := hseg
  rw [hseg, List.mem_ofFn] at heseg
  obtain ⟨j, rfl⟩ := heseg
  exact ⟨j, rfl⟩

theorem g2 : ∀ (n : ℕ) (t μ U : ℂ) (τ ε : ℝ),
    t.im = 0 → μ.im = 0 → U.im = 0 → 0 < ε →

  (hubbardHamiltonian (n := n) t μ U).IsHermitian ∧

  (hubbardHamiltonian (n := n) t μ U = ∑ j : Fin (hubbardTermCount n), hubbardTermVec (n := n) t μ U j) ∧

  (∃ r : ℕ, 1 ≤ r ∧
    ‖wordInterp (hubbardWord (n := n) t μ U τ r)
        - HamiltonianEvolution (hubbardHamiltonian (n := n) t μ U) τ‖ ≤ ε
      ∧ ((hubbardWord (n := n) t μ U τ r).length : ℝ)
        ≤ 16 * ((n : ℝ) + 1) ^ 6
            * (1 + τ ^ 2 * hubbardCoeffSqBound t μ U / ε)
      ∧ ((2 * (n + 1) * (n + 1) * (hubbardWord (n := n) t μ U τ r).length : ℕ) : ℝ)
        ≤ 32 * ((n : ℝ) + 1) ^ 8
            * (1 + τ ^ 2 * hubbardCoeffSqBound t μ U / ε)
      ∧ ((4 * (n + 1) * (n + 1) : ℕ) : ℝ)
        ≤ 16 * ((n : ℝ) + 1) ^ 2
            * (1 + τ ^ 2 * hubbardCoeffSqBound t μ U / ε)) ∧

  (∀ r : ℕ, 1 ≤ r →
    (∀ e ∈ hubbardWord (n := n) t μ U τ r, ∃ j : Fin (hubbardTermCount n),
        e.1 = HamiltonianEvolution (hubbardTermVec (n := n) t μ U j) (τ / (r : ℝ)))
      ∧ ∀ j : Fin (hubbardTermCount n),
          ((hubbardWord (n := n) t μ U τ r).filter (fun e => e.2 = j.val)).length = r) := by
  intro n t μ U τ ε ht hμ hU hε
  refine ⟨hubbardHamiltonian_herm t μ U ht hμ hU, hubbardHamiltonian_sum t μ U, ?_, ?_⟩
  · have hC0 : (0 : ℝ) ≤ hubbardCoeffSqBound t μ U :=
      le_trans (Complex.normSq_nonneg t) (le_max_left _ _)
    have hTC : (0 : ℝ) ≤ τ ^ 2 * hubbardCoeffSqBound t μ U :=
      mul_nonneg (sq_nonneg τ) hC0
    have hm : (hubbardTermCount n : ℝ) ≤ 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1) := by
      exact_mod_cast hubbardTermCount_le n
    have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast (by omega : 1 ≤ n + 1)
    have hM0 : (0 : ℝ) ≤ (hubbardTermCount n : ℝ) := by positivity
    have hm3 : (hubbardTermCount n : ℝ) ^ 3 ≤ 8 * ((n : ℝ) + 1) ^ 6 := by
      rw [pow_three]
      have h2a : (hubbardTermCount n : ℝ) * (hubbardTermCount n : ℝ)
          ≤ (2 * ((n : ℝ) + 1) * ((n : ℝ) + 1))
            * (2 * ((n : ℝ) + 1) * ((n : ℝ) + 1)) :=
        mul_le_mul hm hm hM0 (mul_nonneg (by positivity) (by positivity))
      have h2 : (hubbardTermCount n : ℝ) * ((hubbardTermCount n : ℝ)
          * (hubbardTermCount n : ℝ))
          ≤ (2 * ((n : ℝ) + 1) * ((n : ℝ) + 1))
            * ((2 * ((n : ℝ) + 1) * ((n : ℝ) + 1))
              * (2 * ((n : ℝ) + 1) * ((n : ℝ) + 1))) :=
        mul_le_mul hm h2a (mul_nonneg hM0 hM0) (mul_nonneg (by positivity) (by positivity))
      have hR : (2 * ((n : ℝ) + 1) * ((n : ℝ) + 1))
            * ((2 * ((n : ℝ) + 1) * ((n : ℝ) + 1))
              * (2 * ((n : ℝ) + 1) * ((n : ℝ) + 1)))
          = 8 * ((n : ℝ) + 1) ^ 6 := by ring
      linarith
    have hG : ∀ j : Fin (hubbardTermCount n),
        (relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j)).IsHermitian :=
      fun j => relabel_hermitian _ (term_herm t μ U ht hμ hU j)
    have hpair : ∀ j k : Fin (hubbardTermCount n),
        ‖relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j)‖
          * ‖relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U k)‖
          ≤ 4 * hubbardCoeffSqBound t μ U := by
      intro j k
      rw [l2_norm_relabelGate, l2_norm_relabelGate]
      exact term_norm_pair t μ U j k
    have hcomm : ∀ j k : Fin (hubbardTermCount n),
        ‖pfComm (relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j))
            (relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U k))‖
          ≤ 8 * hubbardCoeffSqBound t μ U := by
      intro j k
      have hn := pfComm_norm_le (I := Fin (2 ^ n))
        (relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j))
        (relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U k))
      have hp := hpair j k
      linarith
    have hS2b := pfCommSum_pair_le
      (fun j => relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j))
      (8 * hubbardCoeffSqBound t μ U) hcomm
    have hS : pfCommutatorSum
        (fun j => relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j))
        ≤ 4 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 := by
      nlinarith [hS2b]
    have hxle : 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε
        ≤ ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊
              + 1 : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil
        (2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε)
      have h2 : ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2
            / ε⌉₊ : ℕ) : ℝ) ≤ ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
            * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega)
      linarith
    have hrpos : (0 : ℝ) < ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
          * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < ⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
        * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)

    have hcastL : ((hubbardWord (n := n) t μ U τ (⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
            * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)).length : ℝ)
        = ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊
              + 1 : ℕ) : ℝ) * (hubbardTermCount n : ℝ) := by
      rw [hubbardWord_length t μ U τ]; push_cast; ring
    have hceil : ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2
            / ε⌉₊ + 1 : ℕ) : ℝ)
        ≤ 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε + 2 := by
      have hxnn : (0 : ℝ) ≤ 2 * τ ^ 2 * hubbardCoeffSqBound t μ U
            * (hubbardTermCount n : ℝ) ^ 2 / ε :=
        div_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0) (sq_nonneg _)) hε.le
      have h1 := Nat.ceil_lt_add_one hxnn
      have h2 : ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2
            / ε⌉₊ : ℕ) : ℝ) + 1 = ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
            * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; ring
      linarith
    have hlenR : ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2
            / ε⌉₊ + 1 : ℕ) : ℝ) * (hubbardTermCount n : ℝ)
        ≤ 16 * ((n : ℝ) + 1) ^ 6 * (1 + τ ^ 2 * hubbardCoeffSqBound t μ U / ε) := by
      have hstep : ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2
              / ε⌉₊ + 1 : ℕ) : ℝ) * (hubbardTermCount n : ℝ)
          ≤ (2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε + 2)
            * (hubbardTermCount n : ℝ) :=
        mul_le_mul_of_nonneg_right hceil hM0
      have heq : (2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε + 2)
          * (hubbardTermCount n : ℝ)
          = 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 3 / ε
            + 2 * (hubbardTermCount n : ℝ) := by ring
      have h1 : 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 3
          ≤ 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (8 * ((n : ℝ) + 1) ^ 6) :=
        mul_le_mul_of_nonneg_left hm3 (by positivity)
      have h1' : 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 3 / ε
          ≤ (2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (8 * ((n : ℝ) + 1) ^ 6)) / ε := by
        rw [div_le_iff₀ hε]
        field_simp
        linarith
      have h2 : (2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (8 * ((n : ℝ) + 1) ^ 6)) / ε
          ≤ 16 * ((n : ℝ) + 1) ^ 6 * (τ ^ 2 * hubbardCoeffSqBound t μ U / ε) := by
        rw [div_le_iff₀ hε]
        field_simp
        linarith
      have hq4 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := by
        have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := hN1
        have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hx]
        have h4 : ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 4 := by ring
        rw [← h4]
        nlinarith [h2, sq_nonneg (((n : ℝ) + 1) ^ 2)]
      have hq2 : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 6 := by
        nlinarith [hq4, sq_nonneg ((n : ℝ) + 1)]
      have hq6 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 6 := by positivity
      have h3 : 2 * (hubbardTermCount n : ℝ) ≤ 16 * ((n : ℝ) + 1) ^ 6 := by
        nlinarith [hm, hq2, hq6]
      refine le_trans (le_trans hstep ?_) (le_refl _)
      rw [heq]
      nlinarith [h1', h2, h3]
    refine ⟨⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1,
      by omega, ?_, ?_, ?_, ?_⟩
    · have herr := product_formula_finite_family_segmented (2 ^ n) (hubbardTermCount n)
        (⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)
        (fun j => relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j)) τ
        (by omega) hG
      have hsumG : ∑ j : Fin (hubbardTermCount n),
          relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j)
            = relabelGate (bitVecEquiv n) (hubbardHamiltonian (n := n) t μ U) :=
        sum_relabel_terms t μ U (bitVecEquiv n)
      calc ‖wordInterp (hubbardWord (n := n) t μ U τ (⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
              * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1))
            - HamiltonianEvolution (hubbardHamiltonian (n := n) t μ U) τ‖
          = ‖relabelGate (bitVecEquiv n) (wordInterp (hubbardWord (n := n) t μ U τ (⌈2 * τ ^ 2
              * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1))
              - HamiltonianEvolution (hubbardHamiltonian (n := n) t μ U) τ)‖ :=
            (l2_norm_relabelGate_sub (bitVecEquiv n) _ _).symm
        _ = ‖relabelGate (bitVecEquiv n) (wordInterp (hubbardWord (n := n) t μ U τ (⌈2 * τ ^ 2
                * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)))
              - relabelGate (bitVecEquiv n)
                  (HamiltonianEvolution (hubbardHamiltonian (n := n) t μ U) τ)‖ :=
            by rw [relabel_sub]
        _ = ‖pfFamily (fun j => relabelGate (bitVecEquiv n)
                (hubbardTermVec (n := n) t μ U j)) τ
              (⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)
              - HamiltonianEvolution
                  (relabelGate (bitVecEquiv n) (hubbardHamiltonian (n := n) t μ U)) τ‖ :=
            by rw [relabel_wordInterp_hubbardWord t μ U τ _ (bitVecEquiv n), relabel_evolution]
        _ = ‖pfFamily (fun j => relabelGate (bitVecEquiv n)
                (hubbardTermVec (n := n) t μ U j)) τ
              (⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)
              - HamiltonianEvolution (∑ j : Fin (hubbardTermCount n),
                  relabelGate (bitVecEquiv n) (hubbardTermVec (n := n) t μ U j)) τ‖ :=
            by rw [hsumG]
        _ ≤ τ ^ 2 / (2 * ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
              * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ))
              * pfCommutatorSum (fun j => relabelGate (bitVecEquiv n)
                  (hubbardTermVec (n := n) t μ U j)) := herr
        _ ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ)
              < 2 * ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
              * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ))]
            have h1 : τ ^ 2
                * pfCommutatorSum (fun j => relabelGate (bitVecEquiv n)
                  (hubbardTermVec (n := n) t μ U j))
                ≤ τ ^ 2 * (4 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hS (sq_nonneg τ)
            have hεx : ε * (2 * τ ^ 2 * hubbardCoeffSqBound t μ U
                * (hubbardTermCount n : ℝ) ^ 2 / ε)
                = 2 * τ ^ 2 * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 := by
              field_simp
            have hεr : ε * (2 * τ ^ 2 * hubbardCoeffSqBound t μ U
                * (hubbardTermCount n : ℝ) ^ 2 / ε)
                ≤ ε * ((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
                  * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hxle hε.le
            have hrr : τ ^ 2 * (4 * hubbardCoeffSqBound t μ U
                * (hubbardTermCount n : ℝ) ^ 2)
                = 2 * (2 * τ ^ 2 * hubbardCoeffSqBound t μ U
                  * (hubbardTermCount n : ℝ) ^ 2) := by ring
            nlinarith [h1, hεx, hεr, hrr]
    · rw [hcastL]
      exact hlenR
    · have h1 : ((2 * (n + 1) * (n + 1) * (hubbardWord (n := n) t μ U τ (⌈2 * τ ^ 2
              * hubbardCoeffSqBound t μ U * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1)).length : ℕ) : ℝ)
          = 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1) * (((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
              * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ) * (hubbardTermCount n : ℝ)) := by
        push_cast
        rw [hcastL]
        push_cast
        ring
      rw [h1]
      calc 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1) * (((⌈2 * τ ^ 2 * hubbardCoeffSqBound t μ U
              * (hubbardTermCount n : ℝ) ^ 2 / ε⌉₊ + 1 : ℕ) : ℝ) * (hubbardTermCount n : ℝ))
          ≤ 2 * ((n : ℝ) + 1) * ((n : ℝ) + 1)
              * (16 * ((n : ℝ) + 1) ^ 6 * (1 + τ ^ 2 * hubbardCoeffSqBound t μ U / ε)) :=
            mul_le_mul_of_nonneg_left hlenR (by positivity)
        _ = 32 * ((n : ℝ) + 1) ^ 8 * (1 + τ ^ 2 * hubbardCoeffSqBound t μ U / ε) := by ring
    · have h1 : ((4 * (n + 1) * (n + 1) : ℕ) : ℝ) = 4 * ((n : ℝ) + 1) ^ 2 := by
        push_cast; ring
      have hT0 : (0 : ℝ) ≤ τ ^ 2 * hubbardCoeffSqBound t μ U / ε :=
        div_nonneg hTC hε.le
      rw [h1]
      nlinarith [hT0]
  · intro r _
    exact ⟨fun e he => hubbardWord_mem t μ U τ r he,
      fun j => hubbardWord_filter_length t μ U τ r j⟩
end Qatlib.Concepts.FermionAlgebra.CarJordanWigner
