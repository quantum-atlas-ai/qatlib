/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SeqEntangle05.MainResults.ExampleStates

open Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs
open Qatlib.Papers.SeqEntangle05.MainResults.SequentialGeneration

def maskBlock (D : ℕ) [DecidableEq (Fin D)] (i : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (fun s => if s = i then (1 : ℂ) else 0)

def ghzBlock : Block 2 := fun i => maskBlock 2 i

def ghzState (n : ℕ) (bits : Fin n → Fin 2) : ℂ :=
  if (∀ k, bits k = 0) ∨ (∀ k, bits k = 1) then 1 else 0

theorem prodBlocks_replicate_ghzBlock (n : ℕ) (is : List (Fin 2)) (h : is.length = n) :
    prodBlocks (List.replicate n ghzBlock) is =
      Matrix.diagonal (fun s : Fin 2 =>
        (is.map (fun i => if s = i then (1 : ℂ) else 0)).prod) := by
  induction is generalizing n with
  | nil =>
      have hn : n = 0 := by simpa using h.symm
      subst hn
      simp
  | cons i is' ih =>
      have hn : n = is'.length + 1 := by simpa using h.symm
      subst hn
      rw [List.replicate_succ, prodBlocks_cons, ih is'.length rfl]
      show Matrix.diagonal (fun s : Fin 2 => if s = i then (1 : ℂ) else 0) *
          Matrix.diagonal (fun s : Fin 2 => (is'.map (fun i => if s = i then (1 : ℂ) else 0)).prod) =
        Matrix.diagonal (fun s : Fin 2 => ((i :: is').map (fun i => if s = i then (1 : ℂ) else 0)).prod)
      simp only [List.map_cons, List.prod_cons]
      rw [Matrix.diagonal_mul_diagonal]

theorem diagonal_mulVec_one {D : ℕ} [DecidableEq (Fin D)] (d : Fin D → ℂ) :
    Matrix.diagonal d *ᵥ (fun _ => (1 : ℂ)) = d := by
  funext s
  rw [mulVec_diagonal]
  simp

theorem prod_indicator (l : List (Fin 2)) (i : Fin 2) :
    (l.map (fun b => if i = b then (1 : ℂ) else 0)).prod =
      if (∀ b ∈ l, i = b) then 1 else 0 := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      rw [List.map_cons, List.prod_cons]
      by_cases hb : i = b
      · rw [if_pos hb, one_mul, ih]
        have hiff : (∀ x ∈ bs, i = x) ↔ (∀ x ∈ b :: bs, i = x) := by
          constructor
          · intro h x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · exact hb
            · exact h x hx'
          · intro h x hx
            exact h x (List.mem_cons_of_mem b hx)
        simp only [hiff]
      · have hneg : ¬ (∀ b_1 ∈ b :: bs, i = b_1) := by
          intro hc
          exact hb (hc b (by simp))
        rw [if_neg hb, zero_mul, if_neg hneg]

theorem forall_mem_ofFn {n : ℕ} (bits : Fin n → Fin 2) (i : Fin 2) :
    (∀ x ∈ List.ofFn bits, i = x) ↔ ∀ k, bits k = i := by
  constructor
  · intro h k
    exact (h (bits k) (List.mem_ofFn.mpr ⟨k, rfl⟩)).symm
  · intro h x hx
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hx
    rw [← hk]
    exact (h k).symm

theorem mpsAmplitude_ghz (n : ℕ) (bits : Fin n → Fin 2) :
    mpsAmplitude (fun _ => ghzBlock) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) bits =
      ((List.ofFn bits).map (fun b => if (0 : Fin 2) = b then (1 : ℂ) else 0)).prod +
      ((List.ofFn bits).map (fun b => if (1 : Fin 2) = b then (1 : ℂ) else 0)).prod := by
  unfold mpsAmplitude blockProd
  have hA : List.ofFn (fun _ : Fin n => ghzBlock) = List.replicate n ghzBlock := by simp
  rw [hA]
  have hlen : (List.ofFn bits).length = n := by simp
  rw [prodBlocks_replicate_ghzBlock n (List.ofFn bits) hlen]
  simp only [mulVec_diagonal, mul_one, one_mul, star_one]
  rw [Fin.sum_univ_two]

theorem ghz_cond_add {n : ℕ} (hn : 1 ≤ n) (bits : Fin n → Fin 2) :
    (if (∀ k, bits k = 0) then (1 : ℂ) else 0) +
        (if (∀ k, bits k = 1) then (1 : ℂ) else 0) =
      if ((∀ k, bits k = 0) ∨ (∀ k, bits k = 1)) then 1 else 0 := by
  by_cases h0 : ∀ k, bits k = 0
  · by_cases h1 : ∀ k, bits k = 1
    · exfalso
      have hk0 := h0 (⟨0, by omega⟩ : Fin n)
      have hk1 := h1 (⟨0, by omega⟩ : Fin n)
      rw [hk0] at hk1
      exact absurd hk1 (by decide)
    · rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]; simp
  · rw [if_neg h0]
    by_cases h1 : ∀ k, bits k = 1
    · rw [if_pos h1, if_pos (Or.inr h1)]; simp
    · rw [if_neg h1, if_neg (by rintro (h | h); exact h0 h; exact h1 h)]; simp

theorem ghzState_isMPS {n : ℕ} (hn : 1 ≤ n) : IsMPS 2 n (ghzState n) := by
  refine ⟨fun _ => ghzBlock, fun _ => (1 : ℂ), fun _ => (1 : ℂ), ?_⟩
  intro bits
  rw [mpsAmplitude_ghz, prod_indicator, prod_indicator]
  simp only [forall_mem_ofFn]
  unfold ghzState
  exact (ghz_cond_add hn bits).symm

def wE : Matrix (Fin 2) (Fin 2) ℂ := fun a b => if a = 0 ∧ b = 1 then (1 : ℂ) else 0

def wBlock : Block 2 := fun i => if i = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) else wE

def wPhiI : Fin 2 → ℂ := fun s => if s = 1 then 1 else 0

def wPhiF : Fin 2 → ℂ := fun s => if s = 0 then 1 else 0

def onesCount : List (Fin 2) → ℕ
  | [] => 0
  | i :: is => onesCount is + (if i = 0 then 0 else 1)

theorem wE_sq_zero : wE ^ 2 = 0 := by
  ext a b
  simp only [pow_two, Matrix.mul_apply, Matrix.zero_apply]
  fin_cases a <;> fin_cases b <;> simp [wE, Fin.sum_univ_two]

theorem wE_pow_zero_one (m : ℕ) : (wE ^ m) 0 1 = if m = 1 then (1 : ℂ) else 0 := by
  by_cases h0 : m = 0
  · subst h0; simp [wE]
  by_cases h1 : m = 1
  · subst h1; simp [wE]
  · have h2 : 2 ≤ m := by omega
    have hm : wE ^ m = wE ^ 2 * wE ^ (m - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [hm, wE_sq_zero, Matrix.zero_mul, if_neg h1]
    simp

theorem prodBlocks_replicate_wBlock (n : ℕ) (is : List (Fin 2)) (h : is.length = n) :
    prodBlocks (List.replicate n wBlock) is = wE ^ onesCount is := by
  induction is generalizing n with
  | nil =>
      have hn : n = 0 := by simpa using h.symm
      subst hn
      simp [onesCount]
  | cons i is' ih =>
      have hn : n = is'.length + 1 := by simpa using h.symm
      subst hn
      rw [List.replicate_succ, prodBlocks_cons, ih is'.length rfl]
      by_cases hi : i = 0
      · subst hi
        simp [wBlock, onesCount]
      · have hwb : wBlock i = wE := by simp [wBlock, hi]
        rw [hwb]
        show wE * wE ^ onesCount is' = wE ^ (onesCount is' + (if i = 0 then 0 else 1))
        rw [if_neg hi, pow_succ']

theorem mpsAmplitude_w (n : ℕ) (bits : Fin n → Fin 2) :
    mpsAmplitude (fun _ => wBlock) wPhiI wPhiF bits =
      (wE ^ onesCount (List.ofFn bits)) 0 1 := by
  unfold mpsAmplitude blockProd
  have hA : List.ofFn (fun _ : Fin n => wBlock) = List.replicate n wBlock := by simp
  rw [hA]
  have hlen : (List.ofFn bits).length = n := by simp
  rw [prodBlocks_replicate_wBlock n (List.ofFn bits) hlen]
  simp [wPhiF, wPhiI, Matrix.mulVec, Fin.sum_univ_two]

def wState (n : ℕ) (bits : Fin n → Fin 2) : ℂ :=
  if onesCount (List.ofFn bits) = 1 then 1 else 0

theorem wState_isMPS (n : ℕ) : IsMPS 2 n (wState n) := by
  refine ⟨fun _ => wBlock, wPhiI, wPhiF, ?_⟩
  intro bits
  rw [mpsAmplitude_w, wE_pow_zero_one]
  unfold wState
  rfl

def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

def clBlock : Block 2 := fun i => fun a b =>
  invSqrt2 * (if b = i then (if a = 0 then (1 : ℂ) else (if i = 0 then 1 else -1)) else 0)

def clPhiI : Fin 2 → ℂ := fun _ => 1

def clPhiF : Fin 2 → ℂ := fun s => if s = 0 then 1 else 0

def adjCount : List (Fin 2) → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest => (if x = 1 ∧ y = 1 then 1 else 0) + adjCount (y :: rest)

def clState (n : ℕ) (bits : Fin n → Fin 2) : ℂ :=
  invSqrt2 ^ n * (-1 : ℂ) ^ (adjCount (List.ofFn bits))

def headSign : List (Fin 2) → ℂ
  | [] => 1
  | i :: _ => if i = 0 then 1 else -1

theorem adj_step (i : Fin 2) (js : List (Fin 2)) :
    (-1 : ℂ) ^ (adjCount js) * (if i = 0 then 1 else headSign js)
      = (-1 : ℂ) ^ (adjCount (i :: js)) := by
  cases js with
  | nil => simp [adjCount, headSign]
  | cons j ks =>
      fin_cases i <;> fin_cases j <;>
        simp [adjCount, headSign, pow_succ, pow_add]

theorem clBlock_mulVec (i : Fin 2) (w : Fin 2 → ℂ) (a : Fin 2) :
    (clBlock i *ᵥ w) a
      = invSqrt2 * (if a = 0 then 1 else (if i = 0 then 1 else -1)) * w i := by
  fin_cases i <;> fin_cases a <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, clBlock]

theorem clChain (l : List (Fin 2)) :
    (prodBlocks (List.replicate l.length clBlock) l *ᵥ clPhiI) 0
      = invSqrt2 ^ l.length * (-1 : ℂ) ^ (adjCount l) ∧
    (prodBlocks (List.replicate l.length clBlock) l *ᵥ clPhiI) 1
      = invSqrt2 ^ l.length * (-1 : ℂ) ^ (adjCount l) * headSign l := by
  induction l with
  | nil => simp [clPhiI, adjCount, headSign]
  | cons i js ih =>
      rw [List.length_cons, List.replicate_succ, prodBlocks_cons, ← Matrix.mulVec_mulVec]
      obtain ⟨h0, h1⟩ := ih
      have hw : ∀ a : Fin 2,
          (prodBlocks (List.replicate js.length clBlock) js *ᵥ clPhiI) a
            = invSqrt2 ^ js.length * (-1 : ℂ) ^ (adjCount js)
              * (if a = 0 then 1 else headSign js) := by
        intro a
        fin_cases a
        · simpa using h0
        · simpa using h1
      constructor
      · rw [clBlock_mulVec, if_pos rfl, hw, ← adj_step i js]
        simp only [List.length_cons, pow_succ]
        ring
      · rw [clBlock_mulVec, hw, ← adj_step i js]
        simp only [List.length_cons, pow_succ, headSign,
          if_neg (show ¬((1 : Fin 2) = 0) by decide)]
        ring

theorem clState_isMPS (n : ℕ) : IsMPS 2 n (clState n) := by
  refine ⟨fun _ => clBlock, clPhiI, clPhiF, ?_⟩
  intro bits
  unfold clState mpsAmplitude blockProd
  have hA : List.ofFn (fun _ : Fin n => clBlock) = List.replicate n clBlock := by simp
  rw [hA]
  have hlen : (List.ofFn bits).length = n := by simp
  have h := (clChain (List.ofFn bits)).1
  rw [hlen] at h
  simp only [Fin.sum_univ_two, clPhiF, star_one, star_zero]
  simpa using h.symm

theorem ghzState_seqGenerable {n : ℕ} (hn : 1 ≤ n) :
    SeqGenerable 2 n (ghzState n) :=
  isMPS_seqGenerable_uncond (ghzState_isMPS hn)

theorem wState_seqGenerable (n : ℕ) : SeqGenerable 2 n (wState n) :=
  isMPS_seqGenerable_uncond (wState_isMPS n)

theorem clState_seqGenerable (n : ℕ) : SeqGenerable 2 n (clState n) :=
  isMPS_seqGenerable_uncond (clState_isMPS n)

end Qatlib.Papers.SeqEntangle05.MainResults.ExampleStates
