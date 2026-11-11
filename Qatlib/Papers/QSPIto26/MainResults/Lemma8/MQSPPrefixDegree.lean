/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSPIto26.MainResults.Core.MQSPCore
import Qatlib.Papers.QSPIto26.MainResults.Lemma4.MQSPDegreeEquality
import Qatlib.Papers.QSPIto26.MainResults.Lemma7.MQSPDegreeStep

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 8 — prefix degrees when `deg P = n`

Ito--Mori--Sakamoto--Fujii, fixed arXiv:2410.02332v3, Lemma 8 (Appendix A, p. 13),
Eqs. (63)--(66).

Lemma 8. Let `(P,Q)` be constructed by m-variable M-QSP in `n` steps via `(φ_0,…,φ_n)` and
`(s_1,…,s_n)`, and define the prefixes `(P^{(l)},Q^{(l)})` by (64). If `deg P = n`, then for all
`l ∈ {1,…,n}` and `j`, `deg P^{(l)} = l` and `deg_{a_j} P^{(l)} = |{k ≤ l | s_k = j}|`.

The proof follows the paper: prefixes satisfy the SU(2) form (Eqs. (6)/(51)) and the per-variable
degree bound `deg_{a_j} P^{(l)} ≤ |{k ≤ l | s_k = j}|` by upward induction on `l` (Lemma 4 trades
`Q`-degrees for `P`-degrees). Since the counts sum to `l` and `deg P = n`, the bounds saturate at
`l = n`; Lemma 7 (c008) then propagates the equalities downward: the `-1` branch would violate the
bound at the shorter prefix, so every prefix degree equals its count.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSPIto26.MainResults.Lemma8

open Qatlib.Papers.QSPIto26.MainResults.Core
open Qatlib.Papers.QSPIto26.MainResults.Lemma4
open Qatlib.Papers.QSPIto26.MainResults.Lemma7

/-! ### Small tools -/

/-- Every index of `Fin (n+1)` is either the last index or the cast of an index of `Fin n`. -/
lemma fin_last_or_castSucc {n : ℕ} (k : Fin (n + 1)) :
    k = Fin.last n ∨ ∃ j : Fin n, k = Fin.castSucc j := by
  rcases Nat.lt_or_ge k.val n with h | h
  · exact Or.inr ⟨⟨k.val, h⟩, rfl⟩
  · have hkn : k.val = n := by omega
    refine Or.inl (Fin.ext ?_)
    rw [Fin.val_last]
    exact hkn

/-- Conjugating the phase constant `e^{iψ}` gives `e^{-iψ}`. -/
lemma conjC_exp (ψ : ℝ) :
    conjC (Complex.exp (Complex.I * (ψ : ℂ))) = Complex.exp (-(Complex.I * (ψ : ℂ))) := by
  have hn : (starRingEnd ℂ) (Complex.I * (ψ : ℂ)) = -(Complex.I * (ψ : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  show (starRingEnd ℂ) (Complex.exp (Complex.I * (ψ : ℂ))) = _
  rw [← Complex.exp_conj, hn]

/-- The involution `P ↦ P^*` maps `0` to `0`. -/
lemma starOp_zero {m : ℕ} : starOp (0 : MLaurent m) = 0 := by
  have h1 : starL (0 : MLaurent m) = 0 := by
    rw [starL_eq]
    exact map_zero _
  show substInv m (starL 0) = 0
  rw [h1]
  exact map_zero _

/-- A zero-step word is just the initial phase `e^{iφ_0σ_z}`. -/
lemma wordMatrix_zero {m : ℕ} (φ' : Fin 1 → ℝ) (s' : Fin 0 → Fin m) :
    wordMatrix 0 φ' s' = phaseOp (φ' 0) := by
  have hL : (List.ofFn fun k : Fin 0 => signalOp (s' k) * phaseOp (φ' k.succ)).prod = 1 := rfl
  show phaseOp (φ' 0) * (List.ofFn fun k : Fin 0 => signalOp (s' k) * phaseOp (φ' k.succ)).prod = _
  rw [hL, mul_one]

/-- The phase operator has SU(2) form `!![P, 0; -0^*, P^*]` with `P = C'(e^{iψ})`. -/
lemma phaseOp_form {m : ℕ} (ψ : ℝ) :
    (phaseOp ψ : Matrix (Fin 2) (Fin 2) (MLaurent m))
      = !![C' (Complex.exp (Complex.I * (ψ : ℂ))), 0;
           -starOp 0, starOp (C' (Complex.exp (Complex.I * (ψ : ℂ))))] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rw [starOp_zero, neg_zero]
    rfl
  · rw [starOp_C', conjC_exp]
    rfl

/-- The count of positions `k ≤ l + 1` with signal `j` splits off the last position. -/
lemma count_castLE_succ {m n : ℕ} (s : Fin n → Fin m) (j : Fin m) (l : ℕ) (h2' : l + 1 ≤ n) :
    (Finset.univ.filter (fun k : Fin (l + 1) => s (Fin.castLE h2' k) = j)).card
      = (Finset.univ.filter (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k) = j)).card
        + (if j = s (Fin.castLE h2' (Fin.last l)) then 1 else 0) := by
  have hcard : ∀ {N : ℕ} (t : Fin N → Fin m),
      (Finset.univ.filter (fun k => t k = j)).card = ∑ k, (if t k = j then 1 else 0) := by
    intro N t
    rw [← Finset.sum_filter (fun k => t k = j) (fun _ => (1 : ℕ)), Finset.card_eq_sum_ones]
  rw [hcard, hcard, Fin.sum_univ_castSucc]
  by_cases hjs : j = s (Fin.castLE h2' (Fin.last l))
  · rw [if_pos hjs.symm, if_pos hjs]
    rfl
  · rw [if_neg (fun h => hjs h.symm), if_neg hjs]
    rfl

/-- Truncating the prefix at `l` and appending the `(l+1)`-st signal and phase reproduces the
prefix truncated at `l + 1`. -/
lemma wordMatrix_castLE_succ {m n : ℕ} (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m) (l : ℕ)
    (h2' : l + 1 ≤ n) :
    wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
        (fun k : Fin (l + 1) => s (Fin.castLE h2' k))
      = wordMatrix l (fun k : Fin (l + 1) => φ (Fin.castLE (Nat.succ_le_succ (Nat.le_of_succ_le h2')) k))
          (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k))
        * signalOp (s (Fin.castLE h2' (Fin.last l)))
        * phaseOp (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) := by
  have key := wordMatrix_append
    (φ := fun k : Fin (l + 1) => φ (Fin.castLE (Nat.succ_le_succ (Nat.le_of_succ_le h2')) k))
    (φn := φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1))))
    (s := fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k))
    (sn := s (Fin.castLE h2' (Fin.last l)))
  have eφ : (Fin.snoc (fun k : Fin (l + 1) => φ (Fin.castLE (Nat.succ_le_succ (Nat.le_of_succ_le h2')) k))
      (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) : Fin (l + 2) → ℝ)
      = fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k) := by
    funext k
    rcases fin_last_or_castSucc k with hk | ⟨k', hk⟩
    · subst hk
      simp only [Fin.snoc_last]
    · subst hk
      simp only [Fin.snoc_castSucc]
      rfl
  have es : (Fin.snoc (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k))
      (s (Fin.castLE h2' (Fin.last l))) : Fin (l + 1) → Fin m)
      = fun k : Fin (l + 1) => s (Fin.castLE h2' k) := by
    funext k
    rcases fin_last_or_castSucc k with hk | ⟨k', hk⟩
    · subst hk
      simp only [Fin.snoc_last]
    · subst hk
      simp only [Fin.snoc_castSucc]
      rfl
  rw [eφ, es] at key
  exact key

/-! ### Lemma 8 -/

/-- Lemma 8 (arXiv:2410.02332v3, p. 13, Eqs. (65)--(66)): every prefix `P^{(l)}` of a word with
`deg P = n` saturates its degree. Complete given the lex-leading-monomial interface hypothesis
`hlead` of Lemmas 4--7. -/
theorem lemma8_prefix_degree {m n : ℕ} (hn : 1 ≤ n) (P Q : MLaurent m)
    (φ : Fin (n + 1) → ℝ) (s : Fin n → Fin m)
    (h : wordMatrix n φ s = !![P, Q; -starOp Q, starOp P])
    (hdeg : degTotal P = n)
    (hlead : ∀ (X : MLaurent m) (j : Fin m), X ≠ 0 →
      degVar j (X * starOp X) = 2 * degVar j X) :
    ∀ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ n),
      degTotal (wordMatrixPrefix n l h2 φ s 0 0) = l ∧
        ∀ j : Fin m,
          degVar j (wordMatrixPrefix n l h2 φ s 0 0) =
            (Finset.univ.filter (fun k : Fin l => s (Fin.castLE h2 k) = j)).card := by
  classical
  -- Every prefix word has SU(2) form and is constructible.
  have formU : ∀ (l : ℕ) (h2 : l ≤ n), ∃ Pl Ql : MLaurent m,
      wordMatrix l (fun k : Fin (l + 1) => φ (Fin.castLE (Nat.succ_le_succ h2) k))
          (fun k : Fin l => s (Fin.castLE h2 k))
        = !![Pl, Ql; -starOp Ql, starOp Pl] ∧ Constructible l Pl Ql := by
    intro l
    induction l with
    | zero =>
      intro h2
      have hform0 : wordMatrix 0 (fun k : Fin (0 + 1) => φ (Fin.castLE (Nat.succ_le_succ h2) k))
          (fun k : Fin 0 => s (Fin.castLE h2 k))
          = !![C' (Complex.exp (Complex.I * ((fun k : Fin (0 + 1) => φ (Fin.castLE (Nat.succ_le_succ h2) k)) 0))), 0;
               -starOp 0, starOp (C' (Complex.exp (Complex.I * ((fun k : Fin (0 + 1) => φ (Fin.castLE (Nat.succ_le_succ h2) k)) 0))))] := by
        rw [wordMatrix_zero]
        exact phaseOp_form _
      exact ⟨_, _, hform0, ⟨_, _, hform0⟩⟩
    | succ l ih =>
      intro h2'
      obtain ⟨Pl, Ql, hform, hcon⟩ := ih (Nat.le_of_succ_le h2')
      have hW : wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
          (fun k : Fin (l + 1) => s (Fin.castLE h2' k))
          = appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) := by
        rw [wordMatrix_castLE_succ φ s l h2', hform]
        rfl
      have hf := append_form Pl Ql (s (Fin.castLE h2' (Fin.last l)))
        (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1))))
      have hfinal : wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
          (fun k : Fin (l + 1) => s (Fin.castLE h2' k))
          = !![(wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
                 (fun k : Fin (l + 1) => s (Fin.castLE h2' k))) 0 0,
               (wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
                 (fun k : Fin (l + 1) => s (Fin.castLE h2' k))) 0 1;
               -starOp ((wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
                 (fun k : Fin (l + 1) => s (Fin.castLE h2' k))) 0 1),
               starOp ((wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
                 (fun k : Fin (l + 1) => s (Fin.castLE h2' k))) 0 0)] := by
        refine Matrix.ext fun i j => ?_
        fin_cases i <;> fin_cases j
        · rfl
        · rfl
        · rw [hW]
          show appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) 1 0
              = -starOp (appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) 0 1)
          exact hf.1
        · rw [hW]
          show appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) 1 1
              = starOp (appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) 0 0)
          exact hf.2
      exact ⟨_, _, hfinal, ⟨_, _, hfinal⟩⟩
  -- Per-variable degree bound by upward induction (Eq. (73)).
  have boundU : ∀ (l : ℕ) (h2 : l ≤ n) (j : Fin m),
      degVar j (wordMatrixPrefix n l h2 φ s 0 0)
        ≤ (Finset.univ.filter (fun k : Fin l => s (Fin.castLE h2 k) = j)).card := by
    intro l
    induction l with
    | zero =>
      intro h2 j
      have hWW0 : wordMatrixPrefix n 0 h2 φ s
          = wordMatrix 0 (fun k : Fin (0 + 1) => φ (Fin.castLE (Nat.succ_le_succ h2) k))
              (fun k : Fin 0 => s (Fin.castLE h2 k)) := rfl
      have h00 : wordMatrixPrefix n 0 h2 φ s 0 0
          = C' (Complex.exp (Complex.I * ((fun k : Fin (0 + 1) => φ (Fin.castLE (Nat.succ_le_succ h2) k)) 0))) := by
        rw [hWW0, wordMatrix_zero]
        rfl
      have hc0 : (Finset.univ.filter (fun k : Fin 0 => s (Fin.castLE h2 k) = j)).card = 0 := by
        simp
      rw [h00, degVar_C', hc0]
    | succ l ih =>
      intro h2' j
      obtain ⟨Pl, Ql, hform, hcon⟩ := formU l (Nat.le_of_succ_le h2')
      have hWW0 : wordMatrixPrefix n l (Nat.le_of_succ_le h2') φ s
          = wordMatrix l (fun k : Fin (l + 1) => φ (Fin.castLE (Nat.succ_le_succ (Nat.le_of_succ_le h2')) k))
              (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k)) := rfl
      have hPlE : wordMatrixPrefix n l (Nat.le_of_succ_le h2') φ s 0 0 = Pl := by
        rw [hWW0, hform]
        rfl
      have hW : wordMatrixPrefix n (l + 1) h2' φ s
          = appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) := by
        have hWW1 : wordMatrixPrefix n (l + 1) h2' φ s
            = wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
                (fun k : Fin (l + 1) => s (Fin.castLE h2' k)) := rfl
        rw [hWW1, wordMatrix_castLE_succ φ s l h2', hform]
        rfl
      have hentry : wordMatrixPrefix n (l + 1) h2' φ s 0 0
          = C' (Complex.exp (Complex.I * (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1))) : ℂ)) / 2)
              * (Pl * (var (s (Fin.castLE h2' (Fin.last l))) + varInv (s (Fin.castLE h2' (Fin.last l))))
                  + Ql * (var (s (Fin.castLE h2' (Fin.last l))) - varInv (s (Fin.castLE h2' (Fin.last l))))) := by
        rw [hW, append_entry00]
      have hubb := degVar_bound_sum j (s (Fin.castLE h2' (Fin.last l)))
        (Complex.exp (Complex.I * (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1))) : ℂ)) / 2) Pl Ql
      rw [← hentry] at hubb
      have hdj := lemma4_degree_eq Pl Ql hcon hlead j
      have hih := ih (Nat.le_of_succ_le h2') j
      rw [hPlE] at hih
      have hc := count_castLE_succ s j l h2'
      omega
  -- The counts over all variables add up to the prefix length (Eq. (73)).
  have sumU : ∀ (l : ℕ) (h2 : l ≤ n),
      ∑ j : Fin m, (Finset.univ.filter (fun k : Fin l => s (Fin.castLE h2 k) = j)).card = l := by
    intro l h2
    have hcard : ∀ j : Fin m,
        (Finset.univ.filter (fun k : Fin l => s (Fin.castLE h2 k) = j)).card
          = ∑ k : Fin l, (if s (Fin.castLE h2 k) = j then 1 else 0) := by
      intro j
      rw [← Finset.sum_filter (fun k => s (Fin.castLE h2 k) = j) (fun _ => (1 : ℕ)), Finset.card_eq_sum_ones]
    simp only [hcard]
    rw [Finset.sum_comm]
    have hone : ∀ k : Fin l,
        ∑ j : Fin m, (if s (Fin.castLE h2 k) = j then 1 else 0) = 1 := by
      intro k
      rw [Finset.sum_eq_single_of_mem (s (Fin.castLE h2 k)) (Finset.mem_univ _)]
      · exact if_pos rfl
      · intro b _ hb
        exact if_neg (Ne.symm hb)
    simp only [hone]
    simp
  -- Saturation at the full length: `deg P = n` forces equality at `l = n`.
  have hPn : wordMatrixPrefix n n (Nat.le_refl n) φ s 0 0 = P := by
    have hWn : wordMatrixPrefix n n (Nat.le_refl n) φ s = wordMatrix n φ s := rfl
    rw [hWn, h]
    rfl
  have topEq : ∀ j : Fin m, degVar j P
      = (Finset.univ.filter (fun k : Fin n => s (Fin.castLE (Nat.le_refl n) k) = j)).card := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨j₀, hj₀⟩ := hcon
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)), degVar j P
        ≤ (Finset.univ.filter (fun k : Fin n => s (Fin.castLE (Nat.le_refl n) k) = j)).card := by
      intro j _
      have hb := boundU n (Nat.le_refl n) j
      rw [hPn] at hb
      exact hb
    have hlt : ∑ j : Fin m, degVar j P
        < ∑ j : Fin m, (Finset.univ.filter (fun k : Fin n => s (Fin.castLE (Nat.le_refl n) k) = j)).card :=
      Finset.sum_lt_sum hle ⟨j₀, Finset.mem_univ _, by
        have hb := boundU n (Nat.le_refl n) j₀
        rw [hPn] at hb
        omega⟩
    have hDT : degTotal P = ∑ j : Fin m, degVar j P := rfl
    have hsum := sumU n (Nat.le_refl n)
    omega
  -- Downward induction on `n - l` using Lemma 7.
  have main : ∀ (d l : ℕ), l + d = n → ∀ (h2 : l ≤ n),
      degTotal (wordMatrixPrefix n l h2 φ s 0 0) = l ∧ ∀ j : Fin m,
        degVar j (wordMatrixPrefix n l h2 φ s 0 0)
          = (Finset.univ.filter (fun k : Fin l => s (Fin.castLE h2 k) = j)).card := by
    intro d
    induction d with
    | zero =>
      intro l hd h2
      have hln : l = n := by omega
      have hln' : n = l := hln.symm
      subst hln'
      show degTotal (wordMatrixPrefix n n (Nat.le_refl n) φ s 0 0) = n ∧ ∀ j : Fin m,
        degVar j (wordMatrixPrefix n n (Nat.le_refl n) φ s 0 0)
          = (Finset.univ.filter (fun k : Fin n => s (Fin.castLE (Nat.le_refl n) k) = j)).card
      refine ⟨by rw [hPn, hdeg], fun j => by rw [hPn, topEq j]⟩
    | succ d ih =>
      intro l hd h2
      have h2' : l + 1 ≤ n := by omega
      have hstep := ih (l + 1) (by omega) h2'
      show degTotal (wordMatrixPrefix n l (Nat.le_of_succ_le h2') φ s 0 0) = l ∧ ∀ j : Fin m,
        degVar j (wordMatrixPrefix n l (Nat.le_of_succ_le h2') φ s 0 0)
          = (Finset.univ.filter (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k) = j)).card
      obtain ⟨Pl, Ql, hform, hcon⟩ := formU l (Nat.le_of_succ_le h2')
      have hWW0 : wordMatrixPrefix n l (Nat.le_of_succ_le h2') φ s
          = wordMatrix l (fun k : Fin (l + 1) => φ (Fin.castLE (Nat.succ_le_succ (Nat.le_of_succ_le h2')) k))
              (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k)) := rfl
      have hPlE : wordMatrixPrefix n l (Nat.le_of_succ_le h2') φ s 0 0 = Pl := by
        rw [hWW0, hform]
        rfl
      have hW : wordMatrixPrefix n (l + 1) h2' φ s
          = appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
              (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) := by
        have hWW1 : wordMatrixPrefix n (l + 1) h2' φ s
            = wordMatrix (l + 1) (fun k : Fin (l + 2) => φ (Fin.castLE (Nat.succ_le_succ h2') k))
                (fun k : Fin (l + 1) => s (Fin.castLE h2' k)) := rfl
        rw [hWW1, wordMatrix_castLE_succ φ s l h2', hform]
        rfl
      have hstep7 := lemma7_degree_step Pl Ql hcon hlead
        (s (Fin.castLE h2' (Fin.last l))) (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1))))
      have hentryEq : ∀ j' : Fin m,
          degVar j' (wordMatrixPrefix n (l + 1) h2' φ s 0 0)
            = degVar j' (appendWord Pl Ql (s (Fin.castLE h2' (Fin.last l)))
                (φ (Fin.castLE (Nat.succ_le_succ h2') (Fin.last (l + 1)))) 0 0) := by
        intro j'
        rw [hW]
      have key : ∀ j : Fin m, degVar j Pl
          = (Finset.univ.filter (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k) = j)).card := by
        intro j
        have hcj := count_castLE_succ s j l h2'
        have hcountL1 := hstep.2 j
        rw [hentryEq j] at hcountL1
        by_cases hjs : j = s (Fin.castLE h2' (Fin.last l))
        · rw [if_pos hjs] at hcj
          rw [hjs] at hcountL1 hcj ⊢
          rcases hstep7.1 with h' | h'
          · have hbL := boundU l (Nat.le_of_succ_le h2') j
            rw [hjs, hPlE] at hbL
            omega
          · omega
        · rw [if_neg hjs] at hcj
          have honej := hstep7.2 j hjs
          rw [honej] at hcountL1
          omega
      refine ⟨?_, fun j => by rw [hPlE]; exact key j⟩
      rw [hPlE]
      have hDT : degTotal Pl = ∑ j : Fin m, degVar j Pl := rfl
      have hsum := sumU l (Nat.le_of_succ_le h2')
      have hsumEq : ∑ j : Fin m, degVar j Pl
          = ∑ j : Fin m, (Finset.univ.filter (fun k : Fin l => s (Fin.castLE (Nat.le_of_succ_le h2') k) = j)).card :=
        Finset.sum_congr rfl (fun j _ => key j)
      omega
  intro l h1 h2
  exact main (n - l) l (by omega) h2

end Qatlib.Papers.QSPIto26.MainResults.Lemma8
