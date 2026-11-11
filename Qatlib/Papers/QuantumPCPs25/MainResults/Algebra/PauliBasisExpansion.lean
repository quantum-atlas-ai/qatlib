/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Pauli expansion of computational-basis projectors (Lemma 7)

Source: Buhrman--Helsen--Weggemans, *Quantum PCPs: on Adaptivity, Multiple
Provers and Reductions to Local Hamiltonians*, arXiv:2403.04841v3 (Quantum 9,
1791 (2025)), Lemma 7, p. 18 (file lines 1089--1105).

The paper uses the single-qubit identity `|b⟩⟨b| = (Z + (1-2b) I)/2` for
`b ∈ {0,1}` and expands the tensor product to obtain
`Π_q = |q⟩⟨q| = 2^{-k} Σ_{j ∈ {0,1}^k} a_j U_j`
where each `U_j ∈ {I,Z}^{⊗k}` is a Pauli word and `a_j ∈ {-1,+1}`.

This file formalises the statement on matrices indexed by the finite set
`Fin k → Bool` of `k`-bit strings.  `pauliWord k s` is the diagonal `{I,Z}`
word acting as `Z` exactly on the qubit positions where `s` is `true`, and
`basisProj k q` is `|q⟩⟨q|`.

Main result: `basisProj_eq_pauliExpansion`, fully proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults.Algebra

open Matrix
open scoped BigOperators ComplexOrder

/-- The computational-basis projector `|q⟩⟨q|` on `k` qubits, indexed by the
type `Fin k → Bool` of `k`-bit strings (paper: Lemma 7, `Π_q`, p. 18). -/
def basisProj (k : ℕ) (q : Fin k → Bool) : Matrix (Fin k → Bool) (Fin k → Bool) ℂ :=
  Matrix.diagonal (fun a => if a = q then 1 else 0)

/-- The diagonal eigenvalue of the `Z` word at basis state `a`. -/
def pauliDiag (k : ℕ) (s : Fin k → Bool) (a : Fin k → Bool) : ℂ :=
  ∏ i, (if s i then (if a i then (-1 : ℂ) else 1) else 1)

/-- The `{I,Z}^{⊗k}` Pauli word indexed by `s : Fin k → Bool`: the diagonal
operator that applies `Z` exactly on the qubit positions where `s` is `true`
(paper: `U_j`, Lemma 7, p. 18). -/
def pauliWord (k : ℕ) (s : Fin k → Bool) : Matrix (Fin k → Bool) (Fin k → Bool) ℂ :=
  Matrix.diagonal (pauliDiag k s)

/-- Every diagonal entry of a Pauli word is `+1` or `-1`, so `U_s ∈ {I,Z}^{⊗k}`
has the form required by Lemma 7 (p. 18). -/
theorem pauliDiag_mem (k : ℕ) (s a : Fin k → Bool) :
    pauliDiag k s a = 1 ∨ pauliDiag k s a = -1 := by
  classical
  rw [pauliDiag]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.prod_univ_castSucc]
      have ih' := ih (fun i => s i.castSucc) (fun i => a i.castSucc)
      have hlast : (if s (Fin.last k) then (if a (Fin.last k) then (-1 : ℂ) else 1)
          else 1) = 1 ∨
          (if s (Fin.last k) then (if a (Fin.last k) then (-1 : ℂ) else 1)
            else 1) = -1 := by
        by_cases hs : s (Fin.last k) <;> by_cases ha : a (Fin.last k) <;>
          simp [hs, ha]
      rcases ih' with h | h <;> rcases hlast with hl | hl <;> simp [h, hl]

/-- The `{+1,-1}` Pauli-expansion coefficient `a_s = ∏_{i : s i = true} (1 - 2 q_i)`
of Lemma 7, p. 18: the sign attached to the `{I,Z}` word that carries `Z` on the
positions where `s` is `true`. -/
def pauliCoeff (k : ℕ) (q s : Fin k → Bool) : ℂ :=
  ∏ i, (if s i then (if q i then (-1 : ℂ) else 1) else 1)

/-- The coefficient `a_s` is `+1` or `-1` (paper: `a_j ∈ {-1,+1}`, Lemma 7, p. 18). -/
theorem pauliCoeff_mem {k : ℕ} (q s : Fin k → Bool) :
    pauliCoeff k q s = 1 ∨ pauliCoeff k q s = -1 := by
  classical
  rw [pauliCoeff]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.prod_univ_castSucc]
      have ih' := ih (fun i => q i.castSucc) (fun i => s i.castSucc)
      have hlast : (if s (Fin.last k) then (if q (Fin.last k) then (-1 : ℂ) else 1)
          else 1) = 1 ∨
          (if s (Fin.last k) then (if q (Fin.last k) then (-1 : ℂ) else 1)
            else 1) = -1 := by
        by_cases hs : s (Fin.last k) <;> by_cases hq : q (Fin.last k) <;>
          simp [hs, hq]
      rcases ih' with h | h <;> rcases hlast with hl | hl <;> simp [h, hl]

/-- **Lemma 7** (arXiv:2403.04841v3, p. 18, Eq. (6)).  The computational-basis
projector on `k` qubits expands as a signed sum of `{I,Z}^{⊗k}` Pauli words:
`|q⟩⟨q| = 2^{-k} Σ_{s} a_s U_s`, with `a_s ∈ {-1,+1}` and `U_s ∈ {I,Z}^{⊗k}`. -/
theorem basisProj_eq_pauliExpansion (k : ℕ) (q : Fin k → Bool) :
    basisProj k q =
      (((2 : ℂ) ^ k)⁻¹) • ∑ s : Fin k → Bool,
        pauliCoeff k q s • pauliWord k s := by
  classical
  ext a b
  simp only [basisProj, pauliWord, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    simp only [if_true]
    have hterm : ∀ s : Fin k → Bool,
        pauliCoeff k q s * pauliDiag k s a =
          ∏ i, (if s i then ((if q i then (-1 : ℂ) else 1) * (if a i then (-1 : ℂ) else 1))
                 else 1) := by
      intro s
      simp only [pauliCoeff, pauliDiag]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hs : s i <;> simp [hs]
    have hsum : (∑ c : Fin k → Bool, pauliCoeff k q c * pauliDiag k c a) =
        ∑ c : Fin k → Bool, ∏ i, (if c i then
          ((if q i then (-1 : ℂ) else 1) * (if a i then (-1 : ℂ) else 1)) else 1) :=
      Finset.sum_congr rfl (fun s _ => hterm s)
    rw [hsum,
      ← Fintype.prod_sum (f := fun i (bb : Bool) =>
        if bb then ((if q i then (-1 : ℂ) else 1) * (if a i then (-1 : ℂ) else 1)) else 1)]
    have hfac : ∀ i : Fin k,
        (∑ bb : Bool, (if bb then
          ((if q i then (-1 : ℂ) else 1) * (if a i then (-1 : ℂ) else 1)) else 1)) =
        (if a i = q i then (2 : ℂ) else 0) := by
      intro i
      rw [Fintype.sum_bool]
      by_cases hai : a i <;> by_cases hqi : q i <;> simp [hai, hqi] <;> norm_num
    simp only [hfac]
    by_cases haq : a = q
    · subst haq
      simp only [if_true]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      field_simp
    · have hzero : (∏ i : Fin k, (if a i = q i then (2 : ℂ) else 0)) = 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp haq
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
      rw [hzero, if_neg haq]
      simp
  · simp only [if_neg hab, mul_zero, Finset.sum_const_zero, mul_zero]

end Qatlib.Papers.QuantumPCPs25.MainResults.Algebra
