/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PetzRecovery26.VirtualAdjoint.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Virtual complex conjugation via Werner--Holevo channels (Theorem 3)

Fixed source version: arXiv:2602.05828v1 (2026-02-05), Section III B and
Theorem 3 (p. 4), Eqs. (6)--(10).

This file formalizes the construction:

* `choi_wernerPlus` / `choi_wernerMinus`: the Choi matrices of the
  Werner--Holevo channels are `(1 + F)/(d + 1)` and `(1 - F)/(d - 1)`
  (p. 4, Eq. (7));
* `virtualCombChoi`: the Choi operator of the virtual 1-slot comb
  `C̃ = F_{A'A} ⊗ F_{BB'} + 1/(d_A+1) 1 - d_A/(d_A+1)(F_{A'A} ⊗ 1_{BB'})`
  (p. 4, Eq. (9), second equality);
* `quasiCoeffOne`, `quasiCoeffTwo`, `quasiCoeffThree` and
  `quasiCoefficients_sum_one`: the quasi-probability coefficients
  `(d_B+1)/2`, `(d_A-1)(d_B-1)/2`, `-d_A(d_B-1)/2` of Eq. (9) sum to one,
  which is what makes `C̃` a *virtual* comb (Eq. (3));
* `linkProduct`: the comb link product (the contraction
  `Tr_{AB}[C̃ (N^T_{AB} ⊗ 1_{A'B'})]` of Eq. (10));
* `link_virtualComb`: Eq. (10), the virtual comb sends the Choi matrix of
  `N` to its transpose (the Choi matrix of `N*`);
* `choi_conjMap`: the Choi matrix of the complex conjugate channel `N*` is
  the transpose of the Choi matrix of `N`;
* `source_theorem3`: for every CPTP channel `N`, the virtual comb acts as the
  complex conjugate: `linkProduct C̃ (choi N)ᵀ = choi (N*)`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.PetzRecovery26.VirtualAdjoint

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Linearity of the Choi matrix and Choi matrices of Werner--Holevo channels -/

/-- The Choi matrix construction is additive. -/
theorem choi_add (M N : MatrixMap A A ℂ) :
    (M + N).choi_matrix = M.choi_matrix + N.choi_matrix := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [MatrixMap.choi_matrix, Matrix.add_apply]

/-- The Choi matrix construction commutes with subtraction. -/
theorem choi_sub (M N : MatrixMap A A ℂ) :
    (M - N).choi_matrix = M.choi_matrix - N.choi_matrix := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [MatrixMap.choi_matrix, Matrix.sub_apply]

/-- The Choi matrix construction is complex-linear. -/
theorem choi_smul (c : ℂ) (M : MatrixMap A A ℂ) :
    (c • M).choi_matrix = c • M.choi_matrix := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [MatrixMap.choi_matrix, Matrix.smul_apply, smul_eq_mul]

/-- Entrywise complex conjugation does not transpose indices:
`conj(single i j c) = single i j (conj c)`. -/
theorem eConj_single (i : A) (j : B) (c : ℂ) :
    eConj (Matrix.single i j c) = Matrix.single i j (star c) := by
  ext x y
  simp only [eConj_apply, Matrix.single, Matrix.of_apply]
  by_cases h : i = x ∧ j = y
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]; simp

/-- Unfolding lemma for `traceScalarMap`. -/
@[simp] theorem traceScalarMap_apply (c : ℂ) (X : Matrix A A ℂ) :
    traceScalarMap c X = c • ((X.trace : ℂ) • (1 : Matrix A A ℂ)) := rfl

/-- The Choi matrix of `X ↦ c • (Tr X • 1)` is `c` times the identity. -/
theorem choi_traceScalarMap (c : ℂ) :
    (traceScalarMap (A := A) c).choi_matrix = c • (1 : Matrix (A × A) (A × A) ℂ) := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp only [MatrixMap.choi_matrix, traceScalarMap_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hb : b = b'
  · subst hb
    by_cases ha : a = a'
    · subst ha
      simp
    · have h1 : (b, a) ≠ (b, a') := fun h => ha (Prod.mk.inj h).2
      rw [if_neg h1, Matrix.trace_single_eq_of_ne a a' (1 : ℂ) ha]
      simp
  · have h1 : (b, a) ≠ (b', a') := fun h => hb (Prod.mk.inj h).1
    rw [if_neg hb, if_neg h1]
    simp

/-- Eq. (7), p. 4: the Choi matrix of `W_d^+` is `(1 + F)/(d+1)`. -/
theorem choi_wernerPlus :
    (wernerPlus : MatrixMap A A ℂ).choi_matrix =
      (((Fintype.card A : ℂ) + 1)⁻¹) • (1 + (flip : Matrix (A × A) (A × A) ℂ)) := by
  rw [wernerPlus, choi_add, choi_smul, choi_traceScalarMap, choi_transposeMap]
  rw [smul_add]

/-- Eq. (7), p. 4: the Choi matrix of `W_d^-` is `(1 - F)/(d-1)`. -/
theorem choi_wernerMinus :
    (wernerMinus : MatrixMap A A ℂ).choi_matrix =
      (((Fintype.card A : ℂ) - 1)⁻¹) • (1 - (flip : Matrix (A × A) (A × A) ℂ)) := by
  rw [wernerMinus, choi_sub, choi_smul, choi_traceScalarMap, choi_transposeMap]
  rw [smul_sub]

/-! ## The virtual comb of Theorem 3 (Eq. (9)) -/

/-- The Choi operator of the 1-slot virtual comb of Theorem 3 (p. 4, Eq. (9),
second equality):
`C̃ = F_{A'A} ⊗ F_{BB'} + 1/(d_A+1) 1 - d_A/(d_A+1)(F_{A'A} ⊗ 1_{BB'})`. -/
def virtualCombChoi : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ :=
  Matrix.kronecker (flip : Matrix (A × A) (A × A) ℂ) (flip : Matrix (B × B) (B × B) ℂ)
    + ((Fintype.card A : ℂ) + 1)⁻¹ •
        (1 : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ)
    - ((Fintype.card A : ℂ) / ((Fintype.card A : ℂ) + 1)) •
        Matrix.kronecker (flip : Matrix (A × A) (A × A) ℂ)
          (1 : Matrix (B × B) (B × B) ℂ)

/-- First quasi-probability coefficient of Eq. (9): `(d_B + 1)/2`. -/
def quasiCoeffOne : ℂ := ((Fintype.card B : ℂ) + 1) / 2

/-- Second quasi-probability coefficient of Eq. (9): `(d_A - 1)(d_B - 1)/2`. -/
def quasiCoeffTwo : ℂ := ((Fintype.card A : ℂ) - 1) * ((Fintype.card B : ℂ) - 1) / 2

/-- Third quasi-probability coefficient of Eq. (9): `-d_A(d_B - 1)/2`. -/
def quasiCoeffThree : ℂ := -((Fintype.card A : ℂ) * ((Fintype.card B : ℂ) - 1)) / 2

/-- The quasi-probability coefficients in Eq. (9) sum to one, as required for a
virtual comb in Eq. (3). -/
theorem quasiCoefficients_sum_one :
    quasiCoeffOne (B := B) + quasiCoeffTwo (A := A) (B := B) +
      quasiCoeffThree (A := A) (B := B) = 1 := by
  simp only [quasiCoeffOne, quasiCoeffTwo, quasiCoeffThree]
  ring

/-! ## The comb link product (Eq. (10)) -/

/-- The comb link product of a 1-slot supermap Choi operator
`C : L(A' A B B')` with the Choi matrix `Nt : L(B A)` (the matrix convention
`N.choi_matrix` orders the output `B` before the input `A`):
`Tr_{AB}[C (Nt ⊗ 1_{A'B'})]` in the ordered basis of Eq. (10). -/
def linkProduct (C : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ)
    (Nt : Matrix (B × A) (B × A) ℂ) : Matrix (B × A) (B × A) ℂ :=
  fun (b', a') (b'', a'') =>
    ∑ a : A, ∑ b : B, ∑ α : A, ∑ β : B,
      Nt (b, a) (β, α) * C ((a', α), (β, b')) ((a'', a), (b, b''))

/-- The trace-preserving diagonal identity for Choi matrices: for a
trace-preserving map, one column of the diagonal `∑_b choi(N)[(b,a),(b,a)]`
equals one (this is `Tr N(|a⟩⟨a|) = 1`, the `a = a'` instance of the
trace-preservation row-sum identity used in Eq. (10)). -/
theorem choi_diag_row_sum (N : MatrixMap A B ℂ) (hTP : N.IsTracePreserving) (a : A) :
    ∑ b : B, N.choi_matrix (b, a) (b, a) = 1 := by
  have h : ∑ b : B, N.choi_matrix (b, a) (b, a) = (N (Matrix.single a a 1)).trace := by
    simp [MatrixMap.choi_matrix, Matrix.trace, Matrix.single]
  rw [h, hTP]
  simp [Matrix.trace, Matrix.single]

/-- Linearity of the link product in its first argument (addition). -/
theorem linkProduct_add (C C' : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ)
    (Nt : Matrix (B × A) (B × A) ℂ) :
    linkProduct (C + C') Nt = linkProduct C Nt + linkProduct C' Nt := by
  ext x y
  simp only [linkProduct, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- Linearity of the link product in its first argument (scalar multiplication). -/
theorem linkProduct_smul (c : ℂ)
    (C : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ)
    (Nt : Matrix (B × A) (B × A) ℂ) :
    linkProduct (c • C) Nt = c • linkProduct C Nt := by
  ext x y
  simp only [linkProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1 with a; congr 1 with b; congr 1 with al; congr 1 with be
  ring

/-- Linearity of the link product in its first argument (subtraction). -/
theorem linkProduct_sub (C C' : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ)
    (Nt : Matrix (B × A) (B × A) ℂ) :
    linkProduct (C - C') Nt = linkProduct C Nt - linkProduct C' Nt := by
  ext x y
  simp only [linkProduct, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Contracting the identity comb operator with `Nt` gives `Tr(Nt)` times the
output identity: the contribution of the `1_{A'ABB'}` summand of Eq. (9). -/
theorem linkProduct_one (Nt : Matrix (B × A) (B × A) ℂ) :
    linkProduct (A := A) (B := B)
      (1 : Matrix ((A × A) × (B × B)) ((A × A) × (B × B)) ℂ) Nt =
      (Nt.trace) • (1 : Matrix (B × A) (B × A) ℂ) := by
  ext ⟨b', a'⟩ ⟨b'', a''⟩
  simp only [linkProduct, Matrix.one_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag,
    smul_eq_mul, Prod.mk.injEq]
  by_cases h1 : a' = a''
  · by_cases h2 : b' = b''
    · subst h1; subst h2
      simp only [true_and, and_true, and_self, ite_true, mul_one, ite_and, mul_ite, mul_zero]
      trans ∑ x : A, ∑ x1 : B, ∑ x3 : B,
        (if x3 = x1 then Nt (x1, x) (x3, x) else 0)
      · congr 1 with x
        congr 1 with x1
        rw [Finset.sum_eq_single x]
        · simp
        · intro x2 _ hx2; simp [hx2]
        · intro hx; simp at hx
      · simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [Finset.sum_comm]
        rw [← Finset.sum_product', Finset.univ_product_univ]
    · simp [h2]
  · simp [h1]

/-- Contracting `F_{A'A} ⊗ F_{BB'}` with `Nt` returns `Nt`: the first summand
of Eq. (9). -/
theorem linkProduct_kron_flip_flip (Nt : Matrix (B × A) (B × A) ℂ) :
    linkProduct (A := A) (B := B)
      (Matrix.kronecker (flip : Matrix (A × A) (A × A) ℂ)
        (flip : Matrix (B × B) (B × B) ℂ)) Nt = Nt := by
  ext ⟨b', a'⟩ ⟨b'', a''⟩
  simp only [linkProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, flip_apply]
  rw [Finset.sum_eq_single a']
  · rw [Finset.sum_eq_single b']
    · rw [Finset.sum_eq_single a'']
      · rw [Finset.sum_eq_single b'']
        · simp
        · intro x _ hx; simp [hx]
        · intro h; simp at h
      · intro x _ hx; simp [hx]
      · intro h; simp at h
    · intro x _ hx
      have h : ¬ (b' = x) := by simpa [eq_comm] using hx
      simp [h]
    · intro h; simp at h
  · intro x _ hx
    have h : ¬ (a' = x) := by simpa [eq_comm] using hx
    simp [h]
  · intro h; simp at h

/-- Contracting `F_{A'A} ⊗ 1_{BB'}` with `Nt` gives the output identity once
`Nt` has the partial-trace normalisation of a channel Choi matrix. -/
theorem linkProduct_kron_flip_one (Nt : Matrix (B × A) (B × A) ℂ)
    (hpartial : ∀ a a' : A, ∑ b : B, Nt (b, a) (b, a') = if a = a' then 1 else 0) :
    linkProduct (A := A) (B := B)
      (Matrix.kronecker (flip : Matrix (A × A) (A × A) ℂ)
        (1 : Matrix (B × B) (B × B) ℂ)) Nt = 1 := by
  ext ⟨b', a'⟩ ⟨b'', a''⟩
  simp only [linkProduct, Matrix.kronecker, Matrix.kroneckerMap_apply, flip_apply,
    Matrix.one_apply]
  by_cases hb : b' = b''
  · subst hb
    simp only [Prod.mk.injEq, and_true, true_and, ite_and, mul_ite, mul_one, mul_zero]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single a']
    · simp only [if_true]
      simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hpartial a' a''
    · intro x _ hx
      have h : ¬ (a' = x) := by simpa [eq_comm] using hx
      simp [h]
    · intro h; simp at h
  · simp [hb]

/-- The partial-trace normalisation used by `linkProduct_kron_flip_one`, derived
from trace preservation of the channel `N`. -/
theorem linkProduct_kron_flip_one_choi (N : MatrixMap A B ℂ)
    (hTP : N.IsTracePreserving) :
    linkProduct (A := A) (B := B)
      (Matrix.kronecker (flip : Matrix (A × A) (A × A) ℂ)
        (1 : Matrix (B × B) (B × B) ℂ)) ((N.choi_matrix)ᵀ) = 1 := by
  apply linkProduct_kron_flip_one
  intro a a'
  have h := (MatrixMap.IsTracePreserving_iff_trace_choi N).mp hTP
  have h' := congrArg (fun M : Matrix A A ℂ => M a' a) h
  simpa [Matrix.traceLeft, Matrix.one_apply, Matrix.transpose_apply, eq_comm] using h'

/-- Eq. (10), p. 4: contracting the virtual comb `C̃` of Eq. (9) with the
transposed Choi matrix of a trace-preserving channel gives back that matrix. -/
theorem link_virtualComb (N : MatrixMap A B ℂ) (hTP : N.IsTracePreserving) :
    linkProduct (virtualCombChoi (A := A) (B := B)) ((N.choi_matrix)ᵀ) =
      (N.choi_matrix)ᵀ := by
  unfold virtualCombChoi
  rw [linkProduct_sub, linkProduct_add, linkProduct_smul, linkProduct_smul]
  rw [linkProduct_kron_flip_flip, linkProduct_one,
    linkProduct_kron_flip_one_choi N hTP]
  have htrace : ((N.choi_matrix)ᵀ).trace = (Fintype.card A : ℂ) := by
    rw [Matrix.trace_transpose, MatrixMap.IsTracePreserving.trace_choi hTP]
    simp
  rw [htrace, smul_smul]
  have hcoef : (((Fintype.card A : ℂ) + 1)⁻¹ * (Fintype.card A : ℂ))
      = (Fintype.card A : ℂ) / ((Fintype.card A : ℂ) + 1) := by
    have hd : ((Fintype.card A : ℂ) + 1) ≠ 0 := by
      have hpos : (0 : ℂ) < (Fintype.card A : ℂ) + 1 := by
        exact_mod_cast Nat.succ_pos (Fintype.card A)
      exact ne_of_gt hpos
    field_simp
  rw [hcoef]
  abel

/-! ## The Choi matrix of the complex conjugate channel -/

/-- The Choi matrix of the complex conjugate `N*` is the transpose of the Choi
matrix of `N` (for Hermitian Choi matrix, e.g. for completely positive `N`). -/
theorem choi_conjMap (M : MatrixMap A B ℂ) (hM : M.choi_matrix.IsHermitian) :
    (conjMap M).choi_matrix = (M.choi_matrix)ᵀ := by
  ext ⟨b1, a1⟩ ⟨b2, a2⟩
  simp only [MatrixMap.choi_matrix, conjMap_apply, eConj_apply, eConj_single, star_one,
    Matrix.transpose_apply]
  exact hM.apply ⟨b2, a2⟩ ⟨b1, a1⟩

/-! ## Theorem 3 -/

/-- **Theorem 3 (Virtual complex conjugation), p. 4.** The 1-slot virtual comb
`C̃` of Eq. (9) universally implements the complex conjugate: for every CPTP
channel `N : A → B`, contracting `C̃` with `N` gives the Choi matrix of `N*`. -/
theorem source_theorem3 (N : MatrixMap A B ℂ) (hCP : N.IsCompletelyPositive)
    (hTP : N.IsTracePreserving) :
    linkProduct (virtualCombChoi (A := A) (B := B)) ((N.choi_matrix)ᵀ) =
      (conjMap N).choi_matrix := by
  rw [choi_conjMap N ((MatrixMap.choi_PSD_iff_CP_map N).mp hCP).1]
  exact link_virtualComb N hTP

end Qatlib.Papers.PetzRecovery26.VirtualAdjoint
