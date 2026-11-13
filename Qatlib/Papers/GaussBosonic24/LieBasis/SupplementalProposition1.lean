/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign

set_option backward.isDefEq.respectTransparency false

/-!
# Pauli Basis for the Symplectic Algebra

This module formalizes Supplemental Proposition 1 (Appendix A.2, Eq. (A27)) of
Barthe et al. on gate-based quantum simulation of Gaussian bosonic circuits on
exponentially many modes. For `M = 2 ^ n` modes, the phased Pauli family
`Bsp(M, ℝ) = i {Y ⊗ Ps} ∪ i {I ⊗ Pa} ∪ {X ⊗ Ps} ∪ {Z ⊗ Ps}` — where `Ps` and
`Pa` range over `n`-qubit Pauli strings with an even or odd number of `Y`
letters — consists of real symplectic `2M × 2M` operators satisfying
`Aᵀ Ω = -Ω A` for `Ω = iY ⊗ I_M`, is Hilbert-Schmidt orthogonal with diagonal
norm `2 ^ (n + 1)`, and has cardinality `2 ^ n * (2 ^ (n + 1) + 1) = M (2M + 1)`.

## Main statements

* `memB_orthogonal`: distinct elements of `MemB` are Hilbert-Schmidt orthogonal.
* `memB_self_trace`: every phased Pauli operator has Hilbert-Schmidt norm
  squared `2 ^ (n + 1)`.
* `memB_real` and `memB_symplectic`: every element of `MemB` is real
  (`(op p)ᴴ = (op p)ᵀ`) and satisfies the symplectic relation `InSp n (op p)`.
* `card_memB`: the family `MemB n` has cardinality `2 ^ n * (2 ^ (n + 1) + 1)`.
* `supplementalProposition1`: combined statement of Supplemental Proposition 1.

## References

* [Barthe et al., 2025][BartheEtAl2025], Supplemental Information, Appendix A.2,
  Supplemental Proposition 1, Eq. (A27).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.GaussBosonic24.LieBasis

/-- The number of `Y` letters in a Pauli word. -/
def yPar {n : ℕ} (w : PauliWord n) : ℕ := ∑ i, if w i = .Y then 1 else 0

/-- A Pauli string is symmetric (`Ps`, real) if it contains an even number of
`Y` letters. -/
def IsSymWord {n : ℕ} (w : PauliWord n) : Prop := Even (yPar w)

/-- A Pauli string is antisymmetric (`Pa`, purely imaginary) if it contains an
odd number of `Y` letters. -/
def IsAntiWord {n : ℕ} (w : PauliWord n) : Prop := Odd (yPar w)

/-- The register-qubit part (`Ps` or `Pa`) of a `PauliElem` on `n + 1` qubits:
the word on qubits `1, …, n`, with qubit `0` as the symplectic qubit. -/
def tailWord {n : ℕ} (p : PauliElem (n+1)) : PauliWord n := fun i => p.word i.succ

/-- Membership in the four families of Eq. (A27) for `M = 2 ^ n` modes:
* `i {Y ⊗ Ps}`: symplectic letter `Y`, phase `i`, symmetric register word;
* `i {I ⊗ Pa}`: symplectic letter `I`, phase `i`, antisymmetric register word;
* `{X ⊗ Ps}`: symplectic letter `X`, phase `1`, symmetric register word;
* `{Z ⊗ Ps}`: symplectic letter `Z`, phase `1`, symmetric register word. -/
def MemB (n : ℕ) (p : PauliElem (n+1)) : Prop :=
  (p.phase = 1 ∧ p.word 0 = .Y ∧ IsSymWord (tailWord p)) ∨
  (p.phase = 1 ∧ p.word 0 = .I ∧ IsAntiWord (tailWord p)) ∨
  (p.phase = 0 ∧ p.word 0 = .X ∧ IsSymWord (tailWord p)) ∨
  (p.phase = 0 ∧ p.word 0 = .Z ∧ IsSymWord (tailWord p))

/-- The symplectic form `Ω = iY ⊗ I_M` (Eq. (A7)) in the Pauli-string model. -/
def omegaElem (n : ℕ) : PauliElem (n+1) := ⟨Fin.cons .Y (fun _ => .I), 1⟩

/-- Symplectic Lie algebra relation `Aᵀ Ω = -Ω A` in the standard `2M × 2M`
representation. -/
def InSp (n : ℕ) (A : Matrix (Reg (n+1)) (Reg (n+1)) ℂ) : Prop :=
  Aᵀ * op (omegaElem n) = -(op (omegaElem n) * A)

/-! ## Elementary Pauli-word facts -/

/-- Per-letter Pauli multiplication is trivial if and only if the letters are equal. -/
theorem pauliMul1_eq_I_iff (a b : Pauli1) : pauliMul1 a b = .I ↔ a = b := by
  cases a <;> cases b <;> simp [pauliMul1]

/-- Two Pauli words whose letterwise products are all trivial are equal. -/
theorem word_eq_of_pauliMul1 {n : ℕ} {w v : PauliWord n}
    (h : ∀ i, pauliMul1 (w i) (v i) = .I) : w = v :=
  funext fun i => (pauliMul1_eq_I_iff (w i) (v i)).1 (h i)

/-- Distinct Pauli words differ at some site with nontrivial letterwise product. -/
theorem exists_pauliMul1_ne {n : ℕ} {p q : PauliElem n} (h : p.word ≠ q.word) :
    ∃ i, pauliMul1 (p.word i) (q.word i) ≠ .I := by
  by_contra hc
  push Not at hc
  exact h (word_eq_of_pauliMul1 hc)

/-- If the words of two phased Pauli operators have a site with nontrivial
letterwise product, their Hilbert-Schmidt inner product `tr(Aᴴ B)` vanishes. -/
theorem trace_mul_eq_zero_of_pauliMul1_ne {n : ℕ} (p q : PauliElem n)
    (h : ∃ i, pauliMul1 (p.word i) (q.word i) ≠ .I) :
    Matrix.trace ((op p)ᴴ * op q) = 0 := by
  rw [op_conjTranspose, ← op_mul]
  refine trace_op_eq_zero_of_word_ne n _ ?_
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa only [PauliElem.mul] using hi⟩

/-! ## Phase determination by the first letter -/

/-- Phase attached by Eq. (A27) to a first letter: `Y` and `I` carry `i`, while
`X` and `Z` carry `1`. -/
def phaseOfLetter (a : Pauli1) : Phase4 := if a = .Y ∨ a = .I then 1 else 0

/-- The phase of any member of `MemB` is determined by its first letter. -/
theorem memB_phase_eq_phaseOfLetter {n : ℕ} {p : PauliElem (n+1)} (hp : MemB n p) :
    p.phase = phaseOfLetter (p.word 0) := by
  rcases hp with ⟨hφ, ha, -⟩ | ⟨hφ, ha, -⟩ | ⟨hφ, ha, -⟩ | ⟨hφ, ha, -⟩ <;>
    (rw [hφ, ha]; decide)

/-- Two members of `MemB` with the same word have the same phase. -/
theorem memB_phase_eq {n : ℕ} {p q : PauliElem (n+1)} (hp : MemB n p) (hq : MemB n q)
    (h : p.word = q.word) : p.phase = q.phase := by
  rw [memB_phase_eq_phaseOfLetter hp, memB_phase_eq_phaseOfLetter hq, h]

/-- Within `MemB`, the underlying Pauli word uniquely determines the element. -/
theorem memB_eq_of_word_eq {n : ℕ} {p q : PauliElem (n+1)} (hp : MemB n p) (hq : MemB n q)
    (h : p.word = q.word) : p = q := by
  obtain ⟨w, φ⟩ := p
  obtain ⟨w', φ'⟩ := q
  simp only [PauliElem.mk.injEq]
  exact ⟨h, memB_phase_eq hp hq h⟩

/-! ## Orthogonality and normalization -/

/-- Distinct members of `MemB` are Hilbert-Schmidt orthogonal. -/
theorem memB_orthogonal {n : ℕ} {p q : PauliElem (n+1)} (hp : MemB n p) (hq : MemB n q)
    (hne : p ≠ q) : Matrix.trace ((op p)ᴴ * op q) = 0 := by
  refine trace_mul_eq_zero_of_pauliMul1_ne p q ?_
  refine exists_pauliMul1_ne ?_
  intro hw
  exact hne (memB_eq_of_word_eq hp hq hw)

/-- Every `(n + 1)`-qubit phased Pauli operator has `tr(Aᴴ A) = 2 ^ (n + 1)`. -/
theorem memB_self_trace {n : ℕ} (p : PauliElem (n+1)) :
    Matrix.trace ((op p)ᴴ * op p) = 2 ^ (n+1) := by
  have hmul : (⟨p.word, -p.phase⟩ : PauliElem (n+1)).mul p = 1 := by
    have hsum : ∑ i, pauliMulPhase (p.word i) (p.word i) = 0 :=
      Finset.sum_eq_zero fun i _ => pauliMulPhase_self (p.word i)
    have hone : (1 : PauliElem (n+1)) = ⟨fun _ => Pauli1.I, 0⟩ := rfl
    show (⟨fun i => pauliMul1 (p.word i) (p.word i),
      -p.phase + p.phase + ∑ i, pauliMulPhase (p.word i) (p.word i)⟩ : PauliElem (n+1)) = 1
    rw [funext fun i => pauliMul1_self (p.word i), hsum, hone, PauliElem.mk.injEq]
    exact ⟨rfl, by abel⟩
  rw [op_conjTranspose, ← op_mul, hmul, op_one, Matrix.trace_one, card_reg]
  simp

/-! ## Symplectic property and cardinality -/

/-- Phased Pauli operators with equal words and phases differing by `2` sum to zero. -/
theorem op_add_eq_zero_of_phase_shift {n : ℕ} {X Y : PauliElem n} (hw : X.word = Y.word)
    (hφ : X.phase = Y.phase + 2) : op X + op Y = 0 := by
  have hpow : (Complex.I : ℂ) ^ X.phase.val = - (Complex.I ^ Y.phase.val) := by
    rw [hφ, I_pow_val_add, zmod4_val_two, pow_two, Complex.I_mul_I, mul_neg_one]
  simp only [op, hw, hpow, neg_smul, neg_add_cancel]

/-- Letterwise Pauli multiplication with `Y` has symmetric output letter. -/
theorem pauliMul1_swap_Y (a : Pauli1) : pauliMul1 a .Y = pauliMul1 .Y a := by
  cases a <;> rfl

/-- The Pauli products corresponding to `Aᴴ Ω` and `Ω A` share the same word. -/
theorem mul_omega_word {n : ℕ} (p : PauliElem (n+1)) :
    ((⟨p.word, -p.phase⟩ : PauliElem (n+1)).mul (omegaElem n)).word
      = ((omegaElem n).mul p).word := by
  funext i
  obtain h | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · subst h
    simpa [PauliElem.mul, omegaElem, Fin.cons_zero] using pauliMul1_swap_Y (p.word 0)
  · simpa [PauliElem.mul, omegaElem, Fin.cons_succ] using
      (pauliMul1_right_I (p.word j.succ)).trans (pauliMul1_I (p.word j.succ)).symm

/-- For every member of `MemB`, the phases of `Aᴴ Ω` and `Ω A` differ by `2`. -/
theorem mul_omega_phase_add_two {n : ℕ} {p : PauliElem (n+1)} (hp : MemB n p) :
    ((⟨p.word, -p.phase⟩ : PauliElem (n+1)).mul (omegaElem n)).phase
      = ((omegaElem n).mul p).phase + 2 := by
  have hI1 : ∀ a : Pauli1, pauliMulPhase a .I = 0 := pauliMulPhase_right_I
  have hI2 : ∀ a : Pauli1, pauliMulPhase .I a = 0 := pauliMulPhase_I
  rcases hp with ⟨hφ, ha, -⟩ | ⟨hφ, ha, -⟩ | ⟨hφ, ha, -⟩ | ⟨hφ, ha, -⟩ <;>
    simp only [PauliElem.mul, omegaElem, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      hφ, ha, hI1, hI2, Finset.sum_const_zero] <;>
    decide

/-- Hermitian form of the symplectic relation: `(op p)ᴴ * Ω + Ω * op p = 0`. -/
theorem memB_symplectic_hermitian {n : ℕ} {p : PauliElem (n+1)} (hp : MemB n p) :
    (op p)ᴴ * op (omegaElem n) + op (omegaElem n) * op p = 0 := by
  simp only [op_conjTranspose, ← op_mul]
  exact op_add_eq_zero_of_phase_shift (mul_omega_word p) (mul_omega_phase_add_two hp)

private lemma P1_transpose_entry (a : Pauli1) (x y : Bool) :
    P1 a y x = (-1 : ℂ) ^ (if a = .Y then 1 else 0 : ℕ) * P1 a x y := by
  cases a <;> cases x <;> cases y <;> simp [P1]

private lemma pauliWordOp_transpose {m : ℕ} (w : PauliWord m) :
    (pauliWordOp m w)ᵀ = (-1 : ℂ) ^ yPar w • pauliWordOp m w := by
  rw [pauliWordOp_eq]
  ext x y
  change (∏ i, P1 (w i) (y i) (x i)) =
    (-1 : ℂ) ^ yPar w * ∏ i, P1 (w i) (x i) (y i)
  calc
    _ = ∏ i, ((-1 : ℂ) ^ (if w i = .Y then 1 else 0 : ℕ) *
        P1 (w i) (x i) (y i)) :=
      Finset.prod_congr rfl fun i _ => P1_transpose_entry (w i) (x i) (y i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; rfl

private lemma yPar_head_tail {n : ℕ} (p : PauliElem (n+1)) :
    yPar p.word = (if p.word 0 = .Y then 1 else 0) + yPar (tailWord p) := by
  exact Fin.sum_univ_succ _

/-- Every operator in `MemB` has real entries: its conjugate transpose equals
its transpose. -/
theorem memB_real {n : ℕ} {p : PauliElem (n+1)} (hp : MemB n p) :
    (op p)ᴴ = (op p)ᵀ := by
  rw [op_conjTranspose, op, op, Matrix.transpose_smul, pauliWordOp_transpose,
    smul_smul]
  congr 1
  rw [yPar_head_tail]
  rcases hp with ⟨hφ, ha, hu⟩ | ⟨hφ, ha, hu⟩ | ⟨hφ, ha, hu⟩ | ⟨hφ, ha, hu⟩
  · rw [hφ, ha, ite_eq_left rfl, pow_add, hu.neg_one_pow]
    simp [zmod4_val_one]
  · rw [hφ, ha, ite_eq_right (by decide), zero_add, hu.neg_one_pow]
    simp [zmod4_val_one]
  · rw [hφ, ha, ite_eq_right (by decide), zero_add, hu.neg_one_pow]
    simp
  · rw [hφ, ha, ite_eq_right (by decide), zero_add, hu.neg_one_pow]
    simp

/-- Every operator in `MemB` satisfies the symplectic relation `Aᵀ Ω = -Ω A`. -/
theorem memB_symplectic {n : ℕ} {p : PauliElem (n+1)} (hp : MemB n p) :
    InSp n (op p) := by
  have h := memB_symplectic_hermitian hp
  rw [memB_real hp] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma yPar_cons {n : ℕ} (a : Pauli1) (w : PauliWord n) :
    yPar (Fin.cons a w) = (if a = .Y then 1 else 0) + yPar w := by
  simp only [yPar, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Swapping `I` and `Y` on the symplectic qubit identifies the four families
with the symmetric words on the full register. -/
private def swapHead {n : ℕ} (w : PauliWord (n+1)) : PauliWord (n+1) :=
  Fin.cons (Equiv.swap .I .Y (w 0)) (fun i => w i.succ)

private lemma swapHead_swapHead {n : ℕ} (w : PauliWord (n+1)) :
    swapHead (swapHead w) = w := by
  simp only [swapHead, Fin.cons_zero, Fin.cons_succ, Equiv.swap_apply_self]
  exact Fin.cons_self_tail w

private lemma memB_iff_swapHead {n : ℕ} (p : PauliElem (n+1)) :
    MemB n p ↔ p.phase = phaseOfLetter (p.word 0) ∧ IsSymWord (swapHead p.word) := by
  unfold MemB phaseOfLetter IsSymWord IsAntiWord swapHead tailWord
  rw [yPar_cons]
  cases ha : p.word 0 <;>
    simp [Equiv.swap_apply_def, Nat.even_add]

private def memBEquivSym (n : ℕ) :
    {p : PauliElem (n+1) // MemB n p} ≃ {w : PauliWord (n+1) // IsSymWord w} where
  toFun p := ⟨swapHead p.1.word, ((memB_iff_swapHead p.1).mp p.2).2⟩
  invFun w := ⟨⟨swapHead w.1, phaseOfLetter (swapHead w.1 0)⟩,
    (memB_iff_swapHead _).mpr ⟨rfl, by simpa only [swapHead_swapHead] using w.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply memB_eq_of_word_eq ((memB_iff_swapHead _).mpr ⟨rfl, by
      simpa only [swapHead_swapHead] using ((memB_iff_swapHead p.1).mp p.2).2⟩) p.2
    exact swapHead_swapHead p.1.word
  right_inv w := Subtype.ext (swapHead_swapHead w.1)

private lemma twice_card_symWord (m : ℕ) :
    2 * Nat.card {w : PauliWord m // IsSymWord w} = 4 ^ m + 2 ^ m := by
  classical
  have hletters : (Finset.univ : Finset Pauli1) = {.I, .X, .Y, .Z} := by decide
  have hsign : (∑ w : PauliWord m, (-1 : ℤ) ^ yPar w) = 2 ^ m := by
    calc
      _ = ∑ w : PauliWord m, ∏ i, (if w i = .Y then (-1 : ℤ) else 1) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [yPar, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro i _
        split_ifs <;> simp
      _ = (∑ a : Pauli1, if a = .Y then (-1 : ℤ) else 1) ^ m :=
        (Fintype.sum_pow (fun a : Pauli1 => if a = .Y then (-1 : ℤ) else 1) m).symm
      _ = _ := by simp [hletters]
  have hpoint (w : PauliWord m) :
      (2 : ℤ) * (if IsSymWord w then 1 else 0) = 1 + (-1 : ℤ) ^ yPar w := by
    rcases Nat.even_or_odd (yPar w) with h | h
    · rw [h.neg_one_pow]
      simp [IsSymWord, h]
    · rw [h.neg_one_pow]
      simp [IsSymWord, Nat.not_even_iff_odd.mpr h]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun w _ => hpoint w)
  have hcard : Fintype.card (PauliWord m) = 4 ^ m := by
    rw [Fintype.card_fun, Fintype.card_fin]
    rfl
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_boole, hsign, hcard] at hsum
  rw [← Fintype.card_subtype] at hsum
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hsum

/-- Cardinality of the symplectic Pauli basis family for `M = 2 ^ n` modes:
`|MemB n| = 2 ^ n * (2 ^ (n + 1) + 1)`. -/
theorem card_memB (n : ℕ) :
    Nat.card {p : PauliElem (n+1) // MemB n p} = 2 ^ n * (2 ^ (n+1) + 1) := by
  rw [Nat.card_congr (memBEquivSym n)]
  have h := twice_card_symWord (n+1)
  have hpow : 4 ^ (n+1) = (2 ^ (n+1)) ^ 2 := by
    rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  rw [hpow] at h
  rw [show 2 ^ (n+1) = 2 ^ n * 2 from pow_succ 2 n] at h ⊢
  nlinarith

/-- **Supplemental Proposition 1** (Eq. (A27)): the phased Pauli family `MemB n`
consists of symplectic operators (`Aᵀ Ω = -Ω A`), is Hilbert-Schmidt orthogonal
with normalization `2 ^ (n + 1)`, and has cardinality
`2 ^ n * (2 ^ (n + 1) + 1) = M (2M + 1)`. -/
theorem supplementalProposition1 (n : ℕ) :
    (∀ p : PauliElem (n+1), MemB n p → InSp n (op p)) ∧
    (∀ p q : PauliElem (n+1), MemB n p → MemB n q → p ≠ q →
      Matrix.trace ((op p)ᴴ * op q) = 0) ∧
    (∀ p : PauliElem (n+1), Matrix.trace ((op p)ᴴ * op p) = 2 ^ (n+1)) ∧
    (Nat.card {p : PauliElem (n+1) // MemB n p} = 2 ^ n * (2 ^ (n+1) + 1)) :=
  ⟨fun _ hp => memB_symplectic hp,
    fun _ _ hp hq hne => memB_orthogonal hp hq hne,
    memB_self_trace,
    card_memB n⟩

end Qatlib.Papers.GaussBosonic24.LieBasis
