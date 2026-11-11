/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7 of arXiv:1311.6474v1

Source: Martin Schwarz, Toby S. Cubitt, Frank Verstraete,
*An Information-Theoretic Proof of the Constructive Commutative Quantum Lovász Local Lemma*,
arXiv:1311.6474v1, Lemma 7 and Eq. (39) (Appendix A.1, p. 12).

The lemma is the special case of the strong converse of the typical subspace theorem that the
paper needs: for a projection `Q` onto a subspace of the `n + m` qubit space whose dimension is
at most `2 ^ (n * R)` with `R < 1`, the overlap of `Q` with the completely mixed state on the
first `n` qubits tensored with the pure ancilla state `(|0⟩⟨0|) ^ m` is at most `2 ^ (-n + n * R)`.

The paper reads the bound as three chained inequalities

  `Tr[Q (𝟙 / 2 ^ n ⊗ (|0⟩⟨0|) ^ m)] ≤ Tr[Q (𝟙 / 2 ^ n)] = 2 ^ (-n) Tr[Q] ≤ 2 ^ (-n + n R)`,

and this file formalises all three: the first two in `trace_mul_mixed_pure_le` and the last in
`lemma7_rank_bound` (integer rank bound) and `lemma7_rpow_bound` (the paper's real exponent form).

The two structural facts used are that the ancilla factor `|0⟩⟨0|` is a contraction with respect
to the identity (`sum_pure_le_sum_all`) and that the diagonal entries of a projection are
nonnegative reals (`diag_re_eq_sum_normSq`).
-/

namespace Qatlib.Papers.LovaszLemma13.MainResults

open Matrix

open scoped Kronecker BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Diagonal entries of a projection -/

section Diagonal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

omit [DecidableEq ι] [DecidableEq α] in
/-- A diagonal entry of a Hermitian projection is the sum of the squared moduli of the row:
`Q v v = ∑ u, Q v u * Q u v` by idempotence, and `Q u v = conj (Q v u)` by hermiticity.  In
particular every diagonal entry is a nonnegative real. -/
lemma diag_re_eq_sum_normSq (Q : Matrix (ι × α) (ι × α) ℂ) (hQ : Q.IsHermitian)
    (hQ2 : Q * Q = Q) (v : ι × α) :
    (Q v v).re = ∑ u, Complex.normSq (Q v u) := by
  have hsplit : (Q * Q) v v = ∑ u, Q v u * Q u v := Matrix.mul_apply ..
  rw [hQ2] at hsplit
  have hconj : ∀ u, Q u v = star (Q v u) := by
    intro u
    have h := hQ.apply v u
    rw [← h]
    exact (star_star (Q u v)).symm
  rw [hsplit, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro u _
  rw [hconj u]
  have hmul : Q v u * star (Q v u) = (Complex.normSq (Q v u) : ℂ) := by
    simp only [Complex.star_def]
    exact Complex.mul_conj (Q v u)
  rw [hmul, Complex.ofReal_re]

omit [DecidableEq ι] [DecidableEq α] in
/-- Diagonal entries of a Hermitian projection are nonnegative reals. -/
lemma diag_re_nonneg (Q : Matrix (ι × α) (ι × α) ℂ) (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (v : ι × α) : 0 ≤ (Q v v).re := by
  rw [diag_re_eq_sum_normSq Q hQ hQ2 v]
  exact Finset.sum_nonneg fun u _ => Complex.normSq_nonneg (Q v u)

omit [DecidableEq ι] [DecidableEq α] in
/-- The (real part of the) trace of a complex matrix is the sum of the real parts of its
diagonal entries. -/
lemma trace_re_eq_sum_diag (A : Matrix (ι × α) (ι × α) ℂ) :
    A.trace.re = ∑ v, (A v v).re := by
  rw [Matrix.trace]
  exact Complex.re_sum _ _

/-! ## The pure ancilla state and the maximally mixed state -/

/-- `|0⟩⟨0|` as a matrix entry: the rank-one projection onto the distinguished ancilla index. -/
noncomputable def pureZero (a₀ : α) : Matrix α α ℂ := Matrix.single a₀ a₀ 1

/-- The identity on the work register decomposes into its diagonal matrix units. -/
lemma one_eq_sum_single : (1 : Matrix ι ι ℂ) = ∑ w, Matrix.single w w 1 := by
  ext i j
  rw [Matrix.sum_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro w _
      by_cases hw : w = i
      · subst hw
        simp [h]
      · simp [hw]

omit [DecidableEq ι] [Fintype α] [DecidableEq α] in
/-- The Kronecker product distributes over finite sums on the left. -/
lemma sum_kronecker (f : ι → Matrix ι ι ℂ) (B : Matrix α α ℂ) :
    (∑ w, f w) ⊗ₖ B = ∑ w, f w ⊗ₖ B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

omit [Fintype α] in
/-- Tensoring the identity with `|0⟩⟨0|` gives the sum of the matrix units on the work register
with the ancilla register pinned to the distinguished index. -/
lemma one_kronecker_pureZero (a₀ : α) :
    (1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀
      = ∑ w, Matrix.single (w, a₀) (w, a₀) (1 : ℂ) := by
  rw [one_eq_sum_single, sum_kronecker]
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [pureZero, Matrix.single_kronecker_single, mul_one]

/-- Multiplying a matrix by `𝟙 ⊗ |0⟩⟨0|` and taking the trace picks out the diagonal entries on
the ancilla-zero slice. -/
lemma trace_mul_one_kronecker_pureZero (Q : Matrix (ι × α) (ι × α) ℂ) (a₀ : α) :
    (Q * ((1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀)).trace = ∑ w, Q (w, a₀) (w, a₀) := by
  rw [one_kronecker_pureZero, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [Matrix.trace_mul_comm, Matrix.trace_single_mul]
  simp

/-- Summing the diagonal entries over the ancilla-zero slice cannot exceed the full diagonal sum,
because all diagonal entries of a projection are nonnegative. -/
lemma sum_pure_le_sum_all (Q : Matrix (ι × α) (ι × α) ℂ) (hQ : Q.IsHermitian)
    (hQ2 : Q * Q = Q) (a₀ : α) :
    ∑ w, (Q (w, a₀) (w, a₀)).re ≤ ∑ v, (Q v v).re := by
  have hinj : Set.InjOn (fun w : ι => (w, a₀)) (↑(Finset.univ : Finset ι)) := by
    intro x _ y _ hxy
    simpa using congr_arg Prod.fst hxy
  calc ∑ w, (Q (w, a₀) (w, a₀)).re
      = ∑ v ∈ Finset.univ.image (fun w : ι => (w, a₀)), (Q v v).re := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ v, (Q v v).re := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
        intro v _ _
        exact diag_re_nonneg Q hQ hQ2 v

end Diagonal

/-! ## The main inequality -/

section Main

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype α] [DecidableEq α]

/-- **Lemma 7, first two inequalities of Eq. (39).**  For a projection `Q` on the joint register
`ι × α` and a pure ancilla state `|0⟩⟨0|` on `α`, the overlap with the completely mixed state on
the work register tensored with the pure ancilla state is at most `1 / dim ι` times the trace of
`Q`, i.e. `Tr[Q (𝟙 / d ⊗ |0⟩⟨0|)] ≤ Tr[Q (𝟙 / d)] = (1 / d) Tr[Q]`. -/
theorem trace_mul_mixed_pure_le (Q : Matrix (ι × α) (ι × α) ℂ) (hQ : Q.IsHermitian)
    (hQ2 : Q * Q = Q) (a₀ : α) :
    (Q * (((Fintype.card ι : ℂ)⁻¹) • ((1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀))).trace.re
      ≤ Q.trace.re / Fintype.card ι := by
  have hcard : ((Fintype.card ι : ℝ)) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast hpos.ne'
  have hcardR : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have htrace :
      (Q * (((Fintype.card ι : ℂ)⁻¹) • ((1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀))).trace
        = ((Fintype.card ι : ℂ)⁻¹) * (Q * ((1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀)).trace := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hcast : ((Fintype.card ι : ℂ)⁻¹) = ((d⁻¹ : ℝ) : ℂ) := by
    rw [hd, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hsum : (Q * ((1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀)).trace
      = ∑ w, Q (w, a₀) (w, a₀) := trace_mul_one_kronecker_pureZero Q a₀
  have hleft :
      (Q * (((Fintype.card ι : ℂ)⁻¹) • ((1 : Matrix ι ι ℂ) ⊗ₖ pureZero a₀))).trace.re
        = d⁻¹ * ∑ w, (Q (w, a₀) (w, a₀)).re := by
    rw [htrace, hsum, hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_sum]
    simp
  have hint : ∑ w, (Q (w, a₀) (w, a₀)).re ≤ ∑ v, (Q v v).re :=
    sum_pure_le_sum_all Q hQ hQ2 a₀
  have hdle : d = (Fintype.card ι : ℝ) := hd
  rw [hleft, hdle, trace_re_eq_sum_diag Q, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hcardR)

end Main

/-! ## The qubit registers of the paper -/

/-- The `n`-qubit work register as an index type. -/
abbrev QubitReg (n : ℕ) : Type := Fin n → Bool

/-- The cardinality of an `n`-qubit register is `2 ^ n`. -/
lemma card_qubitReg (n : ℕ) : Fintype.card (QubitReg n) = 2 ^ n := by
  simp [QubitReg]

/-- The completely mixed state on `n` qubits, `𝟙 / 2 ^ n`, as a matrix. -/
noncomputable def mixedQubits (n : ℕ) : Matrix (QubitReg n) (QubitReg n) ℂ :=
  (((2 ^ n : ℕ) : ℂ)⁻¹) • 1

/-- The pure ancilla state `(|0⟩⟨0|) ^ m` on `m` ancilla qubits. -/
noncomputable def pureZeroQubits (m : ℕ) : Matrix (QubitReg m) (QubitReg m) ℂ :=
  Matrix.single (fun _ => false) (fun _ => false) 1

/-- **Lemma 7, Eq. (39), paper form.**  For a projection `Q` on the `n + m` qubit space,

  `Tr[Q (𝟙 / 2 ^ n ⊗ (|0⟩⟨0|) ^ m)] ≤ Tr[Q (𝟙 / 2 ^ n)] = 2 ^ (-n) Tr[Q]`. -/
theorem lemma7_trace_bound (n m : ℕ)
    (Q : Matrix (QubitReg n × QubitReg m) (QubitReg n × QubitReg m) ℂ)
    (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q) :
    (Q * (mixedQubits n ⊗ₖ pureZeroQubits m)).trace.re ≤ Q.trace.re / 2 ^ n := by
  have h := trace_mul_mixed_pure_le Q hQ hQ2 (fun _ => false)
  rw [card_qubitReg n] at h
  simpa only [mixedQubits, pureZeroQubits, pureZero, Matrix.smul_kronecker,
    Nat.cast_pow, Nat.cast_ofNat] using h

/-- **Lemma 7, last inequality of Eq. (39), integer form.**  If in addition the trace of `Q` is at
most `2 ^ N` with `N ≥ n`, then the overlap is at most `2 ^ (N - n)`, i.e. `2 ^ (-n + n R)` for the
integer rank bound `N = n R`. -/
theorem lemma7_rank_bound (n m N : ℕ)
    (Q : Matrix (QubitReg n × QubitReg m) (QubitReg n × QubitReg m) ℂ)
    (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (hrank : Q.trace.re ≤ (2 : ℝ) ^ N) (hnN : n ≤ N) :
    (Q * (mixedQubits n ⊗ₖ pureZeroQubits m)).trace.re ≤ (2 : ℝ) ^ (N - n) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hle := lemma7_trace_bound n m Q hQ hQ2
  have hdiv : Q.trace.re / 2 ^ n ≤ (2 : ℝ) ^ N / 2 ^ n :=
    div_le_div_of_nonneg_right hrank (le_of_lt hpow)
  refine hle.trans (hdiv.trans (le_of_eq ?_))
  rw [div_eq_mul_inv, pow_sub₀ (2 : ℝ) (by norm_num) hnN]

/-- **Lemma 7, Eq. (39), real exponent form.**  This is the paper's statement with the rank bound
`dim ≤ 2 ^ (n R)`, where `R : ℝ`: the overlap is at most `2 ^ (n (R - 1))`. -/
theorem lemma7_rpow_bound (n m : ℕ) (R : ℝ)
    (Q : Matrix (QubitReg n × QubitReg m) (QubitReg n × QubitReg m) ℂ)
    (hQ : Q.IsHermitian) (hQ2 : Q * Q = Q)
    (hrank : Q.trace.re ≤ (2 : ℝ) ^ ((n : ℝ) * R)) :
    (Q * (mixedQubits n ⊗ₖ pureZeroQubits m)).trace.re ≤ (2 : ℝ) ^ ((n : ℝ) * (R - 1)) := by
  have hle := lemma7_trace_bound n m Q hQ hQ2
  have hdim : Q.trace.re / 2 ^ n = Q.trace.re / (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
  rw [hdim] at hle
  have hpos : (0 : ℝ) < 2 := by norm_num
  refine hle.trans ?_
  calc Q.trace.re / (2 : ℝ) ^ (n : ℝ)
      ≤ (2 : ℝ) ^ ((n : ℝ) * R) / (2 : ℝ) ^ (n : ℝ) :=
        div_le_div_of_nonneg_right hrank (le_of_lt (Real.rpow_pos_of_pos hpos _))
    _ = (2 : ℝ) ^ ((n : ℝ) * R - (n : ℝ)) := (Real.rpow_sub hpos _ _).symm
    _ = (2 : ℝ) ^ ((n : ℝ) * (R - 1)) := by ring_nf

end Qatlib.Papers.LovaszLemma13.MainResults
