/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.SourceModel
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# HammingModel — Hamming states and the one-dimensional encoding space

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
Appendix F.3.2, PDF pages 52–54. Definition 5 (F.30), Lemma 5 (F.31),
Lemma 6 (F.32), Lemma 7 (F.33)–(F.34).

The Hilbert space `C^{2^n}` is modelled as functions `Fin n → Bool → ℂ`; the
Hamming weight of a bit string is the size of its support, and
`hammingState n j` is the normalised uniform superposition over the
weight-`j` layer. `C_j = binom(n,j)` is provided by `Nat.choose`; the
cardinality lemma `card_weight_eq_choose` records that the layer really has
`C_j` elements (Definition 5).
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators
open Matrix

namespace Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding

open Qatlib.Papers.QHamDescent23.MainResults

/-- Bit strings on `n` qubits, i.e. the computational basis of `C^{2^n}`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- Hamming weight `|b|` of a bit string (Definition 5). -/
def weight {n : ℕ} (b : BitString n) : ℕ :=
  (Finset.univ.filter (fun i => b i = true)).card

/-- Flipping the `i`-th qubit. -/
def flipBit {n : ℕ} (i : Fin n) (b : BitString n) : BitString n :=
  fun k => if k = i then (if b k then false else true) else b k

/-- Support of a bit string as a finset of qubit positions. -/
def support {n : ℕ} (b : BitString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i = true)

/-- The Hamming weight equals the cardinality of the support. -/
lemma weight_eq_support_card {n : ℕ} (b : BitString n) : weight b = (support b).card := rfl

/-- The Hamming weight of an `n`-bit string is at most `n`. -/
lemma weight_le {n : ℕ} (b : BitString n) : weight b ≤ n := by
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
    (p := fun i => b i = true)
  simpa [weight, Finset.card_univ, Fintype.card_fin] using h

/-- The number of bit strings of Hamming weight `j` is the binomial
coefficient `binom(n,j)` (the `C_j` of Definition 5). -/
theorem card_weight_eq_choose (n j : ℕ) :
    Fintype.card {b : BitString n // weight b = j} = Nat.choose n j := by
  classical
  -- identify bit strings with their support
  let e : BitString n ≃ Finset (Fin n) :=
    { toFun := fun b => support b
      invFun := fun s => fun i => decide (i ∈ s)
      left_inv := by
        intro b
        funext i
        by_cases h : b i = true
        · simp [support, h]
        · cases hb : b i
          · simp [support, hb]
          · exact absurd hb h
      right_inv := by
        intro s
        ext i
        simp [support] }
  have hcard : Fintype.card {b : BitString n // weight b = j}
      = Fintype.card {s : Finset (Fin n) // s.card = j} := by
    refine Fintype.card_congr ?_
    refine e.subtypeEquiv ?_
    intro b
    rfl
  rw [hcard, Fintype.card_finset_len, Fintype.card_fin]

/-- The `j`-th Hamming state (Definition 5, F.30):
`|H_j⟩ = C_j^{-1/2} Σ_{|b|=j} |b⟩`. -/
def hammingState (n : ℕ) (j : ℕ) : Ket (BitString n) :=
  fun b => if weight b = j then (((Real.sqrt (Nat.choose n j) : ℝ) : ℂ))⁻¹ else 0

/-- The uniform superposition `|s⟩ = |+⟩^{⊗n}` (Lemma 6, F.32). -/
def uniformState (n : ℕ) : Ket (BitString n) :=
  fun _ => (((Real.sqrt ((2 : ℝ) ^ n) : ℝ) : ℂ))⁻¹

/-- The `Σ_j σ_x^{(j)}` operator acting on amplitudes: a sum of all single
qubit flips (Lemma 7, F.33). -/
def sxApply {n : ℕ} (ψ : Ket (BitString n)) : Ket (BitString n) :=
  fun b => ∑ i : Fin n, ψ (flipBit i b)

/-- The `Σ_j σ_z^{(j)}` operator acting on amplitudes (Lemma 7, F.34). -/
def szApply {n : ℕ} (ψ : Ket (BitString n)) : Ket (BitString n) :=
  fun b => ((n : ℂ) - 2 * (weight b : ℂ)) * ψ b

/-- Matrix of `Σ_j σ_x^{(j)}`; the entry counts single-qubit flips sending
`b` to `b'`. -/
def sxMatrix (n : ℕ) : Matrix (BitString n) (BitString n) ℂ :=
  fun b b' => ∑ i : Fin n, if flipBit i b = b' then (1 : ℂ) else 0

/-- The flip-counting matrix `sxMatrix` acts on kets as the sum of single-qubit
flips `sxApply`. -/
lemma sxMatrix_mulVec {n : ℕ} (ψ : Ket (BitString n)) :
    sxMatrix n *ᵥ ψ = sxApply ψ := by
  funext b
  simp only [mulVec, dotProduct, sxMatrix, sxApply, Finset.sum_mul, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

end Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding
