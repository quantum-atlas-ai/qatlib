/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding.HammingModel

set_option backward.isDefEq.respectTransparency false

/-!
# MeasurementEquivalence — Lemma 8 and Proposition 7
(arXiv:2303.01471v1, Appendix F.4)

Source: *Quantum Hamiltonian Descent*, Leng–Hickman–Li–Wu, arXiv:2303.01471v1,
PDF pages 57–58, equations (F.51)–(F.53).
-/

open scoped Matrix BigOperators
open Matrix

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QHamDescent23.MainResults.Measurement

open Qatlib.Papers.QHamDescent23.MainResults
open Qatlib.Papers.QHamDescent23.MainResults.HammingEncoding

/-- POVM element for the event "Hamming weight equals `j`": the diagonal
projector onto the weight-`j` layer (Lemma 8, (F.51)). -/
def layerProjector (n j : ℕ) : Matrix (BitString n) (BitString n) ℂ :=
  fun b b' => if b' = b ∧ weight b = j then 1 else 0

/-!
### Lemma 8 (F.51)

Source: arXiv:2303.01471v1, Lemma 8, p.57, equation (F.51).

Measuring all `n` qubits in the computational basis and then computing the
Hamming weight of the outcome is equivalent to the direct Hamming-weight
measurement with POVM element `Π_j = Σ_{|b|=j} |b⟩⟨b|`: for every state `ψ`,
`⟨ψ|Π_j|ψ⟩ = Σ_{|b|=j} |ψ_b|²`.

Paper proof route: `Π_j` is diagonal, so `⟨ψ|Π_j|ψ⟩ = Σ_b [|b|=j] |ψ_b|²`.

Lean gap: the bracket/`normSq` bookkeeping (the bracket is complex-valued, the
probabilities real) is not yet assembled.
Reusable deps: `bracket`, `Complex.normSq`, `Matrix.mulVec`, `Finset.sum_filter`,
`Complex.normSq_eq_conj_mul_self`.
Suggested tactics: `bracket` unfolds to `Σ_b star (ψ b) * (Π_j ψ) b`; rewrite
`Π_j *ᵥ ψ` entrywise to `if weight b = j then ψ b else 0`, then pull out the
`if` with `Finset.sum_filter` and identify `star z * z = (normSq z : ℂ)`.
-/
/-- Lemma 8 (F.51): the Hamming-weight POVM reproduces the distribution of the
Hamming weight on a one-register state. -/
theorem source_lemma8_weight_measurement (n : ℕ) (ψ : Ket (BitString n)) (j : ℕ) :
    bracket ψ (layerProjector n j *ᵥ ψ)
      = ((∑ b : BitString n, if weight b = j then Complex.normSq (ψ b) else 0 : ℝ) : ℂ) := by
  classical
  rw [bracket]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hmv : (layerProjector n j *ᵥ ψ) b = if weight b = j then ψ b else 0 := by
    simp only [layerProjector, mulVec, dotProduct]
    by_cases hb : weight b = j
    · rw [if_pos hb]
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro b' _ hb'
        simp [hb', hb]
      · intro hbnotmem
        simp at hbnotmem
    · rw [if_neg hb]
      refine Finset.sum_eq_zero (fun b' _ => ?_)
      by_cases hbb : b' = b
      · subst hbb; simp [hb]
      · simp [hbb, hb]
  rw [hmv]
  by_cases hb : weight b = j
  · rw [if_pos hb, if_pos hb]
    exact Complex.normSq_eq_conj_mul_self.symm
  · rw [if_neg hb, if_neg hb]
    simp

/-- POVM element for the `d`-fold tensor product of weight measurements,
with outcome vector `j : Fin d → ℕ` (Proposition 7, (F.53)). -/
def blockProjector (d n : ℕ) (j : Fin d → ℕ) :
    Matrix (Fin d → BitString n) (Fin d → BitString n) ℂ :=
  fun b b' => if b' = b ∧ (∀ i, weight (b i) = j i) then 1 else 0

/-!
### Proposition 7 (F.53)

Source: arXiv:2303.01471v1, Proposition 7, p.57, equation (F.53).

The `d`-fold measurement equivalence: measuring each register in the
computational basis and computing each Hamming weight gives the same outcome
distribution as the tensor product POVM with elements `Π_j = ⊗_i Π_{j_i}`:

`⟨ψ|Π_j|ψ⟩ = Σ_{∀i, |b_i| = j_i} |ψ_b|²`.

Paper proof route: `Π_j` is the tensor product of the diagonal layer
projectors, hence diagonal on the product basis; the same computation as
Lemma 8 applies.

Lean gap: depends on Lemma 8 and on the tensor-product bookkeeping over
`Fin d → BitString n`.
Reusable deps: `source_lemma8_weight_measurement`, `blockProjector`,
`layerProjector`, `bracket`.
Suggested tactics: unfold `blockProjector`, rewrite `Π_j *ᵥ ψ` entrywise, pull
out the conjunction with `Finset.sum_filter` and finish as in Lemma 8.
-/
/-- Proposition 7 (F.53): the tensor product of one-register layer projectors
reproduces the joint weight distribution on `d` registers. -/
theorem source_proposition7_multivariate_measurement
    (d n : ℕ) (ψ : Ket (Fin d → BitString n)) (j : Fin d → ℕ) :
    bracket ψ (blockProjector d n j *ᵥ ψ)
      = ((∑ b : Fin d → BitString n,
            if ∀ i, weight (b i) = j i then Complex.normSq (ψ b) else 0 : ℝ) : ℂ) := by
  classical
  rw [bracket]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hmv : (blockProjector d n j *ᵥ ψ) b = if (∀ i, weight (b i) = j i) then ψ b else 0 := by
    simp only [blockProjector, mulVec, dotProduct]
    by_cases hb : ∀ i, weight (b i) = j i
    · rw [if_pos hb]
      rw [Finset.sum_eq_single b]
      · simp [hb]
      · intro b' _ hb'
        simp [hb', hb]
      · intro hbnotmem
        simp at hbnotmem
    · rw [if_neg hb]
      refine Finset.sum_eq_zero (fun b' _ => ?_)
      by_cases hbb : b' = b
      · subst hbb; simp [hb]
      · simp [hbb, hb]
  rw [hmv]
  by_cases hb : ∀ i, weight (b i) = j i
  · rw [if_pos hb, if_pos hb]
    exact Complex.normSq_eq_conj_mul_self.symm
  · rw [if_neg hb, if_neg hb]
    simp

end Qatlib.Papers.QHamDescent23.MainResults.Measurement
