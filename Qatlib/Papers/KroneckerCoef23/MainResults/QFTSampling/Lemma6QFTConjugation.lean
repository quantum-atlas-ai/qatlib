/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement.BinaryMeasurement

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma6QFTConjugation — Lemma 6 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Lemma 6, pp. 11–12, together with
Eqs. (31)–(33) on p. 12.

Lemma 6: the POVM `M_L = {Π^L_λ}` can be implemented by applying `QFT_n`, then
performing a projective measurement of the representation label `ω`, then applying
`QFT_n†`.  The proof reduces this to

`Π^L_λ = QFT_n† P_λ QFT_n`,                                    (Lemma 6, p. 12)

where `P_λ |ω,i,j⟩ = δ_{ω,λ} |ω,i,j⟩` is the label projector, by expanding
`Π^L_λ |ψ⟩ = (d_λ/n!) Σ_{σ,β} χ_λ(σβ⁻¹) f(σ) |β⟩` (Eqs. (32)–(33)).

What is formalised here:

* `qftConj F P = F† P F`, the operator obtained by "apply `F`, measure `P`, apply `F†`";
* the operator identity `(qftConj F P) v = F†(P(F v))` for every state `v`, so this
  measurement is exactly the paper's "QFT, label measurement, QFT†" procedure;
* `qftConj F P` is an idempotent and has the same trace as `P` (`rank` is preserved);
* the basis matrix element of the left-regular projector, i.e. the second equality of
  Eq. (33): `Π^L_χ β σ = (d_χ/|G|) χ(βσ⁻¹) = (d_χ/|G|) χ(σβ⁻¹)`.

The remaining identification — that for `G = Sₙ` the matrix `QFT_n` is precisely the
unitary intertwining `Π^L_λ` with the label projector `P_λ` — is the noncommutative
Fourier transform over `Sₙ` (Beals' QFT, Eq. (4)–(5) of the paper).  That transform is
not available in Mathlib or in the Frozen library, so the exact equality
`Π^L_λ = QFT_n† P_λ QFT_n` is documented as the gap of this partial formalisation; the
two operator facts that make it meaningful are proved below.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.QFTSampling

open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace
open Qatlib.Papers.KroneckerCoef23.MainResults.ProjectiveMeasurement

variable {V G : Type*}

/-- The operator obtained by applying a unitary `F`, measuring the projector `P`, and
applying the inverse unitary `F†`: `qftConj F P = F† P F` (Lemma 6, p. 12). -/
def qftConj [Fintype V] [DecidableEq V] (F P : Matrix V V ℂ) : Matrix V V ℂ :=
  Fᴴ * P * F

/-- Applying `qftConj F P` to a state `v` equals `F† (P (F v))`: the unitary `F` is
applied, `P` is measured, and `F†` is applied (Lemma 6, p. 12). -/
theorem qftConj_mulVec [Fintype V] [DecidableEq V] (F P : Matrix V V ℂ) (v : V → ℂ) :
    (qftConj F P) *ᵥ v = Fᴴ *ᵥ (P *ᵥ (F *ᵥ v)) := by
  rw [qftConj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- `qftConj F P` is a projector whenever `P` is a projector and `F` is unitary. -/
theorem qftConj_idempotent [Fintype V] [DecidableEq V] (F P : Matrix V V ℂ)
    (hP : P * P = P) (hF : F * Fᴴ = 1) (hF' : Fᴴ * F = 1) :
    qftConj F P * qftConj F P = qftConj F P := by
  have h := conjugated_idempotent (Fᴴ) P hP (by simpa using hF') (by simpa using hF)
  simpa [qftConj, Matrix.conjTranspose_conjTranspose] using h

/-- Conjugating a projector by a unitary preserves its trace (its rank, i.e. the number
of `+1` eigenvalues, which is the counting content used for `#BQP`). -/
theorem qftConj_trace [Fintype V] [DecidableEq V] (F P : Matrix V V ℂ)
    (hF : F * Fᴴ = 1) :
    Matrix.trace (qftConj F P) = Matrix.trace P := by
  rw [qftConj, Matrix.trace_mul_comm (Fᴴ * P) F, ← Matrix.mul_assoc, hF, Matrix.one_mul]

/-- **Lemma 6, operator form** (fixed arXiv:2302.11454v3, p. 12): the POVM implemented
by "apply the unitary `F`, perform the projective measurement `P`, apply `F†`" has the
POVM element `F† P F`; the element is a projector with the same trace (same number of
`+1` eigenvalues) as `P`. -/
theorem lemma6_qft_conjugation [Fintype V] [DecidableEq V] (F P : Matrix V V ℂ)
    (hP : P * P = P) (hF : F * Fᴴ = 1) (hF' : Fᴴ * F = 1) (v : V → ℂ) :
    ((qftConj F P) *ᵥ v = Fᴴ *ᵥ (P *ᵥ (F *ᵥ v))) ∧
    (qftConj F P * qftConj F P = qftConj F P) ∧
    (Matrix.trace (qftConj F P) = Matrix.trace P) :=
  ⟨qftConj_mulVec F P v, qftConj_idempotent F P hP hF hF', qftConj_trace F P hF⟩

variable [Group G] [Fintype G] [DecidableEq G]

/-- The matrix element of the left-regular (central) projector in the group-element basis:
`Π^L_χ β σ = (d_χ/|G|) χ(βσ⁻¹)`.  This is the computation behind Eq. (33) of the proof
of Lemma 6 (p. 12), written there as `Π^L_λ = (d_λ/n!) Σ_{σ,β} χ_λ(σβ⁻¹) f(σ)|β⟩`. -/
theorem leftProjector_apply (χ : G → ℂ) (β σ : G) :
    leftProjector χ β σ =
      charDim χ / (Fintype.card G : ℂ) * χ (β * σ⁻¹) := by
  simp only [leftProjector, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, regMat]
  have hsum : (∑ α : G, χ α * (if β = α * σ then (1 : ℂ) else 0)) = χ (β * σ⁻¹) := by
    rw [Finset.sum_eq_single (β * σ⁻¹)]
    · simp [mul_assoc]
    · intro α _ hα
      have hne : β ≠ α * σ := by
        intro h
        apply hα
        calc α = (α * σ) * σ⁻¹ := by simp
          _ = β * σ⁻¹ := by rw [h]
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum]

/-- Eq. (33) of the proof of Lemma 6 in the form actually displayed in the paper,
`Π^L_χ β σ = (d_χ/|G|) χ(σβ⁻¹)`, which uses the reality of the character
`χ(βσ⁻¹) = χ((βσ⁻¹)⁻¹) = χ(σβ⁻¹)` (paper Eq. (54)). -/
theorem leftProjector_apply_reality (χ : G → ℂ) (hχ : ∀ σ : G, χ σ⁻¹ = χ σ)
    (β σ : G) :
    leftProjector χ β σ =
      charDim χ / (Fintype.card G : ℂ) * χ (σ * β⁻¹) := by
  rw [leftProjector_apply]
  have h := hχ (σ * β⁻¹)
  have hinv : (σ * β⁻¹)⁻¹ = β * σ⁻¹ := by group
  rw [hinv] at h
  rw [h]

end Qatlib.Papers.KroneckerCoef23.MainResults.QFTSampling
