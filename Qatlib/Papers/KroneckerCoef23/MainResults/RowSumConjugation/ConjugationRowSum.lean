/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace.KroneckerTraceFormula

set_option backward.isDefEq.respectTransparency false

/-!
# ConjugationRowSum — Lemma 8 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024).  Lemma 8, p. 15 (supplementary),
Eq. (8) on p. 5 and Eq. (56) on p. 14.

The conjugation representation `ρ_c` of `Sₙ` acts on `ℂ[Sₙ]` by
`ρ_c(π)|σ⟩ = |πσπ⁻¹⟩`; its character is `χ_c(π) = |Z(π)|`, the centralizer order
(supplementary, proof of Lemma 7).  We model `ρ_c` by the permutation matrices
`conjMat g`, define the conjugacy projector
`Π^c_χ = (d_χ / |G|) • Σ_g χ(g) • ρ_c(g)` and the row sum of Eq. (8) in its
Eq. (56) form `R_χ = (1/|G|) Σ_g χ(g) χ_c(g)`, then prove Lemma 8:
`R_χ = d_χ⁻¹ Tr(Π^c_χ)`.

The identification of this `R_χ` with the partition sum `Σ_{μ⊢n} χ(μ)` of Eq. (8)
is the content of `RowSumClassSum`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.RowSumConjugation

open Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The conjugation representation matrix of `g`: `(conjMat g) x y = 1` iff
`x = g y g⁻¹`.  This is `ρ_c(g)` in the basis `{|σ⟩}` of `ℂ[Sₙ]`. -/
def conjMat (g : G) : Matrix G G ℂ := fun x y => if x = g * y * g⁻¹ then 1 else 0

/-- The centralizer order `|Z(g)|`, the character of the conjugation representation. -/
def centralizerCard (g : G) : ℕ := Fintype.card {x : G // x * g = g * x}

/-- The character `χ_c(g) = |Z(g)|` of the conjugation representation
(supplementary, proof of Lemma 7, p. 14). -/
def conjChar (g : G) : ℂ := (centralizerCard g : ℂ)

/-- The conjugacy projector `Π^c_χ = (d_χ / |G|) • Σ_g χ(g) • ρ_c(g)`. -/
def conjProjector (χ : G → ℂ) : Matrix G G ℂ :=
  (charDim χ / (Fintype.card G : ℂ)) • ∑ g : G, χ g • conjMat g

/-- The row sum `R_χ` of Eq. (8) in the equivalent form of Eq. (56):
`R_χ = (1/|G|) Σ_g χ(g) χ_c(g)`. -/
def rowSum (χ : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, χ g * conjChar g

/-- The trace of `ρ_c(g)` is the number of fixed points of conjugation by `g`, namely
the centralizer order `|Z(g)|` (supplementary, proof of Lemma 7). -/
theorem trace_conjMat (g : G) : Matrix.trace (conjMat g) = conjChar g := by
  have hfilter : (Finset.univ.filter (fun x : G => x = g * x * g⁻¹))
      = Finset.univ.filter (fun x : G => x * g = g * x) := by
    apply Finset.filter_congr
    intro x _
    constructor
    · intro hx
      conv_lhs => rw [hx]
      simp [mul_assoc]
    · intro hx
      conv_rhs => rw [← hx]
      simp [mul_assoc]
  simp only [Matrix.trace, Matrix.diag, conjMat]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hfilter, ← Fintype.card_subtype]
  rfl

/-- `Tr(Π^c_χ) = d_χ · R_χ`: expanding the definition and using `Tr(ρ_c(g)) = |Z(g)|`. -/
theorem trace_conjProjector (χ : G → ℂ) :
    Matrix.trace (conjProjector χ) = charDim χ * rowSum χ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [conjProjector, rowSum, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  simp_rw [trace_conjMat]
  field_simp

/-- **Lemma 8** (fixed arXiv:2302.11454v3, p. 15):
`R_λ = d_λ⁻¹ Tr(Π^c_λ)`, where `R_λ` is the row sum of Eq. (8) (in the Eq. (56)
form) and `Π^c_λ` is the conjugacy projector.  The hypothesis `hd` says the
representation `ρ_λ` is nonzero-dimensional. -/
theorem lemma8_rowSum_eq_inv_dim_mul_trace (χ : G → ℂ) (hd : charDim χ ≠ 0) :
    rowSum χ = (charDim χ)⁻¹ * Matrix.trace (conjProjector χ) := by
  rw [trace_conjProjector]
  field_simp

end Qatlib.Papers.KroneckerCoef23.MainResults.RowSumConjugation
