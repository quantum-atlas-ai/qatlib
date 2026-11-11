/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# KroneckerTrace — Lemma 1 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), "Quantum complexity of the Kronecker
coefficients". Lemma 1, p. 4 (supplementary Eqs. (3), (6), (7) on pp. 4 and 7–8).

The paper works with the symmetric group `Sₙ`.  Everything in Lemma 1 is purely a
statement about a finite group and its characters, so we state it for an arbitrary
finite group `G`; the paper's case is `G = Equiv.Perm (Fin n)`.  The three characters
`χμ χν χl` are the irreducible characters labelled by partitions `μ ν λ ⊢ n`.

Model (all matrices are written in the group-element basis of `ℂ[G]`):

* `regMat σ` — the left regular representation `ρ(σ)`, `regMat σ x y = 1` iff `x = σ * y`;
* `leftProjector χ` — the central projector of Eq. (3),
  `Π^L_χ = (d_χ / |G|) • Σ_σ χ(σ) • ρ(σ)` with `d_χ = χ(1)`;
* `Qmat` — the projector of Eq. (6), `Q = (1/|G|) Σ_σ ρ(σ)⊗ρ(σ)⊗ρ(σ)`, acting on the
  triple tensor product `ℂ[G] ⊗ ℂ[G] ⊗ ℂ[G]`, represented as matrices indexed by `G × G × G`;
* `kronProjector χμ χν χl` — `P_μνλ = Q (Π^L_μ ⊗ Π^L_ν ⊗ Π^L_λ)`.

The main theorem `lemma1_kronecker_coeff_eq_normalized_trace` proves
`g_μνλ = (d_μ d_ν d_λ)⁻¹ Tr(P_μνλ)` with `g` given by the character average of Eq. (7),
`g_μνλ = (1/|G|) Σ_σ χ_μ(σ) χ_ν(σ) χ_λ(σ)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The left regular representation matrix of `σ`: `(regMat σ) x y = 1` iff `x = σ * y`.
This is the matrix of `ρ(σ)` in the group-element basis of `ℂ[G]`. -/
def regMat (σ : G) : Matrix G G ℂ := fun x y => if x = σ * y then 1 else 0

/-- The dimension `d_χ = χ(1)` of the irreducible representation with character `χ`. -/
def charDim (χ : G → ℂ) : ℂ := χ 1

/-- Paper Eq. (3): the central projector `Π^L_χ = (d_χ / |G|) • Σ_σ χ(σ) • ρ(σ)`. -/
def leftProjector (χ : G → ℂ) : Matrix G G ℂ :=
  (charDim χ / (Fintype.card G : ℂ)) • ∑ σ : G, χ σ • regMat σ

/-- The Kronecker coefficient as the character average of Eq. (7):
`g_μνλ = (1/|G|) Σ_σ χ_μ(σ) χ_ν(σ) χ_λ(σ)`. -/
def kronCoeff (χμ χν χl : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ σ : G, χμ σ * χν σ * χl σ

/-- The triple Kronecker product of matrices, indexed by `G × G × G`.  It is the matrix
of `A ⊗ B ⊗ C` in the basis `e_x ⊗ e_y ⊗ e_z` of `ℂ[G] ⊗ ℂ[G] ⊗ ℂ[G]`. -/
def kron3 (A B C : Matrix G G ℂ) : Matrix (G × G × G) (G × G × G) ℂ :=
  fun x y => A x.1 y.1 * B x.2.1 y.2.1 * C x.2.2 y.2.2

/-- The triple tensor product of the left regular representation. -/
def tripleReg (σ : G) : Matrix (G × G × G) (G × G × G) ℂ :=
  kron3 (regMat σ) (regMat σ) (regMat σ)

/-- Paper Eq. (6): `Q = (1/|G|) Σ_σ ρ(σ)⊗ρ(σ)⊗ρ(σ)`. -/
def Qmat : Matrix (G × G × G) (G × G × G) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ σ : G, tripleReg σ

/-- The Kronecker projector `P_μνλ = Q (Π^L_μ ⊗ Π^L_ν ⊗ Π^L_λ)` of Theorem 1. -/
def kronProjector (χμ χν χl : G → ℂ) : Matrix (G × G × G) (G × G × G) ℂ :=
  Qmat * kron3 (leftProjector χμ) (leftProjector χν) (leftProjector χl)

/-! ### Trace of the regular representation -/

/-- The regular representation matrix `regMat σ` has trace `|G|` at the identity and `0`
elsewhere: in the left regular representation `Tr(ρ(π)) = 0` unless `π` is the identity
(paper, proof of Lemma 1, p. 4). -/
theorem trace_regMat (σ : G) :
    Matrix.trace (regMat σ) = if σ = 1 then (Fintype.card G : ℂ) else 0 := by
  by_cases hσ : σ = 1
  · subst hσ
    simp [Matrix.trace, regMat]
  · simp [Matrix.trace, regMat, hσ]

/-- Multiplication of regular representation matrices is the regular representation
matrix of the product. -/
theorem regMat_mul (σ α : G) : regMat σ * regMat α = regMat (σ * α) := by
  ext x y
  simp only [Matrix.mul_apply, regMat]
  rw [Finset.sum_eq_single (α * y)]
  · simp [mul_assoc]
  · intro z _ hz
    rw [if_neg hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `regMat σ * A` acts by shifting the row index by `σ⁻¹`. -/
theorem regMat_mul_apply (σ : G) (A : Matrix G G ℂ) (x y : G) :
    (regMat σ * A) x y = A (σ⁻¹ * x) y := by
  simp only [Matrix.mul_apply, regMat]
  rw [Finset.sum_eq_single (σ⁻¹ * x)]
  · simp
  · intro z _ hz
    rw [if_neg, zero_mul]
    intro h
    apply hz
    calc z = σ⁻¹ * (σ * z) := by simp
      _ = σ⁻¹ * x := by rw [h]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A triple sum of a factorised summand is the product of the three sums. -/
theorem sum3_factor {ι κ lam : Type*} [Fintype ι] [Fintype κ] [Fintype lam]
    (f : ι → ℂ) (g : κ → ℂ) (h : lam → ℂ) :
    (∑ i, ∑ j, ∑ k, f i * g j * h k) = (∑ i, f i) * (∑ j, g j) * (∑ k, h k) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul]

/-- The trace of a triple Kronecker product is the product of the traces.  This is the
factorisation `Tr(A⊗B⊗C) = Tr(A) Tr(B) Tr(C)` used in the proof of Lemma 1. -/
theorem trace_kron3 (A B C : Matrix G G ℂ) :
    Matrix.trace (kron3 A B C) = Matrix.trace A * Matrix.trace B * Matrix.trace C := by
  simp only [Matrix.trace, Matrix.diag, kron3]
  simp_rw [Fintype.sum_prod_type]
  exact sum3_factor (fun i => A i i) (fun j => B j j) (fun k => C k k)

/-- The triple Kronecker product is multiplicative. -/
theorem kron3_mul (A1 B1 C1 A2 B2 C2 : Matrix G G ℂ) :
    kron3 A1 B1 C1 * kron3 A2 B2 C2 = kron3 (A1 * A2) (B1 * B2) (C1 * C2) := by
  ext x y
  simp only [kron3, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [← sum3_factor (fun z1 => A1 x.1 z1 * A2 z1 y.1)
    (fun z2 => B1 x.2.1 z2 * B2 z2 y.2.1) (fun z3 => C1 x.2.2 z3 * C2 z3 y.2.2)]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  refine Finset.sum_congr rfl fun z2 _ => ?_
  refine Finset.sum_congr rfl fun z3 _ => ?_
  ring

/-- `Q` is a linear combination of the triple regular representations, so its product with
a triple Kronecker product expands by linearity of the trace. -/
theorem trace_Q_mul (A B C : Matrix G G ℂ) :
    Matrix.trace (Qmat * kron3 A B C) =
      (Fintype.card G : ℂ)⁻¹ * ∑ σ : G,
        (Matrix.trace (regMat σ * A) * Matrix.trace (regMat σ * B) *
          Matrix.trace (regMat σ * C)) := by
  have hmul : ∀ σ : G, tripleReg σ * kron3 A B C
      = kron3 (regMat σ * A) (regMat σ * B) (regMat σ * C) := by
    intro σ
    rw [tripleReg, kron3_mul]
  simp only [Qmat, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul]
  simp_rw [hmul, trace_kron3]

/-- The trace of `regMat σ * Π^L_χ` is `d_χ χ(σ⁻¹)`.  This is the step
`Tr(ρ(σ) Π^L_χ) = d_χ χ(σ⁻¹)` of the paper's computation of `Tr(P_μνλ)`. -/
theorem trace_regMat_mul_leftProjector (σ : G) (χ : G → ℂ) :
    Matrix.trace (regMat σ * leftProjector χ) = charDim χ * χ σ⁻¹ := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [leftProjector, Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  have hterm : ∀ α : G, χ α * Matrix.trace (regMat σ * regMat α)
      = χ α * (if σ * α = 1 then (Fintype.card G : ℂ) else 0) := by
    intro α
    rw [regMat_mul, trace_regMat]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (σ⁻¹)]
  · simp only [mul_inv_cancel, if_true]
    field_simp
  · intro α _ hα
    have hne : σ * α ≠ 1 := by
      intro h
      apply hα
      calc α = σ⁻¹ * (σ * α) := by simp
        _ = σ⁻¹ * 1 := by rw [h]
        _ = σ⁻¹ := mul_one _
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The trace identity of the Kronecker projector (paper Eq. (6) and the computation on
p. 4): `Tr(P_μνλ) = d_μ d_ν d_λ · (1/|G|) Σ_σ χ_μ(σ) χ_ν(σ) χ_λ(σ)`.
The hypotheses `hμ hν hl` record that the characters are real on inverses, which is the
paper's Eq. (54) (`χ(g⁻¹) = χ(g)` in the orthogonal (Young) representation). -/
theorem trace_kronProjector (χμ χν χl : G → ℂ)
    (hμ : ∀ σ : G, χμ σ⁻¹ = χμ σ) (hν : ∀ σ : G, χν σ⁻¹ = χν σ)
    (hl : ∀ σ : G, χl σ⁻¹ = χl σ) :
    Matrix.trace (kronProjector χμ χν χl) =
      charDim χμ * charDim χν * charDim χl * kronCoeff χμ χν χl := by
  simp only [kronProjector]
  rw [trace_Q_mul]
  simp_rw [trace_regMat_mul_leftProjector]
  rw [kronCoeff]
  have hsum : (∑ σ : G,
      (charDim χμ * χμ σ⁻¹) * (charDim χν * χν σ⁻¹) * (charDim χl * χl σ⁻¹))
      = charDim χμ * charDim χν * charDim χl * (∑ σ : G, χμ σ * χν σ * χl σ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hμ σ, hν σ, hl σ]
    ring
  rw [hsum]
  ring

/-- **Lemma 1** (fixed arXiv:2302.11454v3, p. 4):
`g_μνλ = (d_μ d_ν d_λ)⁻¹ Tr(P_μνλ)`, where `g_μνλ` is the Kronecker coefficient of
Eq. (7), `d_χ = χ(1)`, and `P_μνλ = Q (Π^L_μ ⊗ Π^L_ν ⊗ Π^L_λ)` is the projector of
Theorem 1.  The hypotheses `hμ hν hl` are the reality of the characters on inverses
(paper Eq. (54)); `hdμ hdν hdl` say the three representations are nonzero-dimensional. -/
theorem lemma1_kronecker_coeff_eq_normalized_trace (χμ χν χl : G → ℂ)
    (hμ : ∀ σ : G, χμ σ⁻¹ = χμ σ) (hν : ∀ σ : G, χν σ⁻¹ = χν σ)
    (hl : ∀ σ : G, χl σ⁻¹ = χl σ)
    (hdμ : charDim χμ ≠ 0) (hdν : charDim χν ≠ 0) (hdl : charDim χl ≠ 0) :
    kronCoeff χμ χν χl =
      (charDim χμ * charDim χν * charDim χl)⁻¹ *
        Matrix.trace (kronProjector χμ χν χl) := by
  have hD : charDim χμ * charDim χν * charDim χl ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdμ hdν) hdl
  rw [trace_kronProjector χμ χν χl hμ hν hl]
  field_simp

end Qatlib.Papers.KroneckerCoef23.MainResults.KroneckerTrace
