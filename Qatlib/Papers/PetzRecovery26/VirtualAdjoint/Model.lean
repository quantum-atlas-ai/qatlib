/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.Channels.CPTP

set_option backward.isDefEq.respectTransparency false

/-!
# Model for *Simulation of Adjoints and Petz Recovery Maps for Unknown Quantum Channels*

Fixed source version: arXiv:2602.05828v1 (first submitted 2026-02-05).

This file fixes the finite-dimensional matrix model shared by the paper-layer
statements of `Papers/PetzRecovery26/VirtualAdjoint`:

* `eConj` is entrywise complex conjugation of a matrix;
* `transposeMap` and `conjMap` are the channel transpose `Nᵀ` and the channel
  complex conjugate `N*` of Section III A (p. 3);
* `flip` is the SWAP operator `F_{A'A}` (p. 3, Notation), and `symProj` /
  `antiProj` are the projections `P^s = (1+F)/2`, `P^a = (1-F)/2` onto the
  symmetric/antisymmetric subspaces (p. 4, Eq. (6));
* `wernerPlus` / `wernerMinus` are the Werner--Holevo channels
  `W_d^±(X) = (Tr(X) 1_d ± Xᵀ)/(d±1)` (p. 3, Eq. (2)).

Everything is stated over complex matrices indexed by finite types, matching
`QuantumInfo.Channels.MatrixMap`; no abstract axiomatisation is introduced.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.PetzRecovery26.VirtualAdjoint

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ## Complex conjugation, transpose, and the adjoint -/

/-- Entrywise complex conjugation of a matrix. -/
def eConj (X : Matrix A B ℂ) : Matrix A B ℂ := fun i j => star (X i j)

/-- Entrywise complex conjugation unfolds to `star` on entries. -/
@[simp] theorem eConj_apply (X : Matrix A B ℂ) (i : A) (j : B) :
    eConj X i j = star (X i j) := rfl

/-- Entrywise complex conjugation is additive. -/
@[simp] theorem eConj_add (X Y : Matrix A B ℂ) : eConj (X + Y) = eConj X + eConj Y := by
  ext i j; simp [eConj]

/-- Entrywise complex conjugation is conjugate-linear in the scalar. -/
@[simp] theorem eConj_smul (c : ℂ) (X : Matrix A B ℂ) :
    eConj (c • X) = star c • eConj X := by
  ext i j; simp [eConj, smul_eq_mul]

/-- Entrywise complex conjugation is an involution. -/
@[simp] theorem eConj_eConj (X : Matrix A B ℂ) : eConj (eConj X) = X := by
  ext i j; simp [eConj]

/-- Entrywise conjugation commutes with matrix transpose. -/
@[simp] theorem eConj_transpose (X : Matrix A B ℂ) : eConj Xᵀ = (eConj X)ᵀ := by
  ext i j; simp [eConj]

/-- Entrywise complex conjugation fixes the identity matrix. -/
@[simp] theorem eConj_one : eConj (1 : Matrix A A ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [eConj]
  · simp [eConj, h]

/-- Entrywise complex conjugation fixes the zero matrix. -/
@[simp] theorem eConj_zero : eConj (0 : Matrix A B ℂ) = 0 := by
  ext i j; simp [eConj]

/-- The channel transpose `Nᵀ` of Section III A (p. 3): entrywise matrix
transposition, viewed as a complex-linear matrix map. -/
def transposeMap : MatrixMap A A ℂ where
  toFun X := Xᵀ
  map_add' X Y := Matrix.transpose_add X Y
  map_smul' c X := Matrix.transpose_smul c X

/-- The channel transpose acts by matrix transposition. -/
@[simp] theorem transposeMap_apply (X : Matrix A A ℂ) : transposeMap X = Xᵀ := rfl

/-- The channel complex conjugate `N*` of Section III A (p. 3):
`N*(X) = conj(N(conj X))`, entrywise conjugation intertwined with the map. -/
def conjMap (M : MatrixMap A B ℂ) : MatrixMap A B ℂ where
  toFun X := eConj (M (eConj X))
  map_add' X Y := by
    simp only [eConj_add, map_add]
  map_smul' c X := by
    simp only [eConj_smul, map_smul]
    rw [RingHom.id_apply, star_star]

/-- The conjugate channel conjugates both the input and the output. -/
@[simp] theorem conjMap_apply (M : MatrixMap A B ℂ) (X : Matrix A A ℂ) :
    conjMap M X = eConj (M (eConj X)) := rfl

/-- The transpose map is self-conjugate. -/
@[simp] theorem conjMap_transposeMap : conjMap (transposeMap : MatrixMap A A ℂ) = transposeMap := by
  ext X i j
  simp [conjMap, transposeMap, eConj]

/-- Complex conjugation is an involution on matrix maps. -/
@[simp] theorem conjMap_conjMap (M : MatrixMap A B ℂ) : conjMap (conjMap M) = M := by
  ext X i j
  simp [conjMap, eConj]

/-- The transpose map is self-conjugate in the sense that conjugating after
transposition equals transposing after conjugation. -/
theorem conjMap_transposeMap_comm (M : MatrixMap A A ℂ) :
    conjMap (transposeMap ∘ₗ M) = transposeMap ∘ₗ conjMap M := by
  ext X i j
  simp [conjMap, transposeMap, eConj]

/-! ## Flip operator and symmetric/antisymmetric projections -/

/-- The SWAP (flip) operator `F_{A'A}` acting on `A × A`, with
`F |ij⟩ = |ji⟩` (p. 3, Notation). -/
def flip : Matrix (A × A) (A × A) ℂ :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then (1 : ℂ) else 0

/-- Entry formula for the flip (SWAP) operator. -/
theorem flip_apply (x y : A × A) :
    flip x y = if x.1 = y.2 ∧ x.2 = y.1 then (1 : ℂ) else 0 := rfl

/-- The Choi matrix of the transpose map `Nᵀ` is the flip (SWAP) operator `F`
(p. 3, Notation): in the basis `(b, a)` the transpose map sends
`|a₁⟩⟨a₂|` to `|a₂⟩⟨a₁|`, exactly the action of `F`. -/
theorem choi_transposeMap :
    (transposeMap : MatrixMap A A ℂ).choi_matrix = flip := by
  ext ⟨b1, a1⟩ ⟨b2, a2⟩
  simp only [MatrixMap.choi_matrix, transposeMap_apply, Matrix.transpose_apply,
    Matrix.single, Matrix.of_apply, flip_apply]
  by_cases h : a1 = b2 ∧ a2 = b1
  · have h' : b1 = a2 ∧ a1 = b2 := ⟨h.2.symm, h.1⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ (b1 = a2 ∧ a1 = b2) := fun hh => h ⟨hh.2, hh.1.symm⟩
    rw [if_neg h, if_neg h']

/-- The flip operator is symmetric. -/
theorem flip_symm (x y : A × A) : flip x y = flip y x := by
  unfold flip
  by_cases h : x.1 = y.2 ∧ x.2 = y.1
  · have h' : y.1 = x.2 ∧ y.2 = x.1 := ⟨h.2.symm, h.1.symm⟩
    rw [if_pos h, if_pos h']
  · have h' : ¬ (y.1 = x.2 ∧ y.2 = x.1) := fun hh => h ⟨hh.2.symm, hh.1.symm⟩
    rw [if_neg h, if_neg h']

/-- The projection `P^s = (1 + F)/2` onto the symmetric subspace (p. 4, Eq. (6)). -/
def symProj : Matrix (A × A) (A × A) ℂ := (1 / 2 : ℂ) • (1 + flip)

/-- The projection `P^a = (1 - F)/2` onto the antisymmetric subspace (p. 4, Eq. (6)). -/
def antiProj : Matrix (A × A) (A × A) ℂ := (1 / 2 : ℂ) • (1 - flip)

/-- The flip operator is the difference of the symmetric and antisymmetric projections. -/
theorem flip_eq_symProj_sub_antiProj :
    (flip : Matrix (A × A) (A × A) ℂ) = symProj - antiProj := by
  ext x y
  simp only [symProj, antiProj, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, flip_apply, smul_eq_mul]
  by_cases h : x = y
  · subst h
    by_cases h2 : x.1 = x.2
    · simp [h2]; norm_num
    · simp [h2]
  · by_cases h2 : x.1 = y.2 ∧ x.2 = y.1
    · have hne : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
        rintro ⟨e1, e2⟩
        exact h (Prod.ext e1 e2)
      simp [h, h2, hne]; norm_num
    · have hne : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
        rintro ⟨e1, e2⟩
        exact h (Prod.ext e1 e2)
      simp [h, h2, hne]

/-- The symmetric and antisymmetric projections sum to the identity. -/
theorem symProj_add_antiProj :
    (symProj : Matrix (A × A) (A × A) ℂ) + antiProj = 1 := by
  ext x y
  simp only [symProj, antiProj, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, flip_apply, smul_eq_mul]
  by_cases h : x = y
  · subst h
    by_cases hh : x.1 = x.2 <;> simp [hh] <;> norm_num
  · simp [h]

/-! ## Werner--Holevo channels -/

/-- The linear map `X ↦ c • (Tr(X) • 1)`, the isotropic part of `W_d^±`. -/
def traceScalarMap (c : ℂ) : MatrixMap A A ℂ where
  toFun X := c • ((X.trace : ℂ) • (1 : Matrix A A ℂ))
  map_add' X Y := by
    simp only [Matrix.trace_add, add_smul, smul_add]
  map_smul' r X := by
    simp only [Matrix.trace_smul, smul_smul, RingHom.id_apply]
    congr 1
    ring

/-- The Werner--Holevo channel `W_d^+(X) = (Tr(X) 1_d + Xᵀ)/(d+1)` (p. 3, Eq. (2)). -/
def wernerPlus : MatrixMap A A ℂ :=
  traceScalarMap ((Fintype.card A : ℂ) + 1)⁻¹ + ((Fintype.card A : ℂ) + 1)⁻¹ • transposeMap

/-- The Werner--Holevo channel `W_d^-(X) = (Tr(X) 1_d − Xᵀ)/(d−1)` (p. 3, Eq. (2)). -/
def wernerMinus : MatrixMap A A ℂ :=
  traceScalarMap ((Fintype.card A : ℂ) - 1)⁻¹ - ((Fintype.card A : ℂ) - 1)⁻¹ • transposeMap

/-- Explicit action of the Werner--Holevo channel `W_d^+`. -/
theorem wernerPlus_apply (X : Matrix A A ℂ) :
    wernerPlus X =
      ((Fintype.card A : ℂ) + 1)⁻¹ • ((X.trace : ℂ) • (1 : Matrix A A ℂ) + Xᵀ) := by
  change ((Fintype.card A : ℂ) + 1)⁻¹ • ((X.trace : ℂ) • (1 : Matrix A A ℂ)) +
      ((Fintype.card A : ℂ) + 1)⁻¹ • Xᵀ =
    ((Fintype.card A : ℂ) + 1)⁻¹ • ((X.trace : ℂ) • (1 : Matrix A A ℂ) + Xᵀ)
  rw [smul_add]

/-- Explicit action of the Werner--Holevo channel `W_d^-`. -/
theorem wernerMinus_apply (X : Matrix A A ℂ) :
    wernerMinus X =
      ((Fintype.card A : ℂ) - 1)⁻¹ • ((X.trace : ℂ) • (1 : Matrix A A ℂ) - Xᵀ) := by
  change ((Fintype.card A : ℂ) - 1)⁻¹ • ((X.trace : ℂ) • (1 : Matrix A A ℂ)) -
      ((Fintype.card A : ℂ) - 1)⁻¹ • Xᵀ =
    ((Fintype.card A : ℂ) - 1)⁻¹ • ((X.trace : ℂ) • (1 : Matrix A A ℂ) - Xᵀ)
  rw [smul_sub]

/-! ## State-preparation channels and the conjugate of a state-preparation channel -/

/-- The state-preparation channel `R_ρ(X) = Tr(X) ρ` of the proof of Theorem 1
(p. 3): `R_ρ` maps every system `A` into the fixed state `ρ` on `B`. -/
def statePrep (ρ : Matrix B B ℂ) : MatrixMap A B ℂ where
  toFun X := (X.trace : ℂ) • ρ
  map_add' X Y := by
    simp only [Matrix.trace_add, add_smul]
  map_smul' r X := by
    rw [Matrix.trace_smul, smul_smul]
    rfl

/-- A state-preparation channel maps `X` to `Tr X` times the fixed state. -/
@[simp] theorem statePrep_apply (ρ : Matrix B B ℂ) (X : Matrix A A ℂ) :
    statePrep ρ X = (X.trace : ℂ) • ρ := rfl

/-- The state-preparation channel is injective in the prepared state as soon as the
input system is nonempty (apply to the identity matrix). -/
theorem statePrep_injective [Nonempty A] :
    Function.Injective (statePrep (A := A) (B := B)) := by
  intro ρ σ h
  have h1 := congrArg (fun M : MatrixMap A B ℂ => M 1) h
  simp only [statePrep_apply, Matrix.trace_one] at h1
  have hc : (Fintype.card A : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast hpos.ne'
  have h2 := congrArg (fun M : Matrix B B ℂ => ((Fintype.card A : ℂ)⁻¹) • M) h1
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h2

/-- The complex conjugate of the state-preparation channel is the state-preparation
channel of the transposed state: `(R_ρ)^* = R_{ρᵀ}` for Hermitian `ρ` (p. 3,
proof of Theorem 1). -/
theorem conjMap_statePrep (ρ : Matrix A A ℂ) (hρ : ρ.IsHermitian) :
    conjMap (statePrep (A := A) (B := A) ρ) = statePrep (A := A) (B := A) (ρᵀ) := by
  ext X i j
  have htr : (eConj X).trace = star X.trace := by
    simp [eConj, Matrix.trace]
  simp only [conjMap_apply, statePrep_apply, eConj_apply, Matrix.transpose_apply, htr,
    Matrix.smul_apply, smul_eq_mul, star_mul', star_star]
  rw [hρ.apply j i]

end Qatlib.Papers.PetzRecovery26.VirtualAdjoint
