/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic
import Qatlib.Concepts.BosonFock.BosonOperators.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Spin–boson mapping of QAOA — shared paper-layer definitions

Fixed source: arXiv:2505.07929v2 (PDF SHA of the prefetched copy
`assets/2505.07929v2.pdf`), *Spin–Boson Mapping of the Quantum Approximate
Optimization Algorithm*, Boulebnane, Khan, Liu, Larson, Herman, Shaydulin,
Pistoia.

This module collects the definitions shared by the per-claim theorem files of
paper unit `SpinBosonQAOA26.MainResults`:

* spin configurations and their real sign vectors (paper §IV);
* the Gram matrices `G^(herm) = L† L` and its symmetric counterpart
  `G^(sym)` (Definition 1 and Definition 2, PDF p. 21, eqs. (78), (79), (80));
* the path-integral weight `H(a)` of eq. (34), PDF p. 13 / eq. (71), p. 20;
* the two one-sided `f` tensors and the two-sided tensor of Definition 10,
  PDF p. 34, eqs. (182)–(186);
* the displacement (Weyl) representation data of Definition 3, PDF p. 21,
  eqs. (82)–(86), with the multiplication law of eq. (75), PDF p. 21;
* the spin–boson state as a two-component bosonic state (the `ℂ²` spin factor
  is unfolded into two copies of the bosonic space), together with the
  displacement layer, the mixer layer `e^{-i β X}` and the state of eq. (90).

The paper's state lives in `ℂ² ⊗ L²(ℝ)^{⊗ p'}`.  Mathlib has no Weyl
representation of the canonical commutation relations on `L²(ℝ)`, so the
displacement family `D` together with its multiplication law and the vacuum
expectation are carried as the explicit data `WeylFock` below.  This is exactly
the data that the paper's own proofs start from (eqs. (75), (105), (106)); the
analytic construction of `D` from `c†, c` on Fock space is the one input that is
not formalised in this library.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open scoped ComplexConjugate
open Finset Matrix

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions

/-! ## Spin configurations -/

/-- Real value of one spin: `true ↦ 1`, `false ↦ -1`.  These are the values
`a ∈ {1, -1}` of the paper's spin configurations. -/
def spinOf (b : Bool) : ℝ := if b then 1 else -1

/-- `spinOf true = 1`. -/
@[simp] lemma spinOf_true : spinOf true = 1 := rfl
/-- `spinOf false = -1`. -/
@[simp] lemma spinOf_false : spinOf false = -1 := rfl

/-- A spin value squares to one: `spinOf b * spinOf b = 1`. -/
lemma spinOf_mul_self (b : Bool) : spinOf b * spinOf b = 1 := by
  cases b <;> norm_num [spinOf]

/-- A spin value is nonzero. -/
lemma spinOf_ne_zero (b : Bool) : spinOf b ≠ 0 := by
  cases b <;> norm_num [spinOf]

/-- The absolute value of a spin value is one. -/
lemma abs_spinOf (b : Bool) : |spinOf b| = 1 := by
  cases b <;> norm_num [spinOf]

/-- A spin configuration on `n` sites (the bitstrings `a` of the paper). -/
abbrev SpinConfig (n : ℕ) := Fin n → Bool

/-- The real sign vector of a spin configuration. -/
def spinVec {n : ℕ} (a : SpinConfig n) : Fin n → ℝ := fun i => spinOf (a i)

/-- The sign vector evaluated at a site is the spin value of that site. -/
@[simp] lemma spinVec_apply {n : ℕ} (a : SpinConfig n) (i : Fin n) :
    spinVec a i = spinOf (a i) := rfl

/-! ## The Gram matrices of the mode-coupling matrix `L` -/

/-- `G^(herm) := L† L` (Definition 1, PDF p. 21, eq. (78)).  `L` is the
`p' × p` matrix whose columns are the displacement vectors `L_{:,t}`. -/
def gramHerm (p' p : ℕ) (L : Matrix (Fin p') (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  Lᴴ * L

/-- Entrywise form of `G^(herm) = L† L`: `G_{j,k} = ∑_l conj(L_{l,j}) L_{l,k}`. -/
lemma gramHerm_apply {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (j k : Fin p) :
    gramHerm p' p L j k = ∑ l, (starRingEnd ℂ) (L l j) * L l k := by
  simp [gramHerm, Matrix.mul_apply]

/-- `G^(herm)` is Hermitian. -/
lemma gramHerm_conjTranspose {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) :
    (gramHerm p' p L)ᴴ = gramHerm p' p L := by
  simp [gramHerm]

/-- Symmetric counterpart of the Gram matrix (Definition 2, PDF p. 21,
eq. (80)): `G^(sym)_{j,k} = G^(herm)_{k,j}` for `j ≤ k`, extended by symmetry. -/
def gramSym (p' p : ℕ) (L : Matrix (Fin p') (Fin p) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  fun j k => if j ≤ k then gramHerm p' p L k j else gramHerm p' p L j k

/-- For `j ≤ k`, the symmetric Gram matrix uses the transposed Hermitian entry. -/
lemma gramSym_apply_of_le {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) {j k : Fin p}
    (h : j ≤ k) : gramSym p' p L j k = gramHerm p' p L k j := by
  simp [gramSym, h]

/-- For `j > k`, the symmetric Gram matrix uses the Hermitian entry. -/
lemma gramSym_apply_of_gt {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) {j k : Fin p}
    (h : ¬ j ≤ k) : gramSym p' p L j k = gramHerm p' p L j k := by
  simp [gramSym, h]

/-- `G^(sym)` is symmetric (Definition 2). -/
lemma gramSym_symm {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (j k : Fin p) :
    gramSym p' p L j k = gramSym p' p L k j := by
  rcases lt_trichotomy j k with h | h | h
  · rw [gramSym_apply_of_le L (le_of_lt h), gramSym_apply_of_gt L (not_le_of_gt h)]
  · subst h
    simp [gramSym]
  · rw [gramSym_apply_of_gt L (not_le_of_gt h), gramSym_apply_of_le L (le_of_lt h)]

/-- The diagonal of `G^(herm)` is the real sum of the squared norms of the
column `L_{:,j}`. -/
lemma gramHerm_diag_eq_sum_normSq {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (j : Fin p) :
    gramHerm p' p L j j = ((∑ l, Complex.normSq (L l j)) : ℂ) := by
  rw [gramHerm_apply]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]

/-- The diagonal of `G^(herm)` is real, so its imaginary part vanishes. -/
lemma gramHerm_diag_im_zero {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (j : Fin p) :
    (gramHerm p' p L j j).im = 0 := by
  rw [gramHerm_diag_eq_sum_normSq]
  simp

/-! ## The path-integral weight `H(a)` -/

/-- The path-integral weight of Proposition 1, eq. (34) (PDF p. 13), in the
real form of eq. (120) (PDF p. 25): `H(a) = exp(-½ ∑_{j,k} G_{j,k} Γ_j Γ_k a_j a_k)`.
`g` is the symmetric real matrix assembled from the four blocks (116)–(119). -/
def pathWeight {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (Γ a : Fin n → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * ∑ j, ∑ k, g j k * Γ j * Γ k * a j * a k)

/-- The weight is strictly positive. -/
lemma pathWeight_pos {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (Γ a : Fin n → ℝ) :
    0 < pathWeight g Γ a := Real.exp_pos _

/-- `H` as a complex number (the measure `f(a) H(a)` is complex-valued). -/
def pathWeightC {n : ℕ} (g : Matrix (Fin n) (Fin n) ℝ) (Γ a : Fin n → ℝ) : ℂ :=
  (pathWeight g Γ a : ℂ)

/-! ## Index layout for the `(2p+1)`-bit strings of Proposition 1

The paper writes `a = (a_1, …, a_p, a_0, a_{-p}, …, a_{-1}) ∈ {1,-1}^{2p+1}`
(eq. (121), PDF p. 25).  The following three maps address the positive block,
the central entry and the negative block. -/

/-- Position of `a_j` for `1 ≤ j ≤ p`. -/
def posIdx (p : ℕ) (j : Fin p) : Fin (2 * p + 1) := ⟨j.val, by omega⟩

/-- Position of `a_0`. -/
def zeroIdx (p : ℕ) : Fin (2 * p + 1) := ⟨p, by omega⟩

/-- Position of `a_{-j}` for `1 ≤ j ≤ p` (at index `2p + 1 - j`). -/
def negIdx (p : ℕ) (j : Fin p) : Fin (2 * p + 1) := ⟨2 * p - j.val, by omega⟩

/-- The path-integral representation (Proposition 1, eq. (120)) of the overlap
`⟨Ψ_k|Ψ_j⟩` as a sum over `(2p+1)`-bit strings. -/
def pathOverlap {p : ℕ} (g : Matrix (Fin (2 * p + 1)) (Fin (2 * p + 1)) ℝ)
    (Γ : Fin (2 * p + 1) → ℝ) (f : (Fin (2 * p + 1) → ℝ) → ℂ) (j k : Fin p) : ℂ :=
  ∑ a : SpinConfig (2 * p + 1),
    ((spinOf (a (posIdx p k)) * spinOf (a (negIdx p j)) : ℝ) : ℂ) *
      f (spinVec a) * pathWeightC g Γ (spinVec a)

/-! ## The one-sided and two-sided `f` tensors -/

/-- The qubit matrix element `⟨a'| e^{-i β X} |a⟩` in the `±1` basis:
`cos β` on the diagonal and `-i sin β` off the diagonal (Definition 10,
PDF p. 34, eqs. (182), (183)). -/
def xAmplitude (β : ℝ) (a a' : Bool) : ℂ :=
  if a = a' then (Real.cos β : ℂ) else -Complex.I * (Real.sin β : ℂ)

/-- The one-sided `f` tensor `f_{1:p+1}` of Definition 10, eq. (183). -/
def fOneSided {p : ℕ} (β : Fin p → ℝ) (a : Fin (p + 1) → Bool) : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) * ∏ t : Fin p, xAmplitude (β t) (a (Fin.castSucc t)) (a (Fin.succ t))

/-- The two-sided `f` tensor of Definition 10, eq. (186), written in the
`(2p+1)`-position layout: the product of the one-sided tensor on the forward
string `(a_1,…,a_p,a_0)` and the one-sided tensor on the reversed string
`(a_{-1},…,a_{-p},a_0)`. -/
def fTwoSided {p : ℕ} (β : Fin p → ℝ) (a : Fin (2 * p + 1) → Bool) : ℂ :=
  fOneSided β (fun i => if h : i.val < p then a (posIdx p ⟨i.val, h⟩) else a (zeroIdx p)) *
    fOneSided β (fun i => if h : i.val < p then a (negIdx p ⟨i.val, h⟩) else a (zeroIdx p))

/-! ## A spin–boson Hilbert space with displaced vacuum

The paper's bosonic space is `L²(ℝ, dx)^{⊗ p'}`, the vacuum is the oscillator
ground state, and `D(z)` is the product of single-mode displacements
`exp(z_l c†_l - \bar z_l c_l)`.  The data that the paper uses in every proof
are the Weyl law (75)/(100) and the vacuum expectation (105)/(106); `WeylFock`
carries precisely these. -/

/-- Complex inner product `⟨z, w⟩ = ∑_l z_l \overline{w_l}` of two displacement
vectors. -/
def cdot {N : ℕ} (z w : Fin N → ℂ) : ℂ := ∑ l, z l * (starRingEnd ℂ) (w l)

/-- The complex inner product is additive in its first argument. -/
lemma cdot_add_left {N : ℕ} (z z' w : Fin N → ℂ) :
    cdot (z + z') w = cdot z w + cdot z' w := by
  simp [cdot, add_mul, Finset.sum_add_distrib]

/-- The complex inner product is homogeneous in its first argument. -/
lemma cdot_smul_left {N : ℕ} (c : ℂ) (z w : Fin N → ℂ) :
    cdot (c • z) w = c * cdot z w := by
  simp [cdot, Finset.mul_sum, mul_assoc]

/-- The complex inner product vanishes with a zero first argument. -/
lemma cdot_zero_left {N : ℕ} (w : Fin N → ℂ) : cdot (0 : Fin N → ℂ) w = 0 := by
  simp [cdot]

/-- The complex inner product is additive over a finite sum in its first argument. -/
lemma cdot_sum_left {N : ℕ} {ι : Type*} (s : Finset ι) (z : ι → Fin N → ℂ)
    (w : Fin N → ℂ) : cdot (∑ i ∈ s, z i) w = ∑ i ∈ s, cdot (z i) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact cdot_zero_left w
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, cdot_add_left, ih]

/-- Conjugation symmetry of the complex inner product: `⟨w,z⟩ = conj ⟨z,w⟩`. -/
lemma cdot_conj_symm {N : ℕ} (z w : Fin N → ℂ) :
    cdot w z = starRingEnd ℂ (cdot z w) := by
  simp only [cdot, map_sum, map_mul, starRingEnd_apply, star_star]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `⟨z,z⟩` is the real squared norm of `z`, so it has no imaginary part. -/
lemma cdot_self_eq_sum_normSq {N : ℕ} (z : Fin N → ℂ) :
    cdot z z = ((∑ l, Complex.normSq (z l)) : ℂ) := by
  rw [cdot]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.normSq_eq_conj_mul_self, mul_comm]

/-- The self-inner-product `⟨z,z⟩` is real, so its imaginary part vanishes. -/
lemma cdot_self_im {N : ℕ} (z : Fin N → ℂ) : (cdot z z).im = 0 := by
  rw [cdot_self_eq_sum_normSq]
  simp

section Weyl

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- Displacement data on the `p'`-mode bosonic space: a unitary `D z` for every
displacement vector `z`, the vacuum, the Weyl multiplication law (paper eq.
(75), PDF p. 21; multi-mode form eq. (100), PDF p. 23) and the vacuum
expectation (paper eqs. (105), (106), PDF p. 23). -/
structure WeylFock (p' : ℕ) where
  /-- The displacement operator `D(z)` of Definition 3, eqs. (82)–(86). -/
  D : (Fin p' → ℂ) → B ≃ₗᵢ[ℂ] B
  /-- The oscillator ground state `|0⟩`. -/
  vacuum : B
  /-- Weyl multiplication law, eq. (75): `D(z) D(w) = e^{i Im⟨z,w⟩} D(z+w)`. -/
  weyl : ∀ (z w : Fin p' → ℂ) (b : B),
    D z (D w b) = (Complex.exp (Complex.I * (cdot z w).im) : ℂ) • D (z + w) b
  /-- Vacuum expectation, from eq. (106): `⟨0|D(z)|0⟩ = e^{-‖z‖²/2}`. -/
  vacuum_expectation : ∀ z : Fin p' → ℂ,
    inner ℂ vacuum (D z vacuum) =
      (Complex.exp ((-(∑ l, Complex.normSq (z l)) / 2 : ℝ) : ℂ) : ℂ)

/-- The displacement by the zero vector is the identity, `D(0) = 1`: it follows from the
Weyl law, eq. (75), with `z = w = 0` together with bijectivity of `D(0)`. -/
lemma WeylFock.D_zero_apply {p' : ℕ} (W : WeylFock p') (b : B) : W.D 0 b = b := by
  have h : W.D 0 (W.D 0 b) = W.D 0 b := by
    simpa [cdot_zero_left] using
      W.weyl (0 : Fin p' → ℂ) (0 : Fin p' → ℂ) b
  exact (W.D 0).injective h

end Weyl

/-! ## Spin–boson states and the generalized QAOA state

The spin factor `ℂ²` is unfolded into two copies of the bosonic space: a state
is a pair `(ψ₊, ψ₋)` of bosonic vectors, the `+1` and `-1` components of the
spin.  This is the standard isomorphism `ℂ² ⊗ B ≃ B × B`. -/

/-- A spin–boson state: the two spin components. -/
abbrev SBState (B : Type*) := Fin 2 → B

/-- The spin value attached to a component index (`0 ↦ 1`, `1 ↦ -1`). -/
def spinOfIndex (i : Fin 2) : ℝ := if i = 0 then 1 else -1

/-- `spinOfIndex 0 = 1`. -/
@[simp] lemma spinOfIndex_zero : spinOfIndex 0 = 1 := rfl
/-- `spinOfIndex 1 = -1`. -/
@[simp] lemma spinOfIndex_one : spinOfIndex 1 = -1 := by
  simp [spinOfIndex]

/-- Flipping the spin component (`X` acts as `0 ↔ 1`). -/
def flipIndex (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- `flipIndex 0 = 1`. -/
@[simp] lemma flipIndex_zero : flipIndex 0 = 1 := rfl
/-- `flipIndex 1 = 0`. -/
@[simp] lemma flipIndex_one : flipIndex 1 = 0 := by
  simp [flipIndex]
/-- Flipping the spin component twice is the identity. -/
@[simp] lemma flipIndex_flipIndex (i : Fin 2) : flipIndex (flipIndex i) = i := by
  fin_cases i <;> rfl

section State

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- The displacement layer `D(-i γ_t Z L_{:,t})` (Definition 3, eq. (90)):
on the spin component with eigenvalue `a`, the displacement vector is
`a • (-i γ_t L_{:,t})`. -/
def displaceLayer {p' : ℕ} (D : (Fin p' → ℂ) → B → B) (v : Fin p' → ℂ) :
    SBState B → SBState B :=
  fun s i => D (fun l => (spinOfIndex i : ℂ) • v l) (s i)

/-- The mixer layer `exp(-i β X) = cos β · 1 - i sin β · X` on the spin factor. -/
def mixerLayer (β : ℝ) (s : SBState B) : SBState B :=
  fun i => (Real.cos β : ℂ) • s i - (Complex.I * (Real.sin β : ℂ)) • s (flipIndex i)

/-- The initial state `|+⟩ ⊗ |0⟩^{⊗ p'}`: both spin components carry the vacuum
with amplitude `1/√2` (`|+⟩ = (|0⟩+|1⟩)/√2` in the `±1` basis). -/
def initialSBState (vac : B) : SBState B :=
  fun _ => ((Real.sqrt 2)⁻¹ : ℂ) • vac

/-- The generalized QAOA state of eq. (90) (PDF p. 21): the ordered product
`∏←_{t=1}^p e^{-iβ_t X} D(-i γ_t Z L_{:,t})` applied to `|+⟩ ⊗ |0⟩^{⊗p'}`.
The product is written as a left fold, so layer `1` acts first. -/
def qaoaState {p' : ℕ} (D : (Fin p' → ℂ) → B → B) (vac : B) {p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ)
    (γ β : Fin p → ℝ) : SBState B :=
  (List.finRange p).foldl
    (fun s t => mixerLayer (β t) (displaceLayer D (fun l => -Complex.I * (γ t : ℂ) • L l t) s))
    (initialSBState vac)

end State

end Qatlib.Papers.SpinBosonQAOA26.MainResults.Definitions
