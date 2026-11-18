/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.SelSplit
public import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary

@[expose] public section

/-!
# Wire permutations as unitary gates

The public `permMatrix` machinery of `Qatlib.Foundations.PureStateMath.Qubit` proves unitarity only for
involutions. This module extends it to arbitrary wire bijections: products, conjugate
transposes, ket action, and the interaction with placements from `SelSplit`, so that a wire
permutation is a first-class unitary gate and conjugation by it transports a located gate to
the permuted wires. The public two-qubit `swapGate` is transported to `Reg 2` along
`regTwoBool` and identified with the wire-transposition gate.

## Main statements

* `permBijUni`: the permutation matrix of a bijection is unitary.
* `permGate_symm`: a wire permutation gate is inverted by the inverse permutation gate.
* `permPlacedSel`: conjugating a placement by a wire permutation moves it to the permuted
  wires.
* `perm_swap2`: the transported public SWAP is the two-wire transposition gate.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.SelSplit
open scoped Matrix

namespace Qatlib.Concepts.CircuitLang.WirePerm

/-- The product of two permutation matrices is the permutation matrix of the composition. -/
theorem permComp {I : Type*} [Fintype I] [DecidableEq I] (σ τ : I → I) :
    permMatrix σ * permMatrix τ = permMatrix (σ ∘ τ) := by
  ext i j
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ j)
    (fun k _ hk => by
      have h0 : (if k = τ j then (1 : ℂ) else 0) = 0 := by simp [hk]
      rw [h0, mul_zero])
    (fun h => absurd (Finset.mem_univ (τ j)) h)]
  simp

/-- The permutation matrix of the identity function is the identity matrix. -/
theorem permId {I : Type*} [DecidableEq I] :
    permMatrix (fun w => w) = (1 : Matrix I I ℂ) := by
  ext i j
  simp [permMatrix, Matrix.one_apply]

/-- The conjugate transpose of a bijection's permutation matrix is the permutation matrix of
the inverse bijection. -/
theorem permConj {I : Type*} [DecidableEq I] (e : I ≃ I) :
    Matrix.conjTranspose (permMatrix e) = permMatrix e.symm := by
  ext i j
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = e i
  · subst h
    simp [e.symm_apply_apply]
  · have h1 : i ≠ e.symm j := by
      intro hh
      exact h (by rw [hh, e.apply_symm_apply])
    simp [h, h1]

/-- The permutation matrix of a bijection is unitary, extending the public involution-only
`permMatrix_unitary`. -/
theorem permBijUni {I : Type*} [Fintype I] [DecidableEq I] (e : I ≃ I) :
    permMatrix e ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, permConj, permComp,
    Equiv.symm_comp_self]
  exact permId

/-- Applying the permutation matrix of a bijection to a state reads amplitudes through the
inverse bijection. -/
theorem permBijAct {I : Type*} [Fintype I] [DecidableEq I] (e : I ≃ I) (ψ : QState I) (i : I) :
    ApplyGate (permMatrix e) ψ i = ψ (e.symm i) := by
  simp only [ApplyGate, permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (e.symm i)
    (fun k _ hk => by
      have hne : ¬ (i = e k) := fun h => hk (by rw [h, e.symm_apply_apply])
      have h0 : (if i = e k then (1 : ℂ) else 0) = 0 := by simp [hne]
      rw [h0, zero_mul])
    (fun h => absurd (Finset.mem_univ (e.symm i)) h)]
  simp [e.apply_symm_apply]

/-- Matrix-vector multiplication on a basis vector yields the matrix column. -/
theorem matCol {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) (j : I) :
    M *ᵥ Ket j = fun i => M i j := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single j
    (fun k _ hk => by
      have h0 : (if k = j then (1 : ℂ) else 0) = 0 := by simp [hk]
      rw [h0, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- The permutation matrix of a bijection sends a basis vector to the basis vector at the
bijection's image. -/
theorem permBijKet {I : Type*} [Fintype I] [DecidableEq I] (e : I ≃ I) (j : I) :
    ApplyGate (permMatrix e) (Ket j) = Ket (e j) := by
  funext i
  simp only [ApplyGate, permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single j
    (fun k _ hk => by
      have h0 : (if k = j then (1 : ℂ) else 0) = 0 := by simp [hk]
      rw [h0, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- The register relabeling induced by a wire permutation: each register is read through the
inverse-permuted wires. -/
def regPermE {n : ℕ} (e : Wire n ≃ Wire n) : Reg n ≃ Reg n :=
  Equiv.arrowCongr e (Equiv.refl Bool)

/-- Reading a register through a wire permutation permutes the wire arguments by the
inverse permutation. -/
theorem regPermE_apply {n : ℕ} (e : Wire n ≃ Wire n) (x : Reg n) :
    regPermE e x = fun w => x (e.symm w) := rfl

/-- The inverse register relabeling is the relabeling by the inverse wire permutation. -/
theorem regPermSymm {n : ℕ} (e : Wire n ≃ Wire n) :
    (regPermE e).symm = regPermE e.symm := by
  rw [regPermE, Equiv.arrowCongr_symm, Equiv.refl_symm]
  rfl

/-- Relabeling by the inverse permutation reads through the forward permutation. -/
theorem regPermE_symm {n : ℕ} (e : Wire n ≃ Wire n) (x : Reg n) :
    regPermE e.symm x = fun w => x (e w) := by
  funext w
  show x ((e.symm).symm w) = x (e w)
  rw [Equiv.symm_symm]

/-- The wire-permutation gate: the permutation matrix of the induced register relabeling. -/
def WirePermGate {n : ℕ} (e : Wire n ≃ Wire n) : Matrix (Reg n) (Reg n) ℂ :=
  permMatrix (regPermE e)

/-- A wire permutation gate is unitary. -/
theorem permGate_uni {n : ℕ} (e : Wire n ≃ Wire n) :
    WirePermGate e ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  permBijUni (regPermE e)

/-- A wire permutation gate sends the basis state of a register to the basis state of the
relabeled register. -/
theorem permGate_ket {n : ℕ} (e : Wire n ≃ Wire n) (x : Reg n) :
    ApplyGate (WirePermGate e) (Ket x) = Ket (regPermE e x) :=
  permBijKet (regPermE e) x

/-- A wire permutation gate is inverted by the gate of the inverse wire permutation. -/
theorem permGate_symm {n : ℕ} (e : Wire n ≃ Wire n) :
    WirePermGate e * WirePermGate e.symm = 1 := by
  rw [WirePermGate, WirePermGate, permComp]
  have h : regPermE e ∘ regPermE e.symm = id := by
    funext x w
    show x ((e.symm).symm (e.symm w)) = x w
    rw [Equiv.symm_symm]
    exact congrArg x (e.apply_symm_apply w)
  rw [h]
  exact permId

/-- Conjugating a register matrix by a wire permutation reindexes its entries through the
permuted wires. -/
theorem permConj_entry {n : ℕ} (e : Wire n ≃ Wire n) (M : Matrix (Reg n) (Reg n) ℂ)
    (x y : Reg n) :
    (WirePermGate e * M * WirePermGate e.symm) x y
      = M (regPermE e.symm x) (regPermE e.symm y) := by
  have h1 : (WirePermGate e * M * WirePermGate e.symm) x y
      = ((WirePermGate e * M * WirePermGate e.symm) *ᵥ Ket y) x :=
    (congrFun (matCol _ y) x).symm
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    show WirePermGate e.symm *ᵥ Ket y = Ket (regPermE e.symm y) from
      permBijKet (regPermE e.symm) y,
    matCol]
  have h2 := permBijAct (regPermE e) (fun z => M z (regPermE e.symm y)) x
  rw [regPermSymm] at h2
  exact h2

/-- Transport a wire split along a wire permutation. -/
def selMap {m k : ℕ} (e : Wire (m + k) ≃ Wire (m + k)) (S : SplitSel m k) : SplitSel m k where
  sel := fun j => e (S.sel j)
  compl := fun i => e (S.compl i)
  bij := by
    have h : Sum.elim (fun i => e (S.compl i)) (fun j => e (S.sel j))
        = ⇑e ∘ Sum.elim S.compl S.sel := by
      funext ix
      cases ix with
      | inl i => rfl
      | inr j => rfl
    rw [h]
    exact e.bijective.comp S.bij

/-- Conjugating a placement by a wire permutation moves the placement to the permuted
wires. -/
theorem permPlacedSel {m k : ℕ} (e : Wire (m + k) ≃ Wire (m + k)) (S : SplitSel m k)
    (U : Matrix (Reg k) (Reg k) ℂ) :
    WirePermGate e * PlacedSel S U * WirePermGate e.symm = PlacedSel (selMap e S) U := by
  ext x y
  rw [permConj_entry, regPermE_symm e x, regPermE_symm e y, placedSel_bits, placedSel_bits]
  simp only [selMap]
  rfl

/-- The two-wire register basis equivalence: wire zero becomes the first Boolean factor and
wire one the second. -/
def regTwoBool : Reg 2 ≃ Bool × Bool :=
  (regAppendEquiv 1 1).trans (Equiv.prodCongr regOneBool regOneBool)

/-- Reading a two-wire register through `regTwoBool` reads its two wire bits. -/
theorem regTwoBool_eq (x : Reg 2) :
    regTwoBool x = (x ⟨0, by omega⟩, x ⟨1, by omega⟩) := rfl

/-- The transposition swapping the two wires of a two-wire register. -/
def wireSwap2 : Wire 2 ≃ Wire 2 where
  toFun w := if w = 0 then 1 else 0
  invFun w := if w = 0 then 1 else 0
  left_inv w := by fin_cases w <;> simp
  right_inv w := by fin_cases w <;> simp

/-- The wire transposition is its own inverse. -/
theorem wireSwap2_symm : wireSwap2.symm = wireSwap2 := by
  apply Equiv.ext
  intro w
  fin_cases w <;> rfl

/-- Transporting the public two-qubit SWAP gate along `regTwoBool` gives the wire
transposition gate. -/
theorem perm_swap2 :
    Matrix.reindex regTwoBool.symm regTwoBool.symm swapGate = WirePermGate wireSwap2 := by
  ext x y
  have hL : (Matrix.reindex regTwoBool.symm regTwoBool.symm swapGate) x y
      = (if (x ⟨0, by omega⟩, x ⟨1, by omega⟩) = ((y ⟨0, by omega⟩, y ⟨1, by omega⟩).2,
        (y ⟨0, by omega⟩, y ⟨1, by omega⟩).1) then (1 : ℂ) else 0) := by
    show swapGate (regTwoBool x) (regTwoBool y) = _
    rw [regTwoBool_eq, regTwoBool_eq, swapGate, permMatrix, Matrix.of_apply]
  have hR : WirePermGate wireSwap2 x y
      = (if x = fun w => y (wireSwap2 w) then (1 : ℂ) else 0) := by
    show (permMatrix (regPermE wireSwap2)) x y = _
    rw [permMatrix, Matrix.of_apply, regPermE_apply, wireSwap2_symm]
  rw [hL, hR]
  simp only [Prod.mk.injEq, funext_iff, Fin.forall_fin_two, wireSwap2]
  by_cases hx0 : x ⟨0, by omega⟩ = y ⟨1, by omega⟩ <;>
    by_cases hx1 : x ⟨1, by omega⟩ = y ⟨0, by omega⟩ <;> simp_all

end Qatlib.Concepts.CircuitLang.WirePerm
