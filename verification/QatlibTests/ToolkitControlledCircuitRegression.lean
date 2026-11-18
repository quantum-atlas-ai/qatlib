/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.WordRelabel
public import Qatlib.Concepts.CircuitLang.SelSplit
public import Qatlib.Concepts.CircuitLang.WirePerm
public import Qatlib.Concepts.CircuitLang.CtrlGates
public import Qatlib.Concepts.CircuitLang.QueryWords
public import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
public import Qatlib.Foundations.QueryWordCore.Circuit

/-! Circuit regression checks for arbitrary
injective wire selections, controlled gates with disjoint control and target wires, and wire
permutations are exercised on concrete instances, including non-adjacent target wires and a
three-wire Toffoli-shaped gate matched against the public Toffoli matrix. Negative examples
reject a control wire colliding with its target wire, a non-unitary placed block via
`reidxUniIff`, and the permutation matrix of a non-bijective wire map. Queries are counted by `QueryCount`. -/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.WordRelabel
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.SelSplit
open Qatlib.Concepts.CircuitLang.WirePerm
open Qatlib.Concepts.CircuitLang.CtrlGates
open scoped Matrix

namespace QatlibTests.ToolkitControlledCircuit

/-- A three-wire split selecting the middle wire one, with the non-adjacent wires zero and
two as complement. -/
def midSel : SplitSel 2 1 where
  sel := fun _ => ⟨1, by omega⟩
  compl := fun i => if i = 0 then ⟨0, by omega⟩ else ⟨2, by omega⟩
  bij := by decide

/-- Regression: placing the one-wire Hadamard on the middle wire of three, away from its
non-adjacent complement, preserves unitarity. -/
theorem placed_uni_wit :
    PlacedSel midSel (HadamardN 1) ∈ Matrix.unitaryGroup (Reg (2 + 1)) ℂ :=
  placedSel_uni (hadamardN_unitary 1)

/-- Regression: placement on the canonical split equals the last-wire placement. -/
theorem placedLast_eq (U : Matrix (Reg 1) (Reg 1) ℂ) :
    PlacedSel (canSplit 1 1) U = PlacedLast 1 1 U :=
  placedSel_last 1 1 U

/-- A two-wire control specification with control wire zero and target wire one. -/
def cnot01 : CtrlSpec 0 1 where
  ctrl := ⟨0, by omega⟩
  rest := Fin.elim0
  targ := fun _ => ⟨1, by omega⟩
  bij := by decide

/-- Regression: the two-wire controlled NOT flips the target wire exactly when the control
wire is set, on every basis state. -/
theorem ctrl_cnot_ket (x : Reg 2) :
    cnot cnot01 *ᵥ Ket x
      = Ket (Function.update x ⟨1, by omega⟩ (x ⟨1, by omega⟩ ^^ x ⟨0, by omega⟩)) := by
  rw [cnot_ket cnot01 x, show cnot01.ctrl = (⟨0, by omega⟩ : Wire 2) from rfl]
  by_cases hc : x ⟨0, by omega⟩
  · rw [ite_eq_left hc]
    show Qatlib.Foundations.PureStateMath.Ket
        (ctrlUpd cnot01 (fun _ => !(x ⟨1, by omega⟩)) x) = _
    have hEq : ctrlUpd cnot01 (fun _ => !(x ⟨1, by omega⟩)) x
        = Function.update x ⟨1, by omega⟩ (x ⟨1, by omega⟩ ^^ x ⟨0, by omega⟩) := by
      refine ((ctrlUpd_ext cnot01 _ x _).mpr ⟨?_, fun i => i.elim0, ?_⟩).symm
      · have h0 : cnot01.ctrl = (⟨0, by omega⟩ : Wire 2) := rfl
        rw [h0, Function.update_of_ne (by decide)]
      · intro j
        have h1 : cnot01.targ j = (⟨1, by omega⟩ : Wire 2) := rfl
        rw [h1, Function.update_self]
        show (x ⟨1, by omega⟩ ^^ x ⟨0, by omega⟩) = !x ⟨1, by omega⟩
        rw [hc]
        simp
    rw [hEq]
  · rw [ite_eq_right hc]
    have hcf : x ⟨0, by omega⟩ = false := by simpa using hc
    congr 1
    funext w
    fin_cases w
    · simp [Function.update]
    · show x ⟨1, by omega⟩ = (x ⟨1, by omega⟩ ^^ x ⟨0, by omega⟩)
      rw [hcf]
      simp

/-- Regression: a controlled gate with a unitary target block is unitary. -/
theorem ctrl_uni_wit :
    CtrlGate cnot01 cnotU ∈ Matrix.unitaryGroup (Reg (0 + 1 + 1)) ℂ :=
  ctrlGate_uni cnotU_uni

/-- A three-wire control specification with control wire zero and target wires one and
two, without spectators. -/
def toff2Spec : CtrlSpec 0 2 where
  ctrl := ⟨0, by omega⟩
  rest := Fin.elim0
  targ := fun j => if j = 0 then ⟨1, by omega⟩ else ⟨2, by omega⟩
  bij := by decide

/-- The CNOT block action on a two-wire register: flip the second wire when the first is
set. -/
def upd2 (v : Reg 2) : Reg 2 := fun w =>
  if w = ⟨0, by omega⟩ then v ⟨0, by omega⟩ else v ⟨1, by omega⟩ ^^ v ⟨0, by omega⟩

/-- The transported CNOT block sends each two-wire basis state to the flipped one. -/
theorem u2_ket (v : Reg 2) :
    (relabelGate regTwoBool.symm CNOT) *ᵥ Ket v = Ket (upd2 v) := by
  funext z
  rw [show ((relabelGate regTwoBool.symm CNOT) *ᵥ Ket v) z
      = (relabelGate regTwoBool.symm CNOT) z v from
      congrFun (Qatlib.Concepts.CircuitLang.WirePerm.matCol _ v) z]
  rw [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    CNOT, permMatrix, Matrix.of_apply, regTwoBool_eq, regTwoBool_eq, cnotFlip,
    Qatlib.Foundations.PureStateMath.ket_apply]
  simp only [Prod.mk.injEq, funext_iff, Fin.forall_fin_two, upd2]
  by_cases hz0 : z ⟨0, by omega⟩ = v ⟨0, by omega⟩
  · by_cases hz1 : z ⟨1, by omega⟩ = (v ⟨1, by omega⟩ ^^ v ⟨0, by omega⟩)
    · simp_all
    · simp_all
  · simp_all

/-- Regression: the three-wire doubly-controlled bit flip, built from a control wire and a
transported CNOT block, is unitary. -/
theorem ctrl_toff_uni :
    CtrlGate toff2Spec (relabelGate regTwoBool.symm CNOT)
      ∈ Matrix.unitaryGroup (Reg (0 + 2 + 1)) ℂ :=
  ctrlGate_uni ((relabelGate_mem_unitaryGroup regTwoBool.symm CNOT).2 cnot_unitary)

/-- Regression: the three-wire doubly-controlled bit flip flips wire two exactly when both
wire zero and wire one are set, on every basis state. -/
theorem ctrl_toff_ket (x : Reg 3) :
    CtrlGate toff2Spec (relabelGate regTwoBool.symm CNOT) *ᵥ Ket x
      = Ket (Function.update x ⟨2, by omega⟩
          (x ⟨2, by omega⟩ ^^ (x ⟨0, by omega⟩ && x ⟨1, by omega⟩))) := by
  rw [ctrlPerm_ket toff2Spec (relabelGate regTwoBool.symm CNOT) upd2 u2_ket x,
    show toff2Spec.ctrl = (⟨0, by omega⟩ : Wire 3) from rfl]
  by_cases hx0 : x ⟨0, by omega⟩
  · rw [ite_eq_left hx0]
    have hxEq : ctrlUpd toff2Spec (upd2 (fun j => x (toff2Spec.targ j))) x
        = Function.update x ⟨2, by omega⟩
            (x ⟨2, by omega⟩ ^^ (x ⟨0, by omega⟩ && x ⟨1, by omega⟩)) := by
      refine ((ctrlUpd_ext toff2Spec _ x _).mpr ⟨?_, fun i => i.elim0, ?_⟩).symm
      · have h0 : toff2Spec.ctrl = (⟨0, by omega⟩ : Wire 3) := rfl
        rw [h0, Function.update_of_ne (by decide)]
      · intro j
        fin_cases j
        · have hj : toff2Spec.targ ⟨0, by omega⟩ = (⟨1, by omega⟩ : Wire 3) := rfl
          rw [hj, Function.update_of_ne (by decide)]
          simp [toff2Spec, upd2]
        · have hj : toff2Spec.targ ⟨1, by omega⟩ = (⟨2, by omega⟩ : Wire 3) := rfl
          rw [hj, Function.update_self]
          show (x ⟨2, by omega⟩ ^^ (x ⟨0, by omega⟩ && x ⟨1, by omega⟩))
              = (x ⟨2, by omega⟩ ^^ x ⟨1, by omega⟩)
          rw [hx0]
          simp
    rw [hxEq]
  · rw [ite_eq_right hx0]
    congr 1
    funext w
    fin_cases w
    · simp [Function.update]
    · simp [Function.update]
    · show x ⟨2, by omega⟩ = (x ⟨2, by omega⟩ ^^ (x ⟨0, by omega⟩ && x ⟨1, by omega⟩))
      have hxf : x ⟨0, by omega⟩ = false := by simpa using hx0
      rw [hxf]
      simp

/-- Regression: controlling the transported CNOT gives the public Toffoli matrix,
so the equality holds on arbitrary superpositions as well as basis states. -/
theorem ctrl_toff_eq :
    CtrlGate toff2Spec (relabelGate regTwoBool.symm CNOT) =
      toffoliGate (0 : Fin 3) 1 2 := by
  apply matrix_ext_on_kets
  intro x
  have h0 : (⟨0, by decide⟩ : Fin 3) = (0 : Fin 3) := by
    apply Fin.ext
    norm_num
  have h1 : (⟨1, by decide⟩ : Fin 3) = (1 : Fin 3) := by
    apply Fin.ext
    norm_num
  have h2 : (⟨2, by decide⟩ : Fin 3) = (2 : Fin 3) := by
    apply Fin.ext
    norm_num
  rw [ctrl_toff_ket, toffoliGate]
  simpa only [ApplyGate, toffoliUpdate, h0, h1, h2] using
    (applyGate_permMatrix_ket (toffoliUpdate_involutive (0 : Fin 3) 1 2
      (by decide) (by decide)) x).symm

/-- Regression: the transported public SWAP is unitary on `Reg 2`. -/
theorem perm_two_uni :
    Matrix.reindex regTwoBool.symm regTwoBool.symm swapGate
      ∈ Matrix.unitaryGroup (Reg 2) ℂ :=
  reidxUnitary _ swapGate_unitary

/-- Regression: the transported public SWAP is the wire-transposition gate. -/
theorem perm_swap_rw :
    Matrix.reindex regTwoBool.symm regTwoBool.symm swapGate = WirePermGate wireSwap2 :=
  perm_swap2

/-- Regression: denotation commutes with relabeling on a one-query word over a one-wire
register; the single query denotes the relabeled oracle itself. -/
theorem denoteRel_wit :
    Denote (relabelGate regOneBool (HadamardN 1)) (relabelCircuit regOneBool [Step.query])
      = relabelGate regOneBool (HadamardN 1) := by
  rw [denoteRelabel, denoteQOne]

/-- Negative example: a control wire reused as the target wire cannot enumerate the
register, so the collision is rejected at the field level. -/
theorem ctrlDup_reject :
    ¬ Function.Bijective
      (Sum.elim (fun _ : Fin 1 => (0 : Wire 2))
        (Sum.elim Fin.elim0 (fun _ : Fin 1 => (0 : Wire 2)))) := by
  intro h
  have h2 : (Sum.inl ⟨0, by omega⟩ : Fin 1 ⊕ (Fin 0 ⊕ Fin 1))
      = Sum.inr (Sum.inr ⟨0, by omega⟩) :=
    h.1 rfl
  exact absurd h2 (by decide)

/-- Negative example: placing a non-unitary block, twice the identity, stays non-unitary;
reflection goes through `reidxUniIff`. -/
theorem nonUni_reject :
    ¬ (PlacedSel (canSplit 1 1) ((2 : ℂ) • (1 : Matrix (Reg 1) (Reg 1) ℂ))
        ∈ Matrix.unitaryGroup (Reg (1 + 1)) ℂ) := by
  intro h
  have h2 : (((2 : ℂ) • (1 : Matrix (Reg 1) (Reg 1) ℂ))ᴴ
      * ((2 : ℂ) • (1 : Matrix (Reg 1) (Reg 1) ℂ))) = (4 : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Matrix.mul_one]
    congr 1
    simp
    norm_num
  rw [PlacedSel, reidxUniIff, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    tensorGate_conjTranspose, tensorGate_mul, h2] at h
  have e := congrFun (congrFun h ((fun _ => false, fun _ => false) : Reg 1 × Reg 1))
    ((fun _ => false, fun _ => false) : Reg 1 × Reg 1)
  rw [tensorGate_apply, Matrix.smul_apply, Matrix.one_apply] at e
  rw [Matrix.one_apply] at e
  rw [ite_eq_left rfl, ite_eq_left rfl] at e
  norm_num at e

/-- Negative example: the permutation matrix of a non-bijective constant wire map is not
unitary. -/
theorem permNonBij_rej :
    ¬ (permMatrix (fun _ : Wire 2 => (0 : Wire 2)) ∈ Matrix.unitaryGroup (Wire 2) ℂ) := by
  intro h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
  have e := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at e
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_two] at e
  norm_num at e

end QatlibTests.ToolkitControlledCircuit
