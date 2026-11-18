/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.WirePerm
public import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabularyDefs
public import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-!
# Controlled gates with disjoint control and target wires

A controlled gate is specified by one control wire, `m` spectator wires, and `k` target
wires that together enumerate the register exactly once; the enumeration is carried as a
contract field, so a control wire colliding with a target wire is rejected at the field
level. The gate matrix is assembled from `Matrix.blockDiagonal` over the control bit with a
tensor-placed target block, reindexed into the register basis through an equivalence
composed from `regOneBool` and sum-of-arrows equivalences, so unitarity follows from the
block structure.

## Main statements

* `ctrlGate_uni`: a controlled gate with a unitary target block is unitary.
* `ctrlGate_entry`: entry form on raw wire reads.
* `ctrlReg_ext`: registers are equal iff they agree on control, spectator, and target wires.
* `ctrlPerm_ket`: basis-to-basis action for permutation-type target blocks.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped Matrix
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.SelSplit

namespace Qatlib.Concepts.CircuitLang.CtrlGates

/-- One control wire, `m` spectator wires, and `k` target wires of an `(m + k + 1)`-wire
register, enumerated jointly without repetition. -/
structure CtrlSpec (m k : ℕ) where
  /-- The single control wire. -/
  ctrl : Wire (m + k + 1)
  /-- The `m` spectator wires outside control and targets. -/
  rest : Fin m → Wire (m + k + 1)
  /-- The `k` target wires, in target order. -/
  targ : Fin k → Wire (m + k + 1)
  /-- Control, spectator, and target wires jointly enumerate all wires exactly once, so a
  control wire reused as a target wire is rejected here. -/
  bij : Function.Bijective
    (Sum.elim (fun _ : Fin 1 => ctrl) (Sum.elim rest targ))

/-- The full wire enumeration carried by a control specification. -/
def ctrlPart {m k : ℕ} (S : CtrlSpec m k) : Fin 1 ⊕ (Fin m ⊕ Fin k) → Wire (m + k + 1) :=
  Sum.elim (fun _ : Fin 1 => S.ctrl) (Sum.elim S.rest S.targ)

/-- The wire-index equivalence induced by a control specification. -/
noncomputable def ctrlWireE {m k : ℕ} (S : CtrlSpec m k) :
    Fin (m + k + 1) ≃ Fin 1 ⊕ (Fin m ⊕ Fin k) :=
  (Equiv.ofBijective (ctrlPart S) S.bij).symm

/-- The control wire sits in the first summand. -/
theorem ctrlE_ctrl {m k : ℕ} (S : CtrlSpec m k) :
    ctrlWireE S S.ctrl = Sum.inl ⟨0, by omega⟩ := by
  have h1 : ctrlPart S (ctrlWireE S S.ctrl) = S.ctrl :=
    Equiv.ofBijective_apply_symm_apply (ctrlPart S) S.bij S.ctrl
  exact S.bij.1 (h1.trans rfl)

/-- A spectator wire sits in the second summand on the left. -/
theorem ctrlE_rest {m k : ℕ} (S : CtrlSpec m k) (i : Fin m) :
    ctrlWireE S (S.rest i) = Sum.inr (Sum.inl i) := by
  have h1 : ctrlPart S (ctrlWireE S (S.rest i)) = S.rest i :=
    Equiv.ofBijective_apply_symm_apply (ctrlPart S) S.bij (S.rest i)
  exact S.bij.1 (h1.trans rfl)

/-- A target wire sits in the second summand on the right. -/
theorem ctrlE_targ {m k : ℕ} (S : CtrlSpec m k) (j : Fin k) :
    ctrlWireE S (S.targ j) = Sum.inr (Sum.inr j) := by
  have h1 : ctrlPart S (ctrlWireE S (S.targ j)) = S.targ j :=
    Equiv.ofBijective_apply_symm_apply (ctrlPart S) S.bij (S.targ j)
  exact S.bij.1 (h1.trans rfl)

/-- The wire of the control index is the control wire. -/
theorem ctrlW_ctrl {m k : ℕ} (S : CtrlSpec m k) :
    (ctrlWireE S).symm (Sum.inl ⟨0, by omega⟩) = S.ctrl :=
  (Equiv.symm_apply_eq (ctrlWireE S)).mpr (ctrlE_ctrl S).symm

/-- The wire of a left second-summand index is the corresponding spectator wire. -/
theorem ctrlW_rest {m k : ℕ} (S : CtrlSpec m k) (i : Fin m) :
    (ctrlWireE S).symm (Sum.inr (Sum.inl i)) = S.rest i :=
  (Equiv.symm_apply_eq (ctrlWireE S)).mpr (ctrlE_rest S i).symm

/-- The wire of a right second-summand index is the corresponding target wire. -/
theorem ctrlW_targ {m k : ℕ} (S : CtrlSpec m k) (j : Fin k) :
    (ctrlWireE S).symm (Sum.inr (Sum.inr j)) = S.targ j :=
  (Equiv.symm_apply_eq (ctrlWireE S)).mpr (ctrlE_targ S j).symm

/-- The basis equivalence induced by a control specification: a register is read as its
spectator block, its target block, and its control bit. -/
noncomputable def ctrlRegE {m k : ℕ} (S : CtrlSpec m k) :
    Reg (m + k + 1) ≃ (Reg m × Reg k) × Bool :=
  ((((Equiv.arrowCongr (ctrlWireE S) (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin 1) (Fin m ⊕ Fin k) Bool)).trans
    (Equiv.prodCongr regOneBool
      (Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) Bool))).trans
    (Equiv.prodComm Bool (Reg m × Reg k)))

/-- The control equivalence reads a register as its spectator block, its target block, and
its control bit. -/
theorem ctrlRegE_apply {m k : ℕ} (S : CtrlSpec m k) (x : Reg (m + k + 1)) :
    ctrlRegE S x = ((fun i => x (S.rest i), fun j => x (S.targ j)), x S.ctrl) := by
  have h1 : (ctrlRegE S x).1.1 = fun i => x (S.rest i) := by
    have h : (ctrlRegE S x).1.1 = fun i => x ((ctrlWireE S).symm (Sum.inr (Sum.inl i))) := rfl
    rw [h]
    exact funext (fun i => congrArg x (ctrlW_rest S i))
  have h2 : (ctrlRegE S x).1.2 = fun j => x (S.targ j) := by
    have h : (ctrlRegE S x).1.2 = fun j => x ((ctrlWireE S).symm (Sum.inr (Sum.inr j))) := rfl
    rw [h]
    exact funext (fun j => congrArg x (ctrlW_targ S j))
  have h3 : (ctrlRegE S x).2 = x ((ctrlWireE S).symm (Sum.inl ⟨0, by omega⟩)) := rfl
  rw [show ctrlRegE S x = (((ctrlRegE S x).1.1, (ctrlRegE S x).1.2), (ctrlRegE S x).2) from rfl,
    h1, h2, h3, ctrlW_ctrl]

/-- The controlled gate: applies `U` to the target wires exactly when the control wire
reads `true`, and acts as the identity otherwise. -/
noncomputable def CtrlGate {m k : ℕ} (S : CtrlSpec m k) (U : Matrix (Reg k) (Reg k) ℂ) :
    Matrix (Reg (m + k + 1)) (Reg (m + k + 1)) ℂ :=
  Matrix.reindex (ctrlRegE S).symm (ctrlRegE S).symm
    (Matrix.blockDiagonal fun b => if b then TensorGate 1 U else 1)

/-- A controlled gate with a unitary target block is unitary. -/
theorem ctrlGate_uni {m k : ℕ} {S : CtrlSpec m k} {U : Matrix (Reg k) (Reg k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg k) ℂ) :
    CtrlGate S U ∈ Matrix.unitaryGroup (Reg (m + k + 1)) ℂ := by
  refine reidxUnitary _ ?_
  have hU' : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  have hblock : ∀ b : Bool, ((if b then TensorGate 1 U
        else (1 : Matrix (Reg m × Reg k) (Reg m × Reg k) ℂ))ᴴ *
      (if b then TensorGate 1 U else 1)) = 1 := by
    intro b
    cases b
    · simp
    · show (TensorGate 1 U)ᴴ * TensorGate 1 U = 1
      rw [tensorGate_conjTranspose, tensorGate_mul, hU']
      simp [tensorGate_one]
  rw [funext hblock]
  exact Matrix.blockDiagonal_one

/-- Entry form of a controlled gate on raw wire reads: the entry is nonzero only when the
control and spectator wires agree, and then carries the target block `U` when the control
bit is set. -/
theorem ctrlGate_entry {m k : ℕ} (S : CtrlSpec m k) (U : Matrix (Reg k) (Reg k) ℂ)
    (x y : Reg (m + k + 1)) :
    CtrlGate S U x y =
      (if x S.ctrl = y S.ctrl ∧ ∀ i, x (S.rest i) = y (S.rest i) then
        (if x S.ctrl then U (fun j => x (S.targ j)) (fun j => y (S.targ j))
         else if ∀ j, x (S.targ j) = y (S.targ j) then (1 : ℂ) else 0)
      else 0) := by
  rw [CtrlGate]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    ctrlRegE_apply, Matrix.blockDiagonal_apply']
  cases hx : x S.ctrl <;> cases hy : y S.ctrl
  · by_cases hr : ∀ i, x (S.rest i) = y (S.rest i)
    · by_cases ht : ∀ j, x (S.targ j) = y (S.targ j)
      · simp [hr, ht, Matrix.one_apply]
      · simp [hr, ht, funext_iff]
    · simp [hr, funext_iff]
  · simp
  · simp
  · by_cases hr : ∀ i, x (S.rest i) = y (S.rest i)
    · simp [hr, tensorGate_apply]
    · simp [hr, tensorGate_apply, funext_iff]

/-- Two registers of a control specification are equal iff they agree on the control,
spectator, and target wires. -/
theorem ctrlReg_ext {m k : ℕ} (S : CtrlSpec m k) (x y : Reg (m + k + 1)) :
    x = y ↔ x S.ctrl = y S.ctrl ∧ (∀ i, x (S.rest i) = y (S.rest i)) ∧
      ∀ j, x (S.targ j) = y (S.targ j) := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, ⟨fun i => rfl, fun j => rfl⟩⟩
  · rintro ⟨hc, hr, ht⟩
    funext w
    obtain ⟨ix, hix⟩ := S.bij.2 w
    rw [← hix]
    cases ix with
    | inl u => exact hc
    | inr ix' =>
      cases ix' with
      | inl i => exact hr i
      | inr j => exact ht j

/-- Replace the target-wire readings of `x` by the entries of `v`, leaving control and
spectator wires unchanged. -/
noncomputable def ctrlUpd {m k : ℕ} (S : CtrlSpec m k) (v : Reg k) (x : Reg (m + k + 1)) :
    Reg (m + k + 1) := fun w =>
  match ctrlWireE S w with
  | Sum.inl _ => x w
  | Sum.inr (Sum.inl _) => x w
  | Sum.inr (Sum.inr j) => v j

/-- A target update leaves the control wire unchanged. -/
theorem ctrlUpd_ctrl {m k : ℕ} (S : CtrlSpec m k) (v : Reg k) (x : Reg (m + k + 1)) :
    ctrlUpd S v x S.ctrl = x S.ctrl := by
  show (match ctrlWireE S S.ctrl with
    | Sum.inl _ => x S.ctrl
    | Sum.inr (Sum.inl _) => x S.ctrl
    | Sum.inr (Sum.inr j) => v j) = x S.ctrl
  rw [ctrlE_ctrl S]

/-- A target update leaves the spectator wires unchanged. -/
theorem ctrlUpd_rest {m k : ℕ} (S : CtrlSpec m k) (v : Reg k) (x : Reg (m + k + 1))
    (i : Fin m) : ctrlUpd S v x (S.rest i) = x (S.rest i) := by
  show (match ctrlWireE S (S.rest i) with
    | Sum.inl _ => x (S.rest i)
    | Sum.inr (Sum.inl _) => x (S.rest i)
    | Sum.inr (Sum.inr j) => v j) = x (S.rest i)
  rw [ctrlE_rest S]

/-- A target update writes the vector entries on the target wires. -/
theorem ctrlUpd_targ {m k : ℕ} (S : CtrlSpec m k) (v : Reg k) (x : Reg (m + k + 1))
    (j : Fin k) : ctrlUpd S v x (S.targ j) = v j := by
  show (match ctrlWireE S (S.targ j) with
    | Sum.inl _ => x (S.targ j)
    | Sum.inr (Sum.inl _) => x (S.targ j)
    | Sum.inr (Sum.inr j') => v j') = v j
  rw [ctrlE_targ S]

/-- The controlled gate acts on a basis state column-wise: the amplitude at `z` is the
matrix entry at `(z, x)`. -/
theorem ctrlGate_ket {m k : ℕ} (S : CtrlSpec m k) (U : Matrix (Reg k) (Reg k) ℂ)
    (x z : Reg (m + k + 1)) :
    (CtrlGate S U *ᵥ Ket x) z = CtrlGate S U z x :=
  applyGate_eq_mulVec_ket (CtrlGate S U) x z

/-- A register equals a target-updated register iff they agree on the control and spectator
wires and the register's target readings are the update vector. -/
theorem ctrlUpd_ext {m k : ℕ} (S : CtrlSpec m k) (v : Reg k) (x y : Reg (m + k + 1)) :
    y = ctrlUpd S v x ↔ y S.ctrl = x S.ctrl ∧ (∀ i, y (S.rest i) = x (S.rest i)) ∧
      ∀ j, y (S.targ j) = v j := by
  constructor
  · intro h
    exact ⟨by rw [h, ctrlUpd_ctrl], fun i => by rw [h, ctrlUpd_rest],
      fun j => by rw [h, ctrlUpd_targ]⟩
  · rintro ⟨hc, hr, ht⟩
    funext w
    obtain ⟨ix, hix⟩ := S.bij.2 w
    rw [← hix]
    show y (ctrlPart S ix) = (match ctrlWireE S (ctrlPart S ix) with
      | Sum.inl _ => x (ctrlPart S ix)
      | Sum.inr (Sum.inl _) => x (ctrlPart S ix)
      | Sum.inr (Sum.inr j) => v j)
    have hE : ctrlWireE S (ctrlPart S ix) = ix := Equiv.symm_apply_apply _ ix
    rw [hE]
    cases ix with
    | inl u => exact hc
    | inr ix' =>
      cases ix' with
      | inl i => exact hr i
      | inr j => exact ht j

/-- If the target block sends basis states to basis states through `upd`, then the
controlled gate fixes the basis state when the control bit is clear and updates the target
wires when it is set. -/
theorem ctrlPerm_ket {m k : ℕ} (S : CtrlSpec m k) (U : Matrix (Reg k) (Reg k) ℂ)
    (upd : Reg k → Reg k) (hU : ∀ v, U *ᵥ Ket v = Ket (upd v))
    (x : Reg (m + k + 1)) :
    CtrlGate S U *ᵥ Ket x =
      if x S.ctrl then Ket (ctrlUpd S (upd (fun j => x (S.targ j))) x) else Ket x := by
  have hUcol : ∀ a b : Reg k, U a b = if a = upd b then (1 : ℂ) else 0 := by
    intro a b
    have h := congrFun (hU b) a
    rw [Qatlib.Concepts.CircuitLang.WirePerm.matCol U b] at h
    simpa [Qatlib.Foundations.PureStateMath.Ket] using h
  funext z
  rw [show (CtrlGate S U *ᵥ Ket x) z = CtrlGate S U z x from
      congrFun (Qatlib.Concepts.CircuitLang.WirePerm.matCol _ x) z,
    ctrlGate_entry S U z x, hUcol]
  by_cases hc : x S.ctrl
  · rw [ite_eq_left hc]
    simp only [Qatlib.Foundations.PureStateMath.ket_apply, ctrlUpd_ext]
    by_cases hzc : z S.ctrl = x S.ctrl
    · have hzc' : z S.ctrl = true := hzc.trans hc
      by_cases hr : ∀ i, z (S.rest i) = x (S.rest i)
      · have hcand : z S.ctrl = x S.ctrl ∧ ∀ i, z (S.rest i) = x (S.rest i) := ⟨hzc, hr⟩
        by_cases ht : (fun j => z (S.targ j)) = upd (fun j => x (S.targ j))
        · have htriple : z S.ctrl = x S.ctrl ∧ (∀ i, z (S.rest i) = x (S.rest i)) ∧
              ∀ j, z (S.targ j) = upd (fun j => x (S.targ j)) j :=
            ⟨hzc, ⟨hr, fun j => congrFun ht j⟩⟩
          rw [ite_eq_left hcand, ite_eq_left hzc', ite_eq_left ht, ite_eq_left htriple]
        · rw [ite_eq_left hcand, ite_eq_left hzc', ite_eq_right ht,
            ite_eq_right (fun hh => ht (funext hh.2.2))]
      · rw [ite_eq_right (fun h => hr h.2), ite_eq_right (fun h => hr h.2.1)]
    · rw [ite_eq_right (fun h => hzc h.1), ite_eq_right (fun h => hzc h.1)]
  · rw [ite_eq_right hc]
    simp only [Qatlib.Foundations.PureStateMath.ket_apply]
    by_cases hzc : z S.ctrl = x S.ctrl
    · have hzc' : z S.ctrl = false := by
        rw [hzc]
        simpa using hc
      by_cases hr : ∀ i, z (S.rest i) = x (S.rest i)
      · have hcand : z S.ctrl = x S.ctrl ∧ ∀ i, z (S.rest i) = x (S.rest i) := ⟨hzc, hr⟩
        by_cases ht : ∀ j, z (S.targ j) = x (S.targ j)
        · have htriple : z S.ctrl = x S.ctrl ∧ (∀ i, z (S.rest i) = x (S.rest i)) ∧
              ∀ j, z (S.targ j) = x (S.targ j) := ⟨hzc, ⟨hr, ht⟩⟩
          rw [ite_eq_left hcand, ite_eq_right (by simp [hzc']),
            ite_eq_left ht, ite_eq_left ((ctrlReg_ext S z x).mpr htriple)]
        · rw [ite_eq_left hcand, ite_eq_right (by simp [hzc']),
            ite_eq_right ht, ite_eq_right (fun h => ht ((ctrlReg_ext S z x).mp h).2.2)]
      · rw [ite_eq_right (fun h => hr h.2),
          ite_eq_right (fun h => hr ((ctrlReg_ext S z x).mp h).2.1)]
    · rw [ite_eq_right (fun h => hzc h.1),
        ite_eq_right (fun h => hzc ((ctrlReg_ext S z x).mp h).1)]

/-- The one-wire Pauli X block, transported from the public Boolean Pauli X through
`regOneBool`. -/
noncomputable def cnotU : Matrix (Reg 1) (Reg 1) ℂ :=
  relabelGate regOneBool.symm PauliX

/-- The transported Pauli X block is unitary. -/
theorem cnotU_uni : cnotU ∈ Matrix.unitaryGroup (Reg 1) ℂ :=
  (relabelGate_mem_unitaryGroup regOneBool.symm PauliX).2 pauliX_unitary

/-- The transported Pauli X block flips the basis state of a one-wire register. -/
theorem cnotU_ket (b : Bool) : cnotU *ᵥ Ket (fun _ => b) = Ket (fun _ => !b) := by
  funext z
  have hz : z ⟨0, by omega⟩ = !b → z = fun _ => !b := by
    intro h
    funext w
    rw [Subsingleton.elim w ⟨0, by omega⟩]
    exact h
  have hr1 : regOneBool z = z ⟨0, by omega⟩ := rfl
  have hr2 : regOneBool (fun _ => b) = b := rfl
  rw [show (cnotU *ᵥ Ket (fun _ => b)) z = cnotU z (fun _ => b) from
      congrFun (Qatlib.Concepts.CircuitLang.WirePerm.matCol _ _) z,
    cnotU, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    PauliX, permMatrix, Matrix.of_apply, hr1, hr2,
    Qatlib.Foundations.PureStateMath.Ket]
  by_cases h : z ⟨0, by omega⟩ = !b
  · rw [ite_eq_left h, ite_eq_left (hz h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (congrFun hh ⟨0, by omega⟩))]

/-- The controlled-NOT gate built from a control specification with a single target
wire. -/
noncomputable def cnot {m : ℕ} (S : CtrlSpec m 1) :
    Matrix (Reg (m + 1 + 1)) (Reg (m + 1 + 1)) ℂ :=
  CtrlGate S cnotU

/-- The controlled-NOT gate is unitary. -/
theorem cnot_uni {m : ℕ} (S : CtrlSpec m 1) :
    cnot S ∈ Matrix.unitaryGroup (Reg (m + 1 + 1)) ℂ :=
  ctrlGate_uni cnotU_uni

/-- The transported Pauli X block flips the bit read by any one-wire register state. -/
theorem cnotU_ketAll (v : Reg 1) :
    cnotU *ᵥ Ket v = Ket (fun _ => !v ⟨0, by omega⟩) := by
  have hv : v = fun _ => v ⟨0, by omega⟩ := by
    funext w
    rw [Subsingleton.elim w ⟨0, by omega⟩]
  rw [hv, cnotU_ket]

/-- The controlled-NOT gate fixes a basis state when the control wire is clear and flips the
single target wire when the control wire is set. -/
theorem cnot_ket {m : ℕ} (S : CtrlSpec m 1) (x : Reg (m + 1 + 1)) :
    cnot S *ᵥ Ket x =
      if x S.ctrl then Ket (ctrlUpd S (fun _ => !x (S.targ ⟨0, by omega⟩)) x)
      else Ket x := by
  rw [cnot, ctrlPerm_ket S cnotU (fun v => fun _ => !(v ⟨0, by omega⟩)) cnotU_ketAll x]

end Qatlib.Concepts.CircuitLang.CtrlGates
