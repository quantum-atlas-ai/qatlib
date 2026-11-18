/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CircuitLang.WordRelabel
public import Qatlib.Concepts.CircuitLang.CtrlGates
public import Qatlib.Concepts.CircuitLang.WirePerm

@[expose] public section

/-!
# Conjugated words and a non-commutativity witness

The unified word semantics of the circuit language covers sequential composition (`Denote`), parallel
composition (`placedSel_comm`), and controlled gates (`CtrlGate`); this module adds the
missing fourth operation, conjugation. The adjoint word dagger-gates every step, turns a
query into the supplied oracle adjoint, and lists the steps in reverse order, and its
denotation is exactly the conjugate transpose of the original denotation. A concrete
two-wire witness shows that word order is not commutative: flipping the control wire
does not commute with the controlled NOT it controls.

## Main statements

* `denoteAdj`: the adjoint word denotes the daggered matrix.
* `wordAdjUni`: conjugating a unitary word with a unitary oracle stays unitary.
* `cn_ketTT`/`cn_ketFT`/`cnR_ketTT`/`cnR_ketTF`: both controlled NOTs on basis states.
* `cn_cnR_noncomm`: `cn * cnR ≠ cnR * cn` — sequential order matters.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped Matrix
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.WireReg
open Qatlib.Concepts.CircuitLang.LocGates
open Qatlib.Concepts.CircuitLang.CtrlGates
open Qatlib.Concepts.CircuitLang.WirePerm

namespace Qatlib.Concepts.CircuitLang.WordOps

/-! ## Adjoint words -/

/-- The adjoint of one word step: gates are daggered and a query daggers to the
supplied oracle adjoint (the oracle is word data, so the adjoint of a query depends
on the oracle being daggered). -/
def stepAdj {I : Type*} (oadj : Matrix I I ℂ) : Step I → Step I
  | Step.gate U => Step.gate U.conjTranspose
  | Step.query => Step.gate oadj

/-- The adjoint word: steps daggered and listed in reverse order. -/
def wordAdj {I : Type*} (oadj : Matrix I I ℂ) (C : Circuit I) : Circuit I :=
  (C.map (stepAdj oadj)).reverse

/-- Adjoining a step prepends its daggered step at the end. -/
theorem wordAdjCons {I : Type*} (oadj : Matrix I I ℂ) (s : Step I) (C : Circuit I) :
    wordAdj oadj (s :: C) = wordAdj oadj C ++ [stepAdj oadj s] := by
  simp [wordAdj]

/-- A single daggered step denotes the daggered instruction matrix. -/
theorem denoteStepAdj {I : Type*} [Fintype I] [DecidableEq I] (o : Matrix I I ℂ)
    (s : Step I) :
    Denote o [stepAdj o.conjTranspose s] = (InstMat o s).conjTranspose := by
  cases s with
  | gate U => simp [stepAdj, denote_gate, denote_nil, InstMat]
  | query => simp [stepAdj, denote_gate, denote_nil, InstMat]

/-- The adjoint word denotes the conjugate transpose of the original denotation:
conjugation is an operation of the unified word semantics. -/
theorem denoteAdj {I : Type*} [Fintype I] [DecidableEq I] (o : Matrix I I ℂ)
    (C : Circuit I) :
    Denote o (wordAdj o.conjTranspose C) = (Denote o C).conjTranspose := by
  induction C with
  | nil => simp [wordAdj, denote_nil]
  | cons s C ih =>
      rw [wordAdjCons, denote_append, ih, denoteStepAdj]
      cases s with
      | gate U => rw [denote_gate, Matrix.conjTranspose_mul]; rfl
      | query => rw [denote_query, Matrix.conjTranspose_mul]; rfl

/-- Conjugating a unitary word under a unitary oracle stays unitary: unitarity of the
adjoint word follows from the construction, not from an assumption. -/
theorem wordAdjUni {I : Type*} [Fintype I] [DecidableEq I] (o : Matrix I I ℂ)
    (ho : o ∈ Matrix.unitaryGroup I ℂ) {C : Circuit I} (hC : IsUnitaryCircuit C) :
    Denote o (wordAdj o.conjTranspose C) ∈ Matrix.unitaryGroup I ℂ := by
  rw [denoteAdj]
  exact conjTranspose_mem_unitaryGroup (denote_unitary o ho hC)

/-! ## A non-commutativity witness on two wires -/

/-- A one-wire register is determined by its wire-zero reading. -/
theorem reg1_eq (b : Reg 1) : b = fun _ => b ⟨0, by omega⟩ := by
  funext w
  fin_cases w
  rfl

/-- The one-wire flip used as the controlled-NOT target block, on any one-wire
register vector. -/
theorem cnotU_ketR (v : Reg 1) :
    cnotU *ᵥ Ket v = Ket (fun _ => !(v ⟨0, by omega⟩)) := by
  rw [reg1_eq v]
  exact cnotU_ket (v ⟨0, by omega⟩)

/-- The forward control specification: control wire zero, target wire one. -/
def cnSpec : CtrlSpec 0 1 where
  ctrl := ⟨0, by omega⟩
  rest := Fin.elim0
  targ := fun _ => ⟨1, by omega⟩
  bij := by decide

/-- The reverse control specification: control wire one, target wire zero. -/
def cnSpecR : CtrlSpec 0 1 where
  ctrl := ⟨1, by omega⟩
  rest := Fin.elim0
  targ := fun _ => ⟨0, by omega⟩
  bij := by decide

/-- The forward controlled gate uses wire zero as its control. -/
theorem cnSpec_ctrl : cnSpec.ctrl = ⟨0, by omega⟩ := rfl
/-- The forward controlled gate uses wire one as its target. -/
theorem cnSpec_targ0 :
    (cnSpec.targ ⟨0, by omega⟩ : Wire (0 + 1 + 1)) = ⟨1, by omega⟩ := rfl
/-- The reversed controlled gate uses wire one as its control. -/
theorem cnSpecR_ctrl : cnSpecR.ctrl = ⟨1, by omega⟩ := rfl
/-- The reversed controlled gate uses wire zero as its target. -/
theorem cnSpecR_targ0 :
    (cnSpecR.targ ⟨0, by omega⟩ : Wire (0 + 1 + 1)) = ⟨0, by omega⟩ := rfl

/-- The forward controlled NOT on wires zero (control) and one (target). -/
noncomputable def cn : Matrix (Reg (1 + 1)) (Reg (1 + 1)) ℂ :=
  CtrlGate cnSpec cnotU

/-- The reverse controlled NOT: flips wire zero when wire one is set. -/
noncomputable def cnR : Matrix (Reg (1 + 1)) (Reg (1 + 1)) ℂ :=
  CtrlGate cnSpecR cnotU

/-- The forward controlled NOT sends |11⟩ to |10⟩ (control set, target flips). -/
theorem cn_ketTT :
    cn *ᵥ Ket (fun _ => true) = Ket (fun w => decide (w = ⟨0, by omega⟩)) := by
  rw [cn, ctrlPerm_ket cnSpec cnotU (fun v => fun _ => !(v ⟨0, by omega⟩)) cnotU_ketR
    (fun _ => true), ite_eq_left rfl]
  congr 1
  funext w
  match w with
  | ⟨0, _⟩ => exact ctrlUpd_ctrl cnSpec _ _
  | ⟨1, _⟩ =>
    have h1 := ctrlUpd_targ cnSpec
      ((fun v : Reg 1 => fun _ : Fin 1 => !(v ⟨0, by omega⟩))
        (fun j => (fun _ => true) (cnSpec.targ j))) (fun _ => true) ⟨0, by omega⟩
    have h2 : ((fun v : Reg 1 => fun _ : Fin 1 => !(v ⟨0, by omega⟩))
        (fun j => (fun _ => true) (cnSpec.targ j)) : Fin 1 → Bool) ⟨0, by omega⟩
        = false := rfl
    exact (h1.trans h2).trans rfl

/-- The forward controlled NOT fixes |01⟩ (control clear). -/
theorem cn_ketFT :
    cn *ᵥ Ket (fun w => decide (w = ⟨1, by omega⟩)) = Ket (fun w => decide (w = ⟨1, by omega⟩)) := by
  rw [cn, ctrlPerm_ket cnSpec cnotU (fun v => fun _ => !(v ⟨0, by omega⟩)) cnotU_ketR
    (fun w => decide (w = ⟨1, by omega⟩)), ite_eq_right (by simp [cnSpec_ctrl])]

/-- The reverse controlled NOT sends |11⟩ to |01⟩ (control set, target flips). -/
theorem cnR_ketTT :
    cnR *ᵥ Ket (fun _ => true) = Ket (fun w => decide (w = ⟨1, by omega⟩)) := by
  rw [cnR, ctrlPerm_ket cnSpecR cnotU (fun v => fun _ => !(v ⟨0, by omega⟩)) cnotU_ketR
    (fun _ => true), ite_eq_left rfl]
  congr 1
  funext w
  match w with
  | ⟨0, _⟩ =>
    have h1 := ctrlUpd_targ cnSpecR
      ((fun v : Reg 1 => fun _ : Fin 1 => !(v ⟨0, by omega⟩))
        (fun j => (fun _ => true) (cnSpecR.targ j))) (fun _ => true) ⟨0, by omega⟩
    have h2 : ((fun v : Reg 1 => fun _ : Fin 1 => !(v ⟨0, by omega⟩))
        (fun j => (fun _ => true) (cnSpecR.targ j)) : Fin 1 → Bool) ⟨0, by omega⟩
        = false := rfl
    exact (h1.trans h2).trans rfl
  | ⟨1, _⟩ => exact ctrlUpd_ctrl cnSpecR _ _

/-- The reverse controlled NOT fixes |10⟩ (control clear). -/
theorem cnR_ketTF :
    cnR *ᵥ Ket (fun w => decide (w = ⟨0, by omega⟩)) = Ket (fun w => decide (w = ⟨0, by omega⟩)) := by
  rw [cnR, ctrlPerm_ket cnSpecR cnotU (fun v => fun _ => !(v ⟨0, by omega⟩)) cnotU_ketR
    (fun w => decide (w = ⟨0, by omega⟩)), ite_eq_right (by simp [cnSpecR_ctrl])]

/-- The two opposite controlled NOTs do not commute: in one order they send |11⟩ to
|01⟩, in the other to |10⟩. A concrete witness that sequential order matters in the
unified word semantics. -/
theorem cn_cnR_noncomm : cn * cnR ≠ cnR * cn := by
  intro h
  have h11 := congrArg
    (fun M : Matrix (Reg (1 + 1)) (Reg (1 + 1)) ℂ => ApplyGate M (Ket (fun w => true))) h
  rw [applyGate_mul, applyGate_mul,
    show ApplyGate cn (Ket (fun w => true)) = cn *ᵥ Ket (fun w => true) from rfl, cn_ketTT,
    show ApplyGate cnR (Ket (fun w => true)) = cnR *ᵥ Ket (fun w => true) from rfl, cnR_ketTT,
    show ApplyGate cn (Ket (fun w => decide (w = ⟨1, by omega⟩))) =
      cn *ᵥ Ket (fun w => decide (w = ⟨1, by omega⟩)) from rfl, cn_ketFT,
    show ApplyGate cnR (Ket (fun w => decide (w = ⟨0, by omega⟩))) =
      cnR *ᵥ Ket (fun w => decide (w = ⟨0, by omega⟩)) from rfl, cnR_ketTF] at h11
  have hval := congrFun h11 (fun w => decide (w = ⟨1, by omega⟩))
  simp only [Qatlib.Foundations.PureStateMath.ket_apply, ite_true] at hval
  refine absurd hval ?_
  intro hcon
  have h1 : (1 : ℂ) = 0 := by
    by_cases hd : (fun w : Fin (1 + 1) => decide (w = ⟨1, by omega⟩)) =
        (fun w : Fin (1 + 1) => decide (w = ⟨0, by omega⟩))
    · exact absurd (congrFun hd ⟨0, by omega⟩) (by simp)
    · exact hcon.trans (ite_eq_right hd)
  simp at h1

end Qatlib.Concepts.CircuitLang.WordOps
