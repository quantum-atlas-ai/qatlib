/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGThreshold
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSelectFour
import Qatlib.Concepts.MatrixAccess.RitzPipeline.WireContext
import Mathlib.Data.Nat.ModEq
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSplice
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplier

/-!
# Reversible modular word arithmetic

This module builds Boolean graphs and reflection-gate words for remainder, modular addition, and
modular multiplication. It verifies their action on basis states, legal gate compilation,
explicit inverses, and polynomial resource bounds using the reversible computation framework
described in [NielsenChuang2010].

The guarded arithmetic functions act modulo a positive modulus on inputs below it and fix other
inputs. The native words implement addition and subtraction in place, and multiplication in
place when the operand and modulus are coprime, while restoring their ancillary registers.

## Main statements

* `remainder_only_basis`: verifies the remainder output update.
* `ModularReversibleWord.mod_add_value` and `ModularReversibleWord.mod_mul_value`: identify the
  arithmetic values.
* `InPlace.basis`: turns a pair of inverse value functions into an in-place circuit.
* `ModularReversibleWord.frontier1`: collects native arithmetic correctness and resource bounds.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.MatrixAccess.RitzPipeline

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Matrix
open scoped Classical
set_option autoImplicit false

/-- The output selector retaining the remainder wires of the Boolean word division graph. -/
def remSelect (w : ℕ) : Fin (2*w) → Fin (2*w+((booleanWordDivProgram w).nodes+w)) :=
  fun j => booleanWordDivSelect w ⟨w+j.val,by have := j.isLt; omega⟩

/-- The compiled remainder circuit XORs the computed remainder into the output register while
preserving the operand input and restoring the scratch register. -/
theorem remainder_only_basis (w : ℕ) (a b : Reg w) (y : Reg (2*w)) :
    let n := (booleanWordDivProgram w).nodes+w
    Run (1 : Matrix (Reg (2*w+n+2*w)) (Reg (2*w+n+2*w)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordDivDAG w) (remSelect w)))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w) n (2*w) (booleanWordAdderInput w a b) y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w) n (2*w) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordDivRemainder w a b j)) := by
  exact boolean_dag_basis _ _ _ _

/-- The remainder circuit is legal, uses zero queries, and has the stated quadratic bounds on
scratch size, gate count, and total register width. -/
theorem remainder_only_resources (w : ℕ) :
    let n := (booleanWordDivProgram w).nodes+w
    let gs := booleanDAGSteps (booleanWordDivDAG w) (remSelect w)
    n ≤ 20*w^2+6*w+1 ∧ reflectionLegal gs ∧
      gs.length ≤ 600*w^2+182*w+30 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      2*w+n+2*w ≤ 20*w^2+10*w+1 := by
  have hn := (boolean_word_div_resources w).1
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources (booleanWordDivDAG w) (remSelect w)
  exact ⟨hn,hl,by nlinarith,hq,hc,by nlinarith⟩

/-- The selected division graph output represents the natural remainder of the two input word
values. -/
theorem remainder_all_inputs (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue (2*w) (fun j =>
      booleanDAGValue (booleanWordDivDAG w) (booleanWordAdderInput w a b)
        (remSelect w j)) = booleanWordLSBValue w a % booleanWordLSBValue w b :=
  (boolean_word_div_value w a b).2

/-- The output routing that combines existing outputs with outputs of a spliced Boolean graph. -/
def jointOut {M K m n u v : ℕ} (r : Fin m → Fin (M+K))
    (old : Fin u → Fin (M+K)) (new : Fin v → Fin (m+n)) :
    Fin (u+v) → Fin (M+(K+n)) := fun j =>
  if hj : j.val < u then Fin.castLE (by omega) (old ⟨j.val,hj⟩)
  else booleanSpliceSource r (new ⟨j.val-u,by have := j.isLt; omega⟩)

/-- Evaluating selected outputs of a spliced graph agrees with evaluating the appended graph on
the routed outputs of the original graph. -/
theorem multioutput_new {M K m n v : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n)
    (out : Fin v → Fin (m+n)) (x : Reg M) :
    (fun j => booleanDAGValue (booleanDAGSplice g r h) x (booleanSpliceSource r (out j))) =
      fun j => booleanDAGValue h (fun k => booleanDAGValue g x (r k)) (out j) := by
  funext j
  exact boolean_dag_splice_value g r h x (out j)

/-- Splicing the division graph onto two selected operand words computes their natural
remainder. -/
theorem spliced_remainder_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) (x : Reg M) :
    let r : Fin (2*w) → Fin (M+K) := fun j =>
      if hj : j.val < w then a ⟨j.val,hj⟩ else b ⟨j.val-w,by omega⟩
    booleanWordLSBValue (2*w) (fun j =>
      booleanDAGValue (booleanDAGSplice g r (booleanWordDivDAG w)) x
        (booleanSpliceSource r (remSelect w j))) =
      booleanWordLSBValue w (fun j => booleanDAGValue g x (a j)) %
        booleanWordLSBValue w (fun j => booleanDAGValue g x (b j)) := by
  (try dsimp only)
  rw [multioutput_new]
  have hr : (fun k : Fin (2*w) => booleanDAGValue g x
      (if hk : k.val < w then a ⟨k.val,hk⟩ else b ⟨k.val-w,by omega⟩)) =
      booleanWordAdderInput w (fun j => booleanDAGValue g x (a j))
        (fun j => booleanDAGValue g x (b j)) := by
    funext k
    by_cases hk : k.val < w <;> simp [booleanWordAdderInput,hk]
  rw [hr]
  exact (boolean_word_div_value w _ _).2

/-- The routing that concatenates two selected operand words for a division graph. -/
def divRoute {M K : ℕ} (w : ℕ) (a b : Fin w → Fin (M+K)) :
    Fin (2*w) → Fin (M+K) := fun j =>
  if hj : j.val < w then a ⟨j.val,hj⟩ else b ⟨j.val-w,by omega⟩

/-- The graph obtained by appending a word division graph to two selected operand words. -/
def appendRemainder {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) :
    BooleanDAG M (K+((booleanWordDivProgram w).nodes+w)) :=
  booleanDAGSplice g (divRoute w a b) (booleanWordDivDAG w)

/-- The selector for the remainder outputs of an appended division graph. -/
def appendRemainderSelect {M K : ℕ} (w : ℕ)
    (a b : Fin w → Fin (M+K)) :
    Fin (2*w) → Fin (M+(K+((booleanWordDivProgram w).nodes+w))) :=
  fun j => booleanSpliceSource (divRoute w a b) (remSelect w j)

/-- The selected output of `appendRemainder` represents the remainder of the two routed operand
values. -/
theorem append_remainder_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) (x : Reg M) :
    booleanWordLSBValue (2*w) (fun j =>
      booleanDAGValue (appendRemainder g w a b) x (appendRemainderSelect w a b j)) =
      booleanWordLSBValue w (fun j => booleanDAGValue g x (a j)) %
        booleanWordLSBValue w (fun j => booleanDAGValue g x (b j)) :=
  spliced_remainder_value g w a b x

/-- Appending a remainder graph gives a legal circuit with zero queries and the stated bounds on
added nodes and gate count. -/
theorem append_remainder_resources {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) :
    let n := (booleanWordDivProgram w).nodes+w
    let gs := booleanDAGSteps (appendRemainder g w a b) (appendRemainderSelect w a b)
    n ≤ 20*w^2+6*w+1 ∧ reflectionLegal gs ∧
      gs.length ≤ 30*K+600*w^2+182*w+30 ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length := by
  have hn := (boolean_word_div_resources w).1
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources
    (appendRemainder g w a b) (appendRemainderSelect w a b)
  exact ⟨hn,hl,by nlinarith,hq,hc⟩

/-- The Boolean graph obtained by appending a false constant node and then a true constant node. -/
def withConstants {M K : ℕ} (g : BooleanDAG M K) : BooleanDAG M ((K+1)+1) :=
  (g.snoc (.constant false)).snoc (.constant true)

/-- The wire selecting the appended constant with value `b`. -/
def constantWire {M K : ℕ} (b : Bool) : Fin (M+((K+1)+1)) :=
  if b then Fin.last (M+(K+1)) else Fin.castSucc (Fin.last (M+K))

/-- The selected constant wire in `withConstants g` evaluates to `b`. -/
theorem constant_wire_value {M K : ℕ} (g : BooleanDAG M K) (x : Reg M) (b : Bool) :
    booleanDAGValue (withConstants g) x (constantWire b) = b := by
  cases b <;> simp [withConstants,constantWire,booleanDAGValue,booleanNodeValue]

/-- The adjoint of a compiled Boolean graph word is a left inverse, has the same length, and is
legal. -/
theorem dag_explicit_inverse {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) :
    reflectionProgramMatrix (reflectionAdjoint (booleanDAGSteps g out)) *
      reflectionProgramMatrix (booleanDAGSteps g out) = 1 ∧
    (reflectionAdjoint (booleanDAGSteps g out)).length =
      (booleanDAGSteps g out).length ∧
    reflectionLegal (reflectionAdjoint (booleanDAGSteps g out)) := by
  have hl := (boolean_dag_resources g out).1
  have hu := reflectionProgramMatrix_unitary _ hl
  refine ⟨?_, reflectionAdjoint_length _, reflectionAdjoint_legal _ hl⟩
  rw [reflectionAdjoint_matrix _ hl]
  exact Matrix.mem_unitaryGroup_iff'.mp hu

end Qatlib.Concepts.HspRecovery.ReductionCore

namespace Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- The input register concatenating two width-`w` operands and a width-`k` modulus. -/
def input (w k : ℕ) (a b : Reg w) (m : Reg k) : Reg (2*w+k) := fun i =>
  if hi : i.val<2*w then booleanWordAdderInput w a b ⟨i.val,hi⟩
  else m ⟨i.val-2*w,by have := i.isLt; omega⟩

/-- The routing selecting the first two operand words from the combined input register. -/
def operandSource (w k : ℕ) : Fin (2*w) → Fin ((2*w+k)+0) :=
  Fin.castLE (by omega)

/-- The operand routing in the empty graph recovers the concatenated operand input. -/
theorem operand_input (w k : ℕ) (a b : Reg w) (m : Reg k) :
    (fun j => booleanDAGValue (.nil : BooleanDAG (2*w+k) 0)
      (input w k a b m) (operandSource w k j)) = booleanWordAdderInput w a b := by
  funext j
  simp [booleanDAGValue,input,operandSource,j.isLt]

/-- The node count of the addition graph, equal to `5 * w + 1`. -/
def addArithNodes (w : ℕ) : ℕ := 0+(5*w+1)
/-- The operand addition graph with an additional modulus input register. -/
def addGraph (w : ℕ) : BooleanDAG (2*w+(w+1)) (addArithNodes w) :=
  booleanDAGSplice .nil (operandSource w (w+1)) (booleanWordAdderDAG w)
/-- The selector for the width-`w + 1` sum output of the addition graph. -/
def addSelect (w : ℕ) : Fin (w+1) → Fin ((2*w+(w+1))+addArithNodes w) :=
  fun j => booleanSpliceSource (M:=2*w+(w+1)) (K:=0) (n:=5*w+1) (operandSource w (w+1)) (booleanWordAdderSelect w j)

/-- The selected addition output represents the sum of the two width-`w` operand values. -/
theorem add_value (w : ℕ) (a b : Reg w) (m : Reg (w+1)) :
    booleanWordLSBValue (w+1) (fun j =>
      booleanDAGValue (addGraph w) (input w (w+1) a b m) (addSelect w j)) =
      booleanWordLSBValue w a + booleanWordLSBValue w b := by
  have he : (fun j => booleanDAGValue (addGraph w) (input w (w+1) a b m) (addSelect w j)) =
      booleanWordAdderResult w a b := by
    funext j
    have h := boolean_dag_splice_value (.nil : BooleanDAG (2*w+(w+1)) 0)
      (operandSource w (w+1)) (booleanWordAdderDAG w) (input w (w+1) a b m)
      (booleanWordAdderSelect w j)
    rw [operand_input] at h
    exact h

  rw [he]
  exact boolean_word_adder_value w a b

/-- The node count of the full multiplication graph. -/
def mulArithNodes (w : ℕ) : ℕ := 0+(booleanWordMulProgram w).nodes
/-- The operand multiplication graph with an additional modulus input register. -/
def mulGraph (w : ℕ) : BooleanDAG (2*w+2*w) (mulArithNodes w) :=
  booleanDAGSplice .nil (operandSource w (2*w)) (booleanWordMulProgram w).graph
/-- The selector for the width-`2 * w` product output of the multiplication graph. -/
def mulSelect (w : ℕ) : Fin (2*w) → Fin ((2*w+2*w)+mulArithNodes w) :=
  fun j => booleanSpliceSource (M:=2*w+2*w) (K:=0) (n:=(booleanWordMulProgram w).nodes) (operandSource w (2*w)) (booleanWordMulSelect w j)

/-- The selected full multiplication output represents the product of the operand values. -/
theorem mul_full_value (w : ℕ) (a b : Reg w) (m : Reg (2*w)) :
    booleanWordLSBValue (2*w) (fun j =>
      booleanDAGValue (mulGraph w) (input w (2*w) a b m) (mulSelect w j)) =
      booleanWordLSBValue w a * booleanWordLSBValue w b := by
  have he : (fun j => booleanDAGValue (mulGraph w) (input w (2*w) a b m) (mulSelect w j)) =
      booleanWordMulResult w a b := by
    funext j
    have h := boolean_dag_splice_value (.nil : BooleanDAG (2*w+2*w) 0)
      (operandSource w (2*w)) (booleanWordMulProgram w).graph (input w (2*w) a b m)
      (booleanWordMulSelect w j)
    rw [operand_input] at h
    exact h

  rw [he]
  exact boolean_word_mul_value w a b

/-- An original input wire retains its input value in any Boolean graph. -/
theorem input_wire {M K : ℕ} (g : BooleanDAG M K) (x : Reg M) (j : Fin M) :
    booleanDAGValue g x (Fin.castLE (by omega) j) = x j := by
  induction g with
  | nil => rfl
  | @snoc K g node ih =>
    simp only [booleanDAGValue]
    have he : (Fin.castLE (by omega) j : Fin (M+(K+1))) =
        Fin.castSucc (Fin.castLE (by omega) j : Fin (M+K)) := Fin.ext rfl
    rw [he,Fin.lastCases_castSucc]
    exact ih

/-- The routing selecting the modulus word from the combined operand and modulus input. -/
def modulusSource (w k K : ℕ) : Fin k → Fin ((2*w+k)+K) := fun j =>
  ⟨2*w+j.val,by have := j.isLt; omega⟩

/-- The modulus routing recovers the modulus word in any graph on the combined input. -/
theorem modulus_input {K : ℕ} (w k : ℕ) (g : BooleanDAG (2*w+k) K)
    (a b : Reg w) (m : Reg k) :
    (fun j => booleanDAGValue g (input w k a b m) (modulusSource w k K j)) = m := by
  funext j
  have he : modulusSource w k K j =
      Fin.castLE (by omega) (⟨2*w+j.val,by have := j.isLt; omega⟩ : Fin (2*w+k)) := Fin.ext rfl
  rw [he,input_wire]
  simp [input,show ¬2*w+j.val<2*w by omega]

end Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord

namespace Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- The node count of the addition graph followed by a remainder graph. -/
def addNodes (w : ℕ) : ℕ := addArithNodes w+((booleanWordDivProgram (w+1)).nodes+(w+1))
/-- The node count of the multiplication graph followed by a remainder graph. -/
def mulNodes (w : ℕ) : ℕ := mulArithNodes w+((booleanWordDivProgram (2*w)).nodes+2*w)

/-- The Boolean graph computing a sum followed by reduction by the modulus input. -/
def modAddGraph (w : ℕ) : BooleanDAG (2*w+(w+1)) (addNodes w) :=
  appendRemainder (addGraph w) (w+1) (addSelect w) (modulusSource w (w+1) (addArithNodes w))
/-- The selector for the remainder output of the modular addition graph. -/
def modAddSelect (w : ℕ) : Fin (2*(w+1)) → Fin ((2*w+(w+1))+addNodes w) :=
  appendRemainderSelect (w+1) (addSelect w) (modulusSource w (w+1) (addArithNodes w))
/-- The output bit string obtained by evaluating the modular addition graph. -/
def modAddResult (w : ℕ) (a b : Reg w) (m : Reg (w+1)) : Reg (2*(w+1)) := fun j =>
  booleanDAGValue (modAddGraph w) (input w (w+1) a b m) (modAddSelect w j)

/-- The Boolean graph computing a product followed by reduction by the modulus input. -/
def modMulGraph (w : ℕ) : BooleanDAG (2*w+2*w) (mulNodes w) :=
  appendRemainder (mulGraph w) (2*w) (mulSelect w) (modulusSource w (2*w) (mulArithNodes w))
/-- The selector for the remainder output of the modular multiplication graph. -/
def modMulSelect (w : ℕ) : Fin (2*(2*w)) → Fin ((2*w+2*w)+mulNodes w) :=
  appendRemainderSelect (2*w) (mulSelect w) (modulusSource w (2*w) (mulArithNodes w))
/-- The output bit string obtained by evaluating the modular multiplication graph. -/
def modMulResult (w : ℕ) (a b : Reg w) (m : Reg (2*w)) : Reg (2*(2*w)) := fun j =>
  booleanDAGValue (modMulGraph w) (input w (2*w) a b m) (modMulSelect w j)

/-- The modular addition result represents the operand sum modulo the input modulus. -/
theorem mod_add_value (w : ℕ) (a b : Reg w) (m : Reg (w+1)) :
    booleanWordLSBValue (2*(w+1)) (modAddResult w a b m) =
      (booleanWordLSBValue w a + booleanWordLSBValue w b) % booleanWordLSBValue (w+1) m := by
  have h := append_remainder_value (addGraph w) (w+1) (addSelect w)
    (modulusSource w (w+1) (addArithNodes w)) (input w (w+1) a b m)
  rw [add_value,modulus_input] at h
  exact h

/-- The modular multiplication result represents the operand product modulo the input modulus. -/
theorem mod_mul_value (w : ℕ) (a b : Reg w) (m : Reg (2*w)) :
    booleanWordLSBValue (2*(2*w)) (modMulResult w a b m) =
      (booleanWordLSBValue w a * booleanWordLSBValue w b) % booleanWordLSBValue (2*w) m := by
  have h := append_remainder_value (mulGraph w) (2*w) (mulSelect w)
    (modulusSource w (2*w) (mulArithNodes w)) (input w (2*w) a b m)
  rw [mul_full_value,modulus_input] at h
  exact h

/-- The reversible reflection-gate word compiled from the modular addition graph. -/
noncomputable def modAddWord (w : ℕ) : List (ReflectionGate ((2*w+(w+1))+addNodes w+2*(w+1))) :=
  booleanDAGSteps (modAddGraph w) (modAddSelect w)
/-- The reversible reflection-gate word compiled from the modular multiplication graph. -/
noncomputable def modMulWord (w : ℕ) : List (ReflectionGate ((2*w+2*w)+mulNodes w+2*(2*w))) :=
  booleanDAGSteps (modMulGraph w) (modMulSelect w)

/-- The modular addition word XORs its result into the output register and preserves the input
and clean scratch registers. -/
theorem mod_add_basis (w : ℕ) (a b : Reg w) (m : Reg (w+1)) (y : Reg (2*(w+1))) :
    Run 1 (reflectionCompile (modAddWord w))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+(w+1)) (addNodes w) (2*(w+1)) (input w (w+1) a b m) y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+(w+1)) (addNodes w) (2*(w+1)) (input w (w+1) a b m)
        (fun j => y j ^^ modAddResult w a b m j)) :=
  boolean_dag_basis _ _ _ _

/-- The modular multiplication word XORs its result into the output register and preserves the
input and clean scratch registers. -/
theorem mod_mul_basis (w : ℕ) (a b : Reg w) (m : Reg (2*w)) (y : Reg (2*(2*w))) :
    Run 1 (reflectionCompile (modMulWord w))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+2*w) (mulNodes w) (2*(2*w)) (input w (2*w) a b m) y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+2*w) (mulNodes w) (2*(2*w)) (input w (2*w) a b m)
        (fun j => y j ^^ modMulResult w a b m j)) :=
  boolean_dag_basis _ _ _ _

/-- The modular addition word is legal, uses zero queries, and satisfies the stated quadratic
bounds on nodes, gates, and total width. -/
theorem mod_add_resources (w : ℕ) :
    addNodes w ≤ 20*w^2+51*w+28 ∧ reflectionLegal (modAddWord w) ∧
    (modAddWord w).length ≤ 600*w^2+1532*w+842 ∧
    QueryCount (reflectionCompile (modAddWord w)) = 0 ∧
    GateCount (reflectionCompile (modAddWord w)) = (modAddWord w).length ∧
    (2*w+(w+1))+addNodes w+2*(w+1) ≤ 20*w^2+56*w+31 := by
  have hn := (boolean_word_div_resources (w+1)).1
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources (modAddGraph w) (modAddSelect w)
  change (modAddWord w).length ≤ 30*(addNodes w)+2*(w+1) at hg
  refine ⟨?_,hl,?_,hq,hc,?_⟩ <;> dsimp only [addNodes,addArithNodes] at * <;> nlinarith

/-- The modular multiplication word is legal, uses zero queries, and satisfies the stated
quadratic bounds on nodes, gates, and total width. -/
theorem mod_mul_resources (w : ℕ) :
    mulNodes w ≤ 91*w^2+13*w+2 ∧ reflectionLegal (modMulWord w) ∧
    (modMulWord w).length ≤ 2730*w^2+394*w+60 ∧
    QueryCount (reflectionCompile (modMulWord w)) = 0 ∧
    GateCount (reflectionCompile (modMulWord w)) = (modMulWord w).length ∧
    (2*w+2*w)+mulNodes w+2*(2*w) ≤ 91*w^2+21*w+2 := by
  have hn := (boolean_word_div_resources (2*w)).1
  have hm := (boolean_word_mul_resources w).1
  obtain ⟨hl,hg,hq,hc⟩ := boolean_dag_resources (modMulGraph w) (modMulSelect w)
  change (modMulWord w).length ≤ 30*(mulNodes w)+2*(2*w) at hg
  refine ⟨?_,hl,?_,hq,hc,?_⟩ <;> dsimp only [mulNodes,mulArithNodes] at * <;> nlinarith

end Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Bits
open Qatlib
open scoped Classical
set_option autoImplicit false

/-- The least-significant-bit value map is injective on bit strings of fixed width. -/
theorem lsb_injective (w : ℕ) : Function.Injective (booleanWordLSBValue w) := by
  intro a b h
  have he : bitVecEquiv w (fun j => a (Fin.rev j)) =
      bitVecEquiv w (fun j => b (Fin.rev j)) := Fin.ext h
  have hr := (bitVecEquiv w).injective he
  funext j
  simpa only [Fin.rev_rev] using! congrFun hr (Fin.rev j)

/-- The value of the low `k` bits is the full word value modulo `2^k`. -/
theorem low_bits_value (W k : ℕ) (hk : k ≤ W) (a : Reg W) :
    booleanWordLSBValue k (fun j => a (Fin.castLE hk j)) = booleanWordLSBValue W a % 2^k :=
  boolean_word_low_value W k hk a

/-- Negating the final conditional-subtraction flag tests whether the first operand value is
less than the second. -/
theorem cond_sub_less_flag (w : ℕ) (a b : Reg w) :
    (!(booleanWordCondSubResult w a b (Fin.last w))) =
      decide (booleanWordLSBValue w a < booleanWordLSBValue w b) := by
  rw [(boolean_word_cond_sub_value w a b).1]
  by_cases h : booleanWordLSBValue w b ≤ booleanWordLSBValue w a
  · have hn : ¬booleanWordLSBValue w a < booleanWordLSBValue w b := by omega
    simp [h,hn]
  · have hl : booleanWordLSBValue w a < booleanWordLSBValue w b := by omega
    simp [h,hl]

/-- Mapping a Boolean evaluation over mux source routing yields the corresponding mux input
word. -/
theorem mux_sources_map {α : Type*} (H : ℕ) (a b : Fin H → α) (c : α) (f : α → Bool) :
    (fun j => f (booleanMuxSources H a b c j)) =
      booleanWordMuxInput H (fun j => f (a j)) (fun j => f (b j)) (f c) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have hn : ¬2*H < H := by omega
    simp [booleanMuxSources,booleanWordMuxInput,hn]
  · rw [booleanWordMuxInput,Fin.snoc_castSucc]
    by_cases hk : k.val < H
    · simp [booleanMuxSources,booleanWordAdderInput,hk]
    · simp [booleanMuxSources,booleanWordAdderInput,hk,k.isLt]

/-- A mux graph spliced onto shared sources selects the first word when its control is true and
the second word otherwise. -/
theorem shared_mux {M K H : ℕ} (g : BooleanDAG M K) (a b : Fin H → Fin (M+K))
    (c : Fin (M+K)) (x : Reg M) :
    (fun j => booleanDAGValue (booleanDAGSplice g (booleanMuxSources H a b c) (booleanWordMuxDAG H)) x
      (booleanSpliceSource (booleanMuxSources H a b c) (booleanWordMuxSelect H j))) =
      if booleanDAGValue g x c then (fun j => booleanDAGValue g x (a j))
      else (fun j => booleanDAGValue g x (b j)) := by
  have hr : (fun j => booleanDAGValue (booleanDAGSplice g (booleanMuxSources H a b c) (booleanWordMuxDAG H)) x
      (booleanSpliceSource (booleanMuxSources H a b c) (booleanWordMuxSelect H j))) =
      booleanWordMuxResult H (fun j => booleanDAGValue g x (a j)) (fun j => booleanDAGValue g x (b j))
        (booleanDAGValue g x c) := by
    funext j
    rw [boolean_dag_splice_value,mux_sources_map]
    rfl
  rw [hr,boolean_word_mux_value]

end Qatlib.Concepts.HspRecovery.ReductionCore.Bits

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Layout
open Matrix
open scoped Classical
set_option autoImplicit false

/-- The Boolean graph's reversible word embedded into a larger register by a wire injection. -/
noncomputable def liftedDAG {m n o L : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (e : Fin (m+n+o) ↪ Fin L) : List (ReflectionGate L) :=
  (booleanDAGSteps g out).map (knownWireGateMap e)

/-- The embedded graph word performs its Boolean output update on the selected wires while
preserving the surrounding register context. -/
theorem lifted_dag_basis {m n o L : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (e : Fin (m+n+o) ↪ Fin L)
    (s : Reg L) (x : Reg m) (y : Reg o) :
    Run 1 (reflectionCompile (liftedDAG g out e))
      (Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s (booleanDAGInput m n o x y))) =
      Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s (booleanDAGInput m n o x (booleanDAGOutput g out x y))) := by
  rw [← wire_context_ket, liftedDAG,
    wire_context_program _ _ e s _ (boolean_dag_resources g out).1,
    boolean_dag_basis, wire_context_ket]

/-- Embedding a graph word preserves legality and length, uses zero queries, and gives a length
bound of `30 * n + o`. -/
theorem lifted_dag_resources {m n o L : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (e : Fin (m+n+o) ↪ Fin L) :
    reflectionLegal (liftedDAG g out e) ∧
      (liftedDAG g out e).length = (booleanDAGSteps g out).length ∧
      (liftedDAG g out e).length ≤ 30*n+o ∧
      QueryCount (reflectionCompile (liftedDAG g out e)) = 0 ∧
      GateCount (reflectionCompile (liftedDAG g out e)) = (booleanDAGSteps g out).length := by
  obtain ⟨hl,hb,hq,hc⟩ := boolean_dag_resources g out
  refine ⟨knownWireMapList_legal e _ hl,
      by simp [liftedDAG], ?_, queryCount_reflectionCompile _, ?_⟩
  · simpa [liftedDAG] using! hb
  · rw [gateCount_reflectionCompile]
    simp [liftedDAG]

/-- The wire injection enlarging the scratch block from `n` to `N` while preserving input and
output positions. -/
def paddedWires (m n o N : ℕ) (hn : n ≤ N) : Fin (m+n+o) ↪ Fin (m+N+o) where
  toFun i := if hi : i.val < m+n then ⟨i.val,by omega⟩
    else ⟨m+N+(i.val-(m+n)),by have := i.isLt; omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    have hi := i.isLt
    have hj := j.isLt
    by_cases h1 : i.val < m+n <;> by_cases h2 : j.val < m+n <;>
      simp [h1,h2] at hv <;> omega

/-- Restricting a padded graph input along `paddedWires` recovers the original graph input. -/
theorem padded_input_at (m n o N : ℕ) (hn : n ≤ N) (x : Reg m) (y : Reg o)
    (i : Fin (m+n+o)) :
    booleanDAGInput m N o x y (paddedWires m n o N hn i) = booleanDAGInput m n o x y i := by
  by_cases hi : i.val < m+n
  · have hN : i.val < m+N := by omega
    by_cases hm : i.val < m <;> simp [paddedWires,hi,booleanDAGInput,hm,hN]
  · have hm : ¬i.val < m := by omega
    have ha : ¬m+N+(i.val-(m+n)) < m := by omega
    have hb : ¬m+N+(i.val-(m+n)) < m+N := by omega
    simp [paddedWires,hi,booleanDAGInput,hm,ha,hb]

/-- Replacing the embedded unpadded graph input and output in a padded register gives the padded
register with the new output. -/
theorem padded_context (m n o N : ℕ) (hn : n ≤ N)
    (x : Reg m) (y z : Reg o) :
    wireContextExtend (paddedWires m n o N hn) (booleanDAGInput m N o x y)
      (booleanDAGInput m n o x z) = booleanDAGInput m N o x z := by
  funext j
  by_cases hj : ∃ i, paddedWires m n o N hn i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [(wire_context_extend _ _ _ _).1]
    exact (padded_input_at m n o N hn x z i).symm
  · rw [(wire_context_extend _ _ _ _).2.1 _ j hj]
    have hwork : j.val < m+N := by
      by_contra hh
      have hjN : m+N ≤ j.val := by omega
      have hi : m+n+(j.val-(m+N)) < m+n+o := by have := j.isLt; omega
      have hni : ¬m+n+(j.val-(m+N)) < m+n := by omega
      apply hj
      refine ⟨⟨m+n+(j.val-(m+N)),hi⟩,?_⟩
      apply Fin.ext
      simp [paddedWires,hni]
      omega
    by_cases hm : j.val < m <;> simp [booleanDAGInput,hm,hwork]

/-- A graph word embedded in padded scratch space performs the same output update and leaves
that scratch space clean. -/
theorem padded_dag_basis {m n o N : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (hn : n ≤ N) (x : Reg m) (y : Reg o) :
    Run 1 (reflectionCompile (liftedDAG g out (paddedWires m n o N hn)))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput m N o x y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput m N o x (booleanDAGOutput g out x y)) := by
  have h := lifted_dag_basis g out (paddedWires m n o N hn)
    (booleanDAGInput m N o x y) x y
  simpa only [padded_context] using! h

/-- For distinct wires, the physical swap word is legal, has length three, and swaps their basis
values. -/
theorem physical_swap {L : ℕ} (a b : Fin L) (hab : a ≠ b) :
    reflectionLegal (knownSwapSteps a b) ∧ (knownSwapSteps a b).length = 3 ∧
      ∀ x : Reg L, Run 1 (reflectionCompile (knownSwapSteps a b)) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (x ∘ Equiv.swap a b) := by
  obtain ⟨hl,_,hb⟩ := knownSwapSteps_spec a b
  exact ⟨hl,by simp [knownSwapSteps,hab],hb⟩

end Qatlib.Concepts.HspRecovery.ReductionCore.Layout

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Arithmetic

/-- Addition of `a` modulo positive `m` on inputs below `m`, extended by the identity elsewhere. -/
def totalAdd (m a x : ℕ) : ℕ := if 0 < m ∧ x < m then (x+a)%m else x
/-- Subtraction of `a` modulo positive `m` on inputs below `m`, extended by the identity
elsewhere. -/
def totalSub (m a x : ℕ) : ℕ := if 0 < m ∧ x < m then (x+m-(a%m))%m else x

/-- The total modular subtraction map reverses the total modular addition map. -/
theorem sub_add (m a x : ℕ) : totalSub m a (totalAdd m a x) = x := by
  by_cases hm : 0 < m
  · by_cases hx : x < m
    · simp only [totalAdd,hm,hx,and_self,ite_true]
      have hz : (x+a)%m < m := Nat.mod_lt _ hm
      simp only [totalSub,hm,hz,and_self,ite_true]
      have hmod : (x+a)%m=(x+a%m)%m := by
        nth_rw 1 [Nat.add_mod]
        rw [Nat.mod_eq_of_lt hx]
      rw [hmod]
      by_cases hs : x+a%m < m
      · rw [Nat.mod_eq_of_lt hs]
        have he : x+a%m+m-a%m=x+m := by omega
        rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt hx]
      · have hr : a%m < m := Nat.mod_lt _ hm
        have hn : x+a%m-m < m := by omega
        rw [Nat.mod_eq_sub_mod (by omega : m ≤ x+a%m),Nat.mod_eq_of_lt hn]
        have he : x+a%m-m+m-a%m=x := by omega
        rw [he,Nat.mod_eq_of_lt hx]
    · simp [totalAdd,totalSub,hm,hx]
  · simp [totalAdd,totalSub,hm]

/-- The total modular addition map reverses the total modular subtraction map. -/
theorem add_sub (m a x : ℕ) : totalAdd m a (totalSub m a x) = x := by
  by_cases hm : 0 < m
  · by_cases hx : x < m
    · simp only [totalSub,hm,hx,and_self,ite_true]
      have hz : (x+m-a%m)%m < m := Nat.mod_lt _ hm
      simp only [totalAdd,hm,hz,and_self,ite_true]
      have hr : a%m < m := Nat.mod_lt _ hm
      have hmod : ((x+m-a%m)%m+a)%m=(x+m-a%m+a%m)%m := by
        rw [Nat.add_mod, Nat.mod_mod]
        nth_rw 2 [Nat.add_mod]
        rw [Nat.mod_mod]
      rw [hmod,Nat.sub_add_cancel (by omega : a%m ≤ x+m),Nat.add_mod_right,Nat.mod_eq_of_lt hx]
    · simp [totalAdd,totalSub,hm,hx]
  · simp [totalAdd,totalSub,hm]

/-- When `m ≤ N`, total modular addition sends inputs below `N` to outputs below `N`. -/
theorem totalAdd_lt (m a x N : ℕ) (hm : m ≤ N) (hx : x < N) : totalAdd m a x  <  N := by
  unfold totalAdd
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans_le hm
  · exact hx

/-- When `m ≤ N`, total modular subtraction sends inputs below `N` to outputs below `N`. -/
theorem totalSub_lt (m a x N : ℕ) (hm : m ≤ N) (hx : x < N) : totalSub m a x  <  N := by
  unfold totalSub
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans_le hm
  · exact hx

/-- The permutation of `Fin N` given by total modular addition, with total modular subtraction
as its inverse. -/
def addEquiv (m a N : ℕ) (hm : m ≤ N) : Fin N ≃ Fin N where
  toFun x := ⟨totalAdd m a x.val,totalAdd_lt m a x.val N hm x.isLt⟩
  invFun x := ⟨totalSub m a x.val,totalSub_lt m a x.val N hm x.isLt⟩
  left_inv x := Fin.ext (sub_add m a x.val)
  right_inv x := Fin.ext (add_sub m a x.val)
end Qatlib.Concepts.HspRecovery.ReductionCore.Arithmetic

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Swap
open Matrix
open Layout
open scoped Classical

/-- The wire injection selecting the left width-`w` block before a scratch block. -/
def left (w N : ℕ) (j : Fin w) : Fin (w+N+w) := ⟨j.val,by have := j.isLt; omega⟩
/-- The wire injection selecting the right width-`w` block after a scratch block. -/
def right (w N : ℕ) (j : Fin w) : Fin (w+N+w) := ⟨w+N+j.val,by have := j.isLt; omega⟩
/-- The register with the first `k` bits exchanged between two width-`w` blocks and a clean
scratch block between them. -/
def state (w N k : ℕ) (x y : Reg w) : Reg (w+N+w) :=
  booleanDAGInput w N w (fun j => if j.val < k then y j else x j)
    (fun j => if j.val < k then x j else y j)

/-- The concatenated physical swap words for the first `k` pairs of corresponding block wires. -/
noncomputable def swapPrefix (w N : ℕ) : (k : ℕ) → k ≤ w → List (ReflectionGate (w+N+w))
  | 0,_ => []
  | k+1,hk => swapPrefix w N k (by omega) ++
      knownSwapSteps (left w N ⟨k,by omega⟩) (right w N ⟨k,by omega⟩)

/-- Swapping the next corresponding wire pair advances the partially swapped register state by
one position. -/
theorem one_state (w N : ℕ) (j : Fin w) (x y : Reg w) :
    state w N j.val x y ∘ Equiv.swap (left w N j) (right w N j) =
      state w N (j.val+1) x y := by
  funext i
  by_cases hl : i = left w N j
  · subst i
    simp [Function.comp_apply,Equiv.swap_apply_left,state,booleanDAGInput,left,right,
      j.isLt,show ¬w+N+j.val < w by omega,show ¬w+N+j.val < w+N by omega]
  · by_cases hr : i = right w N j
    · subst i
      simp [Function.comp_apply,Equiv.swap_apply_right,state,booleanDAGInput,left,right,
        j.isLt,show ¬w+N+j.val < w by omega,show ¬w+N+j.val < w+N by omega]
    · rw [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hl hr]
      by_cases hi : i.val < w
      · have hn : i.val ≠ j.val := by
          intro he
          apply hl
          exact Fin.ext he
        have he : (i.val < j.val) ↔ (i.val < j.val+1) := by omega
        simp [state,booleanDAGInput,hi,he]
      · by_cases hw : i.val < w+N
        · simp [state,booleanDAGInput,hi,hw]
        · have hn : i.val-(w+N) ≠ j.val := by
            intro he
            apply hr
            apply Fin.ext
            dsimp only [right]
            omega
          have he : (i.val-(w+N) < j.val) ↔ (i.val-(w+N) < j.val+1) := by omega
          simp [state,booleanDAGInput,hi,hw,he]

/-- The prefix swap word exchanges exactly the first `k` bits of the two blocks. -/
theorem prefix_basis (w N k : ℕ) (hk : k ≤ w) (x y : Reg w) :
    Run 1 (reflectionCompile (swapPrefix w N k hk)) (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w N w x y)) =
      Qatlib.Foundations.PureStateMath.Ket (state w N k x y) := by
  induction k with
  | zero => simp [swapPrefix,reflectionCompile,state]
  | succ k ih =>
    rw [swapPrefix,reflectionCompile_append,run_append,ih (by omega)]
    rw [(knownSwapSteps_spec (left w N ⟨k,by omega⟩) (right w N ⟨k,by omega⟩)).2.2]
    exact congrArg Qatlib.Foundations.PureStateMath.Ket (one_state w N ⟨k,by omega⟩ x y)

/-- The prefix swap word is legal and has length `3 * k`. -/
theorem prefix_resources (w N k : ℕ) (hk : k ≤ w) :
    reflectionLegal (swapPrefix w N k hk) ∧ (swapPrefix w N k hk).length = 3*k := by
  induction k with
  | zero => simp [swapPrefix,reflectionLegal]
  | succ k ih =>
    have ht := ih (by omega)
    have hj : left w N (⟨k,by omega⟩ : Fin w) ≠ right w N ⟨k,by omega⟩ := by
      intro he
      have hv := congrArg Fin.val he
      dsimp [left,right] at hv
      omega
    have hs := physical_swap (left w N ⟨k,by omega⟩) (right w N ⟨k,by omega⟩) hj
    constructor
    · exact (reflectionLegal_append _ _).mpr ⟨ht.1,hs.1⟩
    · simp only [swapPrefix,List.length_append,ht.2,hs.2.1]
      omega

/-- The word swapping every pair of corresponding wires in the two width-`w` blocks. -/
noncomputable def word (w N : ℕ) : List (ReflectionGate (w+N+w)) := swapPrefix w N w (Nat.le_refl w)

/-- The full swap word exchanges the two blocks and leaves the scratch block clean. -/
theorem word_basis (w N : ℕ) (x y : Reg w) :
    Run 1 (reflectionCompile (word w N)) (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w N w x y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w N w y x) := by
  have hs := prefix_basis w N w (Nat.le_refl w) x y
  have he : state w N w x y = booleanDAGInput w N w y x := by
    have hx : (fun j : Fin w => if j.val < w then y j else x j) = y := by
      funext j
      simp [j.isLt]
    have hy : (fun j : Fin w => if j.val < w then x j else y j) = x := by
      funext j
      simp [j.isLt]
    exact congrArg₂ (booleanDAGInput w N w) hx hy
  exact hs.trans (congrArg Qatlib.Foundations.PureStateMath.Ket he)

end Qatlib.Concepts.HspRecovery.ReductionCore.Swap

namespace Qatlib.Concepts.HspRecovery.ReductionCore.InPlace
open Matrix Layout
open scoped Classical

/-- The width-`w` output function obtained by evaluating selected wires of a Boolean graph. -/
def value {w n : ℕ} (g : BooleanDAG w n) (out : Fin w → Fin (w+n)) (x : Reg w) : Reg w :=
  fun j => booleanDAGValue g x (out j)

/-- The reversible word that computes a graph output, swaps the input and output blocks, and
applies a second graph to clear the old input. -/
noncomputable def word {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) : List (ReflectionGate (w+max nf ng+w)) :=
  liftedDAG f fo (paddedWires w nf w (max nf ng) (Nat.le_max_left _ _)) ++
  Swap.word w (max nf ng) ++
  liftedDAG g go (paddedWires w ng w (max nf ng) (Nat.le_max_right _ _))

/-- If the second graph's value function is a left inverse of the first, the in-place word
replaces the input by the first graph's value and leaves scratch and output blocks clean. -/
theorem basis {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng))
    (hinv : ∀ x, value g go (value f fo x) = x) (x : Reg w) :
    Run 1 (reflectionCompile (word f fo g go))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (max nf ng) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (max nf ng) w (value f fo x) (fun _ => false)) := by
  have hf := padded_dag_basis f fo (Nat.le_max_left nf ng) x (fun _ => false)
  have hg := padded_dag_basis g go (Nat.le_max_right nf ng) (value f fo x) x
  have hfout : booleanDAGOutput f fo x (fun _ => false) = value f fo x := by
    funext j
    simp [booleanDAGOutput,value]
  have hgout : booleanDAGOutput g go (value f fo x) x = (fun _ => false) := by
    funext j
    have hh := congrFun (hinv x) j
    change (x j ^^ value g go (value f fo x) j) = false
    rw [hh]
    simp
  rw [hfout] at hf
  rw [hgout] at hg
  simp only [word,reflectionCompile_append,run_append]
  rw [hf,Swap.word_basis,hg]

/-- The in-place word is legal, uses zero queries, and has length at most `30 * (nf + ng) + 5 *
w`. -/
theorem resources {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :
    reflectionLegal (word f fo g go) ∧
    (word f fo g go).length ≤ 30*(nf+ng)+5*w ∧
    QueryCount (reflectionCompile (word f fo g go)) = 0 ∧
    GateCount (reflectionCompile (word f fo g go)) = (word f fo g go).length := by
  have hf := lifted_dag_resources f fo (paddedWires w nf w (max nf ng) (Nat.le_max_left _ _))
  have hg := lifted_dag_resources g go (paddedWires w ng w (max nf ng) (Nat.le_max_right _ _))
  have hs := Swap.prefix_resources w (max nf ng) w (Nat.le_refl w)
  have hl : reflectionLegal (word f fo g go) := by
    exact (reflectionLegal_append _ _).mpr
      ⟨(reflectionLegal_append _ _).mpr ⟨hf.1,hs.1⟩,hg.1⟩
  refine ⟨hl,?_,queryCount_reflectionCompile _,gateCount_reflectionCompile _⟩
  dsimp only [word]
  rw [List.length_append,List.length_append]
  change _ + (Swap.swapPrefix w (max nf ng) w (Nat.le_refl w)).length + _ ≤ _
  rw [hs.2]
  omega

/-- The adjoint of the in-place word is a matrix left inverse and has the same length. -/
theorem inverse {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) :
    reflectionProgramMatrix (reflectionAdjoint (word f fo g go)) *
      reflectionProgramMatrix (word f fo g go) = 1 ∧
    (reflectionAdjoint (word f fo g go)).length = (word f fo g go).length := by
  have hl := (resources f fo g go).1
  have hu := reflectionProgramMatrix_unitary _ hl
  refine ⟨?_,reflectionAdjoint_length _⟩
  rw [reflectionAdjoint_matrix _ hl]
  exact Matrix.mem_unitaryGroup_iff'.mp hu

end Qatlib.Concepts.HspRecovery.ReductionCore.InPlace

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open Matrix ModularReversibleWord Bits
open scoped Classical

/-- A Boolean arithmetic graph on two operand words and a modulus, with its node count and
width-`2 * k` output routing. -/
structure Raw (w k : ℕ) where
  nodes : ℕ
  graph : BooleanDAG (2*w+k) nodes
  output : Fin (2*k) → Fin ((2*w+k)+nodes)

/-- The raw modular addition graph and its output selector. -/
def addRaw (w : ℕ) : Raw w (w+1) := ⟨addNodes w,modAddGraph w,modAddSelect w⟩
/-- The raw modular multiplication graph and its output selector. -/
def mulRaw (w : ℕ) : Raw w (2*w) := ⟨mulNodes w,modMulGraph w,modMulSelect w⟩

/-- The word obtained by retaining available bits of `m` up to width `k` and filling additional
positions with false. -/
def extend (w k : ℕ) (m : Reg w) : Reg k := fun j =>
  if hj : j.val < w then m ⟨j.val,hj⟩ else false

/-- The empty width-`w` input graph extended by false and true constant nodes. -/
def constants (w : ℕ) : BooleanDAG w 2 := withConstants .nil

/-- The wire selecting an original input bit in a graph with additional nodes. -/
def inputWire {w K : ℕ} (j : Fin w) : Fin (w+K) := Fin.castLE (by omega) j

/-- The routing fixing the first operand and modulus to constant words while leaving the second
operand as the variable input. -/
def rawSource (w k : ℕ) (a m : Reg w) : Fin (2*w+k) → Fin (w+2) := fun j =>
  if hj : j.val < w then constantWire (a ⟨j.val,hj⟩)
  else if hs : j.val < 2*w then inputWire ⟨j.val-w,by omega⟩
  else if hm : j.val-2*w < w then constantWire (m ⟨j.val-2*w,hm⟩)
  else constantWire false

/-- Evaluating the fixed-operand routing produces the combined input `a`, `x`, and the extended
modulus word. -/
theorem raw_input (w k : ℕ) (a m x : Reg w) :
    (fun j => booleanDAGValue (constants w) x (rawSource w k a m j)) =
      input w k a x (extend w k m) := by
  funext j
  by_cases ha : j.val < w
  · have hs : j.val < 2*w := by omega
    simp only [rawSource,dif_pos ha,constants,constant_wire_value,input,dif_pos hs,
      booleanWordAdderInput]
  · by_cases hs : j.val < 2*w
    · simp only [rawSource,dif_neg ha,dif_pos hs,inputWire,input_wire,input,
        booleanWordAdderInput]
    · by_cases hm : j.val-2*w < w
      · simp only [rawSource,dif_neg ha,dif_neg hs,dif_pos hm,constants,constant_wire_value,
          input,extend]
      · simp only [rawSource,dif_neg ha,dif_neg hs,dif_neg hm,constants,constant_wire_value,
          input,extend]

/-- The raw graph with constant first operand and modulus, and a variable second operand. -/
def curriedGraph {w k : ℕ} (p : Raw w k) (a m : Reg w) : BooleanDAG w (2+p.nodes) :=
  booleanDAGSplice (constants w) (rawSource w k a m) p.graph

/-- The raw output selector transported through the fixed-operand graph splice. -/
def curriedSelect {w k : ℕ} (p : Raw w k) (a m : Reg w) :
    Fin (2*k) → Fin (w+(2+p.nodes)) :=
  fun j => booleanSpliceSource (rawSource w k a m) (p.output j)

/-- Evaluating the curried output agrees with evaluating the raw graph on its fixed operands and
variable input. -/
theorem curried_output {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    (fun j => booleanDAGValue (curriedGraph p a m) x (curriedSelect p a m j)) =
      (fun j => booleanDAGValue p.graph (input w k a x (extend w k m)) (p.output j)) := by
  funext j
  have h := boolean_dag_splice_value (constants w) (rawSource w k a m) p.graph x (p.output j)
  rw [raw_input] at h
  exact h

/-- The constant wires retain their Boolean values after the raw graph is spliced. -/
theorem curried_constant {w k : ℕ} (p : Raw w k) (a m x : Reg w) (b : Bool) :
    booleanDAGValue (curriedGraph p a m) x
      (Fin.castLE (by omega) (constantWire (M:=w) (K:=0) b)) = b := by
  exact (boolean_dag_splice_prefix (constants w) (rawSource w k a m) p.graph x (constantWire b)).trans
    (constant_wire_value (.nil : BooleanDAG w 0) x b)

end Qatlib.Concepts.HspRecovery.ReductionCore.Guarded

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open Matrix ModularReversibleWord Bits
open scoped Classical

/-- The comparison graph node count `7 * w + 1 + 3 * w + 1`. -/
def cmpNodes (w : ℕ) : ℕ := 7*w+1+3*w+1

/-- The routing sending the variable input and constant modulus to the conditional-subtraction
comparison graph. -/
def cmpSource {w k : ℕ} (p : Raw w k) (m : Reg w) : Fin (2*w) → Fin (w+(2+p.nodes)) := fun j =>
  if hj : j.val < w then inputWire ⟨j.val,hj⟩
  else Fin.castLE (by omega) (constantWire (M:=w) (K:=0) (m ⟨j.val-w,by omega⟩))

/-- The curried arithmetic graph followed by a comparison of the input with the modulus. -/
def cmpGraph {w k : ℕ} (p : Raw w k) (a m : Reg w) : BooleanDAG w ((2+p.nodes)+cmpNodes w) :=
  booleanDAGSplice (curriedGraph p a m) (cmpSource p m) (booleanWordCondSubDAG w)
/-- The output wire for the comparison graph's final conditional-subtraction flag. -/
def cmpFlag {w k : ℕ} (p : Raw w k) (m : Reg w) : Fin (w+((2+p.nodes)+cmpNodes w)) :=
  booleanSpliceSource (cmpSource p m) (booleanWordCondSubSelect w (Fin.last w))

/-- The comparison graph extended by the negation of its final flag. -/
def validGraph {w k : ℕ} (p : Raw w k) (a m : Reg w) : BooleanDAG w (((2+p.nodes)+cmpNodes w)+1) :=
  (cmpGraph p a m).snoc (.neg (cmpFlag p m))
/-- The last wire containing the negated comparison flag. -/
def validWire {w k : ℕ} (p : Raw w k) : Fin (w+(((2+p.nodes)+cmpNodes w)+1)) :=
  ⟨w+((2+p.nodes)+cmpNodes w),by omega⟩

/-- The comparison routing evaluates to the concatenation of the input and modulus words. -/
theorem cmp_input {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    (fun j => booleanDAGValue (curriedGraph p a m) x (cmpSource p m j)) =
      booleanWordAdderInput w x m := by
  funext j
  by_cases hj : j.val < w
  · simp only [cmpSource,dif_pos hj,inputWire,input_wire,booleanWordAdderInput]
  · simp only [cmpSource,dif_neg hj,curried_constant,booleanWordAdderInput]

/-- The comparison flag agrees with the final flag of conditional subtraction on the input and
modulus. -/
theorem cmp_flag_value {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    booleanDAGValue (cmpGraph p a m) x (cmpFlag p m) =
      booleanWordCondSubResult w x m (Fin.last w) := by
  have h := boolean_dag_splice_value (curriedGraph p a m) (cmpSource p m)
    (booleanWordCondSubDAG w) x (booleanWordCondSubSelect w (Fin.last w))
  rw [cmp_input] at h
  exact h

/-- The validity wire is true exactly when the input word value is less than the modulus word
value. -/
theorem valid_value {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    booleanDAGValue (validGraph p a m) x (validWire p) =
      decide (booleanWordLSBValue w x < booleanWordLSBValue w m) := by
  have he : validWire p = Fin.last (w+((2+p.nodes)+cmpNodes w)) := Fin.ext rfl
  have hv : booleanDAGValue (validGraph p a m) x (validWire p) =
      (!(booleanDAGValue (cmpGraph p a m) x (cmpFlag p m))) := by
    rw [he]
    exact Fin.lastCases_last (n:=w+((2+p.nodes)+cmpNodes w)) (motive:=fun _ => Bool)
      (last:= !(booleanDAGValue (cmpGraph p a m) x (cmpFlag p m)))
      (cast:= booleanDAGValue (cmpGraph p a m) x)
  exact hv.trans ((congrArg Bool.not (cmp_flag_value p a m x)).trans (cond_sub_less_flag w x m))

/-- Adding comparison and validity nodes preserves every wire of the curried arithmetic graph. -/
theorem valid_old {w k : ℕ} (p : Raw w k) (a m x : Reg w) (i : Fin (w+(2+p.nodes))) :
    booleanDAGValue (validGraph p a m) x (Fin.castLE (by omega) i) =
      booleanDAGValue (curriedGraph p a m) x i := by
  simp only [validGraph,booleanDAGValue]
  have he : (Fin.castLE (by omega) i : Fin (w+(((2+p.nodes)+cmpNodes w)+1))) =
      Fin.castSucc (Fin.castLE (by omega) i : Fin (w+((2+p.nodes)+cmpNodes w))) := Fin.ext rfl
  rw [he,Fin.lastCases_castSucc]
  exact boolean_dag_splice_prefix (curriedGraph p a m) (cmpSource p m) (booleanWordCondSubDAG w) x i

/-- The low `w` result wires of the curried arithmetic graph, routed into the validity graph. -/
def lowSource {w k : ℕ} (p : Raw w k) (a m : Reg w) (hk : w ≤ 2*k) :
    Fin w → Fin (w+(((2+p.nodes)+cmpNodes w)+1)) := fun j =>
  Fin.castLE (by omega) (curriedSelect p a m (Fin.castLE hk j))

/-- The node count of the guarded arithmetic graph, including constants, comparison, validity,
and mux nodes. -/
def nodes {w k : ℕ} (p : Raw w k) : ℕ := (((2+p.nodes)+cmpNodes w)+1)+3*w

/-- The graph selecting the low result bits for inputs below the modulus and the original input
otherwise. -/
def graph {w k : ℕ} (p : Raw w k) (a m : Reg w) (hk : w ≤ 2*k) : BooleanDAG w (nodes p) :=
  booleanDAGSplice (validGraph p a m)
    (booleanMuxSources w (lowSource p a m hk) inputWire (validWire p)) (booleanWordMuxDAG w)

/-- The selector for the width-`w` output of the guarded arithmetic graph. -/
def output {w k : ℕ} (p : Raw w k) (a m : Reg w) (hk : w ≤ 2*k) : Fin w → Fin (w+nodes p) :=
  fun j => booleanSpliceSource
    (booleanMuxSources w (lowSource p a m hk) inputWire (validWire p)) (booleanWordMuxSelect w j)

/-- The guarded graph returns the low arithmetic result bits when the input is below the
modulus, and returns the input otherwise. -/
theorem result {w k : ℕ} (p : Raw w k) (a m x : Reg w) (hk : w ≤ 2*k) :
    InPlace.value (graph p a m hk) (output p a m hk) x =
      if booleanWordLSBValue w x < booleanWordLSBValue w m then
        (fun j => booleanDAGValue (curriedGraph p a m) x (curriedSelect p a m (Fin.castLE hk j)))
      else x := by
  have h := shared_mux (validGraph p a m) (lowSource p a m hk) inputWire (validWire p) x
  have hl : (fun j => booleanDAGValue (validGraph p a m) x (lowSource p a m hk j)) =
      (fun j => booleanDAGValue (curriedGraph p a m) x (curriedSelect p a m (Fin.castLE hk j))) := by
    funext j
    exact valid_old p a m x _
  have hi : (fun j => booleanDAGValue (validGraph p a m) x (inputWire j)) = x := by
    funext j
    exact input_wire _ _ _
  rw [valid_value,hl,hi] at h
  simpa only [Bool.decide_iff] using! h

end Qatlib.Concepts.HspRecovery.ReductionCore.Guarded

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open Qatlib
open scoped Classical BigOperators

/-- Extending a bit string to a width at least its original width preserves its
least-significant-bit value. -/
theorem extend_value (w k : ℕ) (hw : w ≤ k) (a : Reg w) :
    booleanWordLSBValue k (extend w k a) = booleanWordLSBValue w a := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hw
  rw [boolean_word_lsb_value,Fin.sum_univ_add,boolean_word_lsb_value]
  have hhead (j : Fin w) : extend w (w+r) a (Fin.castAdd r j) = a j := by
    simp [extend,j.isLt]
  have htail (j : Fin r) : extend w (w+r) a (Fin.natAdd w j) = false := by
    have hn : ¬w+j.val < w := by omega
    simp [extend,hn]
  simp only [hhead,htail,Fin.val_castAdd,Bool.false_eq_true,ite_false,
    zero_mul,Finset.sum_const_zero,add_zero]

end Qatlib.Concepts.HspRecovery.ReductionCore.Guarded

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Arithmetic
/-- The natural representative of the extended-gcd coefficient of `a`, reduced modulo `m`. -/
def inverseCoefficient (a m : ℕ) : ℕ := (Nat.gcdA a m % (m : ℤ)).toNat

/-- For positive `m` coprime to `a`, the inverse coefficient is below `m` and its product with
`a` is congruent to one modulo `m`. -/
theorem inverse_coefficient_spec (a m : ℕ) (hm : 0 < m) (hc : a.Coprime m) :
    inverseCoefficient a m < m ∧ a * inverseCoefficient a m % m = 1 % m := by
  have hm' : (m : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hm.ne'
  have key := congrArg (fun z : ℤ => (z % (m : ℤ)).toNat) (Nat.gcd_eq_gcd_ab a m)
  (try dsimp only at key)
  rw [Int.add_mul_emod_self_left,← Int.natCast_mod,Int.toNat_natCast,hc.gcd_eq_one] at key
  refine ⟨?_, (Int.ofNat_inj.mp ?_).trans key.symm⟩
  · dsimp [inverseCoefficient]
    rw [Int.toNat_lt (Int.emod_nonneg _ hm')]
    exact Int.emod_lt _ hm'
  · dsimp [inverseCoefficient]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'),
      Int.toNat_of_nonneg (Int.emod_nonneg _ hm'),Int.mul_emod,Int.emod_emod,← Int.mul_emod]

end Qatlib.Concepts.HspRecovery.ReductionCore.Arithmetic

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Arithmetic

/-- The natural modular additive inverse `(m - a % m) % m`. -/
def addInverse (m a : ℕ) : ℕ := (m-a%m)%m

/-- For positive modulus, the modular additive inverse is less than the modulus. -/
theorem add_inverse_lt (m a : ℕ) (hm : 0 < m) : addInverse m a < m := Nat.mod_lt _ hm

/-- Total modular addition by the modular additive inverse equals total modular subtraction. -/
theorem inverse_add_as_sub (m a x : ℕ) : totalAdd m (addInverse m a) x = totalSub m a x := by
  by_cases hm : 0 < m
  · by_cases hx : x < m
    · simp only [totalAdd,totalSub,hm,hx,and_self,ite_true,addInverse]
      have hr : a%m ≤ m := (Nat.mod_lt _ hm).le
      calc
        _ = (x+(m-a%m))%m := by rw [Nat.add_mod,Nat.mod_mod,← Nat.add_mod]
        _ = (x+m-a%m)%m := by rw [Nat.add_sub_assoc hr]
    · simp [totalAdd,totalSub,hm,hx]
  · simp [totalAdd,totalSub,hm]

/-- Multiplication by `a` modulo positive `m` on inputs below `m`, extended by the identity
elsewhere. -/
def totalMul (m a x : ℕ) : ℕ := if 0 < m ∧ x < m then (a*x)%m else x

/-- If `a * b % m = 1 % m`, total modular multiplication by `b` reverses total modular
multiplication by `a`. -/
theorem mul_inverse (m a b x : ℕ) (hab : a*b%m=1%m) :
    totalMul m b (totalMul m a x) = x := by
  by_cases hm : 0 < m
  · by_cases hx : x < m
    · simp only [totalMul,hm,hx,and_self,ite_true]
      have hz : (a*x)%m < m := Nat.mod_lt _ hm
      simp only [hz,and_self,ite_true]
      have hc : Nat.ModEq m (b*a) 1 := by
        change (b*a)%m=1%m
        rw [Nat.mul_comm]
        exact hab
      calc
        _ = (b*(a*x))%m := by rw [Nat.mul_mod,Nat.mod_mod,← Nat.mul_mod]
        _ = ((b*a)*x)%m := by rw [Nat.mul_assoc]
        _ = (1*x)%m := hc.mul_right x
        _ = x := by rw [one_mul,Nat.mod_eq_of_lt hx]
    · simp [totalMul,hm,hx]
  · simp [totalMul,hm]

/-- When `m ≤ N`, total modular multiplication sends inputs below `N` to outputs below `N`. -/
theorem totalMul_lt (m a x N : ℕ) (hm : m ≤ N) (hx : x < N) : totalMul m a x < N := by
  unfold totalMul
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans_le hm
  · exact hx

end Qatlib.Concepts.HspRecovery.ReductionCore.Arithmetic

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Bits
open Qatlib
open scoped Classical

/-- The width-`w` least-significant-bit encoding of `n % 2^w`. -/
def ofNat (w n : ℕ) : Reg w := fun i =>
  (bitVecEquiv w).symm ⟨n%2^w,Nat.mod_lt _ (by positivity)⟩ (Fin.rev i)

/-- The least-significant-bit value of `ofNat w n` is `n % 2^w`. -/
theorem ofNat_value (w n : ℕ) : booleanWordLSBValue w (ofNat w n) = n%2^w := by
  have he : (fun j => ofNat w n (Fin.rev j)) =
      (bitVecEquiv w).symm ⟨n%2^w,Nat.mod_lt _ (by positivity)⟩ := by
    funext j
    simp [ofNat]
  unfold booleanWordLSBValue
  rw [he,Equiv.apply_symm_apply]

/-- The least-significant-bit value of a width-`w` word is less than `2^w`. -/
theorem lsb_lt (w : ℕ) (a : Reg w) : booleanWordLSBValue w a < 2^w :=
  (bitVecEquiv w (fun j => a (Fin.rev j))).isLt
end Qatlib.Concepts.HspRecovery.ReductionCore.Bits

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open ModularReversibleWord Bits Arithmetic
open scoped Classical

/-- The value of the guarded graph is the low-`w` reduction of the raw arithmetic result below
the modulus, and the unchanged input value otherwise. -/
theorem value_formula {w k : ℕ} (p : Raw w k) (a m x : Reg w) (hk : w ≤ 2*k) :
    booleanWordLSBValue w (InPlace.value (graph p a m hk) (output p a m hk) x) =
      if booleanWordLSBValue w x < booleanWordLSBValue w m then
        booleanWordLSBValue (2*k)
          (fun j => booleanDAGValue p.graph (input w k a x (extend w k m)) (p.output j)) % 2^w
      else booleanWordLSBValue w x := by
  rw [result p a m x hk]
  split_ifs with h
  · have ht := low_bits_value (2*k) w hk
      (fun j => booleanDAGValue (curriedGraph p a m) x (curriedSelect p a m j))
    rw [curried_output] at ht
    exact ht
  · rfl

/-- The guarded addition graph represents total modular addition of the fixed operand to the
input. -/
theorem add_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w
      (InPlace.value (graph (addRaw w) a m (by omega)) (output (addRaw w) a m (by omega)) x) =
      totalAdd (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) := by
  have hf := value_formula (addRaw w) a m x (by omega)
  have hr : booleanWordLSBValue (2*(w+1))
      (fun j => booleanDAGValue (addRaw w).graph (input w (w+1) a x (extend w (w+1) m))
        ((addRaw w).output j)) =
      (booleanWordLSBValue w a+booleanWordLSBValue w x)%booleanWordLSBValue w m := by
    have h := mod_add_value w a x (extend w (w+1) m)
    rw [extend_value w (w+1) (by omega)] at h
    exact h
  rw [hr] at hf
  by_cases hx : booleanWordLSBValue w x < booleanWordLSBValue w m
  · have hm : 0 < booleanWordLSBValue w m := by omega
    have hb := (Nat.mod_lt (booleanWordLSBValue w a+booleanWordLSBValue w x) hm).trans (lsb_lt w m)
    rw [if_pos hx,Nat.mod_eq_of_lt hb] at hf
    simpa only [totalAdd,hm,hx,and_self,ite_true,Nat.add_comm] using! hf
  · simpa only [if_neg hx,totalAdd,hx,and_false,ite_false] using! hf

/-- The guarded multiplication graph represents total modular multiplication of the input by the
fixed operand. -/
theorem mul_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w
      (InPlace.value (graph (mulRaw w) a m (by omega)) (output (mulRaw w) a m (by omega)) x) =
      totalMul (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) := by
  have hf := value_formula (mulRaw w) a m x (by omega)
  have hr : booleanWordLSBValue (2*(2*w))
      (fun j => booleanDAGValue (mulRaw w).graph (input w (2*w) a x (extend w (2*w) m))
        ((mulRaw w).output j)) =
      (booleanWordLSBValue w a*booleanWordLSBValue w x)%booleanWordLSBValue w m := by
    have h := mod_mul_value w a x (extend w (2*w) m)
    rw [extend_value w (2*w) (by omega)] at h
    exact h
  rw [hr] at hf
  by_cases hx : booleanWordLSBValue w x < booleanWordLSBValue w m
  · have hm : 0 < booleanWordLSBValue w m := by omega
    have hb := (Nat.mod_lt (booleanWordLSBValue w a*booleanWordLSBValue w x) hm).trans (lsb_lt w m)
    rw [if_pos hx,Nat.mod_eq_of_lt hb] at hf
    simpa only [totalMul,hm,hx,and_self,ite_true] using! hf
  · simpa only [if_neg hx,totalMul,hx,and_false,ite_false] using! hf

/-- The guarded graph node count equals `p.nodes + 13 * w + 5`. -/
theorem nodes_eq {w k : ℕ} (p : Raw w k) : nodes p = p.nodes+13*w+5 := by
  dsimp only [nodes,cmpNodes]
  omega
end Qatlib.Concepts.HspRecovery.ReductionCore.Guarded

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Native
open Matrix Bits Arithmetic
open scoped Classical

/-- The width-`w` encoding of the fixed operand's modular additive inverse. -/
def addInvBits (w : ℕ) (a m : Reg w) : Reg w :=
  ofNat w (addInverse (booleanWordLSBValue w m) (booleanWordLSBValue w a))
/-- The width-`w` encoding of the fixed operand's reduced extended-gcd inverse coefficient. -/
def mulInvBits (w : ℕ) (a m : Reg w) : Reg w :=
  ofNat w (inverseCoefficient (booleanWordLSBValue w a) (booleanWordLSBValue w m))

/-- The guarded width-`w` modular addition function with fixed operand and modulus. -/
def addFunction (w : ℕ) (a m x : Reg w) : Reg w :=
  InPlace.value (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega)) x

/-- The guarded width-`w` modular multiplication function with fixed operand and modulus. -/
def mulFunction (w : ℕ) (a m x : Reg w) : Reg w :=
  InPlace.value (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega)) x

/-- The additive inverse bit string represents the natural modular additive inverse exactly. -/
theorem add_inv_bits_value (w : ℕ) (a m : Reg w) :
    booleanWordLSBValue w (addInvBits w a m) =
      addInverse (booleanWordLSBValue w m) (booleanWordLSBValue w a) := by
  rw [addInvBits,ofNat_value]
  apply Nat.mod_eq_of_lt
  by_cases hm : 0 < booleanWordLSBValue w m
  · exact (add_inverse_lt _ _ hm).trans (lsb_lt w m)
  · have he : booleanWordLSBValue w m = 0 := by omega
    simp [he,addInverse]

/-- The bit-string addition function represents total modular addition on natural word values. -/
theorem add_function_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w (addFunction w a m x) =
      totalAdd (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) :=
  Guarded.add_value w a m x

/-- The bit-string multiplication function represents total modular multiplication on natural
word values. -/
theorem mul_function_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w (mulFunction w a m x) =
      totalMul (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) :=
  Guarded.mul_value w a m x

/-- Addition by the encoded additive inverse reverses the bit-string modular addition function. -/
theorem add_function_inverse (w : ℕ) (a m x : Reg w) :
    addFunction w (addInvBits w a m) m (addFunction w a m x) = x := by
  apply lsb_injective w
  have h := add_function_value w (addInvBits w a m) m (addFunction w a m x)
  rw [add_function_value w a m x,add_inv_bits_value,inverse_add_as_sub,sub_add] at h
  exact h

/-- When the operand and modulus values are coprime, multiplication by the encoded inverse
coefficient reverses the bit-string modular multiplication function. -/
theorem mul_function_inverse (w : ℕ) (a m x : Reg w)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    mulFunction w (mulInvBits w a m) m (mulFunction w a m x) = x := by
  apply lsb_injective w
  have h := mul_function_value w (mulInvBits w a m) m (mulFunction w a m x)
  rw [mul_function_value w a m x] at h
  by_cases hm : 0 < booleanWordLSBValue w m
  · have hs := inverse_coefficient_spec _ _ hm hc
    have hi : booleanWordLSBValue w (mulInvBits w a m) =
        inverseCoefficient (booleanWordLSBValue w a) (booleanWordLSBValue w m) := by
      rw [mulInvBits,ofNat_value,Nat.mod_eq_of_lt (hs.1.trans (lsb_lt w m))]
    rw [hi] at h
    exact h.trans (mul_inverse _ _ _ _ hs.2)
  · simpa only [totalMul,hm,false_and,ite_false] using! h

/-- The shared scratch width for the forward and inverse guarded addition graphs. -/
def addWork (w : ℕ) : ℕ := max (Guarded.nodes (Guarded.addRaw w)) (Guarded.nodes (Guarded.addRaw w))
/-- The shared scratch width for the forward and inverse guarded multiplication graphs. -/
def mulWork (w : ℕ) : ℕ := max (Guarded.nodes (Guarded.mulRaw w)) (Guarded.nodes (Guarded.mulRaw w))

/-- The in-place reversible word for modular addition, using the additive inverse graph to clear
the old input. -/
noncomputable def addWord (w : ℕ) (a m : Reg w) : List (ReflectionGate (w+addWork w+w)) :=
  InPlace.word (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (addInvBits w a m) m (by omega))

/-- The in-place reversible word for modular multiplication, using the inverse-coefficient graph
to clear the old input. -/
noncomputable def mulWord (w : ℕ) (a m : Reg w) : List (ReflectionGate (w+mulWork w+w)) :=
  InPlace.word (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))

/-- The native addition word applies `addFunction` to a basis input and leaves its scratch and
output blocks clean. -/
theorem add_basis (w : ℕ) (a m x : Reg w) :
    Run 1 (reflectionCompile (addWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w (addFunction w a m x) (fun _ => false)) :=
  InPlace.basis _ _ _ _ (add_function_inverse w a m) x

/-- For coprime operand and modulus values, the native multiplication word applies `mulFunction`
to a basis input and leaves its scratch and output blocks clean. -/
theorem mul_basis (w : ℕ) (a m x : Reg w)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    Run 1 (reflectionCompile (mulWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w (mulFunction w a m x) (fun _ => false)) :=
  InPlace.basis _ _ _ _ (fun x => mul_function_inverse w a m x hc) x

end Qatlib.Concepts.HspRecovery.ReductionCore.Native

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Native
open Matrix ModularReversibleWord Bits Arithmetic
open scoped Classical

/-- The guarded addition graph has at most `20 * w^2 + 64 * w + 33` nodes. -/
theorem add_node_bound (w : ℕ) : Guarded.nodes (Guarded.addRaw w) ≤ 20*w^2+64*w+33 := by
  rw [Guarded.nodes_eq]
  change addNodes w+13*w+5 ≤ _
  have h := (mod_add_resources w).1
  omega

/-- The guarded multiplication graph has at most `91 * w^2 + 26 * w + 7` nodes. -/
theorem mul_node_bound (w : ℕ) : Guarded.nodes (Guarded.mulRaw w) ≤ 91*w^2+26*w+7 := by
  rw [Guarded.nodes_eq]
  change mulNodes w+13*w+5 ≤ _
  have h := (mod_mul_resources w).1
  omega

/-- The native addition word is legal, uses zero queries, and satisfies the stated quadratic
gate and workspace bounds, including length at most `1200 * w^2 + 3845 * w + 1980`. -/
theorem add_resources (w : ℕ) (a m : Reg w) :
    reflectionLegal (addWord w a m) ∧
    (addWord w a m).length ≤ 1200*w^2+3845*w+1980 ∧
    QueryCount (reflectionCompile (addWord w a m)) = 0 ∧
    GateCount (reflectionCompile (addWord w a m)) = (addWord w a m).length ∧
    addWork w+w ≤ 20*w^2+65*w+33 ∧
    w+addWork w+w ≤ 20*w^2+66*w+33 := by
  have h := InPlace.resources (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (addInvBits w a m) m (by omega))
  have hn := add_node_bound w
  have hg := h.2.1
  change (addWord w a m).length ≤
    30*(Guarded.nodes (Guarded.addRaw w)+Guarded.nodes (Guarded.addRaw w))+5*w at hg
  refine ⟨h.1,by nlinarith,h.2.2.1,h.2.2.2,?_,?_⟩ <;>
    simp only [addWork,Nat.max_self] <;> omega

/-- The native multiplication word is legal, uses zero queries, and satisfies the stated
quadratic gate and workspace bounds, including length at most `5460 * w^2 + 1565 * w + 420`. -/
theorem mul_resources (w : ℕ) (a m : Reg w) :
    reflectionLegal (mulWord w a m) ∧
    (mulWord w a m).length ≤ 5460*w^2+1565*w+420 ∧
    QueryCount (reflectionCompile (mulWord w a m)) = 0 ∧
    GateCount (reflectionCompile (mulWord w a m)) = (mulWord w a m).length ∧
    mulWork w+w ≤ 91*w^2+27*w+7 ∧
    w+mulWork w+w ≤ 91*w^2+28*w+7 := by
  have h := InPlace.resources (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
  have hn := mul_node_bound w
  have hg := h.2.1
  change (mulWord w a m).length ≤
    30*(Guarded.nodes (Guarded.mulRaw w)+Guarded.nodes (Guarded.mulRaw w))+5*w at hg
  refine ⟨h.1,by nlinarith,h.2.2.1,h.2.2.2,?_,?_⟩ <;>
    simp only [mulWork,Nat.max_self] <;> omega

/-- The adjoint of the native addition word is a matrix left inverse and has the same length. -/
theorem add_inverse (w : ℕ) (a m : Reg w) :
    reflectionProgramMatrix (reflectionAdjoint (addWord w a m)) *
      reflectionProgramMatrix (addWord w a m) = 1 ∧
    (reflectionAdjoint (addWord w a m)).length = (addWord w a m).length :=
  InPlace.inverse (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (addInvBits w a m) m (by omega))

/-- The adjoint of the native multiplication word is a matrix left inverse and has the same
length. -/
theorem mul_inverse_word (w : ℕ) (a m : Reg w) :
    reflectionProgramMatrix (reflectionAdjoint (mulWord w a m)) *
      reflectionProgramMatrix (mulWord w a m) = 1 ∧
    (reflectionAdjoint (mulWord w a m)).length = (mulWord w a m).length :=
  InPlace.inverse (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))

/-- The bit-string subtraction function defined by addition of the encoded modular additive
inverse. -/
def subFunction (w : ℕ) (a m x : Reg w) : Reg w := addFunction w (addInvBits w a m) m x
/-- The native subtraction word defined as the adjoint of the native addition word. -/
noncomputable def subWord (w : ℕ) (a m : Reg w) : List (ReflectionGate (w+addWork w+w)) :=
  reflectionAdjoint (addWord w a m)

/-- The bit-string subtraction function represents total modular subtraction on natural word
values. -/
theorem sub_function_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w (subFunction w a m x) =
      totalSub (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) := by
  have h := add_function_value w (addInvBits w a m) m x
  rw [add_inv_bits_value,inverse_add_as_sub] at h
  exact h

/-- The bit-string modular addition function reverses the subtraction function. -/
theorem add_function_right_inverse (w : ℕ) (a m x : Reg w) :
    addFunction w a m (subFunction w a m x) = x := by
  apply lsb_injective w
  have h := add_function_value w a m (subFunction w a m x)
  rw [sub_function_value,add_sub] at h
  exact h

/-- The native subtraction word applies `subFunction` to a basis input and leaves its scratch
and output blocks clean. -/
theorem sub_basis (w : ℕ) (a m x : Reg w) :
    Run 1 (reflectionCompile (subWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w (subFunction w a m x) (fun _ => false)) := by
  have hf := add_basis w a m (subFunction w a m x)
  rw [add_function_right_inverse] at hf
  rw [subWord,run_reflectionCompile,← hf,run_reflectionCompile,← applyGate_mul,
    (add_inverse w a m).1,applyGate_one]

end Qatlib.Concepts.HspRecovery.ReductionCore.Native

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Native
open Matrix Bits Arithmetic
open scoped Classical

/-- For zero modulus value, the guarded multiplication function is the identity. -/
theorem mul_function_zero (w : ℕ) (a m x : Reg w) (hm : booleanWordLSBValue w m = 0) :
    mulFunction w a m x = x := by
  apply lsb_injective w
  have h := mul_function_value w a m x
  simpa only [hm,totalMul,lt_self_iff_false,false_and,ite_false] using! h

/-- For zero modulus value, the native multiplication word fixes every basis input with clean
scratch and output blocks. -/
theorem mul_basis_zero (w : ℕ) (a m x : Reg w) (hm : booleanWordLSBValue w m = 0) :
    Run 1 (reflectionCompile (mulWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w x (fun _ => false)) := by
  have hi : ∀ x, mulFunction w (mulInvBits w a m) m (mulFunction w a m x) = x := by
    intro y
    rw [mul_function_zero w (mulInvBits w a m) m _ hm,mul_function_zero w a m y hm]
  have h := InPlace.basis (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (mulInvBits w a m) m (by omega)) hi x
  have hh : Run 1 (reflectionCompile (mulWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w (mulFunction w a m x) (fun _ => false)) := h
  rw [mul_function_zero w a m x hm] at hh
  exact hh
end Qatlib.Concepts.HspRecovery.ReductionCore.Native

namespace Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord
open Matrix Bits Arithmetic Native
open scoped Classical
set_option warningAsError false

/-- For coprime operand and modulus values, the native words implement total modular addition,
subtraction, and multiplication with clean ancillary blocks. The result also supplies
quadratic length and workspace bounds and explicit matrix left inverses. -/
theorem frontier1 (w : ℕ) (a m : Reg w)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    (∀ x : Reg w,
      Run 1 (reflectionCompile (addWord w a m))
        (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w x (fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w (addFunction w a m x) (fun _ => false)) ∧
      booleanWordLSBValue w (addFunction w a m x) =
        totalAdd (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) ∧
      Run 1 (reflectionCompile (subWord w a m))
        (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w x (fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w (subFunction w a m x) (fun _ => false)) ∧
      booleanWordLSBValue w (subFunction w a m x) =
        totalSub (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) ∧
      Run 1 (reflectionCompile (mulWord w a m))
        (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w x (fun _ => false))) =
        Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w (mulFunction w a m x) (fun _ => false)) ∧
      booleanWordLSBValue w (mulFunction w a m x) =
        totalMul (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x)) ∧
    (addWord w a m).length ≤ 1200*w^2+3845*w+1980 ∧
    (mulWord w a m).length ≤ 5460*w^2+1565*w+420 ∧
    addWork w+w ≤ 20*w^2+65*w+33 ∧
    mulWork w+w ≤ 91*w^2+27*w+7 ∧
    reflectionProgramMatrix (reflectionAdjoint (addWord w a m)) * reflectionProgramMatrix (addWord w a m) = 1 ∧
    reflectionProgramMatrix (reflectionAdjoint (mulWord w a m)) * reflectionProgramMatrix (mulWord w a m) = 1 := by
  refine ⟨?_,(add_resources w a m).2.1,(mul_resources w a m).2.1,
    (add_resources w a m).2.2.2.2.1,(mul_resources w a m).2.2.2.2.1,
    (add_inverse w a m).1,(mul_inverse_word w a m).1⟩
  intro x
  exact ⟨add_basis w a m x,add_function_value w a m x,sub_basis w a m x,
    sub_function_value w a m x,mul_basis w a m x hc,mul_function_value w a m x⟩
end Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord
