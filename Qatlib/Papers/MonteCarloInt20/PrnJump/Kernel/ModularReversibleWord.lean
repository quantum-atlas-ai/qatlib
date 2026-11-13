/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.LowWord
import Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.Mux
import Qatlib.Concepts.MatrixAccess.RitzPipeline.WireContext
import Mathlib.Data.Nat.ModEq
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSplice
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDivider
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplier

/-!
# Reversible modular arithmetic on Boolean words

This module constructs Boolean DAGs and reflection-gate programs for modular addition and
multiplication. `appendRemainder` attaches division-based reduction, while `Guarded.graph`
leaves inputs outside the represented modulus unchanged.

The `Native` constructions combine forward computation, register swaps, and inverse computation
to update a word with clean workspace. Their basis-state semantics, explicit inverse programs,
and polynomial gate and workspace bounds support the reversible PRN arithmetic used in Monte
Carlo integration. See [KanekoEtAl2020].

## Main statements

* `mod_add_value` and `mod_mul_value`: arithmetic correctness of the reduction DAGs.
* `Native.add_basis` and `Native.mul_basis`: clean in-place updates, with a coprimality
  hypothesis for multiplication.
* `Native.frontier1`: combined arithmetic semantics and resource bounds.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore
open Matrix
open scoped Classical
set_option autoImplicit false

/-- Selects the remainder bits from the Boolean word-division DAG. -/
def remSelect (w : ℕ) : Fin (2*w) → Fin (2*w+((booleanWordDivProgram w).nodes+w)) :=
  fun j => booleanWordDivSelect w ⟨w+j.val,by have := j.isLt; omega⟩

/-- The remainder-only program XORs the computed remainder into the output register while
preserving the operands and restoring its workspace. -/
theorem remainder_only_basis (w : ℕ) (a b : Reg w) (y : Reg (2*w)) :
    let n := (booleanWordDivProgram w).nodes+w
    Run (1 : Matrix (Reg (2*w+n+2*w)) (Reg (2*w+n+2*w)) ℂ)
      (reflectionCompile (booleanDAGSteps (booleanWordDivDAG w) (remSelect w)))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w) n (2*w) (booleanWordAdderInput w a b) y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w) n (2*w) (booleanWordAdderInput w a b)
        (fun j => y j ^^ booleanWordDivRemainder w a b j)) := by
  exact boolean_dag_basis _ _ _ _

/-- The remainder-only program is legal and uses no queries, with explicit quadratic bounds on
nodes, gates, and total wires. -/
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

/-- The selected remainder bits encode the natural-number remainder of the two input words, for
every input pair. -/
theorem remainder_all_inputs (w : ℕ) (a b : Reg w) :
    booleanWordLSBValue (2*w) (fun j =>
      booleanDAGValue (booleanWordDivDAG w) (booleanWordAdderInput w a b)
        (remSelect w j)) = booleanWordLSBValue w a % booleanWordLSBValue w b :=
  (boolean_word_div_value w a b).2

/-- Combines existing output wires and routed outputs of a spliced DAG into one output selector. -/
def jointOut {M K m n u v : ℕ} (r : Fin m → Fin (M+K))
    (old : Fin u → Fin (M+K)) (new : Fin v → Fin (m+n)) :
    Fin (u+v) → Fin (M+(K+n)) := fun j =>
  if hj : j.val < u then Fin.castLE (by omega) (old ⟨j.val,hj⟩)
  else booleanSpliceSource r (new ⟨j.val-u,by have := j.isLt; omega⟩)

/-- Evaluating selected outputs after DAG splicing agrees with evaluating the second DAG on the
routed values of the first. -/
theorem multioutput_new {M K m n v : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAG m n)
    (out : Fin v → Fin (m+n)) (x : Reg M) :
    (fun j => booleanDAGValue (booleanDAGSplice g r h) x (booleanSpliceSource r (out j))) =
      fun j => booleanDAGValue h (fun k => booleanDAGValue g x (r k)) (out j) := by
  funext j
  exact boolean_dag_splice_value g r h x (out j)

/-- Splicing the division DAG onto routed operand words computes their natural-number remainder. -/
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

/-- Routes two word selectors into the dividend and divisor input positions. -/
def divRoute {M K : ℕ} (w : ℕ) (a b : Fin w → Fin (M+K)) :
    Fin (2*w) → Fin (M+K) := fun j =>
  if hj : j.val < w then a ⟨j.val,hj⟩ else b ⟨j.val-w,by omega⟩

/-- Appends a word-division DAG to an existing graph to compute the remainder of two selected
words. -/
def appendRemainder {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) :
    BooleanDAG M (K+((booleanWordDivProgram w).nodes+w)) :=
  booleanDAGSplice g (divRoute w a b) (booleanWordDivDAG w)

/-- Selects the remainder output wires of `appendRemainder`. -/
def appendRemainderSelect {M K : ℕ} (w : ℕ)
    (a b : Fin w → Fin (M+K)) :
    Fin (2*w) → Fin (M+(K+((booleanWordDivProgram w).nodes+w))) :=
  fun j => booleanSpliceSource (divRoute w a b) (remSelect w j)

/-- The remainder appended to a DAG encodes the first selected word modulo the second. -/
theorem append_remainder_value {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) (x : Reg M) :
    booleanWordLSBValue (2*w) (fun j =>
      booleanDAGValue (appendRemainder g w a b) x (appendRemainderSelect w a b j)) =
      booleanWordLSBValue w (fun j => booleanDAGValue g x (a j)) %
        booleanWordLSBValue w (fun j => booleanDAGValue g x (b j)) :=
  spliced_remainder_value g w a b x

/-- The appended remainder program is legal and query-free, with explicit node and gate bounds
in terms of the original graph size. -/
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

/-- Appends constant false and constant true nodes to a Boolean DAG. -/
def withConstants {M K : ℕ} (g : BooleanDAG M K) : BooleanDAG M ((K+1)+1) :=
  (g.snoc (.constant false)).snoc (.constant true)

/-- Selects the appended constant wire corresponding to the Boolean value `b`. -/
def constantWire {M K : ℕ} (b : Bool) : Fin (M+((K+1)+1)) :=
  if b then Fin.last (M+(K+1)) else Fin.castSucc (Fin.last (M+K))

/-- The wire chosen by `constantWire` evaluates to its specified Boolean constant. -/
theorem constant_wire_value {M K : ℕ} (g : BooleanDAG M K) (x : Reg M) (b : Bool) :
    booleanDAGValue (withConstants g) x (constantWire b) = b := by
  cases b <;> simp [withConstants,constantWire,booleanDAGValue,booleanNodeValue]

/-- The adjoint of a compiled Boolean DAG program is a legal left inverse with the same number
of gates. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Concatenates two operand words and a modulus word into the arithmetic input register. -/
def input (w k : ℕ) (a b : Reg w) (m : Reg k) : Reg (2*w+k) := fun i =>
  if hi : i.val<2*w then booleanWordAdderInput w a b ⟨i.val,hi⟩
  else m ⟨i.val-2*w,by have := i.isLt; omega⟩

/-- Selects the two operand words from the arithmetic input register. -/
def operandSource (w k : ℕ) : Fin (2*w) → Fin ((2*w+k)+0) :=
  Fin.castLE (by omega)

/-- The operand wires of the empty DAG recover the two concatenated operand words. -/
theorem operand_input (w k : ℕ) (a b : Reg w) (m : Reg k) :
    (fun j => booleanDAGValue (.nil : BooleanDAG (2*w+k) 0)
      (input w k a b m) (operandSource w k j)) = booleanWordAdderInput w a b := by
  funext j
  simp [booleanDAGValue,input,operandSource,j.isLt]

/-- The number of DAG nodes used for the unreduced addition stage. -/
def addArithNodes (w : ℕ) : ℕ := 0+(5*w+1)
/-- Constructs the word-addition DAG with an additional modulus input register. -/
def addGraph (w : ℕ) : BooleanDAG (2*w+(w+1)) (addArithNodes w) :=
  booleanDAGSplice .nil (operandSource w (w+1)) (booleanWordAdderDAG w)
/-- Selects the full sum bits in `addGraph`. -/
def addSelect (w : ℕ) : Fin (w+1) → Fin ((2*w+(w+1))+addArithNodes w) :=
  fun j => booleanSpliceSource (M:=2*w+(w+1)) (K:=0) (n:=5*w+1) (operandSource w (w+1)) (booleanWordAdderSelect w j)

/-- The selected output of `addGraph` encodes the exact sum of the two operand values. -/
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

/-- The number of DAG nodes used for the unreduced multiplication stage. -/
def mulArithNodes (w : ℕ) : ℕ := 0+(booleanWordMulProgram w).nodes
/-- Constructs the full word-multiplication DAG with an additional modulus input register. -/
def mulGraph (w : ℕ) : BooleanDAG (2*w+2*w) (mulArithNodes w) :=
  booleanDAGSplice .nil (operandSource w (2*w)) (booleanWordMulProgram w).graph
/-- Selects the full product bits in `mulGraph`. -/
def mulSelect (w : ℕ) : Fin (2*w) → Fin ((2*w+2*w)+mulArithNodes w) :=
  fun j => booleanSpliceSource (M:=2*w+2*w) (K:=0) (n:=(booleanWordMulProgram w).nodes) (operandSource w (2*w)) (booleanWordMulSelect w j)

/-- The selected output of `mulGraph` encodes the exact product of the two operand values. -/
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

/-- An input wire of a Boolean DAG retains its original input value. -/
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

/-- Selects the modulus register from the arithmetic inputs, allowing additional DAG nodes. -/
def modulusSource (w k K : ℕ) : Fin k → Fin ((2*w+k)+K) := fun j =>
  ⟨2*w+j.val,by have := j.isLt; omega⟩

/-- The selected modulus wires evaluate to the supplied modulus word. -/
theorem modulus_input {K : ℕ} (w k : ℕ) (g : BooleanDAG (2*w+k) K)
    (a b : Reg w) (m : Reg k) :
    (fun j => booleanDAGValue g (input w k a b m) (modulusSource w k K j)) = m := by
  funext j
  have he : modulusSource w k K j =
      Fin.castLE (by omega) (⟨2*w+j.val,by have := j.isLt; omega⟩ : Fin (2*w+k)) := Fin.ext rfl
  rw [he,input_wire]
  simp [input,show ¬2*w+j.val<2*w by omega]

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- The node count for addition followed by remainder reduction. -/
def addNodes (w : ℕ) : ℕ := addArithNodes w+((booleanWordDivProgram (w+1)).nodes+(w+1))
/-- The node count for multiplication followed by remainder reduction. -/
def mulNodes (w : ℕ) : ℕ := mulArithNodes w+((booleanWordDivProgram (2*w)).nodes+2*w)

/-- Constructs the DAG for addition followed by reduction modulo the input modulus. -/
def modAddGraph (w : ℕ) : BooleanDAG (2*w+(w+1)) (addNodes w) :=
  appendRemainder (addGraph w) (w+1) (addSelect w) (modulusSource w (w+1) (addArithNodes w))
/-- Selects the remainder bits of the modular-addition DAG. -/
def modAddSelect (w : ℕ) : Fin (2*(w+1)) → Fin ((2*w+(w+1))+addNodes w) :=
  appendRemainderSelect (w+1) (addSelect w) (modulusSource w (w+1) (addArithNodes w))
/-- The Boolean output word obtained by evaluating the modular-addition DAG. -/
def modAddResult (w : ℕ) (a b : Reg w) (m : Reg (w+1)) : Reg (2*(w+1)) := fun j =>
  booleanDAGValue (modAddGraph w) (input w (w+1) a b m) (modAddSelect w j)

/-- Constructs the DAG for multiplication followed by reduction modulo the input modulus. -/
def modMulGraph (w : ℕ) : BooleanDAG (2*w+2*w) (mulNodes w) :=
  appendRemainder (mulGraph w) (2*w) (mulSelect w) (modulusSource w (2*w) (mulArithNodes w))
/-- Selects the remainder bits of the modular-multiplication DAG. -/
def modMulSelect (w : ℕ) : Fin (2*(2*w)) → Fin ((2*w+2*w)+mulNodes w) :=
  appendRemainderSelect (2*w) (mulSelect w) (modulusSource w (2*w) (mulArithNodes w))
/-- The Boolean output word obtained by evaluating the modular-multiplication DAG. -/
def modMulResult (w : ℕ) (a b : Reg w) (m : Reg (2*w)) : Reg (2*(2*w)) := fun j =>
  booleanDAGValue (modMulGraph w) (input w (2*w) a b m) (modMulSelect w j)

/-- The modular-addition output encodes the operand sum modulo the supplied modulus value. -/
theorem mod_add_value (w : ℕ) (a b : Reg w) (m : Reg (w+1)) :
    booleanWordLSBValue (2*(w+1)) (modAddResult w a b m) =
      (booleanWordLSBValue w a + booleanWordLSBValue w b) % booleanWordLSBValue (w+1) m := by
  have h := append_remainder_value (addGraph w) (w+1) (addSelect w)
    (modulusSource w (w+1) (addArithNodes w)) (input w (w+1) a b m)
  rw [add_value,modulus_input] at h
  exact h

/-- The modular-multiplication output encodes the operand product modulo the supplied modulus
value. -/
theorem mod_mul_value (w : ℕ) (a b : Reg w) (m : Reg (2*w)) :
    booleanWordLSBValue (2*(2*w)) (modMulResult w a b m) =
      (booleanWordLSBValue w a * booleanWordLSBValue w b) % booleanWordLSBValue (2*w) m := by
  have h := append_remainder_value (mulGraph w) (2*w) (mulSelect w)
    (modulusSource w (2*w) (mulArithNodes w)) (input w (2*w) a b m)
  rw [mul_full_value,modulus_input] at h
  exact h

/-- Compiles the modular-addition DAG into a reversible reflection-gate program. -/
noncomputable def modAddWord (w : ℕ) : List (ReflectionGate ((2*w+(w+1))+addNodes w+2*(w+1))) :=
  booleanDAGSteps (modAddGraph w) (modAddSelect w)
/-- Compiles the modular-multiplication DAG into a reversible reflection-gate program. -/
noncomputable def modMulWord (w : ℕ) : List (ReflectionGate ((2*w+2*w)+mulNodes w+2*(2*w))) :=
  booleanDAGSteps (modMulGraph w) (modMulSelect w)

/-- The modular-addition program XORs its result into the output word and restores the zero
workspace on basis inputs. -/
theorem mod_add_basis (w : ℕ) (a b : Reg w) (m : Reg (w+1)) (y : Reg (2*(w+1))) :
    Run 1 (reflectionCompile (modAddWord w))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+(w+1)) (addNodes w) (2*(w+1)) (input w (w+1) a b m) y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+(w+1)) (addNodes w) (2*(w+1)) (input w (w+1) a b m)
        (fun j => y j ^^ modAddResult w a b m j)) :=
  boolean_dag_basis _ _ _ _

/-- The modular-multiplication program XORs its result into the output word and restores the
zero workspace on basis inputs. -/
theorem mod_mul_basis (w : ℕ) (a b : Reg w) (m : Reg (2*w)) (y : Reg (2*(2*w))) :
    Run 1 (reflectionCompile (modMulWord w))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+2*w) (mulNodes w) (2*(2*w)) (input w (2*w) a b m) y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (2*w+2*w) (mulNodes w) (2*(2*w)) (input w (2*w) a b m)
        (fun j => y j ^^ modMulResult w a b m j)) :=
  boolean_dag_basis _ _ _ _

/-- The modular-addition program is legal and query-free, with explicit quadratic bounds on
nodes, gates, and wires. -/
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

/-- The modular-multiplication program is legal and query-free, with explicit quadratic bounds
on nodes, gates, and wires. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits
open Qatlib
open scoped Classical
set_option autoImplicit false

/-- The least-significant-bit numerical interpretation is injective on words of fixed width. -/
theorem lsb_injective (w : ℕ) : Function.Injective (booleanWordLSBValue w) := by
  intro a b h
  have he : bitVecEquiv w (fun j => a (Fin.rev j)) =
      bitVecEquiv w (fun j => b (Fin.rev j)) := Fin.ext h
  have hr := (bitVecEquiv w).injective he
  funext j
  simpa only [Fin.rev_rev] using! congrFun hr (Fin.rev j)

/-- The value of the lowest `k` bits is the full word value modulo `2^k` when `k ≤ W`. -/
theorem low_bits_value (W k : ℕ) (hk : k ≤ W) (a : Reg W) :
    booleanWordLSBValue k (fun j => a (Fin.castLE hk j)) = booleanWordLSBValue W a % 2^k :=
  boolean_word_low_value W k hk a

/-- Negating the final conditional-subtraction flag tests whether the first word value is
smaller than the second. -/
theorem cond_sub_less_flag (w : ℕ) (a b : Reg w) :
    (!(booleanWordCondSubResult w a b (Fin.last w))) =
      decide (booleanWordLSBValue w a < booleanWordLSBValue w b) := by
  rw [(boolean_word_cond_sub_value w a b).1]
  by_cases h : booleanWordLSBValue w b ≤ booleanWordLSBValue w a
  · have hn : ¬booleanWordLSBValue w a < booleanWordLSBValue w b := by omega
    simp [h,hn]
  · have hl : booleanWordLSBValue w a < booleanWordLSBValue w b := by omega
    simp [h,hl]

/-- Mapping a Boolean-valued function over mux source wires gives the corresponding mux input
register. -/
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

/-- A spliced word mux selects the first routed word when its control is true and the second
otherwise. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Layout
open Matrix
open scoped Classical
set_option autoImplicit false

/-- Embeds a compiled Boolean DAG program into a larger wire register along an injective wire
map. -/
noncomputable def liftedDAG {m n o L : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (e : Fin (m+n+o) ↪ Fin L) : List (ReflectionGate L) :=
  (booleanDAGSteps g out).map (knownWireGateMap e)

/-- The embedded DAG program performs the same output update within the specified wire context. -/
theorem lifted_dag_basis {m n o L : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (e : Fin (m+n+o) ↪ Fin L)
    (s : Reg L) (x : Reg m) (y : Reg o) :
    Run 1 (reflectionCompile (liftedDAG g out e))
      (Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s (booleanDAGInput m n o x y))) =
      Qatlib.Foundations.PureStateMath.Ket (wireContextExtend e s (booleanDAGInput m n o x (booleanDAGOutput g out x y))) := by
  rw [← wire_context_ket, liftedDAG,
    wire_context_program _ _ e s _ (boolean_dag_resources g out).1,
    boolean_dag_basis, wire_context_ket]

/-- Embedding a DAG program preserves legality and length, uses no queries, and gives the bound
`30*n+o` on its gate count. -/
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

/-- Embeds a DAG layout into a larger workspace while preserving its input and output blocks. -/
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

/-- Reading a padded input register along `paddedWires` recovers the original input layout. -/
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

/-- Replacing the embedded small layout updates the output block of the padded layout
accordingly. -/
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

/-- The padded DAG program computes the same output update with the larger zero workspace. -/
theorem padded_dag_basis {m n o N : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (hn : n ≤ N) (x : Reg m) (y : Reg o) :
    Run 1 (reflectionCompile (liftedDAG g out (paddedWires m n o N hn)))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput m N o x y)) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput m N o x (booleanDAGOutput g out x y)) := by
  have h := lifted_dag_basis g out (paddedWires m n o N hn)
    (booleanDAGInput m N o x y) x y
  simpa only [padded_context] using! h

/-- Three legal reflection gates swap two distinct physical wires on every basis state. -/
theorem physical_swap {L : ℕ} (a b : Fin L) (hab : a ≠ b) :
    reflectionLegal (knownSwapSteps a b) ∧ (knownSwapSteps a b).length = 3 ∧
      ∀ x : Reg L, Run 1 (reflectionCompile (knownSwapSteps a b)) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (x ∘ Equiv.swap a b) := by
  obtain ⟨hl,_,hb⟩ := knownSwapSteps_spec a b
  exact ⟨hl,by simp [knownSwapSteps,hab],hb⟩

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Layout

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Arithmetic

/-- Adds `a` modulo `m` on inputs below a positive modulus and leaves all other inputs fixed. -/
def totalAdd (m a x : ℕ) : ℕ := if 0 < m ∧ x < m then (x+a)%m else x
/-- Subtracts `a` modulo `m` on inputs below a positive modulus and leaves all other inputs
fixed. -/
def totalSub (m a x : ℕ) : ℕ := if 0 < m ∧ x < m then (x+m-(a%m))%m else x

/-- Total modular subtraction undoes total modular addition on every natural-number input. -/
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

/-- Total modular addition undoes total modular subtraction on every natural-number input. -/
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

/-- Total modular addition preserves the bound `x < N` when `m ≤ N`. -/
theorem totalAdd_lt (m a x N : ℕ) (hm : m ≤ N) (hx : x < N) : totalAdd m a x  <  N := by
  unfold totalAdd
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans_le hm
  · exact hx

/-- Total modular subtraction preserves the bound `x < N` when `m ≤ N`. -/
theorem totalSub_lt (m a x N : ℕ) (hm : m ≤ N) (hx : x < N) : totalSub m a x  <  N := by
  unfold totalSub
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans_le hm
  · exact hx

/-- The permutation of `Fin N` induced by total modular addition, with total modular subtraction
as its inverse. -/
def addEquiv (m a N : ℕ) (hm : m ≤ N) : Fin N ≃ Fin N where
  toFun x := ⟨totalAdd m a x.val,totalAdd_lt m a x.val N hm x.isLt⟩
  invFun x := ⟨totalSub m a x.val,totalSub_lt m a x.val N hm x.isLt⟩
  left_inv x := Fin.ext (sub_add m a x.val)
  right_inv x := Fin.ext (add_sub m a x.val)
end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Arithmetic

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Swap
open Matrix
open Layout
open scoped Classical

/-- Selects a wire in the left word of the swap layout. -/
def left (w N : ℕ) (j : Fin w) : Fin (w+N+w) := ⟨j.val,by have := j.isLt; omega⟩
/-- Selects the corresponding wire in the right word of the swap layout. -/
def right (w N : ℕ) (j : Fin w) : Fin (w+N+w) := ⟨w+N+j.val,by have := j.isLt; omega⟩
/-- The register state after exchanging the first `k` bits of the two words, with zero
workspace. -/
def state (w N k : ℕ) (x y : Reg w) : Reg (w+N+w) :=
  booleanDAGInput w N w (fun j => if j.val < k then y j else x j)
    (fun j => if j.val < k then x j else y j)

/-- Builds the gate program that swaps the first `k` pairs of word wires. -/
noncomputable def swapPrefix (w N : ℕ) : (k : ℕ) → k ≤ w → List (ReflectionGate (w+N+w))
  | 0,_ => []
  | k+1,hk => swapPrefix w N k (by omega) ++
      knownSwapSteps (left w N ⟨k,by omega⟩) (right w N ⟨k,by omega⟩)

/-- Swapping the next pair of wires advances the partial-swap state by one bit. -/
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

/-- The prefix swap program exchanges precisely the first `k` bits on basis inputs. -/
theorem prefix_basis (w N k : ℕ) (hk : k ≤ w) (x y : Reg w) :
    Run 1 (reflectionCompile (swapPrefix w N k hk)) (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w N w x y)) =
      Qatlib.Foundations.PureStateMath.Ket (state w N k x y) := by
  induction k with
  | zero => simp [swapPrefix,reflectionCompile,state]
  | succ k ih =>
    rw [swapPrefix,reflectionCompile_append,run_append,ih (by omega)]
    rw [(knownSwapSteps_spec (left w N ⟨k,by omega⟩) (right w N ⟨k,by omega⟩)).2.2]
    exact congrArg Qatlib.Foundations.PureStateMath.Ket (one_state w N ⟨k,by omega⟩ x y)

/-- The prefix swap program is legal and has exactly `3*k` gates. -/
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

/-- The program that swaps both complete word registers around the workspace. -/
noncomputable def word (w N : ℕ) : List (ReflectionGate (w+N+w)) := swapPrefix w N w (Nat.le_refl w)

/-- The full swap program exchanges the two word registers on basis states. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Swap

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.InPlace
open Matrix Layout
open scoped Classical

/-- Evaluates the selected word outputs of a Boolean DAG. -/
def value {w n : ℕ} (g : BooleanDAG w n) (out : Fin w → Fin (w+n)) (x : Reg w) : Reg w :=
  fun j => booleanDAGValue g x (out j)

/-- Combines forward DAG evaluation, a word swap, and inverse DAG evaluation in a shared padded
workspace. -/
noncomputable def word {w nf ng : ℕ} (f : BooleanDAG w nf) (fo : Fin w → Fin (w+nf))
    (g : BooleanDAG w ng) (go : Fin w → Fin (w+ng)) : List (ReflectionGate (w+max nf ng+w)) :=
  liftedDAG f fo (paddedWires w nf w (max nf ng) (Nat.le_max_left _ _)) ++
  Swap.word w (max nf ng) ++
  liftedDAG g go (paddedWires w ng w (max nf ng) (Nat.le_max_right _ _))

/-- If the second DAG is a left inverse of the first, the combined program updates the input
word and restores the auxiliary registers. -/
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

/-- The in-place program is legal and query-free, with at most `30*(nf+ng)+5*w` gates. -/
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

/-- The adjoint of the in-place program is a matrix left inverse of equal length. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.InPlace

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded
open Matrix ModularReversibleWord Bits
open scoped Classical

/-- Packages an arithmetic DAG on two operands and a modulus together with its remainder-output
selector. -/
structure Raw (w k : ℕ) where
  nodes : ℕ
  graph : BooleanDAG (2*w+k) nodes
  output : Fin (2*k) → Fin ((2*w+k)+nodes)

/-- Packages the raw modular-addition graph and its output selector. -/
def addRaw (w : ℕ) : Raw w (w+1) := ⟨addNodes w,modAddGraph w,modAddSelect w⟩
/-- Packages the raw modular-multiplication graph and its output selector. -/
def mulRaw (w : ℕ) : Raw w (2*w) := ⟨mulNodes w,modMulGraph w,modMulSelect w⟩

/-- Resizes a word to width `k` by keeping available low bits and filling higher positions with
false. -/
def extend (w k : ℕ) (m : Reg w) : Reg k := fun j =>
  if hj : j.val < w then m ⟨j.val,hj⟩ else false

/-- The input DAG extended by false and true constant wires. -/
def constants (w : ℕ) : BooleanDAG w 2 := withConstants .nil

/-- Embeds an input-word wire among the inputs and additional nodes of a DAG. -/
def inputWire {w K : ℕ} (j : Fin w) : Fin (w+K) := Fin.castLE (by omega) j

/-- Routes a fixed operand, a variable input word, and a fixed modulus into the raw arithmetic
input layout. -/
def rawSource (w k : ℕ) (a m : Reg w) : Fin (2*w+k) → Fin (w+2) := fun j =>
  if hj : j.val < w then constantWire (a ⟨j.val,hj⟩)
  else if hs : j.val < 2*w then inputWire ⟨j.val-w,by omega⟩
  else if hm : j.val-2*w < w then constantWire (m ⟨j.val-2*w,hm⟩)
  else constantWire false

/-- Evaluating the routed sources supplies the fixed operand, variable word, and resized modulus
to the raw graph. -/
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

/-- Specializes a raw arithmetic graph to a fixed operand and modulus using constant nodes. -/
def curriedGraph {w k : ℕ} (p : Raw w k) (a m : Reg w) : BooleanDAG w (2+p.nodes) :=
  booleanDAGSplice (constants w) (rawSource w k a m) p.graph

/-- Selects the arithmetic outputs of the graph specialized to a fixed operand and modulus. -/
def curriedSelect {w k : ℕ} (p : Raw w k) (a m : Reg w) :
    Fin (2*k) → Fin (w+(2+p.nodes)) :=
  fun j => booleanSpliceSource (rawSource w k a m) (p.output j)

/-- The specialized graph has the same output as the raw graph on the corresponding arithmetic
input. -/
theorem curried_output {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    (fun j => booleanDAGValue (curriedGraph p a m) x (curriedSelect p a m j)) =
      (fun j => booleanDAGValue p.graph (input w k a x (extend w k m)) (p.output j)) := by
  funext j
  have h := boolean_dag_splice_value (constants w) (rawSource w k a m) p.graph x (p.output j)
  rw [raw_input] at h
  exact h

/-- The constant wires retain their Boolean values after specialization and splicing. -/
theorem curried_constant {w k : ℕ} (p : Raw w k) (a m x : Reg w) (b : Bool) :
    booleanDAGValue (curriedGraph p a m) x
      (Fin.castLE (by omega) (constantWire (M:=w) (K:=0) b)) = b := by
  exact (boolean_dag_splice_prefix (constants w) (rawSource w k a m) p.graph x (constantWire b)).trans
    (constant_wire_value (.nil : BooleanDAG w 0) x b)

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded
open Matrix ModularReversibleWord Bits
open scoped Classical

/-- The node count of the conditional-subtraction comparison stage. -/
def cmpNodes (w : ℕ) : ℕ := 7*w+1+3*w+1

/-- Routes the variable word and fixed modulus into the comparison stage. -/
def cmpSource {w k : ℕ} (p : Raw w k) (m : Reg w) : Fin (2*w) → Fin (w+(2+p.nodes)) := fun j =>
  if hj : j.val < w then inputWire ⟨j.val,hj⟩
  else Fin.castLE (by omega) (constantWire (M:=w) (K:=0) (m ⟨j.val-w,by omega⟩))

/-- Appends conditional subtraction to compare the variable input with the modulus. -/
def cmpGraph {w k : ℕ} (p : Raw w k) (a m : Reg w) : BooleanDAG w ((2+p.nodes)+cmpNodes w) :=
  booleanDAGSplice (curriedGraph p a m) (cmpSource p m) (booleanWordCondSubDAG w)
/-- Selects the final conditional-subtraction flag in the comparison graph. -/
def cmpFlag {w k : ℕ} (p : Raw w k) (m : Reg w) : Fin (w+((2+p.nodes)+cmpNodes w)) :=
  booleanSpliceSource (cmpSource p m) (booleanWordCondSubSelect w (Fin.last w))

/-- Appends the negated comparison flag to test whether the input is below the modulus. -/
def validGraph {w k : ℕ} (p : Raw w k) (a m : Reg w) : BooleanDAG w (((2+p.nodes)+cmpNodes w)+1) :=
  (cmpGraph p a m).snoc (.neg (cmpFlag p m))
/-- Selects the final validity-test wire. -/
def validWire {w k : ℕ} (p : Raw w k) : Fin (w+(((2+p.nodes)+cmpNodes w)+1)) :=
  ⟨w+((2+p.nodes)+cmpNodes w),by omega⟩

/-- The comparison sources evaluate to the variable word followed by the fixed modulus. -/
theorem cmp_input {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    (fun j => booleanDAGValue (curriedGraph p a m) x (cmpSource p m j)) =
      booleanWordAdderInput w x m := by
  funext j
  by_cases hj : j.val < w
  · simp only [cmpSource,dif_pos hj,inputWire,input_wire,booleanWordAdderInput]
  · simp only [cmpSource,dif_neg hj,curried_constant,booleanWordAdderInput]

/-- The selected comparison flag equals the final flag of conditional subtraction on the input
and modulus. -/
theorem cmp_flag_value {w k : ℕ} (p : Raw w k) (a m x : Reg w) :
    booleanDAGValue (cmpGraph p a m) x (cmpFlag p m) =
      booleanWordCondSubResult w x m (Fin.last w) := by
  have h := boolean_dag_splice_value (curriedGraph p a m) (cmpSource p m)
    (booleanWordCondSubDAG w) x (booleanWordCondSubSelect w (Fin.last w))
  rw [cmp_input] at h
  exact h

/-- The validity wire is true exactly when the input word value is smaller than the modulus
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

/-- Adding the validity test preserves the values of all wires in the specialized arithmetic
graph. -/
theorem valid_old {w k : ℕ} (p : Raw w k) (a m x : Reg w) (i : Fin (w+(2+p.nodes))) :
    booleanDAGValue (validGraph p a m) x (Fin.castLE (by omega) i) =
      booleanDAGValue (curriedGraph p a m) x i := by
  simp only [validGraph,booleanDAGValue]
  have he : (Fin.castLE (by omega) i : Fin (w+(((2+p.nodes)+cmpNodes w)+1))) =
      Fin.castSucc (Fin.castLE (by omega) i : Fin (w+((2+p.nodes)+cmpNodes w))) := Fin.ext rfl
  rw [he,Fin.lastCases_castSucc]
  exact boolean_dag_splice_prefix (curriedGraph p a m) (cmpSource p m) (booleanWordCondSubDAG w) x i

/-- Selects the lowest `w` arithmetic-output bits within the graph extended by the validity
test. -/
def lowSource {w k : ℕ} (p : Raw w k) (a m : Reg w) (hk : w ≤ 2*k) :
    Fin w → Fin (w+(((2+p.nodes)+cmpNodes w)+1)) := fun j =>
  Fin.castLE (by omega) (curriedSelect p a m (Fin.castLE hk j))

/-- The total node count for specialization, comparison, validity testing, and guarded output
selection. -/
def nodes {w k : ℕ} (p : Raw w k) : ℕ := (((2+p.nodes)+cmpNodes w)+1)+3*w

/-- Constructs a mux graph that selects the arithmetic result below the modulus and the original
input otherwise. -/
def graph {w k : ℕ} (p : Raw w k) (a m : Reg w) (hk : w ≤ 2*k) : BooleanDAG w (nodes p) :=
  booleanDAGSplice (validGraph p a m)
    (booleanMuxSources w (lowSource p a m hk) inputWire (validWire p)) (booleanWordMuxDAG w)

/-- Selects the word output of the guarded arithmetic graph. -/
def output {w k : ℕ} (p : Raw w k) (a m : Reg w) (hk : w ≤ 2*k) : Fin w → Fin (w+nodes p) :=
  fun j => booleanSpliceSource
    (booleanMuxSources w (lowSource p a m hk) inputWire (validWire p)) (booleanWordMuxSelect w j)

/-- The guarded graph returns the low arithmetic-output bits below the modulus and leaves other
inputs unchanged. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded
open Qatlib
open scoped Classical BigOperators

/-- Zero extension to a width at least `w` preserves the numerical value of a word. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Arithmetic
/-- Extracts a natural-number modular inverse coefficient from the extended
greatest-common-divisor coefficient. -/
def inverseCoefficient (a m : ℕ) : ℕ := (Nat.gcdA a m % (m : ℤ)).toNat

/-- For a positive modulus and coprime coefficient, `inverseCoefficient` is below the modulus
and gives a multiplicative inverse modulo it. -/
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

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Arithmetic

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Arithmetic

/-- The canonical additive inverse of `a` modulo `m`. -/
def addInverse (m a : ℕ) : ℕ := (m-a%m)%m

/-- The additive inverse is below a positive modulus. -/
theorem add_inverse_lt (m a : ℕ) (hm : 0 < m) : addInverse m a < m := Nat.mod_lt _ hm

/-- Adding the modular additive inverse agrees with total modular subtraction. -/
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

/-- Multiplies by `a` modulo `m` below a positive modulus and leaves other inputs fixed. -/
def totalMul (m a x : ℕ) : ℕ := if 0 < m ∧ x < m then (a*x)%m else x

/-- Multiplication by a modular inverse undoes total modular multiplication on every input. -/
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

/-- Total modular multiplication preserves `x < N` when `m ≤ N`. -/
theorem totalMul_lt (m a x N : ℕ) (hm : m ≤ N) (hx : x < N) : totalMul m a x < N := by
  unfold totalMul
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans_le hm
  · exact hx

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Arithmetic

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits
open Qatlib
open scoped Classical

/-- Encodes `n` modulo `2^w` as a word in least-significant-bit order. -/
def ofNat (w n : ℕ) : Reg w := fun i =>
  (bitVecEquiv w).symm ⟨n%2^w,Nat.mod_lt _ (by positivity)⟩ (Fin.rev i)

/-- The value of `ofNat w n` is `n` modulo `2^w`. -/
theorem ofNat_value (w n : ℕ) : booleanWordLSBValue w (ofNat w n) = n%2^w := by
  have he : (fun j => ofNat w n (Fin.rev j)) =
      (bitVecEquiv w).symm ⟨n%2^w,Nat.mod_lt _ (by positivity)⟩ := by
    funext j
    simp [ofNat]
  unfold booleanWordLSBValue
  rw [he,Equiv.apply_symm_apply]

/-- Every width-`w` word has numerical value smaller than `2^w`. -/
theorem lsb_lt (w : ℕ) (a : Reg w) : booleanWordLSBValue w a < 2^w :=
  (bitVecEquiv w (fun j => a (Fin.rev j))).isLt
end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded
open ModularReversibleWord Bits Arithmetic
open scoped Classical

/-- The guarded output value is the raw arithmetic output modulo `2^w` below the modulus, and
the original value otherwise. -/
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

/-- The guarded raw addition graph computes total modular addition on word values. -/
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

/-- The guarded raw multiplication graph computes total modular multiplication on word values. -/
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

/-- The guarded graph adds exactly `13*w+5` nodes to the raw graph. -/
theorem nodes_eq {w k : ℕ} (p : Raw w k) : nodes p = p.nodes+13*w+5 := by
  dsimp only [nodes,cmpNodes]
  omega
end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Guarded

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Native
open Matrix Bits Arithmetic
open scoped Classical

/-- Encodes the modular additive inverse of the fixed operand as a word. -/
def addInvBits (w : ℕ) (a m : Reg w) : Reg w :=
  ofNat w (addInverse (booleanWordLSBValue w m) (booleanWordLSBValue w a))
/-- Encodes the modular inverse coefficient of the fixed multiplier as a word. -/
def mulInvBits (w : ℕ) (a m : Reg w) : Reg w :=
  ofNat w (inverseCoefficient (booleanWordLSBValue w a) (booleanWordLSBValue w m))

/-- The word function computed by the guarded modular-addition graph. -/
def addFunction (w : ℕ) (a m x : Reg w) : Reg w :=
  InPlace.value (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega)) x

/-- The word function computed by the guarded modular-multiplication graph. -/
def mulFunction (w : ℕ) (a m x : Reg w) : Reg w :=
  InPlace.value (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega)) x

/-- The additive-inverse word encodes the exact canonical additive inverse modulo the
represented modulus. -/
theorem add_inv_bits_value (w : ℕ) (a m : Reg w) :
    booleanWordLSBValue w (addInvBits w a m) =
      addInverse (booleanWordLSBValue w m) (booleanWordLSBValue w a) := by
  rw [addInvBits,ofNat_value]
  apply Nat.mod_eq_of_lt
  by_cases hm : 0 < booleanWordLSBValue w m
  · exact (add_inverse_lt _ _ hm).trans (lsb_lt w m)
  · have he : booleanWordLSBValue w m = 0 := by omega
    simp [he,addInverse]

/-- The numerical value of `addFunction` is total modular addition. -/
theorem add_function_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w (addFunction w a m x) =
      totalAdd (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) :=
  Guarded.add_value w a m x

/-- The numerical value of `mulFunction` is total modular multiplication. -/
theorem mul_function_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w (mulFunction w a m x) =
      totalMul (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) :=
  Guarded.mul_value w a m x

/-- Applying addition with the additive-inverse word undoes `addFunction`. -/
theorem add_function_inverse (w : ℕ) (a m x : Reg w) :
    addFunction w (addInvBits w a m) m (addFunction w a m x) = x := by
  apply lsb_injective w
  have h := add_function_value w (addInvBits w a m) m (addFunction w a m x)
  rw [add_function_value w a m x,add_inv_bits_value,inverse_add_as_sub,sub_add] at h
  exact h

/-- For a multiplier coprime to the modulus, multiplication with its inverse word undoes
`mulFunction`. -/
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

/-- The shared workspace size for the forward and inverse guarded addition graphs. -/
def addWork (w : ℕ) : ℕ := max (Guarded.nodes (Guarded.addRaw w)) (Guarded.nodes (Guarded.addRaw w))
/-- The shared workspace size for the forward and inverse guarded multiplication graphs. -/
def mulWork (w : ℕ) : ℕ := max (Guarded.nodes (Guarded.mulRaw w)) (Guarded.nodes (Guarded.mulRaw w))

/-- The native in-place gate program for guarded modular addition by a fixed word. -/
noncomputable def addWord (w : ℕ) (a m : Reg w) : List (ReflectionGate (w+addWork w+w)) :=
  InPlace.word (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (addInvBits w a m) m (by omega))

/-- The native in-place gate program built from guarded multiplication and its
inverse-coefficient graph. -/
noncomputable def mulWord (w : ℕ) (a m : Reg w) : List (ReflectionGate (w+mulWork w+w)) :=
  InPlace.word (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))

/-- The native addition program computes `addFunction` on basis inputs and restores its
auxiliary registers. -/
theorem add_basis (w : ℕ) (a m x : Reg w) :
    Run 1 (reflectionCompile (addWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w (addFunction w a m x) (fun _ => false)) :=
  InPlace.basis _ _ _ _ (add_function_inverse w a m) x

/-- For a multiplier coprime to the modulus, the native multiplication program computes
`mulFunction` and restores its auxiliary registers. -/
theorem mul_basis (w : ℕ) (a m x : Reg w)
    (hc : (booleanWordLSBValue w a).Coprime (booleanWordLSBValue w m)) :
    Run 1 (reflectionCompile (mulWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (mulWork w) w (mulFunction w a m x) (fun _ => false)) :=
  InPlace.basis _ _ _ _ (fun x => mul_function_inverse w a m x hc) x

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Native

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Native
open Matrix ModularReversibleWord Bits Arithmetic
open scoped Classical

/-- The guarded addition graph has at most `20*w^2+64*w+33` nodes. -/
theorem add_node_bound (w : ℕ) : Guarded.nodes (Guarded.addRaw w) ≤ 20*w^2+64*w+33 := by
  rw [Guarded.nodes_eq]
  change addNodes w+13*w+5 ≤ _
  have h := (mod_add_resources w).1
  omega

/-- The guarded multiplication graph has at most `91*w^2+26*w+7` nodes. -/
theorem mul_node_bound (w : ℕ) : Guarded.nodes (Guarded.mulRaw w) ≤ 91*w^2+26*w+7 := by
  rw [Guarded.nodes_eq]
  change mulNodes w+13*w+5 ≤ _
  have h := (mod_mul_resources w).1
  omega

/-- The native addition program is legal and query-free, with explicit quadratic gate and
workspace bounds. -/
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

/-- The native multiplication program is legal and query-free, with explicit quadratic gate and
workspace bounds. -/
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

/-- The adjoint of the native addition program is a matrix left inverse with the same length. -/
theorem add_inverse (w : ℕ) (a m : Reg w) :
    reflectionProgramMatrix (reflectionAdjoint (addWord w a m)) *
      reflectionProgramMatrix (addWord w a m) = 1 ∧
    (reflectionAdjoint (addWord w a m)).length = (addWord w a m).length :=
  InPlace.inverse (Guarded.graph (Guarded.addRaw w) a m (by omega))
    (Guarded.output (Guarded.addRaw w) a m (by omega))
    (Guarded.graph (Guarded.addRaw w) (addInvBits w a m) m (by omega))
    (Guarded.output (Guarded.addRaw w) (addInvBits w a m) m (by omega))

/-- The adjoint of the native multiplication program is a matrix left inverse with the same
length. -/
theorem mul_inverse_word (w : ℕ) (a m : Reg w) :
    reflectionProgramMatrix (reflectionAdjoint (mulWord w a m)) *
      reflectionProgramMatrix (mulWord w a m) = 1 ∧
    (reflectionAdjoint (mulWord w a m)).length = (mulWord w a m).length :=
  InPlace.inverse (Guarded.graph (Guarded.mulRaw w) a m (by omega))
    (Guarded.output (Guarded.mulRaw w) a m (by omega))
    (Guarded.graph (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))
    (Guarded.output (Guarded.mulRaw w) (mulInvBits w a m) m (by omega))

/-- The word function that adds the modular additive inverse of the fixed operand. -/
def subFunction (w : ℕ) (a m x : Reg w) : Reg w := addFunction w (addInvBits w a m) m x
/-- The native subtraction program obtained as the adjoint of native addition. -/
noncomputable def subWord (w : ℕ) (a m : Reg w) : List (ReflectionGate (w+addWork w+w)) :=
  reflectionAdjoint (addWord w a m)

/-- The numerical value of `subFunction` is total modular subtraction. -/
theorem sub_function_value (w : ℕ) (a m x : Reg w) :
    booleanWordLSBValue w (subFunction w a m x) =
      totalSub (booleanWordLSBValue w m) (booleanWordLSBValue w a) (booleanWordLSBValue w x) := by
  have h := add_function_value w (addInvBits w a m) m x
  rw [add_inv_bits_value,inverse_add_as_sub] at h
  exact h

/-- Native addition composed after `subFunction` returns the original word. -/
theorem add_function_right_inverse (w : ℕ) (a m x : Reg w) :
    addFunction w a m (subFunction w a m x) = x := by
  apply lsb_injective w
  have h := add_function_value w a m (subFunction w a m x)
  rw [sub_function_value,add_sub] at h
  exact h

/-- The native subtraction program computes `subFunction` on basis inputs and restores its
auxiliary registers. -/
theorem sub_basis (w : ℕ) (a m x : Reg w) :
    Run 1 (reflectionCompile (subWord w a m))
      (Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w x (fun _ => false))) =
      Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput w (addWork w) w (subFunction w a m x) (fun _ => false)) := by
  have hf := add_basis w a m (subFunction w a m x)
  rw [add_function_right_inverse] at hf
  rw [subWord,run_reflectionCompile,← hf,run_reflectionCompile,← applyGate_mul,
    (add_inverse w a m).1,applyGate_one]

end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Native

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Native
open Matrix Bits Arithmetic
open scoped Classical

/-- The guarded multiplication function is the identity when the modulus word has value zero. -/
theorem mul_function_zero (w : ℕ) (a m x : Reg w) (hm : booleanWordLSBValue w m = 0) :
    mulFunction w a m x = x := by
  apply lsb_injective w
  have h := mul_function_value w a m x
  simpa only [hm,totalMul,lt_self_iff_false,false_and,ite_false] using! h

/-- For a zero-valued modulus, the native multiplication program fixes basis inputs with zero
auxiliary registers. -/
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
end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Native

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord
open Matrix Bits Arithmetic Native
open scoped Classical

/-- For a multiplier coprime to the represented modulus, the native programs implement total
modular addition, subtraction, and multiplication with clean auxiliary registers, explicit
gate and workspace bounds, and matrix inverse identities. -/
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
end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord
