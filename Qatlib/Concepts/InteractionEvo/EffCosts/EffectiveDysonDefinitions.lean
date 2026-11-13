/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.ComputedGrid.ComputedDysonGridProgram
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision
import Mathlib.Data.Nat.Bits

/-!
# Effective programs for Dyson simulation

This module defines an explicit instruction language `EffectiveStep` and finite programs
`EffectiveProgram`, with matrix semantics, wire legality, resource counts, and success and
failure specifications. Bit encodings and Turing machine compiler predicates make the classical
description costs explicit.

It also defines segment, sparse-oracle, and interaction picture parameters, together with strict
and repeated-index Dyson sums. These interfaces organize the implementation data for the
Hamiltonian simulation framework of [LowWiebe2018].

## Main statements

* `EffectiveGuarantee`: operator, failure, and state error requirements.
* `EffectiveCompilerTime`: a bounded-time machine producing program bits.
* `EffectiveHAMT`: a unitary oracle encoding the sampled Hamiltonian block.
* `EffectiveSparseLegal`: the bounded Hermitian sparse-data conditions.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.InteractionEvo.EffCosts
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Instructions consisting of finite gates, dyadic-angle phase rotations, controlled oracle
queries with an adjoint flag, and zero postselections. -/
inductive EffectiveStep where
  | fixed : FiniteGateCode → EffectiveStep
  | phase : ℕ → ℤ → ℕ → Bool → EffectiveStep
  | query : ℕ → List ℕ → List (ℕ × Bool) → Bool → EffectiveStep
  | postselect : List ℕ → EffectiveStep
  deriving DecidableEq, Repr

/-- A register width and a finite list of effective instructions. -/
structure EffectiveProgram where
  width : ℕ
  steps : List EffectiveStep
  deriving DecidableEq, Repr

/-- A family of oracle matrices indexed by oracle slot and register width. -/
abbrev EffectiveEnvironment := (slot m : ℕ) → Matrix (Reg m) (Reg m) ℂ

/-- Embed `U` on the selected wires when the control bits match, preserving other wires, and act
as the identity when the controls do not match. -/
noncomputable def selectedQuery (n : ℕ) (ws : List ℕ) (cs : List (ℕ × Bool))
    (U : Matrix (Reg ws.length) (Reg ws.length) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y =>
    if hc : ∀ c ∈ cs, ∃ h : c.1 < n, y ⟨c.1,h⟩ = c.2 then
      if ∀ i : Fin n, i.val ∉ ws → x i = y i then
        U (fun i => if h : ws[i] < n then x ⟨ws[i],h⟩ else false)
          (fun i => if h : ws[i] < n then y ⟨ws[i],h⟩ else false)
      else 0
    else if x = y then 1 else 0

/-- Interpret an effective instruction as a register matrix, using the environment for queries
and a diagonal zero projector for postselection. -/
noncomputable def effectiveStepMatrix (n : ℕ) (E : EffectiveEnvironment) :
    EffectiveStep → Matrix (Reg n) (Reg n) ℂ
  | .fixed g => finiteCodeMatrix n g
  | .phase w a b axis =>
      if h : w < n then
        let V := Rz ((a : ℝ) * Real.pi / (2 : ℝ)^b)
        wireGate n ⟨w,h⟩ (if axis then Hadamard * V * Hadamard else V)
      else 1
  | .query slot ws cs adj =>
      selectedQuery n ws cs (if adj then (E slot ws.length)ᴴ else E slot ws.length)
  | .postselect ws => Matrix.diagonal fun x =>
      if ∀ w ∈ ws, ∃ h : w < n, x ⟨w,h⟩=false then 1 else 0

/-- The reverse-order product of instruction matrices giving the semantics of an effective
program. -/
noncomputable def effectiveMatrix (p : EffectiveProgram) (E : EffectiveEnvironment) :
    Matrix (Reg p.width) (Reg p.width) ℂ :=
  (p.steps.map (effectiveStepMatrix p.width E)).reverse.prod

/-- The wire-range and distinctness conditions for an instruction, including disjoint target and
control wires for queries. -/
def effectiveStepLegal (n : ℕ) : EffectiveStep → Prop
  | .fixed g => finiteCodeLegal n g = true
  | .phase w _ _ _ => w < n
  | .query _ ws cs _ => ws.Nodup ∧ (∀ w ∈ ws, w < n) ∧
      (cs.map Prod.fst).Nodup ∧ (∀ c ∈ cs, c.1 < n ∧ c.1 ∉ ws)
  | .postselect ws => ws.Nodup ∧ (∀ w ∈ ws, w < n)

/-- Every instruction of the program is legal at the program's register width. -/
def effectiveLegal (p : EffectiveProgram) : Prop :=
  ∀ s ∈ p.steps, effectiveStepLegal p.width s

/-- Count the oracle query instructions in a program. -/
def effectiveQueries (p : EffectiveProgram) : ℕ :=
  (p.steps.filter fun s => match s with | .query .. => true | _ => false).length

/-- Count the query instructions using oracle slot `j`. -/
def effectiveSlotQueries (p : EffectiveProgram) (j : ℕ) : ℕ :=
  (p.steps.filter fun s => match s with | .query slot _ _ _ => slot == j | _ => false).length

/-- Count the fixed-gate and phase-rotation instructions in a program. -/
def effectiveGates (p : EffectiveProgram) : ℕ :=
  (p.steps.filter fun s => match s with | .fixed .. | .phase .. => true | _ => false).length

/-- Count the postselection instructions in a program. -/
def effectivePostselects (p : EffectiveProgram) : ℕ :=
  (p.steps.filter fun s => match s with | .postselect .. => true | _ => false).length

/-- Count the final ancillary wires plus the wire counts of all explicit postselection
instructions. -/
def effectiveMeasurements (ns : ℕ) (p : EffectiveProgram) : ℕ :=
  p.width-ns + (p.steps.map fun s => match s with | .postselect ws => ws.length | _ => 0).sum

/-- The program contains no postselection instruction. -/
def effectiveCoherent (p : EffectiveProgram) : Prop :=
  ∀ ws : List ℕ, EffectiveStep.postselect ws ∉ p.steps

/-- The program is legal and every oracle matrix used by a query is unitary. -/
def EffectivePhysical (p : EffectiveProgram) (E : EffectiveEnvironment) : Prop :=
  effectiveLegal p ∧ ∀ slot ws cs adj, EffectiveStep.query slot ws cs adj ∈ p.steps →
    E slot ws.length ∈ Matrix.unitaryGroup (Reg ws.length) ℂ

/-- The matrix identifying an `ns`-qubit system register with the initial wires of an `n`-qubit
register whose remaining wires are zero. -/
noncomputable def effectiveFrame (ns n : ℕ) : Matrix (Reg n) (Reg ns) ℂ :=
  fun x y => if (∀ i : Fin ns, ∃ h : i.val < n, x ⟨i.val,h⟩ = y i) ∧
    (∀ i : Fin n, ns ≤ i.val → x i = false) then 1 else 0

/-- Compress a program matrix to its system block using the zero-ancilla frame. -/
noncomputable def effectiveCorner (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment) :
    Matrix (Reg ns) (Reg ns) ℂ :=
  (effectiveFrame ns p.width)ᴴ * effectiveMatrix p E * effectiveFrame ns p.width

/-- Apply the zero-ancilla system block of a program to the input state. -/
noncomputable def effectiveSuccess (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment)
    (ψ : QState (Reg ns)) : QState (Reg ns) := effectiveCorner ns p E *ᵥ ψ

/-- Execute a list of instructions and return the resulting vector together with the accumulated
squared-norm losses at postselections. -/
noncomputable def effectiveStoppedRun (n : ℕ) (E : EffectiveEnvironment) :
    List EffectiveStep → QState (Reg n) → QState (Reg n) × ℝ
  | [], ψ => (ψ,0)
  | step :: rest, ψ =>
      let v := effectiveStepMatrix n E step *ᵥ ψ
      let result := effectiveStoppedRun n E rest v
      match step with
      | .postselect _ => (result.1, result.2 +
          ‖toEuclidean_fromVec ψ‖^2 - ‖toEuclidean_fromVec v‖^2)
      | _ => result

/-- Sum the explicit postselection losses and the final squared-norm loss from projecting
ancillary wires onto zero. -/
noncomputable def effectiveFailure (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment)
    (ψ : QState (Reg ns)) : ℝ :=
  let result := effectiveStoppedRun p.width E p.steps (effectiveFrame ns p.width *ᵥ ψ)
  result.2 + ‖toEuclidean_fromVec result.1‖^2 -
    ‖toEuclidean_fromVec ((effectiveFrame ns p.width)ᴴ *ᵥ result.1)‖^2

/-- The system fits in the program register, the program is coherent, and its action on framed
states stays in the zero-ancilla frame. -/
def EffectiveCleanProgram (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment) : Prop :=
  ns ≤ p.width ∧ effectiveCoherent p ∧ ∀ ψ : QState (Reg ns),
    effectiveMatrix p E *ᵥ (effectiveFrame ns p.width *ᵥ ψ) =
      effectiveFrame ns p.width *ᵥ (effectiveCorner ns p E *ᵥ ψ)

/-- Require physical legality, system-block operator error at most `ε`, failure between zero and
`2 ε` on normalized states, and state error at most `ε` times the input norm. -/
def EffectiveGuarantee (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment)
    (U : Matrix (Reg ns) (Reg ns) ℂ) (ε : ℝ) : Prop :=
  ns ≤ p.width ∧ EffectivePhysical p E ∧
  ‖effectiveCorner ns p E - U‖ ≤ ε ∧
  (∀ ψ : QState (Reg ns), Normalized ψ →
    0 ≤ effectiveFailure ns p E ψ ∧ effectiveFailure ns p E ψ ≤ 2*ε) ∧
  (∀ ψ : QState (Reg ns),
    ‖toEuclidean_fromVec (effectiveSuccess ns p E ψ - U *ᵥ ψ)‖ ≤ ε * ‖toEuclidean_fromVec ψ‖)

/-- Encode a natural number by a unary binary-length prefix, a false delimiter, and its binary
digits. -/
def effectiveNatBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- Encode an integer as the two natural-number fields recording its sign and absolute value. -/
def effectiveIntFields (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]
/-- Serialize an instruction as tagged natural-number fields, including its wires, controls, and
angle or oracle data. -/
def effectiveStepFields : EffectiveStep → List ℕ
  | .fixed (.h w) => [0,w]
  | .fixed (.x w) => [1,w]
  | .fixed (.t w) => [2,w]
  | .fixed (.tdg w) => [3,w]
  | .fixed (.cx c t) => [4,c,t]
  | .phase w a b axis => [5,w] ++ effectiveIntFields a ++ [b,if axis then 1 else 0]
  | .query slot ws cs adj => [6,slot,ws.length] ++ ws ++ [cs.length] ++
      cs.flatMap (fun c => [c.1,if c.2 then 1 else 0]) ++ [if adj then 1 else 0]
  | .postselect ws => [7,ws.length] ++ ws
/-- Serialize the program width, instruction count, and instruction fields using the
natural-number bit encoding. -/
def effectiveProgramBits (p : EffectiveProgram) : List Bool :=
  ([p.width,p.steps.length] ++ p.steps.flatMap effectiveStepFields).flatMap effectiveNatBits

/-- A single finite-state Turing machine halts within the supplied budget on each encoded input
and writes the encoded built program on its output tape. -/
def EffectiveCompilerTime {A : Type} (input : A → List Bool) (build : A → EffectiveProgram)
    (budget : A → ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ a : A, ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
      s ≤ budget a ∧ BitMachineAfter M ((input a).map some) s = some cfg ∧
      Turing.TM0.step M cfg = none ∧
      (∀ i : ℕ, cfg.Tape.right₀.nth i = ((effectiveProgramBits (build a)).map some).getD i none)

/-- Interpret register bits as a natural number with weight `2^i` at wire `i`. -/
def effectiveRegNat {n : ℕ} (x : Reg n) : ℕ := ∑ i : Fin n, if x i then 2^i.val else 0

/-- Register sizes, precision, rational duration, Hamiltonian norm bound, and mean derivative
bound for a simulation segment. -/
structure EffectiveSegmentParameters where
  ns : ℕ
  na : ℕ
  nd : ℕ
  precision : ℕ
  time : ℚ
  alpha : ℚ
  meanDerivative : ℚ
  deriving DecidableEq, Repr

/-- The computed Dyson cutoff at precision `p.precision + 8`. -/
def effectiveSegmentK (p : EffectiveSegmentParameters) : ℕ := computedDysonCutoff (p.precision+8)
/-- The dyadic grid size `2^p.nd`. -/
def effectiveSegmentM (p : EffectiveSegmentParameters) : ℕ := 2^p.nd
/-- Nonnegative time and mean derivative bound, positive norm bound, scaled time at most one
half, and a dyadic grid at least the computed requirement. -/
noncomputable def effectiveSegmentDomain (p : EffectiveSegmentParameters) : Prop :=
  0 ≤ p.time ∧ 0 < p.alpha ∧ 0 ≤ p.meanDerivative ∧
  (p.alpha : ℝ)*(p.time : ℝ) ≤ 1/2 ∧
  computedDysonGridSize p.time p.alpha p.meanDerivative (p.precision+8) ≤ effectiveSegmentM p

/-- Serialize the register sizes, precision, and rational segment parameters as a Boolean list. -/
def effectiveSegmentInput (p : EffectiveSegmentParameters) : List Bool :=
  ([p.ns,p.na,p.nd,p.precision] ++ effectiveIntFields p.time.num ++ [p.time.den] ++
    effectiveIntFields p.alpha.num ++ [p.alpha.den] ++
    effectiveIntFields p.meanDerivative.num ++ [p.meanDerivative.den]).flatMap effectiveNatBits

/-- The block diagonal sampled Hamiltonian matrix on system and time wires, normalized by
`p.alpha`. -/
noncomputable def effectiveGridBlock (p : EffectiveSegmentParameters)
    (H : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) :
    Matrix (Reg (p.ns+p.nd)) (Reg (p.ns+p.nd)) ℂ :=
  fun x y =>
    let tx : Reg p.nd := fun i => x ⟨p.ns+i.val,by omega⟩
    let ty : Reg p.nd := fun i => y ⟨p.ns+i.val,by omega⟩
    if tx=ty then
      (1/(p.alpha : ℂ)) * H ((p.time : ℝ)*effectiveRegNat tx/effectiveSegmentM p)
        (fun i => x ⟨i.val,by omega⟩) (fun i => y ⟨i.val,by omega⟩)
    else 0

/-- The oracle is unitary and its zero-ancilla corner equals the normalized sampled Hamiltonian
block. -/
noncomputable def EffectiveHAMT (p : EffectiveSegmentParameters)
    (H : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (O : Matrix (Reg (p.ns+p.nd+p.na)) (Reg (p.ns+p.nd+p.na)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup (Reg (p.ns+p.nd+p.na)) ℂ ∧
  (effectiveFrame (p.ns+p.nd) (p.ns+p.nd+p.na))ᴴ * O *
    effectiveFrame (p.ns+p.nd) (p.ns+p.nd+p.na) = effectiveGridBlock p H

/-- Place `O` at the specified slot and width, using identity matrices at every other slot-width
pair. -/
noncomputable def effectiveOneOracle (slot width : ℕ)
    (O : Matrix (Reg width) (Reg width) ℂ) : EffectiveEnvironment :=
  fun j m => if h : j=slot ∧ m=width then h.2.symm ▸ O else 1

/-- The field is continuous, has the specified derivative and bounded Hermitian values on the
segment, and its integrable derivative norm obeys the mean derivative bound. -/
noncomputable def EffectiveField (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) : Prop :=
  Continuous H ∧ IntervalIntegrable (fun u => ‖Hd u‖) MeasureTheory.volume 0 (p.time : ℝ) ∧
  (∀ u ∈ Set.Icc 0 (p.time : ℝ), HasDerivAt H (Hd u) u) ∧
  (∀ u ∈ Set.Icc 0 (p.time : ℝ), (H u).IsHermitian ∧ ‖H u‖ ≤ (p.alpha : ℝ)) ∧
  (∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖) ≤ (p.meanDerivative : ℝ)*(p.time : ℝ)

/-- The strictly lower triangular matrix with each nonzero entry equal to `1 / M`. -/
noncomputable def effectiveTriangle (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => if j < i then (1/(M : ℂ)) else 0

/-- The degree-`k` Dyson grid contribution summed over strictly increasing sample indices,
scaled by `(-i t / M)^k`. -/
noncomputable def effectiveStrictDegree {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ((-Complex.I * (t/(M : ℝ) : ℂ))^k) •
    ∑ v : Fin k → Fin M, if StrictMono v then
      ((List.ofFn (fun i : Fin k => H (t*(v i).val/M))).reverse).prod else 0

/-- The segment count `max 1 ⌈2 p.alpha |p.time|⌉₊` for a possibly signed duration. -/
def effectiveLongR (p : EffectiveSegmentParameters) : ℕ := max 1 ⌈2*p.alpha*abs p.time⌉₊
/-- The local parameters obtained by dividing the absolute duration into segments and increasing
precision and the mean derivative bound as specified. -/
def effectiveLongLocal (p : EffectiveSegmentParameters) : EffectiveSegmentParameters :=
  { p with
    time := abs p.time / (effectiveLongR p : ℚ)
    precision := p.precision + Nat.clog 2 (effectiveLongR p) + 8
    meanDerivative := p.meanDerivative * (effectiveLongR p : ℚ) }
/-- The global norm and mean derivative bounds have the required signs, and the derived local
segment parameters satisfy `effectiveSegmentDomain`. -/
noncomputable def effectiveLongDomain (p : EffectiveSegmentParameters) : Prop :=
  0 < p.alpha ∧ 0 ≤ p.meanDerivative ∧ effectiveSegmentDomain (effectiveLongLocal p)
/-- A continuous bounded Hermitian field on the interval between zero and the signed duration,
with the specified derivative and absolute integral mean bound. -/
noncomputable def effectiveLongField (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) : Prop :=
  Continuous H ∧ IntervalIntegrable (fun u => ‖Hd u‖) MeasureTheory.volume 0 (p.time : ℝ) ∧
  (∀ u ∈ Set.uIcc 0 (p.time : ℝ), HasDerivAt H (Hd u) u) ∧
  (∀ u ∈ Set.uIcc 0 (p.time : ℝ), (H u).IsHermitian ∧ ‖H u‖ ≤ (p.alpha : ℝ)) ∧
  |∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖| ≤ (p.meanDerivative : ℝ)*|(p.time : ℝ)|
/-- Shift the field to segment `j`, reversing time and negating the Hamiltonian when the total
duration is negative. -/
noncomputable def effectiveSignedSegment (p : EffectiveSegmentParameters)
    (H : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) (j : ℕ) :
    ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ :=
  fun u => if p.time < 0 then -H (-((j : ℝ)*(effectiveLongLocal p).time+u))
    else H ((j : ℝ)*(effectiveLongLocal p).time+u)

/-- The block matrix indexed by a counter, containing reverse products `B 1` through `B r` for
counter values `r ≤ K` and zero elsewhere. -/
noncomputable def effectiveCompressionBlock (ns nb K : ℕ)
    (B : ℕ → Matrix (Reg ns) (Reg ns) ℂ) :
    Matrix (Reg (ns+nb)) (Reg (ns+nb)) ℂ :=
  fun x y =>
    let bx : Reg nb := fun i => x ⟨ns+i.val,by omega⟩
    let by' : Reg nb := fun i => y ⟨ns+i.val,by omega⟩
    if bx=by' ∧ effectiveRegNat by' ≤ K then
      (((List.range (effectiveRegNat by')).map (fun j => B (j+1))).reverse.prod)
        (fun i => x ⟨i.val,by omega⟩) (fun i => y ⟨i.val,by omega⟩)
    else 0

/-- The system wires followed by the ancillary and time wire block reserved for copy `j`. -/
def effectiveDuplicatedWires (p : EffectiveSegmentParameters) (j : ℕ) : List ℕ :=
  List.range p.ns ++ List.range' (p.ns+j*(p.na+p.nd)) (p.na+p.nd)
/-- The program has room for all copies, every query uses slot zero on a prescribed copy, and
every copy is queried. -/
def EffectiveDuplicatedLayout (p : EffectiveSegmentParameters) (c : EffectiveProgram) : Prop :=
  p.ns+effectiveSegmentK p*(p.na+p.nd) ≤ c.width ∧
  (∀ s ∈ c.steps, match s with
    | .query slot ws _ _ => slot=0 ∧ ∃ j < effectiveSegmentK p, ws=effectiveDuplicatedWires p j
    | _ => True) ∧
  (∀ j < effectiveSegmentK p, ∃ cs adj,
    EffectiveStep.query 0 (effectiveDuplicatedWires p j) cs adj ∈ c.steps)

/-- Register sizes, sparsity, precision, and a rational entry bound for a sparse Hamiltonian
oracle description. -/
structure EffectiveSparseParameters where
  ns : ℕ
  nd : ℕ
  np : ℕ
  d : ℕ
  precision : ℕ
  maxEntry : ℚ
  deriving DecidableEq, Repr
/-- Encoded complex value tables and row-dependent location permutations indexed by the time
register. -/
structure EffectiveSparseData (p : EffectiveSparseParameters) where
  values : Reg p.nd → Reg p.ns → Reg p.ns → Reg (2*p.np)
  locations : Reg p.nd → Reg p.ns → Equiv (Reg p.ns) (Reg p.ns)

/-- Decode the real and imaginary value registers into a complex entry, with affine scaling by
the specified maximum entry parameter. -/
noncomputable def effectiveSparseEntry (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) (r : Reg p.nd) (j k : Reg p.ns) : ℂ :=
  let re : Reg p.np := fun i => S.values r j k ⟨i.val,by omega⟩
  let im : Reg p.np := fun i => S.values r j k ⟨p.np+i.val,by omega⟩
  (p.maxEntry : ℂ) *
    (((2*(effectiveRegNat re : ℝ)/(2 : ℝ)^p.np-1 : ℝ) : ℂ) +
      ((2*(effectiveRegNat im : ℝ)/(2 : ℝ)^p.np-1 : ℝ) : ℂ)*Complex.I)
/-- The sparse parameters have the required positive bounds, decoded matrices are bounded and
Hermitian, and all nonzero entries occur among the first `d` listed locations. -/
noncomputable def EffectiveSparseLegal (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) : Prop :=
  0 < p.np ∧ 0 < p.d ∧ p.d ≤ 2^p.ns ∧ 0 < p.maxEntry ∧
  (∀ r j k, ‖effectiveSparseEntry p S r j k‖ ≤ (p.maxEntry : ℝ)) ∧
  (∀ r, (Matrix.of (effectiveSparseEntry p S r)).IsHermitian) ∧
  (∀ r j k, effectiveSparseEntry p S r j k ≠ 0 →
    ∃ x : Reg p.ns, effectiveRegNat x < p.d ∧ S.locations r j x = k)

/-- The sparse value oracle that XORs the encoded matrix entry into the output value register. -/
noncomputable def effectiveSparseOH (p : EffectiveSparseParameters) (S : EffectiveSparseData p) :
    Matrix (Reg (p.nd+2*p.ns+2*p.np)) (Reg (p.nd+2*p.ns+2*p.np)) ℂ :=
  permMatrix fun x =>
    let r : Reg p.nd := fun i => x ⟨i.val,by omega⟩
    let j : Reg p.ns := fun i => x ⟨p.nd+i.val,by omega⟩
    let k : Reg p.ns := fun i => x ⟨p.nd+p.ns+i.val,by omega⟩
    fun i => if h : p.nd+2*p.ns ≤ i.val then
      x i ^^ S.values r j k ⟨i.val-(p.nd+2*p.ns),by omega⟩ else x i
/-- The sparse location oracle that applies the supplied location permutation to the location
register. -/
noncomputable def effectiveSparseOF (p : EffectiveSparseParameters) (S : EffectiveSparseData p) :
    Matrix (Reg (p.nd+2*p.ns)) (Reg (p.nd+2*p.ns)) ℂ :=
  permMatrix fun x =>
    let r : Reg p.nd := fun i => x ⟨i.val,by omega⟩
    let j : Reg p.ns := fun i => x ⟨p.nd+i.val,by omega⟩
    let l : Reg p.ns := fun i => x ⟨p.nd+p.ns+i.val,by omega⟩
    fun i => if h : p.nd+p.ns ≤ i.val then
      S.locations r j l ⟨i.val-(p.nd+p.ns),by omega⟩ else x i
/-- Place the sparse value and location oracles at slots zero and one respectively, using
identity matrices at other slot-width pairs. -/
noncomputable def effectiveSparseEnvironment (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) : EffectiveEnvironment :=
  fun j m => if j=0 then effectiveOneOracle 0 (p.nd+2*p.ns+2*p.np) (effectiveSparseOH p S) j m
    else effectiveOneOracle 1 (p.nd+2*p.ns) (effectiveSparseOF p S) j m
/-- The block diagonal sampled sparse matrix on system and time registers, normalized by `d *
maxEntry`. -/
noncomputable def effectiveSparseBlock (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) : Matrix (Reg (p.ns+p.nd)) (Reg (p.ns+p.nd)) ℂ :=
  fun x y =>
    let tx : Reg p.nd := fun i => x ⟨p.ns+i.val,by omega⟩
    let ty : Reg p.nd := fun i => y ⟨p.ns+i.val,by omega⟩
    if tx=ty then effectiveSparseEntry p S tx
      (fun i => x ⟨i.val,by omega⟩) (fun i => y ⟨i.val,by omega⟩) /
        ((p.d : ℂ)*(p.maxEntry : ℂ)) else 0

/-- Serialize the sparse register sizes, sparsity, precision, and rational entry bound as a
Boolean list. -/
def effectiveSparseInput (p : EffectiveSparseParameters) : List Bool :=
  ([p.ns,p.nd,p.np,p.d,p.precision] ++ effectiveIntFields p.maxEntry.num ++
    [p.maxEntry.den]).flatMap effectiveNatBits

/-- The sparse and segment descriptions have matching system and time widths, matching
normalization, and enough entry precision for the stated budget. -/
def effectiveSparseCompatible (s : EffectiveSparseParameters) (p : EffectiveSegmentParameters) : Prop :=
  s.ns=p.ns ∧ s.nd=p.nd ∧ s.maxEntry*s.d=p.alpha ∧
  p.precision+Nat.clog 2 (effectiveLongR p)+Nat.clog 2 s.d+16 ≤ s.np

/-- The decoded sparse entries approximate the field at dyadic grid times within the specified
entrywise tolerance, and unlisted entries of the field vanish. -/
noncomputable def effectiveSparseApproximates (s : EffectiveSparseParameters)
    (S : EffectiveSparseData s) (p : EffectiveSegmentParameters)
    (H : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) : Prop :=
  ∃ e : s.ns=p.ns,
    let H' : ℝ → Matrix (Reg s.ns) (Reg s.ns) ℂ := e.symm ▸ H
    (∀ r j k, ‖effectiveSparseEntry s S r j k -
      H' ((p.time : ℝ)*effectiveRegNat r/(2 : ℝ)^s.nd) j k‖ ≤
      (s.maxEntry : ℝ)*(1/2 : ℝ)^s.np) ∧
    (∀ r j k, (∀ x : Reg s.ns, effectiveRegNat x < s.d → S.locations r j x ≠ k) →
      H' ((p.time : ℝ)*effectiveRegNat r/(2 : ℝ)^s.nd) j k = 0)

/-- Segment parameters together with a rational norm-bound parameter for the free Hamiltonian. -/
structure EffectiveIPParameters where
  segment : EffectiveSegmentParameters
  alphaA : ℚ
  deriving DecidableEq, Repr
/-- The free-Hamiltonian bound is nonnegative and the long-time domain holds after setting the
mean derivative bound to `2 alphaA alpha`. -/
noncomputable def effectiveIPDomain (p : EffectiveIPParameters) : Prop :=
  0 ≤ p.alphaA ∧ effectiveLongDomain {p.segment with
    meanDerivative := 2*p.alphaA*p.segment.alpha}
/-- The supplied oracle encodes the interaction picture field using the derived local parameters
and mean derivative bound. -/
noncomputable def effectiveIPHAMT (p : EffectiveIPParameters)
    (A B : Matrix (Reg p.segment.ns) (Reg p.segment.ns) ℂ)
    (O : Matrix (Reg (p.segment.ns+p.segment.nd+p.segment.na))
      (Reg (p.segment.ns+p.segment.nd+p.segment.na)) ℂ) : Prop :=
  EffectiveHAMT (effectiveLongLocal {p.segment with
    meanDerivative := 2*p.alphaA*p.segment.alpha})
    (fun u => interactionGenerator A (fun _ => B) u) O

/-- Serialize the segment parameters followed by the rational free-Hamiltonian bound. -/
def effectiveIPInput (p : EffectiveIPParameters) : List Bool :=
  effectiveSegmentInput p.segment ++
    (effectiveIntFields p.alphaA.num ++ [p.alphaA.den]).flatMap effectiveNatBits

/-- The compiler runs in time bounded by a polynomial of degree `D` in the combined input and
output bit lengths, with coefficient `C`. -/
def EffectivePolynomialCompiler {A : Type} (input : A → List Bool)
    (build : A → EffectiveProgram) (C D : ℕ) : Prop :=
  EffectiveCompilerTime input build (fun a =>
    C*(1+(input a).length+(effectiveProgramBits (build a)).length)^D)

/-- The one-qubit Pauli X matrix obtained from the finite X-gate code. -/
noncomputable def effectivePauliX : Matrix (Reg 1) (Reg 1) ℂ := finiteCodeMatrix 1 (.x 0)
/-- The one-qubit diagonal Pauli Z matrix, with entries one on false and minus one on true. -/
noncomputable def effectivePauliZ : Matrix (Reg 1) (Reg 1) ℂ :=
  Matrix.diagonal fun x => if x ⟨0,by omega⟩ then -1 else 1

/-- Sort the sample indices and multiply the sampled Hamiltonians in reverse sorted order,
retaining repeated indices. -/
noncomputable def effectiveSortedWord {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) (v : Fin k → Fin M) : Matrix I I ℂ :=
  ((((List.ofFn v).mergeSort (fun a b => a ≤ b)).reverse).map
    (fun j => H (t*j.val/M))).prod
/-- Sum the sorted Hamiltonian words over all functions from `Fin k` to `Fin M`, including
repeated indices. -/
noncomputable def effectiveCubeRaw {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, effectiveSortedWord H t M k v
/-- Sum the sorted Hamiltonian words over the noninjective sample-index functions. -/
noncomputable def effectiveCollisionRaw {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, if Function.Injective v then 0 else effectiveSortedWord H t M k v
/-- Sum the repeated-index cube contributions through degree `K`, weighted by `(-i t / M)^k /
k!`. -/
noncomputable def effectiveCubeTruncation {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K+1),
    (((-Complex.I*(t/(M : ℝ) : ℂ))^k)/(Nat.factorial k : ℂ)) • effectiveCubeRaw H t M k
/-- Sum the reverse-ordered Hamiltonian products over strictly increasing sample-index
functions. -/
noncomputable def effectiveStrictRaw {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, if StrictMono v then
    ((List.ofFn (fun i : Fin k => H (t*(v i).val/M))).reverse).prod else 0

/-- A tuple of two natural sizes, two rational parameters, and a natural precision parameter for
Taylor compilation. -/
abbrev EffectiveTaylorParameters := ℕ × ℕ × ℚ × ℚ × ℕ
/-- Serialize the natural and rational fields of the Taylor parameter tuple using the effective
bit encoding. -/
def effectiveTaylorInput (z : EffectiveTaylorParameters) : List Bool :=
  ([z.1,z.2.1,z.2.2.2.2] ++ effectiveIntFields z.2.2.1.num ++ [z.2.2.1.den] ++
    effectiveIntFields z.2.2.2.1.num ++ [z.2.2.2.1.den]).flatMap effectiveNatBits

/-- The dyadic duration `tau * 2^j / 2^nd`, with the endpoint `j = nd` represented directly by
`tau`. -/
def effectiveIPDyadicTime (tau : ℚ) (nd j : ℕ) : ℚ :=
  if j=nd then tau else tau*(2 : ℚ)^j/(2 : ℚ)^nd

/-- Bound the program bit length, phase denominators, and phase numerator bit lengths by the
stated polynomial in public size, instruction count, and register width. -/
def EffectiveFiniteDescription (publicSize : ℕ) (p : EffectiveProgram) (C D : ℕ) : Prop :=
  (effectiveProgramBits p).length ≤ C*(1+publicSize+p.steps.length+p.width)^D ∧
  (∀ w a b axis, EffectiveStep.phase w a b axis ∈ p.steps →
    b ≤ C*(1+publicSize+p.steps.length+p.width)^D ∧
    a.natAbs.bits.length ≤ C*(1+publicSize+p.steps.length+p.width)^D)

/-- The encoded program length plus the sum of denominator exponents over all phase
instructions. -/
def effectiveImplementationSize (p : EffectiveProgram) : ℕ :=
  (effectiveProgramBits p).length +
    (p.steps.map fun s => match s with | .phase _ _ b _ => b | _ => 0).sum

end Qatlib.Concepts.InteractionEvo.EffCosts
