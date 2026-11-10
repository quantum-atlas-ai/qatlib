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
set_option warningAsError false
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

inductive EffectiveStep where
  | fixed : FiniteGateCode → EffectiveStep
  | phase : ℕ → ℤ → ℕ → Bool → EffectiveStep
  | query : ℕ → List ℕ → List (ℕ × Bool) → Bool → EffectiveStep
  | postselect : List ℕ → EffectiveStep
  deriving DecidableEq, Repr

structure EffectiveProgram where
  width : ℕ
  steps : List EffectiveStep
  deriving DecidableEq, Repr

abbrev EffectiveEnvironment := (slot m : ℕ) → Matrix (Reg m) (Reg m) ℂ

noncomputable def selectedQuery (n : ℕ) (ws : List ℕ) (cs : List (ℕ × Bool))
    (U : Matrix (Reg ws.length) (Reg ws.length) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  fun x y =>
    if hc : ∀ c ∈ cs, ∃ h : c.1 < n, y ⟨c.1,h⟩ = c.2 then
      if ∀ i : Fin n, i.val ∉ ws → x i = y i then
        U (fun i => if h : ws[i] < n then x ⟨ws[i],h⟩ else false)
          (fun i => if h : ws[i] < n then y ⟨ws[i],h⟩ else false)
      else 0
    else if x = y then 1 else 0

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

noncomputable def effectiveMatrix (p : EffectiveProgram) (E : EffectiveEnvironment) :
    Matrix (Reg p.width) (Reg p.width) ℂ :=
  (p.steps.map (effectiveStepMatrix p.width E)).reverse.prod

def effectiveStepLegal (n : ℕ) : EffectiveStep → Prop
  | .fixed g => finiteCodeLegal n g = true
  | .phase w _ _ _ => w < n
  | .query _ ws cs _ => ws.Nodup ∧ (∀ w ∈ ws, w < n) ∧
      (cs.map Prod.fst).Nodup ∧ (∀ c ∈ cs, c.1 < n ∧ c.1 ∉ ws)
  | .postselect ws => ws.Nodup ∧ (∀ w ∈ ws, w < n)

def effectiveLegal (p : EffectiveProgram) : Prop :=
  ∀ s ∈ p.steps, effectiveStepLegal p.width s

def effectiveQueries (p : EffectiveProgram) : ℕ :=
  (p.steps.filter fun s => match s with | .query .. => true | _ => false).length

def effectiveSlotQueries (p : EffectiveProgram) (j : ℕ) : ℕ :=
  (p.steps.filter fun s => match s with | .query slot _ _ _ => slot == j | _ => false).length

def effectiveGates (p : EffectiveProgram) : ℕ :=
  (p.steps.filter fun s => match s with | .fixed .. | .phase .. => true | _ => false).length

def effectivePostselects (p : EffectiveProgram) : ℕ :=
  (p.steps.filter fun s => match s with | .postselect .. => true | _ => false).length

def effectiveMeasurements (ns : ℕ) (p : EffectiveProgram) : ℕ :=
  p.width-ns + (p.steps.map fun s => match s with | .postselect ws => ws.length | _ => 0).sum

def effectiveCoherent (p : EffectiveProgram) : Prop :=
  ∀ ws : List ℕ, EffectiveStep.postselect ws ∉ p.steps

def EffectivePhysical (p : EffectiveProgram) (E : EffectiveEnvironment) : Prop :=
  effectiveLegal p ∧ ∀ slot ws cs adj, EffectiveStep.query slot ws cs adj ∈ p.steps →
    E slot ws.length ∈ Matrix.unitaryGroup (Reg ws.length) ℂ

noncomputable def effectiveFrame (ns n : ℕ) : Matrix (Reg n) (Reg ns) ℂ :=
  fun x y => if (∀ i : Fin ns, ∃ h : i.val < n, x ⟨i.val,h⟩ = y i) ∧
    (∀ i : Fin n, ns ≤ i.val → x i = false) then 1 else 0

noncomputable def effectiveCorner (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment) :
    Matrix (Reg ns) (Reg ns) ℂ :=
  (effectiveFrame ns p.width)ᴴ * effectiveMatrix p E * effectiveFrame ns p.width

noncomputable def effectiveSuccess (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment)
    (ψ : QState (Reg ns)) : QState (Reg ns) := effectiveCorner ns p E *ᵥ ψ

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

noncomputable def effectiveFailure (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment)
    (ψ : QState (Reg ns)) : ℝ :=
  let result := effectiveStoppedRun p.width E p.steps (effectiveFrame ns p.width *ᵥ ψ)
  result.2 + ‖toEuclidean_fromVec result.1‖^2 -
    ‖toEuclidean_fromVec ((effectiveFrame ns p.width)ᴴ *ᵥ result.1)‖^2

def EffectiveCleanProgram (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment) : Prop :=
  ns ≤ p.width ∧ effectiveCoherent p ∧ ∀ ψ : QState (Reg ns),
    effectiveMatrix p E *ᵥ (effectiveFrame ns p.width *ᵥ ψ) =
      effectiveFrame ns p.width *ᵥ (effectiveCorner ns p E *ᵥ ψ)

def EffectiveGuarantee (ns : ℕ) (p : EffectiveProgram) (E : EffectiveEnvironment)
    (U : Matrix (Reg ns) (Reg ns) ℂ) (ε : ℝ) : Prop :=
  ns ≤ p.width ∧ EffectivePhysical p E ∧
  ‖effectiveCorner ns p E - U‖ ≤ ε ∧
  (∀ ψ : QState (Reg ns), Normalized ψ →
    0 ≤ effectiveFailure ns p E ψ ∧ effectiveFailure ns p E ψ ≤ 2*ε) ∧
  (∀ ψ : QState (Reg ns),
    ‖toEuclidean_fromVec (effectiveSuccess ns p E ψ - U *ᵥ ψ)‖ ≤ ε * ‖toEuclidean_fromVec ψ‖)

def effectiveNatBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def effectiveIntFields (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]
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
def effectiveProgramBits (p : EffectiveProgram) : List Bool :=
  ([p.width,p.steps.length] ++ p.steps.flatMap effectiveStepFields).flatMap effectiveNatBits

def EffectiveCompilerTime {A : Type} (input : A → List Bool) (build : A → EffectiveProgram)
    (budget : A → ℕ) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))),
    ∀ a : A, ∃ (s : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (q+1))),
      s ≤ budget a ∧ BitMachineAfter M ((input a).map some) s = some cfg ∧
      Turing.TM0.step M cfg = none ∧
      (∀ i : ℕ, cfg.Tape.right₀.nth i = ((effectiveProgramBits (build a)).map some).getD i none)

def effectiveRegNat {n : ℕ} (x : Reg n) : ℕ := ∑ i : Fin n, if x i then 2^i.val else 0

structure EffectiveSegmentParameters where
  ns : ℕ
  na : ℕ
  nd : ℕ
  precision : ℕ
  time : ℚ
  alpha : ℚ
  meanDerivative : ℚ
  deriving DecidableEq, Repr

def effectiveSegmentK (p : EffectiveSegmentParameters) : ℕ := computedDysonCutoff (p.precision+8)
def effectiveSegmentM (p : EffectiveSegmentParameters) : ℕ := 2^p.nd
noncomputable def effectiveSegmentDomain (p : EffectiveSegmentParameters) : Prop :=
  0 ≤ p.time ∧ 0 < p.alpha ∧ 0 ≤ p.meanDerivative ∧
  (p.alpha : ℝ)*(p.time : ℝ) ≤ 1/2 ∧
  computedDysonGridSize p.time p.alpha p.meanDerivative (p.precision+8) ≤ effectiveSegmentM p

def effectiveSegmentInput (p : EffectiveSegmentParameters) : List Bool :=
  ([p.ns,p.na,p.nd,p.precision] ++ effectiveIntFields p.time.num ++ [p.time.den] ++
    effectiveIntFields p.alpha.num ++ [p.alpha.den] ++
    effectiveIntFields p.meanDerivative.num ++ [p.meanDerivative.den]).flatMap effectiveNatBits

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

noncomputable def EffectiveHAMT (p : EffectiveSegmentParameters)
    (H : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (O : Matrix (Reg (p.ns+p.nd+p.na)) (Reg (p.ns+p.nd+p.na)) ℂ) : Prop :=
  O ∈ Matrix.unitaryGroup (Reg (p.ns+p.nd+p.na)) ℂ ∧
  (effectiveFrame (p.ns+p.nd) (p.ns+p.nd+p.na))ᴴ * O *
    effectiveFrame (p.ns+p.nd) (p.ns+p.nd+p.na) = effectiveGridBlock p H

noncomputable def effectiveOneOracle (slot width : ℕ)
    (O : Matrix (Reg width) (Reg width) ℂ) : EffectiveEnvironment :=
  fun j m => if h : j=slot ∧ m=width then h.2.symm ▸ O else 1

noncomputable def EffectiveField (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) : Prop :=
  Continuous H ∧ IntervalIntegrable (fun u => ‖Hd u‖) MeasureTheory.volume 0 (p.time : ℝ) ∧
  (∀ u ∈ Set.Icc 0 (p.time : ℝ), HasDerivAt H (Hd u) u) ∧
  (∀ u ∈ Set.Icc 0 (p.time : ℝ), (H u).IsHermitian ∧ ‖H u‖ ≤ (p.alpha : ℝ)) ∧
  (∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖) ≤ (p.meanDerivative : ℝ)*(p.time : ℝ)

noncomputable def effectiveTriangle (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => if j < i then (1/(M : ℂ)) else 0

noncomputable def effectiveStrictDegree {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ((-Complex.I * (t/(M : ℝ) : ℂ))^k) •
    ∑ v : Fin k → Fin M, if StrictMono v then
      ((List.ofFn (fun i : Fin k => H (t*(v i).val/M))).reverse).prod else 0

def effectiveLongR (p : EffectiveSegmentParameters) : ℕ := max 1 ⌈2*p.alpha*abs p.time⌉₊
def effectiveLongLocal (p : EffectiveSegmentParameters) : EffectiveSegmentParameters :=
  { p with
    time := abs p.time / (effectiveLongR p : ℚ)
    precision := p.precision + Nat.clog 2 (effectiveLongR p) + 8
    meanDerivative := p.meanDerivative * (effectiveLongR p : ℚ) }
noncomputable def effectiveLongDomain (p : EffectiveSegmentParameters) : Prop :=
  0 < p.alpha ∧ 0 ≤ p.meanDerivative ∧ effectiveSegmentDomain (effectiveLongLocal p)
noncomputable def effectiveLongField (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) : Prop :=
  Continuous H ∧ IntervalIntegrable (fun u => ‖Hd u‖) MeasureTheory.volume 0 (p.time : ℝ) ∧
  (∀ u ∈ Set.uIcc 0 (p.time : ℝ), HasDerivAt H (Hd u) u) ∧
  (∀ u ∈ Set.uIcc 0 (p.time : ℝ), (H u).IsHermitian ∧ ‖H u‖ ≤ (p.alpha : ℝ)) ∧
  |∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖| ≤ (p.meanDerivative : ℝ)*|(p.time : ℝ)|
noncomputable def effectiveSignedSegment (p : EffectiveSegmentParameters)
    (H : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ) (j : ℕ) :
    ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ :=
  fun u => if p.time < 0 then -H (-((j : ℝ)*(effectiveLongLocal p).time+u))
    else H ((j : ℝ)*(effectiveLongLocal p).time+u)

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

def effectiveDuplicatedWires (p : EffectiveSegmentParameters) (j : ℕ) : List ℕ :=
  List.range p.ns ++ List.range' (p.ns+j*(p.na+p.nd)) (p.na+p.nd)
def EffectiveDuplicatedLayout (p : EffectiveSegmentParameters) (c : EffectiveProgram) : Prop :=
  p.ns+effectiveSegmentK p*(p.na+p.nd) ≤ c.width ∧
  (∀ s ∈ c.steps, match s with
    | .query slot ws _ _ => slot=0 ∧ ∃ j < effectiveSegmentK p, ws=effectiveDuplicatedWires p j
    | _ => True) ∧
  (∀ j < effectiveSegmentK p, ∃ cs adj,
    EffectiveStep.query 0 (effectiveDuplicatedWires p j) cs adj ∈ c.steps)

structure EffectiveSparseParameters where
  ns : ℕ
  nd : ℕ
  np : ℕ
  d : ℕ
  precision : ℕ
  maxEntry : ℚ
  deriving DecidableEq, Repr
structure EffectiveSparseData (p : EffectiveSparseParameters) where
  values : Reg p.nd → Reg p.ns → Reg p.ns → Reg (2*p.np)
  locations : Reg p.nd → Reg p.ns → Equiv (Reg p.ns) (Reg p.ns)

noncomputable def effectiveSparseEntry (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) (r : Reg p.nd) (j k : Reg p.ns) : ℂ :=
  let re : Reg p.np := fun i => S.values r j k ⟨i.val,by omega⟩
  let im : Reg p.np := fun i => S.values r j k ⟨p.np+i.val,by omega⟩
  (p.maxEntry : ℂ) *
    (((2*(effectiveRegNat re : ℝ)/(2 : ℝ)^p.np-1 : ℝ) : ℂ) +
      ((2*(effectiveRegNat im : ℝ)/(2 : ℝ)^p.np-1 : ℝ) : ℂ)*Complex.I)
noncomputable def EffectiveSparseLegal (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) : Prop :=
  0 < p.np ∧ 0 < p.d ∧ p.d ≤ 2^p.ns ∧ 0 < p.maxEntry ∧
  (∀ r j k, ‖effectiveSparseEntry p S r j k‖ ≤ (p.maxEntry : ℝ)) ∧
  (∀ r, (Matrix.of (effectiveSparseEntry p S r)).IsHermitian) ∧
  (∀ r j k, effectiveSparseEntry p S r j k ≠ 0 →
    ∃ x : Reg p.ns, effectiveRegNat x < p.d ∧ S.locations r j x = k)

noncomputable def effectiveSparseOH (p : EffectiveSparseParameters) (S : EffectiveSparseData p) :
    Matrix (Reg (p.nd+2*p.ns+2*p.np)) (Reg (p.nd+2*p.ns+2*p.np)) ℂ :=
  permMatrix fun x =>
    let r : Reg p.nd := fun i => x ⟨i.val,by omega⟩
    let j : Reg p.ns := fun i => x ⟨p.nd+i.val,by omega⟩
    let k : Reg p.ns := fun i => x ⟨p.nd+p.ns+i.val,by omega⟩
    fun i => if h : p.nd+2*p.ns ≤ i.val then
      x i ^^ S.values r j k ⟨i.val-(p.nd+2*p.ns),by omega⟩ else x i
noncomputable def effectiveSparseOF (p : EffectiveSparseParameters) (S : EffectiveSparseData p) :
    Matrix (Reg (p.nd+2*p.ns)) (Reg (p.nd+2*p.ns)) ℂ :=
  permMatrix fun x =>
    let r : Reg p.nd := fun i => x ⟨i.val,by omega⟩
    let j : Reg p.ns := fun i => x ⟨p.nd+i.val,by omega⟩
    let l : Reg p.ns := fun i => x ⟨p.nd+p.ns+i.val,by omega⟩
    fun i => if h : p.nd+p.ns ≤ i.val then
      S.locations r j l ⟨i.val-(p.nd+p.ns),by omega⟩ else x i
noncomputable def effectiveSparseEnvironment (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) : EffectiveEnvironment :=
  fun j m => if j=0 then effectiveOneOracle 0 (p.nd+2*p.ns+2*p.np) (effectiveSparseOH p S) j m
    else effectiveOneOracle 1 (p.nd+2*p.ns) (effectiveSparseOF p S) j m
noncomputable def effectiveSparseBlock (p : EffectiveSparseParameters)
    (S : EffectiveSparseData p) : Matrix (Reg (p.ns+p.nd)) (Reg (p.ns+p.nd)) ℂ :=
  fun x y =>
    let tx : Reg p.nd := fun i => x ⟨p.ns+i.val,by omega⟩
    let ty : Reg p.nd := fun i => y ⟨p.ns+i.val,by omega⟩
    if tx=ty then effectiveSparseEntry p S tx
      (fun i => x ⟨i.val,by omega⟩) (fun i => y ⟨i.val,by omega⟩) /
        ((p.d : ℂ)*(p.maxEntry : ℂ)) else 0

def effectiveSparseInput (p : EffectiveSparseParameters) : List Bool :=
  ([p.ns,p.nd,p.np,p.d,p.precision] ++ effectiveIntFields p.maxEntry.num ++
    [p.maxEntry.den]).flatMap effectiveNatBits

def effectiveSparseCompatible (s : EffectiveSparseParameters) (p : EffectiveSegmentParameters) : Prop :=
  s.ns=p.ns ∧ s.nd=p.nd ∧ s.maxEntry*s.d=p.alpha ∧
  p.precision+Nat.clog 2 (effectiveLongR p)+Nat.clog 2 s.d+16 ≤ s.np

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

structure EffectiveIPParameters where
  segment : EffectiveSegmentParameters
  alphaA : ℚ
  deriving DecidableEq, Repr
noncomputable def effectiveIPDomain (p : EffectiveIPParameters) : Prop :=
  0 ≤ p.alphaA ∧ effectiveLongDomain {p.segment with
    meanDerivative := 2*p.alphaA*p.segment.alpha}
noncomputable def effectiveIPHAMT (p : EffectiveIPParameters)
    (A B : Matrix (Reg p.segment.ns) (Reg p.segment.ns) ℂ)
    (O : Matrix (Reg (p.segment.ns+p.segment.nd+p.segment.na))
      (Reg (p.segment.ns+p.segment.nd+p.segment.na)) ℂ) : Prop :=
  EffectiveHAMT (effectiveLongLocal {p.segment with
    meanDerivative := 2*p.alphaA*p.segment.alpha})
    (fun u => interactionGenerator A (fun _ => B) u) O

def effectiveIPInput (p : EffectiveIPParameters) : List Bool :=
  effectiveSegmentInput p.segment ++
    (effectiveIntFields p.alphaA.num ++ [p.alphaA.den]).flatMap effectiveNatBits

def EffectivePolynomialCompiler {A : Type} (input : A → List Bool)
    (build : A → EffectiveProgram) (C D : ℕ) : Prop :=
  EffectiveCompilerTime input build (fun a =>
    C*(1+(input a).length+(effectiveProgramBits (build a)).length)^D)

noncomputable def effectivePauliX : Matrix (Reg 1) (Reg 1) ℂ := finiteCodeMatrix 1 (.x 0)
noncomputable def effectivePauliZ : Matrix (Reg 1) (Reg 1) ℂ :=
  Matrix.diagonal fun x => if x ⟨0,by omega⟩ then -1 else 1

noncomputable def effectiveSortedWord {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) (v : Fin k → Fin M) : Matrix I I ℂ :=
  ((((List.ofFn v).mergeSort (fun a b => a ≤ b)).reverse).map
    (fun j => H (t*j.val/M))).prod
noncomputable def effectiveCubeRaw {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, effectiveSortedWord H t M k v
noncomputable def effectiveCollisionRaw {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, if Function.Injective v then 0 else effectiveSortedWord H t M k v
noncomputable def effectiveCubeTruncation {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K+1),
    (((-Complex.I*(t/(M : ℝ) : ℂ))^k)/(Nat.factorial k : ℂ)) • effectiveCubeRaw H t M k
noncomputable def effectiveStrictRaw {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) : Matrix I I ℂ :=
  ∑ v : Fin k → Fin M, if StrictMono v then
    ((List.ofFn (fun i : Fin k => H (t*(v i).val/M))).reverse).prod else 0

abbrev EffectiveTaylorParameters := ℕ × ℕ × ℚ × ℚ × ℕ
def effectiveTaylorInput (z : EffectiveTaylorParameters) : List Bool :=
  ([z.1,z.2.1,z.2.2.2.2] ++ effectiveIntFields z.2.2.1.num ++ [z.2.2.1.den] ++
    effectiveIntFields z.2.2.2.1.num ++ [z.2.2.2.1.den]).flatMap effectiveNatBits

def effectiveIPDyadicTime (tau : ℚ) (nd j : ℕ) : ℚ :=
  if j=nd then tau else tau*(2 : ℚ)^j/(2 : ℚ)^nd

def EffectiveFiniteDescription (publicSize : ℕ) (p : EffectiveProgram) (C D : ℕ) : Prop :=
  (effectiveProgramBits p).length ≤ C*(1+publicSize+p.steps.length+p.width)^D ∧
  (∀ w a b axis, EffectiveStep.phase w a b axis ∈ p.steps →
    b ≤ C*(1+publicSize+p.steps.length+p.width)^D ∧
    a.natAbs.bits.length ≤ C*(1+publicSize+p.steps.length+p.width)^D)

def effectiveImplementationSize (p : EffectiveProgram) : ℕ :=
  (effectiveProgramBits p).length +
    (p.steps.map fun s => match s with | .phase _ _ b _ => b | _ => 0).sum

end Qatlib.Concepts.InteractionEvo.EffCosts
