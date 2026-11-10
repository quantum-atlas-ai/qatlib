/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.NumericalWord.MixedWordError

open Matrix
open scoped Classical Matrix.Norms.L2Operator

set_option autoImplicit false

noncomputable section

def natBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def gateFields {w : ℕ} : LocalQFTGate w → List ℕ
  | .h a => [0, a.val]
  | .cp a b e neg => [1, a.val, b.val, e, if neg then 1 else 0]
  | .swap a b => [2, a.val, b.val]

def synthInput (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : List Bool :=
  ([w, k] ++ gateFields g).flatMap natBits

def synthInputBits (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : ℕ :=
  (synthInput w g k).length

def synthWordBits (width : ℕ) (letters : List (LocalQFTGate width)) : List Bool :=
  ([width, letters.length] ++ letters.flatMap gateFields).flatMap natBits

def IsFixedPrimitive {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ e _ => e ≤ 3
  | _ => True

def dataBits {n : ℕ} (w : ℕ) (hw : w ≤ n) (z : Reg n) : Reg w :=
  fun i => z ⟨i.val, by omega⟩

def auxBits {width : ℕ} (w : ℕ) (z : Reg width) : Reg (width - w) :=
  fun i => z ⟨w + i.val, by omega⟩

def padClean (w width : ℕ) : Matrix (Reg width) (Reg w) ℂ :=
  fun p t => if p = (fun i : Fin width => if h : i.val < w then t ⟨i.val, h⟩ else false)
    then 1 else 0

noncomputable def operatorError {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) : ℝ := ‖A - B‖

def ApproxUpToPhase {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (tol : ℝ) : Prop :=
  ∃ θ : ℝ, ‖A - (Complex.exp (θ * Complex.I)) • B‖ ≤ tol

def WholeStateUpToPhase {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (tol : ℝ) : Prop :=
  ∀ ψ : QState n, Normalized ψ → ∃ θ : ℝ,
    ‖toEuclidean_fromVec (A *ᵥ ψ - (Complex.exp (θ * Complex.I)) • (B *ᵥ ψ))‖ ≤ tol

def cleanAncillaRestored {width : ℕ} (w : ℕ)
    (M : Matrix (Reg width) (Reg w) ℂ) (tol : ℝ) : Prop :=
  ∀ ψ : QState (Reg w), Normalized ψ →
    ‖toEuclidean_fromVec (fun z : Reg width =>
      if auxBits w z = ZeroStr (width - w) then 0 else (M *ᵥ ψ) z)‖ ≤ tol

structure SynthWord where

  width : ℕ

  letters : List (LocalQFTGate width)

def synthWordLegal (p : SynthWord) : Prop :=
  ∀ g ∈ p.letters, IsFixedPrimitive g

def synthWordGates (p : SynthWord) : ℕ := p.letters.length

def synthWordOracleCalls (_p : SynthWord) : ℕ := 0

def synthesisApprox (w : ℕ) (g : LocalQFTGate w) (p : SynthWord) (tol : ℝ) : Prop :=
  (∃ a : ℕ, p.width = w + a) ∧
  synthWordLegal p ∧
  synthWordOracleCalls p = 0 ∧
  ApproxUpToPhase (localProgramMatrix p.letters * padClean w p.width)
    (padClean w p.width * localGateMatrix g) tol ∧
  cleanAncillaRestored w (localProgramMatrix p.letters * padClean w p.width) tol

def synthesisWordAccepted (w : ℕ) (g : LocalQFTGate w) (k : ℕ) (p : SynthWord) : Prop :=
  synthesisApprox w g p (((2 : ℝ) ⁻¹) ^ k)

structure SynthCompiler where

  anc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ

  emit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) → List (LocalQFTGate (w + anc w g k))

def SynthCompiler.Segment (c : SynthCompiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    SynthWord :=
  ⟨w + c.anc w g k, c.emit w g k⟩

def SynthCompiler.AcceptsAt (c : SynthCompiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    Prop :=
  synthesisWordAccepted w g k (c.Segment w g k)

def UniformSynthLedger (c : SynthCompiler) : Prop :=
  ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
    (c.emit w g k).length ≤ C * (1 + synthInputBits w g k + k) ^ D ∧
    c.anc w g k ≤ C * (1 + synthInputBits w g k + k) ^ D

def gateAngle {w : ℕ} : LocalQFTGate w → Option ℝ
  | .cp _ _ e neg => some (dyadicPhaseAngle e neg)
  | _ => none

def angleInputOK {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) (q : ℚ) : Prop :=
  match gateAngle g with
  | none => True
  | some θ => |((q : ℝ) - θ)| ≤ ((2 : ℝ) ⁻¹) ^ bits ∧ ∃ m : ℤ, q = m / ((2 : ℚ) ^ bits)

structure BitWordMachineModel where

  State : Type

  init : List Bool → State

  step : State → Option State

  emit : State → List Bool

  space : State → ℕ

def BitWordMachineModel.runAt (M : BitWordMachineModel) (input : List Bool) :
    ℕ → Option M.State
  | 0 => some (M.init input)
  | t + 1 => (M.runAt input t).bind M.step

def BitWordMachineModel.HaltsAt (M : BitWordMachineModel) (input : List Bool) (t : ℕ) :
    Prop :=
  ∃ s : M.State, M.runAt input t = some s ∧ M.step s = none

def BitWordMachineModel.emitsAt (M : BitWordMachineModel) (input : List Bool) (t : ℕ)
    (out : List Bool) : Prop :=
  ∃ s : M.State, M.runAt input t = some s ∧ M.step s = none ∧ M.emit s = out

def BitWordMachineModel.PeakSpace (M : BitWordMachineModel) (input : List Bool) (t : ℕ) :
    ℕ :=
  ((List.range (t + 1)).map (fun i => (M.runAt input i).elim 0 M.space)).foldl max 0

structure AccessForm (S : Type) where

  slot : S

  adj : Bool

  controlled : Bool

inductive MixedStep (n w : ℕ) (S : Type) where
  | known : LocalQFTGate n → ℕ → MixedStep n w S
  | call : S → Bool → Option (Fin n × Bool) → MixedStep n w S

def MixedStep.form {n w : ℕ} {S : Type} : MixedStep n w S → Option (AccessForm S)
  | .known _ _ => none
  | .call slot adj ctrl => some ⟨slot, adj, ctrl.isSome⟩

def knownCount {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℕ :=
  W.countP (fun s => match s with | .known _ _ => true | .call _ _ _ => false)

def callCount {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℕ :=
  W.countP (fun s => match s with | .known _ _ => false | .call _ _ _ => true)

def knownGates {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : List (LocalQFTGate n) :=
  W.filterMap (fun s => match s with | .known g _ => some g | .call _ _ _ => none)

def knownPrecs {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : List ℕ :=
  W.filterMap (fun s => match s with | .known _ m => some m | .call _ _ _ => none)

def accessCount {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) (φ : AccessForm S) : ℕ :=
  W.countP (fun s => match s.form with
    | some φ' => if φ' = φ then true else false
    | none => false)

def mixedWordLegal {n w : ℕ} {S : Type} (W : List (MixedStep n w S))
    (paid : List (AccessForm S)) : Prop :=
  ∀ s ∈ W, match s.form with | some φ => φ ∈ paid | none => True

noncomputable def mixedStepMatrix {n w : ℕ} (hw : w ≤ n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) : MixedStep n w S → Matrix (Reg n) (Reg n) ℂ
  | .known g _ => localGateMatrix g
  | .call slot adj ctrl =>
      let Q : Matrix (Reg w) (Reg w) ℂ := if adj then (O slot)ᴴ else O slot
      fun p q =>
        if (∀ i : Fin n, w ≤ i.val → p i = q i) then
          let active := match ctrl with
            | none => true
            | some (c, v) => p c = v
          if active then Q (dataBits w hw p) (dataBits w hw q)
          else if dataBits w hw p = dataBits w hw q then 1 else 0
        else 0

noncomputable def mixedWordMatrix {n w : ℕ} (hw : w ≤ n) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S)) :
    Matrix (Reg n) (Reg n) ℂ :=
  (W.map (mixedStepMatrix hw O)).reverse.prod

def mixedWordGates {n w : ℕ} {S : Type} (W : List (MixedStep n w S)) : ℕ := knownCount W

def liftGateTo {n n' : ℕ} (h : n ≤ n') : LocalQFTGate n → LocalQFTGate n'
  | .h a => .h ⟨a.val, by omega⟩
  | .cp a c e neg => .cp ⟨a.val, by omega⟩ ⟨c.val, by omega⟩ e neg
  | .swap a c => .swap ⟨a.val, by omega⟩ ⟨c.val, by omega⟩

def liftWordTo {n n' : ℕ} (h : n ≤ n') (gs : List (LocalQFTGate n)) :
    List (LocalQFTGate n') :=
  gs.map (liftGateTo h)

def compileWord {n w A : ℕ} {S : Type}
    (W : List (MixedStep n w S)) (segs : List (List (LocalQFTGate (n + A)))) :
    List (MixedStep (n + A) w S) :=
  match W with
  | [] => []
  | .known _ _ :: rest =>
      (match segs with
       | s :: segs' => s.map (fun h => .known h 0) ++ compileWord rest segs'
       | [] => compileWord rest [])
  | .call slot adj ctrl :: rest =>
      .call slot adj (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2))) ::
        compileWord rest segs

def AlignedWith {n w A : ℕ} {S : Type} (W : List (MixedStep n w S))
    (segs : List (List (LocalQFTGate (n + A)))) (ks : List ℕ) : Prop :=
  segs.length = knownCount W ∧ ks.length = knownCount W

structure WordCompilation {n w : ℕ} {S : Type} (c : SynthCompiler)
    (W : List (MixedStep n w S)) where

  A : ℕ

  ks : List ℕ

  hlen : ks.length = knownCount W

  hanc : ∀ g k, (g, k) ∈ List.zip (knownGates W) ks → c.anc n g k ≤ A

def SegmentsFrom {n w A : ℕ} {S : Type} (c : SynthCompiler) (W : List (MixedStep n w S))
    (segs : List (List (LocalQFTGate (n + A)))) (ks : List ℕ) : Prop :=
  List.Forall₂ (fun (g : LocalQFTGate n) (sk : List (LocalQFTGate (n + A)) × ℕ) =>
    ∃ h : c.anc n g sk.2 ≤ A,
      sk.1 = (c.emit n g sk.2).map (liftGateTo (Nat.add_le_add_left h n)))
  (knownGates W) (List.zip segs ks)

def BudgetLE {n w : ℕ} {S : Type} {c : SynthCompiler} {W : List (MixedStep n w S)}
    (cmp : WordCompilation c W) (ε : ℝ) : Prop :=
  ((List.zip (knownPrecs W) cmp.ks).map (fun mk =>
    ((2 : ℝ) ⁻¹) ^ mk.1 + ((2 : ℝ) ⁻¹) ^ mk.2)).sum ≤ ε

def AccessPreserved {n w A : ℕ} {S : Type} (W : List (MixedStep n w S))
    (W' : List (MixedStep (n + A) w S)) : Prop :=
  ∀ φ : AccessForm S, accessCount W' φ = accessCount W φ

def CompiledOperatorErrorLE {n w A : ℕ} (hw : w ≤ n) (hwA : w ≤ n + A) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (W' : List (MixedStep (n + A) w S)) (ε : ℝ) : Prop :=
  ApproxUpToPhase (mixedWordMatrix hwA O W' * padClean n (n + A))
    (padClean n (n + A) * mixedWordMatrix hw O W) ε

def CompiledWholeStateErrorLE {n w A : ℕ} (hw : w ≤ n) (hwA : w ≤ n + A) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W : List (MixedStep n w S))
    (W' : List (MixedStep (n + A) w S)) (ε : ℝ) : Prop :=
  ∀ ψ : QState (Reg n), Normalized ψ → ∃ θ : ℝ,
    ‖toEuclidean_fromVec ((mixedWordMatrix hwA O W' * padClean n (n + A)) *ᵥ ψ -
      (Complex.exp (θ * Complex.I)) • ((padClean n (n + A) * mixedWordMatrix hw O W) *ᵥ ψ))‖
      ≤ ε

def CompiledCleanPoolLE {n w A : ℕ} (hwA : w ≤ n + A) {S : Type}
    (O : S → Matrix (Reg w) (Reg w) ℂ) (W' : List (MixedStep (n + A) w S)) (ε : ℝ) : Prop :=
  cleanAncillaRestored n (mixedWordMatrix hwA O W' * padClean n (n + A)) ε

def CompileLedgersOK (sizes : List ℕ) (gateCount bitTime peakSpace : ℕ) (C D : ℕ) : Prop :=
  gateCount ≤ (sizes.map (fun s => C * (1 + s) ^ D)).sum ∧
  bitTime ≤ (sizes.map (fun s => C * (1 + s) ^ D)).sum ∧
  peakSpace ≤ (sizes.map (fun s => C * (1 + s) ^ D)).foldl max 0

def segmentSize {n : ℕ} (g : LocalQFTGate n) (k : ℕ) : ℕ :=
  synthInputBits n g k + k

end

end Qatlib.Concepts.NumericalWord.MixedWordError
