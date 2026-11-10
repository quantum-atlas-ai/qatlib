/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Basic
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordEmitterDefs
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum (LocalQFTGate localGateMatrix localProgramMatrix localGateAdjoint
  localProgramAdjoint dyadicPhaseAngle)
open Qatlib.Foundations.PureStateMath (Reg QState Normalized ZeroStr)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open scoped Matrix.Norms.L2Operator
open scoped Classical

def opcodeOf {w : ℕ} : LocalQFTGate w → Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Opcode
  | .h a => .hadamard a.val
  | .cp a c e neg => .phase a.val c.val e neg
  | .swap a c => .swap a.val c.val

def gateFields {w : ℕ} (g : LocalQFTGate w) : List ℕ :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields (opcodeOf g)

def synthInput (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : List Bool :=
  ([w, k] ++ gateFields g).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits

def synthInputBits (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : ℕ :=
  (synthInput w g k).length

def requestSize (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : ℕ :=
  1 + synthInputBits w g k + k

def IsFixedPrim {w : ℕ} : LocalQFTGate w → Prop
  | .cp _ _ e _ => e ≤ 3
  | _ => True

instance {w : ℕ} (g : LocalQFTGate w) : Decidable (IsFixedPrim g) := by
  cases g with
  | h a => exact isTrue trivial
  | swap a c => exact isTrue trivial
  | cp a c e neg => exact inferInstanceAs (Decidable (e ≤ 3))

def isFixedPrim {w : ℕ} (g : LocalQFTGate w) : Bool := decide (IsFixedPrim g)

theorem isFixedPrim_eq_true_iff {w : ℕ} (g : LocalQFTGate w) :
    isFixedPrim g = true ↔ IsFixedPrim g :=
  decide_eq_true_iff

def dataBits {n : ℕ} (w : ℕ) (hw : w ≤ n) (z : Reg n) : Reg w :=
  fun i => z ⟨i.val, by omega⟩

def auxBits {width : ℕ} (w : ℕ) (z : Reg width) : Reg (width - w) :=
  fun i => z ⟨w + i.val, by omega⟩

def cleanEmbed (w width : ℕ) : Matrix (Reg width) (Reg w) ℂ :=
  fun p t => if p = (fun i : Fin width => if h : i.val < w then t ⟨i.val, h⟩ else false)
    then 1 else 0

noncomputable def opError {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) : ℝ :=
  ‖A - B‖

def approxUpToPhase {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (tol : ℝ) : Prop :=
  ∃ θ : ℝ, ‖A - (Complex.exp (θ * Complex.I)) • B‖ ≤ tol

noncomputable def tolerance (k : ℕ) : ℝ := ((2 : ℝ) ⁻¹) ^ k

def ancillaRestored {width : ℕ} (w : ℕ) (M : Matrix (Reg width) (Reg w) ℂ) (tol : ℝ) :
    Prop :=
  ∀ ψ : QState (Reg w), Normalized ψ →
    ‖toEuclidean_fromVec (fun z : Reg width =>
      if auxBits w z = ZeroStr (width - w) then 0 else (M *ᵥ ψ) z)‖ ≤ tol

structure SynthAnswer where

  width : ℕ

  word : List (LocalQFTGate width)

def answerOracleCalls (_ans : SynthAnswer) : ℕ := 0

def answerBits (ans : SynthAnswer) : List Bool :=
  Qatlib.Concepts.BitWordCompiler.CanonicalCodec.wordBits ⟨ans.width, ans.word.map opcodeOf⟩

def Accepts (w : ℕ) (g : LocalQFTGate w) (k : ℕ) (ans : SynthAnswer) : Prop :=
  (∃ a : ℕ, ans.width = w + a) ∧
  (∀ h ∈ ans.word, IsFixedPrim h) ∧
  answerOracleCalls ans = 0 ∧
  approxUpToPhase (localProgramMatrix ans.word * cleanEmbed w ans.width)
    (cleanEmbed w ans.width * localGateMatrix g) (tolerance k) ∧
  ancillaRestored w (localProgramMatrix ans.word * cleanEmbed w ans.width) (tolerance k)

structure Compiler where

  anc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ

  emit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) → List (LocalQFTGate (w + anc w g k))

def Compiler.Segment (c : Compiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : SynthAnswer :=
  ⟨w + c.anc w g k, c.emit w g k⟩

def AcceptsAt (c : Compiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) : Prop :=
  Accepts w g k (c.Segment w g k)

def UniformLedger (c : Compiler) : Prop :=
  ∃ C D : ℕ, ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
    (c.emit w g k).length ≤ C * (requestSize w g k) ^ D ∧
    c.anc w g k ≤ C * (requestSize w g k) ^ D

def angleInputOK {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) (q : ℚ) : Prop :=
  match g with
  | .cp _ _ e neg =>
      |((q : ℝ) - dyadicPhaseAngle e neg)| ≤ tolerance bits ∧
        ∃ m : ℤ, q = m / ((2 : ℚ) ^ bits)
  | _ => True

def fieldsPlan (fs : List ℕ) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Plan :=
  fs.foldr (fun j acc => .append (.emitNat (.literal j)) acc) (.literal [])

def answerPlan (ans : SynthAnswer) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Plan :=
  let ops := ans.word.map opcodeOf
  .append (.emitNat (.literal ans.width))
    (.append (.emitNat (.literal ops.length))
      (fieldsPlan (ops.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields)))

structure CallForm (S : Type) where

  slot : S

  adj : Bool

  ctrl : Bool

inductive PaidStep (n : ℕ) (S : Type) where
  | known (g : LocalQFTGate n)
  | call (φ : CallForm S)

def PaidStep.form {n : ℕ} {S : Type} : PaidStep n S → Option (CallForm S)
  | .known _ => none
  | .call φ => some φ

def paidLegal {n : ℕ} {S : Type} (W : List (PaidStep n S)) (paid : List (CallForm S)) :
    Prop :=
  ∀ s ∈ W, match s.form with | some φ => φ ∈ paid | none => True

def callCount {n : ℕ} {S : Type} : List (PaidStep n S) → ℕ
  | [] => 0
  | .call _ :: rest => callCount rest + 1
  | .known _ :: rest => callCount rest

def formCount {n : ℕ} {S : Type} (φ : CallForm S) : List (PaidStep n S) → ℕ
  | [] => 0
  | .call ψ :: rest => formCount φ rest + if ψ = φ then 1 else 0
  | .known _ :: rest => formCount φ rest

def knownGates {n : ℕ} {S : Type} : List (PaidStep n S) → List (LocalQFTGate n)
  | [] => []
  | .known g :: rest => g :: knownGates rest
  | .call _ :: rest => knownGates rest

noncomputable def stepMatrix {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ) :
    PaidStep n S → Matrix (Reg n) (Reg n) ℂ
  | .known g => localGateMatrix g
  | .call φ => O φ

noncomputable def wordMatrix {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ) :
    List (PaidStep n S) → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | s :: rest => wordMatrix O rest * stepMatrix O s

def compileWord {n m : ℕ} {S : Type} (f : LocalQFTGate n → List (LocalQFTGate m)) :
    List (PaidStep n S) → List (PaidStep m S)
  | [] => []
  | .known g :: rest => (f g).map PaidStep.known ++ compileWord f rest
  | .call φ :: rest => .call φ :: compileWord f rest

noncomputable def uniformBudget (ε : ℝ) (count : ℕ) : ℝ := ε / ((count : ℝ) + 1)

def Clause1Claim : Prop :=
  ∃ c : Compiler, UniformLedger c ∧
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k → AcceptsAt c w g k

def Clause2Claim : Prop :=
  ∃ (c : Compiler) (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
      (C D : ℕ) (angleInput : (w : ℕ) → LocalQFTGate w → ℕ → ℚ),
    UniformLedger c ∧
    (∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k → AcceptsAt c w g k) ∧
    (∀ (w : ℕ) (g : LocalQFTGate w) (bits : ℕ), angleInputOK g bits (angleInput w g bits)) ∧
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      let ans := c.Segment w g k
      let p := answerPlan ans
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] p = answerBits ans ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput p [] k) (answerBits ans)
        (C * requestSize w g k ^ D) (C * requestSize w g k ^ D)

def Clause3Claim : Prop :=
  ∀ (n : ℕ) (S : Type) (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (paid : List (CallForm S)) (W : List (PaidStep n S)) (L : ℕ) (ε : ℝ),
    (∀ φ, O φ ∈ Matrix.unitaryGroup (Reg n) ℂ) →
    paidLegal W paid → callCount W = L → 0 < ε →
    ∃ (A : ℕ) (f : LocalQFTGate n → List (LocalQFTGate (n + A))) (ks : List ℕ)
      (O' : CallForm S → Matrix (Reg (n + A)) (Reg (n + A)) ℂ)
      (bitTime peakSpace C D : ℕ),
      ks.length = (knownGates W).length ∧
      (∀ φ, O' φ ∈ Matrix.unitaryGroup (Reg (n + A)) ℂ) ∧
      (∀ φ, approxUpToPhase (O' φ * cleanEmbed n (n + A))
        (cleanEmbed n (n + A) * O φ) 0) ∧
      List.Forall₂ (fun (g : LocalQFTGate n) (k : ℕ) => Accepts n g k ⟨n + A, f g⟩)
        (knownGates W) ks ∧
      (ks.map tolerance).sum ≤ ε ∧
      approxUpToPhase
        (wordMatrix O' (compileWord f W) * cleanEmbed n (n + A))
        (cleanEmbed n (n + A) * wordMatrix O W) ε ∧
      (∀ φ : CallForm S, formCount φ (compileWord f W) = formCount φ W) ∧
      callCount (compileWord f W) = L ∧
      paidLegal (compileWord f W) paid ∧
      (compileWord f W).length ≤ L +
        (((knownGates W).zip ks).map
          (fun gk => C * (1 + requestSize n gk.1 gk.2) ^ D)).sum ∧
      bitTime ≤ (((knownGates W).zip ks).map
          (fun gk => C * (1 + requestSize n gk.1 gk.2) ^ D)).sum ∧
      peakSpace ≤ (((knownGates W).zip ks).map
          (fun gk => C * (1 + requestSize n gk.1 gk.2) ^ D)).foldl max 0

end Qatlib.Concepts.MatrixAccess.RitzPipeline
