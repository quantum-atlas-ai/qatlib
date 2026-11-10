/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutatorConsumers
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.RandCompile.ReferenceModel.LocalPauliEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.FiniteStrang
open Qatlib.Concepts.RandCompile.ReferenceModel

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix

structure StrangAccessSynthesis (n : ℕ) where
  word : List (LocalQFTGate n)
  controlledWord : List (LocalQFTGate (n + 1))
  declaredControlledGates : ℕ
  declaredDataBits : ℕ
  declaredFloatBits : ℕ
  floatError : ℝ
  gateError : ℝ
  classicalCost : ℕ

noncomputable def gateWordMatrix {n : ℕ} (gs : List (LocalQFTGate n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  localProgramMatrix gs.reverse

noncomputable def synthAccessMatrix {n : ℕ} (s : StrangAccessSynthesis n) :
    Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (gateWordMatrix s.word)

noncomputable def regControlEmbed {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ := Matrix.of fun x y =>
  if x (Fin.last n) = true ∧ y (Fin.last n) = true
      ∧ ∀ i : Fin n, x i.castSucc = y i.castSucc then
    U (fun i => x i.castSucc) (fun i => y i.castSucc)
  else if x = y then (1 : ℂ) else 0

def regIndexBits (n : ℕ) : ℕ := max 1 (Nat.clog 2 n)

def localGateDataBits {n : ℕ} : LocalQFTGate n → ℕ
  | .h _ => regIndexBits n
  | .cp _ _ k _ => 2 * regIndexBits n + (Nat.log 2 k + 1)
  | .swap _ _ => 2 * regIndexBits n

def gateWordDataBits {n : ℕ} (gs : List (LocalQFTGate n)) : ℕ :=
  (gs.map localGateDataBits).sum

def strangAccessBlocks {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : List (List (LocalQFTGate n) × Fin m) :=
  let ids := List.finRange m
  let step := (ids ++ ids.reverse).map (fun j => ((synth j).word, j))
  (List.replicate r step).flatten

def strangAdjointBlocks {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : List (List (LocalQFTGate n) × Fin m) :=
  (strangAccessBlocks synth r).reverse.map
    (fun b => (localProgramAdjoint b.1, b.2))

def strangControlledBlocks {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : List (List (LocalQFTGate (n + 1)) × Fin m) :=
  let ids := List.finRange m
  let step := (ids ++ ids.reverse).map (fun j => ((synth j).controlledWord, j))
  (List.replicate r step).flatten

noncomputable def strangRegBlockMatrix {n m : ℕ}
    (w : List (List (LocalQFTGate n) × Fin m)) : Matrix (Reg n) (Reg n) ℂ :=
  (w.map (fun b => gateWordMatrix b.1)).foldl (fun W V => V * W) 1

noncomputable def strangBlockMatrix {n m : ℕ}
    (w : List (List (LocalQFTGate n) × Fin m)) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (strangRegBlockMatrix w)

def blockGateTotal {n m : ℕ} (w : List (List (LocalQFTGate n) × Fin m)) : ℕ :=
  (w.map (fun b => b.1.length)).sum

def blockTariffTotal {n m : ℕ} (price : Fin m → ℕ)
    (w : List (List (LocalQFTGate n) × Fin m)) : ℕ :=
  (w.map (fun b => price b.2)).sum

def blockDataBitsTotal {n m : ℕ} (w : List (List (LocalQFTGate n) × Fin m)) : ℕ :=
  (w.map (fun b => gateWordDataBits b.1)).sum

def blockClassicalCostTotal {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : ℕ :=
  ((strangAccessBlocks synth r).map (fun b => (synth b.2).classicalCost)).sum

def forwardSpaceQubits (n : ℕ) : ℕ := n

def controlledSpaceQubits (n : ℕ) : ℕ := n + 1

noncomputable def strangCompileBudget {n m : ℕ} (H : Fin m → Operator (2 ^ n))
    (synth : Fin m → StrangAccessSynthesis n) (t : ℝ) (r : ℕ) : ℝ :=
  |t| ^ 3 * finiteStrangConstant H / (r : ℝ) ^ 2 +
    2 * (r : ℝ) * ∑ j, ((synth j).floatError + (synth j).gateError)

def ferroPairList (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u =>
    ((List.finRange n).filter (fun v => decide (u.val < v.val))).map
      (fun v => (u, v)))

structure FerroData (n : ℕ) where
  p : Fin n → Fin n → ℝ
  q : Fin n → Fin n → ℝ
  d : Fin n → ℝ

def FerroLegal {n : ℕ} (F : FerroData n) : Prop :=
  (∀ u v, 0 ≤ F.p u v ∧ F.p u v ≤ 1) ∧
    (∀ u v, 0 ≤ F.q u v ∧ F.q u v ≤ 1) ∧
      (∀ u, -1 ≤ F.d u ∧ F.d u ≤ 1)

noncomputable def twoWirePauli (n : ℕ) (u v : Fin n) (a b : Fin 4) :
    Operator (2 ^ n) :=
  pauliStringMatrix n (fun i => if i = u then a else if i = v then b else 0)

noncomputable def wireZ (n : ℕ) (u : Fin n) : Operator (2 ^ n) :=
  pauliStringMatrix n (fun i => if i = u then 3 else 0)

noncomputable def ferroTermP (n : ℕ) (u v : Fin n) : Operator (2 ^ n) :=
  -(twoWirePauli n u v 1 1) - twoWirePauli n u v 2 2

noncomputable def ferroTermQ (n : ℕ) (u v : Fin n) : Operator (2 ^ n) :=
  -(twoWirePauli n u v 1 1) + twoWirePauli n u v 2 2

noncomputable def ferroTermD (n : ℕ) (u : Fin n) : Operator (2 ^ n) :=
  (1 : Operator (2 ^ n)) + wireZ n u

noncomputable def ferroHamiltonian {n : ℕ} (F : FerroData n) : Operator (2 ^ n) :=
  ((ferroPairList n).map (fun uv =>
    (F.p uv.1 uv.2) • ferroTermP n uv.1 uv.2 +
      (F.q uv.1 uv.2) • ferroTermQ n uv.1 uv.2)).sum +
    ((List.finRange n).map (fun u => (F.d u) • ferroTermD n u)).sum

inductive FerroMatchgate (n : ℕ) where
  | f : Fin n → ℝ → FerroMatchgate n
  | g : Fin n → Fin n → ℝ → FerroMatchgate n
  | h : Fin n → Fin n → ℝ → FerroMatchgate n

noncomputable def ferroGateMatrix {n : ℕ} : FerroMatchgate n → Operator (2 ^ n)
  | .f u s => ((Real.exp s + 1) / 2) • (1 : Operator (2 ^ n)) +
      ((Real.exp s - 1) / 2) • wireZ n u
  | .g u v t => (1 + t ^ 2 / 2) • (1 : Operator (2 ^ n)) +
      (t / 2) • (twoWirePauli n u v 1 1 - twoWirePauli n u v 2 2) +
      (t ^ 2 / 2) • twoWirePauli n u v 3 3
  | .h u v t => (1 + t ^ 2 / 2) • (1 : Operator (2 ^ n)) +
      (t / 2) • (twoWirePauli n u v 1 1 + twoWirePauli n u v 2 2) -
      (t ^ 2 / 2) • twoWirePauli n u v 3 3

noncomputable def ferroGateHalf {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (FerroMatchgate n) :=
  (List.finRange n).map (fun u => FerroMatchgate.f u (-(β / (r : ℝ)) * F.d u)) ++
    (ferroPairList n).map (fun uv =>
      FerroMatchgate.g uv.1 uv.2 ((β / (r : ℝ)) * F.q uv.1 uv.2)) ++
    (ferroPairList n).map (fun uv =>
      FerroMatchgate.h uv.1 uv.2 ((β / (r : ℝ)) * F.p uv.1 uv.2))

noncomputable def ferroGateWord {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (FerroMatchgate n) :=
  ferroGateHalf F β r ++ (ferroGateHalf F β r).reverse

noncomputable def ferroFullGateWord {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (FerroMatchgate n) :=
  (List.replicate r (ferroGateWord F β r)).flatten

noncomputable def ferroGateRun {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  ((ferroGateWord F β r).map ferroGateMatrix).prod

noncomputable def ferroGatePower {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  (ferroGateRun F β r) ^ r

noncomputable def ferroStepHalf {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (Operator (2 ^ n)) :=
  (List.finRange n).map (fun u =>
    NormedSpace.exp (-(β / (2 * (r : ℝ))) • (F.d u) • ferroTermD n u)) ++
    (ferroPairList n).map (fun uv =>
      NormedSpace.exp (-(β / (2 * (r : ℝ))) • (F.q uv.1 uv.2) •
        ferroTermQ n uv.1 uv.2)) ++
    (ferroPairList n).map (fun uv =>
      NormedSpace.exp (-(β / (2 * (r : ℝ))) • (F.p uv.1 uv.2) •
        ferroTermP n uv.1 uv.2))

noncomputable def ferroStepWord {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (Operator (2 ^ n)) :=
  ferroStepHalf F β r ++ (ferroStepHalf F β r).reverse

noncomputable def ferroRun {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  (ferroStepWord F β r).prod

noncomputable def ferroStepIdeal {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  NormedSpace.exp (-(β / (r : ℝ)) • ferroHamiltonian F)

noncomputable def ferroIdealEvolution {n : ℕ} (F : FerroData n) (β : ℝ) :
    Operator (2 ^ n) :=
  NormedSpace.exp (-(β : ℝ) • ferroHamiltonian F)

noncomputable def ferroPartition {n : ℕ} (F : FerroData n) (β : ℝ) : ℝ :=
  ((ferroIdealEvolution F β).trace).re

noncomputable def ferroGatePartition {n : ℕ} (F : FerroData n) (β : ℝ)
    (r : ℕ) : ℝ :=
  ((ferroGatePower F β r).trace).re

def ferroPerGateErrorC : ℝ := 1

def ferroMultiplicativeC : ℝ := 2 ^ 20

noncomputable def ferroSegments (n : ℕ) (β ε : ℝ) : ℕ := Nat.ceil
  (max (2 * β + 1) (max (32 * (n : ℝ) ^ 2 * β)
    (max (32 * (n : ℝ) ^ 2 * β ^ 2 / ε)
      (2 * Real.sqrt (ferroMultiplicativeC) * (n : ℝ) ^ 2 * β *
        Real.sqrt β / Real.sqrt ε))))

noncomputable def ferroGateCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).length

noncomputable def ferroGateFCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).countP
    (fun g => match g with | .f _ _ => true | _ => false)

noncomputable def ferroGateGCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).countP
    (fun g => match g with | .g _ _ _ => true | _ => false)

noncomputable def ferroGateHCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).countP
    (fun g => match g with | .h _ _ _ => true | _ => false)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
