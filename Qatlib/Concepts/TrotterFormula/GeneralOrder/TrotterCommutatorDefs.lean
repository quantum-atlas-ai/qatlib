/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.FiniteStrang.FiniteStrangCommutatorConsumers
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.RandCompile.ReferenceModel.LocalPauliEvolution

/-!
# Compiled Strang words and ferromagnetic gate models

This module defines labeled Strang synthesis blocks, their matrix interpretations, and gate,
data, tariff, and classical-cost totals. The combined budget `strangCompileBudget` adds declared
synthesis errors to the finite Strang discretization bound, within the product-formula setting
of [ChildsEtAl2021Trotter].

The ferromagnetic model includes real coupling data, Pauli interaction terms, palindromic
exponential steps, and explicit matchgate matrices. Separate definitions record the ideal and
gate-based partition expressions and the counts of the three gate forms.

## Main statements

* `StrangAccessSynthesis`: gate words with declared size, error, and cost data.
* `strangAccessBlocks`: repeated forward-and-reverse labeled synthesis blocks.
* `strangCompileBudget`: discretization and accumulated synthesis error expression.
* `ferroHamiltonian`: Pauli Hamiltonian defined by the coupling data.
* `ferroGatePower`: repeated palindromic matchgate step.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

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

/-- Synthesis data for a Strang access operation, including forward and controlled gate words,
declared sizes, error budgets, and classical cost. -/
structure StrangAccessSynthesis (n : ℕ) where
  word : List (LocalQFTGate n)
  controlledWord : List (LocalQFTGate (n + 1))
  declaredControlledGates : ℕ
  declaredDataBits : ℕ
  declaredFloatBits : ℕ
  floatError : ℝ
  gateError : ℝ
  classicalCost : ℕ

/-- The matrix assigned to a gate word by evaluating `localProgramMatrix` on its reverse. -/
noncomputable def gateWordMatrix {n : ℕ} (gs : List (LocalQFTGate n)) :
    Matrix (Reg n) (Reg n) ℂ :=
  localProgramMatrix gs.reverse

/-- The gate-word matrix of a synthesis record, relabeled from bit registers to `Fin (2^n)`. -/
noncomputable def synthAccessMatrix {n : ℕ} (s : StrangAccessSynthesis n) :
    Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (gateWordMatrix s.word)

/-- The diagonal register matrix that uses diagonal entries of `U` when the final control bit is
true and identity entries when it is false. -/
noncomputable def regControlEmbed {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ := Matrix.of fun x y =>
  if x (Fin.last n) = true ∧ y (Fin.last n) = true
      ∧ ∀ i : Fin n, x i.castSucc = y i.castSucc then
    U (fun i => x i.castSucc) (fun i => y i.castSucc)
  else if x = y then (1 : ℂ) else 0

/-- The binary ceiling-logarithm index width for `n`, bounded below by one. -/
def regIndexBits (n : ℕ) : ℕ := max 1 (Nat.clog 2 n)

/-- The declared data-bit cost of a local gate, accounting for its wire indices and, for a
controlled phase, its integer parameter. -/
def localGateDataBits {n : ℕ} : LocalQFTGate n → ℕ
  | .h _ => regIndexBits n
  | .cp _ _ k _ => 2 * regIndexBits n + (Nat.log 2 k + 1)
  | .swap _ _ => 2 * regIndexBits n

/-- The sum of the local gate data-bit costs in a word. -/
def gateWordDataBits {n : ℕ} (gs : List (LocalQFTGate n)) : ℕ :=
  (gs.map localGateDataBits).sum

/-- The labeled synthesis blocks obtained by repeating a forward traversal and its reverse for
`r` Strang segments. -/
def strangAccessBlocks {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : List (List (LocalQFTGate n) × Fin m) :=
  let ids := List.finRange m
  let step := (ids ++ ids.reverse).map (fun j => ((synth j).word, j))
  (List.replicate r step).flatten

/-- The reversed forward block sequence with each local gate word replaced by its adjoint
program. -/
def strangAdjointBlocks {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : List (List (LocalQFTGate n) × Fin m) :=
  (strangAccessBlocks synth r).reverse.map
    (fun b => (localProgramAdjoint b.1, b.2))

/-- The labeled controlled synthesis blocks obtained by repeating the forward and reverse label
traversal for `r` segments. -/
def strangControlledBlocks {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : List (List (LocalQFTGate (n + 1)) × Fin m) :=
  let ids := List.finRange m
  let step := (ids ++ ids.reverse).map (fun j => ((synth j).controlledWord, j))
  (List.replicate r step).flatten

/-- The register matrix obtained by folding the block gate-word matrices by successive left
multiplication. -/
noncomputable def strangRegBlockMatrix {n m : ℕ}
    (w : List (List (LocalQFTGate n) × Fin m)) : Matrix (Reg n) (Reg n) ℂ :=
  (w.map (fun b => gateWordMatrix b.1)).foldl (fun W V => V * W) 1

/-- The register block matrix relabeled to the finite basis `Fin (2^n)`. -/
noncomputable def strangBlockMatrix {n m : ℕ}
    (w : List (List (LocalQFTGate n) × Fin m)) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (strangRegBlockMatrix w)

/-- The sum of gate-word lengths across a labeled block sequence. -/
def blockGateTotal {n m : ℕ} (w : List (List (LocalQFTGate n) × Fin m)) : ℕ :=
  (w.map (fun b => b.1.length)).sum

/-- The sum of label-dependent prices across a block sequence. -/
def blockTariffTotal {n m : ℕ} (price : Fin m → ℕ)
    (w : List (List (LocalQFTGate n) × Fin m)) : ℕ :=
  (w.map (fun b => price b.2)).sum

/-- The sum of gate-word data-bit costs across a block sequence. -/
def blockDataBitsTotal {n m : ℕ} (w : List (List (LocalQFTGate n) × Fin m)) : ℕ :=
  (w.map (fun b => gateWordDataBits b.1)).sum

/-- The total declared classical synthesis cost across all Strang access blocks. -/
def blockClassicalCostTotal {n m : ℕ} (synth : Fin m → StrangAccessSynthesis n)
    (r : ℕ) : ℕ :=
  ((strangAccessBlocks synth r).map (fun b => (synth b.2).classicalCost)).sum

/-- The declared forward register size of `n` qubits. -/
def forwardSpaceQubits (n : ℕ) : ℕ := n

/-- The declared controlled register size of `n+1` qubits. -/
def controlledSpaceQubits (n : ℕ) : ℕ := n + 1

/-- The sum of the Strang discretization bound and the accumulated floating and gate synthesis
error budgets. -/
noncomputable def strangCompileBudget {n m : ℕ} (H : Fin m → Operator (2 ^ n))
    (synth : Fin m → StrangAccessSynthesis n) (t : ℝ) (r : ℕ) : ℝ :=
  |t| ^ 3 * finiteStrangConstant H / (r : ℝ) ^ 2 +
    2 * (r : ℝ) * ∑ j, ((synth j).floatError + (synth j).gateError)

/-- The list of wire pairs `(u,v)` satisfying `u.val < v.val`, enumerated in increasing wire
order. -/
def ferroPairList (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u =>
    ((List.finRange n).filter (fun v => decide (u.val < v.val))).map
      (fun v => (u, v)))

/-- Real pair-coupling arrays `p` and `q` and on-site coefficients `d` for the ferromagnetic
Hamiltonian. -/
structure FerroData (n : ℕ) where
  p : Fin n → Fin n → ℝ
  q : Fin n → Fin n → ℝ
  d : Fin n → ℝ

/-- The bounds placing both pair-coupling arrays in `[0,1]` and every on-site coefficient in
`[-1,1]`. -/
def FerroLegal {n : ℕ} (F : FerroData n) : Prop :=
  (∀ u v, 0 ≤ F.p u v ∧ F.p u v ≤ 1) ∧
    (∀ u v, 0 ≤ F.q u v ∧ F.q u v ≤ 1) ∧
      (∀ u, -1 ≤ F.d u ∧ F.d u ≤ 1)

/-- The Pauli string using label `a` at wire `u`, label `b` at wire `v` when distinct from `u`,
and identity labels elsewhere. -/
noncomputable def twoWirePauli (n : ℕ) (u v : Fin n) (a b : Fin 4) :
    Operator (2 ^ n) :=
  pauliStringMatrix n (fun i => if i = u then a else if i = v then b else 0)

/-- The Pauli string applying `Z` at wire `u` and identity at every other wire. -/
noncomputable def wireZ (n : ℕ) (u : Fin n) : Operator (2 ^ n) :=
  pauliStringMatrix n (fun i => if i = u then 3 else 0)

/-- The pair term given by the negative sum of the `XX` and `YY` Pauli strings. -/
noncomputable def ferroTermP (n : ℕ) (u v : Fin n) : Operator (2 ^ n) :=
  -(twoWirePauli n u v 1 1) - twoWirePauli n u v 2 2

/-- The pair term given by the negative `XX` Pauli string plus the `YY` Pauli string. -/
noncomputable def ferroTermQ (n : ℕ) (u v : Fin n) : Operator (2 ^ n) :=
  -(twoWirePauli n u v 1 1) + twoWirePauli n u v 2 2

/-- The on-site term `1 + wireZ n u`. -/
noncomputable def ferroTermD (n : ℕ) (u : Fin n) : Operator (2 ^ n) :=
  (1 : Operator (2 ^ n)) + wireZ n u

/-- The sum of the pair terms weighted by `p` and `q` and the on-site terms weighted by `d`. -/
noncomputable def ferroHamiltonian {n : ℕ} (F : FerroData n) : Operator (2 ^ n) :=
  ((ferroPairList n).map (fun uv =>
    (F.p uv.1 uv.2) • ferroTermP n uv.1 uv.2 +
      (F.q uv.1 uv.2) • ferroTermQ n uv.1 uv.2)).sum +
    ((List.finRange n).map (fun u => (F.d u) • ferroTermD n u)).sum

/-- The three parameterized gate forms `f`, `g`, and `h` used in the ferromagnetic matchgate
construction. -/
inductive FerroMatchgate (n : ℕ) where
  | f : Fin n → ℝ → FerroMatchgate n
  | g : Fin n → Fin n → ℝ → FerroMatchgate n
  | h : Fin n → Fin n → ℝ → FerroMatchgate n

/-- The explicit Pauli-matrix expression assigned to each of the three ferromagnetic matchgate
forms. -/
noncomputable def ferroGateMatrix {n : ℕ} : FerroMatchgate n → Operator (2 ^ n)
  | .f u s => ((Real.exp s + 1) / 2) • (1 : Operator (2 ^ n)) +
      ((Real.exp s - 1) / 2) • wireZ n u
  | .g u v t => (1 + t ^ 2 / 2) • (1 : Operator (2 ^ n)) +
      (t / 2) • (twoWirePauli n u v 1 1 - twoWirePauli n u v 2 2) +
      (t ^ 2 / 2) • twoWirePauli n u v 3 3
  | .h u v t => (1 + t ^ 2 / 2) • (1 : Operator (2 ^ n)) +
      (t / 2) • (twoWirePauli n u v 1 1 + twoWirePauli n u v 2 2) -
      (t ^ 2 / 2) • twoWirePauli n u v 3 3

/-- The matchgate half-step listing the on-site `f` gates, the `q`-weighted `g` gates, and the
`p`-weighted `h` gates. -/
noncomputable def ferroGateHalf {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (FerroMatchgate n) :=
  (List.finRange n).map (fun u => FerroMatchgate.f u (-(β / (r : ℝ)) * F.d u)) ++
    (ferroPairList n).map (fun uv =>
      FerroMatchgate.g uv.1 uv.2 ((β / (r : ℝ)) * F.q uv.1 uv.2)) ++
    (ferroPairList n).map (fun uv =>
      FerroMatchgate.h uv.1 uv.2 ((β / (r : ℝ)) * F.p uv.1 uv.2))

/-- The palindromic matchgate step formed from `ferroGateHalf` followed by its reverse. -/
noncomputable def ferroGateWord {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (FerroMatchgate n) :=
  ferroGateHalf F β r ++ (ferroGateHalf F β r).reverse

/-- The full matchgate list formed by repeating the palindromic step `r` times. -/
noncomputable def ferroFullGateWord {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (FerroMatchgate n) :=
  (List.replicate r (ferroGateWord F β r)).flatten

/-- The product of the matrices in one palindromic ferromagnetic matchgate step. -/
noncomputable def ferroGateRun {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  ((ferroGateWord F β r).map ferroGateMatrix).prod

/-- The `r`th power of the single-step ferromagnetic matchgate matrix. -/
noncomputable def ferroGatePower {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  (ferroGateRun F β r) ^ r

/-- The exponential half-step listing on-site, `q`-pair, and `p`-pair imaginary-time factors. -/
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

/-- The palindromic exponential step formed from `ferroStepHalf` followed by its reverse. -/
noncomputable def ferroStepWord {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    List (Operator (2 ^ n)) :=
  ferroStepHalf F β r ++ (ferroStepHalf F β r).reverse

/-- The product of the matrices in one palindromic ferromagnetic exponential step. -/
noncomputable def ferroRun {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  (ferroStepWord F β r).prod

/-- The ideal imaginary-time exponential for inverse-temperature increment `β/r`. -/
noncomputable def ferroStepIdeal {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) :
    Operator (2 ^ n) :=
  NormedSpace.exp (-(β / (r : ℝ)) • ferroHamiltonian F)

/-- The ideal imaginary-time exponential `exp ((-β) • ferroHamiltonian F)`. -/
noncomputable def ferroIdealEvolution {n : ℕ} (F : FerroData n) (β : ℝ) :
    Operator (2 ^ n) :=
  NormedSpace.exp (-(β : ℝ) • ferroHamiltonian F)

/-- The real part of the trace of the ideal ferromagnetic imaginary-time evolution. -/
noncomputable def ferroPartition {n : ℕ} (F : FerroData n) (β : ℝ) : ℝ :=
  ((ferroIdealEvolution F β).trace).re

/-- The real part of the trace of the repeated ferromagnetic matchgate step. -/
noncomputable def ferroGatePartition {n : ℕ} (F : FerroData n) (β : ℝ)
    (r : ℕ) : ℝ :=
  ((ferroGatePower F β r).trace).re

/-- The per-gate error constant, defined to be one. -/
def ferroPerGateErrorC : ℝ := 1

/-- The multiplicative error constant, defined to be `2^20`. -/
def ferroMultiplicativeC : ℝ := 2 ^ 20

/-- The ceiling of the maximum of the specified temperature, size, and tolerance expressions
used to select ferromagnetic segments. -/
noncomputable def ferroSegments (n : ℕ) (β ε : ℝ) : ℕ := Nat.ceil
  (max (2 * β + 1) (max (32 * (n : ℝ) ^ 2 * β)
    (max (32 * (n : ℝ) ^ 2 * β ^ 2 / ε)
      (2 * Real.sqrt (ferroMultiplicativeC) * (n : ℝ) ^ 2 * β *
        Real.sqrt β / Real.sqrt ε))))

/-- The length of the full repeated ferromagnetic matchgate word. -/
noncomputable def ferroGateCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).length

/-- The number of `f` gates in the full repeated ferromagnetic matchgate word. -/
noncomputable def ferroGateFCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).countP
    (fun g => match g with | .f _ _ => true | _ => false)

/-- The number of `g` gates in the full repeated ferromagnetic matchgate word. -/
noncomputable def ferroGateGCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).countP
    (fun g => match g with | .g _ _ _ => true | _ => false)

/-- The number of `h` gates in the full repeated ferromagnetic matchgate word. -/
noncomputable def ferroGateHCount {n : ℕ} (F : FerroData n) (β : ℝ) (r : ℕ) : ℕ :=
  (ferroFullGateWord F β r).countP
    (fun g => match g with | .h _ _ _ => true | _ => false)

end Qatlib.Concepts.TrotterFormula.GeneralOrder
