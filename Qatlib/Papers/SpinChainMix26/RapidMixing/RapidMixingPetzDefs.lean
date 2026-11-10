/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Fin.SuccPred
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.SchattenDiamond.DiamondNorm

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzDefs

open Matrix Qatlib
open scoped Matrix.Norms.L2Operator Classical MatrixOrder ComplexOrder

variable {n d : ℕ}

def chainLabel (n d : ℕ) : Fin (d ^ n) ≃ (Fin n → Fin d) :=
  (finCongr (by simp [Finset.prod_const, Fintype.card_fin])).trans finPiFinEquiv.symm

def siteDigit (n d : ℕ) (i : Fin (d ^ n)) (j : Fin n) : Fin d :=
  chainLabel n d i j

def chainOfDigits (n d : ℕ) (f : Fin n → Fin d) : Fin (d ^ n) :=
  (chainLabel n d).symm f

def blockLabel (s ℓ : ℕ) (hn : 0 < n) (_hℓ : ℓ ≤ n) (i : Fin (d ^ n)) : Fin (d ^ ℓ) :=
  chainOfDigits ℓ d (fun t => siteDigit n d i ⟨(s + t.val) % n, Nat.mod_lt _ hn⟩)

def compLabel (s ℓ : ℕ) (hn : 0 < n) (_hℓ : ℓ ≤ n) (i : Fin (d ^ n)) :
    Fin (d ^ (n - ℓ)) :=
  chainOfDigits (n - ℓ) d
    (fun t => siteDigit n d i ⟨(s + ℓ + t.val) % n, Nat.mod_lt _ hn⟩)

def mergeLabel (s ℓ : ℕ) (hn : 0 < n) (hℓ : ℓ ≤ n) (b : Fin (d ^ ℓ))
    (k : Fin (d ^ (n - ℓ))) : Fin (d ^ n) :=
  chainOfDigits n d fun j =>
    if h : ((j.val + n - s) % n) < ℓ then
      chainLabel ℓ d b ⟨(j.val + n - s) % n, h⟩
    else
      chainLabel (n - ℓ) d k
        ⟨((j.val + n - s) % n) - ℓ, by have := Nat.mod_lt (j.val + n - s) hn; omega⟩

def sysPart (a : ℕ) (u : Fin (d ^ (n + a))) : Fin (d ^ n) :=
  chainOfDigits n d (fun j => siteDigit (n + a) d u ⟨j.val, by omega⟩)

def ancPart (a : ℕ) (u : Fin (d ^ (n + a))) : Fin (d ^ a) :=
  chainOfDigits a d (fun t => siteDigit (n + a) d u ⟨n + t.val, by omega⟩)

def joinLabel (a : ℕ) (b : Fin (d ^ n)) (k : Fin (d ^ a)) : Fin (d ^ (n + a)) :=
  chainOfDigits (n + a) d fun j =>
    if h : j.val < n then chainLabel n d b ⟨j.val, h⟩
    else chainLabel a d k ⟨j.val - n, by omega⟩

noncomputable def pairEmbed {w : ℕ} (U : Operator (d * d)) (i j : Fin w) :
    Operator (d ^ w) :=
  fun u v =>
    if ∀ k : Fin w, k ≠ i → k ≠ j → chainLabel w d u k = chainLabel w d v k then
      U (finProdFinEquiv (chainLabel w d u i, chainLabel w d u j))
        (finProdFinEquiv (chainLabel w d v i, chainLabel w d v j))
    else 0

noncomputable def siteEmbed {w : ℕ} (U : Operator d) (i : Fin w) : Operator (d ^ w) :=
  fun u v =>
    if ∀ k : Fin w, k ≠ i → chainLabel w d u k = chainLabel w d v k then
      U (chainLabel w d u i) (chainLabel w d v i)
    else 0

noncomputable def localTermEmbed (hn : 0 < n) (h : Operator (d * d)) (i : Fin n) :
    Operator (d ^ n) :=
  pairEmbed h i ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

noncomputable def chainHamiltonian (hn : 0 < n) (h : Fin n → Operator (d * d)) :
    Operator (d ^ n) :=
  ∑ i, localTermEmbed hn (h i) i

noncomputable def chainGibbsKernel (H : Operator (d ^ n)) (β : ℝ) : Operator (d ^ n) :=
  NormedSpace.exp (-(β : ℝ) • H)

noncomputable def chainGibbsPartition (H : Operator (d ^ n)) (β : ℝ) : ℝ :=
  ((chainGibbsKernel H β).trace).re

noncomputable def chainGibbs (H : Operator (d ^ n)) (β : ℝ) : Operator (d ^ n) :=
  (chainGibbsPartition H β)⁻¹ • chainGibbsKernel H β

def BoundedChain (h : Fin n → Operator (d * d)) : Prop :=
  ∀ i, (h i).IsHermitian ∧ OperatorSpectralNorm (h i) ≤ 1

structure LocalTermDesc (m : ℕ) where

  len : ℕ

  eval : Fin m → Fin m → ℕ → ℚ

  cost : ℕ → ℕ

namespace LocalTermDesc

def Admits {m : ℕ} (D : LocalTermDesc m) (A : Operator m) : Prop :=
  ∀ (p : ℕ) (i j : Fin m),
    (∃ q : ℤ, D.eval i j p = q / (2 : ℚ) ^ p) ∧
      ‖(D.eval i j p : ℂ) - A i j‖ ≤ ((1 : ℝ) / 2) ^ p

def PolyEvaluable {m : ℕ} (D : LocalTermDesc m) : Prop :=
  ∃ c k : ℕ, ∀ p : ℕ, D.cost p ≤ c * (D.len + p + 1) ^ k

end LocalTermDesc

def descLength {m : ℕ} (desc : Fin n → LocalTermDesc m) : ℕ :=
  (Finset.univ.sup fun i => (desc i).len)

noncomputable def halfTraceDist {D : ℕ} (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

noncomputable def blockReduced (σ : Operator (d ^ n)) (s ℓ : ℕ) (hn : 0 < n)
    (hℓ : ℓ ≤ n) : Operator (d ^ ℓ) :=
  fun b b' =>
    ∑ k : Fin (d ^ (n - ℓ)), σ (mergeLabel s ℓ hn hℓ b k) (mergeLabel s ℓ hn hℓ b' k)

noncomputable def blockCompEmbed (s ℓ : ℕ) (hn : 0 < n) (hℓ : ℓ ≤ n)
    (W : Operator (d ^ ℓ)) (k : Fin (d ^ (n - ℓ))) : Operator (d ^ n) :=
  fun u v =>
    if compLabel s ℓ hn hℓ u = k ∧ compLabel s ℓ hn hℓ v = k then
      W (blockLabel s ℓ hn hℓ u) (blockLabel s ℓ hn hℓ v)
    else 0

noncomputable def petzKraus (σ : Operator (d ^ n)) (s ℓ : ℕ) (hn : 0 < n)
    (hℓ : ℓ ≤ n) : Fin (d ^ (n - ℓ)) → Operator (d ^ n) :=
  fun k =>
    CFC.sqrt σ *
      blockCompEmbed s ℓ hn hℓ ((CFC.sqrt (blockReduced σ s ℓ hn hℓ))⁻¹) k

noncomputable def petzBlockChannel (σ : Operator (d ^ n)) (s ℓ : ℕ) (hn : 0 < n)
    (hℓ : ℓ ≤ n) : Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n) :=
  ∑ k : Fin (d ^ (n - ℓ)), conjBranch (petzKraus σ s ℓ hn hℓ k)

noncomputable def petzGenerator (σ : Operator (d ^ n)) (ℓ : ℕ) (hn : 0 < n)
    (hℓ : ℓ ≤ n) : Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n) :=
  ((ℓ : ℂ)⁻¹) •
    (∑ s : Fin n, petzBlockChannel σ s.val ℓ hn hℓ - (n : ℂ) • LinearMap.id)

noncomputable def liouvilleMatrix (L : Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n)) :
    Matrix (Fin (d ^ n) × Fin (d ^ n)) (Fin (d ^ n) × Fin (d ^ n)) ℂ :=
  LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin (d ^ n)) (Fin (d ^ n)))
    (Matrix.stdBasis ℂ (Fin (d ^ n)) (Fin (d ^ n))) L

noncomputable def idealChannel (L : Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n)) (t : ℝ) :
    Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n) :=
  (LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin (d ^ n)) (Fin (d ^ n)))
      (Matrix.stdBasis ℂ (Fin (d ^ n)) (Fin (d ^ n)))).symm
    (NormedSpace.exp ((t : ℂ) • liouvilleMatrix L))

inductive NN1DGate (w d : ℕ) where
  | one (i : Fin w) (U : Operator d)
  | two (i : Fin w) (U : Operator (d * d))

inductive NN1DStep (w d : ℕ) where
  | gate (g : NN1DGate w d)
  | reset (i : Fin w)

noncomputable def resetMatrixUnit (a : Fin d) : Operator d :=
  fun x y => if x.val = 0 ∧ y = a then 1 else 0

noncomputable def nnGateMatrix {w d : ℕ} : NN1DGate w d → Operator (d ^ w)
  | .one i U => siteEmbed U i
  | .two i U =>
      if h : i.val + 1 < w then pairEmbed U i ⟨i.val + 1, h⟩ else 1

def nnGateLegal {w d : ℕ} : NN1DGate w d → Prop
  | .one _ _ => True
  | .two i _ => i.val + 1 < w

def stepLegal {w d : ℕ} : NN1DStep w d → Prop
  | .gate g => nnGateLegal g
  | .reset _ => True

def nnGateSupport {w d : ℕ} : NN1DGate w d → List (Fin w)
  | .one i _ => [i]
  | .two i _ => if h : i.val + 1 < w then [i, ⟨i.val + 1, h⟩] else [i]

def nnStepSupport {w d : ℕ} : NN1DStep w d → List (Fin w)
  | .gate g => nnGateSupport g
  | .reset i => [i]

noncomputable def stepChannel {w d : ℕ} : NN1DStep w d →
    Operator (d ^ w) →ₗ[ℂ] Operator (d ^ w)
  | .gate g => conjBranch (nnGateMatrix g)
  | .reset i => ∑ a : Fin d, conjBranch (siteEmbed (resetMatrixUnit a) i)

noncomputable def branchChannel {w d : ℕ} (steps : List (NN1DStep w d)) :
    Operator (d ^ w) →ₗ[ℂ] Operator (d ^ w) :=
  (steps.map stepChannel).foldr (fun c acc => acc ∘ₗ c) LinearMap.id

noncomputable def initIsometry (a : ℕ) :
    Matrix (Fin (d ^ (n + a))) (Fin (d ^ n)) ℂ :=
  fun u b => if sysPart a u = b ∧ (ancPart a u).val = 0 then 1 else 0

noncomputable def discardKraus (a : ℕ) (k : Fin (d ^ a)) :
    Matrix (Fin (d ^ n)) (Fin (d ^ (n + a))) ℂ :=
  fun b u => if sysPart a u = b ∧ ancPart a u = k then 1 else 0

noncomputable def discardMap (a : ℕ) :
    Operator (d ^ (n + a)) →ₗ[ℂ] Operator (d ^ n) :=
  ∑ k : Fin (d ^ a), conjBranch (discardKraus a k)

noncomputable def sysChannelOf (a : ℕ) (steps : List (NN1DStep (n + a) d)) :
    Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n) :=
  (discardMap a).comp ((branchChannel steps).comp (conjBranch (initIsometry a)))

structure PetzBranch (w d : ℕ) where

  weight : ℝ

  steps : List (NN1DStep w d)

inductive PetzSamplingLaw where
  | poisson
  | uniform
  deriving DecidableEq, Repr

structure PetzSimArtifact (n d : ℕ) where

  ancillas : ℕ

  branches : List (PetzBranch (n + ancillas) d)

  gates : ℕ

  depth : ℕ

  classicalTime : ℕ

  window : ℕ

  sampleCap : ℕ

  sampler : PetzSamplingLaw

  runTime : ℝ

  windowErr : ℝ

  samplingErr : ℝ

  petzLocalErr : ℝ

  mixingErr : ℝ

  diamondErr : ℝ

  prepErr : ℝ

def branchGates {w d : ℕ} (B : PetzBranch w d) : ℕ :=
  (B.steps.map fun s =>
    match s with
    | .gate _ => 1
    | .reset _ => 0).sum

def branchDepth {w d : ℕ} (B : PetzBranch w d) : ℕ :=
  (B.steps.foldl
      (fun (acc : (Fin w → ℕ) × ℕ) (s : NN1DStep w d) =>
        let m := (nnStepSupport s).foldl (fun r i => max r (acc.1 i)) 0
        let layer := m + 1
        ((fun i => if i ∈ nnStepSupport s then max (acc.1 i) layer else acc.1 i),
          max acc.2 layer))
      (fun _ => (0 : ℕ), (0 : ℕ))).2

def PetzSimArtifact.Legal {n d : ℕ} (A : PetzSimArtifact n d) : Prop :=
  (∀ B ∈ A.branches, 0 ≤ B.weight) ∧
    (A.branches.map (fun B => B.weight)).sum = 1 ∧
    (∀ B ∈ A.branches, ∀ s ∈ B.steps, stepLegal s) ∧
    (∀ B ∈ A.branches, branchGates B ≤ A.gates) ∧
    (∀ B ∈ A.branches, branchDepth B ≤ A.depth)

noncomputable def averageChannel {n d : ℕ} (A : PetzSimArtifact n d) :
    Operator (d ^ n) →ₗ[ℂ] Operator (d ^ n) :=
  (A.branches.map fun B => (B.weight : ℂ) • sysChannelOf A.ancillas B.steps).sum

noncomputable def petzLogSlack (n : ℕ) (t ε : ℝ) : ℕ :=
  Nat.ceil (Real.log (2 * (n : ℝ) * (1 + t) / ε)) + 1

noncomputable def petzGateCore (n : ℕ) (t ε : ℝ) : ℕ :=
  n * Nat.ceil t + Nat.ceil (Real.log (2 / ε))

noncomputable def petzDepthCore (n : ℕ) (t ε : ℝ) : ℕ :=
  Nat.ceil t + Nat.ceil (Real.log (2 * (n : ℝ) / ε))

noncomputable def petzClassicalScale (n b : ℕ) (t ε : ℝ) : ℕ :=
  n + Nat.ceil t + Nat.ceil (Real.log (1 / ε)) + b + 1

noncomputable def petzPrepLog (n : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log ((n : ℝ) / ε)) + 1

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzDefs
