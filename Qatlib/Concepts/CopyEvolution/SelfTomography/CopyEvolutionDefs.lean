/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.CopyDrivenPhaseReadout
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyEvolutionCompletionModelCore
import Qatlib.Concepts.CopyEvolution.SelfTomography.SelfTomographyOnGridOutputQuan
import Qatlib.Concepts.CopyEvolution.SelfTomography.EpsilonCubedSelfTomographyQuan
import Qatlib.Concepts.WalkFind.QRAMModel.QRAMImplementation
import Qatlib.Concepts.WalkFind.WalkSpectrum.EffectiveQRAMImplementation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.CopyEvolution.SelfTomography

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

noncomputable def offgridBranch (D M : ℕ) (eig : Fin D → ℝ) (V : Operator D)
    (z : Fin M) : Operator D :=
  ∑ i, (eig i : ℂ) • outerProduct (fun j => qpeKernel M (-eig i / 2) z * V j i)

noncomputable def offgridBranchMass (D M : ℕ) (eig : Fin D → ℝ) (V : Operator D)
    (z : Fin M) : ℝ :=
  ((offgridBranch D M eig V z).trace).re

noncomputable def offgridConditionalState (D M : ℕ) (eig : Fin D → ℝ) (V : Operator D)
    (z : Fin M) (hm : 0 < offgridBranchMass D M eig V z) : Operator D :=
  ((offgridBranchMass D M eig V z) : ℂ)⁻¹ • (offgridBranch D M eig V z)

noncomputable def offgridLabelDecode (M : ℕ) (z : Fin M) : ℝ :=
  qpeLabelDecode M z

noncomputable def offgridGoodLabels (M : ℕ) (r : ℝ) : Finset (Fin M) :=
  qpeGoodLabels M r

def loadedTable (b m : ℕ) (ψ : Reg b) (i : ℕ) : Bool :=
  readBit ψ (m + i)

def indexedLoad (b a aw t m : ℕ) (ψ : Reg b) : Bool :=
  readBit (qramAction b a aw t m ψ) t

def loadAddress (b a aw : ℕ) (ψ : Reg b) : ℕ :=
  addressValue ψ a aw

def copyEvolutionLoadingProgram (n b a aw t m ml : ℕ) : List SourceCode :=
  List.replicate (n * b) (.qram a aw t m ml)

def copyEvolutionLoadingBasicGates (n b : ℕ) : ℕ :=
  3 * n * b

noncomputable def copyEvolutionLoadingBitCost (a aw t m ml : ℕ) : ℕ :=
  codeBits (.qram a aw t m ml)

inductive BackendAlphabet where
  | localFixedGate : FiniteGateCode → BackendAlphabet
  | addressSwap : ℕ → ℕ → ℕ → ℕ → ℕ → BackendAlphabet
  | additiveQuery : BackendAlphabet
  deriving DecidableEq, Repr

def BackendAlphabet.toSourceCode : BackendAlphabet → SourceCode
  | .localFixedGate g => .local g
  | .addressSwap a aw t m ml => .qram a aw t m ml
  | .additiveQuery => .query

noncomputable def normDependentCopyBudget (t ε residualNorm : ℝ) : ℕ :=
  max 1 (Nat.ceil (8 * t ^ 2 * residualNorm / ε))

structure LabelLaw (M : ℕ) where

  mass : Fin M → ℝ

  nonneg : ∀ z, 0 ≤ mass z

  total : (∑ z, mass z) = 1

def mCopyLaw (M m : ℕ) (p : LabelLaw M) : (Fin m → Fin M) → ℝ :=
  fun t => ∏ i, p.mass (t i)

def labelCount (M m : ℕ) (t : Fin m → Fin M) (z : Fin M) : ℕ :=
  (Finset.univ.filter (fun i => t i = z)).card

noncomputable def labelFrequency (M m : ℕ) (t : Fin m → Fin M) (z : Fin M) : ℝ :=
  ((labelCount M m t z : ℕ) : ℝ) / (m : ℝ)

noncomputable def branchExpectation (D M : ℕ) (A : Operator D) (eig : Fin D → ℝ)
    (V : Operator D) (z : Fin M) : ℝ :=
  (((offgridBranch D M eig V z) * A).trace).re

noncomputable def hermitianExpectationEstimate (D M m : ℕ) (A : Operator D)
    (eig : Fin D → ℝ) (V : Operator D) (t : Fin m → Fin M) : ℝ :=
  ∑ z, labelFrequency M m t z * branchExpectation D M A eig V z

def finCons {n : ℕ} {α : Type*} (a : α) (t : Fin n → α) : Fin (n+1) → α :=
  Fin.cases a (fun i => t i)

def finSuccEquiv (M m : ℕ) : (Fin (m+1) → Fin M) ≃ Fin M × (Fin m → Fin M) where
  toFun t := (t 0, fun i => t i.succ)
  invFun s := finCons s.1 (fun i => s.2 i)
  left_inv t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv s := by
    rcases s with ⟨a, t'⟩
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i.succ
      · rfl
      · rfl

def walkGoalEndpointSpec : Prop :=

  (∀ (b a aw t m : ℕ) (ψ : Reg b), t < b →
    indexedLoad b a aw t m ψ = loadedTable b m ψ (loadAddress b a aw ψ)) ∧

  (∀ (b a aw t m ml : ℕ) (ψ : Reg b),
    sourceCodeLegal b (.qram a aw t m ml) = true →
    loadAddress b a aw (qramAction b a aw t m ψ) = loadAddress b a aw ψ) ∧

  (∀ (b a aw t m ml : ℕ) (ψ : Reg b),
    sourceCodeLegal b (.qram a aw t m ml) = true →
    qramAction b a aw t m (qramAction b a aw t m ψ) = ψ) ∧

  (∀ (n b a aw t m ml : ℕ),
    sourceCodeLegal b (.qram a aw t m ml) = true →
    (copyEvolutionLoadingProgram n b a aw t m ml).length = n * b ∧
    (∀ c ∈ copyEvolutionLoadingProgram n b a aw t m ml, sourceCodeLegal b c = true)) ∧

  (∀ (n b : ℕ), copyEvolutionLoadingBasicGates n b = 3 * n * b ∧
    copyEvolutionLoadingBasicGates n b = copyEvolutionBasicGates n b) ∧

  (∀ (n b a aw t m ml : ℕ),
    ((copyEvolutionLoadingProgram n b a aw t m ml).map
      (fun _ => copyEvolutionLoadingBitCost a aw t m ml)).sum =
      (n * b) * copyEvolutionLoadingBitCost a aw t m ml) ∧

  (∀ (b : ℕ) (cs : List SourceCode), sourceWordLegal b cs →
    IsUnitaryCircuit (sourceCircuit b cs)) ∧

  (∀ (D r : ℕ) (ρ : Operator D) (t ε R : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
    IsDensityOperator ρ → X.PosSemidef → 0 < ε → 0 ≤ R →
    Matrix.traceNorm (X - TensorGate ρ (Matrix.traceLeft X)) ≤ R →
    ∀ (n : ℕ), normDependentCopyBudget t ε R ≤ n →
      Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) r X -
        TensorGate (HamiltonianEvolution ρ t) (1 : Operator r) * X *
          (TensorGate (HamiltonianEvolution ρ t) (1 : Operator r))ᴴ) ≤ ε)

def clause16EndpointSpec : Prop :=

  (∀ (D M : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ),
    0 < M → IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ → (∀ i, 0 ≤ eig i) →
      (∀ (z : Fin M) (j j' : Fin D),
        copyQPEIdealOutput D M ρ ⟨z, (false, j)⟩ ⟨z, (false, j')⟩ =
          offgridBranch D M eig V z j j') ∧
      (∀ (z : Fin M), (offgridBranch D M eig V z).PosSemidef) ∧
      (∀ (z : Fin M), 0 ≤ offgridBranchMass D M eig V z)) ∧

  (∀ (M m : ℕ) (p : LabelLaw M),
    (∑ t : Fin m → Fin M, mCopyLaw M m p t = 1) ∧
    (∀ (j : Fin m) (z : Fin M),
      (∑ t : Fin m → Fin M, mCopyLaw M m p t * (if t j = z then 1 else 0)) = p.mass z)) ∧

  (∀ (D : ℕ) (ρ V : Operator D) (eig : Fin D → ℝ) (ε : ℝ),
    IsDensityOperator ρ → V ∈ Matrix.unitaryGroup (Fin D) ℂ →
    ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ →
    (∀ i, 0 ≤ eig i ∧ eig i ≤ 1) → 0 < ε → ε ≤ 1 / 2 →
    let M : ℕ := Nat.ceil (2 / ε)
    let n : ℕ := Nat.ceil (8 * (M : ℝ) * Real.pi ^ 2 / ε)
    (∀ (j : Fin D) (z : Fin M), z ∈ offgridGoodLabels M (eig j) →
      |offgridLabelDecode M z - eig j| ≤ 2 / (M : ℝ)) ∧
    2 ≤ M ∧ (2 : ℝ) / M ≤ ε ∧
    8 * (M - 1 : ℕ) * Real.pi ^ 2 / (n : ℝ) ≤ ε ∧
    ((M - 1 : ℕ) * n : ℝ) ≤ 1000 / ε ^ 3 ∧
    copyQPEResources D M n = ((M - 1) * n, (M - 1) * n, (M - 1) * n, 0) ∧
    (Matrix.trace (qpeSelfTomographyGoodProjector D M V eig *
      copyQPEIdealOutput D M ρ)).re ≥ 8 / Real.pi ^ 2 ∧
    (Matrix.trace (qpeSelfTomographyGoodProjector D M V eig *
      copyQPEOutput D M n ρ)).re ≥ 8 / Real.pi ^ 2 - ε)

end Qatlib.Concepts.CopyEvolution.SelfTomography
