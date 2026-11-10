/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.CoefficientLCU
import Qatlib.Concepts.LchsSimulation.Quadrature.CompositeGaussAlgebra
import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule
import Qatlib.Concepts.LchsSimulation.LchsRep.GeneralAnalyticLchsKernel
import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialKernelModulus
import Qatlib.Concepts.LchsSimulation.Quadrature.NearExponentialKernelQuadrature
import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Qatlib.Concepts.LchsSimulation.TimeLchs
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.LchsSimulation.Quadrature
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Concepts.LchsSimulation.Quadrature

open Qatlib MeasureTheory Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def lowerOpenHalfPlane : Set ℂ := {z : ℂ | z.im < 0}

def lowerClosedHalfPlane : Set ℂ := {z : ℂ | z.im ≤ 0}

def cauchyWeightPole : ℂ := -Complex.I

noncomputable def complexCauchyWeight (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / (1 - Complex.I * z)

structure KernelBoundary where

  f : ℂ → ℂ

  analytic_open : AnalyticOn ℂ f lowerOpenHalfPlane

  continuous_closed : ContinuousOn f lowerClosedHalfPlane

structure GaussRule (Q : ℕ) where

  node : Fin Q → ℝ

  weight : Fin Q → ℝ

  node_mem : ∀ q, node q ∈ Ioo (-1) 1

  node_inj : Function.Injective node

  weight_pos : ∀ q, 0 < weight q

  exact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
    ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)

  omega : (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
    ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
      (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2)

noncomputable def loadedGaussRule (Q : ℕ) (hQ : 1 ≤ Q) : GaussRule Q :=
  have h := gauss_legendre_rule_exists Q hQ
  have hp := Classical.choose_spec (Classical.choose_spec h)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h), hp.1, hp.2.1,
    hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

def compositeCellWidth (K M : ℕ) : ℝ := (2 * K : ℝ) / M

def compositeCellStart (K M : ℕ) (m : ℕ) : ℝ :=
  (-K : ℝ) + compositeCellWidth K M * (m : ℝ)

def compositeNodeAt {Q M : ℕ} (K : ℕ) (node : Fin Q → ℝ) (m : Fin M) (q : Fin Q) : ℝ :=
  (-K : ℝ) + compositeCellWidth K M * ((m : ℝ) + (node q + 1) / 2)

def compositeCellSum {I : Type} [Fintype I] [DecidableEq I] {Q M : ℕ}
    (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) (Φ : ℝ → Matrix I I ℂ)
    (m : Fin M) : Matrix I I ℂ :=
  ∑ q : Fin Q,
    (((((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
      κ (compositeNodeAt K node m q)) • Φ (compositeNodeAt K node m q))

def compositeSum {I : Type} [Fintype I] [DecidableEq I] {Q M : ℕ}
    (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) (Φ : ℝ → Matrix I I ℂ) :
    Matrix I I ℂ :=
  ∑ m : Fin M, compositeCellSum K node weight κ Φ m

def compositeCoefficients {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) : Fin M → Fin Q → ℂ :=
  fun m q => (((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
    κ (compositeNodeAt K node m q)

noncomputable def lchsIntegrand {I : Type} [Fintype I] [DecidableEq I]
    (β : ℝ) (L H : ℝ → Matrix I I ℂ) (s t : ℝ) : ℝ → Matrix I I ℂ :=
  fun k => highKernelG β k •
    orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t

noncomputable def lchsGenerator {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) : ℝ → Matrix I I ℂ :=
  fun u => L u + Complex.I • H u

noncomputable def lchsSourceIntegral {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ) : QState I :=
  ∫ u in s..t, orderedEvolution A u t *ᵥ b u

noncomputable def lchsForcedResponse {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s : ℝ) (v : QState I) (t : ℝ) : QState I :=
  orderedForcedSolution A b s v t

def compositeCellCount (T Λ : ℝ) (K : ℕ) : ℕ :=
  Nat.ceil (2 * K * Real.exp 1 * T * Λ)

def compositeNodeCount (β K ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log ((8 / (3 * highKernelC β)) * K / ε) / Real.log 4))

structure LchsCostLedger where

  window : ℕ

  cells : ℕ

  nodesPerCell : ℕ

  propagatorEvaluations : ℕ

  amplificationRounds : ℕ

noncomputable def compositeCostLedger (β : ℝ) (T Λ : ℝ) (K : ℕ) (ε : ℝ) : LchsCostLedger :=
  let M := compositeCellCount T Λ K
  let Q := compositeNodeCount β K ε
  ⟨K, M, Q, M * Q, 0⟩

structure GibbsInput (X : Type) where

  energy : X → ℝ

  observable : X → ℝ

  temperature : ℝ

  filterLevel : ℝ

noncomputable def partitionFunction {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, Real.exp (-g.energy x / g.temperature)

noncomputable def gibbsProbability {X : Type} [Fintype X] (g : GibbsInput X) (x : X) : ℝ :=
  Real.exp (-g.energy x / g.temperature) / partitionFunction g

def filterEvent {X : Type} (g : GibbsInput X) (x : X) : Prop :=
  g.energy x ≤ g.filterLevel

noncomputable def filterSuccessProbability {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, if filterEvent g x then gibbsProbability g x else 0

noncomputable def gibbsObservableExpectation {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, gibbsProbability g x * g.observable x

noncomputable def observableRange {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, |g.observable x| + 1

def gibbsSampleCount {X : Type} [Fintype X] (g : GibbsInput X) (ε δ : ℝ) : ℕ :=
  Nat.ceil (Real.log (2 / δ) / (2 * Real.log (1 + ε / (2 * observableRange g))))

end Qatlib.Concepts.LchsSimulation.Quadrature
