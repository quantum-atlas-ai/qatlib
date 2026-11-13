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

/-!
# Data for high-precision LCHS quadrature

The module packages analytic boundary kernels, positive Gauss rules, composite cells, LCHS
source responses, and explicit quadrature cost counts. It also defines finite Gibbs weights,
filtering events, observable averages, and a sample-count expression for subsequent consumers.
See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `GaussRule`: A `Q`-node rule with distinct nodes in `(-1, 1)`, positive weights, polynomial
  exactness through degree `2 * Q - 1`, and the stated squared nodal-product integral.
* `compositeSum`: The sum of `compositeCellSum` over all cells in the symmetric cutoff grid.
* `LchsCostLedger`: A record of the cutoff window, number of cells, nodes per cell, propagator
  evaluations, and amplification rounds.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

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

/-- The set of complex numbers with strictly negative imaginary part. -/
def lowerOpenHalfPlane : Set ℂ := {z : ℂ | z.im < 0}

/-- The set of complex numbers with nonpositive imaginary part. -/
def lowerClosedHalfPlane : Set ℂ := {z : ℂ | z.im ≤ 0}

/-- The point `-Complex.I`, where the denominator `1 - Complex.I * z` vanishes. -/
def cauchyWeightPole : ℂ := -Complex.I

/-- The complex Cauchy-weighted function `f z / (1 - Complex.I * z)`. -/
noncomputable def complexCauchyWeight (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z / (1 - Complex.I * z)

/-- A complex function together with analyticity on the open lower half-plane and continuity on
the closed lower half-plane. -/
structure KernelBoundary where

  f : ℂ → ℂ

  analytic_open : AnalyticOn ℂ f lowerOpenHalfPlane

  continuous_closed : ContinuousOn f lowerClosedHalfPlane

/-- A `Q`-node rule with distinct nodes in `(-1, 1)`, positive weights, polynomial exactness
through degree `2 * Q - 1`, and the stated squared nodal-product integral. -/
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

/-- A chosen `GaussRule Q` obtained from the existence theorem for positive `Q`. -/
noncomputable def loadedGaussRule (Q : ℕ) (hQ : 1 ≤ Q) : GaussRule Q :=
  have h := gauss_legendre_rule_exists Q hQ
  have hp := Classical.choose_spec (Classical.choose_spec h)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h), hp.1, hp.2.1,
    hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩

/-- The uniform cell width `(2 * K : ℝ) / M` for the symmetric cutoff interval. -/
def compositeCellWidth (K M : ℕ) : ℝ := (2 * K : ℝ) / M

/-- The left endpoint `-K + compositeCellWidth K M * m` of the indexed composite cell. -/
def compositeCellStart (K M : ℕ) (m : ℕ) : ℝ :=
  (-K : ℝ) + compositeCellWidth K M * (m : ℝ)

/-- The reference quadrature node affinely mapped into cell `m` of the symmetric cutoff grid. -/
def compositeNodeAt {Q M : ℕ} (K : ℕ) (node : Fin Q → ℝ) (m : Fin M) (q : Fin Q) : ℝ :=
  (-K : ℝ) + compositeCellWidth K M * ((m : ℝ) + (node q + 1) / 2)

/-- The matrix-valued quadrature sum on one composite cell, weighted by the kernel `κ` and the
rescaled rule weights. -/
def compositeCellSum {I : Type} [Fintype I] [DecidableEq I] {Q M : ℕ}
    (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) (Φ : ℝ → Matrix I I ℂ)
    (m : Fin M) : Matrix I I ℂ :=
  ∑ q : Fin Q,
    (((((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
      κ (compositeNodeAt K node m q)) • Φ (compositeNodeAt K node m q))

/-- The sum of `compositeCellSum` over all cells in the symmetric cutoff grid. -/
def compositeSum {I : Type} [Fintype I] [DecidableEq I] {Q M : ℕ}
    (K : ℕ) (node weight : Fin Q → ℝ) (κ : ℝ → ℂ) (Φ : ℝ → Matrix I I ℂ) :
    Matrix I I ℂ :=
  ∑ m : Fin M, compositeCellSum K node weight κ Φ m

/-- The complex coefficient at each cell and node, given by the half cell width times the
reference weight and sampled kernel value. -/
def compositeCoefficients {Q M : ℕ} (K : ℕ) (node weight : Fin Q → ℝ)
    (κ : ℝ → ℂ) : Fin M → Fin Q → ℂ :=
  fun m q => (((compositeCellWidth K M / 2 : ℝ) : ℂ) * ((weight q : ℝ) : ℂ)) *
    κ (compositeNodeAt K node m q)

/-- The principal-power LCHS integrand `highKernelG β k` times the ordered evolution generated
by `Complex.I • (H u + k • L u)`. -/
noncomputable def lchsIntegrand {I : Type} [Fintype I] [DecidableEq I]
    (β : ℝ) (L H : ℝ → Matrix I I ℂ) (s t : ℝ) : ℝ → Matrix I I ℂ :=
  fun k => highKernelG β k •
    orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t

/-- The dissipative generator field `L u + Complex.I • H u`. -/
noncomputable def lchsGenerator {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) : ℝ → Matrix I I ℂ :=
  fun u => L u + Complex.I • H u

/-- The variation-of-constants source integral of `orderedEvolution A u t *ᵥ b u` from `s` to
`t`. -/
noncomputable def lchsSourceIntegral {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ) : QState I :=
  ∫ u in s..t, orderedEvolution A u t *ᵥ b u

/-- The ordered forced solution for generator `A`, source `b`, initial time `s`, and initial
vector `v`. -/
noncomputable def lchsForcedResponse {I : Type} [Fintype I] [DecidableEq I]
    (A : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s : ℝ) (v : QState I) (t : ℝ) : QState I :=
  orderedForcedSolution A b s v t

/-- The prescribed composite cell count `ceil (2 * K * exp(1) * T * Λ)`. -/
def compositeCellCount (T Λ : ℝ) (K : ℕ) : ℕ :=
  Nat.ceil (2 * K * Real.exp 1 * T * Λ)

/-- The prescribed number of nodes per cell, at least one, obtained from the logarithmic kernel
precision budget. -/
def compositeNodeCount (β K ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log ((8 / (3 * highKernelC β)) * K / ε) / Real.log 4))

/-- A record of the cutoff window, number of cells, nodes per cell, propagator evaluations, and
amplification rounds. -/
structure LchsCostLedger where

  window : ℕ

  cells : ℕ

  nodesPerCell : ℕ

  propagatorEvaluations : ℕ

  amplificationRounds : ℕ

/-- The cost record for the prescribed composite grid, with `M * Q` propagator evaluations and
zero amplification rounds. -/
noncomputable def compositeCostLedger (β : ℝ) (T Λ : ℝ) (K : ℕ) (ε : ℝ) : LchsCostLedger :=
  let M := compositeCellCount T Λ K
  let Q := compositeNodeCount β K ε
  ⟨K, M, Q, M * Q, 0⟩

/-- Finite Gibbs-model input consisting of an energy function, an observable, a temperature
parameter, and a filter threshold. -/
structure GibbsInput (X : Type) where

  energy : X → ℝ

  observable : X → ℝ

  temperature : ℝ

  filterLevel : ℝ

/-- The finite sum of Boltzmann weights `Real.exp (-g.energy x / g.temperature)`. -/
noncomputable def partitionFunction {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, Real.exp (-g.energy x / g.temperature)

/-- The Boltzmann weight of `x` divided by `partitionFunction g`. -/
noncomputable def gibbsProbability {X : Type} [Fintype X] (g : GibbsInput X) (x : X) : ℝ :=
  Real.exp (-g.energy x / g.temperature) / partitionFunction g

/-- The energy-threshold event `g.energy x ≤ g.filterLevel`. -/
def filterEvent {X : Type} (g : GibbsInput X) (x : X) : Prop :=
  g.energy x ≤ g.filterLevel

/-- The sum of the Gibbs weights over states satisfying `filterEvent g`. -/
noncomputable def filterSuccessProbability {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, if filterEvent g x then gibbsProbability g x else 0

/-- The finite Gibbs-weighted sum of the observable values. -/
noncomputable def gibbsObservableExpectation {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, gibbsProbability g x * g.observable x

/-- The positive observable scale `∑ x, |g.observable x| + 1`. -/
noncomputable def observableRange {X : Type} [Fintype X] (g : GibbsInput X) : ℝ :=
  ∑ x, |g.observable x| + 1

/-- The integer ceiling of `log (2 / δ) / (2 * log (1 + ε / (2 * observableRange g)))`. -/
def gibbsSampleCount {X : Type} [Fintype X] (g : GibbsInput X) (ε δ : ℝ) : ℕ :=
  Nat.ceil (Real.log (2 / δ) / (2 * Real.log (1 + ε / (2 * observableRange g))))

end Qatlib.Concepts.LchsSimulation.Quadrature
