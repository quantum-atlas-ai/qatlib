/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Finite decision trees and cube laws

`FiniteDecisionTree` records deterministic Boolean queries together with execution traces and
acceptance polynomials. The module also packages product and slice weights as finite probability
laws and defines acceptance, query cost, and polynomials for randomly seeded trees.

These definitions connect concrete decision trees to the polynomial method for query complexity
in [BealsEtAl2001].

## Main statements

* `FiniteDecisionTree.polynomial`: the recursively constructed acceptance polynomial.
* `biasedCubeLaw` and `sliceCubeLaw`: finite probability laws on the Boolean cube.
* `randomizedTreePolynomial`: the seed weighted acceptance polynomial.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.Concentration

/-- A finite Boolean decision tree with output leaves and nodes querying an input coordinate. -/
inductive FiniteDecisionTree (n : ℕ) where
  | leaf (output : Bool)
  | query (address : Fin n) (onFalse onTrue : FiniteDecisionTree n)
  deriving Repr

namespace FiniteDecisionTree

/-- Execute a decision tree, returning its Boolean output and the ordered list of queried
coordinates and answers. -/
def execute {n : ℕ} : FiniteDecisionTree n → (Fin n → Bool) → Bool × List (Fin n × Bool)
  | .leaf b, _ => (b, [])
  | .query i l r, x =>
    let b := x i
    let next := if b then r.execute x else l.execute x
    (next.1, (i,b)::next.2)

/-- The maximum number of query nodes along a path from the root to a leaf. -/
def depth {n : ℕ} : FiniteDecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max l.depth r.depth

/-- The Boolean output of executing a decision tree on an input. -/
def output {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) : Bool := (t.execute x).1

/-- The length of the query trace produced by execution on an input. -/
def queries {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) : ℕ := (t.execute x).2.length

/-- Relabel every query coordinate by a permutation. -/
def relabel {n : ℕ} (e : Equiv.Perm (Fin n)) : FiniteDecisionTree n → FiniteDecisionTree n
  | .leaf b => .leaf b
  | .query i l r => .query (e i) (relabel e l) (relabel e r)

/-- The real valued indicator that a decision tree outputs true. -/
noncomputable def accept {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) : ℝ :=
  if t.output x then 1 else 0

/-- The real multivariate acceptance polynomial obtained by interpolating between the two
branches at each query node. -/
noncomputable def polynomial {n : ℕ} : FiniteDecisionTree n → MvPolynomial (Fin n) ℝ
  | .leaf b => MvPolynomial.C (if b then 1 else 0)
  | .query i l r => (1-MvPolynomial.X i)*l.polynomial+MvPolynomial.X i*r.polynomial

end FiniteDecisionTree

noncomputable section
open scoped BigOperators

/-- The finite distribution associated with a nonnegative normalized Boolean cube weight. -/
def cubeLaw (n : ℕ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w) : FinDist (Fin n → Bool) where
  prob := w
  nonneg := hw.1
  sum_one := hw.2

/-- The Boolean distribution assigning probability `p` to true and `1 - p` to false. -/
def bernoulliLaw (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist Bool where
  prob b := if b then p else 1-p
  nonneg b := by cases b <;> dsimp <;> linarith [hp.1,hp.2]
  sum_one := by simp

/-- The product law of `n` independent Bernoulli coordinates with success probability `p`. -/
def biasedCubeLaw (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist (Fin n → Bool) :=
  independent (fun _ : Fin n => bernoulliLaw p hp)

/-- The uniform finite distribution on Boolean inputs of Hamming weight `k`. -/
def sliceCubeLaw (n k : ℕ) (hk : k ≤ n) : FinDist (Fin n → Bool) :=
  cubeLaw n (sliceWeight n k) (sliceWeight_cubeWeight n k hk)

/-- The product finite law of an independent random seed and Boolean input. -/
def seedInputLaw {Ω : Type*} [Fintype Ω] {n : ℕ} (p : FinDist Ω)
    (q : FinDist (Fin n → Bool)) : FinDist (Ω × (Fin n → Bool)) where
  prob z := p.prob z.1 * q.prob z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.sum_one, mul_one]
    exact p.sum_one

/-- The maximum depth of a finite family of decision trees. -/
def forestDepth {Ω : Type*} [Fintype Ω] {n : ℕ} (t : Ω → FiniteDecisionTree n) : ℕ :=
  Finset.univ.sup (fun ω => (t ω).depth)

/-- The seed averaged acceptance indicator of a family of decision trees. -/
def randomizedTreeAccept {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) : ℝ :=
  p.expect (fun ω => (t ω).accept x)

/-- The expected query count over the seed law at a fixed Boolean input. -/
def randomizedTreeQueries {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) : ℝ :=
  p.expect (fun ω => ((t ω).queries x : ℝ))

/-- The seed weighted sum of the acceptance polynomials of a family of decision trees. -/
def randomizedTreePolynomial {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) : MvPolynomial (Fin n) ℝ :=
  ∑ ω, MvPolynomial.C (p.prob ω) * (t ω).polynomial

end
end Qatlib.Concepts.ProbabilityCore.Concentration
