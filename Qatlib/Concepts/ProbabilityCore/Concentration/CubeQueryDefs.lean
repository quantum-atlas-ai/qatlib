/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeDistribution
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.Concentration

inductive FiniteDecisionTree (n : ℕ) where
  | leaf (output : Bool)
  | query (address : Fin n) (onFalse onTrue : FiniteDecisionTree n)
  deriving Repr

namespace FiniteDecisionTree

def execute {n : ℕ} : FiniteDecisionTree n → (Fin n → Bool) → Bool × List (Fin n × Bool)
  | .leaf b, _ => (b, [])
  | .query i l r, x =>
    let b := x i
    let next := if b then r.execute x else l.execute x
    (next.1, (i,b)::next.2)

def depth {n : ℕ} : FiniteDecisionTree n → ℕ
  | .leaf _ => 0
  | .query _ l r => 1 + max l.depth r.depth

def output {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) : Bool := (t.execute x).1

def queries {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) : ℕ := (t.execute x).2.length

def relabel {n : ℕ} (e : Equiv.Perm (Fin n)) : FiniteDecisionTree n → FiniteDecisionTree n
  | .leaf b => .leaf b
  | .query i l r => .query (e i) (relabel e l) (relabel e r)

noncomputable def accept {n : ℕ} (t : FiniteDecisionTree n) (x : Fin n → Bool) : ℝ :=
  if t.output x then 1 else 0

noncomputable def polynomial {n : ℕ} : FiniteDecisionTree n → MvPolynomial (Fin n) ℝ
  | .leaf b => MvPolynomial.C (if b then 1 else 0)
  | .query i l r => (1-MvPolynomial.X i)*l.polynomial+MvPolynomial.X i*r.polynomial

end FiniteDecisionTree

noncomputable section
open scoped BigOperators

def cubeLaw (n : ℕ) (w : (Fin n → Bool) → ℝ) (hw : CubeWeight n w) : FinDist (Fin n → Bool) where
  prob := w
  nonneg := hw.1
  sum_one := hw.2

def bernoulliLaw (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist Bool where
  prob b := if b then p else 1-p
  nonneg b := by cases b <;> dsimp <;> linarith [hp.1,hp.2]
  sum_one := by simp

def biasedCubeLaw (n : ℕ) (p : ℝ) (hp : p ∈ Set.Icc 0 1) : FinDist (Fin n → Bool) :=
  independent (fun _ : Fin n => bernoulliLaw p hp)

def sliceCubeLaw (n k : ℕ) (hk : k ≤ n) : FinDist (Fin n → Bool) :=
  cubeLaw n (sliceWeight n k) (sliceWeight_cubeWeight n k hk)

def seedInputLaw {Ω : Type*} [Fintype Ω] {n : ℕ} (p : FinDist Ω)
    (q : FinDist (Fin n → Bool)) : FinDist (Ω × (Fin n → Bool)) where
  prob z := p.prob z.1 * q.prob z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.sum_one, mul_one]
    exact p.sum_one

def forestDepth {Ω : Type*} [Fintype Ω] {n : ℕ} (t : Ω → FiniteDecisionTree n) : ℕ :=
  Finset.univ.sup (fun ω => (t ω).depth)

def randomizedTreeAccept {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) : ℝ :=
  p.expect (fun ω => (t ω).accept x)

def randomizedTreeQueries {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) (x : Fin n → Bool) : ℝ :=
  p.expect (fun ω => ((t ω).queries x : ℝ))

def randomizedTreePolynomial {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : FinDist Ω) (t : Ω → FiniteDecisionTree n) : MvPolynomial (Fin n) ℝ :=
  ∑ ω, MvPolynomial.C (p.prob ω) * (t ω).polynomial

end
end Qatlib.Concepts.ProbabilityCore.Concentration
