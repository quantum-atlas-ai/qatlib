/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphStationary.StationaryLaw
public import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.GraphLaplacian
public import Qatlib.Concepts.DirichletForm.EnergyIdentity
public import Qatlib.Concepts.GraphCutTrial.CutEnergyBound
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra

open Qatlib
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open Qatlib.Concepts.DirichletForm.EnergyIdentity
open Qatlib.Concepts.GraphCutTrial.CutEnergyBound
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def adjWeight (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if G.Adj x y then 1 else 0

def neighborCount (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℝ :=
  ∑ y, adjWeight G x y

omit [DecidableEq V] in

/-- The neighbor count equals the graph degree at each vertex. -/
lemma neighborCount_eq_degree (x : V) : neighborCount G x = degree G x := by
  unfold neighborCount adjWeight
  rw [← SimpleGraph.degree_eq_sum_if_adj (R := ℝ) G x]
  exact (Qatlib.Concepts.GraphLaplacian.LaplacianPsd.degree_eq_mathlib G x).symm

def sqrtDegree (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) : ℝ :=
  Real.sqrt (degree G x)

def normalizedAdj (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if G.Adj x y then (sqrtDegree G x)⁻¹ * (sqrtDegree G y)⁻¹ else 0

def normalizedLaplacian (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  fun x y => if x = y then (if degree G x = 0 then 0 else 1) else -normalizedAdj G x y

def degreeScaled (G : SimpleGraph V) [DecidableRel G.Adj] (u : V → ℝ) : V → ℝ :=
  fun x => sqrtDegree G x * u x

def normalizedRayleigh (G : SimpleGraph V) [DecidableRel G.Adj] (u : V → ℝ) : ℝ :=
  (∑ x, ∑ y, degreeScaled G u x * normalizedLaplacian G x y * degreeScaled G u y) /
    (∑ x, (degreeScaled G u x)^2)

def degreeMeanZero (G : SimpleGraph V) [DecidableRel G.Adj] (u : V → ℝ) : Prop :=
  ∑ x, degree G x * u x = 0

def cutConductance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  flow G S / mass G S

def HasConductanceBound (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℝ) : Prop :=
  ∀ S : Finset V, 0 < mass G S → mass G S ≤ 1/2 → h ≤ cutConductance G S

def LazyChainGap (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ) : Prop :=
  ∀ f : V → ℝ, mean G f = 0 → δ ≤ 1 → δ * variance G f ≤ energy G f

def IsDegreeRegular (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Prop :=
  ∀ x, degree G x = d

def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ Sᶜ, (if G.Adj x y then (1 : ℝ) else 0)

def setVolume (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℝ :=
  ∑ x ∈ S, degree G x

def stationarySupport (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun x => 0 < degree G x

def bipartiteHalf (a : ℕ) : ℕ := 2 ^ (a - 1)

def bipartiteAdj (a : ℕ) (x y : Fin (2 ^ a)) : Bool :=
  decide ((x.val < bipartiteHalf a) ≠ (y.val < bipartiteHalf a))

def bipartiteGraph (a : ℕ) : SimpleGraph (Fin (2 ^ a)) where
  Adj x y := bipartiteAdj a x y = true
  symm := ⟨by
    intro x y h
    simp only [bipartiteAdj, decide_eq_true_eq] at h ⊢
    exact Ne.symm h⟩
  loopless := ⟨fun x h => by
    simp only [bipartiteAdj, decide_eq_true_eq] at h
    exact h rfl⟩

instance (a : ℕ) : DecidableRel (bipartiteGraph a).Adj := fun _ _ => by
  unfold bipartiteGraph SimpleGraph.Adj
  infer_instance

def bipartiteHalfIndicator (a : ℕ) (x : Fin (2 ^ a)) : ℝ :=
  if x.val < bipartiteHalf a then 1 else -1

def bipartiteLower (a : ℕ) : Finset (Fin (2 ^ a)) :=
  (Finset.univ : Finset (Fin (2 ^ a))).filter fun x => x.val < bipartiteHalf a

def bipartiteUpper (a : ℕ) : Finset (Fin (2 ^ a)) :=
  (Finset.univ : Finset (Fin (2 ^ a))).filter fun x => bipartiteHalf a ≤ x.val

def normalizedKernel (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if degree G x = 0 then (if x = y then 1 else 0)
  else (if G.Adj x y then (degree G x)⁻¹ else 0)

def separates (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ Sᶜ, ¬ G.Adj x y

def NormalizedChainBridge : Prop :=
  (∀ x y : V, kernel G x y
      = (if x = y then (1 / 2 : ℝ) else 0) + (1 / 2) * normalizedKernel G x y) ∧
  (∀ x : V, (∑ y, normalizedKernel G x y) = 1) ∧
  (∀ x y : V, volume G ≠ 0 →
      (stationary G x * normalizedKernel G x y = stationary G y * normalizedKernel G y x))

def NormalizedChainGapRelation : Prop :=
  (∀ S : Finset V, volume G ≠ 0 → separates G S → 0 < mass G S → mass G S < 1 →
      (mean G (centeredIndicator G S) = 0 ∧
        energy G (centeredIndicator G S) = 0 ∧
        0 < variance G (centeredIndicator G S))) ∧
  (∀ f : V → ℝ, volume G ≠ 0 → (mean G f = 0 ↔ degreeMeanZero G f))

def NormalizedChainCheegerUpper : Prop :=
  ∀ S : Finset V, volume G ≠ 0 → 0 < mass G S → mass G S ≤ 1/2 →
    ∃ f : V → ℝ, (mean G f = 0 ∧ 0 < variance G f ∧
      energy G f / variance G f ≤ 2 * cutConductance G S)

def NormalizedChainDegenerate : Prop :=
  (∀ x : V, degree G x = 0 →
      ((∀ y : V, normalizedKernel G x y = if x = y then 1 else 0) ∧
        (∀ y : V, normalizedLaplacian G x y = 0) ∧
        (volume G ≠ 0 → stationary G x = 0))) ∧
  (volume G = 0 →
      ((∀ x y : V, kernel G x y = if x = y then 1 else 0) ∧
        (∀ f : V → ℝ, energy G f = 0)))

def NormalizedChainCheeger : Prop :=
  NormalizedChainBridge G ∧ NormalizedChainGapRelation G ∧ NormalizedChainCheegerUpper G ∧
    NormalizedChainDegenerate G

def regPadLocal (w a : ℕ) (r : Reg a) : Reg w :=
  fun i => if h : (i : ℕ) < a then r ⟨i, h⟩ else false

def regCatLocal {a b : ℕ} (r : Reg a) (s : Reg b) : Reg (a + b) :=
  fun i => (finSumFinEquiv.symm i).elim r s

noncomputable def graphNeighborOfLocal (n : ℕ) (adj : Fin n → Fin n → Bool)
    (x : Fin n) (k : ℕ) : Fin n :=
  ((Finset.univ.filter (fun j => adj x j)).toList.getD k) x

end Qatlib.Concepts.QuantumGibbs.FormAlgebra
