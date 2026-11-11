/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# InductLearn16 — Lemma 1 (classical inductive decomposition)

Fixed source: Monràs--Sentís--Wittek, *Inductive supervised quantum learning*,
arXiv:1605.07541v2 (13 May 2017). Claim `InductLearn16.c001` ("Lemma 1",
main text p. 2; restated and proved as Lemma 4 in the Supplemental Material,
p. 11, Eqs. (37)--(46)).

The lemma says that every inductive learning protocol can be rewritten, without
changing its expected risk, as: first sample a deterministic classifier
`f : X → Y` from a distribution `T(f|A)` that may depend on the training set
`A`, and then apply `f` to each test instance through the deterministic channel
`Q(y|x,f) = δ_{y,f(x)}`.

The paper's proof (Lemma 4, Eqs. (42)--(45)) has two mathematical ingredients:

* the expected risk depends on the protocol only through its marginal map
  `P̄₁(y|A,x)` (Eq. (42)); and
* every stochastic map `X → Y` between finite sets is a convex combination of
  deterministic maps `Q_f(y|x) = δ_{y,f(x)}` (Eq. (43)).

We model the protocol by its marginal `StochasticMap` and formalize both
ingredients, obtaining the exact risk identity of Eq. (46).  For a finite input
set `X` and finite label set `Y` the convex coefficients are the product
distribution `f ↦ ∏ x, p(f x | x)`, whose marginals recover `p`.

Boundary: the formal statement works with the single-instance (marginal) risk
functional, exactly the object appearing in Eq. (42); the paper's `E[P|A]` is the
`n`-fold average of this functional over i.i.d. test instances, so the identity
proved here is precisely the content of the lemma.  Nothing about quantum
channels is used in this file.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.InductLearn16.MainResults

/-- A stochastic map `X → Y`: a nonnegative matrix whose row sums (over labels)
are one.  This is the marginal protocol `P̄₁(y|A,x)` of Eq. (40). -/
structure StochasticMap (X Y : Type*) [Fintype Y] where
  /-- The transition probability `x ↦ y`. -/
  prob : X → Y → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ prob x y
  /-- Every row is a probability distribution. -/
  sum_eq_one : ∀ x, ∑ y, prob x y = 1

namespace StochasticMap

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The coefficient of the deterministic classifier `f` in the convex
decomposition of `p`: the product distribution `∏ x, p(f x | x)`, i.e. the
measure `T(f|A) = μ_A(f)` of Eq. (43). -/
def classifierWeight (p : StochasticMap X Y) (f : X → Y) : ℝ :=
  ∏ x, p.prob x (f x)

/-- The classifier weights are nonnegative. -/
theorem classifierWeight_nonneg (p : StochasticMap X Y) (f : X → Y) :
    0 ≤ classifierWeight p f :=
  Finset.prod_nonneg fun x _ => p.nonneg x (f x)

/-- The classifier weights form a probability distribution: this is the
normalization used in Eq. (43). -/
theorem classifierWeight_sum_one (p : StochasticMap X Y) :
    ∑ f : X → Y, classifierWeight p f = 1 := by
  unfold classifierWeight
  rw [show (Finset.univ : Finset (X → Y)) =
      Fintype.piFinset (fun _ : X => (Finset.univ : Finset Y)) from
    (Fintype.piFinset_univ).symm]
  rw [Finset.sum_prod_piFinset (s := (Finset.univ : Finset Y))
    (g := fun x y => p.prob x y)]
  simp [p.sum_eq_one]

/-- Marginal recovery: the mixture of deterministic maps with weights
`classifierWeight` reproduces the original stochastic map.  This is Eq. (43),
written in the form used by Eq. (42). -/
theorem classifierWeight_marginal (p : StochasticMap X Y) (x₀ : X) (y₀ : Y) :
    ∑ f : X → Y, classifierWeight p f * (if f x₀ = y₀ then (1 : ℝ) else 0) =
      p.prob x₀ y₀ := by
  classical
  -- Replace the indicator by a product that singles out the input `x₀`.
  have hprod : ∀ f : X → Y,
      (∏ x, p.prob x (f x)) * (if f x₀ = y₀ then (1 : ℝ) else 0) =
        ∏ x, (p.prob x (f x) *
          (if x = x₀ then (if f x = y₀ then 1 else 0) else 1)) := by
    intro f
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_eq_single x₀]
    · simp
    · intro x _ hx
      simp [hx]
    · intro hx
      exact absurd (Finset.mem_univ x₀) hx
  calc ∑ f : X → Y, classifierWeight p f * (if f x₀ = y₀ then (1 : ℝ) else 0)
      = ∑ f : X → Y, ∏ x, (p.prob x (f x) *
          (if x = x₀ then (if f x = y₀ then 1 else 0) else 1)) := by
        unfold classifierWeight
        exact Finset.sum_congr rfl fun f _ => hprod f
    _ = ∑ f ∈ Fintype.piFinset (fun _ : X => (Finset.univ : Finset Y)),
          ∏ x, (p.prob x (f x) *
            (if x = x₀ then (if f x = y₀ then 1 else 0) else 1)) := by
        rw [Fintype.piFinset_univ]
    _ = ∏ x, ∑ y, (p.prob x y *
          (if x = x₀ then (if y = y₀ then 1 else 0) else 1)) := by
        rw [Finset.sum_prod_piFinset (s := (Finset.univ : Finset Y))
          (g := fun x y => p.prob x y *
            (if x = x₀ then (if y = y₀ then 1 else 0) else 1))]
    _ = p.prob x₀ y₀ := by
        rw [Finset.prod_eq_single x₀]
        · simp
        · intro x _ hx
          simp [hx, p.sum_eq_one x]
        · intro hx
          exact absurd (Finset.mem_univ x₀) hx

end StochasticMap

/-- Single-instance expected risk of a protocol with marginal `p` against the
data distribution `P`, for the risk weight `s`.  This is Eq. (42). -/
def expectedRisk {X Y : Type*} [Fintype X] [Fintype Y] (s : Y → Y → ℝ) (p : X → Y → ℝ)
    (P : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ y', s y y' * p x y * P x y'

/-- Risk of a single deterministic classifier `f`.  This is `E[Q_f|A]` in
Eq. (44). -/
def classifierRisk {X Y : Type*} [Fintype X] [Fintype Y] (s : Y → Y → ℝ) (f : X → Y)
    (P : X → Y → ℝ) : ℝ :=
  ∑ x, ∑ y', s (f x) y' * P x y'

/-- The deterministic classifier `f : X → Y` regarded as a stochastic map, i.e.
the channel `Q_f(y|x) = δ_{y,f(x)}` of Eq. (43). -/
def deltaMap {X Y : Type*} [DecidableEq Y] (f : X → Y) : X → Y → ℝ :=
  fun x y => if f x = y then (1 : ℝ) else 0

/-- Evaluation of the deterministic channel `deltaMap f`. -/
@[simp] theorem deltaMap_apply {X Y : Type*} [DecidableEq Y] (f : X → Y) (x : X) (y : Y) :
    deltaMap f x y = if f x = y then (1 : ℝ) else 0 := rfl

/-- The expected risk of Eq. (42), regarded as a linear functional of the
marginal `p` for fixed risk weight `s` and data distribution `P`.  Linearity is
exactly what lets the convex decomposition of Eq. (43) pass to the risk in
Eq. (46). -/
def riskLinear {X Y : Type*} [Fintype X] [Fintype Y] (s : Y → Y → ℝ) (P : X → Y → ℝ) :
    (X → Y → ℝ) →ₗ[ℝ] ℝ where
  toFun p := ∑ x, ∑ y, ∑ y', s y y' * p x y * P x y'
  map_add' p q := by
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro y' _
    ring

/-- Linearity of the expected risk in a convex mixture of deterministic
classifiers: if the marginal `p` is written as the mixture `w` of the
deterministic maps `Q_f(y|x) = δ_{y,f(x)}`, then the protocol risk is the same
mixture of the classifier risks.  This is Eqs. (43)--(46). -/
theorem expectedRisk_eq_mixture {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (w : (X → Y) → ℝ) (p : X → Y → ℝ)
    (hp : ∀ x y, p x y = ∑ f, w f * (if f x = y then (1 : ℝ) else 0))
    (s : Y → Y → ℝ) (P : X → Y → ℝ) :
    expectedRisk s p P = ∑ f, w f * classifierRisk s f P := by
  classical
  -- The risk of the deterministic map `Q_f(y|x) = δ_{y,f(x)}` is the classifier risk.
  have hdeltaRisk : ∀ f : X → Y,
      riskLinear s P (fun x y => if f x = y then (1 : ℝ) else 0) = classifierRisk s f P := by
    intro f
    show (∑ x, ∑ y, ∑ y',
        s y y' * (if f x = y then (1 : ℝ) else 0) * P x y') =
      ∑ x, ∑ y', s (f x) y' * P x y'
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro y' _
    rw [Finset.sum_eq_single (f x)]
    · rw [if_pos rfl]; ring
    · intro y _ hy
      rw [if_neg (Ne.symm hy)]; ring
    · intro h
      exact absurd (Finset.mem_univ (f x)) h
  -- The marginal `p` is the convex mixture of the deterministic maps.
  have hp_mix : p = ∑ f, w f • (fun x y => if f x = y then (1 : ℝ) else 0) := by
    funext x y
    rw [hp x y]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc expectedRisk s p P = riskLinear s P p := rfl
    _ = riskLinear s P (∑ f, w f • (fun x y => if f x = y then (1 : ℝ) else 0)) := by
        rw [hp_mix]
    _ = ∑ f, w f • riskLinear s P (fun x y => if f x = y then (1 : ℝ) else 0) := by
        rw [map_sum]
        apply Finset.sum_congr rfl; intro f _
        rw [map_smul]
    _ = ∑ f, w f * classifierRisk s f P := by
        apply Finset.sum_congr rfl; intro f _
        rw [hdeltaRisk f, smul_eq_mul]

/-- **Lemma 1 (classical inductive decomposition).**  For every inductive
learning protocol (modelled by its marginal stochastic map `p a` for each
training set `a`), there is a family of probability distributions `T(·|a)` over
deterministic classifiers `f : X → Y` such that, for every data distribution
`P`, the expected risk of the protocol equals the mixture, with weights `T`,
of the risks of the deterministic classifiers.  These classifiers are exactly
the channels `Q(y|x,f) = δ_{y,f(x)}` of the paper. -/
theorem inductive_protocol_decomposition {X Y A : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype A] (p : A → StochasticMap X Y) (s : Y → Y → ℝ) :
    ∃ T : A → (X → Y) → ℝ,
      (∀ a f, 0 ≤ T a f) ∧
      (∀ a, ∑ f, T a f = 1) ∧
      (∀ a (P : X → Y → ℝ),
        expectedRisk s (p a).prob P = ∑ f, T a f * classifierRisk s f P) := by
  refine ⟨fun a => (p a).classifierWeight, ?_, ?_, ?_⟩
  · intro a f
    exact StochasticMap.classifierWeight_nonneg (p a) f
  · intro a
    exact StochasticMap.classifierWeight_sum_one (p a)
  · intro a P
    exact expectedRisk_eq_mixture (fun f => (p a).classifierWeight f) (p a).prob
      (fun x y => by rw [StochasticMap.classifierWeight_marginal])
      s P

end Qatlib.Papers.InductLearn16.MainResults
