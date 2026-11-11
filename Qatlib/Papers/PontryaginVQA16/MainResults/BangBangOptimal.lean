/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Pontryagin bang-bang endpoint lemma (claim `c001`)

Source: Zhi-Cheng Yang, Armin Rahmani, Alireza Shabani, Hartmut Neven,
Claudio Chamon, *Optimizing Variational Quantum Algorithms using Pontryagin's
Minimum Principle*, arXiv:1607.06473v3 (11 March 2017), Sec. III.A, p. 3,
Eq. (5) and the paragraph immediately following it:

> An important consequence of Eq. (5) is that if the equations of motion for
> `x`, and consequently the optimal-control Hamiltonian `H`, are linear in `g`,
> generically, the optimal protocol is bang-bang, i.e., at any time during the
> evolution we have `g*_α(t) = g^min_α` or `g*_α(t) = g^max_α`.

The paper's argument is the following.  For fixed `x*` and costate `p*` the
optimal-control Hamiltonian is affine in the independent controls,
`H(x*, p*, g) = c + ∑_α a_α g_α`.  The minimum of a linear function over the
box `∏_α [g^min_α, g^max_α]` is attained at a vertex, and every coordinate whose
coefficient `a_α` is nonzero is pinned to an endpoint of its own interval; the
only escape is `a_α = 0` on a whole interval (the paper calls this
"nongeneric").

This module formalises exactly that argument.  It does not claim the physical
derivation of the optimal-control Hamiltonian; it proves the pointwise optimal
control statement that the paper applies at every time `0 < t < T`.  The
time-ordered propagator entry point for the closed-system dynamics
`|ψ(T)⟩ = T exp(-i ∫_0^T H_g(t) dt)|ψ(0)⟩` (Eq. (2)) is the existing frozen
module `QuantumAlgorithmDev.Foundations.TimeEvolution.DysonPropagator.ContractiveDuhamel`
(its constant-generator evolution and its identification with the Dyson order
are `evolution` and `evolution_eq_ordered`), which is quoted here only as the
semantic anchor of the dynamics — no statement of that module is re-proved.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.PontryaginVQA16.MainResults.BangBangOptimal

/-- The optimal-control Hamiltonian of Eq. (5) when it is affine in the
controls `u : ι → ℝ`, written in the normal form `c + ∑ α, a α * u α`.
`a α` is the coefficient of the control `g_α`, and `c` collects everything
independent of the controls (in the paper: the terms at `g = 0`). -/
def affineCost {ι : Type*} [Fintype ι] (a : ι → ℝ) (c : ℝ) (u : ι → ℝ) : ℝ :=
  c + ∑ i, a i * u i

/-- The admissible control box of Eq. (3): every control moves independently
in its own interval `[lo i, hi i]`. -/
def controlBox {ι : Type*} (lo hi : ι → ℝ) : Set (ι → ℝ) :=
  {u | ∀ i, lo i ≤ u i ∧ u i ≤ hi i}

/-- The vertex of the control box selected by the sign of each coefficient:
positive coefficients take the lower endpoint, all others the upper endpoint.
This is the "bang-bang" candidate. -/
def vertexControl {ι : Type*} [Fintype ι] (lo hi a : ι → ℝ) (i : ι) : ℝ :=
  if 0 ≤ a i then lo i else hi i

/-- A vertex of the box is admissible whenever every interval is nonempty. -/
theorem vertexControl_mem {ι : Type*} [Fintype ι] {lo hi a : ι → ℝ}
    (h : ∀ i, lo i ≤ hi i) : vertexControl lo hi a ∈ controlBox lo hi := by
  intro i
  unfold vertexControl
  split_ifs with h0
  · exact ⟨le_rfl, h i⟩
  · exact ⟨h i, le_rfl⟩

/-- The vertex control is optimal: every admissible control has cost at least
that of `vertexControl`.  This is the attainment half of the bang-bang
statement (Eq. (5)). -/
theorem affineCost_vertex_le {ι : Type*} [Fintype ι] {lo hi a : ι → ℝ} {c : ℝ}
    {u : ι → ℝ} (hu : u ∈ controlBox lo hi) :
    affineCost a c (vertexControl lo hi a) ≤ affineCost a c u := by
  unfold affineCost
  have hsum :
      ∑ i, a i * (vertexControl lo hi a i - u i) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    unfold vertexControl
    split_ifs with h0
    · exact mul_nonpos_of_nonneg_of_nonpos h0 (sub_nonpos.mpr (hu i).1)
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.mp h0)) (sub_nonneg.mpr (hu i).2)
  have hdiff :
      (c + ∑ i, a i * vertexControl lo hi a i) - (c + ∑ i, a i * u i)
        = ∑ i, a i * (vertexControl lo hi a i - u i) := by
    calc
      (c + ∑ i, a i * vertexControl lo hi a i) - (c + ∑ i, a i * u i)
          = (∑ i, a i * vertexControl lo hi a i) - ∑ i, a i * u i := by ring
      _ = ∑ i, (a i * vertexControl lo hi a i - a i * u i) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i, a i * (vertexControl lo hi a i - u i) := by
        exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-- **Existence half of the bang-bang theorem.**  If every control interval is
nonempty, the box admits a vertex at which the affine optimal-control
Hamiltonian is minimal. -/
theorem exists_vertex_minimizer {ι : Type*} [Fintype ι] {lo hi a : ι → ℝ} {c : ℝ}
    (h : ∀ i, lo i ≤ hi i) :
    ∃ u ∈ controlBox lo hi,
      ∀ v ∈ controlBox lo hi, affineCost a c u ≤ affineCost a c v :=
  ⟨vertexControl lo hi a, vertexControl_mem h,
    fun _ hv => affineCost_vertex_le hv⟩

/-- Replacing one coordinate of a control by `x` changes the affine cost by
exactly the coefficient times the displacement.  This is the coordinate-exchange
computation underlying the separating hyperplane argument. -/
theorem affineCost_update_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (c : ℝ) (u : ι → ℝ) (i : ι) (x : ℝ) :
    affineCost a c (Function.update u i x) - affineCost a c u
      = a i * (x - u i) := by
  unfold affineCost
  have hsum :
      (∑ j, a j * Function.update u i x j) - ∑ j, a j * u j
        = ∑ j, (a j * Function.update u i x j - a j * u j) := by
    rw [Finset.sum_sub_distrib]
  rw [add_sub_add_left_eq_sub, hsum, Finset.sum_eq_single i]
  · simp only [Function.update_self]
    ring
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Separating half of the bang-bang theorem.**  Every minimiser of the affine
cost over an independent control box is forced to an endpoint of its interval
in each coordinate whose coefficient is nonzero.  A vanishing coefficient is
precisely the non-generic caveat of the paper: then the coordinate may stay in
the interior. -/
theorem minimizer_endpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {lo hi a : ι → ℝ} {c : ℝ} {u : ι → ℝ}
    (hu : u ∈ controlBox lo hi)
    (hmin : ∀ v ∈ controlBox lo hi, affineCost a c u ≤ affineCost a c v)
    {i : ι} (hai : a i ≠ 0) :
    u i = lo i ∨ u i = hi i := by
  rcases lt_or_gt_of_ne hai with hneg | hpos
  · -- negative coefficient: the upper endpoint is forced
    right
    by_contra hne
    have hlt : u i < hi i := lt_of_le_of_ne (hu i).2 hne
    let v : ι → ℝ := Function.update u i (hi i)
    have hv : v ∈ controlBox lo hi := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp [v, Function.update_self]
        exact le_trans (hu j).1 (hu j).2
      · simp [v, Function.update_of_ne hji]
        exact hu j
    have hle := hmin v hv
    have hdiff : affineCost a c v - affineCost a c u = a i * (hi i - u i) :=
      affineCost_update_sub a c u i (hi i)
    have hneg' : affineCost a c v < affineCost a c u := by
      have : a i * (hi i - u i) < 0 :=
        mul_neg_of_neg_of_pos hneg (sub_pos.mpr hlt)
      linarith
    linarith
  · -- positive coefficient: the lower endpoint is forced
    left
    by_contra hne
    have hlt : lo i < u i := lt_of_le_of_ne (hu i).1 (Ne.symm hne)
    let v : ι → ℝ := Function.update u i (lo i)
    have hv : v ∈ controlBox lo hi := by
      intro j
      by_cases hji : j = i
      · subst hji
        simp [v, Function.update_self]
        exact le_trans (hu j).1 (hu j).2
      · simp [v, Function.update_of_ne hji]
        exact hu j
    have hle := hmin v hv
    have hdiff : affineCost a c v - affineCost a c u = a i * (lo i - u i) :=
      affineCost_update_sub a c u i (lo i)
    have hneg' : affineCost a c v < affineCost a c u := by
      have : a i * (lo i - u i) < 0 :=
        mul_neg_of_pos_of_neg hpos (sub_neg.mpr hlt)
      linarith
    linarith

/-- **Claim `c001`: bang-bang optimal protocols for controls entering linearly.**

If at a given time the optimal-control Hamiltonian of Eq. (5) is affine in the
independent controls `g` over the box of Eq. (3), and the optimal control `g*`
minimises it, then every control whose coefficient is nonzero sits at an
endpoint of its interval.  No hypothesis on the number of variational
parameters is used, matching the paper's remark that the conclusion holds
"regardless of the number of variational parameters". -/
theorem bangBang_optimal_protocol {ι : Type*} [Fintype ι] [DecidableEq ι]
    {lo hi a : ι → ℝ} {c : ℝ} {u : ι → ℝ}
    (hu : u ∈ controlBox lo hi)
    (hmin : ∀ v ∈ controlBox lo hi, affineCost a c u ≤ affineCost a c v)
    (hgen : ∀ i, a i ≠ 0) :
    ∀ i, u i = lo i ∨ u i = hi i :=
  fun i => minimizer_endpoint hu hmin (hgen i)

/-- **Claim `c001`, time-dependent form.**  The bang-bang conclusion holds "at
any time during the evolution": for every time slice `t` at which the optimal
control minimises an affine optimal-control Hamiltonian with nonzero
coefficients, the control at that time is at an endpoint. -/
theorem bangBang_at_every_time {T ι : Type*} [Fintype ι] [DecidableEq ι]
    {lo hi : ι → ℝ} (u : T → ι → ℝ) (a : T → ι → ℝ) (c : T → ℝ)
    (hu : ∀ t, u t ∈ controlBox lo hi)
    (hmin : ∀ (t : T) (v : ι → ℝ), v ∈ controlBox lo hi →
      affineCost (a t) (c t) (u t) ≤ affineCost (a t) (c t) v)
    (hgen : ∀ (t : T) (i : ι), a t i ≠ 0) :
    ∀ (t : T) (i : ι), u t i = lo i ∨ u t i = hi i :=
  fun t i => minimizer_endpoint (hu t) (hmin t) (hgen t i)

/-! ## From linear equations of motion to an affine optimal-control Hamiltonian

Pontryagin's Hamiltonian of an evolution `ẋ = f(x, u)` is `H = p · f(x, u)`.
If the dynamics is linear in the controls,
`f(x, u) = B₀ x + ∑ α, u α • B α x`, then for fixed `(x, p)` the map
`u ↦ H(x, p, u)` is affine, with coefficient `p (B α x)` on the control `u α`.
This is the bridge that turns the paper's "the equations of motion are linear in
`g`" (Eqs. (6), (7) for the closed system; Eq. (8) for the Lindblad case) into
the hypothesis of `bangBang_optimal_protocol`. -/

/-- The control-linear vector field
`f(x, u) = B₀ x + ∑ α, u α • B α x`, evaluated at the state `x`. -/
def linearControlField {ι X : Type*} [Fintype ι] [AddCommGroup X] [Module ℝ X]
    (B₀ : X →ₗ[ℝ] X) (B : ι → X →ₗ[ℝ] X) (u : ι → ℝ) (x : X) : X :=
  B₀ x + ∑ i, u i • B i x

/-- The optimal-control Hamiltonian `H(x, p, u) = p (f(x, u))` of a
control-linear vector field, evaluated at the state `x`. -/
def optimalControlHamiltonian {ι X : Type*} [Fintype ι] [AddCommGroup X]
    [Module ℝ X] (B₀ : X →ₗ[ℝ] X) (B : ι → X →ₗ[ℝ] X) (p : X →ₗ[ℝ] ℝ)
    (u : ι → ℝ) (x : X) : ℝ :=
  p (linearControlField B₀ B u x)

/-- **Linearity of the equations of motion gives the affine optimal-control
Hamiltonian.**  `H(x, p, u) = p (B₀ x) + ∑ α, u α * p (B α x)`, so the
coefficient multiplying the control `u α` is the costate pairing `p (B α x)` of
the corresponding generator. -/
theorem optimalControlHamiltonian_affine {ι X : Type*} [Fintype ι]
    [AddCommGroup X] [Module ℝ X] (B₀ : X →ₗ[ℝ] X) (B : ι → X →ₗ[ℝ] X)
    (p : X →ₗ[ℝ] ℝ) (u : ι → ℝ) (x : X) :
    optimalControlHamiltonian B₀ B p u x
      = affineCost (fun i => p (B i x)) (p (B₀ x)) u := by
  unfold optimalControlHamiltonian linearControlField affineCost
  rw [map_add, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- **Claim `c001` in optimal-control form.**  For a state dynamics that is
linear in the controls, the optimal control over the box of Eq. (3) is
bang-bang in every coordinate whose costate coefficient `p (B α x)` does not
vanish.  This is the exact statement the paper derives from Eq. (5) for the
closed-system equations of motion (6), (7). -/
theorem bangBang_of_linearDynamics {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup X] [Module ℝ X] {B₀ : X →ₗ[ℝ] X} {B : ι → X →ₗ[ℝ] X}
    {p : X →ₗ[ℝ] ℝ} {x : X} {lo hi : ι → ℝ} {u : ι → ℝ}
    (hu : u ∈ controlBox lo hi)
    (hmin : ∀ v ∈ controlBox lo hi,
      optimalControlHamiltonian B₀ B p u x ≤
        optimalControlHamiltonian B₀ B p v x)
    (hgen : ∀ i, p (B i x) ≠ 0) :
    ∀ i, u i = lo i ∨ u i = hi i := by
  have hmin' : ∀ v ∈ controlBox lo hi,
      affineCost (fun i => p (B i x)) (p (B₀ x)) u ≤
        affineCost (fun i => p (B i x)) (p (B₀ x)) v := by
    intro v hv
    simpa only [optimalControlHamiltonian_affine] using hmin v hv
  exact bangBang_optimal_protocol hu hmin' hgen

end Qatlib.Papers.PontryaginVQA16.MainResults.BangBangOptimal
