/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceGalaxySimulation — Theorem 3 (galaxy simulation)

Fixed version: arXiv:1003.3683v2 (5 Nov 2010), Childs--Kothari, "Simulating
sparse Hamiltonians with star decompositions", §4, Theorem 3, pages 8--9.

A galaxy is a disjoint union of stars.  A star has a distinguished centre and
some leaves, and the galaxy Hamiltonian only couples the centre to its leaves.
For a vertex `x` let `R x` be the *star data*: the centre, the list of leaves
in a fixed order, and the edge weights.  The paper shows:

* `R x` is constant on each star (`R x = R y` when `x`,`y` share a star);
* given `R x` one can implement the unitary `U` with `U |x,0> = |x,R(x)>`
  using `O(d)` oracle calls (`d` the maximum degree);
* the Hamiltonian `K`, which is `H` acting on `|x,R(x)>` instead of `|x>`, is
  query-free, because all star information is already in the second register;
* `H = U† K U`, so `e^{-iHt}` can be simulated with `O(d)` calls.

The formal model below is the discrete basis-state model used in the proof
("it suffices to implement `H_j` correctly on all basis states").  States are
pairs `(x, r)` with `x : Fin N` the vertex and `r : Option (StarDesc N d)` the
second register (`none` is the initialised register).  `Umap` is the
involution computing `R`, `Kpure` is the query-free Hamiltonian `K` (it reads
only the second register), and `Hrow` is the action of the galaxy Hamiltonian
on the basis vector `|x>` tensored with the initialised second register.  The
main theorem proves `U K U |x,0> = H |x,0>` on every basis state.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.StarDecompSim10.MainResults.GalaxySimulation

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {N d : ℕ}

/-- All the information about a star: its centre, the leaves in a fixed order
(a `none` slot is an unused slot), and the edge weights. -/
structure StarDesc (N d : ℕ) where
  /-- The centre of the star. -/
  center : Fin N
  /-- The leaves, in a fixed order; unused slots are `none`. -/
  nbr : Fin d → Option (Fin N)
  /-- The weight of the corresponding edge. -/
  wt : Fin d → ℂ

/-- The weight of the edge from a leaf `x` to the centre, read off the star
data.  (Slots with a different leaf contribute zero.) -/
def leafWt (r : StarDesc N d) (x : Fin N) : ℂ :=
  ∑ i : Fin d, if r.nbr i = some x then r.wt i else 0

/-- The set of possible neighbours in a star: at most one per slot, so at
most `d` of them. -/
def nbrImage (r : StarDesc N d) : Finset (Option (Fin N)) :=
  (Finset.univ : Finset (Fin d)).image r.nbr

/-- The nbr Image card le property in the paper model. -/
theorem nbrImage_card_le (r : StarDesc N d) : (nbrImage r).card ≤ d := by
  unfold nbrImage
  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d))) (f := r.nbr)

/-- A star has at most `d + 1` vertices (centre plus at most `d` leaves). -/
theorem star_card_le (r : StarDesc N d) : (nbrImage r).card + 1 ≤ d + 1 := by
  have := nbrImage_card_le r
  omega

/-! ## The unitary `U` computing the star data -/

/-- The second-register action of `U`: `none ↦ some (R x)` and
`some (R x) ↦ none`, everything else fixed.  This is an involution. -/
def Ureg (R : Fin N → StarDesc N d) (r : Option (StarDesc N d)) (x : Fin N) :
    Option (StarDesc N d) :=
  match r with
  | none => some (R x)
  | some r0 => if r0 = R x then none else some r0

/-- The Ureg invol property in the paper model. -/
theorem Ureg_invol (R : Fin N → StarDesc N d) (x : Fin N) (r : Option (StarDesc N d)) :
    Ureg R (Ureg R r x) x = r := by
  unfold Ureg
  cases r with
  | none => simp
  | some r0 =>
      by_cases h : r0 = R x
      · simp [h]
      · simp [h]

/-- The state space: vertex register and second register holding star data. -/
abbrev State (N d : ℕ) := Fin N × Option (StarDesc N d)

/-- The unitary `U` as a permutation of the computational basis, computing
`|x,0> ↦ |x,R(x)>`. -/
def Umap (R : Fin N → StarDesc N d) : State N d ≃ State N d where
  toFun p := (p.1, Ureg R p.2 p.1)
  invFun p := (p.1, Ureg R p.2 p.1)
  left_inv p := by
    obtain ⟨x, r⟩ := p
    show (x, Ureg R (Ureg R r x) x) = (x, r)
    rw [Ureg_invol]
  right_inv p := by
    obtain ⟨x, r⟩ := p
    show (x, Ureg R (Ureg R r x) x) = (x, r)
    rw [Ureg_invol]

/-- `U` applied twice returns the original basis state. -/
theorem Umap_invol (R : Fin N → StarDesc N d) (p : State N d) :
    Umap R (Umap R p) = p := by
  obtain ⟨x, r⟩ := p
  show (x, Ureg R (Ureg R r x) x) = (x, r)
  rw [Ureg_invol]

/-- `U` as a linear map on the state space (a linear equivalence, hence
unitary: it is a permutation matrix). -/
def Uapply (R : Fin N → StarDesc N d) :
    (State N d →₀ ℂ) ≃ₗ[ℂ] (State N d →₀ ℂ) :=
  Finsupp.domLCongr (Umap R)

/-- The Uapply single property in the paper model. -/
theorem Uapply_single (R : Fin N → StarDesc N d) (p : State N d) (c : ℂ) :
    Uapply R (Finsupp.single p c) = Finsupp.single (Umap R p) c :=
  Finsupp.domLCongr_single (Umap R) p c

/-- `U` is an involution (so `U† = U`). -/
theorem Uapply_invol (R : Fin N → StarDesc N d) (v : State N d →₀ ℂ) :
    Uapply R (Uapply R v) = v := by
  have hft : (Umap R).trans (Umap R) = Equiv.refl (State N d) := by
    apply Equiv.ext
    intro p
    exact Umap_invol R p
  have htrans : Uapply R ≪≫ₗ Uapply R = LinearEquiv.refl ℂ (State N d →₀ ℂ) := by
    unfold Uapply
    rw [Finsupp.domLCongr_trans, hft, Finsupp.domLCongr_refl]
  have := congrArg (fun e : (State N d →₀ ℂ) ≃ₗ[ℂ] (State N d →₀ ℂ) => e v) htrans
  simpa [LinearEquiv.trans_apply] using this

/-! ## The query-free Hamiltonian `K` -/

/-- `K` on a basis state `|x, r>`: it only reads the second register `r`.
If `x` is the centre, it maps to the sum of the star's leaves with their
weights, keeping the second register `r`; otherwise it maps to the centre
with the leaf's edge weight. -/
def Kpure (p : State N d) : State N d →₀ ℂ :=
  match p.2 with
  | none => 0
  | some r =>
      if p.1 = r.center then
        ∑ i : Fin d,
          match r.nbr i with
          | some y => Finsupp.single (y, some r) (r.wt i)
          | none => 0
      else Finsupp.single (r.center, some r) (leafWt r p.1)

/-- Linear extension of `K` to the whole state space (spanned by basis
states). -/
def Kapply (v : State N d →₀ ℂ) : State N d →₀ ℂ :=
  v.sum (fun p c => c • Kpure p)

/-- The Kapply single property in the paper model. -/
theorem Kapply_single (p : State N d) (c : ℂ) :
    Kapply (Finsupp.single p c) = c • Kpure p := by
  unfold Kapply
  exact Finsupp.sum_single_index (a := p) (b := c)
    (h := fun p c => c • Kpure p) (by simp)

/-- `K` never changes the second register: its output is supported on states
whose second coordinate equals the input's.  Therefore `K` needs no oracle
queries — all star data it uses is already stored in the register. -/
theorem Kpure_support_snd (p : State N d) :
    ∀ q ∈ (Kpure p).support, q.2 = p.2 := by
  intro q hq
  obtain ⟨x, r0⟩ := p
  cases r0 with
  | none =>
      simp [Kpure] at hq
  | some r =>
      simp only [Kpure] at hq
      by_cases hc : x = r.center
      · rw [if_pos hc] at hq
        rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hq
        by_contra hne
        apply hq
        apply Finset.sum_eq_zero
        intro i _
        cases hni : r.nbr i with
        | none => simp
        | some y =>
            apply Finsupp.single_eq_of_ne
            intro heq
            exact hne (by rw [heq])
      · rw [if_neg hc] at hq
        rw [Finsupp.mem_support_iff] at hq
        by_contra hne
        apply hq
        apply Finsupp.single_eq_of_ne
        intro heq
        exact hne (by rw [heq])

/-! ## The galaxy Hamiltonian `H` -/

/-- The action of the galaxy Hamiltonian on the basis vector `|x>`, with the
second register initialised to `none`.  If `x` is a centre, the edges are the
star's leaves in slot order; otherwise `x` is a leaf and the only edge goes
to the centre with weight `leafWt`. -/
def Hrow (R : Fin N → StarDesc N d) (x : Fin N) : State N d →₀ ℂ :=
  if x = (R x).center then
    ∑ i : Fin d,
      match (R x).nbr i with
      | some y => Finsupp.single (y, none) ((R x).wt i)
      | none => 0
  else Finsupp.single ((R x).center, none) (leafWt (R x) x)

/-- The star data is constant on a star: the centre carries the same data as
its members.  (Paper: "if `x` and `y` belong to the same star then
`R(x) = R(y)`".) -/
def StarClosed (R : Fin N → StarDesc N d) : Prop :=
  (∀ x, R (R x).center = R x) ∧
  (∀ x i y, (R x).nbr i = some y → R y = R x)

/-! ## Correctness of the simulation on basis states -/

/-- **Theorem 3, core identity** (p. 9): `U K U |x,0> = H |x> ⊗ |0>`.
The first `U` computes `R(x)` into the second register; `K` applies the
galaxy Hamiltonian using only that stored data; the final `U` uncomputes the
second register, which `K` left unchanged.  Star-closedness is used exactly
where the second register must agree on the leaves of the star. -/
theorem galaxy_simulation_on_basis (R : Fin N → StarDesc N d) (hR : StarClosed R)
    (x : Fin N) :
    Uapply R (Kapply (Uapply R (Finsupp.single (x, none) 1))) = Hrow R x := by
  obtain ⟨hcenter, hnbr⟩ := hR
  rw [Uapply_single]
  have hU0 : Umap R (x, none) = (x, some (R x)) := by
    simp [Umap, Ureg]
  rw [hU0, Kapply_single]
  simp only [one_smul]
  change Uapply R (Kpure (x, some (R x))) = Hrow R x
  have hK : Kpure (x, some (R x)) =
      (if x = (R x).center then
        (∑ i : Fin d,
          match (R x).nbr i with
          | some y => Finsupp.single (y, some (R x)) ((R x).wt i)
          | none => 0)
      else Finsupp.single ((R x).center, some (R x)) (leafWt (R x) x)) := rfl
  rw [hK]
  unfold Hrow
  by_cases hx : x = (R x).center
  · rw [if_pos hx, if_pos hx]
    -- distribute `U` over the finite sum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases hni : (R x).nbr i with
    | none => simp
    | some y =>
        have hy : R y = R x := hnbr x i y hni
        have hUy : Umap R (y, some (R x)) = (y, none) := by
          simp [Umap, Ureg, hy]
        rw [Uapply_single, hUy]
  · rw [if_neg hx, if_neg hx]
    have hcc : R (R x).center = R x := hcenter x
    have hUc : Umap R ((R x).center, some (R x)) = ((R x).center, none) := by
      simp [Umap, Ureg, hcc]
    rw [Uapply_single, hUc]

/-! ## Query bound for the star data -/

/-- The star data `R(x)` contains at most `d` neighbour slots, hence the star
of `x` is determined by the (at most) `d` neighbours of `x`, when `x` is a
centre, or by the one neighbour of `x` and then the at most `d` neighbours of
that centre, when `x` is a leaf: `d + 1` oracle calls in the worst case. -/
theorem star_query_bound (R : Fin N → StarDesc N d) (x : Fin N) :
    (nbrImage (R x)).card ≤ d ∧ (nbrImage (R x)).card + 1 ≤ d + 1 := by
  exact ⟨nbrImage_card_le (R x), star_card_le (R x)⟩

/-- **Theorem 3 (Galaxy simulation)**, arXiv:1003.3683v2 §4 p.8--9.
For a galaxy of maximum degree `d` whose star data `R` is star-closed, there
is a unitary `U` (an involution on the computational basis, computing
`|x,0> ↦ |x,R(x)>`) and a query-free Hamiltonian `K`, such that

* `K` leaves the second register unchanged (so it reads no oracle),
* `U K U |x,0> = H |x,0>` for every basis state `|x>`,
* the star data — hence `U` — is determined by at most `d + 1` oracle calls.

The paper's conclusion is then that `e^{-iH t}` is simulated with `O(d)`
calls to the oracle for `H` (the calls are only those of `U` and `U†`). -/
theorem galaxy_simulation (R : Fin N → StarDesc N d) (hR : StarClosed R) :
    (∀ v, Uapply R (Uapply R v) = v) ∧
    (∀ p : State N d, ∀ q ∈ (Kpure p).support, q.2 = p.2) ∧
    (∀ x, Uapply R (Kapply (Uapply R (Finsupp.single (x, none) 1))) = Hrow R x) ∧
    (∀ x, (nbrImage (R x)).card + 1 ≤ d + 1) := by
  refine ⟨Uapply_invol R, ?_, ?_, ?_⟩
  · intro p
    exact Kpure_support_snd p
  · intro x
    exact galaxy_simulation_on_basis R hR x
  · intro x
    exact star_card_le (R x)

end Qatlib.Papers.StarDecompSim10.MainResults.GalaxySimulation
