/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.GraphLaplacian
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option backward.isDefEq.respectTransparency false

/-!
# AdiabNoLocMin14.MainResults — single-basin ground states and their walk bridge

Jarret & Jordan, *Adiabatic optimization without local minima*, fixed arXiv:1405.7552v2
(20 pages; local PDF SHA-256 `6285934ded680097a3a1ec977f0d2d5b03619ac774a5880df3d5889e812a4b3e`).

## Source results covered

* §2 eqs. (1)--(2): the graph-Laplacian-plus-potential Hamiltonian
  `H_{G,W} = L_G + ∑_x W(x)|x⟩⟨x|`, realised here as Mathlib's `SimpleGraph.lapMatrix ℝ`
  plus `Matrix.diagonal W`.
* §2 eq. (23): the eigenvalue equation
  `(d_x + W(x))ψ(x) - ∑_{y ∈ N_x} ψ(y) = E ψ(x)`.
* §4.3 eqs. (48)--(51) and **Proposition 5** (p. 12): for a single-basin potential `W`,
  the set `S[ψ] = {x | Δ²ψ(x) < 0}` is a connected set of vertices in `G`.
* §4.2 eqs. (26)--(32): the similarity transform `P = E⁻¹ D⁻¹ H_{G,W} D` with
  `D = diag(ψ)` is row-stochastic, its stationary law `ψ²` is invariant, and the
  stationary-weighted flux `ψ(x)²P_{xy}` is the cut expression (31) used to build `Φ_H`.

## Boundary

No eigenvalue ordering, spectral gap `γ`, conductance `Φ_H`, Cheeger inequality,
Poincaré bound or adiabatic runtime is asserted here: Propositions 3, 4 and 6 and the
§3 caterpillar counterexample of §3 remain open for this Paper. Positivity of `ψ` is the
Perron--Frobenius input quoted in the source; it is carried as a hypothesis, not derived.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabNoLocMin14.MainResults

open Matrix
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphLaplacian.LaplacianPsd
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The Hamiltonian of form (2) -/

/-- Source eq. (2): the Hamiltonian `H_{G,W} = L_G + ∑_x W(x)|x⟩⟨x|` in the vertex
basis, with `L_G` Mathlib's graph Laplacian. -/
def hamiltonian (G : SimpleGraph V) [DecidableRel G.Adj] (W : V → ℝ) : Matrix V V ℝ :=
  G.lapMatrix ℝ + Matrix.diagonal W

/-- Source eq. (1)--(2) entrywise: the diagonal of `H_{G,W}` is `d_x + W(x)` and an edge
entry is `-1`. -/
lemma hamiltonian_apply (G : SimpleGraph V) [DecidableRel G.Adj] (W : V → ℝ) (x y : V) :
    hamiltonian G W x y =
      (if x = y then ((G.degree x : ℝ) + W x) else if G.Adj x y then -1 else 0) := by
  rw [hamiltonian, Matrix.add_apply, lapMatrix_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · by_cases hadj : G.Adj x y <;> simp [hxy, hadj]

/-- `H_{G,W}` is symmetric, being the sum of the symmetric graph Laplacian and a diagonal
matrix. -/
lemma hamiltonian_symm (G : SimpleGraph V) [DecidableRel G.Adj] (W : V → ℝ) (x y : V) :
    hamiltonian G W x y = hamiltonian G W y x := by
  rw [hamiltonian_apply, hamiltonian_apply]
  by_cases hxy : x = y
  · subst hxy
    simp
  · by_cases hadj : G.Adj x y
    · have hadj' : G.Adj y x := G.adj_symm hadj
      simp [hxy, Ne.symm hxy, hadj, hadj']
    · have hadj' : ¬ G.Adj y x := fun h => hadj (G.adj_symm h)
      simp [hxy, Ne.symm hxy, hadj, hadj']

/-- The row of `H_{G,W}` weighted by `ψ` is the matrix--vector product entry. -/
lemma sum_row_eq_mulVec (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (x : V) :
    ∑ y, hamiltonian G W x y * ψ y = (hamiltonian G W *ᵥ ψ) x := rfl

/-- Source eq. (23), left-hand side: the action of `H_{G,W}` on a vertex vector. -/
lemma hamiltonian_mulVec (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (x : V) :
    (hamiltonian G W *ᵥ ψ) x =
      (degree G x + W x) * ψ x - ∑ y ∈ G.neighborFinset x, ψ y := by
  rw [hamiltonian, Matrix.add_mulVec]
  simp only [Pi.add_apply]
  rw [SimpleGraph.lapMatrix_mulVec_apply, Matrix.mulVec_diagonal, degree_eq_mathlib (G := G) x]
  ring

/-- `ψ` is an eigenvector of `H_{G,W}` with eigenvalue `E`. -/
def IsEigenstate (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (E : ℝ) : Prop :=
  hamiltonian G W *ᵥ ψ = E • ψ

/-- Source eq. (23): the eigenvector equation written out at every vertex. -/
theorem eigenEquation (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (h : IsEigenstate G W ψ E) (x : V) :
    (degree G x + W x) * ψ x - ∑ y ∈ G.neighborFinset x, ψ y = E * ψ x := by
  have hx := congrFun h x
  rw [hamiltonian_mulVec] at hx
  simpa using hx

/-! ## The second difference and source eqs. (48)--(51) -/

/-- Source eq. (48): the discrete second difference of `ψ` at `x`. -/
def deltaSq (G : SimpleGraph V) [DecidableRel G.Adj] (ψ : V → ℝ) (x : V) : ℝ :=
  -(degree G x) * ψ x + ∑ y ∈ G.neighborFinset x, ψ y

/-- Source eq. (49): `L_G|ψ⟩ = -∑_x Δ²ψ(x)|x⟩`, read entrywise as
`Δ²ψ(x) = -(L_G ψ)(x)`. -/
lemma deltaSq_eq_neg_lapMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (ψ : V → ℝ) (x : V) :
    deltaSq G ψ x = -((G.lapMatrix ℝ *ᵥ ψ) x) := by
  rw [SimpleGraph.lapMatrix_mulVec_apply, deltaSq, degree_eq_mathlib (G := G) x]
  ring

/-- Source eq. (51): on an eigenstate the second difference is `(W(x) - E)ψ(x)`. -/
theorem deltaSq_eq_mul_sub (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (h : IsEigenstate G W ψ E) (x : V) : deltaSq G ψ x = (W x - E) * ψ x := by
  have hx := eigenEquation G h x
  rw [deltaSq]
  have hsum : ∑ y ∈ G.neighborFinset x, ψ y = (degree G x + W x) * ψ x - E * ψ x := by
    linarith
  rw [hsum]
  ring

/-! ## Connectivity vocabulary of §2 and §4.3 -/

/-- Source eq. (4): `ψ` has a local maximum at `x` when no neighbour carries a larger
amplitude. -/
def IsLocalMax (G : SimpleGraph V) [DecidableRel G.Adj] (ψ : V → ℝ) (x : V) : Prop :=
  ∀ y : V, G.Adj x y → ψ y ≤ ψ x

/-- Source §2: `ψ` is single-peaked when its local maxima form a connected vertex set,
`(G.induce {x | IsLocalMax G ψ x}).Preconnected`. -/
def IsSinglePeaked (G : SimpleGraph V) [DecidableRel G.Adj] (ψ : V → ℝ) : Prop :=
  (G.induce {x : V | IsLocalMax G ψ x}).Preconnected

/-- Source Definition 4 (§4.3): `W` is a single-basin potential when every sublevel set
`{x | W(x) < E}` is connected in `G`. -/
def IsSingleBasin (G : SimpleGraph V) [DecidableRel G.Adj] (W : V → ℝ) : Prop :=
  ∀ E : ℝ, (G.induce {x : V | W x < E}).Preconnected

/-! ## Proposition 5 -/

/-- Source eq. (50) together with the sign argument after (51): because all amplitudes are
positive, `S[ψ] = {x | Δ²ψ(x) < 0}` is exactly the sublevel set `{x | W(x) < E}`. -/
theorem sSet_eq_sublevel (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (h : IsEigenstate G W ψ E) (hpos : ∀ x, 0 < ψ x) :
    {x : V | deltaSq G ψ x < 0} = {x : V | W x < E} := by
  ext x
  simp only [Set.mem_setOf_eq, deltaSq_eq_mul_sub G h x]
  constructor
  · intro hlt
    by_contra _
    have hnn : 0 ≤ (W x - E) * ψ x := mul_nonneg (by linarith) (le_of_lt (hpos x))
    linarith
  · intro hlt
    exact mul_neg_of_neg_of_pos (by linarith) (hpos x)

/-- **Proposition 5** (source §4.3, p. 12). For a single-basin potential `W` on `G` and a
strictly positive eigenstate `ψ` of `H_{G,W} = L_G + W` with energy `E`, the set
`S[ψ] = {x | Δ²ψ(x) < 0}` is a connected set of vertices in `G`. -/
theorem prop5 (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (h : IsEigenstate G W ψ E) (hpos : ∀ x, 0 < ψ x) (hsingle : IsSingleBasin G W) :
    (G.induce {x : V | deltaSq G ψ x < 0}).Preconnected := by
  rw [sSet_eq_sublevel G h hpos]
  exact hsingle E

/-! ## The walk bridge of §4.2, eqs. (26)--(32) -/

/-- Source eq. (26): the similarity transform `P = E⁻¹ D⁻¹ H_{G,W} D` with `D = diag(ψ)`,
written entrywise. -/
def walkMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (E : ℝ) :
    Matrix V V ℝ :=
  fun x y => hamiltonian G W x y * ψ y / (E * ψ x)

/-- Source eqs. (25)--(26): `P` is row-stochastic, since the eigenvector equation (23) says
that the row of `H_{G,W}` weighted by `ψ` sums to `E ψ(x)`. -/
theorem walkMatrix_row_sum (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (h : IsEigenstate G W ψ E) (hpos : ∀ x, 0 < ψ x) (hE : E ≠ 0) (x : V) :
    ∑ y, walkMatrix G W ψ E x y = 1 := by
  have hx : ψ x ≠ 0 := (hpos x).ne'
  have hsum : ∑ y, hamiltonian G W x y * ψ y = E * ψ x := by
    rw [sum_row_eq_mulVec, hamiltonian_mulVec]
    exact eigenEquation G h x
  rw [show (∑ y, walkMatrix G W ψ E x y) =
      ∑ y, hamiltonian G W x y * ψ y / (E * ψ x) from rfl]
  rw [← Finset.sum_div, hsum]
  exact div_self (mul_ne_zero hE hx)

/-- The stationary-weighted transition mass `ψ(x)²P_{xy}` — the quantity that source
eqs. (29) and (31) actually compute. -/
def walkFlux (G : SimpleGraph V) [DecidableRel G.Adj] (W ψ : V → ℝ) (E : ℝ) (x y : V) : ℝ :=
  ψ x * hamiltonian G W x y * ψ y / E

/-- `ψ(x)²P_{xy}` is the flux `ψ(x)H_{G,W}(x,y)ψ(y)/E`; this unwinds the `D`-conjugation
of eq. (26). -/
theorem sq_mul_walkMatrix (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (hpos : ∀ x, 0 < ψ x) (hE : E ≠ 0) (x y : V) :
    (ψ x) ^ 2 * walkMatrix G W ψ E x y = walkFlux G W ψ E x y := by
  rw [walkMatrix, walkFlux]
  have hx : ψ x ≠ 0 := (hpos x).ne'
  field_simp

/-- Source eq. (29): the walk is reversible, `ψ(x)²P_{xy} = ψ(y)²P_{yx}`, because
`H_{G,W}` is symmetric. -/
theorem walkFlux_detailed_balance (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ}
    {E : ℝ} (x y : V) :
    walkFlux G W ψ E x y = walkFlux G W ψ E y x := by
  rw [walkFlux, walkFlux, hamiltonian_symm G W y x]
  ring

/-- Source eqs. (27)--(28): the stationary law `ψ²` is invariant under `P`. -/
theorem walkFlux_invariant (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (h : IsEigenstate G W ψ E) (hE : E ≠ 0) (y : V) :
    ∑ x, walkFlux G W ψ E x y = ψ y ^ 2 := by
  have hsum : ∑ x, hamiltonian G W y x * ψ x = E * ψ y := by
    rw [sum_row_eq_mulVec, hamiltonian_mulVec]
    exact eigenEquation G h y
  have hstep : ∑ x, walkFlux G W ψ E x y =
      ∑ x, (hamiltonian G W y x * ψ x) * ψ y / E := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [walkFlux, hamiltonian_symm G W y x]
    ring
  rw [hstep, ← Finset.sum_div, ← Finset.sum_mul, hsum]
  field_simp

/-- Source eq. (31) termwise: across a genuine (off-diagonal) ordered pair the flux is
`-ψ(x)ψ(y)/E` on an edge and zero otherwise. -/
theorem walkFlux_cut (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    {x y : V} (hxy : x ≠ y) :
    walkFlux G W ψ E x y = (if G.Adj x y then -(ψ x * ψ y) / E else 0) := by
  rw [walkFlux, hamiltonian_apply]
  simp only [hxy, if_false]
  by_cases hadj : G.Adj x y
  · simp only [hadj, if_true]
    ring
  · simp only [hadj, if_false]
    ring

/-- Source eq. (31): the flow out of a cut `S` in the walk `P` is the negative of the
edge-boundary sum divided by the ground energy `E`. -/
theorem walkFlux_flow (G : SimpleGraph V) [DecidableRel G.Adj] {W ψ : V → ℝ} {E : ℝ}
    (S : Finset V) :
    ∑ x ∈ S, ∑ y ∈ Sᶜ, walkFlux G W ψ E x y =
      ∑ x ∈ S, ∑ y ∈ Sᶜ, (if G.Adj x y then -(ψ x * ψ y) / E else 0) := by
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  have hxy : x ≠ y := by
    rintro rfl
    exact Finset.mem_compl.mp hy hx
  exact walkFlux_cut G hxy

end Qatlib.Papers.AdiabNoLocMin14.MainResults
