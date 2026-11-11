/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Mathlib.Analysis.Calculus.MeanValue

set_option backward.isDefEq.respectTransparency false

/-!
# Hamiltonian oracle model — vocabulary for Yonge-Mallo, arXiv:1108.2479v1

Fixed source: David Yonge-Mallo, *Adversary lower bounds in the Hamiltonian
oracle model*, arXiv:1108.2479v1 (11 Aug 2011).

This module supplies the objects of the Hamiltonian oracle model of Section 2
(pp. 1–2) and the spectral adversary data of Section 3 (pp. 2–4) needed to state
Theorem 3.1 (p. 3):

* `HamiltonianModel` — a bounded-error-free description of a continuous-time
  algorithm in the Hamiltonian oracle model.  The total Hamiltonian on input
  `x` is `H_x(t) = g(t) • H_Q(x) + H_D(t)` with `H_Q(x) = ∑_j H_j(x_j)`, each
  `H_j` bounded in operator norm by `1`, and `|g(t)| ≤ 1` (source §2, p. 2).
  The state `|ψ_x^t⟩` evolves by the Schrödinger equation
  `i d/dt |ψ_x^t⟩ = H_x(t) |ψ_x^t⟩` from an input-independent initial state
  (source §2, p. 1: "The algorithm starts in the initial state `ψ^0`").
* `BoundedErrorComputes` — the algorithm's final measurement computes `f`
  with error at most `ε` on every input, read through a two-outcome projective
  measurement at time `T` (source §2, p. 2 "correct with probability at least
  2/3" generalised to `1-ε`).
* `progressMeasure` — the spectral progress measure
  `w^t = ∑_{x,y} Γ[x,y] · δ[x] · δ[y] · ⟨ψ_x^t | ψ_y^t⟩` of Section 3 (p. 3).
* `filteredGamma` — the filtered adversary matrix `Γ_j`, with
  `Γ_j[x,y] = Γ[x,y]` when `x_j ≠ y_j` and `0` otherwise (source §3, p. 3).
* `maxFilteredSpec` — the maximum `max_j λ(Γ_j)` over all coordinates, the
  denominator of Theorem 3.1.

All definitions are the source's own; this module states no theorem.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

namespace Qatlib.Papers.AdversaryHam11.MainResults

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-! ## Section 2: the Hamiltonian oracle model -/

/-- **A continuous-time algorithm in the Hamiltonian oracle model** (source §2,
pp. 1–2).

The Hamiltonian oracle on input `x` is `H_Q(x) = ∑_j H_j(x_j)`, where each
`H_j(x_j)` has operator norm at most `1`.  `driver` is the input-independent
driver Hamiltonian `H_D(t)`, and `coupling` is the coefficient `g(t)` with
`|g(t)| ≤ 1`.  The combined Hamiltonian is
`H_x(t) = g(t) • H_Q(x) + H_D(t)` (`totalHam_eq`).  The state `state x t` is
`|ψ_x^t⟩`; it starts from the input-independent `initial` and evolves by the
Schrödinger equation `i d/dt |ψ_x^t⟩ = H_x(t) |ψ_x^t⟩` (`schrodinger`). -/
structure HamiltonianModel (X H : Type) [Fintype X] [Fintype H] [DecidableEq H] (n : ℕ) where
  /-- The per-coordinate oracle Hamiltonians `H_j(x_j)`. -/
  oracle : X → Fin n → Matrix H H ℂ
  /-- Source §2, p. 2: `‖H_j‖ ≤ 1`. -/
  oracle_bound : ∀ x j, ‖oracle x j‖ ≤ 1
  /-- The input-independent driver Hamiltonian `H_D(t)`. -/
  driver : ℝ → Matrix H H ℂ
  /-- The coupling strength `g(t)` of the oracle term. -/
  coupling : ℝ → ℝ
  /-- Source §2, p. 2: `|g(t)| ≤ 1`. -/
  coupling_bound : ∀ t, |coupling t| ≤ 1
  /-- The combined Hamiltonian `H_x(t) = g(t) H_Q(x) + H_D(t)`. -/
  totalHam : X → ℝ → Matrix H H ℂ
  /-- The Hamiltonian decomposition of source §2, p. 2. -/
  totalHam_eq : ∀ x t, totalHam x t = (coupling t : ℂ) • (∑ j, oracle x j) + driver t
  /-- The state `|ψ_x^t⟩` of the algorithm on input `x` at time `t`. -/
  state : X → ℝ → QState H
  /-- The input-independent initial state `ψ^0`. -/
  initial : QState H
  /-- The initial state is normalized. -/
  initial_normalized : Normalized initial
  /-- Source §2, p. 1: "The algorithm starts in the initial state `ψ^0`"
  (input-independent). -/
  initial_state : ∀ x, state x 0 = initial
  /-- The Schrödinger equation `i d/dt |ψ_x^t⟩ = H_x(t) |ψ_x^t⟩`, i.e.
  `d/dt |ψ_x^t⟩ = -i H_x(t) |ψ_x^t⟩` (source §2, p. 2). -/
  schrodinger :
    ∀ x t, HasDerivAt (state x) ((-Complex.I) • (totalHam x t).mulVec (state x t)) t
  /-- Unitary evolution preserves normalization. -/
  state_normalized : ∀ x t, Normalized (state x t)

/-- **The algorithm computes `f` with bounded error `ε` in time `T`**
(source §2, p. 2; §3 output condition, p. 3).

The final state at time `T` is measured by a two-outcome projective measurement
`(accept, 1 - accept)`; the outcome `f x` is correct on input `x` with
probability at least `1 - ε`.  This is the source's "computes `f` with bounded
error" (tightened from the printed `2/3` to the free parameter `ε ∈ [0,1]`). -/
structure BoundedErrorComputes {X H : Type} [Fintype X] [Fintype H] [DecidableEq H] {n : ℕ}
    (M : HamiltonianModel X H n) (f : X → Bool) (ε T : ℝ) where
  /-- The error parameter is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- The error parameter is at most one. -/
  eps_le_one : ε ≤ 1
  /-- The "yes" outcome projector `Π_1`. -/
  accept : Matrix H H ℂ
  /-- The outcome projector is self-adjoint. -/
  accept_herm : accept.IsHermitian
  /-- The outcome projector is idempotent. -/
  accept_idem : accept * accept = accept
  /-- The complementary outcome projector is idempotent. -/
  complement_idem : (1 - accept) * (1 - accept) = 1 - accept
  /-- The success probability on each input `x` is at least `1 - ε`. -/
  success : ∀ x,
    (Inner ((if f x then accept else (1 - accept)) *ᵥ M.state x T) (M.state x T)).re ≥ 1 - ε

/-! ## Section 3: the spectral adversary data -/

/-- The filtered adversary matrix `Γ_j` (source §3, p. 3): keep the entry
`Γ[x,y]` exactly when the `j`-th input coordinates differ, and zero otherwise. -/
noncomputable def filteredGamma {X : Type} {n : ℕ}
    (input : X → Fin n → Bool) (Γ : Matrix X X ℝ) (j : Fin n) : Matrix X X ℝ :=
  fun x y => if input x j ≠ input y j then Γ x y else 0

/-- The denominator `max_j λ(Γ_j)` of Theorem 3.1 (source p. 3), read as the
supremum of the spectral norms `‖Γ_j‖` over all coordinates.  It is `0` when
there are no coordinates. -/
noncomputable def maxFilteredSpec {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (Γ : Matrix X X ℝ) : NNReal :=
  Finset.univ.sup (fun j : Fin n => (⟨‖filteredGamma input Γ j‖, norm_nonneg _⟩ : NNReal))

/-- Every filtered spectral norm is bounded by `max_j λ(Γ_j)`. -/
theorem le_maxFilteredSpec {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (input : X → Fin n → Bool) (Γ : Matrix X X ℝ) (j : Fin n) :
    ‖filteredGamma input Γ j‖ ≤ (maxFilteredSpec input Γ : ℝ) := by
  unfold maxFilteredSpec
  have hle : (⟨‖filteredGamma input Γ j‖, norm_nonneg _⟩ : NNReal) ≤
      Finset.univ.sup
        (fun j : Fin n => (⟨‖filteredGamma input Γ j‖, norm_nonneg _⟩ : NNReal)) :=
    Finset.le_sup (f := fun j : Fin n => (⟨‖filteredGamma input Γ j‖, norm_nonneg _⟩ : NNReal))
      (Finset.mem_univ j)
  exact NNReal.coe_le_coe.mpr hle

/-- The **spectral progress measure** of Section 3 (p. 3):
`w^t = ∑_{x,y} Γ[x,y] · δ[x] · δ[y] · ⟨ψ_x^t | ψ_y^t⟩`, with the real adversary
data `Γ`, `δ` cast to `ℂ` and the complex inner products `⟨ψ_x^t | ψ_y^t⟩`. -/
noncomputable def progressMeasure {X H : Type} [Fintype X] [Fintype H]
    (Γ : Matrix X X ℝ) (δ : X → ℝ) (state : X → ℝ → QState H) (t : ℝ) : ℂ :=
  ∑ x, ∑ y, ((Γ x y : ℝ) : ℂ) * ((δ x : ℝ) : ℂ) * ((δ y : ℝ) : ℂ) *
    Inner (state x t) (state y t)

end Qatlib.Papers.AdversaryHam11.MainResults
