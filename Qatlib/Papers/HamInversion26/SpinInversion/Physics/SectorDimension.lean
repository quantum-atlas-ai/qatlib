/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The Tavis–Cummings coarse-sector dimension, closed form

Supplement of arXiv:2607.29382v2, Eqs. (S99)–(S100), pages S21–S22.  Restricting the
Tavis–Cummings family to at most `N` excitations and removing the Schur–Weyl multiplicities
leaves the coarse sectors indexed by `j = 0, …, N` with dimension

`d_{j,L} = binom(M + L − j, L − j)`, hence `d_j = Σ_{L = j}^{N} binom(M + L − j, L − j)`.

This module proves the hockey-stick evaluation of that sum,

`Σ_{L=j}^{N} binom(M + L − j, L − j) = binom(M + N − j + 1, N − j)`,

so `d_j` is a binomial coefficient that depends only on `M` and `N − j` and, in particular,
not on the photon number `n`.  That is the combinatorial half of the `O_{M,N}(1)` bookkeeping
of Proposition S20; the query-count assembly `q_TC ≤ Σ_j [q_univ(d_j) + 1] − 1` and the
Schur–Weyl reduction itself are not part of this module.
-/

open Finset
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Physics

set_option autoImplicit false

/-- **Coarse-sector dimension, closed form** (Eqs. (S99)–(S100), page S22): the sum of the
multiplicity-free sector dimensions `binom(M + L − j, L − j)` over `L = j, …, N` is the single
binomial coefficient `binom(M + N − j + 1, N − j)`. -/
theorem sum_choose_eq_choose {M N j : ℕ} (hj : j ≤ N) :
    (∑ L ∈ Finset.Icc j N, Nat.choose (M + L - j) (L - j)) =
      Nat.choose (M + N - j + 1) (N - j) := by
  have hbij : (∑ L ∈ Finset.Icc j N, Nat.choose (M + L - j) (L - j)) =
      ∑ m ∈ Finset.Icc M (M + N - j), Nat.choose m M := by
    refine Finset.sum_bij (fun L _ => M + L - j) ?_ ?_ ?_ ?_
    · intro L hL
      simp only [Finset.mem_Icc] at hL ⊢
      omega
    · intro L1 hL1 L2 hL2 heq
      simp only [Finset.mem_Icc] at hL1 hL2
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨m - M + j, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        omega
      · omega
    · intro L hL
      simp only [Finset.mem_Icc] at hL
      rw [show L - j = M + L - j - M by omega,
        Nat.choose_symm (show M ≤ M + L - j by omega)]
  rw [hbij, Nat.sum_Icc_choose, ← Nat.choose_symm (show M + 1 ≤ M + N - j + 1 by omega)]
  congr 1
  omega

end Qatlib.Papers.HamInversion26.SpinInversion.Physics
