/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions.SourceTheta

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults.Sec4Inequalities
open Qatlib.Papers.PolySysCrypto18.MainResults
open Qatlib.Papers.PolySysCrypto18.MainResults.Sec2Reductions

/-- Natural parameters used in the numerical inequality-reduction ledgers. The record does not itself attach these parameters to a polynomial system. -/
structure IneqParams where
  /-- number `m` of integer variables `Y` -/
  m : ℕ
  /-- number `n` of finite-field variables `X` -/
  n : ℕ
  /-- number `s` of inequalities -/
  s : ℕ
  /-- total sparseness `T_G` of `G = {g_1,…,g_s}` -/
  TG : ℕ
  /-- `d_g = max_l deg(g_l)` -/
  dg : ℕ
  /-- `h = max{p−1, u_1, …, u_m}` -/
  h : ℕ

/-- Proposed numerical variable-count ledger for the Boolean inequality reduction. Identifying this number with a constructed system's variables requires a separate source bridge. -/
def bGNumVars (ip : IneqParams) : ℕ :=
  (ip.m + ip.n) * ip.TG * ip.dg * (Nat.log2 ip.dg + 1) * (Nat.log2 ip.h + 1)

/-- Proposed numerical sparseness ledger for the Boolean inequality reduction. This definition does not count actual monomial supports. -/
def bGSparseness (ip : IneqParams) : ℕ :=
  (ip.m + ip.n) * ip.TG * ip.dg ^ 2 * (Nat.log2 ip.dg + 1) * (Nat.log2 ip.h + 1) ^ 2

/-- Every natural vector bounded coordinatewise by the positive integer `u` has a Boolean preimage under the coordinatewise `theta u` map. Polynomial substitution and feasibility preservation are separate obligations. -/
theorem lemma_4_1 {u : ℕ} (hu : 0 < u) (m : ℕ) :
    ∀ Y : Fin m → ℕ, (∀ j, Y j ≤ u) →
      ∃ Y_bit : Fin m → (Fin (Nat.log2 u + 1) → Bool),
        ∀ j, theta u (fun i => (Y_bit j i).toNat) = Y j := by
  intro Y hY
  choose B hB using fun j => theta_surjective hu (Y j) (hY j)
  exact ⟨B, hB⟩

end Qatlib.Papers.PolySysCrypto18.MainResults.Sec4Inequalities
