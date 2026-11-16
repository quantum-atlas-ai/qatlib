/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# SubHypergraph13 — hypergeometric tail bounds (Lemma 2)

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), **Lemma 2, page 4**.

The paper states three tail bounds for a hypergeometric variable `X` with
expectation `µ` and mass `Pr[X = j] = C(K,j) C(N-K,r-j) / C(N,r)`:
`Pr[X ≥ (1+δ)µ] ≤ exp(-µδ²/3)`, `Pr[X ≤ (1-δ)µ] ≤ exp(-µδ²/2)`, and
`Pr[X > (1+δ)µ] < (1/2)^((1+δ)µ)` for `δ > 2e-1`.  The paper derives them from
Theorem 2.10 of its reference [9]; it does not reprove them.

Below, `hypergeomMass`, `hypergeomMean`, `hypergeomTailGE/LE/GT` are the source
objects from `SourceModel.lean`.  We additionally *prove* (no `sorry`) that the
hypergeometric masses sum to one (Vandermonde), which certifies that the
`hypergeomTail*` quantities really are probabilities; the three tail bounds
themselves are recorded as the faithful statement of Lemma 2.
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

@[expose] public section


set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults.HypergeometricTailBounds
open Qatlib.Papers.SubHypergraph13.MainResults

/-! ## Normalisation of the hypergeometric masses (Vandermonde) -/

/-- Each hypergeometric mass is nonnegative. -/
theorem hypergeomMass_nonneg (N K r j : ℕ) : 0 ≤ hypergeomMass N K r j := by
  unfold hypergeomMass
  positivity

/-- **Vandermonde normalisation.** For `K ≤ N` and `r ≤ N` the hypergeometric
masses over `j ∈ {0,…,r}` sum to one:
`∑_j C(K,j) C(N-K,r-j)/C(N,r) = 1`.
This is the paper's `Pr`-mass being a genuine probability (p.4). -/
theorem hypergeomMass_sum_eq_one (N K r : ℕ) (hK : K ≤ N) (hr : r ≤ N) :
    ∑ j ∈ Finset.range (r + 1), hypergeomMass N K r j = 1 := by
  have hNat : ∑ j ∈ Finset.range (r + 1),
      Nat.choose K j * Nat.choose (N - K) (r - j) = Nat.choose N r := by
    have h := Nat.add_choose_eq K (N - K) r
    rw [Nat.add_sub_of_le hK] at h
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => Nat.choose K a * Nat.choose (N - K) b) r] at h
    exact h.symm
  have hA : ∑ j ∈ Finset.range (r + 1),
      (Nat.choose K j : ℝ) * (Nat.choose (N - K) (r - j) : ℝ) = (Nat.choose N r : ℝ) := by
    exact_mod_cast hNat
  have hpos : (Nat.choose N r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hr).ne'
  unfold hypergeomMass
  rw [← Finset.sum_div, hA]
  exact div_self hpos

/-! ## Lemma 2 (p.4) — the three tail bounds -/

/-! The remaining paper theorem requires unformalized probabilistic/circuit machinery and is intentionally omitted from this verified leaf. -/

end Qatlib.Papers.SubHypergraph13.MainResults.HypergeometricTailBounds
