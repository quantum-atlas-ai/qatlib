/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BddDegreeCSP15.FourierTools.SourceModel

@[expose] public section


/-!
# BddDegreeCSP15 — Theorem 1.1, proved `x` vs `¬x` step (Block `XorAlgorithms`)

Fixed source: arXiv:1505.03424v2, Theorem 1.1 (p. 3, (1.2)), "in
particular" part: for odd `k`, if some assignment has `|P(x)| ≥ b` then
an assignment `y` with `P(y) ≥ b` exists — the purely combinatorial
`x` vs `¬x` step of the Max-kXOR advantage argument.

The declarations below establish the combinatorial negation step. Algorithmic
running-time and advantage guarantees require additional hypotheses and are
separate from these identities.
-/

set_option autoImplicit false

namespace Qatlib.Papers.BddDegreeCSP15.XorAlgorithms

open scoped BigOperators
open Finset Qatlib.Papers.BddDegreeCSP15.FourierTools

/-- For odd `k`, negating every variable flips the advantage polynomial: `P(¬x) = −P(x)`
(source §3/§4; the `x` vs `¬x` step of Theorem 1.1). -/
theorem maxXOR_advantage_neg {n k : ℕ} (I : MaxKXORInstance n k) (hk : Odd k)
    (x : SignCube n) :
    I.advantage (fun i => !(x i)) = -I.advantage x := by
  unfold MaxKXORInstance.advantage
  have hsum :
      (∑ ℓ : Fin I.m, (I.sign ℓ * ∏ j ∈ I.scope ℓ, signOfBool (!(x j))))
        = ∑ ℓ : Fin I.m, -(I.sign ℓ * ∏ j ∈ I.scope ℓ, signOfBool (x j)) := by
    apply Finset.sum_congr rfl
    intro ℓ _
    have hprod : (∏ j ∈ I.scope ℓ, signOfBool (!(x j)))
        = (∏ _j ∈ I.scope ℓ, (-1 : ℝ)) * ∏ j ∈ I.scope ℓ, signOfBool (x j) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      rw [signOfBool_not]
      ring
    rw [hprod, Finset.prod_const, I.arity ℓ]
    rw [show (-1 : ℝ) ^ k = -1 from hk.neg_one_pow]
    ring
  rw [hsum, Finset.sum_neg_distrib]
  ring

/-- **Fixed arXiv:1505.03424v2, Theorem 1.1, "in particular" part (p. 3, (1.2)).**
For odd `k`, if some assignment has `|P(x)| ≥ b` then an assignment `y`
with `P(y) ≥ b` exists (and hence `val(y) ≥ ½ + b`).  This is the purely
combinatorial `x` vs `¬x` step; it does not assert an algorithmic running-time
bound or the remaining guarantees of Theorem 1.1. -/
theorem theorem_1_1_odd_negation (n k : ℕ) (I : MaxKXORInstance n k) (hk : Odd k)
    (b : ℝ) (x : SignCube n) (hx : b ≤ |I.advantage x|) :
    ∃ y : SignCube n, b ≤ I.advantage y := by
  by_cases h : b ≤ I.advantage x
  · exact ⟨x, h⟩
  · push Not at h
    refine ⟨fun i => !(x i), ?_⟩
    rw [maxXOR_advantage_neg I hk x]
    have hneg : I.advantage x < 0 := by
      by_contra hnn
      push Not at hnn
      have habs : |I.advantage x| = I.advantage x := abs_of_nonneg hnn
      rw [habs] at hx
      linarith
    rw [abs_of_neg hneg] at hx
    linarith

end Qatlib.Papers.BddDegreeCSP15.XorAlgorithms
