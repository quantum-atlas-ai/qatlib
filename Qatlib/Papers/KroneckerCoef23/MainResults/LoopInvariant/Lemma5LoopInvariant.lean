/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# LoopInvariant — Lemma 5 of Bravyi–Chowdhury–Gosset–Havlíček–Zhu

Fixed version: arXiv:2302.11454v3 (7 May 2024), Lemma 5 and Eq. (25), p. 11.

Lemma 5: for `0 ≤ k ≤ n` the state after the `k`-th iteration of the for loop of
Algorithm 1 is

`|φ_k⟩ = |0⟩ Σ_{j=1}^k |F̂^j⟩ + Σ_{j=k+1}^n |τ_j⟩ |f̂_j⟩`.   (25)

For `k = 0` the first sum is absent; for `k = n` the second sum is absent and
`|φ_n⟩ = |0⟩ Σ_{j=1}^n |F̂^j⟩ = |0⟩|f̂⟩`.

We model the two families of vectors of (25) as an arbitrary sequence in an
additive commutative group: `A j = |0⟩|F̂^j⟩` and `B j = |τ_j⟩|f̂_j⟩`.  Then:

* `phi_zero` and `phi_n` are the two endpoint readings of (25);
* `phi_step` is the loop body: going from `k` to `k+1` replaces the `|τ_{k+1}⟩|f̂_{k+1}⟩`
  term by the `|0⟩|F̂^{k+1}⟩` term, i.e. `φ_{k+1} = φ_k + A (k+1) - B (k+1)`
  (the paper's Claim 1, proved there from Eqs. (16)–(19));
* `lemma5_loop_invariant` propagates the closed form through the loop by induction.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.KroneckerCoef23.MainResults.LoopInvariant

variable {W : Type*} [AddCommGroup W]

/-- The closed-form state of Eq. (25): the `|0⟩ Σ_{j=1}^k |F̂^j⟩` part is the sum of
`A j = |0⟩|F̂^j⟩` over `j = 1,…,k`, and the `Σ_{j=k+1}^n |τ_j⟩|f̂_j⟩` part is the
sum of `B j = |τ_j⟩|f̂_j⟩` over `j = k+1,…,n`. -/
def phi (A B : ℕ → W) (n k : ℕ) : W :=
  (∑ j ∈ Finset.range k, A (j + 1)) + ∑ j ∈ Finset.Ico (k + 1) (n + 1), B j

/-- Lemma 5, endpoint `k = 0`: the first term of Eq. (25) is absent. -/
theorem phi_zero (A B : ℕ → W) (n : ℕ) :
    phi A B n 0 = ∑ j ∈ Finset.Ico 1 (n + 1), B j := by
  simp [phi]

/-- Lemma 5, endpoint `k = n`: the second term of Eq. (25) is absent, so
`|φ_n⟩ = |0⟩ Σ_{j=1}^n |F̂^j⟩`. -/
theorem phi_n (A B : ℕ → W) (n : ℕ) :
    phi A B n n = ∑ j ∈ Finset.range n, A (j + 1) := by
  simp [phi]

/-- One iteration of the loop: passing from `k` to `k+1` adds the `|0⟩|F̂^{k+1}⟩`
term and removes the `|τ_{k+1}⟩|f̂_{k+1}⟩` term, for `k+1 ≤ n`. -/
theorem phi_step (A B : ℕ → W) {n k : ℕ} (hk : k + 1 ≤ n) :
    phi A B n (k + 1) = phi A B n k + A (k + 1) - B (k + 1) := by
  have hA : (∑ j ∈ Finset.range (k + 1), A (j + 1))
      = (∑ j ∈ Finset.range k, A (j + 1)) + A (k + 1) := by
    rw [Finset.sum_range_succ]
  have hsingle : (∑ j ∈ Finset.Ico (k + 1) (k + 2), B j) = B (k + 1) := by
    rw [Finset.sum_Ico_succ_top (le_refl (k + 1))]
    simp
  have hcons := Finset.sum_Ico_consecutive B (m := k + 1) (n := k + 2) (k := n + 1)
    (by omega) (by omega)
  rw [hsingle] at hcons
  have hsplit : (∑ j ∈ Finset.Ico (k + 1) (n + 1), B j)
      = B (k + 1) + ∑ j ∈ Finset.Ico (k + 2) (n + 1), B j := hcons.symm
  have hidx : k + 1 + 1 = k + 2 := by omega
  simp only [phi, hidx]
  rw [hA, hsplit]
  abel

/-- **Lemma 5** (fixed arXiv:2302.11454v3, Eq. (25), p. 11), in induction form: if
the loop starts in the state `phi A B n 0` and each iteration implements the
update `φ_{k+1} = φ_k + A (k+1) - B (k+1)` of the paper's Claim 1, then after
`k` iterations the state is the closed form `phi A B n k`. -/
theorem lemma5_loop_invariant (A B : ℕ → W) (n : ℕ) (φ : ℕ → W)
    (h0 : φ 0 = phi A B n 0)
    (hstep : ∀ k, k + 1 ≤ n → φ (k + 1) = φ k + A (k + 1) - B (k + 1)) :
    ∀ k, k ≤ n → φ k = phi A B n k := by
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
      intro hk
      rw [hstep k hk, ih (by omega), phi_step A B hk]

end Qatlib.Papers.KroneckerCoef23.MainResults.LoopInvariant
