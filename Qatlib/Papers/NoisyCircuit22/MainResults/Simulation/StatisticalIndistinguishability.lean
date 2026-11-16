/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic.Linarith

public import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.SimulationModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Corollary 1 (no statistical test)

Fixed arXiv:2211.03999v1, Corollary 1, p.2.

Assuming anti-concentration, no statistical test applied to `M` samples can distinguish the
output of a noisy random circuit from the classical algorithm with running time
`poly(n, M)`.  The mathematical core is the standard fact that a test's advantage is at
most the total variation distance of the two distributions on `M`-tuples.

The test-advantage bound requires equal total masses. Nonnegativity is unnecessary;
probability distributions satisfy the added premise by normalization.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Simulation

open BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

/-- A statistical test cannot distinguish two distributions better than their total
variation distance. -/
theorem test_advantage_le_totalVariation {α : Type*} [Fintype α]
    (p q : α → ℝ) (test : α → Bool) (hmass : ∑ x, p x = ∑ x, q x) :
    TestAdvantage p q test ≤ TotalVariation p q := by
  classical
  let a : α → ℝ := fun x => if test x then p x - q x else 0
  let b : α → ℝ := fun x => if test x then 0 else p x - q x
  have hab : ∀ x, a x + b x = p x - q x := by
    intro x
    dsimp [a, b]
    cases test x <;> simp
  have hsum : (∑ x, a x) + ∑ x, b x = 0 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hab]
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  have hpoint : ∀ x, |a x| + |b x| = |p x - q x| := by
    intro x
    dsimp [a, b]
    cases test x <;> simp
  have htotal : (∑ x, |a x|) + ∑ x, |b x| = ∑ x, |p x - q x| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => hpoint x)
  have ha := Finset.abs_sum_le_sum_abs a Finset.univ
  have hb := Finset.abs_sum_le_sum_abs b Finset.univ
  have heq : (∑ x, b x) = -(∑ x, a x) := by linarith
  rw [heq, abs_neg] at hb
  have hadv : TestAdvantage p q test = |∑ x, a x| := by
    unfold TestAdvantage
    rw [← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp [a]
    cases test x <;> simp
  rw [hadv]
  unfold TotalVariation
  linarith

/-- Fixed arXiv:2211.03999v1, Corollary 1, p.2: no test on `M` samples distinguishes the
noisy circuit from the classical sampler with advantage greater than `mu`, provided the
`M`-sample distributions are `mu`-close in total variation. -/
theorem source_corollary1_no_test {α : Type*} [Fintype α] {M : ℕ}
    (p q : (Fin M → α) → ℝ) (test : (Fin M → α) → Bool)
    (mu : ℝ) (hTV : TotalVariation p q ≤ mu)
    (hmass : ∑ x, p x = ∑ x, q x) :
    TestAdvantage p q test ≤ mu := by
  calc
    TestAdvantage p q test ≤ TotalVariation p q :=
      test_advantage_le_totalVariation p q test hmass
    _ ≤ mu := hTV

end Qatlib.Papers.NoisyCircuit22.MainResults.Simulation
