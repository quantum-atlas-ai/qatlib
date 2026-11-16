/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DistTesting09.MainResults.Defs
public import Qatlib.Papers.DistTesting09.MainResults.LowerBounds
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section


/-!
# A classical uniformity lower bound for symmetric tests

This module proves the fixed-sample version of Corollary 1 of
arXiv:0907.3920v1, Section 6.3. The test must be invariant under relabeling the
outcomes, as in the fingerprint reduction preceding Lemma 11. Without this
condition the known half-support distribution is easily distinguished by its labels.

The proof bounds the probability of any repeated sample by `M²` times the
largest point probability. All injective sample tuples are related by an
outcome permutation, so a symmetric Boolean test agrees on these tuples.
This gives a direct birthday-bound proof without Poissonization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.DistTesting09.MainResults.Defs

namespace Qatlib.Papers.DistTesting09.MainResults.LowerBounds

variable {N M : ℕ}

/-- Two distinct sample coordinates have a prescribed common value with its squared mass. -/
private theorem pair_value (p : Dist N) (a b : Fin M) (hab : a ≠ b) (x : Fin N) :
    p.probEvent (fun S => S a = x ∧ S b = x) = p.prob x * p.prob x := by
  classical
  simpa [FinDist.probEvent, hab, Ne.symm hab, Finset.sum_filter,
    Finset.sum_ite_eq', pow_two] using
    p.probOf_subset_product (fun y => y = x) ({a, b} : Finset (Fin M))

/-- The probability of a collision between two specified distinct coordinates is at most
the largest point probability. -/
private theorem pair_bound (p : Dist N) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ x, p.prob x ≤ C) (a b : Fin M) :
    p.probEvent (fun S => a ≠ b ∧ S a = S b) ≤ C := by
  classical
  by_cases hab : a = b
  · simpa [FinDist.probEvent, hab] using hC
  · calc
      _ ≤ p.probEvent (fun S => ∃ x : Fin N, S a = x ∧ S b = x) :=
        probEvent_mono p _ _ (fun S h => ⟨S a, rfl, h.2.symm⟩)
      _ ≤ ∑ x : Fin N, p.probEvent (fun S => S a = x ∧ S b = x) :=
        FinDist.union_bound p (fun x S => S a = x ∧ S b = x)
      _ = ∑ x : Fin N, p.prob x * p.prob x :=
        Finset.sum_congr rfl (fun x _ => pair_value p a b hab x)
      _ ≤ ∑ x : Fin N, C * p.prob x :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hp x) (p.nonneg x))
      _ = C := by rw [← Finset.mul_sum, p.sum_one, mul_one]

/-- A union bound over ordered pairs bounds the probability that a sample tuple repeats. -/
private theorem repeat_bound (p : Dist N) (C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ x, p.prob x ≤ C) :
    p.probEvent (L := M) (fun S => ¬ Function.Injective S) ≤ (M : ℝ) ^ 2 * C := by
  classical
  have hevent : (fun S : Fin M → Fin N => ¬ Function.Injective S) =
      (fun S => ∃ a, ∃ b, a ≠ b ∧ S a = S b) := by
    funext S
    apply propext
    constructor
    · intro h
      by_contra hn
      apply h
      intro a b hab
      by_contra hne
      exact hn ⟨a, b, hne, hab⟩
    · rintro ⟨a, b, hne, hab⟩ hinj
      exact hne (hinj hab)
  simp only [hevent]
  calc
    _ ≤ ∑ a : Fin M, p.probEvent (fun S => ∃ b, a ≠ b ∧ S a = S b) :=
      FinDist.union_bound p (fun a S => ∃ b, a ≠ b ∧ S a = S b)
    _ ≤ ∑ a : Fin M, ∑ b : Fin M, p.probEvent (fun S => a ≠ b ∧ S a = S b) :=
      Finset.sum_le_sum (fun a _ =>
        FinDist.union_bound p (fun b S => a ≠ b ∧ S a = S b))
    _ ≤ ∑ _a : Fin M, ∑ _b : Fin M, C :=
      Finset.sum_le_sum (fun a _ =>
        Finset.sum_le_sum (fun b _ => pair_bound p C hC hp a b))
    _ = (M : ℝ) ^ 2 * C := by simp [pow_two, mul_assoc]

/-- The stated sample budget makes repeats have probability less than one third whenever
each outcome has probability at most `2 / N`. -/
private theorem repeat_lt (hN : 2 ≤ N)
    (hM : (M : ℝ) ≤ (1 / 32) * Real.sqrt (N : ℝ))
    (p : Dist N) (hp : ∀ x, p.prob x ≤ 2 / (N : ℝ)) :
    p.probEvent (L := M) (fun S => ¬ Function.Injective S) < (1 : ℝ) / 3 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hscaled : 32 * (M : ℝ) ≤ Real.sqrt (N : ℝ) := by linarith
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 32 * (M : ℝ)) hscaled
  have hMsq : (M : ℝ) ^ 2 ≤ (N : ℝ) / 1024 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hbound := repeat_bound (M := M) p (2 / (N : ℝ)) (by positivity) hp
  have hnum : (M : ℝ) ^ 2 * (2 / (N : ℝ)) < (1 : ℝ) / 3 := by
    rw [← mul_div_assoc, div_lt_iff₀ hNpos]
    nlinarith
  exact hbound.trans_lt hnum

/-- Corollary 1 of arXiv:0907.3920v1, Section 6.3, for deterministic tests invariant under
relabeling outcomes. With at most `sqrt N / 32` samples, such a test cannot accept uniformity
with probability at least `2/3` and accept the flat half-support law with probability at most
`1/3`. The symmetry premise makes explicit the fingerprint reduction before Lemma 11. -/
theorem corollary1_classical_lower_bound [NeZero N] (hN : 2 ≤ N) (M : ℕ)
    (hM : (M : ℝ) ≤ (1 / 32) * Real.sqrt (N : ℝ)) (p : Dist N)
    (hp : ∀ i : Fin N, p.prob i = if (i : ℕ) < N / 2 then 2 / (N : ℝ) else 0) :
    ∀ test : (Fin M → Fin N) → Bool,
      (∀ (σ : Equiv.Perm (Fin N)) (S : Fin M → Fin N), test (σ ∘ S) = test S) →
      ¬ ((2 : ℝ) / 3 ≤ (uniform N).probEvent (L := M) (fun S => test S = true) ∧
          p.probEvent (L := M) (fun S => test S = true) ≤ (1 : ℝ) / 3) := by
  classical
  intro test hsym htest
  have hu : ∀ i : Fin N, (uniform N).prob i ≤ 2 / (N : ℝ) := by
    intro i
    rw [uniform_prob, ← one_div]
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)
  have hpmax : ∀ i : Fin N, p.prob i ≤ 2 / (N : ℝ) := by
    intro i
    rw [hp i]
    split
    · exact le_rfl
    · positivity
  have hbu := repeat_lt hN hM (uniform N) hu
  have hbp := repeat_lt hN hM p hpmax
  have hex : ∃ S : Fin M → Fin N, Function.Injective S ∧ test S = true := by
    by_contra h
    have hle := probEvent_mono (uniform N) (fun S : Fin M → Fin N => test S = true)
      (fun S => ¬ Function.Injective S) (fun S hs hinj => h ⟨S, hinj, hs⟩)
    linarith [htest.1]
  obtain ⟨S, hS, htestS⟩ := hex
  have hall : ∀ T : Fin M → Fin N, Function.Injective T → test T = true := by
    intro T hT
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair S T hS hT
    have hcomp : σ ∘ S = T := funext hσ
    rw [← hcomp, hsym, htestS]
  have hle := probEvent_mono p (Function.Injective : (Fin M → Fin N) → Prop)
    (fun T => test T = true) hall
  have hcompl := probEvent_compl p (Function.Injective : (Fin M → Fin N) → Prop)
  linarith [htest.2]

end Qatlib.Papers.DistTesting09.MainResults.LowerBounds
