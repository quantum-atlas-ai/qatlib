/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.IntegerFactor21.MainResults.Notation.SourceCost
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Output vocabulary for the factoring algorithms

Source: Harvey--Hittmeir, fixed arXiv:2105.11105v1.

Algorithm 4.6 (`Factoring (semi)primes`, p.11) and Theorem 1.1 (p.1) both
promise a deterministic procedure that, on input `N`, either returns the two
factors of a semiprime or certifies that `N` is prime.  `FactorResult N` makes
that output contract a type: every term of `FactorResult N` is *by
construction* either a nontrivial factorisation `N = d₁ * d₂` or a proof that
`N` is prime.  Inputs are explicitly restricted to `1 < N`, the domain on which
the factoring problem is posed.  Consequently, a function
`(N : ℕ) → 1 < N → FactorResult N` needs no separate correctness hypothesis --
its codomain already carries the specification.

`FactoringAlgorithm` bundles such a function with its bit-operation cost, and
`theorem11Bound` is the real-valued bound appearing in Theorem 1.1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.IntegerFactor21.MainResults.Notation

/-- Output of a factoring algorithm on input `N`: either a nontrivial
factorisation `N = d₁ * d₂` (both factors `> 1`), or a certificate that `N`
is prime.  This is the promise "returns p and q" / "returns N is prime" of
Algorithm 4.6 and Theorem 1.1. -/
inductive FactorResult (N : ℕ) : Type
  /-- A nontrivial factorisation `N = d₁ * d₂` with `1 < d₁` and `1 < d₂`. -/
  | factors (d₁ d₂ : ℕ) (h₁ : 1 < d₁) (h₂ : 1 < d₂) (hN : N = d₁ * d₂) : FactorResult N
  /-- A certificate that `N` is prime. -/
  | prime (hN : N.Prime) : FactorResult N

/-- A deterministic integer factorisation algorithm: a function assigning to
every `N` an output satisfying the factorisation contract, together with its
worst-case bit-operation cost `cost N` on input `N`. -/
structure FactoringAlgorithm where
  /-- The algorithm's output on input `N`. -/
  result : (N : ℕ) → 1 < N → FactorResult N
  /-- Worst-case bit-operation cost on input `N` (the paper's `F(N)`). -/
  cost : ℕ → ℕ

/-- Trial division has a mathematically correct output on every promised input:
either `N` is prime or a proper divisor and its complementary factor are both
nontrivial.  This is the existence witness used to show the interface is
inhabited independently of any complexity claim. -/
def trialDivisionResult (N : ℕ) (hN : 1 < N) : FactorResult N := by
  classical
  by_cases hp : N.Prime
  · exact FactorResult.prime hp
  · let hex := Nat.exists_dvd_of_not_prime2 (by omega) hp
    let d := Classical.choose hex
    have hdvd : d ∣ N := (Classical.choose_spec hex).1
    have hd : 2 ≤ d := (Classical.choose_spec hex).2.1
    have hlt : d < N := (Classical.choose_spec hex).2.2
    have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdvd
    have hqpos : 0 < N / d := Nat.div_pos (le_trans (by omega) (Nat.le_of_lt hlt)) (by omega)
    have hq : 1 < N / d := by
      by_contra hnq
      have hle : N / d ≤ 1 := Nat.le_of_not_gt hnq
      have hqone : N / d = 1 := by omega
      have : N = d := by simpa [hqone] using hmul.symm
      omega
    exact FactorResult.factors d (N / d) hd hq hmul.symm

/-- A concrete correct factoring algorithm (with a deliberately explicit
quadratic trial-division cost bound). -/
def trialDivisionAlgorithm : FactoringAlgorithm where
  result := trialDivisionResult
  cost := fun N => N * N

/-- The restricted factoring interface is inhabited. -/
theorem factoringAlgorithm_nonempty : Nonempty FactoringAlgorithm :=
  ⟨trialDivisionAlgorithm⟩

/-- The real-valued bound `N^{1/5} log^{16/5} N / (log log N)^{3/5}` of
Theorem 1.1 (p.1). -/
def theorem11Bound (N : ℕ) : ℝ :=
  (N : ℝ) ^ ((1 : ℝ) / 5) * (Real.log N) ^ ((16 : ℝ) / 5) /
    (Real.log (Real.log N)) ^ ((3 : ℝ) / 5)

/-- `A` achieves the bound of Theorem 1.1: for all sufficiently large `N`,
its cost is at most a constant times `theorem11Bound N`. -/
def AchievesTheorem11Bound (A : FactoringAlgorithm) : Prop :=
  ∃ N₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ N → (A.cost N : ℝ) ≤ C * theorem11Bound N

end Qatlib.Papers.IntegerFactor21.MainResults.Notation
