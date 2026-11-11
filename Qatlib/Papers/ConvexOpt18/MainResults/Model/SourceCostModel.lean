/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceConvexModel

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 cost model and algorithm interfaces

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3 (18 Dec 2019).

The paper states its headline results in the `Õ`-calculus (`O~(f) = f · log^{O(1)}`); this
module fixes that calculus and the algorithm interfaces used by the upper- and lower-bound
claims.  It is a *model* file: the query/gate counts are data of the interface, while the
mathematical accuracy guarantees are ordinary predicates on `Pt n`.

Honest boundary: the paper fixes no machine model beyond Definitions 2.4--2.7 (oracle
interfaces).  We therefore record an algorithm as a record carrying (a) its oracle-call and
gate counts, (b) its success probability, and (c) the accuracy guarantee on the concrete
convex-optimization instance.  This is exactly the level at which the paper's theorems are
stated.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- `g = Õ(f)`: there are constants `C > 0`, `k` with `g(n) ≤ C f(n) (log(n+3)+1)ᵏ` for
every dimension `n` (the paper's `Õ` suppresses polylogarithmic factors in `n, R, r, ε`).
The base `log(n+3)+1` is `≥ 1` for all `n`, so powers are monotone in the exponent; it is
within a constant factor of `log(n+2)` and only serves as a convenient majorant. -/
def TildeO (g f : ℕ → ℝ) : Prop :=
  ∃ C k : ℕ, 0 < C ∧ ∀ n : ℕ, g n ≤ (C : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ k

/-- `poly(n)` bound: `g(n) ≤ c (n+2)^d`. -/
def PolyBounded (g : ℕ → ℝ) : Prop :=
  ∃ c d : ℕ, ∀ n : ℕ, g n ≤ (c : ℝ) * ((n : ℝ) + 2) ^ d

/-- The `tildeO_of_le` result for the ConvexOpt18 paper model. -/
lemma tildeO_of_le {g h f : ℕ → ℝ} (hgh : ∀ n, g n ≤ h n) (hh : TildeO h f) : TildeO g f := by
  obtain ⟨C, k, hC, hbound⟩ := hh
  exact ⟨C, k, hC, fun n => (hgh n).trans (hbound n)⟩

/-- The `TildeO.add` result for the ConvexOpt18 paper model. -/
lemma TildeO.add {g₁ g₂ f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h₁ : TildeO g₁ f) (h₂ : TildeO g₂ f) : TildeO (fun n => g₁ n + g₂ n) f := by
  obtain ⟨C₁, k₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, k₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, max k₁ k₂, by positivity, fun n => ?_⟩
  have hlog : 1 ≤ Real.log ((n : ℝ) + 3) + 1 := by
    have h0 : 0 ≤ Real.log ((n : ℝ) + 3) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have h₁' : g₁ n ≤ (C₁ : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ k₁ := hb₁ n
  have h₂' : g₂ n ≤ (C₂ : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ k₂ := hb₂ n
  have hmono₁ : (Real.log ((n : ℝ) + 3) + 1) ^ k₁
      ≤ (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hlog (le_max_left _ _)
  have hmono₂ : (Real.log ((n : ℝ) + 3) + 1) ^ k₂
      ≤ (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ :=
    pow_le_pow_right₀ hlog (le_max_right _ _)
  have hc₁ : 0 ≤ (C₁ : ℝ) * f n := mul_nonneg (by positivity) (hf n)
  have hc₂ : 0 ≤ (C₂ : ℝ) * f n := mul_nonneg (by positivity) (hf n)
  have hsum : g₁ n + g₂ n ≤
      (C₁ : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ +
        (C₂ : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ := by
    exact add_le_add
      (h₁'.trans (mul_le_mul_of_nonneg_left hmono₁ hc₁))
      (h₂'.trans (mul_le_mul_of_nonneg_left hmono₂ hc₂))
  calc g₁ n + g₂ n
      ≤ (C₁ : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ +
          (C₂ : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ := hsum
    _ = ((C₁ + C₂ : ℕ) : ℝ) * f n * (Real.log ((n : ℝ) + 3) + 1) ^ max k₁ k₂ := by
        push_cast; ring

/-- The `TildeO.const` result for the ConvexOpt18 paper model. -/
lemma TildeO.const (c : ℕ) : TildeO (fun _ => (c : ℝ)) (fun _ => 1) := by
  refine ⟨c + 1, 0, by positivity, fun n => ?_⟩
  simp only [pow_zero, mul_one]
  push_cast
  linarith

/-- The paper's convex-optimization accuracy guarantee (Section 1): the output `x` lies in
the `ε`-neighborhood `B₂(K, ε)` of `K` and satisfies `f(x) ≤ min_{y∈K} f(y) + ε`
(cf. (1.7), (2.4) with the error term `ζ` set to `ε`). -/
def ConvexOptimizationGuarantee {n : ℕ} (f : Pt n → ℝ) (K : Set (Pt n)) (ε : ℝ)
    (x : Pt n) : Prop :=
  x ∈ neighborhood K ε ∧ ∀ y ∈ K, f x ≤ f y + ε

/-- A quantum algorithm for convex optimization, recorded at the paper's interface level:
oracle-call counts, gate count, tolerated oracle error, success probability, and the
accuracy guarantee attained by its output. -/
structure ConvexOptimizationAlgorithm {n : ℕ} (f : Pt n → ℝ) (K : Set (Pt n)) where
  memQueries : ℕ
  evalQueries : ℕ
  gates : ℕ
  memberError : ℝ
  ε : ℝ
  successProb : ℝ
  output : Pt n
  guarantee : ConvexOptimizationGuarantee f K ε output
  success_ge : 9 / 10 ≤ successProb

/-- A quantum algorithm for a membership-oracle-to-optimization reduction (Definition 2.7
output produced from Definition 2.5 queries). -/
structure OptimizationOracleAlgorithm {n : ℕ} (K : Set (Pt n)) where
  memQueries : ℕ
  gates : ℕ
  ε : ℝ
  oracle : OptimizationOracle K
  memberError : ℝ
  successProb : ℝ
  success_ge : 9 / 10 ≤ successProb

/-- Query counts of the paper's separation-to-optimization pipeline (Theorem 2.5 of [21] plus
Theorem 2.4): `O(n log(nκ/ε))` separation queries, each implemented with `Õ(1)` membership
queries.  We record the composite count `sepQueries * memQueriesPerSep`. -/
def membershipToOptimizationQueryCount (sepQueries memPerSep : ℕ) : ℕ :=
  sepQueries * memPerSep

end Qatlib.Papers.ConvexOpt18.MainResults
