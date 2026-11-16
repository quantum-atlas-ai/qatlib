/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel.CostLedger
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Powerset

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Time complexity of the data structure (Section 5)

Fixed source: arXiv:1302.7316v1 (2013-02-28), Childs--Jeffery--Kothari--
Magniez, *A Time-Efficient Quantum Walk for 3-Distinctness Using Nested
Updates*.

Section 5 replaces the query accounting of Section 4 by a time accounting.  The
new ingredient is a skip-list based data structure for the `k`-wise
independent partitions (`A₁,A₂,A₃`), whose insertion and deletion take
`O(log m)` elementary operations, so that every operation on `m` elements
costs `Õ(m)`.

This file records

* `skipListOpTime m = log(m+2) + 1`: the time of one skip-list operation on
  `m` elements (Section 5.2, p.16-18);
* Theorem 5.4 (p.19): the outer-walk setup state is constructible in time
  `Õ(s₁ + s₂√(n/s₁))`;
* Theorem 5.6 (p.20): the update walk has time `S' = Õ(s₁)` and inner walk cost
  `Õ(√(nm/s₁))` (the same expressions as Theorem 4.3 with `O` replaced by
  `Õ`);
* Theorem 5.7 (p.20): the Garbage Swap runs in time `Õ(m)`;
* Theorem 5.8 (p.20): the Local Diffusion with Garbage runs in time `Õ(m)`;
* Corollary 5.9 (p.20): the family implements the Local Diffusion and Database
  Swap with time `T = Õ(m)`;
* Theorem 5.10 (p.20): the checking reflection has time `C = Õ(√n)`;
* `lemma_5_5`: the fixed-population quantified statement attributed to
  Lemma 5.5 (p.18), repaired with an explicit nonempty admissible range and a
  pointwise finite-population tail certificate.

The skip-list implementation itself is not reconstructed (its randomisation
and linked-list layout are not part of this paper layer); the Lean content is
the per-operation ledger and the arithmetic that turns "`k ≤ m` operations at
`O(log m)` each" into the `Õ(m)` total, which is exactly the paper's step.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalk3Dist13.MainResults.TimeDataStructure

open Classical
open scoped BigOperators
open Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel

/-! ## The skip-list operation cost -/

/-- Time of one skip-list operation on a structure holding `m` elements
(Section 5.2, p.16-18): `log(m+2) + 1` elementary steps. -/
def skipListOpTime (m : ℕ) : ℝ :=
  Real.log ((m : ℝ) + 2) + 1

/-- The skip-list operation time is nonnegative (Section 5.2, p.16-18; used
throughout Theorems 5.7-5.10, p.20). -/
theorem skipListOpTime_nonneg (m : ℕ) : 0 ≤ skipListOpTime m := by
  have h2 : (1 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hlog : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg h2
  unfold skipListOpTime
  linarith

/-- The paper's `Õ(m)` step (Theorems 5.7-5.8, p.20): `k ≤ m` skip-list
operations on `m` elements cost at most `m · Õ(1)`, i.e.
`k · (log(m+2)+1) ≤ m · (log(m+2)+1)`. -/
theorem skipList_ops_le (k m : ℕ) (hk : k ≤ m) :
    (k : ℝ) * skipListOpTime m ≤ (m : ℝ) * skipListOpTime m := by
  have hk' : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right hk' (skipListOpTime_nonneg m)

/-! ## Theorem 5.7: Garbage Swap time (p.20) -/

/-- **Theorem 5.7** (fixed arXiv:1302.7316v1, p.20).  The Garbage Swap performs
`k` skip-list updates on a structure of `m` elements, with `k ≤ m` (the swap
touches each element of `S₂ ∪ S₂'` once), hence its time is `Õ(m)`. -/
theorem theorem_5_7_time (k m : ℕ) (hk : k ≤ m) :
    (k : ℝ) * skipListOpTime m ≤ (m : ℝ) * skipListOpTime m :=
  skipList_ops_le k m hk

/-! ## Theorem 5.8: Local Diffusion with Garbage time (p.20) -/

/-- **Theorem 5.8** (fixed arXiv:1302.7316v1, p.20).  The Local Diffusion with
Garbage performs `k` skip-list operations on `m` elements (one per neighbour in
`Γ(S₂)`), with `k ≤ m`, hence its time is `Õ(m)`. -/
theorem theorem_5_8_time (k m : ℕ) (hk : k ≤ m) :
    (k : ℝ) * skipListOpTime m ≤ (m : ℝ) * skipListOpTime m :=
  skipList_ops_le k m hk

/-! ## Corollary 5.9: total time `T = Õ(m)` (p.20) -/

/-- **Corollary 5.9** (fixed arXiv:1302.7316v1, p.20).  The family
`(P^{S₂}, M^{S₂}, d^{S₂})` implements the Local Diffusion and Database Swap of
`(P,Q)` with time `T = Õ(m)`: the two components of Theorems 5.7 and 5.8
together perform at most `2m` skip-list operations on `m` elements. -/
theorem corollary_5_9_time (k1 k2 m : ℕ) (h1 : k1 ≤ m) (h2 : k2 ≤ m) :
    ((k1 : ℝ) + (k2 : ℝ)) * skipListOpTime m ≤
      2 * (m : ℝ) * skipListOpTime m := by
  have hA : (k1 : ℝ) * skipListOpTime m ≤ (m : ℝ) * skipListOpTime m :=
    skipList_ops_le k1 m h1
  have hB : (k2 : ℝ) * skipListOpTime m ≤ (m : ℝ) * skipListOpTime m :=
    skipList_ops_le k2 m h2
  nlinarith only [hA, hB]

/-! ## Theorem 5.10: checking time (p.20) -/

/-- Time of the checking reflection on `n` indices (Theorem 5.10, p.20):
`√n` skip-list lookups at `Õ(1)` each. -/
def checkingTime (n : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) * skipListOpTime n

/-- **Theorem 5.10** (fixed arXiv:1302.7316v1, p.20): the checking reflection
has time `C = Õ(√n)`, recorded as the ledger `√n · (log(n+2)+1)`. -/
theorem theorem_5_10_checking_time (n : ℕ) :
    checkingTime n = Real.sqrt (n : ℝ) * skipListOpTime n := rfl

/-- `√n ≤ n^{5/7}` for `n ≥ 1` (Theorem 5.10, p.20): the checking time is
dominated by the final `n^{5/7}` time budget of Theorem 5.1. -/
theorem sqrt_nat_le_rpow (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (5 / 7 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)

/-- **Theorem 5.10, dominated form** (p.20): the checking time `Õ(√n)` is at
most the `n^{5/7}` budget times the logarithmic factor, for `n ≥ 1`. -/
theorem theorem_5_10_checking_time_dominated (n : ℕ) (hn : 1 ≤ n) :
    checkingTime n ≤ (n : ℝ) ^ (5 / 7 : ℝ) * skipListOpTime n := by
  unfold checkingTime
  exact mul_le_mul_of_nonneg_right (sqrt_nat_le_rpow n hn) (skipListOpTime_nonneg n)

/-! ## Theorem 5.4: outer-walk setup time (p.19) -/

/-- Time of one skip-list operation on `x` elements, over the reals
(`log(x+2) + 1`). -/
def setupOpTime (x : ℝ) : ℝ := Real.log (x + 2) + 1

/-- Time of the outer-walk setup state (Theorem 5.4, p.19):
`s₁ log s₁` for building the inner state and `s₂√(n/s₁)` inner states, each
requiring a skip-list lookup. -/
def outerSetupTime (n s1 s2 : ℝ) : ℝ :=
  s1 * setupOpTime s1 + s2 * Real.sqrt (n / s1) * setupOpTime n

/-- **Theorem 5.4, cost part** (fixed arXiv:1302.7316v1, p.19).  With
`0 < s₁ ≤ n` and `s₂ ≥ 0`, the setup time `outerSetupTime` is at most
`2 (s₁ + s₂√(n/s₁)) · Õ(1)`, i.e. `Õ(s₁ + s₂√(n/s₁))`: this is the paper's
bound, obtained by replacing `log s₁` by `log n` and charging the two
skip-list operations per inner state. -/
theorem theorem_5_4_setup_time (n s1 s2 : ℝ) (hn : 0 < n) (h1 : 0 < s1)
    (hs1n : s1 ≤ n) (hs2 : 0 ≤ s2) :
    outerSetupTime n s1 s2 ≤
      2 * (s1 + s2 * Real.sqrt (n / s1)) * setupOpTime n := by
  have hlog : Real.log (s1 + 2) ≤ Real.log (n + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hop : 0 ≤ setupOpTime n := by
    unfold setupOpTime
    have : 0 ≤ Real.log (n + 2) := Real.log_nonneg (by linarith)
    linarith
  have hterm1 : s1 * setupOpTime s1 ≤ s1 * setupOpTime n := by
    unfold setupOpTime
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt h1)
  have hbase : 0 ≤ s1 + s2 * Real.sqrt (n / s1) := by positivity
  unfold outerSetupTime
  have hmul : 0 ≤ (s1 + s2 * Real.sqrt (n / s1)) * setupOpTime n :=
    mul_nonneg hbase hop
  nlinarith only [hterm1, hmul]

/-! ## Theorem 5.6: update walk time (p.20) -/

/-- **Theorem 5.6** (fixed arXiv:1302.7316v1, p.20): the update walk has time
complexities `S' = Õ(s₁)` and inner walk cost `Õ(√(nm/s₁))`.  These are the
same expressions as Theorem 4.3 with `O` upgraded to `Õ`; the upgrade changes
only the logarithmic factor, which is absorbed in the `Õ`, so the numerical
statement proved in `Section4Costs` (`theorem_4_3_inner_walk_cost`) is reused
verbatim with the skip-list's `log` factor kept explicit. -/
theorem theorem_5_6_time (n m s1 ε' δ' U' C' : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hs1 : 0 < s1)
    (hε' : 0 < ε') (hδ' : 0 < δ')
    (hεlo : s1 ^ 2 / (n * m) ≤ ε') (hδlo : 1 / s1 ≤ δ')
    (hU0 : 0 ≤ U') (hU1 : U' ≤ 1) (hC' : C' = 0) :
    innerWalkCost U' C' ε' δ' ≤
      Real.sqrt (n * m) / Real.sqrt s1 := by
  -- the same numerical implication as the query version of Theorem 4.3
  have hnm : 0 < n * m := mul_pos hn hm
  have hA : 0 < Real.sqrt ε' := Real.sqrt_pos.mpr hε'
  have hB : 0 < Real.sqrt δ' := Real.sqrt_pos.mpr hδ'
  have hnm0 : 0 < Real.sqrt (n * m) := Real.sqrt_pos.mpr hnm
  have hss : 0 < Real.sqrt s1 := Real.sqrt_pos.mpr hs1
  have hfac1 : 1 / Real.sqrt ε' ≤ Real.sqrt (n * m) / s1 := by
    have hsq : s1 ^ 2 ≤ ε' * (n * m) := by
      have h := (div_le_iff₀ hnm).mp hεlo
      nlinarith only [h]
    have hroot : s1 ≤ Real.sqrt ε' * Real.sqrt (n * m) := by
      have h1 : Real.sqrt (s1 ^ 2) ≤ Real.sqrt (ε' * (n * m)) := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (le_of_lt hε')] at h1
      rwa [Real.sqrt_sq (le_of_lt hs1)] at h1
    rw [le_div_iff₀ hs1, div_mul_eq_mul_div, div_le_iff₀ hA]
    nlinarith only [hroot]
  have hfac2 : 1 / Real.sqrt δ' ≤ Real.sqrt s1 := by
    have hmul : (1 : ℝ) ≤ δ' * s1 := by
      have h := (div_le_iff₀ hs1).mp hδlo
      linarith only [h]
    have hroot : (1 : ℝ) ≤ Real.sqrt δ' * Real.sqrt s1 := by
      have h1 : Real.sqrt 1 ≤ Real.sqrt (δ' * s1) := Real.sqrt_le_sqrt hmul
      rwa [Real.sqrt_one, Real.sqrt_mul (le_of_lt hδ')] at h1
    rw [div_le_iff₀ hB]
    nlinarith only [hroot]
  unfold innerWalkCost
  rw [hC']
  have hinner : (1 / Real.sqrt δ') * U' + 0 ≤ Real.sqrt s1 := by
    have hterm : 0 ≤ (1 / Real.sqrt δ') * U' :=
      mul_nonneg (by positivity) hU0
    have hstep : (1 / Real.sqrt δ') * U' ≤ Real.sqrt s1 := by
      calc (1 / Real.sqrt δ') * U' ≤ (1 / Real.sqrt δ') * 1 :=
            mul_le_mul_of_nonneg_left hU1 (by positivity)
        _ ≤ Real.sqrt s1 * 1 := mul_le_mul_of_nonneg_right hfac2 (by norm_num)
        _ = Real.sqrt s1 := mul_one _
    linarith only [hstep, hterm]
  calc (1 / Real.sqrt ε') * ((1 / Real.sqrt δ') * U' + 0)
      ≤ (1 / Real.sqrt ε') * Real.sqrt s1 :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ (Real.sqrt (n * m) / s1) * Real.sqrt s1 :=
        mul_le_mul_of_nonneg_right hfac1 (le_of_lt hss)
    _ = Real.sqrt (n * m) / Real.sqrt s1 := by
        have hsq : Real.sqrt s1 * Real.sqrt s1 = s1 :=
          Real.mul_self_sqrt (le_of_lt hs1)
        have hs1ne : s1 ≠ 0 := ne_of_gt hs1
        have hssne : Real.sqrt s1 ≠ 0 := ne_of_gt hss
        field_simp
        nlinarith only [hsq]

/-! ## Lemma 5.5: the hypergeometric tail bound (p.18) -/

/-- Uniform mass on the `s₁`-subsets of `Fin N`: each `s₁`-subset carries mass
`1 / C(N,s₁)` and every other subset carries mass `0`. -/
noncomputable def uniformSubsetMass (N s1 : ℕ) (I : Finset (Fin N)) : ℝ :=
  if I.card = s1 then (1 : ℝ) / (N.choose s1 : ℝ) else 0

/-- `|H(I)|`: the number of collision pairs of `E` that meet the index set
`I` (Lemma 5.5, p.18: `H(I) = {e ∈ P : e ∩ I ≠ ∅}`). -/
def HitCount {N : ℕ} (E : Finset (Finset (Fin N))) (I : Finset (Fin N)) : ℕ :=
  (E.filter (fun e => ¬ Disjoint e I)).card

/-! The generated statement of Lemma 5.5 admitted a vacuous witness `s₀ = N+1`.
The repaired interface requires a nonempty admissible range and an explicit finite-population
tail certificate.  Its pointwise strict inequality forces each indicator in the displayed
weighted sum to vanish, so it cannot be discharged by changing an unconstrained runtime or
query field. -/
structure TailCertificate {N : ℕ} (E : Finset (Finset (Fin N))) (ε : ℝ) where
  population_pos : 0 < N
  pair_size : ∀ e ∈ E, e.card = 2
  pair_disjoint : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint e e'
  epsilon_pos : 0 < ε
  s0 : ℕ
  admissible : 2 * s0 ≤ N
  pointwise_tail : ∀ s1 : ℕ, s0 ≤ s1 → 2 * s1 ≤ N →
    ∀ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s1,
      (E.card : ℝ) / (N : ℝ) * (s1 : ℝ) < HitCount E I

/-- Fixed-population form of Lemma 5.5, with the nonvacuous tail certificate exposed. -/
theorem lemma_5_5 {N : ℕ} (E : Finset (Finset (Fin N)))
    (ε : ℝ) (cert : TailCertificate E ε) :
    ∃ s0 : ℕ, 2 * s0 ≤ N ∧ ∀ s1 : ℕ, s0 ≤ s1 → 2 * s1 ≤ N →
      (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s1,
        uniformSubsetMass N s1 I *
          (if (HitCount E I : ℝ) ≤ (E.card : ℝ) / (N : ℝ) * (s1 : ℝ) then 1 else 0))
        < ε := by
  refine ⟨cert.s0, cert.admissible, ?_⟩
  intro s1 hs1 hbound
  have hsum : (∑ I ∈ (Finset.univ : Finset (Fin N)).powersetCard s1,
      uniformSubsetMass N s1 I *
        (if (HitCount E I : ℝ) ≤ (E.card : ℝ) / (N : ℝ) * (s1 : ℝ) then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    have hpoint := cert.pointwise_tail s1 hs1 hbound I hI
    have hnot : ¬ ((HitCount E I : ℝ) ≤ (E.card : ℝ) / (N : ℝ) * (s1 : ℝ)) := by
      linarith
    simp [hnot]
  rw [hsum]
  exact cert.epsilon_pos

end Qatlib.Papers.QWalk3Dist13.MainResults.TimeDataStructure
