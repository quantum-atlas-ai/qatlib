/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Monotone certificate-family search

This module models finite edge patterns, injective copies, and the monotone property of
containing a pattern from a certificate family. `PatternFinder` supplies sound per-pattern
outputs, finite seed spaces, exceptional seed bounds, and costs; `runFamily` chooses a
successful result from the family when one exists.

The family results combine soundness and completeness outside exceptional sets with a union
count and a summed cost bound. `corollary3_answer` packages these conclusions under explicit
support-size and per-pattern cost assumptions. Quantum-walk search provides the surrounding
algorithmic setting [MagniezNayakRolandSantha2011].

## Main statements

* `satisfies_mono`: monotonicity under adding host edges.
* `runFamily_fail_card`: the certificate-family failure-count bound.
* `corollary3_answer`: the combined witness, failure, and cost guarantees.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms

variable {n k : ℕ}

/-- The vertices occurring as either endpoint of an edge in the pattern. -/
def patternSupport (P : Finset (Fin k × Fin k)) : Finset (Fin k) :=
  P.image Prod.fst ∪ P.image Prod.snd

/-- An injective map from `Fin k` into `Fin n` that sends every pattern edge to an edge of the
host relation. -/
def PatternCopy (P : Finset (Fin k × Fin k)) (G : Finset (Fin n × Fin n))
    (f : Fin k → Fin n) : Prop :=
  Function.Injective f ∧ ∀ p ∈ P, (f p.1, f p.2) ∈ G

/-- The existence of an injective edge-preserving copy of the pattern in the host relation. -/
def PatternFound (P : Finset (Fin k × Fin k)) (G : Finset (Fin n × Fin n)) : Prop :=
  ∃ f, PatternCopy P G f

/-- The property that the host relation contains a copy of at least one pattern in the
certificate family. -/
def Satisfies (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n)) : Prop :=
  ∃ P ∈ certs, PatternFound P G

/-- Adding host edges preserves satisfaction of a pattern certificate family. -/
theorem satisfies_mono {certs : Finset (Finset (Fin k × Fin k))}
    {G G' : Finset (Fin n × Fin n)} (hsub : G ⊆ G') (h : Satisfies certs G) :
    Satisfies certs G' := by
  obtain ⟨P, hP, f, hinj, hedges⟩ := h
  exact ⟨P, hP, f, hinj, fun p hp => hsub (hedges p hp)⟩

/-- A pattern-finding interface with a finite nonempty seed type, a cost function, sound
outputs, and exceptional seed sets whose sizes satisfy a uniform inverse-power bound. -/
structure PatternFinder (n k : ℕ) where

  seed : Type

  [seedFin : Fintype seed]

  [seedNe : Nonempty seed]

  e : ℕ

  run : (Finset (Fin k × Fin k)) → Finset (Fin n × Fin n) → seed → Option (Fin k → Fin n)

  cost : (Finset (Fin k × Fin k)) → Finset (Fin n × Fin n) → seed → ℕ

  sound : ∀ (P : Finset (Fin k × Fin k)) (G : Finset (Fin n × Fin n)) (ρ : seed)
    (f : Fin k → Fin n), run P G ρ = some f → PatternCopy P G f

  misses : (Finset (Fin k × Fin k)) → Finset (Fin n × Fin n) → Finset seed

  miss_spec : ∀ (P : Finset (Fin k × Fin k)) (G : Finset (Fin n × Fin n)) (ρ : seed),
    PatternFound P G → run P G ρ = none → ρ ∈ misses P G

  miss_card : ∀ (P : Finset (Fin k × Fin k)) (G : Finset (Fin n × Fin n)),
    (misses P G).card * n ^ e ≤ Fintype.card seed

attribute [instance] PatternFinder.seedFin PatternFinder.seedNe

/-- Choose a successful finder result for a pattern in the certificate family when one exists,
and return `none` otherwise. -/
noncomputable def runFamily (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n))
    (ρ : ff.seed) : Option (Fin k → Fin n) := by
  classical
  exact if h : ∃ P ∈ certs, ∃ f, ff.run P G ρ = some f then ff.run (Classical.choose h) G ρ
    else none

/-- A result returned by the family finder is a valid copy of some pattern in the certificate
family. -/
theorem runFamily_sound (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n)) (ρ : ff.seed)
    {f : Fin k → Fin n} (h : runFamily ff certs G ρ = some f) :
    ∃ P ∈ certs, PatternCopy P G f := by
  classical
  by_cases hex : ∃ P ∈ certs, ∃ g, ff.run P G ρ = some g
  · rw [runFamily, dif_pos hex] at h
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1, ff.sound _ _ _ _ h⟩
  · rw [runFamily, dif_neg hex] at h
    exact absurd h (by simp)

/-- If the host satisfies the certificate family and the seed avoids every member's exceptional
set, the family finder returns a result. -/
theorem runFamily_complete (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n)) (ρ : ff.seed)
    (hφ : Satisfies certs G) (hρ : ∀ P ∈ certs, ρ ∉ ff.misses P G) :
    ∃ f, runFamily ff certs G ρ = some f := by
  classical
  obtain ⟨P, hP, hfound⟩ := hφ
  have hne : ff.run P G ρ ≠ none := by
    intro hnone
    exact hρ P hP (ff.miss_spec P G ρ hfound hnone)
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hne
  have hex : ∃ Q ∈ certs, ∃ g, ff.run Q G ρ = some g := ⟨P, hP, f, hf⟩
  obtain ⟨g, hg⟩ := (Classical.choose_spec hex).2
  exact ⟨g, by rw [runFamily, dif_pos hex]; exact hg⟩

/-- The union of the exceptional seed sets over all patterns in the certificate family. -/
def familyMisses (ff : PatternFinder n k) (certs : Finset (Finset (Fin k × Fin k)))
    (G : Finset (Fin n × Fin n)) : Finset ff.seed := by
  classical
  exact certs.biUnion fun P => ff.misses P G

/-- When the host satisfies the family, a seed on which the family finder returns `none` belongs
to the union of exceptional sets. -/
theorem runFamily_fail_mem_familyMisses (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n)) (ρ : ff.seed)
    (hφ : Satisfies certs G) (h : runFamily ff certs G ρ = none) :
    ρ ∈ familyMisses ff certs G := by
  classical
  obtain ⟨P, hP, hfound⟩ := hφ
  refine Finset.mem_biUnion.mpr ⟨P, hP, ?_⟩
  refine ff.miss_spec P G ρ hfound ?_
  by_contra hne
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.mp hne
  have hex : ∃ Q ∈ certs, ∃ g, ff.run Q G ρ = some g := ⟨P, hP, f, hf⟩
  rw [runFamily, dif_pos hex] at h
  obtain ⟨g, hg⟩ := (Classical.choose_spec hex).2
  rw [hg] at h
  cases h

/-- The seeds for which the host satisfies the certificate family but the family finder returns
`none`. -/
def familyFail (ff : PatternFinder n k) (certs : Finset (Finset (Fin k × Fin k)))
    (G : Finset (Fin n × Fin n)) : Finset ff.seed := by
  classical
  exact Finset.univ.filter fun ρ => Satisfies certs G ∧ runFamily ff certs G ρ = none

/-- The number of family-failure seeds, multiplied by `n^ff.e`, is at most the number of
certificates times the total seed count. -/
theorem runFamily_fail_card (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n)) :
    (familyFail ff certs G).card * n ^ ff.e ≤ certs.card * Fintype.card ff.seed := by
  classical
  have hle : (familyFail ff certs G).card ≤ (familyMisses ff certs G).card := by
    refine Finset.card_le_card fun ρ hρ => ?_
    simp only [familyFail, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    exact runFamily_fail_mem_familyMisses ff certs G ρ hρ.1 hρ.2
  have hbound : ((familyMisses ff certs G).card) * n ^ ff.e ≤
      certs.card * Fintype.card ff.seed := by
    have hsplit : ((familyMisses ff certs G).card) * n ^ ff.e ≤
        ∑ P ∈ certs, ((ff.misses P G).card * n ^ ff.e) := by
      have hunion := Finset.card_biUnion_le (s := certs) (t := fun P => ff.misses P G)
      calc ((familyMisses ff certs G).card) * n ^ ff.e
          ≤ (∑ P ∈ certs, (ff.misses P G).card) * n ^ ff.e :=
            Nat.mul_le_mul_right _ hunion
        _ = ∑ P ∈ certs, ((ff.misses P G).card * n ^ ff.e) := by
            rw [Finset.sum_mul]
    refine hsplit.trans ?_
    calc ∑ P ∈ certs, ((ff.misses P G).card * n ^ ff.e)
        ≤ ∑ _P ∈ certs, Fintype.card ff.seed :=
          Finset.sum_le_sum fun P _ => ff.miss_card P G
      _ = certs.card * Fintype.card ff.seed := by
          rw [Finset.sum_const, smul_eq_mul]
  exact (Nat.mul_le_mul_right _ hle).trans hbound

/-- The sum of the per-pattern finder costs over the certificate family. -/
def familyCost (ff : PatternFinder n k) (certs : Finset (Finset (Fin k × Fin k)))
    (G : Finset (Fin n × Fin n)) (ρ : ff.seed) : ℕ :=
  ∑ P ∈ certs, ff.cost P G ρ

/-- If certificate supports have sizes between two and `k`, the assumed support-dependent costs
give total family cost at most `certs.card * c * (Nat.log 2 n + 2)^3 * n^(2 - 2/k)`. -/
theorem familyCost_le (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) (G : Finset (Fin n × Fin n)) (ρ : ff.seed)
    {c : ℝ} (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hsupp : ∀ P ∈ certs, 2 ≤ (patternSupport P).card)
    (hk : ∀ P ∈ certs, (patternSupport P).card ≤ k)
    (hcost : ∀ P ∈ certs, (ff.cost P G ρ : ℝ) ≤
      c * ((Nat.log 2 n : ℝ) + 2) ^ 3 *
        (n : ℝ) ^ (2 - 2 / ((patternSupport P).card : ℝ))) :
    (familyCost ff certs G ρ : ℝ) ≤
      certs.card * (c * ((Nat.log 2 n : ℝ) + 2) ^ 3 * (n : ℝ) ^ (2 - 2 / (k : ℝ))) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : ∀ P ∈ certs, (n : ℝ) ^ (2 - 2 / ((patternSupport P).card : ℝ)) ≤
      (n : ℝ) ^ (2 - 2 / (k : ℝ)) := by
    intro P hP
    refine Real.rpow_le_rpow_of_exponent_le hnR ?_
    have ht : (0 : ℝ) < ((patternSupport P).card : ℝ) := by
      have h2 := hsupp P hP
      exact_mod_cast (lt_of_lt_of_le (by norm_num) h2)
    have htk : ((patternSupport P).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk P hP
    have hdiv : 2 / (k : ℝ) ≤ 2 / ((patternSupport P).card : ℝ) := by
      have htk : ((patternSupport P).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk P hP
      exact div_le_div_of_nonneg_left (by norm_num) ht htk
    linarith
  have hmain : (∑ P ∈ certs, (ff.cost P G ρ : ℝ)) ≤
      ∑ _P ∈ certs,
        (c * ((Nat.log 2 n : ℝ) + 2) ^ 3 * (n : ℝ) ^ (2 - 2 / (k : ℝ))) := by
    refine Finset.sum_le_sum fun P hP => ?_
    refine (hcost P hP).trans ?_
    have hbase : (0 : ℝ) ≤ c * ((Nat.log 2 n : ℝ) + 2) ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left (hexp P hP) hbase
  calc (familyCost ff certs G ρ : ℝ) = ∑ P ∈ certs, (ff.cost P G ρ : ℝ) := by
        simp only [familyCost, Nat.cast_sum]
    _ ≤ _ := hmain
    _ = certs.card * (c * ((Nat.log 2 n : ℝ) + 2) ^ 3 * (n : ℝ) ^ (2 - 2 / (k : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Combine family-finder soundness, success outside all exceptional sets, the union
failure-count bound, and the stated total cost bound under the support-size and per-pattern
cost hypotheses. -/
theorem corollary3_answer (ff : PatternFinder n k)
    (certs : Finset (Finset (Fin k × Fin k))) {c : ℝ} (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hsupp : ∀ P ∈ certs, 2 ≤ (patternSupport P).card)
    (hk : ∀ P ∈ certs, (patternSupport P).card ≤ k)
    (hcost : ∀ (G : Finset (Fin n × Fin n)) (ρ : ff.seed) (P : Finset (Fin k × Fin k)),
      P ∈ certs →
      (ff.cost P G ρ : ℝ) ≤
        c * ((Nat.log 2 n : ℝ) + 2) ^ 3 *
          (n : ℝ) ^ (2 - 2 / ((patternSupport P).card : ℝ)))
    (G : Finset (Fin n × Fin n)) :
    (∀ (ρ : ff.seed) (f : Fin k → Fin n), runFamily ff certs G ρ = some f →
        ∃ P ∈ certs, PatternCopy P G f) ∧
      (∀ (ρ : ff.seed), Satisfies certs G → (∀ P ∈ certs, ρ ∉ ff.misses P G) →
        ∃ f, runFamily ff certs G ρ = some f) ∧
      (familyFail ff certs G).card * n ^ ff.e ≤ certs.card * Fintype.card ff.seed ∧
      (∀ ρ : ff.seed, (familyCost ff certs G ρ : ℝ) ≤
        certs.card * (c * ((Nat.log 2 n : ℝ) + 2) ^ 3 * (n : ℝ) ^ (2 - 2 / (k : ℝ)))) :=
  ⟨fun ρ _ => runFamily_sound ff certs G ρ,
    fun ρ hφ hρ => runFamily_complete ff certs G ρ hφ hρ,
    runFamily_fail_card ff certs G,
    fun ρ => familyCost_le ff certs G ρ hn hc hsupp hk (fun P hP => hcost G ρ P hP)⟩

end Qatlib.Concepts.WalkSearch.WalkAlgorithms
