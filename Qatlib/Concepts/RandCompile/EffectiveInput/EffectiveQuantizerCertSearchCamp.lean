/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.EffectiveInput.EffectiveQuantizerCertSearchStat
import Qatlib.Concepts.DiamondQdrift.QuantizerCert.EffectiveCeilQuantizerLawCamp

/-!
# Correctness of finite quantizer certificate search

This module proves correctness of the bounded rational certificate search `certSearch`. It
relates rational and real certificates, identifies the least certified precision, and proves
invariance under changes to oracle values beyond the searched prefix. These input-quantization
guarantees support the qDRIFT framework of [Campbell2019].

## Main statements

* `certSearch_spec`: characterizes failure and the least successful precision.
* `effectiveQuantizerCertSearch`: proves the effective search specification and precision bound.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Qatlib.Concepts.RandCompile.EffectiveInput
open Matrix
open scoped Classical BigOperators

/-- The rational ceiling-quantizer certificate is equivalent to its real-valued counterpart. -/
private theorem certRat_iff_cert {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (k : ℕ) :
    ceilQuantizerCertRat M q k ↔ ceilQuantizerCert M q k := by
  unfold ceilQuantizerCertRat ceilQuantizerCert ratLowerMass
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rfl

/-- Rational ceiling-quantizer certification at precision `k` depends only on oracle values at
that precision. -/
private theorem certRat_congr {L : ℕ} (M : ℕ) {q q' : Fin L → ℕ → ℚ} (k : ℕ)
    (h : ∀ j, q' j k = q j k) :
    ceilQuantizerCertRat M q' k ↔ ceilQuantizerCertRat M q k := by
  unfold ceilQuantizerCertRat
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h j)]

/-- With zero fuel, the search returns precision zero exactly when the precision-zero rational
certificate holds. -/
private theorem certSearch_zero {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) :
    certSearch M q 0 = if ceilQuantizerCertRat M q 0 then some 0 else none := rfl

/-- Increasing the fuel by one preserves any previously successful search result. -/
private theorem certSearch_succ_some {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (fuel k : ℕ)
    (h : certSearch M q fuel = some k) : certSearch M q (fuel+1) = some k := by
  simp only [certSearch, h]

/-- After an unsuccessful search through `fuel`, the next step returns `fuel + 1` exactly when
its rational certificate holds. -/
private theorem certSearch_succ_none {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (fuel : ℕ)
    (h : certSearch M q fuel = none) :
    certSearch M q (fuel+1) =
      if ceilQuantizerCertRat M q (fuel+1) then some (fuel+1) else none := by
  simp only [certSearch, h]

/-- The search returns no result exactly when every precision within its fuel fails
certification. Any returned precision is certified, is within the fuel bound, and is the
least certified precision. -/
private theorem certSearch_spec {L : ℕ} (M : ℕ) (q : Fin L → ℕ → ℚ) (fuel : ℕ) :
    (certSearch M q fuel = none ↔ ∀ k ≤ fuel, ¬ ceilQuantizerCertRat M q k) ∧
    (∀ k : ℕ, certSearch M q fuel = some k →
      k ≤ fuel ∧ ceilQuantizerCertRat M q k ∧
      (∀ k' : ℕ, k' < k → ¬ ceilQuantizerCertRat M q k')) := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [certSearch_zero]
        constructor
        · intro h k hk
          have hk0 : k = 0 := Nat.le_zero.mp hk
          subst hk0
          intro hcert
          rw [if_pos hcert] at h
          exact absurd h (Option.some_ne_none 0)
        · intro h
          exact if_neg (h 0 (Nat.zero_le 0))
      · intro k hk
        rw [certSearch_zero] at hk
        by_cases hc : ceilQuantizerCertRat M q 0
        · rw [if_pos hc] at hk
          have hk0 : k = 0 := (Option.some.inj hk).symm
          subst hk0
          exact ⟨Nat.zero_le 0, hc, fun k' hk' => absurd hk' (Nat.not_lt_zero k')⟩
        · rw [if_neg hc] at hk
          exact absurd hk.symm (Option.some_ne_none k)
  | succ fuel ih =>
      obtain ⟨ihA, ihB⟩ := ih
      rcases hs : certSearch M q fuel with _ | k
      · refine ⟨?_, ?_⟩
        · rw [certSearch_succ_none M q fuel hs]
          constructor
          · intro h k' hk'
            rcases Nat.lt_or_ge k' (fuel+1) with hlt | hge
            · exact ihA.mp hs k' (Nat.le_of_lt_succ hlt)
            · have hkfuel : k' = fuel+1 := Nat.le_antisymm hk' hge
              subst hkfuel
              intro hcert
              rw [if_pos hcert] at h
              exact absurd h (Option.some_ne_none (fuel+1))
          · intro h
            exact if_neg (h (fuel+1) (le_refl (fuel+1)))
        · intro k' hk'
          rw [certSearch_succ_none M q fuel hs] at hk'
          by_cases hc : ceilQuantizerCertRat M q (fuel+1)
          · rw [if_pos hc] at hk'
            have hkfuel : k' = fuel+1 := (Option.some.inj hk').symm
            subst hkfuel
            exact ⟨le_refl (fuel+1), hc,
              fun k'' hk'' => ihA.mp hs k'' (Nat.le_of_lt_succ hk'')⟩
          · rw [if_neg hc] at hk'
            exact absurd hk'.symm (Option.some_ne_none k')
      · have hspec := ihB k hs
        refine ⟨?_, ?_⟩
        · rw [certSearch_succ_some M q fuel k hs]
          constructor
          · intro h
            exact absurd h (Option.some_ne_none k)
          · intro hcon
            exact (hcon k (by omega) hspec.2.1).elim
        · intro k' hk'
          rw [certSearch_succ_some M q fuel k hs] at hk'
          have hk'eq : k' = k := (Option.some.inj hk').symm
          subst hk'eq
          exact ⟨hspec.1.trans (by omega), hspec.2.1, hspec.2.2⟩

/-- Valid rational lower oracles with positive total mass and positive quantizer scale satisfy
`EffectiveQuantizerCertSearch`, including termination at the least certified precision, its
logarithmic bound, and dependence only on the searched oracle prefix. -/
theorem effectiveQuantizerCertSearch : EffectiveQuantizerCertSearch := by
  intro L M h q hor hlam hM
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hcertk, hbudget, -⟩ :=
      effectiveCeilQuantizerLaw L M h q hor hlam hM
    have hcertRatk : ceilQuantizerCertRat M q (effectiveQuantizerPrecision M q) :=
      (certRat_iff_cert M q _).mpr hcertk
    have hmin : ∀ k' < effectiveQuantizerPrecision M q,
        ¬ ceilQuantizerCert M q k' := by
      intro k' hk' hcert'
      have hsInf : effectiveQuantizerPrecision M q ≤ k' := Nat.sInf_le hcert'
      omega
    have hne : certSearch M q (effectiveQuantizerPrecision M q) ≠ none := by
      intro hnone
      have hcon := (certSearch_spec M q _).1.mp hnone
        (effectiveQuantizerPrecision M q) (le_refl _)
      exact hcon hcertRatk
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hne
    obtain ⟨hle, hcertRatk', hminRat⟩ := (certSearch_spec M q _).2 k hk
    have hkeq : k = effectiveQuantizerPrecision M q := by
      rcases Nat.lt_trichotomy k (effectiveQuantizerPrecision M q) with hlt | heq | hgt
      · exact absurd hcertRatk'
          (fun hc => hmin k hlt ((certRat_iff_cert M q k).mp hc))
      · exact heq
      · omega
    rw [hkeq] at hk
    exact ⟨effectiveQuantizerPrecision M q, hk, hbudget⟩
  · intro fuel k hk
    obtain ⟨-, hcertRatk, hminRat⟩ := (certSearch_spec M q fuel).2 k hk
    refine ⟨(certRat_iff_cert M q k).mp hcertRatk, ?_, rfl⟩
    intro k' hk' hcert'
    exact hminRat k' hk' ((certRat_iff_cert M q k').mpr hcert')
  · intro fuel q' hagree
    have hone : ∀ (fuel : ℕ) (q'' : Fin L → ℕ → ℚ),
        (∀ (j : Fin L) (k' : ℕ), k' ≤ fuel → q'' j k' = q j k') →
        certSearch M q'' fuel = certSearch M q fuel := by
      intro fuel
      induction fuel with
      | zero =>
          intro q'' hagree0
          rw [certSearch_zero, certSearch_zero]
          by_cases hc : ceilQuantizerCertRat M q 0
          · rw [if_pos hc, if_pos ((certRat_congr M 0
              (fun j => hagree0 j 0 (Nat.zero_le 0))).mpr hc)]
          · rw [if_neg hc, if_neg (fun H => hc
              ((certRat_congr M 0 (fun j => hagree0 j 0 (Nat.zero_le 0))).mp H))]
      | succ fuel ih =>
          intro q'' hagree0
          have hprev := ih q'' (fun j k' hk' => hagree0 j k' (Nat.le_succ_of_le hk'))
          have hlast : (if ceilQuantizerCertRat M q'' (fuel+1) then some (fuel+1) else none)
              = (if ceilQuantizerCertRat M q (fuel+1) then some (fuel+1) else none) := by
            by_cases hc : ceilQuantizerCertRat M q (fuel+1)
            · rw [if_pos hc, if_pos ((certRat_congr M (fuel+1)
                (fun j => hagree0 j (fuel+1) (le_refl (fuel+1)))).mpr hc)]
            · rw [if_neg hc, if_neg (fun H => hc
                ((certRat_congr M (fuel+1)
                  (fun j => hagree0 j (fuel+1) (le_refl (fuel+1)))).mp H))]
          rcases hs : certSearch M q fuel with _ | k
          · rw [certSearch_succ_none M q'' fuel (by rw [hprev]; exact hs),
              certSearch_succ_none M q fuel hs, hlast]
          · rw [certSearch_succ_some M q'' fuel k (by rw [hprev]; exact hs),
              certSearch_succ_some M q fuel k hs]
    exact hone fuel q' hagree

end Qatlib.Concepts.RandCompile.EffectiveInput
