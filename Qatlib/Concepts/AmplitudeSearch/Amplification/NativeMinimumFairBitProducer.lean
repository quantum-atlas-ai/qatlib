/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs

/-!
# Exact masses for the dyadic threshold producer

This module proves the point masses of the uniform dyadic threshold producer and its bounded
rejection process. `thresholdRunLaw_mass` identifies accepted outcomes by a geometric rejection
factor and gives the remaining failure probability; the marginal results relate accepted indices
to the uniform initialization law used by minimum search.

The producer calculations support the initialization interface for the minimum-finding setting
of [DurrHoyer1996]. Auxiliary finite-PMF identities express mapped and bound masses as finite
real sums.

## Main statements

* `thresholdWords_ge`, `card_accepted`, and `card_rejected` count accepted and rejected dyadic
  words for a positive table size.
* `thresholdRoundLaw_some_mass` and `thresholdRoundLaw_none_mass` give the one-round
  accepted-index and rejection masses.
* `thresholdRunLaw_mass` gives the exact geometric accepted masses and the failure mass
  `thresholdRejectProb N ^ r`.
* `thresholdRunLaw_accepted_matches_frozen_initial` identifies each accepted-index marginal as
  the total acceptance probability times its uniform initialization mass.
- `thresholdRunLaw_total_mass` shows that the accepted and failed real masses sum to one.

## References

- [Dürr and Høyer, 1996][DurrHoyer1996]. *A quantum algorithm for finding the minimum*. 1996.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin.PlannedRetry

open Qatlib.Concepts.AmplitudeSearch.Amplification.Experiment
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false

open Qatlib
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib.Concepts.AmplitudeSearch.InterruptMin.AQuantumAlgorithmForFindingTheMinimum1999
open Qatlib
open Qatlib.Concepts.SearchStopping.GroverSuccess
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib
open scoped ENNReal BigOperators Classical

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

/-- The real-valued point mass of a finite PMF at a specified outcome. -/
noncomputable def realMass {α : Type*} [Fintype α] (p : PMF α) (a : α) : ℝ := (p a).toReal

/-- The real mass of `true` under the fair-bit law is one half. -/
theorem fairBitLaw_true : (fairBitLaw true).toReal = 1 / 2 := by
  rw [fairBitLaw, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]
  simp [Fintype.card_bool]

/-- The real mass of `false` under the fair-bit law is one half. -/
theorem fairBitLaw_false : (fairBitLaw false).toReal = 1 / 2 := by
  rw [fairBitLaw, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]
  simp [Fintype.card_bool]

/-- Every `k`-bit word has real mass `1 / 2 ^ k` under `fairWordLaw k`. -/
theorem fairWordLaw_toReal (k : ℕ) (w : Fin (2 ^ k)) :
    (fairWordLaw k w).toReal = 1 / (2 ^ k : ℝ) := by
  rw [fairWordLaw, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]
  simp [Fintype.card_fin, one_div]

/-- The threshold producer's word width equals the natural-number ceiling of `binaryLog N`. -/
theorem thresholdWidth_eq (N : ℕ) : thresholdWidth N = Nat.ceil (binaryLog N) := rfl

/-- The threshold word count is `2 ^ thresholdWidth N`. -/
theorem thresholdWords_eq (N : ℕ) : thresholdWords N = 2 ^ thresholdWidth N := rfl

/-- The threshold word count is positive for every `N`. -/
theorem thresholdWords_pos (N : ℕ) : 0 < thresholdWords N := by
  unfold thresholdWords
  positivity

/-- For positive `N`, the dyadic threshold word space contains at least `N` words. -/
theorem thresholdWords_ge (N : ℕ) (hN : 0 < N) : N ≤ thresholdWords N := by
  have hlog2 : Real.log 2 > 0 := Real.log_pos (by norm_num)
  have hceil : binaryLog N ≤ (thresholdWidth N : ℝ) := by
    rw [thresholdWidth_eq]
    exact_mod_cast Nat.le_ceil _
  have hprod : binaryLog N * Real.log 2 ≤ (thresholdWidth N : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hceil hlog2.le
  have hexp : Real.exp (binaryLog N * Real.log 2) ≤
      Real.exp ((thresholdWidth N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hprod
  have hid : Real.exp (binaryLog N * Real.log 2) = N := by
    rw [show binaryLog N * Real.log 2 = Real.log N by
          unfold binaryLog; field_simp]
    exact Real.exp_log (by exact_mod_cast hN)
  have htwo : ∀ (k : ℕ), Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, show (↑k + 1) * Real.log 2 = (↑k : ℝ) * Real.log 2 + Real.log 2 by ring,
        Real.exp_add, ih, Real.exp_log (by norm_num)]
      ring
  have hid2 : Real.exp ((thresholdWidth N : ℝ) * Real.log 2) = (thresholdWords N : ℝ) := by
    rw [thresholdWords, Nat.cast_pow]
    exact htwo (thresholdWidth N)
  have hfinal : (N : ℝ) ≤ (thresholdWords N : ℝ) := by
    rw [← hid, ← hid2]
    exact hexp
  exact_mod_cast hfinal

/-- A word is accepted as index `i` exactly when its natural-number value equals `i.val`. -/
theorem acceptThreshold_some_iff (N : ℕ) (w : Fin (thresholdWords N)) (i : Fin N) :
    acceptThreshold N w = some i ↔ w.val = i.val := by
  by_cases hw : w.val < N
  · simp only [acceptThreshold, dif_pos hw]
    constructor
    · intro hh
      have hinj : (⟨w.val, hw⟩ : Fin N) = i := Option.some.inj hh
      exact congrArg Fin.val hinj
    · intro hh
      have hv : (⟨w.val, hw⟩ : Fin N) = i := Fin.ext hh
      simp [hv]
  · simp only [acceptThreshold, dif_neg hw]
    constructor
    · intro h
      cases h
    · intro h
      have hwlt : w.val < N := by have hi := i.isLt; rwa [← h] at hi
      exact absurd hwlt hw

/-- Views an accepted dyadic word as an element of `Fin N` by retaining its value. -/
def acceptedWord (N : ℕ) (_hN : 0 < N) :
    {w : Fin (thresholdWords N) // w.val < N} → Fin N := fun w => ⟨w.val, w.property⟩

/-- Indexes a rejected dyadic word in `Fin (thresholdWords N - N)` by subtracting `N` from its
value. -/
def rejectedWord (N : ℕ) (_hN : 0 < N) :
    {w : Fin (thresholdWords N) // N ≤ w.val} → Fin (thresholdWords N - N) :=
  fun w => ⟨w.val - N, by omega⟩

/-- For positive `N`, exactly `N` dyadic words have values below `N`. -/
theorem card_accepted (N : ℕ) (hN : 0 < N) :
    Fintype.card {w : Fin (thresholdWords N) // w.val < N} = N := by
  have hNM : N ≤ thresholdWords N := thresholdWords_ge N hN
  have hinj : Function.Injective (acceptedWord N hN) := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    simpa [acceptedWord] using! congrArg (fun w => w.val) hxy
  have hsurj : Function.Surjective (acceptedWord N hN) := by
    intro i
    let w : {w : Fin (thresholdWords N) // w.val < N} :=
      ⟨⟨i.val, i.isLt.trans_le hNM⟩, i.isLt⟩
    refine ⟨w, ?_⟩
    apply Fin.ext
    rfl
  have e : {w : Fin (thresholdWords N) // w.val < N} ≃ Fin N :=
    Equiv.ofBijective (acceptedWord N hN) ⟨hinj, hsurj⟩
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- For positive `N`, exactly `thresholdWords N - N` dyadic words have values at least `N`. -/
theorem card_rejected (N : ℕ) (hN : 0 < N) :
    Fintype.card {w : Fin (thresholdWords N) // N ≤ w.val} = thresholdWords N - N := by
  have hNM : N ≤ thresholdWords N := thresholdWords_ge N hN
  have hinj : Function.Injective (rejectedWord N hN) := by
    intro x y hxy
    apply Subtype.ext
    have hx : N ≤ x.val := x.property
    have hy : N ≤ y.val := y.property
    have hval : x.val - N = y.val - N := by
      simpa [rejectedWord] using! congrArg (fun w => w.val) hxy
    omega
  have hsurj : Function.Surjective (rejectedWord N hN) := by
    intro k
    have hk' : k.val < thresholdWords N - N := k.isLt
    have h1 : N + k.val < thresholdWords N := by omega
    have h2 : N ≤ N + k.val := by omega
    refine ⟨⟨⟨N + k.val, h1⟩, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [rejectedWord]
    omega
  have e : {w : Fin (thresholdWords N) // N ≤ w.val} ≃ Fin (thresholdWords N - N) :=
    Equiv.ofBijective (rejectedWord N hN) ⟨hinj, hsurj⟩
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- Every accepted word has real mass `1 / 2 ^ thresholdWidth N` under the uniform word law. -/
theorem accepted_word_mass (N : ℕ) (w : {w : Fin (thresholdWords N) // w.val < N}) :
    (fairWordLaw (thresholdWidth N) w.1).toReal = 1 / (2 ^ thresholdWidth N : ℝ) :=
  fairWordLaw_toReal _ _

/-- Every rejected word has real mass `1 / 2 ^ thresholdWidth N` under the uniform word law. -/
theorem rejected_word_mass (N : ℕ) (w : {w : Fin (thresholdWords N) // N ≤ w.val}) :
    (fairWordLaw (thresholdWidth N) w.1).toReal = 1 / (2 ^ thresholdWidth N : ℝ) :=
  fairWordLaw_toReal _ _

/-- Each index has real mass `1 / N` under the minimum-search initialization law `iterationPMF N
hN`. -/
theorem threshold_matches_frozen_initial (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (iterationPMF N hN i).toReal = 1 / (N : ℝ) := by
  simp [iterationPMF, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]

/-- For positive `N`, the ratio of rejected words to all threshold words is strictly less than
one. -/
theorem reject_prob_lt_one (N : ℕ) (hN : 0 < N) :
    ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ) < 1 := by
  have hNM : N ≤ thresholdWords N := thresholdWords_ge N hN
  have hlt : (thresholdWords N - N : ℕ) < thresholdWords N := by omega
  have hpos : (0 : ℝ) < thresholdWords N := Nat.cast_pos.mpr (thresholdWords_pos N)
  rw [div_lt_one hpos]
  exact_mod_cast hlt

/-- An extended nonnegative real bounded above by one is finite. -/
theorem ennreal_ne_top_of_le_one {x : ℝ≥0∞} (h : x ≤ 1) : x ≠ ∞ := by
  intro hx
  subst hx
  exact absurd (show (∞ : ℝ≥0∞) ≤ 1 from h) (not_le_of_gt ENNReal.one_lt_top)

/-- On finite types, the real point mass of a bound PMF is the sum of the products of the input
masses and conditional output masses. -/
theorem bind_mass_real {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (f : α → PMF β)
    (b : β) :
    ((p.bind f) b).toReal = ∑ a, (p a).toReal * ((f a) b).toReal := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [ENNReal.toReal_mul]
  · intro a ha
    have h1 : p a ≤ 1 := PMF.coe_le_one p a
    have h2 : (f a) b ≤ 1 := PMF.coe_le_one (f a) b
    have h3 : p a * (f a) b ≤ 1 := by
      calc p a * (f a) b ≤ 1 * (f a) b := mul_le_mul_of_nonneg_right h1 (bot_le)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h2 (bot_le)
        _ = 1 := one_mul _
    exact ennreal_ne_top_of_le_one h3

/-- On finite types, the real point mass of a mapped PMF is the sum of input masses weighted by
the indicator of the target fiber. -/
theorem map_mass_real {α β : Type*} [Fintype α] [Fintype β] (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a, (p a).toReal * (if b = f a then 1 else 0) := by
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a ha
    by_cases h : b = f a
    · simp [h]
    · simp [h]
  · intro a ha
    by_cases h : b = f a
    · exact ennreal_ne_top_of_le_one (by simpa [h] using! (PMF.coe_le_one p a))
    · simp [h]

/-- A finite sum of the constant `c` over the elements satisfying a predicate equals the number
of those elements times `c`. -/
theorem sum_indicator_filter (α : Type*) [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℝ) :
    (∑ a ∈ (Finset.univ : Finset α), (if p a then c else 0))
      = (Finset.univ.filter p).card * c := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The real mass of a mapped uniform finite law equals the cardinality of the target fiber
divided by the cardinality of the source type. -/
theorem uniform_map_mass_real {α : Type*} [Fintype α] [Nonempty α] {β : Type*}
    (f : α → β) (b : β) :
    ((PMF.uniformOfFintype' α).map f b).toReal
      = (Finset.univ.filter (fun a => b = f a)).card * (1 / (Fintype.card α : ℝ)) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · calc
      (∑ a ∈ (Finset.univ : Finset α), (if b = f a then (PMF.uniformOfFintype' α) a else 0).toReal)
          = ∑ a ∈ (Finset.univ : Finset α),
              (if b = f a then (1 / (Fintype.card α : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : b = f a
            · rw [PMF.uniformOfFintype'_apply]
              simp [h, ENNReal.toReal_inv, ENNReal.toReal_natCast, div_eq_mul_inv]
            · simp [h]
      _ = (Finset.univ.filter (fun a => b = f a)).card * (1 / (Fintype.card α : ℝ)) :=
            sum_indicator_filter α (fun a => b = f a) (1 / (Fintype.card α : ℝ))
  · intro a ha
    by_cases h : b = f a
    · exact ennreal_ne_top_of_le_one (by
        simpa [h] using! (PMF.coe_le_one (PMF.uniformOfFintype' α) a))
    · simp [h]

/-- The real mass obtained by mapping the producer word law equals the number of words mapped to
the target divided by `thresholdWords N`. -/
theorem producerWordLaw_map_mass (N : ℕ) {β : Type*} (f : Fin (thresholdWords N) → β) (b : β) :
    ((producerWordLaw N).map f b).toReal
      = (Finset.univ.filter (fun a : Fin (thresholdWords N) => b = f a)).card
          * (1 / (thresholdWords N : ℝ)) := by
  letI : Nonempty (Fin (thresholdWords N)) :=
    ⟨⟨0, by unfold thresholdWords; positivity⟩⟩
  have h := uniform_map_mass_real f b
  unfold producerWordLaw
  rwa [show Fintype.card (Fin (thresholdWords N)) = thresholdWords N from Fintype.card_fin _] at h

/-- A dyadic word is rejected exactly when its value is at least `N`. -/
theorem acceptThreshold_none_iff (N : ℕ) (w : Fin (thresholdWords N)) :
    none = acceptThreshold N w ↔ N ≤ w.val := by
  by_cases hlt : w.val < N
  · have h : acceptThreshold N w = some ⟨w.val, hlt⟩ := by simp [acceptThreshold, hlt]
    simp [h, Nat.not_le.mpr hlt]
  · have h : acceptThreshold N w = none := by simp [acceptThreshold, hlt]
    simp [h, Nat.not_lt.mp hlt]

/-- For positive `N`, each accepted index has one-round real mass `1 / 2 ^ thresholdWidth N`. -/
theorem thresholdRoundLaw_some_mass (N : ℕ) (hN : 0 < N) (i : Fin N) :
    ((thresholdRoundLaw N) (some i)).toReal = 1 / (2 ^ thresholdWidth N : ℝ) := by
  letI : Nonempty (Fin (thresholdWords N)) :=
    ⟨⟨0, by unfold thresholdWords; positivity⟩⟩
  have hi : i.val < thresholdWords N := i.isLt.trans_le (thresholdWords_ge N hN)
  have hcard : (Finset.univ.filter (fun w : Fin (thresholdWords N) =>
      some i = acceptThreshold N w)).card = 1 := by
    have hset : Finset.univ.filter (fun w : Fin (thresholdWords N) =>
        some i = acceptThreshold N w) = {⟨i.val, hi⟩} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h' : acceptThreshold N w = some i := h.symm
        have h'' : w.val = i.val := (acceptThreshold_some_iff N w i).mp h'
        exact Fin.ext h''
      · intro h
        have h'' : w.val = i.val := congrArg Fin.val h
        exact ((acceptThreshold_some_iff N w i).mpr h'').symm
    rw [hset]
    simp
  have hcast : (thresholdWords N : ℝ) = (2 ^ thresholdWidth N : ℝ) := by
    rw [thresholdWords_eq]
    push_cast
    ring
  rw [thresholdRoundLaw, producerWordLaw]
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · calc
      (∑ a ∈ (Finset.univ : Finset (Fin (thresholdWords N))),
          (@ite ℝ≥0∞ (some i = acceptThreshold N a) (Classical.propDecidable _)
            (PMF.uniformOfFintype' (Fin (thresholdWords N)) a) 0).toReal)
          = ∑ a ∈ (Finset.univ : Finset (Fin (thresholdWords N))),
              (if some i = acceptThreshold N a then (1 / (thresholdWords N : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : some i = acceptThreshold N a
            · rw [PMF.uniformOfFintype'_apply]
              simp [h, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
                div_eq_mul_inv]
            · simp [h]
      _ = (Finset.univ.filter (fun a : Fin (thresholdWords N) =>
            some i = acceptThreshold N a)).card * (1 / (thresholdWords N : ℝ)) :=
            sum_indicator_filter (Fin (thresholdWords N))
              (fun a : Fin (thresholdWords N) => some i = acceptThreshold N a)
              (1 / (thresholdWords N : ℝ))
      _ = 1 / (thresholdWords N : ℝ) := by rw [hcard]; ring
      _ = 1 / (2 ^ thresholdWidth N : ℝ) := by rw [hcast]
  · intro a ha
    by_cases h : some i = acceptThreshold N a
    · exact ennreal_ne_top_of_le_one (by
        simpa [h] using! (PMF.coe_le_one (PMF.uniformOfFintype' (Fin (thresholdWords N))) a))
    · simp [h]

/-- For positive `N`, one-round rejection has real mass `(thresholdWords N - N) / thresholdWords
N`, with the subtraction taken in the natural numbers. -/
theorem thresholdRoundLaw_none_mass (N : ℕ) (hN : 0 < N) :
    ((thresholdRoundLaw N) (none : Option (Fin N))).toReal
      = ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ) := by
  letI : Nonempty (Fin (thresholdWords N)) :=
    ⟨⟨0, by unfold thresholdWords; positivity⟩⟩
  have hcard : (Finset.univ.filter (fun w : Fin (thresholdWords N) =>
      none = acceptThreshold N w)).card = thresholdWords N - N := by
    have hset : Finset.univ.filter (fun w : Fin (thresholdWords N) =>
        none = acceptThreshold N w)
        = Finset.univ.filter (fun w : Fin (thresholdWords N) => N ≤ w.val) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact acceptThreshold_none_iff N w
    rw [hset]
    have hsub := Fintype.card_subtype (fun w : Fin (thresholdWords N) => N ≤ w.val)
    rw [card_rejected N hN] at hsub
    exact hsub.symm
  rw [thresholdRoundLaw, producerWordLaw]
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · calc
      (∑ a ∈ (Finset.univ : Finset (Fin (thresholdWords N))),
          (@ite ℝ≥0∞ (none = acceptThreshold N a) (Classical.propDecidable _)
            (PMF.uniformOfFintype' (Fin (thresholdWords N)) a) 0).toReal)
          = ∑ a ∈ (Finset.univ : Finset (Fin (thresholdWords N))),
              (if none = acceptThreshold N a then (1 / (thresholdWords N : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases h : none = acceptThreshold N a
            · rw [PMF.uniformOfFintype'_apply]
              simp [h, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast,
                div_eq_mul_inv]
            · simp [h]
      _ = (Finset.univ.filter (fun a : Fin (thresholdWords N) =>
            none = acceptThreshold N a)).card * (1 / (thresholdWords N : ℝ)) :=
            sum_indicator_filter (Fin (thresholdWords N))
              (fun a : Fin (thresholdWords N) => none = acceptThreshold N a)
              (1 / (thresholdWords N : ℝ))
      _ = ((thresholdWords N - N : ℕ) : ℝ) * (1 / (thresholdWords N : ℝ)) := by rw [hcard]
      _ = ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ) := by
        rw [div_eq_mul_inv]
        congr 1
        norm_num
  · intro a ha
    by_cases h : none = acceptThreshold N a
    · exact ennreal_ne_top_of_le_one (by
        simpa [h] using! (PMF.coe_le_one (PMF.uniformOfFintype' (Fin (thresholdWords N))) a))
    · simp [h]

/-- The continuation law after one threshold draw: acceptance produces an outcome with zero
rejections, while rejection runs the remaining draws and increments accepted rejection
counts. -/
noncomputable def runContinuation {N r : ℕ} (o : Option (Fin N)) : PMF (ThresholdOutcome N (r + 1)) :=
  match o with
  | some i => PMF.pure (.accepted i ⟨0, by omega⟩)
  | none => (thresholdRunLaw N r).map (bumpOutcome)

/-- The law with `r + 1` available draws binds one-round sampling to `runContinuation`. -/
theorem thresholdRunLaw_eq_bind (N r : ℕ) :
    thresholdRunLaw N (r + 1) = (thresholdRoundLaw N).bind (runContinuation) := rfl

/-- If incrementing an outcome yields failure, the original outcome was failure. -/
theorem bumpOutcome_failed_preimage (N r : ℕ) (a : ThresholdOutcome N r)
    (h : (ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a) :
    a = (ThresholdOutcome.failed : ThresholdOutcome N r) := by
  cases a with
  | failed => rfl
  | accepted j m => simp [bumpOutcome] at h

/-- Mapping `bumpOutcome` over a threshold run preserves the real mass of the failed outcome. -/
theorem map_bump_failed (N r : ℕ) :
    (((thresholdRunLaw N r).map (bumpOutcome : ThresholdOutcome N r → ThresholdOutcome N (r + 1)))
        (ThresholdOutcome.failed : ThresholdOutcome N (r + 1))).toReal
      = ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal := by
  rw [map_mass_real]
  have hconv : ∀ a ∈ (Finset.univ : Finset (ThresholdOutcome N r)),
      ((thresholdRunLaw N r) a).toReal
        * (@ite ℝ ((ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a)
            (Classical.propDecidable _) 1 0)
        = (if (ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a
            then ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal
            else 0) := by
    intro a ha
    by_cases h : (ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a
    · have ha : a = (ThresholdOutcome.failed : ThresholdOutcome N r) :=
        bumpOutcome_failed_preimage N r a h
      subst ha
      simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl hconv]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun a : ThresholdOutcome N r =>
      (ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a)).card = 1 := by
    have hset : Finset.univ.filter (fun a : ThresholdOutcome N r =>
        (ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a)
        = {ThresholdOutcome.failed} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        exact bumpOutcome_failed_preimage N r a h
      · intro h
        subst h
        rfl
    rw [hset]
    simp
  rw [hcard]
  ring

/-- No outcome mapped by `bumpOutcome` is an accepted outcome with zero rejections. -/
theorem bumpOutcome_rejections_ne_zero (N r : ℕ) (a : ThresholdOutcome N r) (i : Fin N) :
    bumpOutcome a ≠ (ThresholdOutcome.accepted i ⟨0, by omega⟩ : ThresholdOutcome N (r + 1)) := by
  cases a with
  | failed => simp [bumpOutcome]
  | accepted j m =>
    intro h
    have hval := congrArg
      (fun x : ThresholdOutcome N (r + 1) => match x with
        | .accepted _ n => n.val
        | .failed => 0) h
    simp only [bumpOutcome] at hval
    exact absurd hval (by omega)

/-- An accepted outcome with index `i` and rejection count `k + 1` has the accepted outcome with
index `i` and count `k` as its only possible preimage under `bumpOutcome`. -/
theorem bumpOutcome_accepted_preimage (N r : ℕ) (i : Fin N) (k : Fin r) (a : ThresholdOutcome N r)
    (h : (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
        = bumpOutcome a) :
    a = (ThresholdOutcome.accepted i k : ThresholdOutcome N r) := by
  cases a with
  | failed => simp [bumpOutcome] at h
  | accepted j m =>
    have h' : (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
        = (ThresholdOutcome.accepted j ⟨m.val + 1, by omega⟩ : ThresholdOutcome N (r + 1)) := by
      simpa only [bumpOutcome] using! h
    have hj : i = j := by
      injection h'
    have hk : (k.val + 1 : ℕ) = m.val + 1 := by
      injection h' with hj hk'
      exact congrArg Fin.val hk'
    have hmk : m = k := by
      apply Fin.ext
      omega
    simp only [hj, hmk]

/-- After mapping `bumpOutcome` over a threshold run, an accepted outcome with zero rejections
has real mass zero. -/
theorem map_bump_zero_rejections (N r : ℕ) (i : Fin N) :
    (((thresholdRunLaw N r).map (bumpOutcome : ThresholdOutcome N r → ThresholdOutcome N (r + 1)))
        (ThresholdOutcome.accepted i ⟨0, by omega⟩ : ThresholdOutcome N (r + 1))).toReal = 0 := by
  rw [map_mass_real]
  have hconv : ∀ a ∈ (Finset.univ : Finset (ThresholdOutcome N r)),
      ((thresholdRunLaw N r) a).toReal
        * (@ite ℝ ((ThresholdOutcome.accepted i ⟨0, by omega⟩ : ThresholdOutcome N (r + 1))
            = bumpOutcome a) (Classical.propDecidable _) 1 0)
        = (if (ThresholdOutcome.accepted i ⟨0, by omega⟩ : ThresholdOutcome N (r + 1)) = bumpOutcome a
            then ((thresholdRunLaw N r) a).toReal else 0) := by
    intro a ha
    by_cases hc : (ThresholdOutcome.accepted i ⟨0, by omega⟩ : ThresholdOutcome N (r + 1))
        = bumpOutcome a
    · exact absurd hc.symm (bumpOutcome_rejections_ne_zero N r a i)
    · simp [hc]
  rw [Finset.sum_congr rfl hconv]
  rw [← Finset.sum_filter]
  have hempty : (Finset.univ.filter (fun a : ThresholdOutcome N r =>
      (ThresholdOutcome.accepted i ⟨0, by omega⟩ : ThresholdOutcome N (r + 1)) = bumpOutcome a)) = ∅ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      exact (bumpOutcome_rejections_ne_zero N r a i ha.symm).elim
    · intro h
      exact absurd h (by simp)
  rw [hempty]
  simp

/-- Mapping `bumpOutcome` shifts the real mass of an accepted outcome from rejection count `k`
to count `k + 1` without changing its index. -/
theorem map_bump_succ_rejections (N r : ℕ) (i : Fin N) (k : Fin r) :
    (((thresholdRunLaw N r).map (bumpOutcome : ThresholdOutcome N r → ThresholdOutcome N (r + 1)))
        (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))).toReal
      = ((thresholdRunLaw N r) (ThresholdOutcome.accepted i k : ThresholdOutcome N r)).toReal := by
  rw [map_mass_real]
  have hconv : ∀ a ∈ (Finset.univ : Finset (ThresholdOutcome N r)),
      ((thresholdRunLaw N r) a).toReal
        * (@ite ℝ ((ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
            = bumpOutcome a) (Classical.propDecidable _) 1 0)
        = (if (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
            = bumpOutcome a
            then ((thresholdRunLaw N r) (ThresholdOutcome.accepted i k : ThresholdOutcome N r)).toReal
            else 0) := by
    intro a ha
    by_cases h : (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
        = bumpOutcome a
    · have ha : a = (ThresholdOutcome.accepted i k : ThresholdOutcome N r) :=
        bumpOutcome_accepted_preimage N r i k a h
      subst ha
      simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl hconv]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun a : ThresholdOutcome N r =>
      (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
        = bumpOutcome a)).card = 1 := by
    have hset : Finset.univ.filter (fun a : ThresholdOutcome N r =>
        (ThresholdOutcome.accepted i ⟨k.val + 1, by omega⟩ : ThresholdOutcome N (r + 1))
          = bumpOutcome a)
        = {ThresholdOutcome.accepted i k} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        exact bumpOutcome_accepted_preimage N r i k a h
      · intro h
        subst h
        rfl
    rw [hset]
    simp
  rw [hcard]
  ring

/-- The real mass of a run outcome splits into the first-draw rejection contribution and the sum
of the first-draw acceptance contributions. -/
theorem thresholdRunLaw_mass_split (N r : ℕ) (o : ThresholdOutcome N (r + 1)) :
    ((thresholdRunLaw N (r + 1)) o).toReal
      = ((thresholdRoundLaw N) none).toReal * ((runContinuation none) o).toReal
        + ∑ x ∈ (Finset.univ : Finset (Option (Fin N))).erase none,
            ((thresholdRoundLaw N) x).toReal * ((runContinuation x) o).toReal := by
  classical
  rw [thresholdRunLaw_eq_bind, bind_mass_real]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Option (Fin N)))
    (fun x : Option (Fin N) => ((thresholdRoundLaw N) x).toReal * ((runContinuation x) o).toReal)
    (Finset.mem_univ none)]
  ring

/-- For positive `N`, acceptance of index `i` after `n` rejections has real mass
`thresholdRejectProb N ^ n.val / 2 ^ thresholdWidth N`, and failure after `r` draws has mass
`thresholdRejectProb N ^ r`. -/
theorem thresholdRunLaw_mass (N : ℕ) (hN : 0 < N) (r : ℕ) :
    (∀ (i : Fin N) (n : Fin r),
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal
        = thresholdRejectProb N ^ n.val * (1 / (2 ^ thresholdWidth N : ℝ)))
    ∧ ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal
        = thresholdRejectProb N ^ r := by
  have hq : thresholdRejectProb N = ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ) := rfl
  induction r with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro i n
        exact Fin.elim0 n
      · simp [thresholdRunLaw, thresholdRejectProb]
  | succ r ih =>
      have hnone := thresholdRoundLaw_none_mass N hN
      have hsome := thresholdRoundLaw_some_mass N hN
      refine ⟨?_, ?_⟩
      · intro i n
        by_cases hn0 : n.val = 0
        · have hfin : (n : Fin (r + 1)) = ⟨0, by omega⟩ := Fin.ext hn0
          rw [thresholdRunLaw_mass_split]
          have hone : (∑ x ∈ (Finset.univ : Finset (Option (Fin N))).erase none,
              ((thresholdRoundLaw N) x).toReal
                * ((runContinuation x) (ThresholdOutcome.accepted i n : ThresholdOutcome N (r + 1))).toReal)
              = ((thresholdRoundLaw N) (some i)).toReal
                  * ((PMF.pure (.accepted i ⟨0, by omega⟩))
                      (ThresholdOutcome.accepted i n : ThresholdOutcome N (r + 1))).toReal := by
            refine Finset.sum_eq_single (some i) ?_ ?_
            · intro b hb hne
              cases b with
              | none => exact absurd (Finset.mem_erase.mp hb).1 (by simp)
              | some j =>
                have hj : j ≠ i := by
                  intro hj
                  exact hne (by subst hj; rfl)
                have hne' : ¬(i = j ∧ n = (0 : Fin (r + 1))) := by
                  intro hc
                  obtain ⟨hij, _⟩ := hc
                  exact (Ne.symm hj) hij
                simp [runContinuation, PMF.pure_apply, hne']
            · intro h
              exact (h (Finset.mem_erase.mpr
                ⟨show (some i : Option (Fin N)) ≠ none by simp, Finset.mem_univ (some i)⟩)).elim
          rw [hone]
          simp only [PMF.pure_apply]
          rw [if_pos (congrArg _ hfin)]
          have hz : ((runContinuation none)
              (ThresholdOutcome.accepted i n : ThresholdOutcome N (r + 1))).toReal = 0 := by
            simp only [runContinuation]
            rw [hfin]
            exact map_bump_zero_rejections N r i
          rw [hz]
          rw [hsome]
          simp [hq, thresholdRejectProb, hn0]
        · have hn1 : 1 ≤ n.val := by omega
          have hnr : n.val ≤ r := by omega
          obtain ⟨k, hk⟩ : ∃ k : Fin r, n.val = k.val + 1 := by
            refine ⟨⟨n.val - 1, ?_⟩, ?_⟩
            · exact lt_of_lt_of_le (show n.val - 1 < n.val by omega) hnr
            · exact (Nat.sub_add_cancel hn1).symm
          rw [thresholdRunLaw_mass_split]
          have hone : (∑ x ∈ (Finset.univ : Finset (Option (Fin N))).erase none,
              ((thresholdRoundLaw N) x).toReal
                * ((runContinuation x) (ThresholdOutcome.accepted i n : ThresholdOutcome N (r + 1))).toReal) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro b hb
            cases b with
            | none => exact absurd (Finset.mem_erase.mp hb).1 (by simp)
            | some j =>
              have hne' : ¬(i = j ∧ n = (0 : Fin (r + 1))) := by
                intro hc
                obtain ⟨_, hn0'⟩ := hc
                exact hn0 (congrArg Fin.val hn0')
              simp [runContinuation, PMF.pure_apply, hne']
          rw [hone]
          have hfin' : (n : Fin (r + 1)) = ⟨k.val + 1, by omega⟩ := Fin.ext hk
          have hz : ((runContinuation none)
                (ThresholdOutcome.accepted i n : ThresholdOutcome N (r + 1))).toReal
              = ((thresholdRunLaw N r) (ThresholdOutcome.accepted i k : ThresholdOutcome N r)).toReal := by
            simp only [runContinuation]
            rw [hfin']
            exact map_bump_succ_rejections N r i k
          rw [hz, ih.1 i k, hnone, hq, hk]
          rw [pow_succ]
          ring
      · rw [thresholdRunLaw_mass_split]
        have hone : (∑ x ∈ (Finset.univ : Finset (Option (Fin N))).erase none,
            ((thresholdRoundLaw N) x).toReal
              * ((runContinuation x) (ThresholdOutcome.failed : ThresholdOutcome N (r + 1))).toReal) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro b hb
          cases b with
          | none => exact absurd (Finset.mem_erase.mp hb).1 (by simp)
          | some j => simp [runContinuation, PMF.pure_apply]
        rw [hone]
        have hz : ((runContinuation none) (ThresholdOutcome.failed : ThresholdOutcome N (r + 1))).toReal
            = ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal := by
          simp only [runContinuation]
          exact map_bump_failed N r
        rw [hz, ih.2, hnone, hq]
        rw [pow_succ]
        ring

/-- For positive `N`, the real mass of accepting index `i` after `n` rejections is
`thresholdRejectProb N ^ n.val / 2 ^ thresholdWidth N`. -/
theorem thresholdRunLaw_accepted_mass (N : ℕ) (hN : 0 < N) (r : ℕ) (i : Fin N) (n : Fin r) :
    ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal
      = thresholdRejectProb N ^ n.val * (1 / (2 ^ thresholdWidth N : ℝ)) :=
  (thresholdRunLaw_mass N hN r).1 i n

/-- For positive `N`, the real probability of exhausting `r` draws without acceptance is
`thresholdRejectProb N ^ r`. -/
theorem thresholdRunLaw_failed_mass (N : ℕ) (hN : 0 < N) (r : ℕ) :
    ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal
      = thresholdRejectProb N ^ r :=
  (thresholdRunLaw_mass N hN r).2

/-- Multiplying the finite geometric sum `∑ n : Fin r, q ^ n.val` by `1 - q` gives `1 - q ^ r`
for every real `q`. -/
theorem sum_fin_pow (q : ℝ) (r : ℕ) :
    (1 - q) * (∑ n : Fin r, q ^ n.val) = 1 - q ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hsucc : ∀ i : Fin r, (i.succ : Fin (r + 1)).val = i.val + 1 := fun _ => rfl
      have hstep : (∑ i : Fin r, q ^ (i.succ : Fin (r + 1)).val) = q * (∑ i : Fin r, q ^ i.val) := by
        calc
          (∑ i : Fin r, q ^ (i.succ : Fin (r + 1)).val) = ∑ i : Fin r, (q * q ^ i.val) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Fin.val_succ, pow_succ]
            ring
          _ = q * (∑ i : Fin r, q ^ i.val) := by rw [Finset.mul_sum]
      rw [Fin.sum_univ_succ, hstep]
      have hzero : (0 : Fin (r + 1)).val = 0 := rfl
      simp only [hzero, pow_zero]
      calc
        (1 - q) * (1 + q * (∑ i : Fin r, q ^ i.val))
            = (1 - q) + q * ((1 - q) * (∑ i : Fin r, q ^ i.val)) := by ring
        _ = (1 - q) + q * (1 - q ^ r) := by rw [ih]
        _ = 1 - q ^ r * q := by ring

/-- For positive `N`, one minus the rejection probability equals `N` times the mass of a single
dyadic word. -/
theorem one_sub_reject_prob (N : ℕ) (hN : 0 < N) :
    1 - thresholdRejectProb N = (N : ℝ) * (1 / (2 ^ thresholdWidth N : ℝ)) := by
  have hNM : N ≤ thresholdWords N := thresholdWords_ge N hN
  have hcast : ((thresholdWords N - N : ℕ) : ℝ) = (thresholdWords N : ℝ) - (N : ℝ) := by
    rw [Nat.cast_sub hNM]
  have hM : (thresholdWords N : ℝ) = (2 ^ thresholdWidth N : ℝ) := by
    rw [thresholdWords_eq]
    push_cast
    ring
  have h2w : (2 ^ thresholdWidth N : ℝ) ≠ 0 := by positivity
  rw [thresholdRejectProb, hcast, hM]
  field_simp
  ring

/-- For positive `N`, the total mass of accepting a fixed index, summed over rejection counts
and multiplied by `N`, equals `1 - thresholdRejectProb N ^ r`. -/
theorem thresholdRunLaw_accepted_marginal (N : ℕ) (hN : 0 < N) (r : ℕ) (i : Fin N) :
    (∑ n : Fin r,
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
      * (N : ℝ) = 1 - thresholdRejectProb N ^ r := by
  have hmass := thresholdRunLaw_accepted_mass N hN r i
  have hgeom := sum_fin_pow (thresholdRejectProb N) r
  have hone := one_sub_reject_prob N hN
  have hsum : (∑ n : Fin r,
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
      = (1 / (2 ^ thresholdWidth N : ℝ)) * (∑ n : Fin r, thresholdRejectProb N ^ n.val) := by
    calc
      (∑ n : Fin r,
          ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
          = ∑ n : Fin r,
              (thresholdRejectProb N ^ n.val * (1 / (2 ^ thresholdWidth N : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hmass n
      _ = (1 / (2 ^ thresholdWidth N : ℝ)) * (∑ n : Fin r, thresholdRejectProb N ^ n.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  calc
    (∑ n : Fin r,
        ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
        * (N : ℝ)
        = (1 / (2 ^ thresholdWidth N : ℝ))
            * (∑ n : Fin r, thresholdRejectProb N ^ n.val) * (N : ℝ) := by rw [hsum]
    _ = (1 - thresholdRejectProb N) * (∑ n : Fin r, thresholdRejectProb N ^ n.val) := by
      rw [hone]
      ring
    _ = 1 - thresholdRejectProb N ^ r := hgeom

/-- For positive `N`, each accepted-index marginal equals the total acceptance probability times
that index's mass under the uniform minimum-search initialization law. -/
theorem thresholdRunLaw_accepted_matches_frozen_initial (N : ℕ) (hN : 0 < N)
    (r : ℕ) (i : Fin N) :
    (∑ n : Fin r,
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
      = (1 - thresholdRejectProb N ^ r) * (iterationPMF N hN i).toReal := by
  have hmarg := thresholdRunLaw_accepted_marginal N hN r i
  have hunif := threshold_matches_frozen_initial N hN i
  rw [hunif]
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmain : (1 - thresholdRejectProb N ^ r) * (1 / (N : ℝ))
      = (1 - thresholdRejectProb N ^ r) / (N : ℝ) := by ring
  rw [hmain]
  exact (eq_div_iff hNne).2 hmarg

/-- For positive `N`, the total real mass of all accepted outcomes is `1 - thresholdRejectProb N
^ r`. -/
theorem thresholdRunLaw_accepted_total (N : ℕ) (hN : 0 < N) (r : ℕ) :
    (∑ i : Fin N, ∑ n : Fin r,
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
      = 1 - thresholdRejectProb N ^ r := by
  calc
    (∑ i : Fin N, ∑ n : Fin r,
        ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
        = ∑ i : Fin N,
            ((1 - thresholdRejectProb N ^ r) * (iterationPMF N hN i).toReal) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [thresholdRunLaw_accepted_matches_frozen_initial N hN r i]
    _ = (1 - thresholdRejectProb N ^ r) * (∑ i : Fin N, (iterationPMF N hN i).toReal) := by
          rw [Finset.mul_sum]
    _ = 1 - thresholdRejectProb N ^ r := by
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hsum : (∑ i : Fin N, (iterationPMF N hN i).toReal) = 1 := by
        calc
          (∑ i : Fin N, (iterationPMF N hN i).toReal) = ∑ _i : Fin N, (1 / (N : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [threshold_matches_frozen_initial N hN i]
          _ = (1 / (N : ℝ)) * (N : ℝ) := by
            rw [Finset.sum_const]
            simp [Fintype.card_fin, nsmul_eq_mul, mul_comm]
          _ = 1 := by field_simp
      rw [hsum]
      ring

/-- For positive `N`, the sum of all accepted-outcome real masses and the failed-outcome real
mass is one. -/
theorem thresholdRunLaw_total_mass (N : ℕ) (hN : 0 < N) (r : ℕ) :
    (∑ i : Fin N, ∑ n : Fin r,
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
      + ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal = 1 := by
  have hacc := thresholdRunLaw_accepted_total N hN r
  have hfail := thresholdRunLaw_failed_mass N hN r
  rw [hacc, hfail]
  ring
end Qatlib.Concepts.AmplitudeSearch.Amplification
