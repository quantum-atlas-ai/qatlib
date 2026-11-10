/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AmplitudeSearch.Amplification.NativeMinimumConstructionDefs
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

noncomputable def realMass {α : Type*} [Fintype α] (p : PMF α) (a : α) : ℝ := (p a).toReal

theorem fairBitLaw_true : (fairBitLaw true).toReal = 1 / 2 := by
  rw [fairBitLaw, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]
  simp [Fintype.card_bool]

theorem fairBitLaw_false : (fairBitLaw false).toReal = 1 / 2 := by
  rw [fairBitLaw, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]
  simp [Fintype.card_bool]

theorem fairWordLaw_toReal (k : ℕ) (w : Fin (2 ^ k)) :
    (fairWordLaw k w).toReal = 1 / (2 ^ k : ℝ) := by
  rw [fairWordLaw, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]
  simp [Fintype.card_fin, one_div]

theorem thresholdWidth_eq (N : ℕ) : thresholdWidth N = Nat.ceil (binaryLog N) := rfl

theorem thresholdWords_eq (N : ℕ) : thresholdWords N = 2 ^ thresholdWidth N := rfl

theorem thresholdWords_pos (N : ℕ) : 0 < thresholdWords N := by
  unfold thresholdWords
  positivity

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

def acceptedWord (N : ℕ) (_hN : 0 < N) :
    {w : Fin (thresholdWords N) // w.val < N} → Fin N := fun w => ⟨w.val, w.property⟩

def rejectedWord (N : ℕ) (_hN : 0 < N) :
    {w : Fin (thresholdWords N) // N ≤ w.val} → Fin (thresholdWords N - N) :=
  fun w => ⟨w.val - N, by omega⟩

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

theorem accepted_word_mass (N : ℕ) (w : {w : Fin (thresholdWords N) // w.val < N}) :
    (fairWordLaw (thresholdWidth N) w.1).toReal = 1 / (2 ^ thresholdWidth N : ℝ) :=
  fairWordLaw_toReal _ _

theorem rejected_word_mass (N : ℕ) (w : {w : Fin (thresholdWords N) // N ≤ w.val}) :
    (fairWordLaw (thresholdWidth N) w.1).toReal = 1 / (2 ^ thresholdWidth N : ℝ) :=
  fairWordLaw_toReal _ _

theorem threshold_matches_frozen_initial (N : ℕ) (hN : 0 < N) (i : Fin N) :
    (iterationPMF N hN i).toReal = 1 / (N : ℝ) := by
  simp [iterationPMF, PMF.uniformOfFintype'_apply, ENNReal.toReal_inv _]

theorem reject_prob_lt_one (N : ℕ) (hN : 0 < N) :
    ((thresholdWords N - N : ℕ) : ℝ) / (thresholdWords N : ℝ) < 1 := by
  have hNM : N ≤ thresholdWords N := thresholdWords_ge N hN
  have hlt : (thresholdWords N - N : ℕ) < thresholdWords N := by omega
  have hpos : (0 : ℝ) < thresholdWords N := Nat.cast_pos.mpr (thresholdWords_pos N)
  rw [div_lt_one hpos]
  exact_mod_cast hlt

theorem ennreal_ne_top_of_le_one {x : ℝ≥0∞} (h : x ≤ 1) : x ≠ ∞ := by
  intro hx
  subst hx
  exact absurd (show (∞ : ℝ≥0∞) ≤ 1 from h) (not_le_of_gt ENNReal.one_lt_top)

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

theorem sum_indicator_filter (α : Type*) [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℝ) :
    (∑ a ∈ (Finset.univ : Finset α), (if p a then c else 0))
      = (Finset.univ.filter p).card * c := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]

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

theorem producerWordLaw_map_mass (N : ℕ) {β : Type*} (f : Fin (thresholdWords N) → β) (b : β) :
    ((producerWordLaw N).map f b).toReal
      = (Finset.univ.filter (fun a : Fin (thresholdWords N) => b = f a)).card
          * (1 / (thresholdWords N : ℝ)) := by
  letI : Nonempty (Fin (thresholdWords N)) :=
    ⟨⟨0, by unfold thresholdWords; positivity⟩⟩
  have h := uniform_map_mass_real f b
  unfold producerWordLaw
  rwa [show Fintype.card (Fin (thresholdWords N)) = thresholdWords N from Fintype.card_fin _] at h

theorem acceptThreshold_none_iff (N : ℕ) (w : Fin (thresholdWords N)) :
    none = acceptThreshold N w ↔ N ≤ w.val := by
  by_cases hlt : w.val < N
  · have h : acceptThreshold N w = some ⟨w.val, hlt⟩ := by simp [acceptThreshold, hlt]
    simp [h, Nat.not_le.mpr hlt]
  · have h : acceptThreshold N w = none := by simp [acceptThreshold, hlt]
    simp [h, Nat.not_lt.mp hlt]

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

noncomputable def runContinuation {N r : ℕ} (o : Option (Fin N)) : PMF (ThresholdOutcome N (r + 1)) :=
  match o with
  | some i => PMF.pure (.accepted i ⟨0, by omega⟩)
  | none => (thresholdRunLaw N r).map (bumpOutcome)

theorem thresholdRunLaw_eq_bind (N r : ℕ) :
    thresholdRunLaw N (r + 1) = (thresholdRoundLaw N).bind (runContinuation) := rfl

theorem bumpOutcome_failed_preimage (N r : ℕ) (a : ThresholdOutcome N r)
    (h : (ThresholdOutcome.failed : ThresholdOutcome N (r + 1)) = bumpOutcome a) :
    a = (ThresholdOutcome.failed : ThresholdOutcome N r) := by
  cases a with
  | failed => rfl
  | accepted j m => simp [bumpOutcome] at h

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

theorem thresholdRunLaw_accepted_mass (N : ℕ) (hN : 0 < N) (r : ℕ) (i : Fin N) (n : Fin r) :
    ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal
      = thresholdRejectProb N ^ n.val * (1 / (2 ^ thresholdWidth N : ℝ)) :=
  (thresholdRunLaw_mass N hN r).1 i n

theorem thresholdRunLaw_failed_mass (N : ℕ) (hN : 0 < N) (r : ℕ) :
    ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal
      = thresholdRejectProb N ^ r :=
  (thresholdRunLaw_mass N hN r).2

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

theorem thresholdRunLaw_total_mass (N : ℕ) (hN : 0 < N) (r : ℕ) :
    (∑ i : Fin N, ∑ n : Fin r,
      ((thresholdRunLaw N r) (ThresholdOutcome.accepted i n : ThresholdOutcome N r)).toReal)
      + ((thresholdRunLaw N r) (ThresholdOutcome.failed : ThresholdOutcome N r)).toReal = 1 := by
  have hacc := thresholdRunLaw_accepted_total N hN r
  have hfail := thresholdRunLaw_failed_mass N hN r
  rw [hacc, hfail]
  ring
end Qatlib.Concepts.AmplitudeSearch.Amplification
