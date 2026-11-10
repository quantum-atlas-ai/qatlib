/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryHitting
set_option warningAsError false


open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open scoped Classical

variable {n : ℕ}

noncomputable def booleanQuotientRep (H : AddSubgroup (BooleanVec n))
    (q : BooleanVec n ⧸ H) : BooleanVec n :=
  Classical.choose (QuotientAddGroup.mk'_surjective H q)

@[simp] theorem booleanQuotientRep_mk (H : AddSubgroup (BooleanVec n))
    (q : BooleanVec n ⧸ H) :
    QuotientAddGroup.mk' H (booleanQuotientRep H q) = q :=
  Classical.choose_spec (QuotientAddGroup.mk'_surjective H q)

theorem booleanQuotientRep_not_mem (H : AddSubgroup (BooleanVec n))
    (q : BooleanVec n ⧸ H) (hq : q ≠ 0) : booleanQuotientRep H q ∉ H := by
  intro hmem
  apply hq
  rw [← booleanQuotientRep_mk H q]
  exact (QuotientAddGroup.eq_zero_iff (booleanQuotientRep H q)).2 hmem

theorem booleanDot_eq_of_quotient_eq (H : AddSubgroup (BooleanVec n))
    {x y a : BooleanVec n} (ha : a ∈ booleanOrthogonal H)
    (hxy : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y) :
    booleanDot x a = booleanDot y a := by
  let φ : (BooleanVec n ⧸ H) →+ ZMod 2 :=
    QuotientAddGroup.lift H (booleanDotHom a) (by
      intro z hz
      exact (mem_booleanOrthogonal H a).1 ha ⟨z, hz⟩)
  have h := congrArg φ hxy
  change booleanDot a x = booleanDot a y at h
  simpa only [booleanDot, mul_comm] using h

theorem boolean_quotient_eq_iff_pairings_eq (H : AddSubgroup (BooleanVec n))
    (x y : BooleanVec n) :
    QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y ↔
      ∀ a : booleanOrthogonal H, booleanDot x a = booleanDot y a := by
  constructor
  · intro hxy a
    exact booleanDot_eq_of_quotient_eq H a.property hxy
  · intro hpair
    have hd : x - y ∈ booleanOrthogonal (booleanOrthogonal H) := by
      rw [mem_booleanOrthogonal]
      intro a
      have hsub : booleanDot (x - y) a = booleanDot x a - booleanDot y a := by
        simp only [booleanDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [hsub, hpair a, sub_self]
    rw [booleanOrthogonal_booleanOrthogonal_eq] at hd
    exact (QuotientAddGroup.eq_iff_sub_mem).2 hd

noncomputable def booleanQuotientMissEvent {m : ℕ}
    (H : AddSubgroup (BooleanVec n)) (q : BooleanVec n ⧸ H)
    (xs : Fin m → AddChar (BooleanVec n) ℂ) : Prop :=
  ∀ i, booleanDot (booleanQuotientRep H q) (booleanDecodedSamples xs i) = 0

theorem booleanQuotientMissEvent_iff {m : ℕ}
    (H : AddSubgroup (BooleanVec n)) (q : BooleanVec n ⧸ H)
    (x : BooleanVec n) (hx : QuotientAddGroup.mk' H x = q)
    (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hs : ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) :
    booleanQuotientMissEvent H q xs ↔
      ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0 := by
  have hrep : QuotientAddGroup.mk' H (booleanQuotientRep H q) =
      QuotientAddGroup.mk' H x := (booleanQuotientRep_mk H q).trans hx.symm
  unfold booleanQuotientMissEvent
  apply forall_congr'
  intro i
  rw [booleanDot_eq_of_quotient_eq H (hs i) hrep]

theorem boolean_recovery_failure_iff_quotient_miss {m : ℕ}
    (H : AddSubgroup (BooleanVec n))
    (xs : Fin m → AddChar (BooleanVec n) ℂ)
    (hs : ∀ i, booleanDecodedSamples xs i ∈ booleanOrthogonal H) :
    booleanSampleCandidate (booleanDecodedSamples xs) ≠ H ↔
      ∃ q : {q : BooleanVec n ⧸ H // q ≠ 0}, booleanQuotientMissEvent H q.1 xs := by
  have hsep : booleanSampleCandidate (booleanDecodedSamples xs) ≠ H ↔
      ∃ x : BooleanVec n, x ∉ H ∧
        ∀ i, booleanDot x (booleanDecodedSamples xs i) = 0 := by
    simpa only [not_forall, Classical.not_imp, not_exists, not_not, exists_prop] using
      (not_congr (booleanSampleCandidate_eq_iff_hits_outside H
        (booleanDecodedSamples xs) hs))
  rw [hsep]
  constructor
  · rintro ⟨x, hx, hmiss⟩
    have hq : QuotientAddGroup.mk' H x ≠ 0 := by
      intro hzero
      exact hx ((QuotientAddGroup.eq_zero_iff x).1 hzero)
    refine ⟨⟨QuotientAddGroup.mk' H x, hq⟩, ?_⟩
    exact (booleanQuotientMissEvent_iff H _ x rfl xs hs).2 hmiss
  · rintro ⟨q, hmiss⟩
    exact ⟨booleanQuotientRep H q.1, booleanQuotientRep_not_mem H q.1 q.2, hmiss⟩

theorem card_booleanQuotient_eq_annihilator (H : AddSubgroup (BooleanVec n)) :
    Fintype.card (BooleanVec n ⧸ H) = Fintype.card (characterAnnihilator H) := by
  have hQ : Fintype.card H * Fintype.card (BooleanVec n ⧸ H) =
      Fintype.card (BooleanVec n) := by
    simpa only [AddSubgroup.index, Nat.card_eq_fintype_card] using H.card_mul_index
  apply Nat.mul_right_cancel (Fintype.card_pos (α := H))
  calc
    Fintype.card (BooleanVec n ⧸ H) * Fintype.card H =
        Fintype.card (BooleanVec n) := by rw [Nat.mul_comm]; exact hQ
    _ = Fintype.card (characterAnnihilator H) * Fintype.card H :=
      (card_characterAnnihilator H).symm

theorem card_booleanNonzeroQuotient (H : AddSubgroup (BooleanVec n)) :
    (Fintype.card {q : BooleanVec n ⧸ H // q ≠ 0} : ℝ) =
      (Fintype.card (BooleanVec n ⧸ H) : ℝ) - 1 := by
  have hpos : 1 ≤ Fintype.card (BooleanVec n ⧸ H) := Fintype.card_pos
  rw [Fintype.card_subtype_compl (fun q : BooleanVec n ⧸ H => q = 0),
    Fintype.card_subtype_eq, Nat.cast_sub hpos, Nat.cast_one]

variable {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem hiddenSubgroupSampleDist_boolean_failure_eq_quotient_union
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) =
      (hiddenSubgroupSampleDist f e).probEvent
        (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          ∃ q : {q : BooleanVec n ⧸ H // q ≠ 0}, booleanQuotientMissEvent H q.1 xs) := by
  apply hiddenSubgroupSampleDist_boolean_event_congr f H hf e m
  intro xs hs
  exact boolean_recovery_failure_iff_quotient_miss H xs hs

theorem hiddenSubgroupSampleDist_boolean_quotient_miss
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ)
    (q : BooleanVec n ⧸ H) (hq : q ≠ 0) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent (booleanQuotientMissEvent (m := m) H q) =
      (1 / 2 : ℝ) ^ m := by
  have heq := hiddenSubgroupSampleDist_boolean_event_congr f H hf e m
    (booleanQuotientMissEvent H q)
    (fun xs => ∀ i, booleanDot (booleanQuotientRep H q) (booleanDecodedSamples xs i) = 0)
    (fun _ _ => Iff.rfl)
  exact heq.trans (hiddenSubgroupSampleDist_boolean_halfspace_event f H hf e
    (booleanQuotientRep H q) (booleanQuotientRep_not_mem H q hq) m)

theorem hiddenSubgroupSampleDist_boolean_failure_le_nonzero_quotient
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) ≤
      (Fintype.card {q : BooleanVec n ⧸ H // q ≠ 0} : ℝ) * (1 / 2 : ℝ) ^ m := by
  classical
  let I := {q : BooleanVec n ⧸ H // q ≠ 0}
  let c := Fintype.equivFin I
  let p := hiddenSubgroupSampleDist f e
  let E : Fin (Fintype.card I) → (Fin m → AddChar (BooleanVec n) ℂ) → Prop :=
    fun j xs => booleanQuotientMissEvent H (c.symm j).1 xs
  have hpred : (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
      ∃ q : I, booleanQuotientMissEvent H q.1 xs) = (fun xs => ∃ j, E j xs) := by
    funext xs
    apply propext
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨c q, by simpa only [E, c.symm_apply_apply] using hq⟩
    · rintro ⟨j, hj⟩
      exact ⟨c.symm j, hj⟩
  have heach (j : Fin (Fintype.card I)) : p.probEvent (E j) = (1 / 2 : ℝ) ^ m :=
    hiddenSubgroupSampleDist_boolean_quotient_miss f H hf e
      (c.symm j).1 (c.symm j).2 m
  calc
    p.probEvent (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) =
        p.probEvent (fun xs => ∃ j, E j xs) := by
      rw [hiddenSubgroupSampleDist_boolean_failure_eq_quotient_union f H hf e m]
      apply hiddenSubgroupSampleDist_boolean_event_congr f H hf e m
      intro xs _
      rw [congrFun hpred xs]
    _ ≤ ∑ j : Fin (Fintype.card I), p.probEvent (E j) := FinDist.union_bound p E
    _ = (Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ m := by
      simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem hiddenSubgroupSampleDist_boolean_failure_le_quotient
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (hiddenSubgroupSampleDist f e).probEvent
      (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H) ≤
      ((Fintype.card (BooleanVec n ⧸ H) : ℝ) - 1) / (2 : ℝ) ^ m := by
  have h := hiddenSubgroupSampleDist_boolean_failure_le_nonzero_quotient f H hf e m
  rwa [card_booleanNonzeroQuotient, div_pow, one_pow, mul_one_div] at h

theorem hiddenSubgroupFreshSamples_boolean_failure_le_quotient
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H),
      hiddenSubgroupFreshSamples f e m xs) ≤
      ENNReal.ofReal (((Fintype.card (BooleanVec n ⧸ H) : ℝ) - 1) / (2 : ℝ) ^ m) := by
  rw [hiddenSubgroupFreshSamples_event]
  exact ENNReal.ofReal_le_ofReal
    (hiddenSubgroupSampleDist_boolean_failure_le_quotient f H hf e m)

theorem hiddenSubgroupFreshSamples_boolean_failure_le_annihilator
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
        booleanSampleCandidate (booleanDecodedSamples xs) ≠ H),
      hiddenSubgroupFreshSamples f e m xs) ≤
      ENNReal.ofReal (((Fintype.card (characterAnnihilator H) : ℝ) - 1) / (2 : ℝ) ^ m) := by
  simpa only [card_booleanQuotient_eq_annihilator] using
    hiddenSubgroupFreshSamples_boolean_failure_le_quotient f H hf e m

theorem hiddenSubgroupSampleDist_boolean_success_ge_quotient
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    1 - ((Fintype.card (BooleanVec n ⧸ H) : ℝ) - 1) / (2 : ℝ) ^ m ≤
      (hiddenSubgroupSampleDist f e).probEvent
        (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H) := by
  classical
  let p := hiddenSubgroupSampleDist f e
  let E : (Fin m → AddChar (BooleanVec n) ℂ) → Prop := fun xs =>
    booleanSampleCandidate (booleanDecodedSamples xs) = H
  have hsplit : p.probEvent (fun xs => ¬ E xs) + p.probEvent E = 1 := by
    simp only [FinDist.probEvent, Finset.sum_filter, ← Finset.sum_add_distrib]
    calc
      _ = ∑ xs : Fin m → AddChar (BooleanVec n) ℂ, p.probOf xs := by
        apply Finset.sum_congr rfl
        intro xs _
        by_cases hE : E xs <;> simp [hE]
      _ = 1 := FinDist.sum_probOf p m
  have hfail := hiddenSubgroupSampleDist_boolean_failure_le_quotient f H hf e m
  change p.probEvent (fun xs => ¬ E xs) ≤ _ at hfail
  change _ ≤ p.probEvent E
  linarith

theorem hiddenSubgroupFreshSamples_boolean_success_ge_quotient
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n))
    (hf : HidesSubgroup f H) (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ) :
    ENNReal.ofReal (1 - ((Fintype.card (BooleanVec n ⧸ H) : ℝ) - 1) / (2 : ℝ) ^ m) ≤
      ∑ xs ∈ Finset.univ.filter (fun xs : Fin m → AddChar (BooleanVec n) ℂ =>
          booleanSampleCandidate (booleanDecodedSamples xs) = H),
        hiddenSubgroupFreshSamples f e m xs := by
  rw [hiddenSubgroupFreshSamples_event]
  exact ENNReal.ofReal_le_ofReal
    (hiddenSubgroupSampleDist_boolean_success_ge_quotient f H hf e m)

end Qatlib.Concepts.HspRecovery.ReductionCore
