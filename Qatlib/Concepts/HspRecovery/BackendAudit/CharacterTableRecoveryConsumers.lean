/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.BackendAudit.CharacterTableRecoveryProbability
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree

open Qatlib.Concepts.HspRecovery.Distinguisher

namespace Qatlib.Concepts.HspRecovery.BackendAudit

open Matrix
open scoped Classical

section Ledger

variable {G R : Type}
  [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

theorem tableGroupRecordDist_probEvent_relabel (f : G → R) (e : G ≃ AddChar G ℂ)
    {m : ℕ} (E : (Fin m → G) → Prop) [DecidablePred E] :
    (tableGroupRecordDist f e).probEvent E =
      (hiddenSubgroupSampleDist f e).probEvent
        (fun χs : Fin m → AddChar G ℂ => E (fun i => e.symm (χs i))) := by
  classical
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf
  refine Finset.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin m)) e) ?_ ?_
  · intro xs
    show xs ∈ Finset.univ.filter E ↔
        (fun k : Fin m => e (xs k)) ∈ Finset.univ.filter
          (fun χs : Fin m → AddChar G ℂ => E (fun i => e.symm (χs i)))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hf : (fun i : Fin m => e.symm (e (xs i))) = xs :=
      funext fun i => e.symm_apply_apply (xs i)
    constructor
    · intro hEx
      rw [hf]
      exact hEx
    · intro hE
      rw [← hf]
      exact hE
  · intro xs _
    rfl

noncomputable def tableDecodedRun (tab : G → G → Bool) (f : G → R) (e : G ≃ AddChar G ℂ)
    (A : Matrix G G ℂ) (m : ℕ) : PMF (Finset G) × (ℕ × ℕ × ℕ) :=
  ((hiddenSubgroupFreshSamples f e m).map fun χs : Fin m → AddChar G ℂ =>
      (tableKernelDecode tab (List.ofFn fun i => e.symm (χs i))).1,
    (∑ _i : Fin m, QueryCount (tableSamplingCircuit (R := R) e A),
     ∑ _i : Fin m, GateCount (tableSamplingCircuit (R := R) e A),
     ∑ _i : Fin m, Fintype.card G))

theorem tableDecodedRun_ledger (tab : G → G → Bool) (f : G → R) (e : G ≃ AddChar G ℂ)
    (A : Matrix G G ℂ) (m : ℕ) :
    (tableDecodedRun tab f e A m).2 = (m, 2 * m, m * Fintype.card G) := by
  simp [tableDecodedRun, tableSamplingCircuit, hiddenSubgroupSamplingCircuit,
    QueryCount, GateCount, mul_comm]

theorem tableDecodedRun_reads (tab : G → G → Bool) (e : G ≃ AddChar G ℂ)
    (m : ℕ) (χs : Fin m → AddChar G ℂ) :
    (tableKernelDecode tab (List.ofFn fun i => e.symm (χs i))).2
      = Fintype.card G * m := by
  rw [tableKernelDecode_reads, List.length_ofFn]

theorem tableFreshRecord_success_ge (tab : G → G → Bool) (f : G → R) (e : G ≃ AddChar G ℂ)
    (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (htab : ∀ a y, tab a y = true ↔ e a y = 1) (m : ℕ) :
    ENNReal.ofReal (1 - (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹)^m) ≤
      ∑ χs ∈ Finset.univ.filter (fun χs : Fin m → AddChar G ℂ =>
          ((tableKernelDecode tab (List.ofFn fun i => e.symm (χs i))).1 : Set G) = (H : Set G)),
        hiddenSubgroupFreshSamples f e m χs := by
  have hgoal : (hiddenSubgroupSampleDist f e).probEvent
      (fun χs : Fin m → AddChar G ℂ =>
        ((tableKernelDecode tab (List.ofFn fun i => e.symm (χs i))).1 : Set G) = (H : Set G)) =
      (tableGroupRecordDist f e).probEvent (fun xs : Fin m → G =>
        ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G)) :=
    (tableGroupRecordDist_probEvent_relabel f e (fun xs : Fin m → G =>
      ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G))).symm
  rw [hiddenSubgroupFreshSamples_event, hgoal]
  exact ENNReal.ofReal_le_ofReal
    (character_table_actual_subgroup_recovery_probability f e tab H m hf htab)

theorem tableFreshRecord_budget_ge (tab : G → G → Bool) (f : G → R) (e : G ≃ AddChar G ℂ)
    (A : Matrix G G ℂ) (H : AddSubgroup G) (hf : HidesSubgroup f H)
    (htab : ∀ a y, tab a y = true ↔ e a y = 1) (k : ℕ) :
    ENNReal.ofReal (1 - ((2 : ℝ)⁻¹)^k) ≤
      ∑ χs ∈ Finset.univ.filter (fun χs : Fin (tableRecoverySamples (Fintype.card G) k) →
          AddChar G ℂ =>
          ((tableKernelDecode tab (List.ofFn fun i => e.symm (χs i))).1 : Set G) = (H : Set G)),
        hiddenSubgroupFreshSamples f e (tableRecoverySamples (Fintype.card G) k) χs := by
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have h6 := (character_table_computed_sample_budget (Fintype.card G) k).2 hpos
  refine le_trans ?_ (tableFreshRecord_success_ge tab f e H hf htab
    (tableRecoverySamples (Fintype.card G) k))
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem tablePreparedRecoveryRun_consumer (tab : G → G → Bool) (f : G → R)
    (e : G ≃ AddChar G ℂ) (A : Matrix G G ℂ) (H : AddSubgroup G) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup G ℂ) (hprep : A *ᵥ Qatlib.Foundations.PureStateMath.Ket (0 : G) = Uniform G)
    (hf : HidesSubgroup f H) (htab : ∀ a y, tab a y = true ↔ e a y = 1) :
    let m := tableRecoverySamples (Fintype.card G) k
    IsUnitaryCircuit (tableSamplingCircuit (R := R) e A) ∧
      Run (AddOracle f) (tableSamplingCircuit (R := R) e A)
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (0 : G)) (Qatlib.Foundations.PureStateMath.Ket (0 : R))) =
        Run (AddOracle f) (hiddenSubgroupSamplingCircuit (R := R) e)
          (TensorState (Uniform G) (Qatlib.Foundations.PureStateMath.Ket (0 : R))) ∧
      (tableDecodedRun tab f e A m).2 = (m, 2 * m, m * Fintype.card G) ∧
      ENNReal.ofReal (1 - ((2 : ℝ)⁻¹)^k) ≤
        ∑ χs ∈ Finset.univ.filter (fun χs : Fin m → AddChar G ℂ =>
            ((tableKernelDecode tab (List.ofFn fun i => e.symm (χs i))).1 : Set G) =
              (H : Set G)), hiddenSubgroupFreshSamples f e m χs := by
  have h7 := character_table_actual_preparation_and_resource_bridge e A f hA hprep
  exact ⟨h7.1, h7.2.2.2, tableDecodedRun_ledger tab f e A _,
    tableFreshRecord_budget_ge tab f e A H hf htab k⟩

end Ledger

section Four

def fourTable (a x : ZMod 4) : Bool := decide (a * x = 0)

noncomputable def fourCharacterLabeling : ZMod 4 ≃ AddChar (ZMod 4) ℂ :=
  (AddChar.zmodAddEquiv (n := 4)).toEquiv

theorem fourCharacterLabeling_apply (a x : ZMod 4) :
    fourCharacterLabeling a x = primRoot 4 ^ (((a * x).val : ℤ)) := by
  show (AddChar.zmodAddEquiv (n := 4)) a x = _
  rw [zmodAddEquiv_apply_stdAddChar, stdAddChar_eq_primRoot_zpow]

theorem zmodAddEquiv_apply_eq_one_iff {N : ℕ} [NeZero N] (a x : ZMod N) :
    (AddChar.zmodAddEquiv (n := N)).toEquiv a x = 1 ↔ a * x = 0 := by
  constructor
  · intro h
    have h1 : (AddChar.zmodAddEquiv (n := N)) a x = 1 := h
    rw [zmodAddEquiv_apply_stdAddChar a x] at h1
    refine ZMod.injective_stdAddChar ?_
    simpa only [AddChar.map_zero_eq_one] using h1
  · intro h
    have h1 : (AddChar.zmodAddEquiv (n := N)).toEquiv a x = ZMod.stdAddChar (a * x) :=
      zmodAddEquiv_apply_stdAddChar a x
    rw [h1, h, AddChar.map_zero_eq_one]

theorem fourTable_correct (a x : ZMod 4) :
    fourTable a x = true ↔ fourCharacterLabeling a x = 1 := by
  rw [fourTable, decide_eq_true_eq]
  exact (zmodAddEquiv_apply_eq_one_iff a x).symm

private theorem four_val_eq (k : ℕ) (hk : k < 4) (x : ZMod 4) (h : x.val = k) :
    x = ((k : ℕ) : ZMod 4) := by
  apply ZMod.val_injective
  rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

private theorem four_val_cases (x : ZMod 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have hlt : x.val < 4 := ZMod.val_lt x
  rcases (show x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 by omega) with h | h | h | h
  · exact Or.inl (four_val_eq 0 (by norm_num) x h)
  · exact Or.inr (Or.inl (four_val_eq 1 (by norm_num) x h))
  · exact Or.inr (Or.inr (Or.inl (four_val_eq 2 (by norm_num) x h)))
  · exact Or.inr (Or.inr (Or.inr (four_val_eq 3 (by norm_num) x h)))

private theorem four_even_cases (x : ZMod 4) (hx : x.val % 2 = 0) : x = 0 ∨ x = 2 := by
  rcases four_val_cases x with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hx (by decide)
  · exact Or.inr rfl
  · exact absurd hx (by decide)

private theorem four_even_mul (a x : ZMod 4) (ha : a.val % 2 = 0) (hx : x.val % 2 = 0) :
    (a * x).val = 0 := by
  rcases four_even_cases a ha with rfl | rfl <;>
    rcases four_even_cases x hx with rfl | rfl <;> decide

def fourEvenSubgroup : AddSubgroup (ZMod 4) where
  carrier := {x | x.val % 2 = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [ZMod.val_add]
    omega
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [ZMod.val_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [ZMod.neg_val']
    have hlt : a.val < 4 := ZMod.val_lt a
    omega

theorem mem_fourEvenSubgroup (x : ZMod 4) : x ∈ fourEvenSubgroup ↔ x.val % 2 = 0 := Iff.rfl

theorem card_fourEvenSubgroup : Fintype.card ↥fourEvenSubgroup = 2 := by
  have hfil : (Finset.univ.filter fun x : ZMod 4 => x.val % 2 = 0).card = 2 := by decide
  have heq : Fintype.card ↥fourEvenSubgroup
      = (Finset.univ.filter fun x : ZMod 4 => x.val % 2 = 0).card := by
    refine (Fintype.card_congr ?_).trans (Fintype.card_subtype
      (fun x : ZMod 4 => x.val % 2 = 0))
    exact
      { toFun := fun hx : {x : ZMod 4 // x ∈ fourEvenSubgroup} => ⟨(hx : ZMod 4), hx.property⟩
        invFun := fun hx : {x : ZMod 4 // x.val % 2 = 0} => ⟨(hx : ZMod 4), hx.property⟩
        left_inv := fun a => Subtype.ext rfl
        right_inv := fun a => Subtype.ext rfl }
  exact heq.trans hfil

theorem card_fourEvenAnnihilator :
    Fintype.card (characterAnnihilator fourEvenSubgroup) = 2 := by
  have h := card_characterAnnihilator fourEvenSubgroup
  rw [card_fourEvenSubgroup] at h
  have hG : Fintype.card (ZMod 4) = 4 := by simp
  omega

theorem hidesSubgroup_fourParity :
    HidesSubgroup (fun x : ZMod 4 => (x.val : ZMod 2)) fourEvenSubgroup := by
  intro x y
  constructor
  · intro h
    have hv : ((x.val : ℕ) : ZMod 2).val = ((y.val : ℕ) : ZMod 2).val := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast] at hv
    show (x - y).val % 2 = 0
    rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val']
    have hx : x.val < 4 := ZMod.val_lt x
    have hy : y.val < 4 := ZMod.val_lt y
    omega
  · intro h
    have h0 : (x - y).val % 2 = 0 := h
    rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val'] at h0
    have hx : x.val < 4 := ZMod.val_lt x
    have hy : y.val < 4 := ZMod.val_lt y
    have h2 : x.val % 2 = y.val % 2 := by omega
    show ((x.val : ℕ) : ZMod 2) = ((y.val : ℕ) : ZMod 2)
    apply ZMod.val_injective (n := 2)
    rw [ZMod.val_natCast, ZMod.val_natCast]
    exact h2

theorem fourCharacterLabeling_mem_ann_iff (a : ZMod 4) :
    fourCharacterLabeling a ∈ characterAnnihilator fourEvenSubgroup ↔ a.val % 2 = 0 := by
  constructor
  · intro h
    have h2 : fourCharacterLabeling a (2 : ZMod 4) = 1 :=
      ((mem_characterAnnihilator fourEvenSubgroup (fourCharacterLabeling a)).1 h)
        ⟨2, (mem_fourEvenSubgroup 2).2 (by decide)⟩
    have hmul : a * (2 : ZMod 4) = 0 :=
      (zmodAddEquiv_apply_eq_one_iff a 2).1 h2
    have hval : a.val * (2 : ZMod 4).val % 4 = 0 := by
      rw [← ZMod.val_mul, hmul, ZMod.val_zero]
    have h2val : (2 : ZMod 4).val = 2 := by decide
    rw [h2val] at hval
    have hva : a.val < 4 := ZMod.val_lt a
    omega
  · intro h
    rw [mem_characterAnnihilator]
    intro hsub
    rw [fourCharacterLabeling_apply, four_even_mul a (hsub : ZMod 4) h hsub.property,
      Nat.cast_zero, zpow_zero]

theorem four_record_dist_prob (a : ZMod 4) :
    (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).prob a
      = if a.val % 2 = 0 then (1 : ℝ) / 2 else 0 := by
  show (hiddenSubgroupSampleDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).prob
      (fourCharacterLabeling a) = _
  rw [hiddenSubgroupSampleDist_prob _ fourEvenSubgroup hidesSubgroup_fourParity
      fourCharacterLabeling (fourCharacterLabeling a),
    fourCharacterLabeling_mem_ann_iff a, card_fourEvenAnnihilator]
  by_cases h : a.val % 2 = 0 <;> simp [h]

theorem four_decode_even_labels {m : ℕ} (xs : Fin m → ZMod 4)
    (hex : ∀ i, (xs i).val % 2 = 0) (htwo : ∃ i, xs i = 2) :
    ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4))
      = (fourEvenSubgroup : Set (ZMod 4)) := by
  obtain ⟨i₀, hi₀⟩ := htwo
  ext x
  simp only [SetLike.mem_coe, mem_fourEvenSubgroup,
    mem_tableKernelDecode, fourTable, decide_eq_true_eq]
  constructor
  · intro hall
    have hmem : xs i₀ ∈ List.ofFn xs := by
      rw [List.mem_ofFn]
      exact ⟨i₀, rfl⟩
    have h2x : (2 : ZMod 4) * x = 0 := by
      have hzi := hall _ hmem
      rw [hi₀] at hzi
      exact hzi
    have hval : (2 : ZMod 4).val * x.val % 4 = 0 := by
      rw [← ZMod.val_mul, h2x, ZMod.val_zero]
    have h2val : (2 : ZMod 4).val = 2 := by decide
    rw [h2val] at hval
    have hx : x.val < 4 := ZMod.val_lt x
    omega
  · intro heven a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    rcases four_even_cases (xs i) (hex i) with h | h
    · rw [h, zero_mul]
    · rw [h]
      rcases four_even_cases x heven with rfl | rfl
      · rw [mul_zero]
      · decide

theorem four_decode_univ_of_zero {m : ℕ} (xs : Fin m → ZMod 4) (h0 : ∀ i, xs i = 0) :
    ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, SetLike.mem_coe, mem_tableKernelDecode,
    fourTable, decide_eq_true_eq]
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  rw [h0 i, zero_mul]

theorem four_univ_ne_even :
    (Set.univ : Set (ZMod 4)) ≠ (fourEvenSubgroup : Set (ZMod 4)) := by
  intro h
  have h1 : (1 : ZMod 4) ∈ (fourEvenSubgroup : Set (ZMod 4)) := by
    rw [← h]
    trivial
  exact absurd ((mem_fourEvenSubgroup 1).1 (SetLike.mem_coe.1 h1)) (by decide)

end Four

end Qatlib.Concepts.HspRecovery.BackendAudit

namespace Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open Matrix
open scoped Classical

theorem character_table_mod_four_actual_consumer :
    (∀ a x : ZMod 4, fourCharacterLabeling a x = primRoot 4 ^ (((a*x).val:ℤ))) ∧
      (∀ x : ZMod 4, x∈fourEvenSubgroup ↔ x.val%2=0) ∧
      (∀ m : ℕ,
        let f : ZMod 4 → ZMod 2 := fun x => (x.val:ZMod 2)
        let tab : ZMod 4 → ZMod 4 → Bool := fun a x => decide (a*x=0)
        (tableGroupRecordDist f fourCharacterLabeling).probEvent (fun xs : Fin m → ZMod 4 =>
          ((tableKernelDecode tab (List.ofFn xs)).1 : Set (ZMod 4)) ≠ (fourEvenSubgroup:Set (ZMod 4))) = ((2:ℝ)⁻¹)^m) := by
  refine ⟨fourCharacterLabeling_apply, fun x => mem_fourEvenSubgroup x, ?_⟩
  intro m
  show (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
      (fun xs : Fin m → ZMod 4 =>
        ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) ≠
          (fourEvenSubgroup : Set (ZMod 4))) = ((2 : ℝ)⁻¹)^m
  classical
  have hBA : ∀ xs : Fin m → ZMod 4, (∀ i, xs i = 0) →
      ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) ≠
        (fourEvenSubgroup : Set (ZMod 4)) := by
    intro xs hxs heq
    exact four_univ_ne_even (by rw [← heq, four_decode_univ_of_zero xs hxs])
  have hAS : ∀ xs : Fin m → ZMod 4,
      ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) ≠
        (fourEvenSubgroup : Set (ZMod 4)) →
      (∀ i, xs i = 0) ∨ (∃ i, (xs i).val % 2 = 1) := by
    intro xs hxs
    by_contra hcon
    push Not at hcon
    obtain ⟨hnB, hnS⟩ := hcon
    obtain ⟨i, hi⟩ := hnB
    have hexeven : ∀ i, (xs i).val % 2 = 0 := by
      intro i
      have hne := hnS i
      omega
    exact hxs (four_decode_even_labels xs hexeven
      ⟨i, (four_even_cases (xs i) (hexeven i)).resolve_left hi⟩)
  have hS0 :
      (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
        (fun xs : Fin m → ZMod 4 => ∃ i, (xs i).val % 2 = 1) = 0 := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    apply Finset.sum_eq_zero
    intro xs hxs
    have hex : ∃ i, (xs i).val % 2 = 1 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hxs
    obtain ⟨i, hi⟩ := hex
    have hz : (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2))
        fourCharacterLabeling).prob (xs i) = 0 := by
      rw [four_record_dist_prob, if_neg (by omega)]
    rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf,
        Finset.prod_eq_zero (Finset.mem_univ i) hz]
  have hle :
      (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
        (fun xs : Fin m → ZMod 4 =>
          ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) ≠
            (fourEvenSubgroup : Set (ZMod 4))) ≤
      (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
        (fun xs : Fin m → ZMod 4 => ∀ i, xs i = 0) := by
    calc (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2))
          fourCharacterLabeling).probEvent
          (fun xs : Fin m → ZMod 4 =>
            ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) ≠
              (fourEvenSubgroup : Set (ZMod 4))) ≤
          (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
            (fun xs : Fin m → ZMod 4 =>
              (∀ i, xs i = 0) ∨ (∃ i, (xs i).val % 2 = 1)) :=
          probEvent_mono _ _ _ hAS
      _ ≤ (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
            (fun xs : Fin m → ZMod 4 => ∀ i, xs i = 0) +
          (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
            (fun xs : Fin m → ZMod 4 => ∃ i, (xs i).val % 2 = 1) :=
          probEvent_union_le _ _ _
      _ = (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
            (fun xs : Fin m → ZMod 4 => ∀ i, xs i = 0) := by rw [hS0, add_zero]
  have hge :
      (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
        (fun xs : Fin m → ZMod 4 => ∀ i, xs i = 0) ≤
      (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probEvent
        (fun xs : Fin m → ZMod 4 =>
          ((tableKernelDecode fourTable (List.ofFn xs)).1 : Set (ZMod 4)) ≠
            (fourEvenSubgroup : Set (ZMod 4))) :=
    probEvent_mono _ _ _ hBA
  rw [le_antisymm hle hge]
  have hprod := Qatlib.Concepts.HspRecovery.Distinguisher.FinDist.sum_probOf_forall_eq_pow
    (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling)
    (fun a : ZMod 4 => a = 0) m
  have hsingle : (∑ a ∈ Finset.univ.filter (fun a : ZMod 4 => a = 0),
      (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).prob a)
      = (1 : ℝ) / 2 := by
    rw [Finset.sum_filter, Finset.sum_ite_eq', if_pos (Finset.mem_univ 0),
      four_record_dist_prob, if_pos (show ((0 : ZMod 4).val % 2 = 0) by decide)]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  calc (∑ xs ∈ Finset.univ.filter (fun xs : Fin m → ZMod 4 => ∀ i, xs i = 0),
        (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).probOf xs)
      = (∑ a ∈ Finset.univ.filter (fun a : ZMod 4 => a = 0),
          (tableGroupRecordDist (fun x : ZMod 4 => (x.val : ZMod 2)) fourCharacterLabeling).prob a) ^ m :=
        hprod
    _ = ((2 : ℝ)⁻¹)^m := by
        rw [hsingle]
        have h12 : (1 : ℝ) / 2 = ((2 : ℝ)⁻¹) := by norm_num
        rw [h12]

end Qatlib.Concepts.HspRecovery.BackendAudit
