/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveDefs
import Qatlib.Concepts.HspRecovery.OpenSieve.RepresentationSieveContinuationDefs
import Qatlib.Concepts.HspRecovery.OpenSieve.RepresentationSieveContinuation
import Qatlib.Concepts.HspRecovery.OpenSieve.SubgroupEndpointCounterex
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Nodup
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.SieveAlgorithm
open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve

open Qatlib
open Qatlib.Concepts.HspRecovery.OpenSieve
open scoped Classical BigOperators ENNReal

open Qatlib
open scoped Classical BigOperators ENNReal

private theorem generalCollisionGridCovers (N m t : ℕ) (hm : 0 < m) (ht : t < N) :
    ∃ j a : ℕ, j ≤ N / m + 1 ∧ a < m ∧ j * m = t + a := by
  set q := t / m with hq
  set u := t % m with hu
  have hdecomp : q * m + u = t := by
    rw [hq, hu]
    exact Nat.div_add_mod' t m
  have hu' : u < m := by
    rw [hu]
    exact Nat.mod_lt _ hm
  have hqdiv : q ≤ N / m := by
    refine (Nat.le_div_iff_mul_le hm).2 ?_
    omega
  by_cases hz : u = 0
  · refine ⟨q, 0, by omega, by omega, ?_⟩
    omega
  · refine ⟨q + 1, m - u, by omega, by omega, ?_⟩
    calc (q + 1) * m = q * m + m := by ring
      _ = (t - u) + m := by
        have h : t - u = q * m := by omega
        rw [h]
      _ = t + (m - u) := by omega

private theorem generalCollisionGridPoint {N : ℕ} [NeZero N] (s : ZMod N) (m j a : ℕ)
    (hj : j * m = s.val + a) :
    (↑(j * m) : ZMod N) = (a : ZMod N) + s := by
  have hsv : (s.val : ZMod N) = s := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (ZMod.val_lt s)
  have hcast : (↑(j * m) : ZMod N) = (↑(s.val + a) : ZMod N) := by rw [hj]
  have hsum : (↑(s.val + a) : ZMod N) = (s.val : ZMod N) + (a : ZMod N) := by
    norm_cast
  rw [hcast, hsum, hsv, add_comm]

private theorem mem_generalCollisionRotations {N : ℕ} [NeZero N] (m a : ℕ)
    (ha : a < m) : (a : ZMod N) ∈ generalCollisionRotations N m := by
  simp [generalCollisionRotations, List.mem_range]
  exact ⟨a, ha, rfl⟩

private theorem mem_generalCollisionReflections {N : ℕ} [NeZero N] (m j : ℕ)
    (hj : j ≤ N / m + 1) : (↑(j * m) : ZMod N) ∈ generalCollisionReflections N m := by
  simp [generalCollisionReflections, List.mem_range]
  exact ⟨j, Nat.lt_succ_of_le hj, rfl⟩

theorem clause14_collision_value_collision {N : ℕ} [NeZero N] {S : Type}
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (m : ℕ) (hm : 0 < m) (hN : N ≤ m * m) :
    ∃ (a b : ZMod N),
      a ∈ generalCollisionRotations N m ∧
        b ∈ generalCollisionReflections N m ∧
        f (a, false) = f (b, true) ∧
        b - a = s := by
  obtain ⟨j, a₀, hj, ha, hja⟩ :=
    generalCollisionGridCovers N m s.val hm (ZMod.val_lt s)
  have hpartner : (↑(j * m) : ZMod N) = (a₀ : ZMod N) + s :=
    generalCollisionGridPoint s m j a₀ hja
  have hval : f (↑a₀, false) = f (↑(j * m), true) := by
    have hh := (hf (↑a₀, false) (↑a₀ + s, true)).mpr (Or.inr rfl)
    rw [← hpartner] at hh
    exact hh
  have hdiff : (↑(j * m) : ZMod N) - (a₀ : ZMod N) = s := by
    rw [hpartner]
    exact sub_eq_iff_eq_add.mpr (add_comm _ _)
  exact ⟨↑a₀, ↑(j * m),
    mem_generalCollisionRotations m a₀ ha,
    mem_generalCollisionReflections m j hj, hval, hdiff⟩

private theorem generalCollisionMatch_of_exists {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (a : ZMod N) :
    ∀ (bs : List (ZMod N)),
      (∃ b ∈ bs, f (b, true) = f (a, false)) →
        ∃ b', generalCollisionMatch dec f a bs = some b' ∧ b' ∈ bs ∧
          f (b', true) = f (a, false) := by
  intro bs
  induction bs with
  | nil => intro h; simp at h
  | cons b rest ih =>
    intro h
    by_cases hb : f (b, true) = f (a, false)
    · refine ⟨b, ?_, ?_, hb⟩
      · simp [generalCollisionMatch, hb]
      · simp
    · have hrest : ∃ b' ∈ rest, f (b', true) = f (a, false) := by
        rcases h with ⟨b', hb', heq⟩
        rw [List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact absurd heq hb
        · exact ⟨b', hb', heq⟩
      have hres : ∃ b', generalCollisionMatch dec f a rest = some b' ∧ b' ∈ rest ∧
          f (b', true) = f (a, false) := ih hrest
      obtain ⟨b', hfind, hmem, heq⟩ := hres
      refine ⟨b', ?_, List.mem_cons.mpr (Or.inr hmem), heq⟩
      simp [generalCollisionMatch, hb, hfind]

private theorem generalCollisionMatch_eq_none {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (a : ZMod N) :
    ∀ (bs : List (ZMod N)), (¬ ∃ b ∈ bs, f (a, false) = f (b, true)) →
      generalCollisionMatch dec f a bs = none := by
  intro bs
  induction bs with
  | nil => intro h; simp [generalCollisionMatch]
  | cons b rest ih =>
    intro h
    have hb : f (b, true) ≠ f (a, false) := by
      intro hb'
      exact h ⟨b, by simp, hb'.symm⟩
    have hrest : ¬ ∃ b' ∈ rest, f (a, false) = f (b', true) := by
      intro h'
      rcases h' with ⟨b', hb', heq⟩
      exact h ⟨b', by simp [hb'], heq⟩
    simp [generalCollisionMatch, hb, ih hrest]

private theorem generalCollisionPair_of_exists {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) (m : ℕ) :
    ∀ (rots : List (ZMod N)),
      (∃ a ∈ rots, ∃ b ∈ generalCollisionReflections N m, f (a, false) = f (b, true)) →
        ∃ (a b : ZMod N),
          generalCollisionPair dec f m rots = some (a, b) ∧ f (a, false) = f (b, true) := by
  intro rots
  induction rots with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro h
    by_cases hmatch : ∃ b ∈ generalCollisionReflections N m, f (a, false) = f (b, true)
    · obtain ⟨b, hbmem, heq⟩ := hmatch
      obtain ⟨b', hfind, _, heq'⟩ :=
        generalCollisionMatch_of_exists dec f a (generalCollisionReflections N m)
          ⟨b, hbmem, heq.symm⟩
      refine ⟨a, b', ?_, heq'.symm⟩
      simp [generalCollisionPair, hfind]
    · have hrest : ∃ a' ∈ rest,
          ∃ b ∈ generalCollisionReflections N m, f (a', false) = f (b, true) := by
        rcases h with ⟨a', ha', hb⟩
        rw [List.mem_cons] at ha'
        rcases ha' with rfl | ha'
        · exact absurd hb hmatch
        · exact ⟨a', ha', hb⟩
      have hnone : generalCollisionMatch dec f a (generalCollisionReflections N m) = none :=
        generalCollisionMatch_eq_none dec f a _ hmatch
      have hres : ∃ (a' b' : ZMod N),
          generalCollisionPair dec f m rest = some (a', b') ∧
            f (a', false) = f (b', true) := ih hrest
      obtain ⟨a', b', hfind, heq⟩ := hres
      refine ⟨a', b', ?_, heq⟩
      simp [generalCollisionPair, hnone, hfind]

theorem clause14_collision_determines_slope {N : ℕ} [NeZero N] {S : Type}
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (a b : ZMod N)
    (hval : f (a, false) = f (b, true)) : b - a = s := by
  rcases (hf (a, false) (b, true)).mp hval with h1 | h2
  · exact absurd h1 (by simp)
  · have hbs : b = a + s := by
      have := congrArg Prod.fst h2
      simpa [dihedralReflect] using! this
    rw [hbs]
    exact sub_eq_iff_eq_add.mpr (add_comm _ _)

theorem clause14_collision_recovery {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (m : ℕ) (hm : 0 < m) (hN : N ≤ m * m) :
    (∀ u : ZMod N, u ≠ s → generalCollisionRun f m (some u) = 0) ∧
      ENNReal.ofReal 1 ≤ generalCollisionRun f m (some s) := by
  obtain ⟨a, b, hamem, hbmem, hval, hdiff⟩ := clause14_collision_value_collision f s hf m hm hN
  obtain ⟨a', b', hfind, hval'⟩ :=
    generalCollisionPair_of_exists (Classical.decEq S) f m (generalCollisionRotations N m)
      ⟨a, hamem, b, hbmem, hval⟩
  have hslope : b' - a' = s := clause14_collision_determines_slope f s hf a' b' hval'
  have hreported : generalCollisionSlopeWith (Classical.decEq S) f m = some s := by
    unfold generalCollisionSlopeWith
    rw [hfind]
    simp only [Option.some.injEq]
    exact hslope
  constructor
  · intro u hu
    rw [generalCollisionRun, generalCollisionRunWith, PMF.pure_apply, hreported]
    simp [hu]
  · rw [generalCollisionRun, generalCollisionRunWith, PMF.pure_apply, hreported]
    simp

theorem clause14_collision_endpoint (N m : ℕ) [NeZero N] (hm : 0 < m) (hN : N ≤ m * m) :
    ShiftRecoveryEndpoint N 1 (generalCollisionLedger N m) := by
  refine ⟨fun S f => generalCollisionRun f m, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact le_max_right _ _
  · rfl
  · have hpos : 0 < generalCollisionQueryCount N m := by
      have : 0 < m := hm
      simp [generalCollisionQueryCount, generalCollisionRotations, generalCollisionReflections]
    exact Nat.mul_pos hpos (by omega)
  · intro S instF instDec instAdd f s hf
    exact clause14_collision_recovery f s hf m hm hN

theorem clause14_collision_query_count (N m : ℕ) :
    generalCollisionQueryCount N m = m + (N / m + 2) := by
  simp [generalCollisionQueryCount, generalCollisionRotations, generalCollisionReflections]

theorem clause14_collision_query_bound (N m : ℕ) (hm : 0 < m) (hN : N ≤ m * m) :
    generalCollisionQueryCount N m ≤ 2 * m + 2 := by
  rw [clause14_collision_query_count]
  have hdiv : N / m ≤ m := by
    refine (Nat.div_le_iff_le_mul hm).2 ?_
    omega
  omega

theorem clause14_collision_width_spec (N : ℕ) (hN : 0 < N) :
    0 < generalCollisionWidth N ∧ N ≤ generalCollisionWidth N * generalCollisionWidth N := by
  refine ⟨by simp [generalCollisionWidth], ?_⟩
  have h := Nat.succ_le_succ_sqrt N
  show N ≤ (Nat.sqrt N + 1) * (Nat.sqrt N + 1)
  omega

theorem clause16_collision_ledger_account (N m : ℕ) :
    (generalCollisionLedger N m).samples = generalCollisionQueryCount N m ∧
      (generalCollisionLedger N m).queries = generalCollisionQueryCount N m ∧
      (generalCollisionLedger N m).comparisons =
        max (generalCollisionCompareCount N m) (sortCompareSteps (generalCollisionQueryCount N m)) ∧
      (generalCollisionLedger N m).bitOps =
        sortBitOps (generalCollisionQueryCount N m) (labelBits N) ∧
      (generalCollisionLedger N m).integerBits = labelBits N ∧
      (generalCollisionLedger N m).workspaceBits =
        workspaceBits (generalCollisionQueryCount N m) (labelBits N) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem clause16_collision_compare_account (N m : ℕ) :
    generalCollisionCompareCount N m ≤ (generalCollisionLedger N m).comparisons := by
  exact le_max_left _ _

theorem clause16_collision_bitops_account (N m : ℕ) :
    sortBitOps (generalCollisionLedger N m).samples (generalCollisionLedger N m).integerBits
      ≤ (generalCollisionLedger N m).bitOps := by
  rfl

private theorem abelianReflect_eq_dihedralReflect {N : ℕ} [NeZero N] (s : ZMod N)
    (p : DihedralReg N) : abelianReflect s p = dihedralReflect N s p := by
  rcases p with ⟨a, t⟩
  cases t <;> rfl

theorem walkGoal_transport_is_dihedral {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f g : ZMod N → S) (s : ZMod N)
    (hh : HiddenShift f g s) :
    DihedralReflectionHides N (shiftToDihedralOracle f g) s := by
  have hh' : AbelianReflectionHides (shiftToDihedralOracle f g) s := source_shift_dihedral hh
  unfold DihedralReflectionHides
  rintro ⟨a, ta⟩ ⟨b, tb⟩
  have h : shiftToDihedralOracle f g (a, ta) = shiftToDihedralOracle f g (b, tb) ↔
      (b, tb) = (a, ta) ∨ (b, tb) = abelianReflect s (a, ta) := hh' (a, ta) (b, tb)
  refine Iff.intro ?_ ?_
  · intro hq
    rcases h.mp hq with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (h2.trans (abelianReflect_eq_dihedralReflect s (a, ta)))
  · intro hq
    rcases hq with h1 | h2
    · exact h.mpr (Or.inl h1)
    · exact h.mpr (Or.inr (h2.trans (abelianReflect_eq_dihedralReflect s (a, ta)).symm))

theorem walkGoal_abelian_collision_recovery {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f g : ZMod N → S) (s : ZMod N)
    (hh : HiddenShift f g s) (m : ℕ) (hm : 0 < m) (hN : N ≤ m * m) :
    (∀ u : ZMod N, u ≠ s → generalCollisionRun (shiftToDihedralOracle f g) m (some u) = 0) ∧
      ENNReal.ofReal 1 ≤ generalCollisionRun (shiftToDihedralOracle f g) m (some s) :=
  clause14_collision_recovery (shiftToDihedralOracle f g) s (walkGoal_transport_is_dihedral f g s hh)
    m hm hN

theorem walkGoal_shift_collision_determines {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f g : ZMod N → S) (s : ZMod N)
    (hh : HiddenShift f g s) (a b : ZMod N) (hval : f a = g b) : b - a = s := by
  have hg : Function.Injective g := hh.2.1
  have h1 : g b = g (a + s) := by rw [← hh.2.2 a]; exact hval.symm
  have h2 : b = a + s := hg h1
  rw [h2]
  exact sub_eq_iff_eq_add.mpr (add_comm _ _)

theorem clause16_general_slope_bits (N : ℕ) [NeZero N] (s : ZMod N) :
    generalSlopeOfBits N (generalSlopeBits N) (generalSlopeBit N s)
      = s := by
  have hval : s.val < 2 ^ generalSlopeBits N := by
    have hs := ZMod.val_lt s
    have hN : N ≤ 2 ^ generalSlopeBits N := by
      have hiff := (Nat.log2_lt (n := N) (k := Nat.log2 N + 1) (by omega))
      have hlt : N < 2 ^ (Nat.log2 N + 1) := hiff.mp (by omega)
      unfold generalSlopeBits
      omega
    omega
  have hsum := sum_bits_eq s.val (generalSlopeBits N) hval
  unfold generalSlopeOfBits
  have hbits : ∀ i : Fin (generalSlopeBits N),
      (if generalSlopeBit N s i.val then (2 ^ (i : ℕ) : ℕ) else 0)
        = (if s.val / 2 ^ (i : ℕ) % 2 = 1 then (2 ^ (i : ℕ) : ℕ) else 0) := by
    intro i
    by_cases h : s.val / 2 ^ (i : ℕ) % 2 = 1 <;> simp [generalSlopeBit, h]
  rw [Finset.sum_congr rfl fun i _ => hbits i]
  rw [hsum]
  have hcast : ((s.val : ℕ) : ZMod N) = s := by
    rw [ZMod.natCast_val s]
    exact ZMod.cast_id N s
  exact hcast

theorem clause16_general_descent_slope (N : ℕ) [NeZero N] (s : ZMod N) (k : ℕ)
    (_hk : k ≤ generalSlopeBits N) :
    generalDescentSlope N k s = (s.val / 2 ^ k : ℕ) := by
  rfl

private theorem map_range_getD {α : Type} : ∀ (k i : ℕ) (f : ℕ → α) (d : α),
    i < k → (List.map f (List.range k)).getD i d = f i
  | 0, _, _, _, h => by omega
  | Nat.succ k, 0, f, d, _ => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.getD_cons_zero]
  | Nat.succ k, Nat.succ i, f, d, h => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.getD_cons_succ]
      exact map_range_getD k i (f ∘ Nat.succ) d (by omega)

private theorem fin_bitListValue (bs : List Bool) :
    (∑ i : Fin bs.length, if bs.getD i.val false then (2 ^ i.val : ℕ) else 0)
      = bitValue bs := by
  induction bs with
  | nil => simp [bitValue]
  | cons b bs ih =>
    have hshift : ∀ (i : Fin bs.length),
        (if (b :: bs).getD (i.val + 1) false then (2 ^ (i.val + 1) : ℕ) else 0)
          = 2 * (if bs.getD i.val false then (2 ^ i.val : ℕ) else 0) := by
      intro i
      rw [List.getD_cons_succ, pow_succ]
      by_cases h : bs.getD i.val false = true
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.getD_cons_zero, pow_zero, Fin.val_zero, Fin.val_succ]
    have hsum2 : (∑ i : Fin bs.length,
        if (b :: bs).getD (i.val + 1) false then (2 ^ (i.val + 1) : ℕ) else 0)
        = ∑ i : Fin bs.length, 2 * (if bs.getD i.val false then (2 ^ i.val : ℕ) else 0) :=
      Fintype.sum_congr _ _ (fun i => hshift i)
    rw [hsum2, ← Finset.mul_sum, ih]
    simp only [bitValue]

theorem bitListValue_eq_bitValue (bs : List Bool) : bitListValue bs = bitValue bs := by
  rw [← fin_bitListValue bs, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp [hi]

theorem clause16_general_bit_value_eq_val (N : ℕ) [NeZero N] (s : ZMod N) :
    bitListValue (generalSlopeBitList N s) = s.val := by
  have hget : ∀ (i : ℕ) (hi : i < generalSlopeBits N),
      (generalSlopeBitList N s).getD i false = generalSlopeBit N s i := by
    intro i hi
    rw [generalSlopeBitList]
    exact map_range_getD (generalSlopeBits N) i (generalSlopeBit N s) false hi
  have hfin : (∑ i : Fin (generalSlopeBits N),
      if generalSlopeBit N s i.val then (2 ^ i.val : ℕ) else 0) = s.val := by
    have hval : s.val < 2 ^ generalSlopeBits N := by
      have hs := ZMod.val_lt s
      have hN : N ≤ 2 ^ generalSlopeBits N := by
        have hiff := (Nat.log2_lt (n := N) (k := Nat.log2 N + 1) (by omega))
        have hlt : N < 2 ^ (Nat.log2 N + 1) := hiff.mp (by omega)
        unfold generalSlopeBits
        omega
      omega
    have h := sum_bits_eq s.val (generalSlopeBits N) hval
    simpa only [generalSlopeBit, decide_eq_true_eq] using! h
  have hrange : (∑ i ∈ Finset.range (generalSlopeBits N),
      if generalSlopeBit N s i then (2 ^ i : ℕ) else 0)
      = ∑ i : Fin (generalSlopeBits N),
        if generalSlopeBit N s i.val then (2 ^ i.val : ℕ) else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [hi]
  have hsum : bitListValue (generalSlopeBitList N s) = s.val := by
    have hlen : (generalSlopeBitList N s).length = generalSlopeBits N := by
      simp [generalSlopeBitList]
    simp only [bitListValue]
    rw [hlen]
    have hcongr : (∑ i ∈ Finset.range (generalSlopeBits N),
          if (generalSlopeBitList N s).getD i false then (2 ^ i : ℕ) else 0)
        = ∑ i ∈ Finset.range (generalSlopeBits N),
          if generalSlopeBit N s i then (2 ^ i : ℕ) else 0 :=
      Finset.sum_congr rfl (fun i hi => by rw [hget i (Finset.mem_range.mp hi)])
    rw [hcongr, hrange, hfin]
  exact hsum

theorem clause16_general_candidate_eq_slope (N : ℕ) [NeZero N] (s : ZMod N) :
    generalDescentCandidate N (generalSlopeBitList N s) = s := by
  have hcast : ((s.val : ℕ) : ZMod N) = s := by
    rw [ZMod.natCast_val s]
    exact ZMod.cast_id N s
  simp only [generalDescentCandidate]
  rw [clause16_general_bit_value_eq_val N s, hcast]

theorem clause16_general_candidate_is_house (n : ℕ) (bs : List Bool) :
    generalDescentCandidate (2 ^ n) bs = assembleCandidate n bs := by
  rw [generalDescentCandidate, bitListValue_eq_bitValue]
  apply ZMod.val_injective
  simp only [assembleCandidate]
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_mod]

theorem clause16_general_window_key_eq (n t : ℕ) (k : ZMod (2 ^ n)) :
    generalWindowKey (2 ^ n) (2 ^ t) k = windowKey n t 0 k := by
  simp [generalWindowKey, windowKey]

theorem clause16_general_window_agree_iff (n t : ℕ) (k ℓ : ZMod (2 ^ n)) :
    generalWindowAgree (2 ^ n) (2 ^ t) k ℓ ↔ windowAgree n t 0 k ℓ := by
  simp [generalWindowAgree, generalWindowKey, windowAgree]

theorem clause16_general_window_agree_mod (N q : ℕ) [NeZero N] (k ℓ : ZMod N) :
    generalWindowAgree N q k ℓ ↔ k.val % q = ℓ.val % q := Iff.rfl

theorem clause16_frozen_complete_descent :
    (∀ (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
      DihedralReflectionHides (2 ^ n) f s →
        (∀ s' : ZMod (2 ^ n), s' ≠ s → slopeDescent n S f (some s') = 0) ∧
        slopeDescent n S f (some s) = 1 - slopeDescent n S f none) := by
  intro n S inst inst_1 inst_2 f s hf
  exact (clause16.2.1.1 n S f s hf)

theorem clause16_frozen_descent_failure :
    (∀ (n : ℕ) (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
      (f : DihedralReg (2 ^ n) → S) (s : ZMod (2 ^ n)),
      DihedralReflectionHides (2 ^ n) f s →
        slopeDescent n S f none ≤ ENNReal.ofReal (descentFailureBound n)) := by
  intro n S inst inst_1 inst_2 f s hf
  exact (clause16.2.1.2 n S f s hf)

theorem clause16_frozen_descent_records :
    ∀ n : ℕ, descentRecords n = Qatlib.Concepts.HspRecovery.ReductionCore.sourcePowerTwoQueryBudget n := by
  intro n
  exact clause16.2.2.1 n

theorem clause16_frozen_actual_sorting :
    (∀ (α : Type) (key : α → ℕ) (L : List α),
      (sortRecords key L).Perm L ∧ (sortRecords key L).length = L.length) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α),
      sortedByKey key (sortRecords key L)) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α),
      sortCompareCount key L ≤ L.length * L.length) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α) (p : α × α),
      p ∈ sortedPairs key (sortRecords key L) → key p.1 = key p.2) ∧
    (∀ (α : Type) (key : α → ℕ) (L : List α),
      2 * (sortedPairs key (sortRecords key L)).length ≤ L.length) ∧
    (∀ (n w t : ℕ) (α : Type) [DecidableEq α] (label : α → ZMod (2 ^ n))
      (L : List α),
      (sievePairWith n label w t L).length =
        (sortedPairs (fun r => windowKey n w t (label r))
          (sortRecords (fun r => windowKey n w t (label r)) L)).length) := by
  have h := clause16.2.2.2
  refine ⟨h.1.1, h.1.2.1, h.1.2.2.1, ?_, h.1.2.2.2.2.1, h.1.2.2.2.2.2⟩
  intro α key L p hp
  exact h.1.2.2.2.1 α key L p hp

theorem clause16_frozen_bit_time_and_space :
    (∀ (α : Type) (key : α → ℕ) (L : List α) (k : ℕ),
      sortCompareCount key L * (k + 1) ≤ sortBitTime k L.length) ∧
    (∀ (n : ℕ),
      descentBitTime n ≤
        ∑ k ∈ Finset.Icc 1 n, 2 * (levelTrials k * levelRecords k) ^ 2 * (k + 1)) ∧
    (∀ (n k : ℕ), k ∈ Finset.Icc 1 n →
      sortSpace k (levelTrials k * levelRecords k) ≤ descentSpace n) ∧
    (∀ (n : ℕ),
      descentSpace n ≤ ∑ k ∈ Finset.Icc 1 n, levelTrials k * levelRecords k * k) := by
  exact clause16.2.2.2.2

theorem clause16_general_sort_ledgers (N : ℕ) (samples : ℕ) :
    generalSortCompareSteps samples = samples * (Nat.log2 (samples + 1) + 1) ∧
      generalSortBitOps samples (labelBits N)
        = generalSortCompareSteps samples * labelBits N ∧
      generalWorkspaceBits samples (labelBits N) = samples * (labelBits N + 2) ∧
      (generalRecoveryLedger N samples).comparisons = generalSortCompareSteps samples ∧
      (generalRecoveryLedger N samples).bitOps
        = generalSortBitOps samples (labelBits N) ∧
      (generalRecoveryLedger N samples).workspaceBits
        = generalWorkspaceBits samples (labelBits N) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem clause16_general_ledger_side_conditions (N : ℕ) (samples : ℕ) (hs : 0 < samples) :
    (generalRecoveryLedger N samples).samples ≤ (generalRecoveryLedger N samples).queries ∧
      generalSortCompareSteps (generalRecoveryLedger N samples).samples
        ≤ (generalRecoveryLedger N samples).comparisons ∧
      generalSortBitOps (generalRecoveryLedger N samples).samples
        (generalRecoveryLedger N samples).integerBits
        ≤ (generalRecoveryLedger N samples).bitOps ∧
      0 < (generalRecoveryLedger N samples).workspaceBits := by
  have h1 : (generalRecoveryLedger N samples).samples
      = (generalRecoveryLedger N samples).queries := rfl
  have h2 : (generalRecoveryLedger N samples).comparisons
      = generalSortCompareSteps (generalRecoveryLedger N samples).samples := rfl
  have h3 : (generalRecoveryLedger N samples).bitOps
      = generalSortBitOps (generalRecoveryLedger N samples).samples
        (generalRecoveryLedger N samples).integerBits := rfl
  have h4 : 0 < (generalRecoveryLedger N samples).workspaceBits := by
    unfold generalRecoveryLedger
    dsimp [generalWorkspaceBits]
    have hpos : 0 < labelBits N := by
      unfold labelBits
      positivity
    nlinarith
  refine ⟨h1.le, h2.le, h3.le, h4⟩

theorem walkGoal_abelian_shift_transport (A : Type) [AddCommGroup A] [Fintype A] :
    AbelianShiftTransport A := by
  intro S _ _ _ f g s hs
  exact sourceOracleReductions.1 A S f g s hs

theorem walkGoal_abelian_pow2_transport (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) :
    DihedralReflectionHides (2 ^ n) (shiftToDihedralOracle f g) s := by
  simpa [DihedralReflectionHides, AbelianReflectionHides, abelianReflect, dihedralReflect] using!
    (source_shift_dihedral h)

theorem walkGoal_abelian_pow2_wrong_zero (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) (u : ZMod (2 ^ n)) (hu : u ≠ s) :
    abelianShiftRun n S f g (some u) = 0 := by
  exact descent_wrong_zero n S (shiftToDihedralOracle f g) s
    (walkGoal_abelian_pow2_transport n f g s h) u hu

theorem walkGoal_abelian_pow2_success_mass (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) :
    abelianShiftRun n S f g (some s) = 1 - abelianShiftRun n S f g none := by
  exact descent_mass n (shiftToDihedralOracle f g) s (walkGoal_abelian_pow2_transport n f g s h)

theorem walkGoal_abelian_pow2_failure_bound (n : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f g : ZMod (2 ^ n) → S) (s : ZMod (2 ^ n))
    (h : HiddenShift f g s) :
    abelianShiftRun n S f g none ≤ ENNReal.ofReal (descentFailureBound n) := by
  exact descent_fail_bound n S (shiftToDihedralOracle f g) s
      (walkGoal_abelian_pow2_transport n f g s h)

private def devRootCeil (n : ℕ) : ℕ := Nat.ceil (Real.sqrt (n : ℝ))

private theorem devRootCeil_mono : Monotone devRootCeil := by
  intro n m hnm
  exact Nat.ceil_mono (Real.sqrt_le_sqrt (Nat.cast_le.mpr hnm))

private theorem devRootCeil_square (n : ℕ) : n ≤ devRootCeil n ^ 2 := by
  have hs : Real.sqrt (n : ℝ) ≤ (devRootCeil n : ℝ) := Nat.le_ceil _
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  have hm : (0 : ℝ) ≤ devRootCeil n := Nat.cast_nonneg _
  have hnn : (n : ℝ) ≤ (devRootCeil n : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  exact_mod_cast hnn

private theorem dev_budget_polynomial (n : ℕ) :
    sourcePowerTwoQueryBudget n ≤ 24000 * (n + 1) ^ 2 * 2 ^ (3 * devRootCeil n) := by
  induction n with
  | zero => simp [sourcePowerTwoQueryBudget]
  | succ n ih =>
    have hm : 2 ^ (3 * devRootCeil n) ≤ 2 ^ (3 * devRootCeil (n + 1)) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 3 (devRootCeil_mono (by omega)))
    have hrec : sourcePowerTwoQueryBudget (n + 1) =
        24000 * (n + 2) * 2 ^ (3 * devRootCeil n) + sourcePowerTwoQueryBudget n := by
      simp only [sourcePowerTwoQueryBudget, sourceParityTrials, devRootCeil]
      ring
    have hsq : (n + 2) + (n + 1) ^ 2 ≤ (n + 2) ^ 2 := by nlinarith
    calc
      sourcePowerTwoQueryBudget (n + 1) =
          24000 * (n + 2) * 2 ^ (3 * devRootCeil n) + sourcePowerTwoQueryBudget n := hrec
      _ ≤ 24000 * (n + 2) * 2 ^ (3 * devRootCeil n)
          + 24000 * (n + 1) ^ 2 * 2 ^ (3 * devRootCeil n) := Nat.add_le_add_left ih _
      _ = 24000 * ((n + 2) + (n + 1) ^ 2) * 2 ^ (3 * devRootCeil n) := by ring
      _ ≤ 24000 * (n + 2) ^ 2 * 2 ^ (3 * devRootCeil n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 24000 hsq)
      _ ≤ 24000 * (n + 2) ^ 2 * 2 ^ (3 * devRootCeil (n + 1)) :=
        Nat.mul_le_mul_left _ hm
      _ = _ := by ring

private theorem dev_budget_pow (n : ℕ) :
    sourcePowerTwoQueryBudget n ≤ 2 ^ (15 + 7 * devRootCeil n) := by
  have hnp : n + 1 ≤ 2 ^ (2 * devRootCeil n) :=
    (show n + 1 ≤ 2 * devRootCeil n ^ 2 + 1 by nlinarith [devRootCeil_square n]).trans
      (Nat.two_mul_sq_add_one_le_two_pow_two_mul _)
  have hpow : 2 ^ (2 * devRootCeil n * 2) = (2 ^ (2 * devRootCeil n)) ^ 2 :=
    Nat.pow_mul (2) (2 * devRootCeil n) 2
  have h2 : (n + 1) ^ 2 ≤ 2 ^ (4 * devRootCeil n) := by
    have h1 : (n + 1) ^ 2 ≤ (2 ^ (2 * devRootCeil n)) ^ 2 := Nat.pow_le_pow_left hnp 2
    rw [← hpow, show 2 * devRootCeil n * 2 = 4 * devRootCeil n by omega] at h1
    exact h1
  have h24 : 24000 ≤ 2 ^ 15 := by decide
  calc
    sourcePowerTwoQueryBudget n ≤ 24000 * (n + 1) ^ 2 * 2 ^ (3 * devRootCeil n) :=
      dev_budget_polynomial n
    _ ≤ 24000 * 2 ^ (4 * devRootCeil n) * 2 ^ (3 * devRootCeil n) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 24000 h2)
    _ = 24000 * (2 ^ (4 * devRootCeil n) * 2 ^ (3 * devRootCeil n)) := by ring
    _ = 24000 * 2 ^ (7 * devRootCeil n) := by
      rw [← pow_add, show 4 * devRootCeil n + 3 * devRootCeil n = 7 * devRootCeil n by omega]
    _ ≤ 2 ^ 15 * 2 ^ (7 * devRootCeil n) := Nat.mul_le_mul_right _ h24
    _ = 2 ^ (15 + 7 * devRootCeil n) := by
      rw [← pow_add, show 15 + 7 * devRootCeil n = 15 + 7 * devRootCeil n by rfl]

theorem walkGoal_abelian_pow2_query_growth :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      (abelianShiftQueries n : ℝ) ≤ C * (2 : ℝ) ^ (c * Real.sqrt (labelBits (2 ^ n))) := by
  have hbound : ∀ n : ℕ, (sourcePowerTwoQueryBudget n : ℝ)
      ≤ 4194304 * (2 : ℝ) ^ (7 * Real.sqrt (n : ℝ)) := by
    intro n
    have hceil : (devRootCeil n : ℝ) ≤ Real.sqrt (n : ℝ) + 1 :=
      (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
    have hexp : ((15 + 7 * devRootCeil n : ℕ) : ℝ) ≤ 22 + 7 * Real.sqrt (n : ℝ) := by
      push_cast
      linarith
    have hcast : ((2 ^ (15 + 7 * devRootCeil n) : ℕ) : ℝ)
        = (2 : ℝ) ^ ((15 + 7 * devRootCeil n : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      norm_num
      rw [← Real.rpow_natCast]
      push_cast
      ring
    have h1 : ((2 ^ (15 + 7 * devRootCeil n) : ℕ) : ℝ)
        = (2 : ℝ) ^ ((15 + 7 * devRootCeil n : ℕ) : ℝ) := hcast
    have h2 : (2 : ℝ) ^ ((15 + 7 * devRootCeil n : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (22 + 7 * Real.sqrt (n : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    calc
      (sourcePowerTwoQueryBudget n : ℝ) ≤ ((2 ^ (15 + 7 * devRootCeil n) : ℕ) : ℝ) := by
        exact_mod_cast (dev_budget_pow n)
      _ = (2 : ℝ) ^ ((15 + 7 * devRootCeil n : ℕ) : ℝ) := h1
      _ ≤ (2 : ℝ) ^ (22 + 7 * Real.sqrt (n : ℝ)) := h2
      _ = 4194304 * (2 : ℝ) ^ (7 * Real.sqrt (n : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
  refine ⟨4194304, 7, by norm_num, by norm_num, ?_⟩
  intro n
  have hbits : labelBits (2 ^ n) = n + 1 := by
    simp [labelBits, Nat.log2_two_pow]
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (labelBits (2 ^ n) : ℝ) := by
    rw [hbits]
    have h1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (n : ℕ) ≤ n + 1 by omega)
    exact Real.sqrt_le_sqrt h1
  have hexp : (7 * Real.sqrt (n : ℝ) : ℝ) ≤ 7 * Real.sqrt (labelBits (2 ^ n) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  calc
    (abelianShiftQueries n : ℝ) = (sourcePowerTwoQueryBudget n : ℝ) := by
      rw [abelianShiftQueries, descentRecords_eq]
    _ ≤ 4194304 * (2 : ℝ) ^ (7 * Real.sqrt (n : ℝ)) := hbound n
    _ ≤ 4194304 * (2 : ℝ) ^ (7 * Real.sqrt (labelBits (2 ^ n) : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by norm_num)

def walkGoal_abelian_endpoint_obligation (A : Type) [AddCommGroup A] [Fintype A] : Prop :=
  AbelianShiftEndpoint A

def walkGoal_subgroup_endpoint_is_refuted :
    ∀ (lg : RecoveryLedger), ¬ SubgroupRecoveryEndpoint 4 lg := by
  intro lg
  exact not_subgroup_endpoint lg

theorem walkGoal_slope_determined_by_fibres {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s t : ZMod N)
    (hf : DihedralReflectionHides N f s) (ht : DihedralReflectionHides N f t) :
    s = t := by

  have hcases : (dihedralReflect N s (0, false) = (0, false)) ∨
      (dihedralReflect N s (0, false) = dihedralReflect N t (0, false)) := by

    have hmem : f (0, false) = f (dihedralReflect N s (0, false)) :=
      (hf (0, false) (dihedralReflect N s (0, false))).mpr (Or.inr rfl)
    have hdisj := (ht (0, false) (dihedralReflect N s (0, false))).mp hmem
    exact hdisj
  rcases hcases with hcases | hcases
  · have hne : ¬dihedralReflect N s (0, false) = (0, false) := by
      intro hh
      have := congrArg Prod.snd hh
      simp [dihedralReflect] at this
    exact absurd hcases hne
  · have hfst : s = t := by
      have := congrArg Prod.fst hcases
      simp [dihedralReflect] at this
      exact this
    exact hfst

private theorem min'_eq_of_le {α : Type} [LinearOrder α] (s : Finset α) (H : s.Nonempty)
    (e : α) (hmem : e ∈ s) (hge : ∀ j ∈ s, e ≤ j) : s.min' H = e := by
  have h1 : s.min' H ≤ e := Finset.min'_le s e hmem
  have h2 : e ≤ s.min' H := hge (s.min' H) (Finset.min'_mem s H)
  exact le_antisymm h1 h2

theorem dvd_of_zmod_natCast_eq {N e j k : ℕ} (he : e ∣ N) (hj : j < N)
    (h : ((j : ℕ) : ZMod N) = ((k * e : ℕ) : ZMod N)) : e ∣ j := by
  have hv := congrArg ZMod.val h
  simp only [ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt hj] at hv
  refine Nat.dvd_iff_mod_eq_zero.mpr ?_
  rw [hv, Nat.mod_mod_of_dvd _ he,
    Nat.mod_eq_zero_of_dvd (by
      rw [Nat.mul_comm]; exact Nat.dvd_mul_right e k)]

theorem mod_congr_of_zmod_eq {N e b k : ℕ} [NeZero N] (he : e ∣ N) (hb : b < N)
    (s : ZMod N) (h : ((b : ℕ) : ZMod N) = s + ((k * e : ℕ) : ZMod N)) :
    b % e = s.val % e := by
  have hv := congrArg ZMod.val h
  simp only [ZMod.val_add, ZMod.val_natCast] at hv
  rw [Nat.mod_eq_of_lt hb] at hv
  have hdvd : e ∣ k * e := by
    rw [Nat.mul_comm]
    exact Nat.dvd_mul_right e k
  have hstep1 : b % e = (s.val + k * e % N) % e := by
    rw [hv, Nat.mod_mod_of_dvd _ he]
  have hstep2 : (s.val + k * e % N) % e = (s.val % e + (k * e) % e) % e := by
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ he]
  have hstep3 : (k * e) % e = 0 := Nat.mod_eq_zero_of_dvd hdvd
  calc b % e = (s.val + k * e % N) % e := hstep1
    _ = (s.val % e + (k * e) % e) % e := hstep2
    _ = (s.val % e + 0) % e := by rw [hstep3]
    _ = s.val % e := by rw [Nat.add_zero, Nat.mod_mod]

theorem subgroupRotationPeriod_dvd {N : ℕ} (H : DihedralSubgroupData N) :
    subgroupRotationPeriod H ∣ N := by
  have h1 : H.period * subgroupRotationPeriod H = N := Nat.mul_div_cancel' H.periodDvd
  have h2 : subgroupRotationPeriod H ∣ H.period * subgroupRotationPeriod H :=
    Nat.dvd_mul_left _ _
  refine h2.trans (show H.period * subgroupRotationPeriod H ∣ N from ?_)
  rw [h1]

theorem subgroupRotationPeriod_pos {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    0 < subgroupRotationPeriod H := by
  have he : subgroupRotationPeriod H ∣ N := subgroupRotationPeriod_dvd H
  by_contra h
  have hz : subgroupRotationPeriod H = 0 := Nat.eq_zero_of_not_pos h
  rw [hz] at he
  exact absurd he (by simp [NeZero.ne N])

theorem subgroupRotationPeriod_le {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    subgroupRotationPeriod H ≤ N :=
  Nat.le_of_dvd (NeZero.pos N) (subgroupRotationPeriod_dvd H)

theorem walkGoal_rotation_period_in_fibre {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (H : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) :
    f (0, false) = f ((subgroupRotationPeriod H : ℕ), false) := by
  have horbit : DihedralSubgroupOrbit N H (0, false) ((subgroupRotationPeriod H : ℕ), false) := by
    show ∃ k : ℕ, ((subgroupRotationPeriod H : ℕ) : ZMod N) = (0 : ZMod N) +
      ((k * (N / H.period) : ℕ) : ZMod N)
    refine ⟨1, ?_⟩
    simp only [subgroupRotationPeriod, Nat.one_mul, zero_add]
  exact (hf (0, false) ((subgroupRotationPeriod H : ℕ), false)).mpr horbit

theorem walkGoal_rotation_fibre_dvd {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (H : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) (j : ℕ) (hj : j < N)
    (h : f (0, false) = f ((j : ℕ), false)) :
    subgroupRotationPeriod H ∣ j := by
  have horbit : ∃ k : ℕ, ((j : ℕ) : ZMod N) = (0 : ZMod N) +
      ((k * subgroupRotationPeriod H : ℕ) : ZMod N) := by
    simpa only [DihedralSubgroupOrbit] using! (hf (0, false) ((j : ℕ), false)).mp h
  obtain ⟨k, hk⟩ := horbit
  exact dvd_of_zmod_natCast_eq (subgroupRotationPeriod_dvd H) hj (by
    simpa only [zero_add] using! hk)

theorem walkGoal_reflection_fibre_mod {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (H : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) (s : ZMod N) (hs : H.slope = some s)
    (b : ℕ) (hb : b < N) (h : f (0, false) = f ((b : ℕ), true)) :
    b % subgroupRotationPeriod H = s.val % subgroupRotationPeriod H := by
  have horbit : ∃ s' : ZMod N, H.slope = some s' ∧
      ∃ k : ℕ, ((b : ℕ) : ZMod N) = (0 : ZMod N) + s' +
        ((k * subgroupRotationPeriod H : ℕ) : ZMod N) := by
    simpa only [DihedralSubgroupOrbit] using! (hf (0, false) ((b : ℕ), true)).mp h
  obtain ⟨s', hs', ⟨k, hk⟩⟩ := horbit
  have hss : s' = s := Option.some.inj (hs'.symm.trans hs)
  rw [hss] at hk
  exact mod_congr_of_zmod_eq (subgroupRotationPeriod_dvd H) hb s (by
    simpa only [zero_add] using! hk)

theorem walkGoal_reflection_in_fibre {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (H : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) (s : ZMod N) (hs : H.slope = some s) :
    f (0, false) = f ((s.val : ℕ), true) := by
  have horbit : DihedralSubgroupOrbit N H (0, false) ((s.val : ℕ), true) := by
    show ∃ s' : ZMod N, H.slope = some s' ∧
      ∃ k : ℕ, ((s.val : ℕ) : ZMod N) = (0 : ZMod N) + s' +
        ((k * subgroupRotationPeriod H : ℕ) : ZMod N)
    refine ⟨s, hs, 0, ?_⟩
    simp only [Nat.zero_mul, Nat.cast_zero, zero_add, add_zero, ZMod.natCast_val,
      ZMod.cast_id]
  exact (hf (0, false) ((s.val : ℕ), true)).mpr horbit

theorem walkGoal_no_reflection_fibre {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (H : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) (hs : H.slope = none)
    (b : ℕ) : f (0, false) ≠ f ((b : ℕ), true) := by
  intro h
  have horbit : ∃ s' : ZMod N, H.slope = some s' ∧
      ∃ k : ℕ, ((b : ℕ) : ZMod N) = (0 : ZMod N) + s' +
        ((k * subgroupRotationPeriod H : ℕ) : ZMod N) := by
    simpa only [DihedralSubgroupOrbit] using! (hf (0, false) ((b : ℕ), true)).mp h
  obtain ⟨s', hs', _⟩ := horbit
  rw [hs] at hs'
  simp at hs'

theorem walkGoal_rotationPeriodOf_eq {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S)
    (H : DihedralSubgroupData N) (hf : DihedralSubgroupHides f H) :
    rotationPeriodOfWith dec f = subgroupRotationPeriod H := by
  have henum : subgroupRotationPeriod H ≤ N := subgroupRotationPeriod_le H
  have hepos : 0 < subgroupRotationPeriod H := subgroupRotationPeriod_pos H
  have hmem : subgroupRotationPeriod H ∈ rotationPeriodCandidatesWith dec f := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    by_cases hlt : subgroupRotationPeriod H < N
    · have hfib := walkGoal_rotation_period_in_fibre f H hf
      simp only [decide_eq_true_eq]
      exact Or.inr ⟨by omega, hfib⟩
    · simp only [decide_eq_true_eq]
      exact Or.inl (by omega)
  have hge : ∀ j ∈ rotationPeriodCandidatesWith dec f, subgroupRotationPeriod H ≤ j := by
    intro j hj
    have hjrange : j ≤ N := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      omega
    have hjmem := (Finset.mem_filter.mp hj).2
    simp only [decide_eq_true_eq] at hjmem
    rcases hjmem with hjn | ⟨hj1, hjf⟩
    · omega
    · by_cases hjN : j = N
      · omega
      · have hlt : j < N := by omega
        have hdvd : subgroupRotationPeriod H ∣ j :=
          walkGoal_rotation_fibre_dvd f H hf j hlt hjf
        have hle : subgroupRotationPeriod H ≤ j := Nat.le_of_dvd (by omega) hdvd
        omega
  unfold rotationPeriodOfWith
  exact min'_eq_of_le _ _ _ hmem hge

theorem walkGoal_reflectionPartnerOf_none {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S)
    (H : DihedralSubgroupData N) (hf : DihedralSubgroupHides f H) (hs : H.slope = none) :
    reflectionPartnerOfWith dec f = none := by
  have hcands : ∀ b ∈ reflectionPartnerCandidatesWith dec f, b = N := by
    intro b hb
    have hbmem := (Finset.mem_filter.mp hb).2
    simp only [decide_eq_true_eq] at hbmem
    rcases hbmem with hbn | hbf
    · exact hbn
    · exact absurd hbf (walkGoal_no_reflection_fibre f H hf hs b)
  have hmin : reflectionPartnerMinWith dec f = N := by
    unfold reflectionPartnerMinWith
    refine min'_eq_of_le _ _ _ (by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      simp) (by intro b hb; rw [hcands b hb])
  simp [reflectionPartnerOfWith, hmin]

theorem walkGoal_reflectionPartnerOf_some {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S)
    (H : DihedralSubgroupData N) (hf : DihedralSubgroupHides f H) (s : ZMod N)
    (hs : H.slope = some s) :
    ∃ b : ℕ, reflectionPartnerOfWith dec f = some b ∧ b < N ∧
      f (0, false) = f ((b : ℕ), true) ∧
      b % subgroupRotationPeriod H = s.val % subgroupRotationPeriod H := by
  have hfib := walkGoal_reflection_in_fibre f H hf s hs
  have hmem : s.val ∈ reflectionPartnerCandidatesWith dec f := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := ZMod.val_lt s
      omega), ?_⟩
    simp only [decide_eq_true_eq]
    exact Or.inr hfib
  have hmin_le : reflectionPartnerMinWith dec f ≤ s.val := by
    show (reflectionPartnerCandidatesWith dec f).min' _ ≤ s.val
    exact Finset.min'_le _ s.val hmem
  have hmin_lt : reflectionPartnerMinWith dec f < N := by
    have hval := ZMod.val_lt s
    omega
  have hmin_mem : reflectionPartnerMinWith dec f ∈ reflectionPartnerCandidatesWith dec f := by
    show (reflectionPartnerCandidatesWith dec f).min' _ ∈ reflectionPartnerCandidatesWith dec f
    refine Finset.min'_mem _ ⟨N, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp
  have hmin_fib : f (0, false) = f ((reflectionPartnerMinWith dec f : ℕ), true) := by
    have hmem' := (Finset.mem_filter.mp hmin_mem).2
    simp only [decide_eq_true_eq] at hmem'
    rcases hmem' with hbn | hbf
    · rw [hbn] at hmin_lt
      omega
    · exact hbf
  refine ⟨reflectionPartnerMinWith dec f, ?_, hmin_lt, hmin_fib, ?_⟩
  · simp only [reflectionPartnerOfWith, if_neg (Nat.ne_of_lt hmin_lt)]
  · exact walkGoal_reflection_fibre_mod f H hf s hs _ hmin_lt hmin_fib

theorem walkGoal_subgroupReductionAnswer_eq {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S)
    (H : DihedralSubgroupData N) (hf : DihedralSubgroupHides f H) :
    subgroupReductionAnswerWith dec f = reduceSubgroupData H := by
  have hper : rotationPeriodOfWith dec f = subgroupRotationPeriod H :=
      walkGoal_rotationPeriodOf_eq dec f H hf
  have hepos : 0 < subgroupRotationPeriod H := subgroupRotationPeriod_pos H
  have hperiod : N / rotationPeriodOfWith dec f = H.period := by
    have h1 : H.period * (N / H.period) = N := Nat.mul_div_cancel' H.periodDvd
    have h2 : (N / (N / H.period)) * (N / H.period) = N := by
      have := Nat.mul_div_cancel' (subgroupRotationPeriod_dvd H)
      rw [Nat.mul_comm] at this
      exact this
    have heq : H.period = N / (N / H.period) := by
      have h3 : H.period * (N / H.period) = (N / (N / H.period)) * (N / H.period) := by
        rw [h1]
        exact h2.symm
      exact Nat.mul_right_cancel (by
        have := subgroupRotationPeriod_pos H
        exact this) h3
    rw [hper]
    exact heq.symm
  have hper' : N / subgroupRotationPeriod H = H.period := by
    rw [← hper]
    exact hperiod
  cases hsH : H.slope with
  | none =>
    have hnone : reflectionPartnerOfWith dec f = none :=
        walkGoal_reflectionPartnerOf_none dec f H hf hsH
    simp only [subgroupReductionAnswerWith, reduceSubgroupData, hper, hper', hsH, hnone,
      Option.map_none]
  | some s =>
    obtain ⟨b, hb, hblt, hbfib, hbmod⟩ := walkGoal_reflectionPartnerOf_some dec f H hf s hsH
    simp only [subgroupReductionAnswerWith, reduceSubgroupData, hper, hper', hsH, hb,
      Option.map_some]
    congr 1
    exact congrArg some hbmod

theorem walkGoal_reduced_data_unique {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (H H' : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) (hf' : DihedralSubgroupHides f H') :
    reduceSubgroupData H = reduceSubgroupData H' := by
  have hper : H.period = H'.period := by
    have hle : subgroupRotationPeriod H' ≤ subgroupRotationPeriod H := by
      by_cases hlt : subgroupRotationPeriod H < N
      · have hfib := walkGoal_rotation_period_in_fibre f H hf
        have hdvd : subgroupRotationPeriod H' ∣ subgroupRotationPeriod H :=
          walkGoal_rotation_fibre_dvd f H' hf' _ hlt hfib
        exact Nat.le_of_dvd (by
          have := subgroupRotationPeriod_pos H
          exact this) hdvd
      · have henum := subgroupRotationPeriod_le H
        have hle' : subgroupRotationPeriod H' ≤ N :=
          Nat.le_of_dvd (NeZero.pos N) (subgroupRotationPeriod_dvd H')
        omega
    have hge : subgroupRotationPeriod H ≤ subgroupRotationPeriod H' := by
      by_cases hlt : subgroupRotationPeriod H' < N
      · have hfib := walkGoal_rotation_period_in_fibre f H' hf'
        have hdvd : subgroupRotationPeriod H ∣ subgroupRotationPeriod H' :=
          walkGoal_rotation_fibre_dvd f H hf _ hlt hfib
        exact Nat.le_of_dvd (by
          have := subgroupRotationPeriod_pos H'
          exact this) hdvd
      · have henum := subgroupRotationPeriod_le H'
        have hle' : subgroupRotationPeriod H ≤ N :=
          Nat.le_of_dvd (NeZero.pos N) (subgroupRotationPeriod_dvd H)
        omega
    have heq : subgroupRotationPeriod H = subgroupRotationPeriod H' := le_antisymm hge hle
    have h1 : H.period * subgroupRotationPeriod H = N := Nat.mul_div_cancel' H.periodDvd
    have h2 : H'.period * subgroupRotationPeriod H' = N := Nat.mul_div_cancel' H'.periodDvd
    rw [← heq] at h2
    have h3 : H.period * subgroupRotationPeriod H
        = H'.period * subgroupRotationPeriod H := by omega
    exact Nat.mul_right_cancel (by
      have := subgroupRotationPeriod_pos H
      exact this) h3
  have heq : subgroupRotationPeriod H' = subgroupRotationPeriod H := by
    unfold subgroupRotationPeriod
    rw [hper]
  cases hsH : H.slope with
  | none =>
    cases hsH' : H'.slope with
    | none =>
      simp only [reduceSubgroupData, hsH, hsH', Option.map_none]
      rw [hper]
    | some s' =>
      exfalso
      have hfib := walkGoal_reflection_in_fibre f H' hf' s' hsH'
      exact walkGoal_no_reflection_fibre f H hf hsH _ hfib
  | some s =>
    cases hsH' : H'.slope with
    | none =>
      exfalso
      have hfib := walkGoal_reflection_in_fibre f H hf s hsH
      exact walkGoal_no_reflection_fibre f H' hf' hsH' _ hfib
    | some s' =>
      have hfib := walkGoal_reflection_in_fibre f H' hf' s' hsH'
      have hval := ZMod.val_lt s'
      have hmod : s'.val % subgroupRotationPeriod H' = s.val % subgroupRotationPeriod H := by
        rw [heq]
        exact walkGoal_reflection_fibre_mod f H hf s hsH s'.val hval hfib
      simp only [reduceSubgroupData, hsH, hsH', Option.map_some]
      rw [hper]
      congr 1
      exact congrArg some hmod.symm

theorem walkGoal_reduced_data_well_formed {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    ReducedSubgroupDataWellFormed (reduceSubgroupData H) := by
  refine ⟨H.periodDvd, ?_⟩
  intro s hs
  cases hsH : H.slope with
  | none =>
      have h1 : (none : Option (ZMod N)).map (fun t => t.val % subgroupRotationPeriod H)
          = some s := by
        simp only [reduceSubgroupData, hsH, Option.map_none] at hs
        exact hs
      simp at h1
  | some r =>
      have h1 : (some r).map (fun t => t.val % subgroupRotationPeriod H) = some s := by
        simp only [reduceSubgroupData, hsH, Option.map_some] at hs
        exact hs
      have h2 : r.val % subgroupRotationPeriod H = s := Option.some.inj h1
      subst h2
      exact Nat.mod_lt _ (by
        have := subgroupRotationPeriod_pos H
        omega)

theorem walkGoal_prop21_rotation_part {N : ℕ} [NeZero N] (H : DihedralSubgroupData N) :
    H.period * subgroupRotationPeriod H = N ∧ 0 < H.period := by
  have h1 : H.period * subgroupRotationPeriod H = N := Nat.mul_div_cancel' H.periodDvd
  have h2 : 0 < H.period := by
    have hmod : N % H.period = 0 := (Nat.dvd_iff_mod_eq_zero).mp H.periodDvd
    by_contra h
    have hz : H.period = 0 := Nat.eq_zero_of_not_pos h
    rw [hz] at hmod
    simp only [Nat.mod_zero] at hmod
    exact absurd hmod (NeZero.ne N)
  exact ⟨h1, h2⟩

theorem walkGoal_prop21_reduction {N : ℕ} [NeZero N] {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S) (H : DihedralSubgroupData N)
    (hf : DihedralSubgroupHides f H) :
    (∀ a b : ℕ, a < N → b < N →
        (f ((a : ℕ), false) = f ((b : ℕ), false) ↔
          ∃ k : ℕ, ((b : ℕ) : ZMod N) = ((a : ℕ) : ZMod N) +
            ((k * subgroupRotationPeriod H : ℕ) : ZMod N))) ∧
    (∀ a b : ℕ, a < N → b < N →
        (f ((a : ℕ), false) = f ((b : ℕ), true) ↔
          ∃ s : ZMod N, H.slope = some s ∧
            ∃ k : ℕ, ((b : ℕ) : ZMod N) = ((a : ℕ) : ZMod N) + s +
              ((k * subgroupRotationPeriod H : ℕ) : ZMod N))) ∧
    subgroupReductionAnswerWith dec f = reduceSubgroupData H := by
  refine ⟨fun a b (ha : a < N) (hb : b < N) => ?_, ?_⟩
  · simpa only [DihedralSubgroupOrbit] using! hf ((a : ℕ), false) ((b : ℕ), false)
  · refine ⟨fun a b (ha : a < N) (hb : b < N) => ?_,
      walkGoal_subgroupReductionAnswer_eq dec f H hf⟩
    simpa only [DihedralSubgroupOrbit] using! hf ((a : ℕ), false) ((b : ℕ), true)

theorem walkGoal_subgroup_reduction_success {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (dec : DecidableEq S) (f : DihedralReg N → S)
    (H : DihedralSubgroupData N) (hf : DihedralSubgroupHides f H) :
    (∀ o : Option (ReducedSubgroupData N),
        o ≠ some (reduceSubgroupData H) → subgroupReductionRunWith dec f o = 0) ∧
      ENNReal.ofReal 1 ≤ subgroupReductionRunWith dec f (some (reduceSubgroupData H)) := by
  have hans := walkGoal_subgroupReductionAnswer_eq dec f H hf
  constructor
  · intro o ho
    have hne : o ≠ some (subgroupReductionAnswerWith dec f) := by
      rw [hans]
      exact ho
    rw [subgroupReductionRunWith, PMF.pure_apply]
    simp [hne]
  · rw [subgroupReductionRunWith, PMF.pure_apply, hans]
    simp

theorem walkGoal_reduced_subgroup_endpoint {N : ℕ} [NeZero N] :
    ReducedSubgroupEndpoint N (subgroupReductionLedger N) := by
  have hpos : 0 < subgroupReductionQueryCount N := by
    have hN : (1 : ℕ) ≤ N := NeZero.pos N
    dsimp [subgroupReductionQueryCount]
    omega
  refine ⟨fun S f => subgroupReductionRun f, le_rfl, le_rfl, le_rfl, ?_, ?_⟩
  · simp only [subgroupReductionLedger, workspaceBits]
    exact Nat.mul_pos (by omega) (by omega)
  · intro S instF instDec instAdd f H hf
    have hsucc := walkGoal_subgroup_reduction_success (Classical.decEq S) f H hf
    exact hsucc

theorem walkGoal_subgroup_reduction_ledger_fits (N : ℕ) [NeZero N] :
    subgroupReductionQueryCount N = 2 * N + 1 ∧
      subgroupReductionCompareCount N = 2 * N ∧
      (subgroupReductionLedger N).samples = subgroupReductionQueryCount N ∧
      (subgroupReductionLedger N).queries = subgroupReductionQueryCount N ∧
      (subgroupReductionLedger N).comparisons
          = sortCompareSteps (subgroupReductionQueryCount N) ∧
      (subgroupReductionLedger N).bitOps
          = sortBitOps (subgroupReductionQueryCount N) (labelBits N) ∧
      (subgroupReductionLedger N).integerBits = labelBits N ∧
      (subgroupReductionLedger N).workspaceBits
          = workspaceBits (N + 1) (labelBits N) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem walkGoal_subgroup_reduction_compare_budget (N : ℕ) [NeZero N] :
    subgroupReductionCompareCount N ≤ sortCompareSteps (subgroupReductionQueryCount N) := by
  have hpos : 0 < subgroupReductionQueryCount N := by
    have hN : (1 : ℕ) ≤ N := NeZero.pos N
    dsimp [subgroupReductionQueryCount]
    omega
  have hk : (1 : ℕ) ≤ Nat.log2 (subgroupReductionQueryCount N + 1) + 1 := by
    have := Nat.log2_le_self (subgroupReductionQueryCount N + 1)
    omega
  have hmul : subgroupReductionQueryCount N
      ≤ subgroupReductionQueryCount N * (Nat.log2 (subgroupReductionQueryCount N + 1) + 1) := by
    have h := Nat.mul_le_mul hk (le_refl (subgroupReductionQueryCount N))
    simpa [Nat.mul_comm, Nat.one_mul] using! h
  have h2 : 2 * N ≤ subgroupReductionQueryCount N := by
    dsimp [subgroupReductionQueryCount]
    omega
  show 2 * N ≤ sortCompareSteps (subgroupReductionQueryCount N)
  rw [sortCompareSteps]
  omega

private theorem pow_two_ge_succ (a : ℕ) : 2 ^ a ≥ a + 1 := by
  induction a with
  | zero => decide
  | succ a ih =>
    have h : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    omega

theorem radixAlpha_zero (r : ℕ) : radixAlpha r 0 = 0 := by
  simp [radixAlpha]

theorem radixAlpha_eq_iff (r k a : ℕ) (hr : 2 ≤ r) (hk : 0 < k) :
    radixAlpha r k = a ↔
      r ^ a ∣ k ∧ ∀ n, a < n → n ≤ k → ¬ (r ^ n ∣ k) := by
  simp only [radixAlpha, if_neg (Nat.ne_of_gt hk)]
  rw [Nat.findGreatest_eq_iff]
  constructor
  · rintro ⟨ha, hP, hmax⟩
    refine ⟨?_, ?_⟩
    · by_cases hz : a = 0
      · simp [hz]
      · exact hP hz
    · intro n hn hnk
      by_contra hc
      exact hmax hn hnk hc
  · rintro ⟨hdiv, hmax⟩
    refine ⟨?_, ?_, ?_⟩
    · by_cases hz : a = 0
      · omega
      · have hle : r ^ a ≤ k := Nat.le_of_dvd (by positivity) hdiv
        have hrp : 2 ^ a ≤ r ^ a := Nat.pow_le_pow_left hr a
        have := pow_two_ge_succ a
        omega
    · by_cases hz : a = 0
      · simp [hz]
      · exact fun _ => hdiv
    · intro n hn hnk hPn
      exact hmax n hn hnk hPn

theorem radixAlpha_dvd (r k : ℕ) (hr : 2 ≤ r) (hk : 0 < k) :
    r ^ radixAlpha r k ∣ k := by
  exact ((radixAlpha_eq_iff r k (radixAlpha r k) hr hk).mp rfl).1

theorem radixAlpha_cancellation (r k ℓ a : ℕ) (hr : 2 ≤ r) (hlt : ℓ < k)
    (h : r ^ (a + 1) ∣ k - ℓ) : radixAlpha r (k - ℓ) ≥ a + 1 := by
  have hpos : 0 < k - ℓ := by omega
  have hpos' : 0 < r ^ (a + 1) := by
    have h1 : 1 ≤ r ^ (a + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hle : r ^ (a + 1) ≤ k - ℓ := Nat.le_of_dvd hpos h
  have hbound : a + 1 ≤ k - ℓ := by
    have hrp : 2 ^ (a + 1) ≤ r ^ (a + 1) := Nat.pow_le_pow_left hr (a + 1)
    have h2a := pow_two_ge_succ (a + 1)
    omega
  have hP : (fun j => r ^ j ∣ k - ℓ) (a + 1) := h
  have hfg : a + 1 ≤ Nat.findGreatest (fun j => r ^ j ∣ k - ℓ) (k - ℓ) :=
    Nat.le_findGreatest hbound hP
  simp only [radixAlpha, if_neg (Nat.ne_of_gt hpos)]
  exact hfg

theorem radixFinalLabel (r n k : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n)
    (h : r ^ (n - 1) ∣ k) : ∃ b : ℕ, b < r ∧ k = b * r ^ (n - 1) := by
  have hmul : k / r ^ (n - 1) * r ^ (n - 1) = k := Nat.div_mul_cancel h
  have hpos : 0 < r ^ (n - 1) := by
    have h1 : 1 ≤ r ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hlt : k / r ^ (n - 1) < r := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have hz : r * r ^ (n - 1) = r ^ n := by
      have h1 : r * r ^ (n - 1) = r ^ 1 * r ^ (n - 1) := by rw [pow_one]
      rw [h1, ← pow_add]
      congr 1
      omega
    rw [hz]
    exact hk
  exact ⟨k / r ^ (n - 1), hlt, hmul.symm⟩

theorem radixGreedyValue_ge (r N : ℕ) (L : List ℕ) (k ℓ : ℕ)
    (h : (k, ℓ) ∈ radixPairs (radixMinAlphaSublist r L)) :
    radixPairValue r N k ℓ ≤ radixGreedyValue r N L := by
  have hmono : ∀ (ps : List (ℕ × ℕ)) (a : ℕ),
      a ≤ ps.foldl (fun b q => max b (radixPairValue r N q.1 q.2)) a := by
    intro ps
    induction ps with
    | nil => intro a; simp
    | cons q qs ih =>
      intro a
      simp only [List.foldl_cons]
      have h1 := ih (max a (radixPairValue r N q.1 q.2))
      omega
  have hfold : ∀ (ps : List (ℕ × ℕ)) (acc : ℕ) (p : ℕ × ℕ), p ∈ ps →
      radixPairValue r N p.1 p.2 ≤
        ps.foldl (fun a q => max a (radixPairValue r N q.1 q.2)) acc := by
    intro ps
    induction ps with
    | nil => intro acc p hp; simp at hp
    | cons q qs ih =>
      intro acc p hp
      have hp' : p = q ∨ p ∈ qs := by simp at hp; omega
      rcases hp' with hpq | hp'
      · rw [hpq]
        simp only [List.foldl_cons]
        have h1 := hmono qs (max acc (radixPairValue r N q.1 q.2))
        omega
      · have h1 := ih (max acc (radixPairValue r N q.1 q.2)) p hp'
        simp only [List.foldl_cons] at h1 ⊢
        omega
  have h1 := hfold (radixPairs (radixMinAlphaSublist r L)) 0 (k, ℓ) h
  unfold radixGreedyValue
  omega

theorem radixGreedy_progress (r N : ℕ) (hr : 2 ≤ r) (L : List ℕ) (k ℓ : ℕ)
    (hk : k ∈ radixMinAlphaSublist r L) (hl : ℓ ∈ radixMinAlphaSublist r L)
    (hne : k ≠ ℓ) (hlt : ℓ < k) (hkN : k < N) (hlN : ℓ < N)
    (h : r ^ (radixMinAlpha r L + 1) ∣ k - ℓ) :
    radixGreedyValue r N L ≥ radixMinAlpha r L + 1 := by
  have hpair : (k, ℓ) ∈ radixPairs (radixMinAlphaSublist r L) := by
    simp only [radixPairs, List.mem_flatMap]
    refine ⟨k, hk, ?_⟩
    simp only [List.mem_map]
    refine ⟨ℓ, ?_, rfl⟩
    simp only [List.mem_filter]
    exact ⟨hl, by simp [Ne.symm hne]⟩
  have hmod : (k + N - ℓ) % N = k - ℓ := by
    have h1 : k - ℓ < N := by omega
    have h3 : k + N - ℓ = N + (k - ℓ) := by omega
    rw [h3, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h1]
  have hval : radixPairValue r N k ℓ ≥ radixAlpha r (k - ℓ) := by
    simp only [radixPairValue]
    have : radixAlpha r ((k + N - ℓ) % N) = radixAlpha r (k - ℓ) := by rw [hmod]
    omega
  have hcancel : radixAlpha r (k - ℓ) ≥ radixMinAlpha r L + 1 :=
    radixAlpha_cancellation r k ℓ (radixMinAlpha r L) hr hlt h
  have hge := radixGreedyValue_ge r N L k ℓ hpair
  omega

theorem clause14_window_key_iff (N q : ℕ) [NeZero N] (k ℓ : ZMod N) :
    generalWindowKey N q k = generalWindowKey N q ℓ ↔ generalWindowAgree N q k ℓ := by
  rfl

theorem clause14_radix_schedule (r N : ℕ) [NeZero N] (s : ZMod N) :
    (radixDigits r N s).length = radixDigitCount r N ∧
      (radixWidths r N).length = radixDigitCount r N := by
  constructor
  · unfold radixDigits
    simp
  · unfold radixWidths
    simp

theorem clause14_radix_digit_count_pow (r N : ℕ) (hr : 2 ≤ r) (hN : 1 ≤ N) :
    N ≤ r ^ radixDigitCount r N := by
  by_cases hN1 : N = 1
  · subst hN1
    have hlog : Nat.log r 0 = 0 := by
      rw [Nat.log_eq_zero_iff]
      omega
    rw [radixDigitCount, if_neg (by omega), hlog, pow_one]
    omega
  · have hN2 : 2 ≤ N := by omega
    have hcount : radixDigitCount r N = Nat.log r (N - 1) + 1 := by
      rw [radixDigitCount, if_neg (by omega)]
    rw [hcount]
    have h1 : Nat.log r (N - 1) < Nat.log r (N - 1) + 1 := by omega
    have h2 := (Nat.log_lt_iff_lt_pow (b := r) (x := Nat.log r (N - 1) + 1)
      (y := N - 1) (by omega) (by omega)).mp h1
    omega

theorem clause14_radix_schedule_covers (r N : ℕ) [NeZero N] (s : ZMod N) :
    (radixDigits r N s).length = radixDigitCount r N ∧
      (radixWidths r N).length = radixDigitCount r N ∧
      (radixWidths r N).getD 0 0 = radixDigitCount r N := by
  refine ⟨?_, ?_, ?_⟩
  · unfold radixDigits
    simp
  · unfold radixWidths
    simp
  · by_cases hk : radixDigitCount r N = 0
    · simp [radixWidths, hk]
    · rw [radixWidths, map_range_getD (radixDigitCount r N) 0
        (fun i => radixDigitCount r N - i) 0 (by omega)]
      simp

def clause14_general_endpoint_obligation (N : ℕ) (p : ℝ) : Prop :=
  ∃ samples : ℕ, 0 < samples ∧ GeneralShiftEndpoint N p (generalRecoveryLedger N samples)

def clause14_radix_endpoint_obligation (r : ℕ) : Prop := RadixRecoveryEndpoint r

theorem clause14_partner_set_dec_independent {N : ℕ} [NeZero N] {S : Type}
    (dec₁ dec₂ : DecidableEq S) (f : DihedralReg N → S) :
    generalPartnerSetWith dec₁ f = generalPartnerSetWith dec₂ f := by
  ext q
  simp [generalPartnerSetWith]

theorem clause14_partner_set_singleton {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S)
    (s : ZMod N) (hf : DihedralReflectionHides N f s) :
    generalPartnerSetWith dec f = {⟨s, true⟩} := by
  ext q
  simp only [generalPartnerSetWith, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro hq
    have h1 := (hf (generalBasePoint N) q).mp hq.1.symm
    rcases h1 with h1 | h1
    · have hbase : q = (0, false) := by simpa [generalBasePoint] using! h1
      rw [hbase] at hq
      exact absurd hq.2 (by simp)
    · have hpartner : q = (s, true) := by
        simpa [generalBasePoint, dihedralReflect] using! h1
      exact hpartner
  · intro hq
    subst hq
    refine ⟨?_, rfl⟩
    exact (hf (s, true) (generalBasePoint N)).mpr
      (Or.inr (by simp [generalBasePoint, dihedralReflect]))

theorem clause14_recovered_slope_eq {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S)
    (s : ZMod N) (hf : DihedralReflectionHides N f s) :
    generalRecoveredSlopeWith dec f = s := by
  calc generalRecoveredSlopeWith dec f = (generalPartnerSetWith dec f).sum fun q => q.1 := rfl
    _ = (⟨s, true⟩ : DihedralReg N).1 := by
      rw [clause14_partner_set_singleton dec f s hf]
      simp
    _ = s := rfl

theorem clause14_recovery_run_pure {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S) :
    ∀ u : ZMod N, generalRecoveryRunWith dec f (some u) =
      if u = generalRecoveredSlopeWith dec f then 1 else 0 := by
  intro u
  have hlaw : generalRecoveryRunWith dec f =
      PMF.pure (some (generalRecoveredSlopeWith dec f)) := rfl
  rw [hlaw, PMF.pure_apply]
  by_cases h : u = generalRecoveredSlopeWith dec f
  · simp [h]
  · simp [h, Option.some.injEq]

theorem clause14_recovery_success {N : ℕ} [NeZero N] {S : Type}
    (dec : DecidableEq S) (f : DihedralReg N → S)
    (s : ZMod N) (hf : DihedralReflectionHides N f s) :
    (∀ u : ZMod N, u ≠ s → generalRecoveryRunWith dec f (some u) = 0) ∧
      ENNReal.ofReal 1 ≤ generalRecoveryRunWith dec f (some s) := by
  have hslope := clause14_recovered_slope_eq dec f s hf
  constructor
  · intro u hu
    rw [clause14_recovery_run_pure dec f]
    simp [hu, hslope]
  · rw [clause14_recovery_run_pure dec f]
    simp [hslope]

theorem clause14_recovery_ledger_fits (N : ℕ) [NeZero N] :
    generalRecoveryQueryCount N = 2 * N ∧
      generalRecoveryCompareCount N = 2 * N ∧
      (generalRecoveryLedger N (generalRecoveryQueryCount N)).samples
          = generalRecoveryQueryCount N ∧
      (generalRecoveryLedger N (generalRecoveryQueryCount N)).queries
          = generalRecoveryQueryCount N ∧
      (generalRecoveryLedger N (generalRecoveryQueryCount N)).comparisons
          = generalSortCompareSteps (generalRecoveryQueryCount N) ∧
      (generalRecoveryLedger N (generalRecoveryQueryCount N)).bitOps
          = generalSortBitOps (generalRecoveryQueryCount N) (labelBits N) ∧
      (generalRecoveryLedger N (generalRecoveryQueryCount N)).workspaceBits
          = generalWorkspaceBits (generalRecoveryQueryCount N) (labelBits N) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem clause14_general_endpoint_discharged (N : ℕ) [NeZero N] (p : ℝ) (hp : p ≤ 1) :
    clause14_general_endpoint_obligation N p := by
  have hpos : 0 < generalRecoveryQueryCount N := by
    dsimp [generalRecoveryQueryCount]
    have hN : (1 : ℕ) ≤ N := NeZero.pos N
    omega
  refine ⟨generalRecoveryQueryCount N, hpos, ?_⟩
  refine ⟨fun S f => generalRecoveryRun f, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · have hbits : 0 ≤ labelBits N := Nat.zero_le _
    simp only [generalRecoveryLedger, generalWorkspaceBits]
    exact Nat.mul_pos hpos (by omega)
  · intro S instF instDec instAdd f s hf
    have h := clause14_recovery_success (Classical.decEq S) f s hf
    have hmass : generalRecoveryRun f (some s) = 1 := by
      have hrun := clause14_recovery_run_pure (Classical.decEq S) f
      have hslope := clause14_recovered_slope_eq (Classical.decEq S) f s hf
      rw [show generalRecoveryRun f = generalRecoveryRunWith (Classical.decEq S) f from rfl]
      rw [hrun]
      simp [hslope]
    refine ⟨h.1, ?_⟩
    calc ENNReal.ofReal p ≤ ENNReal.ofReal 1 := ENNReal.ofReal_mono hp
      _ = 1 := by simp
      _ = generalRecoveryRun f (some s) := hmass.symm

theorem clause13_record_counts_are_realised {N : ℕ} [NeZero N] {S : Type}
    [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S)
    (a q w m : ℕ) :
    (∀ L ∈ (actualHalfWidthRecordLaw f w (sieveFreshRecordCount m)).support,
      L.length = sieveFreshRecordCount m) ∧
      (∀ L ∈ (actualStageLaw f a q w (sieveFreshRecordCount m) m).support,
        2 ^ m * L.length ≤ sieveFreshRecordCount m) ∧
      sieveKeptRecordCount m (sieveFreshRecordCount m) ≤ sieveRecordCount m ∧
      sieveRecordCount m = 2 * sieveFreshRecordCount m ∧
      sieveQueryLedger m = 2 * sieveFreshRecordCount m + 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro L hL
    exact clause2_actual_fresh_length f w (sieveFreshRecordCount m) L hL
  · intro L hL
    exact clause2_actual_stage_length f a q w (sieveFreshRecordCount m) m L hL
  · exact clause2_kept_record_ledger_le m (sieveFreshRecordCount m)
  · rfl
  · simp only [sieveQueryLedger, sieveFreshRecordCount]
    ring

theorem clause13_transport_with_sieve_and_resources (N : ℕ) [NeZero N] :
    RepTransportTarget N ∧
      (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
        (f : DihedralReg N → S) (a q w L0 m : ℕ),
        ∃ (stageLaw : Fin (m + 1) → PMF (List (ActualHalfWidthRecord N))),
          stageLaw 0 = actualHalfWidthRecordLaw f w L0 ∧
          (∀ j : Fin m,
            stageLaw j.succ = (stageLaw j.castSucc).bind (actualLayerCombine a q)) ∧
          stageLaw ⟨m, by omega⟩ =
            (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q m)) ∧
      (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
        (f : DihedralReg N → S) (a q w m : ℕ),
        (∀ L ∈ (actualHalfWidthRecordLaw f w (sieveFreshRecordCount m)).support,
          L.length = sieveFreshRecordCount m) ∧
          (∀ L ∈ (actualStageLaw f a q w (sieveFreshRecordCount m) m).support,
            2 ^ m * L.length ≤ sieveFreshRecordCount m) ∧
          sieveKeptRecordCount m (sieveFreshRecordCount m) ≤ sieveRecordCount m ∧
          sieveRecordCount m = 2 * sieveFreshRecordCount m ∧
          sieveQueryLedger m = 2 * sieveFreshRecordCount m + 1) := by
  refine ⟨clause1_representation_record_bridge N, ?_, ?_⟩
  · intro S _ _ _ f a q w L0 m
    exact clause2_actual_stage_law f a q w L0 m
  · intro S _ _ _ f a q w m
    exact clause13_record_counts_are_realised f a q w m

theorem clause13_endpoint (N : ℕ) [NeZero N] :
    RepTransportTarget N ∧
      (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
        (f : DihedralReg N → S) (a q w L0 m : ℕ),
        ∃ (stageLaw : Fin (m + 1) → PMF (List (ActualHalfWidthRecord N))),
          stageLaw 0 = actualHalfWidthRecordLaw f w L0 ∧
          (∀ j : Fin m,
            stageLaw j.succ = (stageLaw j.castSucc).bind (actualLayerCombine a q)) ∧
          stageLaw ⟨m, by omega⟩ =
            (actualHalfWidthRecordLaw f w L0).bind (actualLayeredCombine a q m)) ∧
      (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
        (f : DihedralReg N → S) (a q w m : ℕ),
        (∀ L ∈ (actualHalfWidthRecordLaw f w (sieveFreshRecordCount m)).support,
          L.length = sieveFreshRecordCount m) ∧
          (∀ L ∈ (actualStageLaw f a q w (sieveFreshRecordCount m) m).support,
            2 ^ m * L.length ≤ sieveFreshRecordCount m) ∧
          sieveKeptRecordCount m (sieveFreshRecordCount m) ≤ sieveRecordCount m ∧
          sieveRecordCount m = 2 * sieveFreshRecordCount m ∧
          sieveQueryLedger m = 2 * sieveFreshRecordCount m + 1) :=
  clause13_transport_with_sieve_and_resources N

theorem clause14_endpoint (N : ℕ) [NeZero N] :
    (∀ m : ℕ, 0 < m → N ≤ m * m →
      ShiftRecoveryEndpoint N 1 (generalCollisionLedger N m)) ∧
      (ShiftRecoveryEndpoint N 1 (generalCollisionLedger N (generalCollisionWidth N))) ∧
      (generalCollisionQueryCount N (generalCollisionWidth N)
        ≤ 2 * generalCollisionWidth N + 2) := by
  obtain ⟨hw, hN⟩ := clause14_collision_width_spec N (NeZero.pos N)
  refine ⟨?_, ?_, ?_⟩
  · intro m hm hmN
    exact clause14_collision_endpoint N m hm hmN
  · exact clause14_collision_endpoint N (generalCollisionWidth N) hw hN
  · exact clause14_collision_query_bound N (generalCollisionWidth N) hw hN

theorem walkGoal_endpoint (N : ℕ) [NeZero N] :
    (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S] (f g : ZMod N → S)
      (s : ZMod N), HiddenShift f g s →
      (∀ u : ZMod N, u ≠ s →
        generalCollisionRun (shiftToDihedralOracle f g) (generalCollisionWidth N) (some u) = 0) ∧
        ENNReal.ofReal 1 ≤
          generalCollisionRun (shiftToDihedralOracle f g) (generalCollisionWidth N) (some s)) ∧
    (∀ (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S] (f g : ZMod N → S)
      (s : ZMod N) (a b : ZMod N), HiddenShift f g s → f a = g b → b - a = s) := by
  obtain ⟨hw, hN⟩ := clause14_collision_width_spec N (NeZero.pos N)
  refine ⟨?_, ?_⟩
  · intro S instF instDec instAdd f g s hh
    exact walkGoal_abelian_collision_recovery f g s hh (generalCollisionWidth N) hw hN
  · intro S instF instDec instAdd f g s a b hh hval
    exact walkGoal_shift_collision_determines f g s hh a b hval

theorem clause16_endpoint (N : ℕ) (m : ℕ) (hm : 0 < m) :
    (generalCollisionLedger N m).samples = generalCollisionQueryCount N m ∧
      (generalCollisionLedger N m).queries = generalCollisionQueryCount N m ∧
      generalCollisionCompareCount N m ≤ (generalCollisionLedger N m).comparisons ∧
      sortBitOps (generalCollisionLedger N m).samples (generalCollisionLedger N m).integerBits
        ≤ (generalCollisionLedger N m).bitOps ∧
      (generalCollisionLedger N m).integerBits = labelBits N ∧
      0 < (generalCollisionLedger N m).workspaceBits := by
  obtain ⟨hacc, hq, hcomp, hbits, hint, hwsp⟩ := clause16_collision_ledger_account N m
  refine ⟨hacc, hq, ?_, ?_, hint, ?_⟩
  · rw [hcomp]
    exact le_max_left _ _
  · rw [hbits, hacc, hint]
  · rw [hwsp]
    have hpos : 0 < generalCollisionQueryCount N m := by
      simp [generalCollisionQueryCount, generalCollisionRotations, generalCollisionReflections]
    exact Nat.mul_pos hpos (by omega)

private theorem mem_zmodBasisRot {n : ℕ} [NeZero n] {m a : ℕ} (ha : a < m) :
    ((a : ℕ) : ZMod n) ∈ zmodBasis m := by
  classical
  rw [zmodBasis, Finset.mem_union]
  left
  rw [Finset.mem_image]
  exact ⟨a, Finset.mem_range.mpr ha, rfl⟩

private theorem mem_zmodBasisRefl {n : ℕ} [NeZero n] {m j : ℕ} (hj : j ≤ n / m + 1) :
    ((j * m : ℕ) : ZMod n) ∈ zmodBasis m := by
  classical
  rw [zmodBasis, Finset.mem_union]
  right
  rw [Finset.mem_image]
  exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩

theorem walkGoal_zmod_basis_covers {n : ℕ} [NeZero n] (m : ℕ) (hm : 0 < m) (hN : n ≤ m * m)
    (x : ZMod n) :
    ∃ a ∈ zmodBasis m, ∃ b ∈ zmodBasis m, b - a = x := by
  classical
  set q := x.val / m with hq
  set u := x.val % m with hu
  have hdecomp : q * m + u = x.val := by
    rw [hq, hu]
    exact Nat.div_add_mod' x.val m
  have hu' : u < m := by
    rw [hu]
    exact Nat.mod_lt _ hm
  have hxl : x.val < n := ZMod.val_lt x
  have hqdiv : q ≤ n / m := by
    refine (Nat.le_div_iff_mul_le hm).2 ?_
    omega
  have hvalcast : (x.val : ZMod n) = x := by
    apply ZMod.val_injective
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (ZMod.val_lt x)
  by_cases hz : u = 0
  · have hqm : q * m = x.val := by omega
    have hpartner : ((q * m : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) + x := by
      rw [hqm, hvalcast]
      simp
    refine ⟨((0 : ℕ) : ZMod n), mem_zmodBasisRot (hm), ((q * m : ℕ) : ZMod n),
      mem_zmodBasisRefl (by omega), ?_⟩
    rw [sub_eq_iff_eq_add.mpr]
    exact hpartner.trans (add_comm _ _)
  · have hqm : q * m = x.val - u := by omega
    have hsplit : (q + 1) * m = x.val + (m - u) := by
      calc (q + 1) * m = q * m + m := by ring
        _ = (x.val - u) + m := by rw [hqm]
        _ = x.val + (m - u) := by omega
    have hsum : ((x.val + (m - u) : ℕ) : ZMod n) =
        (x.val : ZMod n) + ((m - u : ℕ) : ZMod n) := by
      norm_cast
    have hpartner : (((q + 1) * m : ℕ) : ZMod n) = ((m - u : ℕ) : ZMod n) + x := by
      rw [hsplit, hsum, hvalcast, add_comm]
    refine ⟨((m - u : ℕ) : ZMod n), mem_zmodBasisRot (by omega), (((q + 1) * m : ℕ) : ZMod n),
      mem_zmodBasisRefl (by omega), ?_⟩
    rw [sub_eq_iff_eq_add.mpr]
    exact hpartner.trans (add_comm _ _)

theorem walkGoal_product_basis_covers {ι : Type} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, NeZero (n i)) (D : ∀ i, Finset (ZMod (n i)))
    (hD : ∀ i, ∀ x : ZMod (n i), ∃ a ∈ D i, ∃ b ∈ D i, b - a = x) :
    ∀ x : (i : ι) → ZMod (n i),
      ∃ a ∈ productDifferenceBasis n hn D, ∃ b ∈ productDifferenceBasis n hn D, b - a = x := by
  classical
  intro x
  have ha : ∀ i, (Classical.choose (hD i (x i))) ∈ D i :=
    fun i => (Classical.choose_spec (hD i (x i))).1
  have hb : ∀ i, (Classical.choose ((Classical.choose_spec (hD i (x i))).2))
      - Classical.choose (hD i (x i)) = x i :=
    fun i => (Classical.choose_spec ((Classical.choose_spec (hD i (x i))).2)).2
  have hmemA : (fun i => Classical.choose (hD i (x i))) ∈ productDifferenceBasis n hn D := by
    simp only [productDifferenceBasis, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ha
  have hmemB : (fun i => Classical.choose ((Classical.choose_spec (hD i (x i))).2))
      ∈ productDifferenceBasis n hn D := by
    simp only [productDifferenceBasis, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun i => (Classical.choose_spec ((Classical.choose_spec (hD i (x i))).2)).1
  refine ⟨fun i => Classical.choose (hD i (x i)), hmemA,
    fun i => Classical.choose ((Classical.choose_spec (hD i (x i))).2), hmemB, ?_⟩
  funext i
  exact hb i

theorem walkGoal_product_basis_card {ι : Type} [Fintype ι] (n : ι → ℕ)
    (hn : ∀ i, NeZero (n i)) (D : ∀ i, Finset (ZMod (n i))) :
    (productDifferenceBasis n hn D).card ≤ ∏ i, (D i).card := by
  classical
  have hle : (productDifferenceBasis n hn D).card ≤
      (Finset.pi (Finset.univ : Finset ι) D).card := by
    refine Finset.card_le_card_of_injOn
      (fun x : (i : ι) → ZMod (n i) => fun i _ => x i) ?_ ?_
    · intro x hx
      have hx' : ∀ i, x i ∈ D i := (Finset.mem_filter.mp hx).2
      exact Finset.mem_pi.mpr (fun i _ => hx' i)
    · intro x _ y _ hxy
      funext i
      exact congrFun (congrFun hxy i) (Finset.mem_univ i)
  rw [Finset.card_pi] at hle
  exact hle

theorem walkGoal_abelian_difference_basis_covers {A : Type} [AddCommGroup A] [Fintype A]
    {ι : Type} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, NeZero (n i))
    (D : ∀ i, Finset (ZMod (n i)))
    (e : A ≃+ ((i : ι) → ZMod (n i)))
    (hD : ∀ i, ∀ x : ZMod (n i), ∃ a ∈ D i, ∃ b ∈ D i, b - a = x) :
    AbelianDifferenceBasis (abelianDifferenceBasis n hn D e) := by
  classical
  intro s
  obtain ⟨pa, hpa, pb, hpb, hdiff⟩ := walkGoal_product_basis_covers n hn D hD (e s)
  have hpa' : ∀ i, pa i ∈ D i := by
    simpa only [productDifferenceBasis, Finset.mem_filter, Finset.mem_univ, true_and] using! hpa
  have hpb' : ∀ i, pb i ∈ D i := by
    simpa only [productDifferenceBasis, Finset.mem_filter, Finset.mem_univ, true_and] using! hpb
  refine ⟨e.symm pa, ?_, e.symm pb, ?_, ?_⟩
  · simp only [abelianDifferenceBasis, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [e.apply_symm_apply]
    exact hpa' i
  · simp only [abelianDifferenceBasis, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [e.apply_symm_apply]
    exact hpb' i
  · apply e.injective
    calc e (e.symm pb - e.symm pa) = e (e.symm pb) - e (e.symm pa) := by rw [map_sub]
      _ = pb - pa := by rw [e.apply_symm_apply, e.apply_symm_apply]
      _ = e s := hdiff

theorem walkGoal_abelian_difference_basis_exists (A : Type) [AddCommGroup A] [Fintype A] :
    ∃ (D : Finset A), AbelianDifferenceBasis D := by
  classical
  obtain ⟨ι, hι, n, hn, e⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
  obtain ⟨e'⟩ := e
  have hprod : A ≃+ ((i : ι) → ZMod (n i)) :=
    e'.trans (DirectSum.addEquivProd (fun i => ZMod (n i)))
  have hn' : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  refine ⟨abelianDifferenceBasis n hn' (fun i => zmodBasis (zmodBasisWidth (n i))) hprod, ?_⟩
  refine walkGoal_abelian_difference_basis_covers n hn' (fun i => zmodBasis (zmodBasisWidth (n i)))
    hprod fun i x => ?_
  obtain ⟨hpos, hsq⟩ := clause14_collision_width_spec (n i) (by have := hn i; omega)
  exact walkGoal_zmod_basis_covers (zmodBasisWidth (n i)) hpos hsq x

theorem walkGoal_abelian_collision_determines {A S : Type} [AddCommGroup A]
    (f g : A → S) (s : A) (hf : HiddenShift f g s) (d₁ d₂ : A)
    (hval : f d₁ = g d₂) : d₂ - d₁ = s := by
  have hg : g d₂ = f (d₂ - s) := by
    have h := hf.2.2 (d₂ - s)
    rw [sub_add_cancel d₂ s] at h
    exact h.symm
  have hinj : d₁ = d₂ - s := hf.1 (hval.trans hg)
  rw [sub_eq_iff_eq_add]
  calc d₂ = d₂ - s + s := (sub_add_cancel d₂ s).symm
    _ = d₁ + s := by rw [hinj]
    _ = s + d₁ := (add_comm _ _).symm

private theorem list_find?_eq_some_pred {α : Type} {p : α → Bool} {l : List α} {a : α}
    (h : List.find? p l = some a) : p a = true := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
    by_cases hb : p b = true
    · have h1 : List.find? p (b :: bs) = some b := List.find?_cons_of_pos hb
      rw [h1] at h
      cases h
      exact hb
    · have h2 : List.find? p bs = some a := List.find?_cons_of_neg hb ▸ h
      exact ih h2

private theorem list_find?_isSome_of_witness {α : Type} {p : α → Bool} {l : List α} {a : α}
    (ha : a ∈ l) (hpa : p a = true) : (List.find? p l).isSome := by
  have hne : (List.find? p l) ≠ none := by
    intro hn
    have hall := (List.find?_eq_none.mp hn) a ha
    exact hall hpa
  refine (Option.isSome_iff_exists).2 ?_
  cases hp : List.find? p l with
  | none => exact absurd hp hne
  | some b => exact ⟨b, rfl⟩

private theorem mem_abelianPairs {A : Type} (D : List A) {d₁ d₂ : A}
    (h₁ : d₁ ∈ D) (h₂ : d₂ ∈ D) : (d₁, d₂) ∈ abelianPairs D := by
  simp only [abelianPairs, List.mem_flatMap, List.mem_map]
  exact ⟨d₁, h₁, d₂, h₂, rfl⟩

private theorem abelianShiftPair_spec {A S : Type} [DecidableEq A] [DecidableEq S]
    (f g : A → S) (D : List A) {p q : A} (h : abelianShiftPair f g D = some (p, q)) :
    f p = g q ∧ p ∈ D ∧ q ∈ D := by
  have h' : List.find? (fun t : A × A => decide (f t.1 = g t.2)) (abelianPairs D) = some (p, q) := h
  have hmem : (p, q) ∈ abelianPairs D := List.mem_of_find?_eq_some h'
  have hpred : decide (f p = g q) = true := by
    have h2 := list_find?_eq_some_pred h'
    simpa using! h2
  have hmem' : p ∈ D ∧ q ∈ D := by
    simp only [abelianPairs, List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨d₁, hd₁, d₂, hd₂, hpair⟩ := hmem
    rcases Prod.ext_iff.mp hpair with ⟨rfl, rfl⟩
    exact ⟨hd₁, hd₂⟩
  exact ⟨of_decide_eq_true hpred, hmem'.1, hmem'.2⟩

theorem abelianDifferenceBasis_univ {A : Type} [AddCommGroup A] [Fintype A] :
    AbelianDifferenceBasis (Finset.univ : Finset A) := by
  intro s
  exact ⟨0, Finset.mem_univ _, s, Finset.mem_univ _, sub_zero s⟩

theorem walkGoal_abelian_shift_reported {A S : Type} [AddCommGroup A] [Fintype A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (s : A) (hf : HiddenShift f g s)
    (D : List A) (hD : AbelianDifferenceBasis D.toFinset) :
    abelianShiftCandidate f g D = some s := by
  classical
  obtain ⟨d₁, hd₁, d₂, hd₂, hdiff⟩ := hD s
  have hd₁' : d₁ ∈ D := (List.mem_toFinset.mp hd₁)
  have hd₂' : d₂ ∈ D := (List.mem_toFinset.mp hd₂)
  have hpartner : d₂ = d₁ + s := by
    have h2 : d₂ - d₁ = s := hdiff
    rw [sub_eq_iff_eq_add] at h2
    exact h2.trans (add_comm _ _)
  have hval : f d₁ = g d₂ := by
    have h := hf.2.2 d₁
    rw [← hpartner] at h
    exact h
  have hval' : decide (f d₁ = g d₂) = true := decide_eq_true_eq.mpr hval
  have hne : (abelianShiftPair f g D) ≠ none := by
    intro hn
    have hall := (List.find?_eq_none.mp hn) (d₁, d₂) (mem_abelianPairs D hd₁' hd₂')
    exact hall hval'
  obtain ⟨pq, hpq⟩ : ∃ pq : A × A, abelianShiftPair f g D = some pq := by
    cases hpq' : abelianShiftPair f g D with
    | none => exact absurd hpq' hne
    | some pq => exact ⟨pq, rfl⟩
  obtain ⟨p, q⟩ := pq
  obtain ⟨hcoll, hp, hq⟩ := abelianShiftPair_spec f g D hpq
  have hshift : q - p = s := walkGoal_abelian_collision_determines f g s hf p q hcoll
  unfold abelianShiftCandidate
  rw [hpq]
  exact congrArg some hshift

theorem walkGoal_abelian_shift_recovery {A S : Type} [AddCommGroup A] [Fintype A]
    [DecidableEq A] [DecidableEq S] (f g : A → S) (s : A) (hf : HiddenShift f g s)
    (D : List A) (hD : AbelianDifferenceBasis D.toFinset) :
    (∀ u : A, u ≠ s → abelianBasisShiftRun f g D (some u) = 0) ∧
      ENNReal.ofReal 1 ≤ abelianBasisShiftRun f g D (some s) := by
  classical
  have hreported : abelianShiftCandidate f g D = some s :=
    walkGoal_abelian_shift_reported f g s hf D hD
  constructor
  · intro u hu
    rw [abelianBasisShiftRun, PMF.pure_apply, hreported]
    simp [hu]
  · rw [abelianBasisShiftRun, PMF.pure_apply, hreported]
    simp

theorem walkGoal_abelian_ledger_account {A : Type} (D : List A) (bits : ℕ) :
    (abelianShiftLedger D bits).samples = abelianShiftQueryCount D ∧
      (abelianShiftLedger D bits).queries = abelianShiftQueryCount D ∧
      abelianShiftCompareCount D ≤ (abelianShiftLedger D bits).comparisons ∧
      sortBitOps (abelianShiftLedger D bits).samples (abelianShiftLedger D bits).integerBits
        ≤ (abelianShiftLedger D bits).bitOps ∧
      (abelianShiftLedger D bits).integerBits = bits ∧
      (abelianShiftLedger D bits).workspaceBits = workspaceBits (max (2 * D.length) 1) bits ∧
      0 < (abelianShiftLedger D bits).workspaceBits := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · exact le_max_left _ _
  · simp [abelianShiftLedger, sortBitOps]
  · rw [abelianShiftLedger]
    exact Nat.mul_pos (by omega) (by omega)

theorem walkGoal_difference_basis_card_sq {A : Type} [AddCommGroup A] [Fintype A]
    (D : Finset A) (hD : AbelianDifferenceBasis D) :
    Fintype.card A ≤ D.card ^ 2 := by
  classical
  have hsurj : Function.Surjective (fun p : D × D => (p.2 : A) - (p.1 : A)) := by
    intro s
    obtain ⟨d₁, hd₁, d₂, hd₂, h⟩ := hD s
    refine ⟨(⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩), ?_⟩
    simpa using! h
  have hle := Fintype.card_le_of_surjective (fun p : D × D => (p.2 : A) - (p.1 : A)) hsurj
  simpa [pow_two] using! hle

theorem walkGoal_difference_basis_card_lower (m : ℕ) (D : Finset (ZMod (4 ^ m)))
    (hD : AbelianDifferenceBasis D) : 2 ^ m ≤ D.card := by
  have hcard : Fintype.card (ZMod (4 ^ m)) ≤ D.card ^ 2 :=
    walkGoal_difference_basis_card_sq D hD
  rw [ZMod.card] at hcard
  have h4 : 4 ^ m = (2 ^ m) ^ 2 := by
    have h1 : 4 ^ m = (2 ^ 2) ^ m := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    have h2 : (2 ^ 2) ^ m = 2 ^ (2 * m) := by rw [← pow_mul]
    have h3 : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by
      calc 2 ^ (2 * m) = 2 ^ (m * 2) := by rw [Nat.mul_comm]
        _ = (2 ^ m) ^ 2 := by rw [pow_mul]
    rw [h1, h2, h3]
  have hcard' : (2 ^ m) ^ 2 ≤ D.card ^ 2 := by
    rw [← h4]
    exact hcard
  nlinarith [Nat.zero_le (2 ^ m), Nat.zero_le D.card]

theorem walkGoal_classical_budget_obstruction (C : ℝ) (hC : 0 < C) (m : ℕ)
    (hm : C * Real.sqrt (2 * (m : ℝ) + 1) < (m + 1 : ℝ))
    (D : Finset (ZMod (4 ^ m))) (hD : AbelianDifferenceBasis D) :
    (2 * D.card : ℝ) > 2 ^ (C * Real.sqrt (labelBits (Fintype.card (ZMod (4 ^ m))))) := by
  have hcard : 2 ^ m ≤ D.card := walkGoal_difference_basis_card_lower m D hD
  have hbits : labelBits (Fintype.card (ZMod (4 ^ m))) = 2 * m + 1 := by
    rw [ZMod.card, labelBits]
    have hlog : Nat.log2 (4 ^ m) = 2 * m := by
      have h1 : 4 ^ m = (2 ^ 2) ^ m := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      have h2 : (2 ^ 2) ^ m = 2 ^ (2 * m) := by rw [← pow_mul]
      rw [h1, h2]
      exact Nat.log2_two_pow
    rw [hlog]
  have hle : (2 : ℝ) ^ ((m + 1 : ℕ) : ℝ) ≤ (2 * D.card : ℝ) := by
    rw [Real.rpow_natCast, pow_succ]
    have h1 : (2 : ℝ) ^ m = ((2 ^ m : ℕ) : ℝ) := by norm_cast
    have h2 : ((2 ^ m : ℕ) : ℝ) ≤ (D.card : ℝ) := Nat.cast_le.mpr hcard
    calc (2 : ℝ) ^ m * 2 = ((2 ^ m : ℕ) : ℝ) * 2 := by rw [h1]
      _ ≤ (D.card : ℝ) * 2 := by exact mul_le_mul_of_nonneg_right h2 (by norm_num)
      _ = (2 * D.card : ℝ) := by ring
  have hm' : C * Real.sqrt (2 * (m : ℝ) + 1) < ((m + 1 : ℕ) : ℝ) := by
    push_cast
    exact hm
  have hlt : (2 : ℝ) ^ (C * Real.sqrt (2 * (m : ℝ) + 1))
      < (2 : ℝ) ^ ((m + 1 : ℕ) : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hm'
  rw [hbits]
  have hcast : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  exact lt_of_lt_of_le hlt hle

private theorem radix_pow_lt_pow_lt (r : ℕ) (hr : 1 < r) :
    ∀ a b : ℕ, r ^ a < r ^ b → a < b := by
  intro a
  induction a with
  | zero =>
    intro b h
    by_cases hb : b = 0
    · subst hb; simp at h
    · omega
  | succ a ih =>
    intro b h
    cases b with
    | zero => simp at h; omega
    | succ b =>
      have h' : r ^ a * r < r ^ b * r := by simpa [pow_succ] using! h
      have h'' : r ^ a < r ^ b := (Nat.mul_lt_mul_right (by omega : (0:ℕ) < r)).mp h'
      have := ih b h''
      omega

private theorem radix_sqrt_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 := Real.sq_sqrt hx
    rw [h] at h1
    norm_num at h1
    exact h1.symm
  · intro h
    rw [h, Real.sqrt_zero]

private theorem radix_dvd_mod_of_dvd {d x N : ℕ} (h1 : d ∣ x) (h2 : d ∣ N) :
    d ∣ x % N := by
  have h3 : d ∣ N * (x / N) := by
    have hmod : N % d = 0 := (Nat.dvd_iff_mod_eq_zero).mp h2
    have heq : N = d * (N / d) := by
      have := Nat.mod_add_div N d
      omega
    rw [heq]
    simpa [mul_assoc] using! Nat.dvd_mul_right d ((N / d) * (x / N))
  have h4 : x % N = x - N * (x / N) := by
    have := Nat.mod_add_div x N
    omega
  rw [h4]
  exact Nat.dvd_sub h1 h3

private theorem radix_mod_eq_zero_of_lt (x N : ℕ) (h0 : 0 < x) (hlt : x < 2 * N)
    (hdvd : N ∣ x) : x = N := by
  have hmod : x % N = 0 := (Nat.dvd_iff_mod_eq_zero).mp hdvd
  have hNpos : 0 < N := by
    by_contra hc
    have : N = 0 := Nat.eq_zero_of_not_pos hc
    subst this
    omega
  have hxN : N ≤ x := by
    by_contra hc
    have hxlt : x < N := Nat.lt_of_not_ge hc
    have : x % N = x := Nat.mod_eq_of_lt hxlt
    omega
  have hsub : x - N < N := by
    have : x < N + N := by omega
    omega
  have heq : x % N = x - N := by
    rw [Nat.mod_eq_sub_mod hxN, Nat.mod_eq_of_lt hsub]
  omega

private theorem radix_sub_child_pos (k ℓ N : ℕ) (hk : k < N) (hℓ : ℓ < N)
    (hne : k ≠ ℓ) : 0 < (k + N - ℓ) % N := by
  by_contra hc
  have hz : (k + N - ℓ) % N = 0 := Nat.eq_zero_of_not_pos hc
  have hdvd : N ∣ k + N - ℓ := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hz
  have h0 : 0 < k + N - ℓ := by
    have : 0 < N - ℓ := by omega
    omega
  have hlt : k + N - ℓ < 2 * N := by
    have h1 : k + N < N + N := by omega
    have h2 : N - ℓ ≤ N := by omega
    omega
  have heq : k + N - ℓ = N := radix_mod_eq_zero_of_lt (k + N - ℓ) N h0 hlt hdvd
  omega

private theorem radix_add_child_pos (k ℓ N : ℕ) (hk : k < N) (hℓ : ℓ < N)
    (hne : k ≠ ℓ) (hsum : k + ℓ ≠ N) : 0 < (k + ℓ) % N := by
  by_contra hc
  have hz : (k + ℓ) % N = 0 := Nat.eq_zero_of_not_pos hc
  have hdvd : N ∣ k + ℓ := by
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hz
  have h0 : 0 < k + ℓ := by
    by_cases h1 : k = 0
    · subst h1
      have h2 : ℓ ≠ 0 := by omega
      omega
    · omega
  have hlt : k + ℓ < 2 * N := by
    have h1 : k < N := hk
    have h2 : ℓ < N := hℓ
    omega
  have heq : k + ℓ = N := radix_mod_eq_zero_of_lt (k + ℓ) N h0 hlt hdvd
  omega

private theorem radix_pow_dvd_pow (r a n : ℕ) (hr : 1 < r) (h : a ≤ n) :
    r ^ a ∣ r ^ n := by
  have hle : n = a + (n - a) := (Nat.add_sub_of_le h).symm
  rw [hle, pow_add]
  exact Nat.dvd_mul_right _ _

theorem radixAlpha_le (r n k : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n) :
    radixAlpha r k ≤ n - 1 := by
  by_cases hzero : k = 0
  · subst k
    simp [radixAlpha]
  · have hdiv : r ^ radixAlpha r k ∣ k := radixAlpha_dvd r k hr (Nat.pos_of_ne_zero hzero)
    have hle : r ^ radixAlpha r k ≤ k :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hzero) hdiv
    have hlt : r ^ radixAlpha r k < r ^ n := lt_of_le_of_lt hle hk
    have hlt' : radixAlpha r k < n := radix_pow_lt_pow_lt r (by omega) _ _ hlt
    omega

theorem radixBeta_nonneg (r n k : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n) :
    0 ≤ radixBeta r n k := by
  unfold radixBeta
  have h := radixAlpha_le r n k hr hn hk
  omega

theorem radixValue_pos (r n k : ℕ) : 0 < radixValue r n k := by
  unfold radixValue
  exact Real.exp_pos _

theorem radixValue_le_one (r n k : ℕ) : radixValue r n k ≤ 1 := by
  unfold radixValue
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hx : -(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)) ≤ 0 := by
    have hprod : 0 ≤ (Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)) :=
      mul_nonneg (le_of_lt hlog) (Real.sqrt_nonneg _)
    linarith
  have h2 := Real.exp_le_exp.mpr hx
  rw [Real.exp_zero] at h2
  exact h2

theorem radixValue_eq_one_iff (r n k : ℕ) :
    radixValue r n k = 1 ↔ radixBeta r n k = 0 := by
  unfold radixValue
  have hlog : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · intro h
    have hexp : -(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)) = 0 :=
      (Real.exp_eq_one_iff _).mp h
    rcases mul_eq_zero.mp hexp with hzero | hzero
    · exact absurd hzero (by simp [hlog])
    · have hsqrt : Real.sqrt (2 * (radixBeta r n k : ℝ)) = 0 := by
        simpa using! hzero
      have hx : 2 * (radixBeta r n k : ℝ) = 0 := (radix_sqrt_eq_zero_iff (by positivity)).mp hsqrt
      have hx' : (radixBeta r n k : ℝ) = 0 := by linarith
      exact_mod_cast hx'
  · intro h
    have hx : 2 * (radixBeta r n k : ℝ) = 0 := by
      rw [h]
      norm_num
    have hsqrt : Real.sqrt (2 * (radixBeta r n k : ℝ)) = 0 :=
      (radix_sqrt_eq_zero_iff (by positivity)).mpr hx
    have hexp : -(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)) = 0 := by
      simp [hsqrt]
    exact (Real.exp_eq_one_iff _).mpr hexp

theorem radixValue_ge_of_beta_le (r n k c : ℕ) (h : radixBeta r n k ≤ c) :
    Real.exp (-(Real.log 3) * Real.sqrt (2 * (c : ℝ))) ≤ radixValue r n k := by
  unfold radixValue
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcast : (radixBeta r n k : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
  have hsq : Real.sqrt (2 * (radixBeta r n k : ℝ)) ≤ Real.sqrt (2 * (c : ℝ)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hmul : -(Real.log 3) * Real.sqrt (2 * (c : ℝ))
      ≤ -(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ)) := by
    have := mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hlog.le)
    simpa using! this
  exact Real.exp_le_exp.mpr hmul

theorem radixValue_ge_of_alpha_ge (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (h : radixAlpha r ℓ ≤ radixAlpha r k) :
    radixValue r n ℓ ≤ radixValue r n k := by
  apply radixValue_ge_of_beta_le
  have hαk := radixAlpha_le r n k hr hn hk
  have hαℓ := radixAlpha_le r n ℓ hr hn hℓ
  unfold radixBeta
  omega

theorem radixAlpha_ge_of_dvd (r k a : ℕ) (hr : 2 ≤ r) (hk : 0 < k) (h : r ^ a ∣ k) :
    a ≤ radixAlpha r k := by
  by_cases ha0 : a = 0
  · simp [ha0]
  · have hge : a < r ^ a := by
      have h2 : 2 ^ a ≤ r ^ a := Nat.pow_le_pow_left hr a
      have h3 : a + 1 ≤ 2 ^ a := pow_two_ge_succ a
      omega
    have hle : a ≤ k := by
      have hdiv : r ^ a ≤ k := Nat.le_of_dvd hk h
      omega
    have hkey := (radixAlpha_eq_iff r k (radixAlpha r k) hr hk).mp rfl
    by_contra hcon
    have hlt : radixAlpha r k < a := Nat.lt_of_not_ge hcon
    exact hkey.2 a hlt hle h

theorem radixChild_alpha_ge_sub (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = radixAlpha r ℓ) :
    radixAlpha r k ≤ radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) := by
  by_cases hk0 : k = 0
  · subst k
    have hz : radixAlpha r 0 = 0 := by simp [radixAlpha]
    rw [hz]
    exact Nat.zero_le _
  by_cases hℓ0 : ℓ = 0
  · subst ℓ
    have hz : radixAlpha r 0 = 0 := by simp [radixAlpha]
    rw [hα, hz]
    exact Nat.zero_le _
  have hdk : r ^ radixAlpha r k ∣ k := radixAlpha_dvd r k hr (Nat.pos_of_ne_zero hk0)
  have hdℓ : r ^ radixAlpha r ℓ ∣ ℓ := radixAlpha_dvd r ℓ hr (Nat.pos_of_ne_zero hℓ0)
  have hαk : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
  have hαn : radixAlpha r ℓ ≤ n := by
    rw [← hα]
    omega
  have hrN : r ^ radixAlpha r ℓ ∣ r ^ n := radix_pow_dvd_pow r _ _ (by omega) hαn
  have h1 : r ^ radixAlpha r ℓ ∣ r ^ n - ℓ := Nat.dvd_sub hrN hdℓ
  have hsum : k + (r ^ n) - ℓ = k + (r ^ n - ℓ) := by
    have hle : ℓ ≤ r ^ n := by omega
    omega
  have hsub : r ^ radixAlpha r ℓ ∣ k + (r ^ n) - ℓ := by
    rw [hα] at hdk
    rw [hsum]
    exact Nat.dvd_add hdk h1
  have hrem : r ^ radixAlpha r ℓ ∣ (k + (r ^ n) - ℓ) % (r ^ n) :=
    radix_dvd_mod_of_dvd hsub hrN
  have hpos : 0 < (k + (r ^ n) - ℓ) % (r ^ n) :=
    radix_sub_child_pos k ℓ (r ^ n) hk hℓ hne
  exact radixAlpha_ge_of_dvd r _ _ hr hpos (by rw [hα]; exact hrem)

theorem radixChild_alpha_ge_add (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = radixAlpha r ℓ) (hsum : k + ℓ ≠ r ^ n) :
    radixAlpha r k ≤ radixAlpha r ((k + ℓ) % (r ^ n)) := by
  by_cases hk0 : k = 0
  · subst k
    have hz : radixAlpha r 0 = 0 := by simp [radixAlpha]
    rw [hz]
    exact Nat.zero_le _
  by_cases hℓ0 : ℓ = 0
  · subst ℓ
    have hz : radixAlpha r 0 = 0 := by simp [radixAlpha]
    rw [hα, hz]
    exact Nat.zero_le _
  have hdk : r ^ radixAlpha r k ∣ k := radixAlpha_dvd r k hr (Nat.pos_of_ne_zero hk0)
  have hdℓ : r ^ radixAlpha r ℓ ∣ ℓ := radixAlpha_dvd r ℓ hr (Nat.pos_of_ne_zero hℓ0)
  have hαk : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
  have hαn : radixAlpha r ℓ ≤ n := by
    rw [← hα]
    omega
  have hrN : r ^ radixAlpha r ℓ ∣ r ^ n := radix_pow_dvd_pow r _ _ (by omega) hαn
  have hsum' : r ^ radixAlpha r ℓ ∣ k + ℓ := by
    rw [hα] at hdk
    exact Nat.dvd_add hdk hdℓ
  have hrem : r ^ radixAlpha r ℓ ∣ (k + ℓ) % (r ^ n) := radix_dvd_mod_of_dvd hsum' hrN
  have hpos : 0 < (k + ℓ) % (r ^ n) :=
    radix_add_child_pos k ℓ (r ^ n) hk hℓ hne hsum
  exact radixAlpha_ge_of_dvd r _ _ hr hpos (by rw [hα]; exact hrem)

theorem radixSharedTrits_spec (r k ℓ : ℕ) (hradix : r ^ radixAlpha r k ∣ radixDiff k ℓ) :
    radixTritsShare r (radixAlpha r k) k ℓ (radixSharedTrits r k ℓ) ∧
      (∀ j, radixSharedTrits r k ℓ < j → j ≤ radixDiff k ℓ →
        ¬ radixTritsShare r (radixAlpha r k) k ℓ j) := by
  have hP0 : radixTritsShare r (radixAlpha r k) k ℓ 0 := by
    simpa [radixTritsShare] using! hradix
  obtain ⟨hle, hspec, hmax⟩ :=
    (Nat.findGreatest_eq_iff (P := fun j => radixTritsShare r (radixAlpha r k) k ℓ j)
      (k := radixDiff k ℓ) (m := radixSharedTrits r k ℓ)).mp rfl
  refine ⟨?_, ?_⟩
  · by_cases hm : radixSharedTrits r k ℓ = 0
    · simpa [hm] using! hP0
    · exact hspec hm
  · intro j hj hjl
    exact hmax hj hjl

theorem radixSharedTrits_le_beta (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hradix : r ^ radixAlpha r k ∣ radixDiff k ℓ) :
    radixSharedTrits r k ℓ ≤ radixBeta r n k := by
  obtain ⟨hshare, _⟩ := radixSharedTrits_spec r k ℓ hradix
  have hdiff : 0 < radixDiff k ℓ := by
    by_cases h : k ≥ ℓ
    · rw [radixDiff, if_pos h]
      omega
    · rw [radixDiff, if_neg h]
      omega
  have hdifflt : radixDiff k ℓ < r ^ n := by
    by_cases h : k ≥ ℓ
    · rw [radixDiff, if_pos h]
      omega
    · rw [radixDiff, if_neg h]
      omega
  have hle : r ^ (radixAlpha r k + radixSharedTrits r k ℓ) ≤ radixDiff k ℓ :=
    Nat.le_of_dvd hdiff hshare
  have hlt : r ^ (radixAlpha r k + radixSharedTrits r k ℓ) < r ^ n :=
    lt_of_le_of_lt hle hdifflt
  have hlt' : radixAlpha r k + radixSharedTrits r k ℓ < n :=
    radix_pow_lt_pow_lt r (by omega) _ _ hlt
  have hα : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
  have hαn : radixAlpha r k ≤ n := by omega
  have hsum : radixAlpha r k + radixSharedTrits r k ℓ + 1 ≤ n := by omega
  have hsub : n - radixAlpha r k = (n - 1 - radixAlpha r k) + 1 := by omega
  unfold radixBeta
  omega

private theorem radix_sqrt_gap (β m : ℝ) (hβ : 1 ≤ β) (hm : 0 ≤ m) (hmβ : m ≤ β)
    (h : Real.sqrt (2 * β) - 1 / 2 < m) :
    Real.sqrt (2 * β) - Real.sqrt (2 * (β - m)) > 1 := by
  set u : ℝ := Real.sqrt (2 * β) with hu
  set v : ℝ := Real.sqrt (2 * (β - m)) with hv
  have hu2 : u ^ 2 = 2 * β := by
    rw [hu]; exact Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = 2 * (β - m) := by
    rw [hv]; exact Real.sq_sqrt (by positivity)
  have hu1 : 1 ≤ u := by
    rw [hu]
    have hlt : Real.sqrt 1 ≤ Real.sqrt (2 * β) := Real.sqrt_le_sqrt (by linarith)
    simpa using! hlt
  have hv0 : 0 ≤ v := by rw [hv]; exact Real.sqrt_nonneg _
  by_contra hcon
  have hle : u - 1 ≤ v := by linarith [hcon]
  have hkey : v ^ 2 ≥ (u - 1) ^ 2 := by
    have hh1 : 0 ≤ v - (u - 1) := by linarith
    have hh2 : 0 ≤ v + (u - 1) := by linarith
    nlinarith [mul_nonneg hh1 hh2]
  have hsq : (u - 1) ^ 2 = u ^ 2 - 2 * u + 1 := by ring
  have hkey' : 2 * (β - m) ≥ u ^ 2 - 2 * u + 1 := by
    rw [hv2, hsq] at hkey
    exact hkey
  have hmain : 2 * m ≤ 2 * u - 1 := by
    have hkey'' : 2 * β - 2 * m ≥ u ^ 2 - 2 * u + 1 := by linarith [hkey']
    rw [hu2] at hkey''
    linarith
  rw [hu] at hmain
  linarith [h]

private theorem radixAlpha_dvd' (r k : ℕ) (hr : 2 ≤ r) : r ^ radixAlpha r k ∣ k := by
  by_cases hzero : k = 0
  · subst k
    simp [radixAlpha]
  · exact radixAlpha_dvd r k hr (Nat.pos_of_ne_zero hzero)

theorem radixChild_alpha_gain (r n k ℓ m : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = radixAlpha r ℓ)
    (ham : radixAlpha r k + m ≤ n - 1)
    (hm : r ^ (radixAlpha r k + m) ∣ radixDiff k ℓ) :
    radixAlpha r k + m ≤ radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) := by
  have hdk : r ^ radixAlpha r k ∣ k := radixAlpha_dvd' r k hr
  have hdℓ : r ^ radixAlpha r ℓ ∣ ℓ := radixAlpha_dvd' r ℓ hr
  have ham' : radixAlpha r k + m ≤ n := by omega
  have hrN : r ^ (radixAlpha r k + m) ∣ r ^ n := radix_pow_dvd_pow r _ _ (by omega) ham'
  have hsub : r ^ (radixAlpha r k + m) ∣ k + (r ^ n) - ℓ := by
    by_cases hge : k ≥ ℓ
    · have hsub' : k + (r ^ n) - ℓ = (k - ℓ) + (r ^ n) := by omega
      rw [hsub']
      have hdiff : r ^ (radixAlpha r k + m) ∣ k - ℓ := by
        rw [radixDiff, if_pos hge] at hm
        exact hm
      exact Nat.dvd_add hdiff hrN
    · have hsub' : k + (r ^ n) - ℓ = (r ^ n) - (ℓ - k) := by
        have hle : ℓ ≤ r ^ n := by omega
        omega
      rw [hsub']
      have hdiff : r ^ (radixAlpha r k + m) ∣ ℓ - k := by
        rw [radixDiff, if_neg hge] at hm
        exact hm
      exact Nat.dvd_sub hrN hdiff
  have hrem : r ^ (radixAlpha r k + m) ∣ (k + (r ^ n) - ℓ) % (r ^ n) :=
    radix_dvd_mod_of_dvd hsub hrN
  have hpos : 0 < (k + (r ^ n) - ℓ) % (r ^ n) :=
    radix_sub_child_pos k ℓ (r ^ n) hk hℓ hne
  exact radixAlpha_ge_of_dvd r _ _ hr hpos hrem

theorem radixExpectedChildValue_lower (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = radixAlpha r ℓ) (hsum : k + ℓ ≠ r ^ n)
    (hradix : r ^ radixAlpha r k ∣ radixDiff k ℓ) :
    radixExpectedChildValue r n k ℓ ≥
      (radixValue r n k
        + Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ))))
        / 2 := by
  have hshared := radixSharedTrits_le_beta r n k ℓ hr hn hk hℓ hne hradix
  obtain ⟨hshare, _⟩ := radixSharedTrits_spec r k ℓ hradix
  have ham : radixAlpha r k + radixSharedTrits r k ℓ ≤ n - 1 := by
    have hα : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
    have hβ : radixBeta r n k = n - 1 - radixAlpha r k := by
      unfold radixBeta
      omega
    rw [hβ] at hshared
    omega
  have hgain := radixChild_alpha_gain r n k ℓ (radixSharedTrits r k ℓ) hr hn hk hℓ hne
    hα ham hshare
  have hαsub : radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) ≤ n - 1 := by
    have h := radixAlpha_le r n _ hr hn (by
      have := radix_sub_child_pos k ℓ (r ^ n) hk hℓ hne
      have : (k + (r ^ n) - ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by
        have : 0 < r ^ n := by positivity
        omega)
      omega)
    exact h

  have hβsub : radixBeta r n ((k + (r ^ n) - ℓ) % (r ^ n))
      ≤ radixBeta r n k - radixSharedTrits r k ℓ := by
    have hα : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
    have hαchild : radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) ≤ n - 1 := hαsub
    have hgainle : radixAlpha r k + radixSharedTrits r k ℓ
        ≤ radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) := hgain
    have hmn : radixSharedTrits r k ℓ ≤ n - 1 - radixAlpha r k := by omega
    unfold radixBeta
    omega
  have hvsub : Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)))
      ≤ radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n)) :=
    radixValue_ge_of_beta_le r n _ _ hβsub

  have hαadd : radixAlpha r ((k + ℓ) % (r ^ n)) ≤ n - 1 := by
    have h := radixAlpha_le r n _ hr hn (by
      have := radix_add_child_pos k ℓ (r ^ n) hk hℓ hne hsum
      have : (k + ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by
        have : 0 < r ^ n := by positivity
        omega)
      omega)
    exact h
  have hβadd : radixBeta r n ((k + ℓ) % (r ^ n)) ≤ radixBeta r n k := by
    unfold radixBeta
    have h := radixChild_alpha_ge_add r n k ℓ hr hn hk hℓ hne hα hsum
    omega
  have hvadd : radixValue r n k ≤ radixValue r n ((k + ℓ) % (r ^ n)) :=
    radixValue_ge_of_beta_le r n _ _ hβadd
  have hval : radixValue r n k
      = Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k : ℕ) : ℝ))) := rfl
  unfold radixExpectedChildValue
  have hsum' : (radixValue r n ((k + ℓ) % (r ^ n))
      + radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n)))
      ≥ (radixValue r n k
        + Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)))) :=
    add_le_add hvadd hvsub
  have hhalf : (radixValue r n ((k + ℓ) % (r ^ n))
      + radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))) / 2
      ≥ (radixValue r n k
        + Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)))) / 2 := by
    linarith
  exact hhalf

theorem radixExpectedChildValue_gt (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = radixAlpha r ℓ) (hsum : k + ℓ ≠ r ^ n)
    (hradix : r ^ radixAlpha r k ∣ radixDiff k ℓ)
    (hm : Real.sqrt (2 * (radixBeta r n k : ℝ)) < radixSharedTrits r k ℓ) :
    radixExpectedChildValue r n k ℓ > 2 * radixValue r n k := by
  have hshared := radixSharedTrits_le_beta r n k ℓ hr hn hk hℓ hne hradix
  have hβm : (radixSharedTrits r k ℓ : ℝ) ≤ (radixBeta r n k : ℝ) := by
    exact_mod_cast hshared
  have hm1 : 1 ≤ radixSharedTrits r k ℓ := by
    have hsqrt : 0 ≤ Real.sqrt (2 * (radixBeta r n k : ℝ)) := Real.sqrt_nonneg _
    have h1 : (0:ℝ) < (radixSharedTrits r k ℓ : ℝ) := by linarith
    have h2 : 0 < radixSharedTrits r k ℓ := by exact_mod_cast h1
    omega
  have hβ1 : (1 : ℝ) ≤ (radixBeta r n k : ℝ) := by
    have hle : radixSharedTrits r k ℓ ≤ radixBeta r n k := hshared
    have : 1 ≤ radixBeta r n k := by omega
    exact_mod_cast this
  have hgap : Real.sqrt (2 * (radixBeta r n k : ℝ))
      - Real.sqrt (2 * ((radixBeta r n k : ℝ) - (radixSharedTrits r k ℓ : ℝ))) > 1 := by
    have h1 : Real.sqrt (2 * (radixBeta r n k : ℝ)) - 1 / 2
        < (radixSharedTrits r k ℓ : ℝ) := by linarith
    have h2 : (0:ℝ) ≤ (radixSharedTrits r k ℓ : ℝ) := by positivity
    have h3 : (radixSharedTrits r k ℓ : ℝ) ≤ (radixBeta r n k : ℝ) := hβm
    exact radix_sqrt_gap (radixBeta r n k : ℝ) (radixSharedTrits r k ℓ : ℝ) hβ1 h2 h3 h1
  have hlower := radixExpectedChildValue_lower r n k ℓ hr hn hk hℓ hne hα hsum hradix
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcast : ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)
      = (radixBeta r n k : ℝ) - (radixSharedTrits r k ℓ : ℝ) := by
    have hle : radixSharedTrits r k ℓ ≤ radixBeta r n k := hshared
    rw [Nat.cast_sub hle]
  have hW : Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)))
      > 3 * radixValue r n k := by
    have hgap' : Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ))
        = Real.sqrt (2 * ((radixBeta r n k : ℝ) - (radixSharedTrits r k ℓ : ℝ))) := by
      rw [hcast]
    have hkey : -(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ))
        > Real.log 3 * 1 - Real.log 3 * Real.sqrt (2 * (radixBeta r n k : ℝ)) := by
      rw [hgap']
      nlinarith [hgap, hlog]
    have hexp := Real.exp_lt_exp.mpr hkey
    have h3 : Real.exp (Real.log 3) = (3:ℝ) := by
      rw [Real.exp_log (by norm_num : (0:ℝ) < 3)]
    have heq : Real.exp (Real.log 3 * 1 - Real.log 3 * Real.sqrt (2 * (radixBeta r n k : ℝ)))
        = Real.exp (Real.log 3) * Real.exp (-(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp' : Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)))
        > Real.exp (Real.log 3) * Real.exp (-(Real.log 3) * Real.sqrt (2 * (radixBeta r n k : ℝ))) := by
      rw [← heq]
      exact hexp
    have hval : radixValue r n k
        = Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k : ℕ) : ℝ))) := rfl
    rw [h3, ← hval] at hexp'
    exact hexp'
  have hhalf : (radixValue r n k
      + Real.exp (-(Real.log 3) * Real.sqrt (2 * ((radixBeta r n k - radixSharedTrits r k ℓ : ℕ) : ℝ)))) / 2
      > 2 * radixValue r n k := by
    linarith
  linarith

theorem radixFinalValue (r n k : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n)
    (hk0 : k ≠ 0) :
    radixValue r n k = 1 ↔ radixFinalTest r n k := by
  rw [radixValue_eq_one_iff]
  have hαk : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  constructor
  · intro h
    have hα : radixAlpha r k = n - 1 := by
      unfold radixBeta at h
      omega
    refine ⟨?_, hk0⟩
    have hdiv := (radixAlpha_eq_iff r k (radixAlpha r k) hr hkpos).mp rfl
    rw [hα] at hdiv
    exact hdiv.1
  · intro h
    have hge : n - 1 ≤ radixAlpha r k := radixAlpha_ge_of_dvd r k (n - 1) hr hkpos h.1
    have hα : radixAlpha r k = n - 1 := by omega
    unfold radixBeta
    omega

theorem radixListValue_ge (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (L : List ℕ)
    (hL : ∀ k ∈ L, k < r ^ n) :
    (L.length : ℝ) * Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))
      ≤ radixListValue r n L := by
  induction L with
  | nil => simp [radixListValue]
  | cons k L ih =>
    have hk : k < r ^ n := hL k (by simp)
    have hα : radixAlpha r k ≤ n - 1 := radixAlpha_le r n k hr hn hk
    have hβ : radixBeta r n k ≤ n - 1 := by
      unfold radixBeta
      omega
    have hv : Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))
        ≤ radixValue r n k := radixValue_ge_of_beta_le r n k (n - 1) hβ
    have hrest : (L.length : ℝ) * Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))
        ≤ radixListValue r n L := by
      apply ih
      intro j hj
      exact hL j (by simp [hj])
    have hsum' : radixListValue r n (k :: L) = radixValue r n k + radixListValue r n L := by
      simp only [radixListValue, List.map_cons, List.sum_cons]
    have hlen : ((k :: L).length : ℝ) = (L.length : ℝ) + 1 := by
      simp only [List.length_cons]
      push_cast
      ring
    have hdist : ((L.length : ℝ) + 1) * Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))
        = (L.length : ℝ) * Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))
          + Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ))) := by ring
    rw [hsum', hlen, hdist]
    linarith

noncomputable def radixFreshRecords (n : ℕ) : ℕ :=
  ⌊(n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))⌋₊ + 1

noncomputable def radixBudgetLedger (r n : ℕ) : RecoveryLedger where
  samples := radixFreshRecords n
  queries := radixFreshRecords n
  macros := 2 * radixFreshRecords n
  measurements := 2 * radixFreshRecords n
  comparisons := sortCompareSteps (radixFreshRecords n)
  bitOps := sortBitOps (radixFreshRecords n) (labelBits (r ^ n))
  integerBits := labelBits (r ^ n)
  workspaceBits := workspaceBits (radixFreshRecords n) (labelBits (r ^ n))

theorem radixBudgetLedger_samples_le_queries (r n : ℕ) :
    (radixBudgetLedger r n).samples ≤ (radixBudgetLedger r n).queries := by
  rfl

theorem radixBudgetLedger_comparisons (r n : ℕ) :
    sortCompareSteps (radixBudgetLedger r n).samples ≤ (radixBudgetLedger r n).comparisons := by
  rfl

theorem radixBudgetLedger_bitOps (r n : ℕ) :
    sortBitOps (radixBudgetLedger r n).samples (radixBudgetLedger r n).integerBits
      ≤ (radixBudgetLedger r n).bitOps := by
  rfl

theorem radixBudgetLedger_workspace (r n : ℕ) (hn : 1 ≤ n) :
    0 < (radixBudgetLedger r n).workspaceBits := by
  have h1 : 0 < radixFreshRecords n := by
    unfold radixFreshRecords
    omega
  have h2 : 0 < labelBits (r ^ n) := by
    unfold labelBits
    omega
  simp [radixBudgetLedger, workspaceBits]
  omega

theorem radixBudgetLedger_queries_le (r n : ℕ) (hn : 1 ≤ n) :
    ((radixBudgetLedger r n).queries : ℝ) ≤ 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) := by
  set x : ℝ := (n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))) with hx
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := by
    have h := Nat.floor_le (by positivity : (0:ℝ) ≤ x)
    exact_mod_cast h
  have hthree : Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))) = 3 ^ Real.sqrt (2 * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
  have h1 : (1:ℝ) ≤ Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))) := by
    have hsqrt : 0 ≤ Real.sqrt (2 * (n : ℝ)) := Real.sqrt_nonneg _
    have hlog : 0 ≤ Real.log 3 := le_of_lt (Real.log_pos (by norm_num))
    have hmul : 0 ≤ (Real.log 3) * Real.sqrt (2 * (n : ℝ)) := mul_nonneg hlog hsqrt
    have hexp : Real.exp 0 ≤ Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))) :=
      Real.exp_le_exp.mpr hmul
    have hone : Real.exp 0 = 1 := by norm_num
    rw [hone] at hexp
    exact hexp
  have hle : x + 1 ≤ 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) := by
    rw [← hthree]
    rw [hx]
    linarith
  have hq : ((radixBudgetLedger r n).queries : ℝ) = (⌊x⌋₊ : ℝ) + 1 := by
    simp [radixBudgetLedger, radixFreshRecords, hx]
  rw [hq]
  linarith

private theorem radix_mod_mul_of_dvd {d k M : ℕ} (hd : d ∣ k) :
    k % (d * M) = d * ((k / d) % M) := by
  have hkEq : (k / d) * d = k := Nat.div_mul_cancel hd
  calc k % (d * M) = ((k / d) * d) % (d * M) := by rw [hkEq]
    _ = ((k / d) * d) % (M * d) := by rw [Nat.mul_comm d M]
    _ = ((k / d) % M) * d := Nat.mul_mod_mul_right d (k / d) M
    _ = d * ((k / d) % M) := Nat.mul_comm _ _

private theorem radix_digit_data (r a k m : ℕ) (hr : 2 ≤ r) :
    ∃ d w : ℕ, radixFirstDigit r a k m = d ∧ radixUpperDigits r a k m = w ∧
      radixQuotient r a k m = d + r * w ∧ d < r ∧ w < r ^ m := by
  refine ⟨radixQuotient r a k m % r, radixQuotient r a k m / r, ?_⟩
  refine ⟨rfl, rfl, (Nat.mod_add_div (radixQuotient r a k m) r).symm, ?_, ?_⟩
  · exact Nat.mod_lt _ (by omega : 0 < r)
  · have hu : radixQuotient r a k m < r ^ (m + 1) :=
      Nat.mod_lt _ (Nat.pow_pos (by omega : 0 < r))
    have hu2 : radixQuotient r a k m < r * r ^ m := by
      have h2 := hu
      rwa [pow_succ, ← Nat.mul_comm r (r ^ m)] at h2
    exact Nat.div_lt_of_lt_mul hu2

private theorem radix_pattern_core {r m : ℕ} (hr : 2 ≤ r)
    (u v d w d' w' : ℕ)
    (hu : u = d + r * w) (hv : v = d' + r * w')
    (hd : d < r) (hd1 : 1 ≤ d) (hd' : d' < r) (hd1' : 1 ≤ d')
    (hw : w < r ^ m) (hw' : w' < r ^ m)
    (hpat : (if d ≤ r - d then (d - 1, w) else (r - d - 1, r ^ m - 1 - w))
      = (if d' ≤ r - d' then (d' - 1, w') else (r - d' - 1, r ^ m - 1 - w'))) :
    u = v ∨ u + v = r ^ (m + 1) := by
  by_cases h1 : d ≤ r - d
  · by_cases h2 : d' ≤ r - d'
    · simp only [h1, h2, if_true] at hpat
      have hd'' : d = d' := by
        have h := congrArg Prod.fst hpat
        simp at h
        omega
      have hw'' : w = w' := by simpa using! congrArg Prod.snd hpat
      left
      rw [hu, hv, hd'', hw'']
    · simp only [h1, h2, if_false] at hpat
      have hd'' : d - 1 = r - d' - 1 := by simpa using! congrArg Prod.fst hpat
      have hw'' : w = r ^ m - 1 - w' := by simpa using! congrArg Prod.snd hpat
      have hds : d + d' = r := by omega
      have hws : w + w' + 1 = r ^ m := by omega
      right
      rw [hu, hv]
      calc (d + r * w) + (d' + r * w') = (d + d') + r * (w + w') := by ring
        _ = r + r * (w + w') := by rw [hds]
        _ = r * (w + w' + 1) := by ring
        _ = r * r ^ m := by rw [hws]
        _ = r ^ (m + 1) := by rw [pow_succ]; ring
  · by_cases h2 : d' ≤ r - d'
    · simp only [h1, h2, if_false] at hpat
      have hd'' : r - d - 1 = d' - 1 := by simpa using! congrArg Prod.fst hpat
      have hw'' : r ^ m - 1 - w = w' := by simpa using! congrArg Prod.snd hpat
      have hds : d + d' = r := by omega
      have hws : w + w' + 1 = r ^ m := by omega
      right
      rw [hu, hv]
      calc (d + r * w) + (d' + r * w') = (d + d') + r * (w + w') := by ring
        _ = r + r * (w + w') := by rw [hds]
        _ = r * (w + w' + 1) := by ring
        _ = r * r ^ m := by rw [hws]
        _ = r ^ (m + 1) := by rw [pow_succ]; ring
    · simp only [h1, h2, if_false] at hpat
      have hd'' : r - d - 1 = r - d' - 1 := by simpa using! congrArg Prod.fst hpat
      have hw'' : r ^ m - 1 - w = r ^ m - 1 - w' := by simpa using! congrArg Prod.snd hpat
      have hd''' : d = d' := by
        have h := congrArg Prod.fst hpat
        simp at h
        omega
      have hw''' : w = w' := by
        have h := congrArg Prod.snd hpat
        simp at h
        omega
      left
      rw [hu, hv, hd''', hw''']

private theorem radix_dvd_sub_of_mod_eq {A B M : ℕ} (hM : 0 < M)
    (h : A % M = B % M) (hle : B ≤ A) : M ∣ A - B := by
  have hmod : B ≡ A [MOD M] := by
    show B % M = A % M
    rw [h]
  exact (Nat.modEq_iff_dvd' hle).mp hmod

private theorem radix_dvd_add_of_mod_sum {A B M : ℕ} (hM : 0 < M)
    (h : A % M + B % M = M) : M ∣ A + B := by
  have hmod : (A + B) % M = 0 := by
    rw [Nat.add_mod, h, Nat.mod_self]
  exact Nat.dvd_iff_mod_eq_zero.mpr hmod

private theorem radixFirstDigit_pos {r a k m : ℕ} (hr : 2 ≤ r)
    (hk : r ^ a ∣ k) (hk1 : ¬ (r ^ (a + 1) ∣ k)) :
    1 ≤ radixFirstDigit r a k m := by
  have hmod : radixQuotient r a k m % r = (k / r ^ a) % r := by
    rw [radixQuotient]
    exact Nat.mod_mod_of_dvd (k / r ^ a)
      (by rw [pow_succ]; exact Nat.dvd_mul_left r (r ^ m))
  have hquot : ¬ (r ∣ (k / r ^ a)) := by
    intro hh
    have hmul0 : r ^ a * r ∣ r ^ a * (k / r ^ a) := Nat.mul_dvd_mul_left (r ^ a) hh
    have hmul : r ^ (a + 1) ∣ k := by
      have h3 := hmul0
      have h4 : r ^ a * r = r ^ (a + 1) := (pow_succ r a).symm
      have h5 : r ^ a * (k / r ^ a) = k := by rw [Nat.mul_comm, Nat.div_mul_cancel hk]
      rw [h4, h5] at h3
      exact h3
    exact hk1 hmul
  have hnz : (k / r ^ a) % r ≠ 0 :=
    fun hh => hquot (Nat.dvd_iff_mod_eq_zero.mpr hh)
  have hid : radixFirstDigit r a k m = radixQuotient r a k m % r := rfl
  have hne : radixQuotient r a k m % r ≠ 0 := by
    intro hh
    have hz : (k / r ^ a) % r = 0 := by rw [← hmod]; exact hh
    exact hnz hz
  rw [hid]
  omega

theorem radixPatternIndex_agrees {r a k ℓ m : ℕ} (hr : 2 ≤ r)
    (hk : r ^ a ∣ k) (hℓ : r ^ a ∣ ℓ)
    (hk1 : ¬ (r ^ (a + 1) ∣ k)) (hℓ1 : ¬ (r ^ (a + 1) ∣ ℓ))
    (hpat : radixPatternIndex r a k m = radixPatternIndex r a ℓ m) :
    radixSignAgree (r ^ (a + m + 1)) k ℓ := by
  obtain ⟨d, w, hdfd, hduw, hud, hdlt, hwl⟩ := radix_digit_data r a k m hr
  obtain ⟨d', w', hdfd', hduw', hvd, hdlt', hwl'⟩ := radix_digit_data r a ℓ m hr
  have hpos : 1 ≤ d := by
    have h1 := radixFirstDigit_pos (m := m) hr hk hk1
    rw [hdfd] at h1
    exact h1
  have hpos' : 1 ≤ d' := by
    have h1 := radixFirstDigit_pos (m := m) hr hℓ hℓ1
    rw [hdfd'] at h1
    exact h1
  have hpat' : (if radixFirstDigit r a k m ≤ r - radixFirstDigit r a k m
      then (radixFirstDigit r a k m - 1, radixUpperDigits r a k m)
      else (r - radixFirstDigit r a k m - 1, r ^ m - 1 - radixUpperDigits r a k m))
    = (if radixFirstDigit r a ℓ m ≤ r - radixFirstDigit r a ℓ m
      then (radixFirstDigit r a ℓ m - 1, radixUpperDigits r a ℓ m)
      else (r - radixFirstDigit r a ℓ m - 1, r ^ m - 1 - radixUpperDigits r a ℓ m)) := by
    simpa [radixPatternIndex] using! hpat
  rw [hdfd, hduw, hdfd', hduw'] at hpat'
  have hcase : radixQuotient r a k m = radixQuotient r a ℓ m ∨
      radixQuotient r a k m + radixQuotient r a ℓ m = r ^ (m + 1) := by
    refine radix_pattern_core hr _ _ _ _ _ _ hud hvd hdlt hpos hdlt' hpos' hwl hwl' ?_
    exact hpat'
  have hk1 : r ^ a * (k / r ^ a) = k := by rw [Nat.mul_comm, Nat.div_mul_cancel hk]
  have hl1 : r ^ a * (ℓ / r ^ a) = ℓ := by rw [Nat.mul_comm, Nat.div_mul_cancel hℓ]
  rcases hcase with huv | hsum
  · have hres : (k / r ^ a) % r ^ (m + 1) = (ℓ / r ^ a) % r ^ (m + 1) := by
      simpa [radixQuotient] using! huv
    by_cases hge : k / r ^ a ≥ ℓ / r ^ a
    · have hsub : r ^ (m + 1) ∣ (k / r ^ a) - (ℓ / r ^ a) :=
        radix_dvd_sub_of_mod_eq (Nat.pow_pos (by omega : 0 < r)) hres hge
      have hmul0 : r ^ a * r ^ (m + 1) ∣ r ^ a * ((k / r ^ a) - (ℓ / r ^ a)) :=
        Nat.mul_dvd_mul_left (r ^ a) hsub
      have hmul : r ^ (a + m + 1) ∣ r ^ a * ((k / r ^ a) - (ℓ / r ^ a)) := by
        have h2 := hmul0
        rwa [← pow_add, ← Nat.add_assoc a m 1] at h2
      have hid : r ^ a * ((k / r ^ a) - (ℓ / r ^ a)) = k - ℓ := by
        calc r ^ a * ((k / r ^ a) - (ℓ / r ^ a))
            = r ^ a * (k / r ^ a) - r ^ a * (ℓ / r ^ a) :=
            Nat.mul_sub (r ^ a) (k / r ^ a) (ℓ / r ^ a)
          _ = k - ℓ := by rw [hk1, hl1]
      have hkℓ : ℓ ≤ k := by
        have h3 : r ^ a * (k / r ^ a) ≥ r ^ a * (ℓ / r ^ a) := Nat.mul_le_mul_left _ hge
        rw [hk1, hl1] at h3
        exact h3
      refine Or.inr ?_
      rw [radixDiff, if_pos hkℓ, ← hid]
      exact hmul
    · have hlt : ℓ / r ^ a > k / r ^ a := by omega
      have hle : k / r ^ a ≤ ℓ / r ^ a := by omega
      have hsub : r ^ (m + 1) ∣ (ℓ / r ^ a) - (k / r ^ a) :=
        radix_dvd_sub_of_mod_eq (Nat.pow_pos (by omega : 0 < r)) hres.symm hle
      have hmul0 : r ^ a * r ^ (m + 1) ∣ r ^ a * ((ℓ / r ^ a) - (k / r ^ a)) :=
        Nat.mul_dvd_mul_left (r ^ a) hsub
      have hmul : r ^ (a + m + 1) ∣ r ^ a * ((ℓ / r ^ a) - (k / r ^ a)) := by
        have h2 := hmul0
        rwa [← pow_add, ← Nat.add_assoc a m 1] at h2
      have hid : r ^ a * ((ℓ / r ^ a) - (k / r ^ a)) = ℓ - k := by
        calc r ^ a * ((ℓ / r ^ a) - (k / r ^ a))
            = r ^ a * (ℓ / r ^ a) - r ^ a * (k / r ^ a) :=
            Nat.mul_sub (r ^ a) (ℓ / r ^ a) (k / r ^ a)
          _ = ℓ - k := by rw [hk1, hl1]
      have hkℓ : k < ℓ := by
        have h3 : r ^ a * (ℓ / r ^ a) > r ^ a * (k / r ^ a) :=
          (Nat.mul_lt_mul_left (Nat.pow_pos (by omega : 0 < r))).mpr hlt
        rw [hk1, hl1] at h3
        exact h3
      refine Or.inr ?_
      rw [radixDiff, if_neg (by omega), ← hid]
      exact hmul
  · have hres : (k / r ^ a) % r ^ (m + 1) + (ℓ / r ^ a) % r ^ (m + 1) = r ^ (m + 1) := by
      simpa [radixQuotient] using! hsum
    have hsub : r ^ (m + 1) ∣ (k / r ^ a) + (ℓ / r ^ a) :=
      radix_dvd_add_of_mod_sum (Nat.pow_pos (by omega : 0 < r)) hres
    have hmul0 : r ^ a * r ^ (m + 1) ∣ r ^ a * ((k / r ^ a) + (ℓ / r ^ a)) :=
      Nat.mul_dvd_mul_left (r ^ a) hsub
    have hmul : r ^ (a + m + 1) ∣ r ^ a * ((k / r ^ a) + (ℓ / r ^ a)) := by
      have h2 := hmul0
      rwa [← pow_add, ← Nat.add_assoc a m 1] at h2
    have hid : r ^ a * ((k / r ^ a) + (ℓ / r ^ a)) = k + ℓ := by
      calc r ^ a * ((k / r ^ a) + (ℓ / r ^ a))
          = r ^ a * (k / r ^ a) + r ^ a * (ℓ / r ^ a) := by rw [Nat.mul_add]
        _ = k + ℓ := by rw [hk1, hl1]
    refine Or.inl ?_
    rw [← hid]
    exact hmul

theorem radixPigeonhole {r n a m : ℕ} {L : List ℕ}
    (hr : 3 ≤ r) (hn : 1 ≤ n)
    (hbound : ∀ k ∈ L, k < r ^ n)
    (halpha : ∀ k ∈ L, radixAlpha r k = a)
    (hnonzero : ∀ k ∈ L, k ≠ 0)
    (hnodup : L.Nodup)
    (hsep : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → ¬ radixSignAgree (r ^ (a + m + 1)) k ℓ) :
    L.length ≤ (r / 2) * r ^ m := by
  classical
  have hdata : ∀ k ∈ L, ∃ d w : ℕ,
      radixFirstDigit r a k m = d ∧ radixUpperDigits r a k m = w ∧
      radixQuotient r a k m = d + r * w ∧ 1 ≤ d ∧ d < r ∧ w < r ^ m := by
    intro k hk
    obtain ⟨d, w, hdfd, hduw, hud, hdlt, hwl⟩ := radix_digit_data r a k m (by omega)
    have hα : radixAlpha r k = a := halpha k hk
    have hkpos : 0 < k := Nat.pos_of_ne_zero (hnonzero k hk)
    have hnot : ¬ (r ^ (a + 1) ∣ k) := by
      intro hh
      have hge : a + 1 ≤ radixAlpha r k :=
        radixAlpha_ge_of_dvd r k (a + 1) (by omega) hkpos hh
      omega
    have hpos : 1 ≤ radixFirstDigit r a k m :=
      radixFirstDigit_pos (m := m) (by omega)
        (by rw [← hα]; exact radixAlpha_dvd' r k (by omega)) hnot
    refine ⟨d, w, hdfd, hduw, hud, ?_, hdlt, hwl⟩
    rw [hdfd] at hpos
    exact hpos

  have hinj : Set.InjOn (radixPatternIndex r a · m) ↑(L.toFinset) := by
    intro k hk ℓ hℓ hpat
    simp only [Finset.mem_coe, List.mem_toFinset] at hk hℓ
    have hdk : r ^ a ∣ k := by rw [← halpha k hk]; exact radixAlpha_dvd' r k (by omega)
    have hdl : r ^ a ∣ ℓ := by rw [← halpha ℓ hℓ]; exact radixAlpha_dvd' r ℓ (by omega)
    have hαk : radixAlpha r k = a := halpha k hk
    have hαℓ : radixAlpha r ℓ = a := halpha ℓ hℓ
    have hk1 : ¬ (r ^ (a + 1) ∣ k) := by
      intro hh
      have hge : a + 1 ≤ radixAlpha r k := radixAlpha_ge_of_dvd r k (a + 1) (by omega)
        (Nat.pos_of_ne_zero (hnonzero k hk)) hh
      omega
    have hℓ1 : ¬ (r ^ (a + 1) ∣ ℓ) := by
      intro hh
      have hge : a + 1 ≤ radixAlpha r ℓ := radixAlpha_ge_of_dvd r ℓ (a + 1) (by omega)
        (Nat.pos_of_ne_zero (hnonzero ℓ hℓ)) hh
      omega
    have hagree := radixPatternIndex_agrees (by omega) hdk hdl hk1 hℓ1 hpat
    by_cases hne : k = ℓ
    · exact hne
    · exact absurd hagree (hsep k hk ℓ hℓ hne)

  have hmaps : Set.MapsTo (radixPatternIndex r a · m) ↑(L.toFinset)
      ((Finset.range (r / 2) ×ˢ Finset.range (r ^ m)) : Finset (ℕ × ℕ)) := by
    intro k hk
    simp only [Finset.mem_coe, List.mem_toFinset] at hk
    obtain ⟨d, w, hdfd, hduw, hud, hdle, hdlt, hwl⟩ := hdata k hk
    have hpat : (fun x => radixPatternIndex r a x m) k
        = if d ≤ r - d then (d - 1, w) else (r - d - 1, r ^ m - 1 - w) := by
      show radixPatternIndex r a k m = _
      unfold radixPatternIndex
      rw [hdfd, hduw]
    rw [hpat]
    have hmin : min d (r - d) ≤ r / 2 := by
      have h1 : min d (r - d) ≤ d := Nat.min_le_left _ _
      have h2 : min d (r - d) ≤ r - d := Nat.min_le_right _ _
      have h3 : 2 * min d (r - d) ≤ d + (r - d) := by omega
      omega
    by_cases h : d ≤ r - d
    · simp only [h, if_true, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
      refine ⟨?_, hwl⟩
      have h4 : min d (r - d) = d := by
        apply Nat.min_eq_left
        omega
      omega
    · simp only [h, if_false, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
      refine ⟨?_, ?_⟩
      have h4 : min d (r - d) = r - d := by
        apply Nat.min_eq_right
        omega
      omega
      omega
  have hcard : (L.toFinset).card
      ≤ ((Finset.range (r / 2) ×ˢ Finset.range (r ^ m)) : Finset (ℕ × ℕ)).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  calc L.length = (L.toFinset).card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ ((Finset.range (r / 2) ×ˢ Finset.range (r ^ m)) : Finset (ℕ × ℕ)).card := hcard
    _ = (r / 2) * r ^ m := by rw [Finset.card_product, Finset.card_range, Finset.card_range]

theorem radixPigeonhole_three {n a m : ℕ} {L : List ℕ}
    (hn : 1 ≤ n)
    (hbound : ∀ k ∈ L, k < 3 ^ n)
    (halpha : ∀ k ∈ L, radixAlpha 3 k = a)
    (hnonzero : ∀ k ∈ L, k ≠ 0)
    (hnodup : L.Nodup)
    (hsep : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → ¬ radixSignAgree (3 ^ (a + m + 1)) k ℓ) :
    L.length ≤ 3 ^ m := by
  have h := radixPigeonhole (r := 3) (n := n) (a := a) (m := m) (L := L)
    (by omega) hn hbound halpha hnonzero hnodup hsep
  rw [show (3 : ℕ) / 2 = 1 by omega] at h
  simpa using! h

private theorem radix_foldl_max {r N : ℕ} (acc : ℕ) (l : List (ℕ × ℕ)) :
    acc ≤ l.foldl (fun acc q => max acc (radixPairValue r N q.1 q.2)) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons q l ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left _ _)
      (ih (max acc (radixPairValue r N q.1 q.2)))

private theorem radix_foldl_ge {r N : ℕ} (acc : ℕ) (pairs : List (ℕ × ℕ)) (p : ℕ × ℕ)
    (hp : p ∈ pairs) :
    radixPairValue r N p.1 p.2
      ≤ pairs.foldl (fun acc q => max acc (radixPairValue r N q.1 q.2)) acc := by
  induction pairs generalizing acc with
  | nil => simp at hp
  | cons q l ih =>
    simp only [List.foldl_cons]
    by_cases hpq : p = q
    · rw [hpq]
      have h1 : radixPairValue r N q.1 q.2 ≤ max acc (radixPairValue r N q.1 q.2) :=
        le_max_of_le_right (le_refl _)
      exact le_trans h1
        (radix_foldl_max (r := r) (N := N) (max acc (radixPairValue r N q.1 q.2)) l)
    · have hmem : p ∈ l := by
        simp only [List.mem_cons] at hp
        rcases hp with h | h
        · exact absurd h hpq
        · exact h
      exact ih (max acc (radixPairValue r N q.1 q.2)) hmem

theorem radixGreedyValue_ge_pair {r N : ℕ} {L : List ℕ} {k ℓ : ℕ}
    (hk : k ∈ radixMinAlphaSublist r L) (hℓ : ℓ ∈ radixMinAlphaSublist r L)
    (hne : k ≠ ℓ) :
    radixPairValue r N k ℓ ≤ radixGreedyValue r N L := by
  have hmem : (k, ℓ) ∈ radixPairs (radixMinAlphaSublist r L) := by
    rw [radixPairs]
    simp only [List.mem_flatMap]
    refine ⟨k, hk, ?_⟩
    rw [List.mem_map]
    refine ⟨ℓ, ?_, rfl⟩
    rw [List.mem_filter]
    have hne' : ℓ ≠ k := fun h => hne h.symm
    exact ⟨hℓ, by simp [hne']⟩
  have h := radix_foldl_ge (r := r) (N := N) 0 (radixPairs (radixMinAlphaSublist r L)) (k, ℓ) hmem
  simpa [radixGreedyValue] using! h

theorem radixPairValue_le_separates {r n a m k ℓ : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = a) (hαℓ : radixAlpha r ℓ = a)
    (hsum : k + ℓ ≠ r ^ n)
    (ham : a + m + 1 ≤ n)
    (hpv : radixPairValue r (r ^ n) k ℓ ≤ a + m) :
    ¬ radixSignAgree (r ^ (a + m + 1)) k ℓ := by
  intro hagree
  rcases hagree with hsum' | hdiff'
  · have hrN : r ^ (a + m + 1) ∣ r ^ n := radix_pow_dvd_pow r _ _ (by omega) ham
    have hrem : r ^ (a + m + 1) ∣ (k + ℓ) % (r ^ n) := radix_dvd_mod_of_dvd hsum' hrN
    have hpos : 0 < (k + ℓ) % (r ^ n) :=
      radix_add_child_pos k ℓ (r ^ n) hk hℓ hne hsum
    have hge : a + m + 1 ≤ radixAlpha r ((k + ℓ) % (r ^ n)) :=
      radixAlpha_ge_of_dvd r _ _ hr hpos hrem
    have hpv' : a + m + 1 ≤ radixPairValue r (r ^ n) k ℓ := by
      unfold radixPairValue
      omega
    omega
  · have hrN : r ^ (a + m + 1) ∣ r ^ n := radix_pow_dvd_pow r _ _ (by omega) ham
    have hsub : r ^ (a + m + 1) ∣ k + (r ^ n) - ℓ := by
      by_cases hge : k ≥ ℓ
      · have hsub' : k + (r ^ n) - ℓ = (k - ℓ) + (r ^ n) := by omega
        rw [hsub']
        have hdiff : r ^ (a + m + 1) ∣ k - ℓ := by
          rw [radixDiff, if_pos hge] at hdiff'
          exact hdiff'
        exact Nat.dvd_add hdiff hrN
      · have hsub' : k + (r ^ n) - ℓ = (r ^ n) - (ℓ - k) := by
          have hle : ℓ ≤ r ^ n := by omega
          omega
        rw [hsub']
        have hdiff : r ^ (a + m + 1) ∣ ℓ - k := by
          rw [radixDiff, if_neg hge] at hdiff'
          exact hdiff'
        exact Nat.dvd_sub hrN hdiff
    have hrem : r ^ (a + m + 1) ∣ (k + (r ^ n) - ℓ) % (r ^ n) :=
      radix_dvd_mod_of_dvd hsub hrN
    have hpos : 0 < (k + (r ^ n) - ℓ) % (r ^ n) :=
      radix_sub_child_pos k ℓ (r ^ n) hk hℓ hne
    have hge : a + m + 1 ≤ radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) :=
      radixAlpha_ge_of_dvd r _ _ hr hpos hrem
    have hpv' : a + m + 1 ≤ radixPairValue r (r ^ n) k ℓ := by
      unfold radixPairValue
      omega
    omega

theorem radixMinAlphaSublist_length_le {r n m : ℕ} {L : List ℕ} (hr : 3 ≤ r) (hn : 1 ≤ n)
    (hbound : ∀ k ∈ L, k < r ^ n)
    (hnonzero : ∀ k ∈ L, k ≠ 0)
    (hnodup : L.Nodup)
    (hstates : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → k + ℓ ≠ r ^ n)
    (ham : radixMinAlpha r L + m + 1 ≤ n)
    (hgreedy : radixGreedyValue r (r ^ n) L ≤ radixMinAlpha r L + m) :
    (radixMinAlphaSublist r L).length ≤ (r / 2) * r ^ m := by
  set a : ℕ := radixMinAlpha r L with ha
  set L' : List ℕ := radixMinAlphaSublist r L with hL'
  have hα' : ∀ k ∈ L', radixAlpha r k = a := by
    intro k hk
    have hmem : k ∈ L.filter (fun x => radixAlpha r x == radixMinAlpha r L) := by
      rw [hL'] at hk
      exact hk
    rw [List.mem_filter] at hmem
    obtain ⟨_, hkeq⟩ := hmem
    have h1 : radixAlpha r k = a := by
      rw [ha]
      simp only [beq_iff_eq] at hkeq
      exact hkeq
    exact h1
  have hbound' : ∀ k ∈ L', k < r ^ n := by
    intro k hk
    have hmem : k ∈ L.filter (fun x => radixAlpha r x == radixMinAlpha r L) := by
      rw [hL'] at hk
      exact hk
    rw [List.mem_filter] at hmem
    obtain ⟨hkl, _⟩ := hmem
    exact hbound k hkl
  have hnonzero' : ∀ k ∈ L', k ≠ 0 := by
    intro k hk
    have hmem : k ∈ L.filter (fun x => radixAlpha r x == radixMinAlpha r L) := by
      rw [hL'] at hk
      exact hk
    rw [List.mem_filter] at hmem
    obtain ⟨hkl, _⟩ := hmem
    exact hnonzero k hkl
  have hnodup' : L'.Nodup := by
    have hmem : L' = L.filter (fun x => radixAlpha r x == radixMinAlpha r L) := by
      rw [hL']
      rfl
    rw [hmem]
    exact hnodup.filter _
  have hsep : ∀ k ∈ L', ∀ ℓ ∈ L', k ≠ ℓ →
      ¬ radixSignAgree (r ^ (a + m + 1)) k ℓ := by
    intro k hk ℓ hℓ hne
    have hgreedy' : radixPairValue r (r ^ n) k ℓ ≤ a + m := by
      have h1 := radixGreedyValue_ge_pair (r := r) (N := r ^ n) (L := L) hk hℓ hne
      rw [ha] at hgreedy
      omega
    have hsum : k + ℓ ≠ r ^ n := by
      have hmem : k ∈ L.filter (fun x => radixAlpha r x == radixMinAlpha r L) := by
        rw [hL'] at hk
        exact hk
      rw [List.mem_filter] at hmem
      obtain ⟨hkl, _⟩ := hmem
      have hmem2 : ℓ ∈ L.filter (fun x => radixAlpha r x == radixMinAlpha r L) := by
        rw [hL'] at hℓ
        exact hℓ
      rw [List.mem_filter] at hmem2
      obtain ⟨hℓl, _⟩ := hmem2
      exact hstates k hkl ℓ hℓl hne
    have ham' : a + m + 1 ≤ n := by rw [ha]; exact ham
    exact radixPairValue_le_separates (r := r) (n := n) (a := a) (m := m) (k := k) (ℓ := ℓ)
      (by omega) hn (hbound' k hk) (hbound' ℓ hℓ) hne (hα' k hk) (hα' ℓ hℓ) hsum ham'
      hgreedy'
  have h := radixPigeonhole (r := r) (n := n) (a := a) (m := m) (L := L') (by omega) hn
    hbound' hα' hnonzero' hnodup' hsep
  simpa [hL'] using! h

theorem radixMinAlphaSublist_length_le_three {n m : ℕ} {L : List ℕ} (hn : 1 ≤ n)
    (hbound : ∀ k ∈ L, k < 3 ^ n)
    (hnonzero : ∀ k ∈ L, k ≠ 0)
    (hnodup : L.Nodup)
    (hstates : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → k + ℓ ≠ 3 ^ n)
    (ham : radixMinAlpha 3 L + m + 1 ≤ n)
    (hgreedy : radixGreedyValue 3 (3 ^ n) L ≤ radixMinAlpha 3 L + m) :
    (radixMinAlphaSublist 3 L).length ≤ 3 ^ m := by
  have h := radixMinAlphaSublist_length_le (r := 3) (n := n) (m := m) (L := L)
    (by omega) hn hbound hnonzero hnodup hstates ham hgreedy
  rw [show (3 : ℕ) / 2 = 1 by omega] at h
  simpa using! h

theorem radixPeriodAttrition_le_one {n m : ℕ} {L : List ℕ} (hn : 1 ≤ n)
    (hbound : ∀ k ∈ L, k < 3 ^ n)
    (hnonzero : ∀ k ∈ L, k ≠ 0)
    (hnodup : L.Nodup)
    (hstates : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → k + ℓ ≠ 3 ^ n)
    (ham : radixMinAlpha 3 L + m + 1 ≤ n)
    (hgreedy : radixGreedyValue 3 (3 ^ n) L ≤ radixMinAlpha 3 L + m)
    (hm : (m : ℝ) ≤ Real.sqrt (2 * ((n - 1 - radixMinAlpha 3 L : ℕ) : ℝ))) :
    radixPeriodAttrition 3 n (radixMinAlphaSublist 3 L) ≤ 1 := by
  set a : ℕ := radixMinAlpha 3 L with ha
  set L' : List ℕ := radixMinAlphaSublist 3 L with hL'
  have hα' : ∀ k ∈ L', radixAlpha 3 k = a := by
    intro k hk
    have hmem : k ∈ L.filter (fun x => radixAlpha 3 x == radixMinAlpha 3 L) := by
      rw [hL'] at hk
      exact hk
    rw [List.mem_filter] at hmem
    obtain ⟨_, hkeq⟩ := hmem
    have h1 : radixAlpha 3 k = a := by
      rw [ha]
      simp only [beq_iff_eq] at hkeq
      exact hkeq
    exact h1
  by_cases hemp : L' = []
  · simp [radixPeriodAttrition, hemp]
  · obtain ⟨k₀, hk₀⟩ := List.exists_mem_of_ne_nil L' hemp
    have hsame : ∀ k ∈ L', radixValue 3 n k = radixValue 3 n k₀ := by
      intro k hk
      have h1 : radixBeta 3 n k = radixBeta 3 n k₀ := by
        unfold radixBeta
        have h2 := hα' k hk
        have h3 := hα' k₀ hk₀
        omega
      unfold radixValue
      rw [h1]
    have hsum : ∀ (l : List ℕ), (∀ k ∈ l, radixValue 3 n k = radixValue 3 n k₀) →
        (l.map (radixValue 3 n)).sum = (l.length : ℝ) * radixValue 3 n k₀ := by
      intro l hl
      induction l with
      | nil => simp
      | cons k l ih =>
        have hk : radixValue 3 n k = radixValue 3 n k₀ := hl k (by simp)
        have hl' : ∀ j ∈ l, radixValue 3 n j = radixValue 3 n k₀ :=
          fun j hj => hl j (by simp [hj])
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [hk, ih hl']
        push_cast
        ring
    have hattr : radixPeriodAttrition 3 n L' = (L'.length : ℝ) * radixValue 3 n k₀ := by
      unfold radixPeriodAttrition
      exact hsum L' (fun k hk => hsame k hk)
    have hpack : L'.length ≤ 3 ^ m := by
      have h := radixMinAlphaSublist_length_le_three (n := n) (m := m) (L := L) hn
        hbound hnonzero hnodup hstates (by rw [← ha]; exact ham) (by rw [← ha]; exact hgreedy)
      simpa [hL'] using! h
    have hβ : radixBeta 3 n k₀ = n - 1 - a := by
      unfold radixBeta
      have h2 := hα' k₀ hk₀
      rw [ha] at h2
      omega
    have hsqrt : 0 ≤ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)) := Real.sqrt_nonneg _
    have hcast : (m : ℝ) ≤ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)) := by
      rw [ha] at hm
      exact hm
    have hrpow : (3 ^ m : ℝ) ≤ (3 : ℝ) ^ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)) := by
      have h1 : (3 ^ m : ℝ) = 3 ^ (m : ℝ) := by
        rw [Real.rpow_natCast 3 m]
      rw [h1]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) hcast
    have hV : radixValue 3 n k₀
        = 3 ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)))) := by
      unfold radixValue
      rw [hβ]
      have h3 : (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))))
          = Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        ring
      rw [h3]
    have hone : (3 : ℝ) ^ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))
        * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)))) = 1 := by
      have h1 : (3 : ℝ) ^ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))
          = Real.exp (Real.log 3 * Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
      have h2 : (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))))
          = Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        ring
      rw [h1, h2]
      rw [← Real.exp_add]
      have hz : Real.log 3 * Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))
          + -(Real.log 3) * Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)) = 0 := by ring
      rw [hz]
      exact Real.exp_zero
    have hmain : (L'.length : ℝ) * radixValue 3 n k₀ ≤ 1 := by
      have h1 : (L'.length : ℝ) ≤ 3 ^ m := by exact_mod_cast hpack
      have h2 : (3 ^ m : ℝ) ≤ (3 : ℝ) ^ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)) := hrpow
      rw [hV]
      have h3 : (3 ^ m : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)))) ≤ 1 := by
        calc (3 ^ m : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))))
            ≤ (3 : ℝ) ^ Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))
              * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)))) := by
                gcongr
          _ = 1 := hone
      calc (L'.length : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ))))
          ≤ (3 ^ m : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)))) := by
            have hnonneg : 0 ≤ (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 - a : ℕ) : ℝ)))) :=
              Real.rpow_nonneg (by norm_num) _
            gcongr
        _ ≤ 1 := h3
    rw [hattr]
    exact hmain

private theorem radix_final_quotient {r n k : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : 0 < k) (hk' : k < r ^ n) (hdiv : r ^ (n - 1) ∣ k) :
    ∃ u : ℕ, k = r ^ (n - 1) * u ∧ 1 ≤ u ∧ u < r := by
  obtain ⟨u, hu⟩ := hdiv
  have hq : k = r ^ (n - 1) * u := hu
  have hpos : 0 < r ^ (n - 1) := Nat.pow_pos (by omega)
  have hqu : r ^ (n - 1) * u / r ^ (n - 1) = u := Nat.mul_div_cancel_left u hpos
  have hdivu : k / r ^ (n - 1) = u := by rw [hq]; exact hqu
  have hu1 : 1 ≤ u := by
    have h2 : 0 < r ^ (n - 1) * u := by rw [← hq]; exact hk
    by_contra hcon
    have h0 : u = 0 := by omega
    rw [h0, Nat.mul_zero] at h2
    simp at h2
  have hN : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  have hu2 : u < r := by
    have h3 : k < r ^ (n - 1) * r := by rw [← hN]; exact hk'
    have h4 : k / r ^ (n - 1) < r := Nat.div_lt_of_lt_mul h3
    rw [hdivu] at h4
    exact h4
  exact ⟨u, hq, hu1, hu2⟩

theorem radixShiftReadout_pos {r n k : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : 0 < k) (hk' : k < r ^ n) (hdiv : r ^ (n - 1) ∣ k) :
    1 ≤ radixShiftReadout r n k ∧ radixShiftReadout r n k < r := by
  obtain ⟨u, hq, hu1, hu2⟩ := radix_final_quotient hr hn hk hk' hdiv
  have hpos : 0 < r ^ (n - 1) := Nat.pow_pos (by omega)
  have hqu : r ^ (n - 1) * u / r ^ (n - 1) = u := Nat.mul_div_cancel_left u hpos
  have hdivu : k / r ^ (n - 1) = u := by rw [hq]; exact hqu
  unfold radixShiftReadout
  rw [hdivu]
  have : u % r = u := Nat.mod_eq_of_lt hu2
  rw [this]
  exact ⟨hu1, hu2⟩

theorem radixShiftReadout_sign {r n k : ℕ} (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : 0 < k) (hk' : k < r ^ n) (hdiv : r ^ (n - 1) ∣ k) :
    radixShiftReadout r n (r ^ n - k) + radixShiftReadout r n k = r := by
  obtain ⟨u, hq, hu1, hu2⟩ := radix_final_quotient hr hn hk hk' hdiv
  have hpos : 0 < r ^ (n - 1) := Nat.pow_pos (by omega)
  have hqu : r ^ (n - 1) * u / r ^ (n - 1) = u := Nat.mul_div_cancel_left u hpos
  have hdivu : k / r ^ (n - 1) = u := by rw [hq]; exact hqu
  have hN : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  have hNk : r ^ n - k = r ^ (n - 1) * (r - u) := by
    rw [hN, hq]
    exact (Nat.mul_sub (r ^ (n - 1)) r u).symm
  have hdivuNk : (r ^ n - k) / r ^ (n - 1) = r - u := by
    rw [hNk]
    exact Nat.mul_div_cancel_left (r - u) hpos
  have hcomp2 : r - u < r := by omega
  have hread : radixShiftReadout r n (r ^ n - k) = r - u := by
    unfold radixShiftReadout
    rw [hdivuNk]
    have : (r - u) % r = r - u := Nat.mod_eq_of_lt hcomp2
    rw [this]
  have hread2 : radixShiftReadout r n k = u := by
    unfold radixShiftReadout
    rw [hdivu]
    have : u % r = u := Nat.mod_eq_of_lt hu2
    rw [this]
  rw [hread, hread2]
  omega

private theorem radix_foldl_min_le (r : ℕ) (acc : ℕ) (L : List ℕ) :
    L.foldl (fun a k => Nat.min a (radixAlpha r k)) acc ≤ acc ∧
      ∀ k ∈ L, L.foldl (fun a j => Nat.min a (radixAlpha r j)) acc ≤ radixAlpha r k := by
  induction L generalizing acc with
  | nil => simp
  | cons j L ih =>
    simp only [List.foldl_cons]
    have h1 := ih (acc := Nat.min acc (radixAlpha r j))
    refine ⟨?_, ?_⟩
    · exact le_trans h1.1 (Nat.min_le_left _ _)
    · intro k hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact le_trans h1.1 (Nat.min_le_right _ _)
      · exact h1.2 k hk

private theorem radix_foldl_min_ge (r a : ℕ) : ∀ (acc : ℕ) (L : List ℕ),
    a ≤ acc → (∀ k ∈ L, a ≤ radixAlpha r k) →
    a ≤ L.foldl (fun acc k => Nat.min acc (radixAlpha r k)) acc := by
  intro acc L
  induction L generalizing acc with
  | nil =>
    intro hacc h
    simpa using! hacc
  | cons k L ih =>
    intro hacc h
    simp only [List.foldl_cons]
    have hk : a ≤ radixAlpha r k := h k (by simp)
    have hrest : ∀ j ∈ L, a ≤ radixAlpha r j := fun j hj => h j (by simp [hj])
    have hproof : a ≤ Nat.min acc (radixAlpha r k) := Nat.le_min.mpr ⟨hacc, hk⟩
    have h1 := ih (Nat.min acc (radixAlpha r k)) hproof hrest
    exact h1

theorem radixMinAlpha_le (r : ℕ) (L : List ℕ) (k : ℕ) (hk : k ∈ L) :
    radixMinAlpha r L ≤ radixAlpha r k := by
  cases L with
  | nil => simp at hk
  | cons j L =>
    have hfold : radixMinAlpha r (j :: L)
        = L.foldl (fun acc k => Nat.min acc (radixAlpha r k)) (radixAlpha r j) := rfl
    rw [hfold]
    by_cases hjk : j = k
    · rw [hjk]
      exact (radix_foldl_min_le r (radixAlpha r k) L).1
    · have hkL : k ∈ L := by
        rcases List.mem_cons.mp hk with h | h
        · exact absurd h.symm hjk
        · exact h
      exact (radix_foldl_min_le r (radixAlpha r j) L).2 k hkL

theorem radixMinAlpha_ge (r : ℕ) (L : List ℕ) (a : ℕ) (hne : L ≠ [])
    (h : ∀ k ∈ L, a ≤ radixAlpha r k) : a ≤ radixMinAlpha r L := by
  cases L with
  | nil => simp at hne
  | cons j L =>
    have hfold : radixMinAlpha r (j :: L)
        = L.foldl (fun acc k => Nat.min acc (radixAlpha r k)) (radixAlpha r j) := rfl
    rw [hfold]
    have h1 : a ≤ radixAlpha r j := h j (by simp)
    have h2 : a ≤ L.foldl (fun acc k => Nat.min acc (radixAlpha r k)) (radixAlpha r j) :=
      radix_foldl_min_ge r a (radixAlpha r j) L h1 (fun k hk => h k (by simp [hk]))
    exact h2

private theorem radix_listValue_filter_add (r n : ℕ) (L : List ℕ) (p : ℕ → Bool) :
    ((L.filter p).map (radixValue r n)).sum
      + ((L.filter (fun k => !p k)).map (radixValue r n)).sum
      = (L.map (radixValue r n)).sum := by
  induction L with
  | nil => simp
  | cons k L ih =>
    by_cases h : p k
    · have h1 : (k :: L).filter p = k :: L.filter p := by simp [List.filter, h]
      have h2 : (k :: L).filter (fun k => !p k) = L.filter (fun k => !p k) := by
        simp [List.filter, h]
      have h3 : (k :: L).map (radixValue r n) = radixValue r n k :: L.map (radixValue r n) := rfl
      rw [h1, h2, h3]
      simp only [List.map_cons, List.sum_cons]
      linarith
    · have h1 : (k :: L).filter p = L.filter p := by simp [List.filter, h]
      have h2 : (k :: L).filter (fun k => !p k) = k :: L.filter (fun k => !p k) := by
        simp [List.filter, h]
      have h3 : (k :: L).map (radixValue r n) = radixValue r n k :: L.map (radixValue r n) := rfl
      rw [h1, h2, h3]
      simp only [List.map_cons, List.sum_cons]
      linarith

theorem radixListValue_partition (r n : ℕ) (L : List ℕ) :
    radixListValue r n (radixKeptLabels r L) + radixListValue r n (radixMinAlphaSublist r L)
      = radixListValue r n L := by
  unfold radixKeptLabels radixMinAlphaSublist radixListValue
  simpa only [add_comm] using!
    (radix_listValue_filter_add r n L (fun k => radixAlpha r k == radixMinAlpha r L))

theorem radixGreedyChild_alpha (r N : ℕ) (k ℓ : ℕ) :
    radixAlpha r (radixGreedyChild r N k ℓ) = radixPairValue r N k ℓ := by
  unfold radixGreedyChild radixPairValue
  by_cases h : radixAlpha r ((k + ℓ) % N) < radixAlpha r ((k + N - ℓ) % N)
  · have h2 : radixAlpha r ((k + ℓ) % N) ≤ radixAlpha r ((k + N - ℓ) % N) := by omega
    simp only [if_pos h]
    rw [max_eq_right h2]
  · have h' : radixAlpha r ((k + N - ℓ) % N) ≤ radixAlpha r ((k + ℓ) % N) := by omega
    simp only [if_neg h]
    rw [max_eq_left h']

theorem radixListValue_step_lower (r n N : ℕ) (L : List ℕ) :
    radixListValue r n L - radixPeriodAttrition r n (radixMinAlphaSublist r L)
      ≤ radixListValue r n (radixPeriodStep r N L) := by
  have hpart : radixListValue r n (radixKeptLabels r L)
      + radixListValue r n (radixMinAlphaSublist r L) = radixListValue r n L :=
    radixListValue_partition r n L
  have hattr : radixPeriodAttrition r n (radixMinAlphaSublist r L)
      = radixListValue r n (radixMinAlphaSublist r L) := rfl
  have hsplit : radixListValue r n (radixPeriodStep r N L)
      = radixListValue r n (radixKeptLabels r L) + radixListValue r n (radixPeriodChildren r N L) := by
    unfold radixPeriodStep radixListValue
    rw [List.map_append, List.sum_append]
  have hnonneg : 0 ≤ radixListValue r n (radixPeriodChildren r N L) := by
    have h : ∀ l : List ℕ, 0 ≤ (l.map (radixValue r n)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons k l ih =>
        simp only [List.map_cons, List.sum_cons]
        have h1 : 0 < radixValue r n k := radixValue_pos r n k
        linarith
    exact h (radixPeriodChildren r N L)
  rw [hattr, hsplit]
  linarith

theorem radixPeriodStep_minAlpha {r N : ℕ} {L : List ℕ}
    (hprod : ∃ k ℓ, radixGreedyPair r N L = some (k, ℓ) ∧
      radixPairValue r N k ℓ > radixMinAlpha r L) :
    radixMinAlpha r (radixPeriodStep r N L) ≥ radixMinAlpha r L + 1 := by
  obtain ⟨k, ℓ, hkℓ, hval⟩ := hprod
  have hαc : radixAlpha r (radixGreedyChild r N k ℓ) = radixPairValue r N k ℓ :=
    radixGreedyChild_alpha r N k ℓ
  have hgt : radixMinAlpha r L < radixAlpha r (radixGreedyChild r N k ℓ) := by omega
  have hchild : radixPeriodChildren r N L = [radixGreedyChild r N k ℓ] := by
    simp only [radixPeriodChildren, hkℓ]
  have hkept : ∀ j ∈ radixKeptLabels r L, radixMinAlpha r L + 1 ≤ radixAlpha r j := by
    intro j hj
    obtain ⟨hjL, hne⟩ := List.mem_filter.mp hj
    have hne' : radixAlpha r j ≠ radixMinAlpha r L := by
      intro hcon
      have h1 : (radixAlpha r j == radixMinAlpha r L) = true := by simp [hcon]
      rw [h1] at hne
      simp at hne
    have h1 : radixMinAlpha r L ≤ radixAlpha r j := radixMinAlpha_le r L j hjL
    omega
  have hne : radixPeriodStep r N L ≠ [] := by
    intro hcon
    have h2 : radixPeriodChildren r N L = [] := by
      unfold radixPeriodStep at hcon
      simp at hcon
      exact hcon.2
    rw [hchild] at h2
    simp at h2
  have hall : ∀ j ∈ radixPeriodStep r N L, radixMinAlpha r L + 1 ≤ radixAlpha r j := by
    intro j hj
    rw [radixPeriodStep, List.mem_append] at hj
    rcases hj with hj | hj
    · exact hkept j hj
    · have hj' : j = radixGreedyChild r N k ℓ := by
        rw [hchild] at hj
        simpa using! hj
      subst hj'
      omega
  exact radixMinAlpha_ge r (radixPeriodStep r N L) (radixMinAlpha r L + 1) hne hall

private theorem radixPeriodChildren_lt (r N : ℕ) (hN : 0 < N) (L : List ℕ) :
    ∀ k ∈ radixPeriodChildren r N L, k < N := by
  intro k hk
  cases hg : radixGreedyPair r N L with
  | none => simp [radixPeriodChildren, hg] at hk
  | some p =>
    obtain ⟨k0, ℓ0⟩ := p
    simp only [radixPeriodChildren, hg] at hk
    have hk' : k = radixGreedyChild r N k0 ℓ0 := by simpa using! hk
    have hc : radixGreedyChild r N k0 ℓ0 = (k0 + ℓ0) % N ∨
          radixGreedyChild r N k0 ℓ0 = (k0 + N - ℓ0) % N := by
      unfold radixGreedyChild
      split <;> simp
    rcases hc with hc | hc
    · rw [hk', hc]
      exact Nat.mod_lt _ hN
    · rw [hk', hc]
      exact Nat.mod_lt _ hN

theorem radixSieveRun_labels_lt (r N : ℕ) (hN : 0 < N) {L : List ℕ} (hL : ∀ k ∈ L, k < N) :
    ∀ (p : ℕ) (k : ℕ), k ∈ radixSieveRun r N p L → k < N := by
  intro p
  induction p with
  | zero =>
    intro k hk
    exact hL k hk
  | succ p ih =>
    intro k hk
    have hk' : k ∈ radixPeriodStep r N (radixSieveRun r N p L) := by
      simpa only [radixSieveRun] using! hk
    rw [radixPeriodStep, List.mem_append] at hk'
    rcases hk' with hk' | hk'
    · exact ih k ((List.mem_filter.mp hk').1)
    · exact radixPeriodChildren_lt r N hN (radixSieveRun r N p L) k hk'

theorem radixSieveRun_succ (r N p : ℕ) (L : List ℕ) :
    radixSieveRun r N (p + 1) L = radixPeriodStep r N (radixSieveRun r N p L) := rfl

theorem radixSieveRun_ne_nil (n p : ℕ) {L : List ℕ}
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L))
    (hne : L ≠ []) : radixSieveRun 3 (3 ^ n) p L ≠ [] := by
  induction p with
  | zero => exact hne
  | succ p ih =>
    have hcond := hp p (by omega)
    obtain ⟨k, ℓ, hkℓ, hval⟩ := hcond.productive
    have hαc : radixAlpha 3 (radixGreedyChild 3 (3 ^ n) k ℓ) = radixPairValue 3 (3 ^ n) k ℓ :=
      radixGreedyChild_alpha 3 (3 ^ n) k ℓ
    have hgt : radixMinAlpha 3 (radixSieveRun 3 (3 ^ n) p L)
        < radixAlpha 3 (radixGreedyChild 3 (3 ^ n) k ℓ) := by omega
    have hch : radixPeriodChildren 3 (3 ^ n) (radixSieveRun 3 (3 ^ n) p L) ≠ [] := by
      simp only [radixPeriodChildren, hkℓ]
      intro hcon
      simp at hcon
    intro hcon
    have hstep : radixPeriodStep 3 (3 ^ n) (radixSieveRun 3 (3 ^ n) p L) = [] := by
      simpa only [radixSieveRun] using! hcon
    rw [radixPeriodStep] at hstep
    have happ : radixKeptLabels 3 (radixSieveRun 3 (3 ^ n) p L) = []
        ∧ radixPeriodChildren 3 (3 ^ n) (radixSieveRun 3 (3 ^ n) p L) = [] := by
      simpa using! hstep
    exact hch happ.2

theorem radixSieveRun_minAlpha (n p : ℕ) {L : List ℕ} (hn : 1 ≤ n)
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L)) :
    radixMinAlpha 3 (radixSieveRun 3 (3 ^ n) p L) ≥ radixMinAlpha 3 L + p := by
  induction p with
  | zero =>
    rw [radixSieveRun]
    omega
  | succ p ih =>
    have hcond := hp p (by omega)
    have hstep : radixMinAlpha 3 (radixPeriodStep 3 (3 ^ n) (radixSieveRun 3 (3 ^ n) p L))
        ≥ radixMinAlpha 3 (radixSieveRun 3 (3 ^ n) p L) + 1 :=
      radixPeriodStep_minAlpha hcond.productive
    rw [radixSieveRun_succ]
    have hprev : radixMinAlpha 3 (radixSieveRun 3 (3 ^ n) p L) ≥ radixMinAlpha 3 L + p :=
      ih (fun q hq => hp q (by omega))
    omega

theorem radixSieve_value_lower (n p : ℕ) {L : List ℕ} (hn : 1 ≤ n)
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L)) :
    radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L) ≥ radixListValue 3 n L - (p : ℝ) := by
  induction p with
  | zero =>
    rw [radixSieveRun]
    linarith
  | succ p ih =>
    have hcond := hp p (by omega)
    obtain ⟨m, ham, hm, hgreedy⟩ := hcond.shared
    have hattr : radixPeriodAttrition 3 n
        (radixMinAlphaSublist 3 (radixSieveRun 3 (3 ^ n) p L)) ≤ 1 :=
      radixPeriodAttrition_le_one hn hcond.bound hcond.nonzero hcond.nodup hcond.states
        ham hgreedy hm
    have hstep : radixListValue 3 n (radixPeriodStep 3 (3 ^ n) (radixSieveRun 3 (3 ^ n) p L))
        ≥ radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L)
          - radixPeriodAttrition 3 n (radixMinAlphaSublist 3 (radixSieveRun 3 (3 ^ n) p L)) :=
      radixListValue_step_lower 3 n (3 ^ n) (radixSieveRun 3 (3 ^ n) p L)
    rw [radixSieveRun_succ]
    have hprev : radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L)
        ≥ radixListValue 3 n L - (p : ℝ) := ih (fun q hq => hp q (by omega))
    have h1 : radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L) - 1
        ≤ radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L)
          - radixPeriodAttrition 3 n (radixMinAlphaSublist 3 (radixSieveRun 3 (3 ^ n) p L)) := by
      linarith
    have hp1 : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
    linarith

theorem radixInitialValue_ge (n : ℕ) (hn : 1 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < 3 ^ n) (hlen : L.length = radixFreshRecords n) :
    (n : ℝ) ≤ radixListValue 3 n L := by
  have hfloor : (⌊(n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))⌋₊ : ℝ)
      ≤ (n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))) := by
    have h := Nat.floor_le (by positivity :
      (0:ℝ) ≤ (n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))))
    exact_mod_cast h
  have hceil : (n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))
      < (⌊(n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))⌋₊ : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ))))
    exact_mod_cast h
  have hthree : Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))
      = (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
  have hrec0 : (n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))
      ≤ (radixFreshRecords n : ℝ) := by
    have h1 : (radixFreshRecords n : ℝ)
        = (⌊(n : ℝ) * Real.exp ((Real.log 3) * Real.sqrt (2 * (n : ℝ)))⌋₊ : ℝ) + 1 := by
      simp [radixFreshRecords]
    rw [h1]
    linarith
  have hrec : (n : ℝ) * (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) ≤ (radixFreshRecords n : ℝ) := by
    rw [hthree] at hrec0
    exact hrec0
  have hsub : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have hsqrt : Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hper : (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ))))
      ≤ (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    linarith
  have hexp : Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))
      = (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  have h1 := radixListValue_ge 3 n (by norm_num) hn L hL
  rw [hexp, hlen] at h1
  have hnonneg : 0 ≤ (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hnonneg' : 0 ≤ (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hrec' : (radixFreshRecords n : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ))))
      ≤ (radixFreshRecords n : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * ((n - 1 : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left hper (by positivity)
  have hmul : (n : ℝ) ≤ (radixFreshRecords n : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ)))) := by
    have hab : (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ)))) = 1 := by
      have hexp1 : (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ))
          = Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))) :=
        Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3) (Real.sqrt (2 * (n : ℝ)))
      have hexp2 : (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ))))
          = Real.exp (Real.log 3 * (-(Real.sqrt (2 * (n : ℝ))))) :=
        Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3) (-(Real.sqrt (2 * (n : ℝ))))
      have hz : Real.log 3 * Real.sqrt (2 * (n : ℝ))
          + Real.log 3 * (-(Real.sqrt (2 * (n : ℝ)))) = 0 := by ring
      rw [hexp1, hexp2, ← Real.exp_add, hz, Real.exp_zero]
    have hstep : (n : ℝ) * ((3 : ℝ) ^ Real.sqrt (2 * (n : ℝ))
        * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ)))))
        ≤ (radixFreshRecords n : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ)))) := by
      have h := mul_le_mul_of_nonneg_right hrec hnonneg'
      simpa only [mul_assoc] using! h
    calc (n : ℝ) = (n : ℝ) * 1 := by ring
      _ = (n : ℝ) * ((3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ))))) := by
        rw [hab]
      _ ≤ (radixFreshRecords n : ℝ) * (3 : ℝ) ^ (-(Real.sqrt (2 * (n : ℝ)))) := hstep
  linarith

private theorem radix_listValue_eq_card_of_final (n : ℕ) (hn : 1 ≤ n)
    {L : List ℕ} (hbound : ∀ k ∈ L, k < 3 ^ n) (hfin : ∀ k ∈ L, radixFinalTest 3 n k) :
    radixListValue 3 n L = (L.length : ℝ) := by
  induction L with
  | nil => simp [radixListValue]
  | cons k L ih =>
    have hk1 : radixValue 3 n k = 1 :=
      (radixFinalValue 3 n k (by norm_num) hn (hbound k (by simp)) (by
        have := hfin k (by simp)
        exact this.2)).mpr (hfin k (by simp))
    have hrest : ∀ j ∈ L, j < 3 ^ n := fun j hj => hbound j (by simp [hj])
    have hfinrest : ∀ j ∈ L, radixFinalTest 3 n j := fun j hj => hfin j (by simp [hj])
    have h2 := ih hrest hfinrest
    have hsum : radixListValue 3 n (k :: L) = radixValue 3 n k + radixListValue 3 n L := by
      simp only [radixListValue, List.map_cons, List.sum_cons]
    have hlen : ((k :: L).length : ℝ) = (L.length : ℝ) + 1 := by
      simp only [List.length_cons]
      push_cast
      ring
    rw [hsum, hk1, h2, hlen]
    ring

theorem radixSieve_final_states_of_value (n p : ℕ) (hn : 1 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < 3 ^ n) (hinit : (n : ℝ) ≤ radixListValue 3 n L)
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L))
    (hfinal : ∀ k ∈ radixSieveRun 3 (3 ^ n) p L, radixFinalTest 3 n k) :
    1 ≤ (radixSieveRun 3 (3 ^ n) p L).length := by
  have hne : radixSieveRun 3 (3 ^ n) p L ≠ [] := by
    apply radixSieveRun_ne_nil n p hp
    intro hcon
    have hz : L.length = 0 := by simpa using! hcon
    have hz' : (0 : ℝ) ≤ radixListValue 3 n L := by
      have h1 : (0 : ℝ) ≤ (L.length : ℝ) * Real.exp (-(Real.log 3) * Real.sqrt (2 * ((n - 1 : ℕ) : ℝ))) :=
        by positivity
      have h2 := radixListValue_ge 3 n (by norm_num) hn L hL
      linarith
    have h3 : (n : ℝ) ≤ radixListValue 3 n L := hinit
    have hz'' : radixListValue 3 n L = 0 := by
      rw [hcon]
      simp [radixListValue]
    have hn' : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hval : 1 ≤ radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L) := by
    have hv := radixSieve_value_lower n p hn hp
    have hprog := radixSieveRun_minAlpha n p hn hp
    have hαle : radixMinAlpha 3 (radixSieveRun 3 (3 ^ n) p L) ≤ n - 1 := by
      have hall : ∀ k ∈ radixSieveRun 3 (3 ^ n) p L, radixAlpha 3 k ≤ n - 1 := by
        intro k hk
        have hklt : k < 3 ^ n := radixSieveRun_labels_lt 3 (3 ^ n) (by positivity) hL p k hk
        exact radixAlpha_le 3 n k (by norm_num) hn hklt
      obtain ⟨k, hk⟩ := List.exists_mem_of_ne_nil _ hne
      exact le_trans (radixMinAlpha_le 3 _ k hk) (hall k hk)
    have hp' : p + 1 ≤ n := by omega
    have hp'' : (p : ℝ) ≤ (n : ℝ) - 1 := by
      have h2 : ((p + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp'
      rw [Nat.cast_add, Nat.cast_one] at h2
      linarith
    linarith
  have hcard : radixListValue 3 n (radixSieveRun 3 (3 ^ n) p L)
      = (radixSieveRun 3 (3 ^ n) p L).length := by
    apply radix_listValue_eq_card_of_final n hn
    · intro k hk
      exact radixSieveRun_labels_lt 3 (3 ^ n) (by positivity) hL p k hk
    · exact hfinal
  have hval' : 1 ≤ ((radixSieveRun 3 (3 ^ n) p L).length : ℝ) := by
    have h := hval
    rw [hcard] at h
    exact h
  exact_mod_cast hval'

theorem radixSieve_final_states (n p : ℕ) (hn : 1 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < 3 ^ n) (hlen : L.length = radixFreshRecords n)
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L))
    (hfinal : ∀ k ∈ radixSieveRun 3 (3 ^ n) p L, radixFinalTest 3 n k) :
    1 ≤ (radixSieveRun 3 (3 ^ n) p L).length := by
  exact radixSieve_final_states_of_value n p hn hL (radixInitialValue_ge n hn hL hlen) hp hfinal

theorem radixFinalStateLabel_lt (r n a : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (ha : a < r) :
    radixFinalStateLabel r n a < r ^ n := by
  have h1 : 0 < r ^ (n - 1) := Nat.pow_pos (by omega : 0 < r)
  calc a * r ^ (n - 1) < r * r ^ (n - 1) := (Nat.mul_lt_mul_right h1).2 ha
    _ = r ^ n := by
      rw [← Nat.pow_succ']
      congr 1
      omega

theorem radixFinalStateLabel_spec (r n a : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (ha : 0 < a)
    (ha' : a < r) :
    radixFinalTest r n (radixFinalStateLabel r n a) ∧ radixFinalStateLabel r n a < r ^ n := by
  have h1 : 0 < r ^ (n - 1) := Nat.pow_pos (by omega : 0 < r)
  refine ⟨⟨?_, ?_⟩, radixFinalStateLabel_lt r n a hr hn ha'⟩
  · show r ^ (n - 1) ∣ a * r ^ (n - 1)
    rw [Nat.mul_comm]
    exact Nat.dvd_mul_right (r ^ (n - 1)) a
  · show a * r ^ (n - 1) ≠ 0
    exact Nat.ne_of_gt (Nat.mul_pos ha h1)

theorem radixFinalIndex_final (r n a : ℕ) (hr : 2 ≤ r) (ha : a < r) :
    radixFinalIndex r n (radixFinalStateLabel r n a) = a := by
  have h1 : 0 < r ^ (n - 1) := Nat.pow_pos (by omega : 0 < r)
  have h2 : (a * r ^ (n - 1)) / r ^ (n - 1) = a := by
    rw [show a * r ^ (n - 1) = r ^ (n - 1) * a by ring]
    exact Nat.mul_div_right a h1
  show (radixFinalStateLabel r n a / r ^ (n - 1)) % r = a
  rw [radixFinalStateLabel, h2, Nat.mod_eq_of_lt ha]

theorem radixFinalState_iff (r n k : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n) :
    radixFinalTest r n k ↔ ∃ a : ℕ, 0 < a ∧ a < r ∧ k = radixFinalStateLabel r n a := by
  constructor
  · rintro ⟨hdv, hne⟩
    obtain ⟨b, hb, hk⟩ := radixFinalLabel r n k hr hn hk hdv
    have hb0 : 0 < b := by
      by_contra hcon
      have hbz : b = 0 := Nat.eq_zero_of_not_pos hcon
      have hkz : k = 0 := by rw [hk, hbz]; simp
      exact hne hkz
    refine ⟨b, hb0, hb, ?_⟩
    rw [hk]
    rfl
  · rintro ⟨a, ha0, _, rfl⟩
    have h1 : 0 < r ^ (n - 1) := Nat.pow_pos (by omega : 0 < r)
    refine ⟨?_, ?_⟩
    · show r ^ (n - 1) ∣ a * r ^ (n - 1)
      rw [Nat.mul_comm]
      exact Nat.dvd_mul_right (r ^ (n - 1)) a
    · show a * r ^ (n - 1) ≠ 0
      exact Nat.ne_of_gt (Nat.mul_pos ha0 h1)

theorem radixPhaseIndex_final (r n s a : ℕ) (hr : 2 ≤ r) :
    radixPhaseIndex r n s (radixFinalStateLabel r n a) = (s * a) % r := by
  have h1 : 0 < r ^ (n - 1) := Nat.pow_pos (by omega : 0 < r)
  have h2 : (s * (a * r ^ (n - 1))) / r ^ (n - 1) = s * a := by
    rw [show s * (a * r ^ (n - 1)) = s * a * r ^ (n - 1) by ring]
    rw [show s * a * r ^ (n - 1) = r ^ (n - 1) * (s * a) by ring]
    exact Nat.mul_div_right (s * a) h1
  show ((s * radixFinalStateLabel r n a) / r ^ (n - 1)) % r = (s * a) % r
  rw [radixFinalStateLabel, h2]

private theorem radix_finalPhaseVal (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (s a : ℕ) :
    (s * (a * r ^ (n - 1))) % r ^ n = ((s * a) % r) * r ^ (n - 1) := by
  have h1 : 0 < r ^ (n - 1) := Nat.pow_pos (by omega : 0 < r)
  have hrpow : r * r ^ (n - 1) = r ^ n := by
    have h := Nat.pow_succ' (m := r) (n := n - 1)
    rw [show Nat.succ (n - 1) = n by omega] at h
    exact h.symm
  have hmul : s * (a * r ^ (n - 1))
      = (s * a / r) * r ^ n + ((s * a) % r) * r ^ (n - 1) := by
    have hdecomp : s * a = r * (s * a / r) + (s * a) % r := (Nat.div_add_mod (s * a) r).symm
    calc s * (a * r ^ (n - 1)) = (s * a) * r ^ (n - 1) := by ring
      _ = (r * (s * a / r) + (s * a) % r) * r ^ (n - 1) := by
        conv_lhs => rw [hdecomp]
      _ = (s * a / r) * r ^ n + ((s * a) % r) * r ^ (n - 1) := by
        calc (r * (s * a / r) + (s * a) % r) * r ^ (n - 1)
            = (s * a / r) * (r * r ^ (n - 1)) + (s * a % r) * r ^ (n - 1) := by ring
          _ = (s * a / r) * r ^ n + (s * a % r) * r ^ (n - 1) := by rw [hrpow]
  have ht : ((s * a) % r) * r ^ (n - 1) < r ^ n := by
    calc ((s * a) % r) * r ^ (n - 1) < r * r ^ (n - 1) :=
        (Nat.mul_lt_mul_right h1).2 (Nat.mod_lt _ (by omega : 0 < r))
      _ = r ^ n := hrpow
  have hq : (s * a / r) * r ^ n % r ^ n = 0 :=
    Nat.mod_eq_zero_of_dvd (by rw [Nat.mul_comm]; exact dvd_mul_right (r ^ n) (s * a / r))
  rw [hmul]
  rw [Nat.add_mod, hq, Nat.zero_add]
  have hBlt : ((s * a) % r) * r ^ (n - 1) % r ^ n < r ^ n := Nat.mod_lt_of_lt ht
  rw [Nat.mod_eq_of_lt hBlt, Nat.mod_eq_of_lt ht]

private theorem radix_finalPhaseReal (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (s a : ℕ) :
    ((((s * a) % r) * r ^ (n - 1) : ℕ) : ℝ) / (r : ℝ) ^ n
      = (((s * a) % r : ℕ) : ℝ) / r := by
  have hnpow : r ^ (n - 1) * r = r ^ n := by
    have h := Nat.pow_succ' (m := r) (n := n - 1)
    rw [show Nat.succ (n - 1) = n by omega] at h
    rw [Nat.mul_comm] at h
    exact h.symm
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hN0 : (r : ℝ) ^ n ≠ 0 := by positivity
  rw [div_eq_iff hN0]
  have hpow : (r ^ (n - 1) : ℝ) * r = (r : ℝ) ^ n := by
    rw [← Nat.cast_pow]
    exact_mod_cast hnpow
  calc ((((s * a) % r) * r ^ (n - 1) : ℕ) : ℝ) = (((s * a) % r : ℕ) : ℝ) * (r ^ (n - 1) : ℝ) := by
        norm_cast
    _ = (((s * a) % r : ℕ) : ℝ) / r * ((r ^ (n - 1) : ℝ) * r) := by
      have hcancel : (((s * a) % r : ℕ) : ℝ) / r * r = (((s * a) % r : ℕ) : ℝ) := by
        field_simp
      calc (((s * a) % r : ℕ) : ℝ) * (r ^ (n - 1) : ℝ)
          = ((((s * a) % r : ℕ) : ℝ) / r * r) * (r ^ (n - 1) : ℝ) := by rw [hcancel]
          _ = (((s * a) % r : ℕ) : ℝ) / r * (r * (r ^ (n - 1) : ℝ)) := by ring
          _ = (((s * a) % r : ℕ) : ℝ) / r * ((r ^ (n - 1) : ℝ) * r) := by ring
    _ = (((s * a) % r : ℕ) : ℝ) / r * (r : ℝ) ^ n := by rw [hpow]

theorem radixFinalPhase (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    (s : ZMod (r ^ n)) (a : ℕ) (ha : a < r) :
    dihedralQubitPhase (r ^ n) s ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n))
      = radixRootOfUnity r ((s.val * a) % r) := by
  have hklt : radixFinalStateLabel r n a < r ^ n := radixFinalStateLabel_lt r n a hr hn ha
  have hkval : ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n)).val
      = radixFinalStateLabel r n a := ZMod.val_natCast_of_lt hklt
  have hval : (s * ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n))).val
      = ((s.val * a) % r) * r ^ (n - 1) := by
    rw [ZMod.val_mul, hkval, radixFinalStateLabel]
    exact radix_finalPhaseVal r n hr hn s.val a
  have hdiv : ((s * ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n))).val : ℝ)
      / (r : ℝ) ^ n = ((((s.val * a) % r) : ℕ) : ℝ) / r := by
    rw [hval]
    exact radix_finalPhaseReal r n hr hn s.val a
  rw [dihedralQubitPhase]
  unfold radixRootOfUnity
  apply congrArg Complex.exp
  apply congrArg (fun z : ℂ => z * Complex.I)
  apply congrArg (fun z : ℝ => (z : ℂ))
  apply congrArg (fun z : ℝ => 2 * Real.pi * z)
  simpa only [Nat.cast_pow] using! hdiv

theorem radixShiftCandidates_spec (r : ℕ) [NeZero r] (a t : ℕ) (u : ZMod r) :
    u ∈ radixShiftCandidates r a t ↔ u * (a : ZMod r) = (t : ZMod r) := by
  simp [radixShiftCandidates]

theorem radixShiftCandidates_sound (r n : ℕ) [NeZero r] (hr : 2 ≤ r)
    (s : ℕ) (a : ℕ) :
    (s % r : ZMod r) ∈ radixShiftCandidates r a
      (radixPhaseIndex r n s (radixFinalStateLabel r n a)) := by
  rw [radixShiftCandidates_spec]
  have hphase : radixPhaseIndex r n s (radixFinalStateLabel r n a) = (s * a) % r :=
    radixPhaseIndex_final r n s a hr
  rw [hphase]
  calc (s % r : ZMod r) * (a : ZMod r) = ((s : ZMod r) * (a : ZMod r)) := by
        rw [ZMod.natCast_mod s r]
    _ = (((s * a : ℕ) : ZMod r)) := by norm_cast
    _ = (((s * a) % r : ℕ) : ZMod r) := by rw [← ZMod.natCast_mod (s * a) r]

theorem radixReadout_correct (r n : ℕ) [NeZero r] (hr : 2 ≤ r)
    (s : ℕ) (a : ℕ) (hunit : IsUnit (a : ZMod r)) :
    radixReadout r a (radixPhaseIndex r n s (radixFinalStateLabel r n a))
      = (s % r : ZMod r) := by
  have hphase : radixPhaseIndex r n s (radixFinalStateLabel r n a) = (s * a) % r :=
    radixPhaseIndex_final r n s a hr
  rw [radixReadout, hphase]
  have hmul : (((s * a) % r : ℕ) : ZMod r) = (s % r : ZMod r) * (a : ZMod r) := by
    calc (((s * a) % r : ℕ) : ZMod r) = (((s * a : ℕ) : ZMod r)) := by
          rw [← ZMod.natCast_mod (s * a) r]
      _ = ((s : ZMod r) * (a : ZMod r)) := by norm_cast
      _ = ((s % r : ZMod r) * (a : ZMod r)) := by rw [ZMod.natCast_mod s r]
  rw [hmul, mul_assoc, ZMod.mul_inv_of_unit (a : ZMod r) hunit]
  simp

theorem radixTerminalReadout (r n : ℕ) [NeZero r] (hr : 2 ≤ r)
    (s : ZMod (r ^ n)) (k : ℕ) (a : ℕ) (ha : k = radixFinalStateLabel r n a)
    (hunit : IsUnit (a : ZMod r)) :
    radixReadout r a (radixPhaseIndex r n s.val k) = (s.val % r : ZMod r) := by
  have hcorrect := radixReadout_correct r n hr s.val a hunit
  rw [← ha] at hcorrect
  exact hcorrect

theorem radixFinalIndex_unit_of_prime (r a : ℕ) (hr : r.Prime) (ha : 0 < a)
    (ha' : a < r) : IsUnit (a : ZMod r) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.coprime_comm.mp (hr.coprime_iff_not_dvd.mpr (by
    intro hd
    have hle : r ≤ a := Nat.le_of_dvd (by omega : 0 < a) hd
    omega))

theorem radixRunTerminalReadout (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hrp : r.Prime) (s : ZMod (r ^ n)) (k : ℕ) (hk : radixFinalTest r n k)
    (hklt : k < r ^ n) :
    ∃ a : ℕ, 0 < a ∧ a < r ∧ k = radixFinalStateLabel r n a ∧
      radixFinalIndex r n k = a ∧
      radixReadout r a (radixPhaseIndex r n s.val k) = (s.val % r : ZMod r) := by
  obtain ⟨a, ha0, ha1, hka⟩ := (radixFinalState_iff r n k hr hn hklt).mp hk
  refine ⟨a, ha0, ha1, hka, ?_, ?_⟩
  · rw [hka]
    exact radixFinalIndex_final r n a hr ha1
  · have hunit : IsUnit (a : ZMod r) := radixFinalIndex_unit_of_prime r a hrp ha0 ha1
    exact radixTerminalReadout r n hr s k a hka hunit

theorem radixLevelDigit_mod : ∀ (r s j : ℕ),
    radixLevelDigit r s j = ((radixLevelSlope r s j) % r : ZMod r) := by
  intro r s j
  revert s
  induction j with
  | zero =>
    intro s
    rfl
  | succ j ih =>
    intro s
    show radixLevelDigit r (s / r) j = ((radixLevelSlope r (s / r) j) % r : ZMod r)
    exact ih (s / r)

theorem radixLevelSlope_succ (r s j : ℕ) :
    radixLevelSlope r s (Nat.succ j) = radixLevelSlope r (s / r) j := rfl

theorem radixLevelDigit_succ (r s j : ℕ) :
    radixLevelDigit r s (Nat.succ j) = radixLevelDigit r (s / r) j := rfl

theorem radixReadouts_cons (r n s : ℕ) :
    radixReadouts r (Nat.succ n) s = radixLevelDigit r s 0 :: radixReadouts r n (s / r) := rfl

theorem radixReadouts_length : ∀ (r n s : ℕ), (radixReadouts r n s).length = n := by
  intro r n
  induction n with
  | zero =>
    intro s
    rfl
  | succ n ih =>
    intro s
    simp [radixReadouts, ih (s / r)]

theorem radixReadoutValue_reassemble : ∀ (r n s : ℕ) (_hr : 2 ≤ r),
    s < r ^ n → radixReadoutValue r (radixReadouts r n s) = s := by
  intro r n
  induction n with
  | zero =>
    intro s hr hs
    have hz : s = 0 := by
      have hlt : s < 1 := by simpa using! hs
      omega
    subst hz
    rfl
  | succ n ih =>
    intro s hr hs
    have hdiv : s / r < r ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < r)]
      have hpow : r ^ n * r = r ^ (n + 1) := by rw [Nat.pow_succ]
      rw [hpow]
      exact hs
    have hrec := ih (s / r) hr hdiv
    have hval : (radixLevelDigit r s 0).val = s % r := by
      show ((s % r : ℕ) : ZMod r).val = s % r
      exact ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega : 0 < r))
    show (radixLevelDigit r s 0).val + r * radixReadoutValue r (radixReadouts r n (s / r)) = s
    rw [hval, hrec]
    have hdm : s % r + r * (s / r) = s := by
      calc s % r + r * (s / r) = r * (s / r) + s % r := by rw [Nat.add_comm]
        _ = s := Nat.div_add_mod s r
    exact hdm

theorem radixLevelReadout (r n : ℕ) [NeZero r] (hr : 2 ≤ r)
    (s : ℕ) (j : ℕ) (a : ℕ) (hunit : IsUnit (a : ZMod r)) :
    radixLevelDigit r s j
      = radixReadout r a (radixPhaseIndex r (n - j) (radixLevelSlope r s j)
          (radixFinalStateLabel r (n - j) a)) := by
  have hrec := radixReadout_correct r (n - j) hr (radixLevelSlope r s j) a hunit
  rw [hrec, radixLevelDigit_mod]

theorem radixRecursion_recovers (r n : ℕ) [NeZero r] (hr : 2 ≤ r)
    (s : ℕ) (hs : s < r ^ n) :
    radixReadoutValue r (radixReadouts r n s) = s ∧
      (∀ j : ℕ, j < n → ∀ a : ℕ, IsUnit (a : ZMod r) →
        radixLevelDigit r s j
          = radixReadout r a (radixPhaseIndex r (n - j) (radixLevelSlope r s j)
              (radixFinalStateLabel r (n - j) a))) := by
  refine ⟨radixReadoutValue_reassemble r n s hr hs, ?_⟩
  intro j hj a hunit
  exact radixLevelReadout r n hr s j a hunit

noncomputable def radixLevelRecords (n j : ℕ) : ℕ := radixFreshRecords (n - j)

noncomputable def radixRecursionRecords (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, radixLevelRecords n j

theorem radixLevelRecords_le (r n j : ℕ) (hj : j < n) :
    (radixLevelRecords n j : ℝ) ≤ (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) := by
  have hmj : 1 ≤ n - j := by omega
  have hle : n - j ≤ n := Nat.sub_le _ _
  have h1 := radixBudgetLedger_queries_le r (n - j) hmj
  have hq : (radixBudgetLedger r (n - j)).queries = radixFreshRecords (n - j) := rfl
  rw [hq] at h1
  have hsqrt : Real.sqrt (2 * ((n - j : ℕ) : ℝ)) ≤ Real.sqrt (2 * (n : ℝ)) := by
    gcongr
  have hexp : (3 : ℝ) ^ Real.sqrt (2 * ((n - j : ℕ) : ℝ))
      ≤ (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hsqrt
  show (radixFreshRecords (n - j) : ℝ) ≤ _
  calc (radixFreshRecords (n - j) : ℝ)
      ≤ (3 : ℝ) ^ Real.sqrt (2 * ((n - j : ℕ) : ℝ)) * (((n - j : ℕ) : ℝ) + 1) := h1
    _ ≤ (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) := by
      gcongr

theorem radixRecursionRecords_le (r n : ℕ) (hn : 1 ≤ n) :
    (radixRecursionRecords n : ℝ)
      ≤ (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2 := by
  have hcast : (radixRecursionRecords n : ℝ)
      = ∑ j ∈ Finset.range n, (radixLevelRecords n j : ℝ) := by
    rw [radixRecursionRecords]
    exact_mod_cast Finset.sum_congr rfl (fun j _ => rfl)
  rw [hcast]
  calc (∑ j ∈ Finset.range n, (radixLevelRecords n j : ℝ))
      ≤ ∑ _ ∈ Finset.range n, (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) := by
        gcongr with j hj
        exact radixLevelRecords_le r n j (by simpa using! hj)
    _ = ((Finset.range n).card : ℝ) * ((3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1)) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
    _ ≤ (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2 := by
        rw [Finset.card_range]
        have hpos : 0 ≤ (3 : ℝ) ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) := by positivity
        nlinarith

noncomputable def radixBudgetConstant (r : ℕ) : ℝ :=
  1000 * (1 + 2 * (Real.log r / Real.log 2 + 1) / (Real.log 2 * Real.log 3 ^ 3))

noncomputable def radixRecursionLedger (r n : ℕ) : RecoveryLedger where
  samples := radixRecursionRecords n
  queries := radixRecursionRecords n
  macros := 2 * radixRecursionRecords n
  measurements := 2 * radixRecursionRecords n
  comparisons := sortCompareSteps (radixRecursionRecords n)
  bitOps := sortBitOps (radixRecursionRecords n) (labelBits (r ^ n))
  integerBits := labelBits (r ^ n)
  workspaceBits := workspaceBits (radixFreshRecords n) (labelBits (r ^ n))

noncomputable def radixLevelTrials (n j : ℕ) : ℕ := 1000 * (n - j + 1)

noncomputable def radixAmplifiedRecords (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, radixLevelTrials n j * radixLevelRecords n j

noncomputable def radixAmplifiedLedger (r n : ℕ) : RecoveryLedger where
  samples := radixAmplifiedRecords n
  queries := radixAmplifiedRecords n
  macros := 2 * radixAmplifiedRecords n
  measurements := 2 * radixAmplifiedRecords n
  comparisons := sortCompareSteps (radixAmplifiedRecords n)
  bitOps := sortBitOps (radixAmplifiedRecords n) (labelBits (r ^ n))
  integerBits := labelBits (r ^ n)
  workspaceBits := workspaceBits (radixFreshRecords n) (labelBits (r ^ n))

private theorem radix_natLog2_le (x : ℕ) : (Nat.log2 x : ℝ) ≤ Real.log x / Real.log 2 := by
  have h : Nat.log2 x ≤ Real.logb 2 x := Real.log2_le_logb x
  rw [Real.logb] at h
  exact h

private theorem radix_natLog2_add_one_le (x : ℕ) (hx : 1 ≤ x) :
    (Nat.log2 x : ℝ) + 1 ≤ 2 * Real.log ((x + 1 : ℕ) : ℝ) / Real.log 2 := by
  have h := radix_natLog2_le x
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxp : (0:ℝ) < (x:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hx)
  have hsp : (0:ℝ) < ((x + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_succ x)
  have hle : (x:ℝ) ≤ ((x + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_succ x)
  have hmain : Real.log (x : ℝ) ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hxp hsp hle
  have hone : 1 ≤ Real.log ((x + 1 : ℕ) : ℝ) / Real.log 2 := by
    have h2le : (2:ℝ) ≤ ((x + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (show 2 ≤ x + 1 by omega)
    have h1 := Real.strictMonoOn_log.monotoneOn (a := 2) (b := ((x + 1 : ℕ) : ℝ))
      (by norm_num) hsp h2le
    calc 1 = Real.log 2 / Real.log 2 := by field_simp
      _ ≤ Real.log ((x + 1 : ℕ) : ℝ) / Real.log 2 :=
        div_le_div_of_nonneg_right h1 (le_of_lt hpos)
  have hmul : ((Nat.log2 x : ℝ) + 1) * Real.log 2
      ≤ 2 * Real.log ((x + 1 : ℕ) : ℝ) := by
    have h1 : (Nat.log2 x : ℝ) * Real.log 2 ≤ Real.log (x : ℝ) := by
      calc (Nat.log2 x : ℝ) * Real.log 2
          ≤ (Real.log (x : ℝ) / Real.log 2) * Real.log 2 :=
            mul_le_mul_of_nonneg_right h (le_of_lt hpos)
        _ = Real.log (x : ℝ) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
    have h2 : (1:ℝ) * Real.log 2 ≤ Real.log ((x + 1 : ℕ) : ℝ) := by
      have hone' := hone
      rw [le_div_iff₀ hpos] at hone'
      exact hone'
    calc ((Nat.log2 x : ℝ) + 1) * Real.log 2
        = (Nat.log2 x : ℝ) * Real.log 2 + 1 * Real.log 2 := by ring
      _ ≤ Real.log (x : ℝ) + Real.log ((x + 1 : ℕ) : ℝ) := add_le_add h1 h2
      _ ≤ 2 * Real.log ((x + 1 : ℕ) : ℝ) := by linarith
  apply (le_div_iff₀ hpos).2
  exact hmul

private theorem radix_labelBits_le (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    (labelBits (r ^ n) : ℝ) ≤ (n : ℝ) * (Real.log r / Real.log 2 + 1) := by
  have h1 := radix_natLog2_le (r ^ n)
  have h2 : Real.log (↑(r ^ n) : ℝ) / Real.log 2
      = (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2) := by
    have heq : ((r ^ n : ℕ) : ℝ) = (r : ℝ) ^ n := by rw [Nat.cast_pow]
    rw [heq, Real.log_pow]
    ring
  rw [h2] at h1
  have h3 : (0:ℝ) ≤ Real.log (↑r : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by simpa using! (Nat.cast_le.mpr hr)))
      (le_of_lt (Real.log_pos (by norm_num)))
  unfold labelBits
  rw [Nat.cast_add]
  push_cast
  have h4 : (Nat.log2 (r ^ n) : ℝ) + 1 ≤ (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2) + 1 := by
    linarith
  calc (Nat.log2 (r ^ n) : ℝ) + 1 ≤ (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2) + 1 := h4
    _ ≤ (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) := by
      have hn1 : (1:ℝ) ≤ (n : ℝ) := by simpa using! (Nat.cast_le.mpr hn)
      have hmul := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
      rw [mul_add]
      linarith

private theorem radix_freshRecords_gt (n : ℕ) :
    (n : ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))) < radixFreshRecords n := by
  have h := Nat.lt_floor_add_one
    ((n : ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))))
  simpa [radixFreshRecords] using! h

private theorem radix_recursionRecords_ge (n : ℕ) (hn : 1 ≤ n) :
    radixFreshRecords n ≤ radixRecursionRecords n := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  calc radixFreshRecords n = radixLevelRecords n 0 := rfl
    _ ≤ ∑ j ∈ Finset.range n, radixLevelRecords n j := by
      refine Finset.single_le_sum (fun j _ => Nat.zero_le _) h0
    _ = radixRecursionRecords n := rfl

private theorem radix_log_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.log 3 * Real.sqrt (2 * (n : ℝ)) ≤ Real.log ((radixRecursionRecords n : ℝ) + 2) := by
  have hgt : (n : ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ)))
      < radixFreshRecords n := radix_freshRecords_gt n
  have hge : radixFreshRecords n ≤ radixRecursionRecords n :=
    radix_recursionRecords_ge n hn
  have hLpos : 0 < radixRecursionRecords n := by
    have hfr : 0 < radixFreshRecords n := by
      unfold radixFreshRecords
      omega
    omega
  have hpos : (0:ℝ) < (n:ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))) := by
    positivity
  have hnp : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hlt : (n:ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ)))
      < ((radixRecursionRecords n : ℝ) + 2) := by
    have h2 : ((radixRecursionRecords n : ℕ) : ℝ) + 2 > (radixFreshRecords n : ℝ) := by
      have hge' : (radixFreshRecords n : ℝ) ≤ (radixRecursionRecords n : ℝ) :=
        Nat.cast_le.mpr hge
      linarith
    linarith
  have hpos2 : (0:ℝ) < ((radixRecursionRecords n : ℕ) : ℝ) + 2 := by
    have hLpos' : (0:ℝ) < ((radixRecursionRecords n : ℕ) : ℝ) := by
      exact_mod_cast hLpos
    linarith
  have hlog : Real.log ((n:ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))))
      ≤ Real.log ((radixRecursionRecords n : ℝ) + 2) :=
    Real.strictMonoOn_log.monotoneOn hpos hpos2 (le_of_lt hlt)
  have hmul : Real.log ((n:ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))))
      = Real.log (n : ℝ) + Real.log 3 * Real.sqrt (2 * (n : ℝ)) := by
    calc Real.log ((n:ℝ) * Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ))))
        = Real.log (n : ℝ) + Real.log (Real.exp (Real.log 3 * Real.sqrt (2 * (n : ℝ)))) := by
          rw [Real.log_mul (ne_of_gt hnp) (Real.exp_ne_zero _)]
      _ = Real.log (n : ℝ) + Real.log 3 * Real.sqrt (2 * (n : ℝ)) := by rw [Real.log_exp]
  rw [hmul] at hlog
  have hnlog : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    simpa using! (Nat.cast_le.mpr hn)
  linarith

theorem radix_budgetConstant_pos (r : ℕ) (hr : 1 ≤ r) :
    1 ≤ radixBudgetConstant r := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h5 : (0:ℝ) ≤ Real.log (↑r : ℝ) / Real.log 2 := by
    have h1 : (0:ℝ) ≤ Real.log (↑r : ℝ) :=
      Real.log_nonneg (by simpa using! (Nat.cast_le.mpr hr))
    exact div_nonneg h1 (le_of_lt h2)
  have h6 : (0:ℝ) < 2 * (Real.log (↑r : ℝ) / Real.log 2 + 1)
      / (Real.log 2 * Real.log 3 ^ 3) := by
    have : (0:ℝ) < Real.log (↑r : ℝ) / Real.log 2 + 1 := by linarith
    positivity
  have : (1:ℝ) ≤ 1000 * (1 + 2 * (Real.log (↑r : ℝ) / Real.log 2 + 1)
      / (Real.log 2 * Real.log 3 ^ 3)) := by nlinarith
  exact this

theorem radix_budgetConstant_ge_1000 (r : ℕ) (hr : 1 ≤ r) :
    1000 ≤ radixBudgetConstant r := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h5 : (0:ℝ) ≤ Real.log (↑r : ℝ) / Real.log 2 := by
    have h1 : (0:ℝ) ≤ Real.log (↑r : ℝ) :=
      Real.log_nonneg (by simpa using! (Nat.cast_le.mpr hr))
    exact div_nonneg h1 (le_of_lt h2)
  have h6 : (0:ℝ) < 2 * (Real.log (↑r : ℝ) / Real.log 2 + 1)
      / (Real.log 2 * Real.log 3 ^ 3) := by
    have : (0:ℝ) < Real.log (↑r : ℝ) / Real.log 2 + 1 := by linarith
    positivity
  have : (1000:ℝ) ≤ 1000 * (1 + 2 * (Real.log (↑r : ℝ) / Real.log 2 + 1)
      / (Real.log 2 * Real.log 3 ^ 3)) := by nlinarith
  exact this

theorem radixRecursionLedger_samples_le_queries (r n : ℕ) :
    (radixRecursionLedger r n).samples ≤ (radixRecursionLedger r n).queries := by
  rfl

theorem radixRecursionLedger_comparisons (r n : ℕ) :
    sortCompareSteps (radixRecursionLedger r n).samples ≤ (radixRecursionLedger r n).comparisons := by
  rfl

theorem radixRecursionLedger_bitOps_account (r n : ℕ) :
    sortBitOps (radixRecursionLedger r n).samples (radixRecursionLedger r n).integerBits
      ≤ (radixRecursionLedger r n).bitOps := by
  rfl

theorem radixRecursionLedger_workspace (r n : ℕ) :
    0 < (radixRecursionLedger r n).workspaceBits := by
  have h1 : 0 < radixFreshRecords n := by
    unfold radixFreshRecords
    omega
  have h2 : 0 < labelBits (r ^ n) := by
    unfold labelBits
    omega
  rw [radixRecursionLedger, workspaceBits]
  exact mul_pos h1 (by linarith)

theorem radixRecursionLedger_queries_le (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) :
    ((radixRecursionLedger r n).queries : ℝ)
      ≤ radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
  have hrec := radixRecursionRecords_le r n hn
  have hC : 1 ≤ radixBudgetConstant r := radix_budgetConstant_pos r (by omega)
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 4 := by
    have h0 : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h2 : (0:ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h3 : (0:ℝ) ≤ (n : ℝ) + 1 - 1 := by linarith
    have h1 : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [mul_nonneg h2 h3]
    calc ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ 2 * 1 := by ring
      _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((n : ℝ) + 1) ^ 4 := by ring
  have hX : (0:ℝ) ≤ 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by positivity
  calc ((radixRecursionLedger r n).queries : ℝ)
      = (radixRecursionRecords n : ℝ) := rfl
    _ ≤ 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2 := hrec
    _ ≤ 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_right hC hX
      calc 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4
          = 1 * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4) := by ring
        _ ≤ radixBudgetConstant r * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4) := hmul
        _ = radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by ring

private theorem radix_sortBitOps_shape (L b n : ℕ) (r : ℕ)
    (hr : 1 ≤ r) (hn : 1 ≤ n) (hL : 0 < L)
    (hlog : Real.log 3 * Real.sqrt (n : ℝ) ≤ Real.log ((L : ℝ) + 2))
    (hb : (b : ℝ) ≤ (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1)) :
    (L : ℝ) * ((Nat.log2 (L + 1) : ℝ) + 1) * (b : ℝ)
      ≤ radixBudgetConstant r * (L : ℝ) * (Real.log ((L : ℝ) + 2)) ^ 4 := by
  have hδ : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hγ : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hC : 1 ≤ radixBudgetConstant r := radix_budgetConstant_pos r hr
  have hC0 : (0:ℝ) ≤ radixBudgetConstant r := le_trans (by norm_num) hC
  have hβ : (0:ℝ) ≤ Real.log (↑r : ℝ) / Real.log 2 := by
    have h1 : (0:ℝ) ≤ Real.log (↑r : ℝ) :=
      Real.log_nonneg (by simpa using! (Nat.cast_le.mpr hr))
    exact div_nonneg h1 (le_of_lt hδ)
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by simpa using! (Nat.cast_le.mpr hn)
    have h2 : Real.sqrt 1 ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn1
    simpa using! h2
  have hlogpos : (0:ℝ) < Real.log ((L : ℝ) + 2) := by
    have h1 : Real.log 3 ≤ Real.log 3 * Real.sqrt (n : ℝ) := by
      simpa using! (mul_le_mul_of_nonneg_left hsqrt1 (le_of_lt hγ))
    have h2 : Real.log 3 ≤ Real.log ((L : ℝ) + 2) := le_trans h1 hlog
    exact lt_of_lt_of_le hγ h2

  have hlog3 : (Real.log 3 * Real.sqrt (n : ℝ)) ^ 3 ≤ Real.log ((L : ℝ) + 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hlog 3
  have hlog3' : (Real.log 3 * Real.sqrt (n : ℝ)) ^ 3
      = (Real.log 3) ^ 3 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [mul_pow]
    congr 1
    calc Real.sqrt (n : ℝ) ^ 3 = Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ)) ^ 2 := by
          rw [pow_succ]
          ring
      _ = Real.sqrt (n : ℝ) * (n : ℝ) := by rw [Real.sq_sqrt (by positivity)]
      _ = (n : ℝ) * Real.sqrt (n : ℝ) := by ring
  have hlog3'' : (Real.log 3) ^ 3 * (n : ℝ) ≤ Real.log ((L : ℝ) + 2) ^ 3 := by
    have h1 : (Real.log 3) ^ 3 * (n : ℝ)
        ≤ (Real.log 3) ^ 3 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      have h2 : (0:ℝ) ≤ (Real.log 3) ^ 3 * (n : ℝ) := by positivity
      have h3 : (1:ℝ) ≤ Real.sqrt (n : ℝ) := hsqrt1
      have hmul := mul_le_mul_of_nonneg_left h3 h2
      calc (Real.log 3) ^ 3 * (n : ℝ)
          ≤ (Real.log 3) ^ 3 * (n : ℝ) * Real.sqrt (n : ℝ) := by simpa using! hmul
        _ = (Real.log 3) ^ 3 * ((n : ℝ) * Real.sqrt (n : ℝ)) := by ring
    rw [hlog3'] at hlog3
    exact le_trans h1 hlog3

  have hpay : (2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2)
      ≤ radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 3 := by
    have h1 : radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 3
        ≥ radixBudgetConstant r * (Real.log 3) ^ 3 * (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hlog3'' hC0
      calc radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 3
          ≥ radixBudgetConstant r * ((Real.log 3) ^ 3 * (n : ℝ)) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
        _ = radixBudgetConstant r * (Real.log 3) ^ 3 * (n : ℝ) := by ring
    have h2 : radixBudgetConstant r * (Real.log 3) ^ 3 * (n : ℝ)
        ≥ 2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2 := by
      set u : ℝ := (Real.log (↑r : ℝ) / Real.log 2 + 1) * (n : ℝ) / Real.log 2 with hu
      have hu0 : 0 ≤ u := by
        have hb1 : (0:ℝ) ≤ Real.log (↑r : ℝ) / Real.log 2 + 1 := by linarith
        rw [hu]
        exact div_nonneg (mul_nonneg hb1 (Nat.cast_nonneg n)) (le_of_lt hδ)
      have hA : radixBudgetConstant r * (Real.log 3) ^ 3 * (n : ℝ)
          = 1000 * (Real.log 3) ^ 3 * (n : ℝ) + 2000 * u := by
        unfold radixBudgetConstant
        rw [hu]
        field_simp
        ring
      have hR : 2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2 = 2 * u := by
        rw [hu]
        ring
      rw [hA, hR]
      have h3 : (0:ℝ) ≤ 1000 * (Real.log 3) ^ 3 * (n : ℝ) := by positivity
      linarith
    exact le_trans h2 h1

  have hcmp : (Nat.log2 (L + 1) : ℝ) + 1
      ≤ 2 * Real.log ((L : ℝ) + 2) / Real.log 2 := by
    have hcast : ((L + 2 : ℕ) : ℝ) = (L : ℝ) + 2 := by
      push_cast
      ring
    have h := radix_natLog2_add_one_le (L + 1) (by omega)
    rwa [hcast] at h
  have hA : (0:ℝ) ≤ 2 * Real.log ((L : ℝ) + 2) / Real.log 2 := by
    have := hlogpos
    positivity
  have hb0 : (0:ℝ) ≤ (b : ℝ) := by positivity
  calc (L : ℝ) * ((Nat.log2 (L + 1) : ℝ) + 1) * (b : ℝ)
      = (L : ℝ) * (((Nat.log2 (L + 1) : ℝ) + 1) * (b : ℝ)) := by ring
    _ ≤ (L : ℝ) * ((2 * Real.log ((L : ℝ) + 2) / Real.log 2)
        * ((n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1))) := by
      have hmul := mul_le_mul hcmp hb hb0 hA
      exact mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg L)
    _ ≤ (L : ℝ) * (radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 4) := by
      have hmul : (2 * Real.log ((L : ℝ) + 2) / Real.log 2)
          * ((n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1))
          ≤ radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 4 := by
        have h1 : (2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2)
            * Real.log ((L : ℝ) + 2)
            ≤ radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 4 := by
          have hmul : (2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2)
                * Real.log ((L : ℝ) + 2)
              ≤ radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 3
                  * Real.log ((L : ℝ) + 2) :=
            mul_le_mul_of_nonneg_right hpay (le_of_lt hlogpos)
          calc (2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2)
              * Real.log ((L : ℝ) + 2)
              ≤ radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 3
                  * Real.log ((L : ℝ) + 2) := hmul
            _ = radixBudgetConstant r * Real.log ((L : ℝ) + 2) ^ 4 := by
              rw [pow_succ']
              ring
        have h2 : (2 * Real.log ((L : ℝ) + 2) / Real.log 2)
              * ((n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1))
            = (2 * (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) / Real.log 2)
                * Real.log ((L : ℝ) + 2) := by ring
        rw [h2]
        exact h1
      exact mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg L)
    _ = radixBudgetConstant r * (L : ℝ) * (Real.log ((L : ℝ) + 2)) ^ 4 := by ring

theorem radixRecursionLedger_bitOps_le (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) :
    ((radixRecursionLedger r n).bitOps : ℝ)
      ≤ radixBudgetConstant r * ((radixRecursionLedger r n).queries : ℝ)
          * (Real.log (((radixRecursionLedger r n).queries : ℝ) + 2)) ^ 4 := by
  have hγ : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hLpos : 0 < radixRecursionRecords n := by
    have hge := radix_recursionRecords_ge n hn
    have hfr : 0 < radixFreshRecords n := by
      unfold radixFreshRecords
      omega
    omega
  have hlog : Real.log 3 * Real.sqrt (n : ℝ)
      ≤ Real.log ((radixRecursionRecords n : ℝ) + 2) := by
    have h := radix_log_lower n hn
    have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
      have hle : (n:ℝ) ≤ 2 * (n:ℝ) := by linarith
      exact Real.sqrt_le_sqrt hle
    have hmul := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hγ)
    exact le_trans hmul h
  have hbits : (labelBits (r ^ n) : ℝ) ≤ (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) :=
    radix_labelBits_le r n (by omega) hn
  have hshape := radix_sortBitOps_shape (radixRecursionRecords n) (labelBits (r ^ n)) n r
    (by omega) hn hLpos hlog hbits
  calc ((radixRecursionLedger r n).bitOps : ℝ)
      = (radixRecursionRecords n : ℝ) * ((Nat.log2 (radixRecursionRecords n + 1) : ℝ) + 1)
          * (labelBits (r ^ n) : ℝ) := by
        simp [radixRecursionLedger, sortBitOps, sortCompareSteps]
    _ ≤ radixBudgetConstant r * (radixRecursionRecords n : ℝ)
          * (Real.log ((radixRecursionRecords n : ℝ) + 2)) ^ 4 := hshape
    _ = radixBudgetConstant r * ((radixRecursionLedger r n).queries : ℝ)
          * (Real.log (((radixRecursionLedger r n).queries : ℝ) + 2)) ^ 4 := by
      have hq : (radixRecursionLedger r n).queries = radixRecursionRecords n := rfl
      rw [hq]

theorem radixRecursionLedger_budget (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) :
    (radixRecursionLedger r n).samples ≤ (radixRecursionLedger r n).queries ∧
      sortCompareSteps (radixRecursionLedger r n).samples
        ≤ (radixRecursionLedger r n).comparisons ∧
      sortBitOps (radixRecursionLedger r n).samples (radixRecursionLedger r n).integerBits
        ≤ (radixRecursionLedger r n).bitOps ∧
      0 < (radixRecursionLedger r n).workspaceBits ∧
      ((radixRecursionLedger r n).queries : ℝ)
        ≤ radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 ∧
      ((radixRecursionLedger r n).bitOps : ℝ)
        ≤ radixBudgetConstant r * ((radixRecursionLedger r n).queries : ℝ)
            * (Real.log (((radixRecursionLedger r n).queries : ℝ) + 2)) ^ 4 :=
  ⟨radixRecursionLedger_samples_le_queries r n, radixRecursionLedger_comparisons r n,
    radixRecursionLedger_bitOps_account r n, radixRecursionLedger_workspace r n,
    radixRecursionLedger_queries_le r n hr hn,
    radixRecursionLedger_bitOps_le r n hr hn⟩

theorem radixAmplifiedRecords_le (n : ℕ) :
    radixAmplifiedRecords n ≤ 1000 * (n + 1) * radixRecursionRecords n := by
  calc radixAmplifiedRecords n
      = ∑ j ∈ Finset.range n, (1000 * (n - j + 1)) * radixLevelRecords n j := by
        simp [radixAmplifiedRecords, radixLevelTrials]
    _ ≤ ∑ j ∈ Finset.range n, (1000 * (n + 1)) * radixLevelRecords n j := by
        exact Finset.sum_le_sum (fun j _ => by
          have h1 : 1000 * (n - j + 1) ≤ 1000 * (n + 1) := by omega
          exact mul_le_mul_of_nonneg_right h1 (Nat.zero_le _))
    _ = 1000 * (n + 1) * (∑ j ∈ Finset.range n, radixLevelRecords n j) := by
        rw [← Finset.mul_sum]
    _ = 1000 * (n + 1) * radixRecursionRecords n := rfl

theorem radixAmplifiedLedger_samples_le_queries (r n : ℕ) :
    (radixAmplifiedLedger r n).samples ≤ (radixAmplifiedLedger r n).queries := by
  rfl

theorem radixAmplifiedLedger_comparisons (r n : ℕ) :
    sortCompareSteps (radixAmplifiedLedger r n).samples
      ≤ (radixAmplifiedLedger r n).comparisons := by
  rfl

theorem radixAmplifiedLedger_bitOps_account (r n : ℕ) :
    sortBitOps (radixAmplifiedLedger r n).samples (radixAmplifiedLedger r n).integerBits
      ≤ (radixAmplifiedLedger r n).bitOps := by
  rfl

theorem radixAmplifiedLedger_workspace (r n : ℕ) :
    0 < (radixAmplifiedLedger r n).workspaceBits := by
  have h1 : 0 < radixFreshRecords n := by
    unfold radixFreshRecords
    omega
  have h2 : 0 < labelBits (r ^ n) := by
    unfold labelBits
    omega
  rw [radixAmplifiedLedger, workspaceBits]
  exact mul_pos h1 (by linarith)

theorem radixAmplifiedLedger_queries_le (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) :
    ((radixAmplifiedLedger r n).queries : ℝ)
      ≤ radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
  have hrec := radixRecursionRecords_le r n hn
  have hamp := radixAmplifiedRecords_le n
  have hC : 1000 ≤ radixBudgetConstant r := radix_budgetConstant_ge_1000 r (by omega)
  have hsq : ((n : ℝ) + 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 4 := by
    have h0 : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h2 : (0:ℝ) ≤ (n : ℝ) + 1 := by linarith
    have h3 : (0:ℝ) ≤ (n : ℝ) + 1 - 1 := by linarith
    have h4 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [mul_nonneg h2 h3]
    calc ((n : ℝ) + 1) ^ 3 = ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) := by ring
      _ ≤ ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ((n : ℝ) + 1) ^ 4 := by ring
  have hX : (0:ℝ) ≤ 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by positivity
  calc ((radixAmplifiedLedger r n).queries : ℝ)
      = (radixAmplifiedRecords n : ℝ) := rfl
    _ ≤ 1000 * ((n : ℝ) + 1) * (radixRecursionRecords n : ℝ) := by
      have h3 : (radixAmplifiedRecords n : ℝ)
          ≤ 1000 * ((n : ℝ) + 1) * (radixRecursionRecords n : ℝ) := by
        exact_mod_cast hamp
      exact h3
    _ ≤ 1000 * ((n : ℝ) + 1) * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2) := by
      have h1 : (1000 * ((n : ℝ) + 1)) * (radixRecursionRecords n : ℝ)
          ≤ (1000 * ((n : ℝ) + 1))
              * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hrec (by positivity)
      calc 1000 * ((n : ℝ) + 1) * (radixRecursionRecords n : ℝ)
          = (1000 * ((n : ℝ) + 1)) * (radixRecursionRecords n : ℝ) := by ring
        _ ≤ (1000 * ((n : ℝ) + 1)) * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2) := h1
        _ = 1000 * ((n : ℝ) + 1) * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2) := by ring
    _ ≤ radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
      have hmul : 1000 * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4)
          ≤ radixBudgetConstant r * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4) :=
        mul_le_mul_of_nonneg_right hC hX
      have h3 : (3 ^ Real.sqrt (2 * (n : ℝ))) * ((n : ℝ) + 1) ^ 3
          ≤ (3 ^ Real.sqrt (2 * (n : ℝ))) * ((n : ℝ) + 1) ^ 4 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have h4 : 1000 * ((3 ^ Real.sqrt (2 * (n : ℝ))) * ((n : ℝ) + 1) ^ 3)
          ≤ 1000 * ((3 ^ Real.sqrt (2 * (n : ℝ))) * ((n : ℝ) + 1) ^ 4) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      calc 1000 * ((n : ℝ) + 1) * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 2)
          = 1000 * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 3 := by ring
        _ ≤ 1000 * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
          calc 1000 * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 3
              = 1000 * ((3 ^ Real.sqrt (2 * (n : ℝ))) * ((n : ℝ) + 1) ^ 3) := by ac_rfl
            _ ≤ 1000 * ((3 ^ Real.sqrt (2 * (n : ℝ))) * ((n : ℝ) + 1) ^ 4) := h4
            _ = 1000 * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by ac_rfl
        _ ≤ radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by
          calc 1000 * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4
              = 1000 * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4) := by ac_rfl
            _ ≤ radixBudgetConstant r * (3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4) := hmul
            _ = radixBudgetConstant r * 3 ^ Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) + 1) ^ 4 := by ac_rfl

theorem radixAmplifiedLedger_bitOps_le (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) :
    ((radixAmplifiedLedger r n).bitOps : ℝ)
      ≤ radixBudgetConstant r * ((radixAmplifiedLedger r n).queries : ℝ)
          * (Real.log (((radixAmplifiedLedger r n).queries : ℝ) + 2)) ^ 4 := by
  have hγ : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hamp : radixRecursionRecords n ≤ radixAmplifiedRecords n := by
    have hterm : ∀ j ∈ Finset.range n,
        radixLevelRecords n j ≤ radixLevelTrials n j * radixLevelRecords n j := by
      intro j hj
      have h2 : 1 ≤ radixLevelTrials n j := by
        have hjn : j < n := Finset.mem_range.mp hj
        unfold radixLevelTrials
        omega
      calc radixLevelRecords n j = 1 * radixLevelRecords n j := by rw [Nat.one_mul]
        _ ≤ radixLevelTrials n j * radixLevelRecords n j :=
          Nat.mul_le_mul h2 (le_refl _)
    calc radixRecursionRecords n = ∑ j ∈ Finset.range n, radixLevelRecords n j := rfl
      _ ≤ ∑ j ∈ Finset.range n, radixLevelTrials n j * radixLevelRecords n j :=
        Finset.sum_le_sum hterm
      _ = radixAmplifiedRecords n := rfl
  have hLpos : 0 < radixAmplifiedRecords n := by
    have h0 : 0 < radixRecursionRecords n := by
      have hge := radix_recursionRecords_ge n hn
      have hfr : 0 < radixFreshRecords n := by
        unfold radixFreshRecords
        omega
      omega
    omega
  have hlog : Real.log 3 * Real.sqrt (n : ℝ)
      ≤ Real.log ((radixAmplifiedRecords n : ℝ) + 2) := by
    have h := radix_log_lower n hn
    have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
      have hle : (n:ℝ) ≤ 2 * (n:ℝ) := by linarith
      exact Real.sqrt_le_sqrt hle
    have hmul := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hγ)
    have h1 : Real.log ((radixRecursionRecords n : ℝ) + 2)
        ≤ Real.log ((radixAmplifiedRecords n : ℝ) + 2) := by
      have h2 : (radixRecursionRecords n : ℝ) + 2
          ≤ (radixAmplifiedRecords n : ℝ) + 2 := by
        have h3 : (radixRecursionRecords n : ℝ) ≤ (radixAmplifiedRecords n : ℝ) :=
          Nat.cast_le.mpr hamp
        linarith
      have hpos1 : (0:ℝ) < (radixRecursionRecords n : ℝ) + 2 := by
        have h3 : (0:ℝ) < (radixRecursionRecords n : ℝ) := by
          have h0 : 0 < radixRecursionRecords n := by
            have hge := radix_recursionRecords_ge n hn
            have hfr : 0 < radixFreshRecords n := by
              unfold radixFreshRecords
              omega
            omega
          exact Nat.cast_pos.mpr h0
        linarith
      have hpos2 : (0:ℝ) < (radixAmplifiedRecords n : ℝ) + 2 := by
        have h3 : (0:ℝ) < (radixAmplifiedRecords n : ℝ) := by
          exact Nat.cast_pos.mpr hLpos
        linarith
      exact Real.strictMonoOn_log.monotoneOn hpos1 hpos2 h2
    exact le_trans (le_trans hmul h) h1
  have hbits : (labelBits (r ^ n) : ℝ) ≤ (n : ℝ) * (Real.log (↑r : ℝ) / Real.log 2 + 1) :=
    radix_labelBits_le r n (by omega) hn
  have hshape := radix_sortBitOps_shape (radixAmplifiedRecords n) (labelBits (r ^ n)) n r
    (by omega) hn hLpos hlog hbits
  calc ((radixAmplifiedLedger r n).bitOps : ℝ)
      = (radixAmplifiedRecords n : ℝ)
          * ((Nat.log2 (radixAmplifiedRecords n + 1) : ℝ) + 1)
          * (labelBits (r ^ n) : ℝ) := by
        simp [radixAmplifiedLedger, sortBitOps, sortCompareSteps]
    _ ≤ radixBudgetConstant r * (radixAmplifiedRecords n : ℝ)
          * (Real.log ((radixAmplifiedRecords n : ℝ) + 2)) ^ 4 := hshape
    _ = radixBudgetConstant r * ((radixAmplifiedLedger r n).queries : ℝ)
          * (Real.log (((radixAmplifiedLedger r n).queries : ℝ) + 2)) ^ 4 := by
      have hq : (radixAmplifiedLedger r n).queries = radixAmplifiedRecords n := rfl
      rw [hq]

theorem dihedralQubitState_phaseRatio (N : ℕ) [NeZero N] (s k : ZMod N) (u : ℂ) (hu : ‖u‖ = 1) :
    (u • dihedralQubitState N s k) true / (u • dihedralQubitState N s k) false
      = dihedralQubitPhase N s k := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  have hsqrt : ((1 : ℂ) / Real.sqrt 2) ≠ 0 := by
    intro h
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      have h2' : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
      exact_mod_cast h2'
    rcases div_eq_zero_iff.mp h with h1 | h1
    · norm_num at h1
    · exact h2 h1
  have hden : (u • dihedralQubitState N s k) false ≠ 0 := by
    simp only [Pi.smul_apply, smul_eq_mul, dihedralQubitState, Bool.cond_false]
    intro h
    have hz : u * ((1 : ℂ) / Real.sqrt 2 * 1) = 0 := by simpa using! h
    rcases mul_eq_zero.mp hz with h | h
    · exact hu0 h
    · exact hsqrt (by simpa using! h)
  rw [div_eq_iff (by exact hden)]
  simp only [Pi.smul_apply, smul_eq_mul, dihedralQubitState, Bool.cond_true, Bool.cond_false]
  ring

private theorem radixListValue_append (r n : ℕ) (L₁ L₂ : List ℕ) :
    radixListValue r n (L₁ ++ L₂) = radixListValue r n L₁ + radixListValue r n L₂ := by
  unfold radixListValue
  simp [List.map_append, List.sum_append]

theorem radixGreedyChild_value_max (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) :
    radixValue r n (radixGreedyChild r (r ^ n) k ℓ)
      = max (radixValue r n ((k + ℓ) % (r ^ n)))
        (radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))) := by
  have hgα : radixAlpha r (radixGreedyChild r (r ^ n) k ℓ) = radixPairValue r (r ^ n) k ℓ :=
    radixGreedyChild_alpha r (r ^ n) k ℓ
  have hsumlt : (k + ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by omega)
  have hdifflt : (k + (r ^ n) - ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by omega)
  have hglt : radixGreedyChild r (r ^ n) k ℓ < r ^ n := by
    unfold radixGreedyChild
    split
    · exact hdifflt
    · exact hsumlt
  have hαsum : radixAlpha r ((k + ℓ) % (r ^ n)) ≤ radixAlpha r (radixGreedyChild r (r ^ n) k ℓ) := by
    rw [hgα]
    unfold radixPairValue
    exact Nat.le_max_left _ _
  have hαdiff : radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n))
      ≤ radixAlpha r (radixGreedyChild r (r ^ n) k ℓ) := by
    rw [hgα]
    unfold radixPairValue
    exact Nat.le_max_right _ _
  have hsumv : radixValue r n ((k + ℓ) % (r ^ n))
      ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) :=
    radixValue_ge_of_alpha_ge r n (radixGreedyChild r (r ^ n) k ℓ) ((k + ℓ) % (r ^ n))
      hr hn hglt hsumlt hαsum
  have hdiffv : radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))
      ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) :=
    radixValue_ge_of_alpha_ge r n (radixGreedyChild r (r ^ n) k ℓ)
      ((k + (r ^ n) - ℓ) % (r ^ n)) hr hn hglt hdifflt hαdiff
  unfold radixGreedyChild
  split
  · rw [max_eq_right]
    exact radixValue_ge_of_alpha_ge r n ((k + (r ^ n) - ℓ) % (r ^ n)) ((k + ℓ) % (r ^ n))
      hr hn hdifflt hsumlt (by omega)
  · rw [max_eq_left]
    exact radixValue_ge_of_alpha_ge r n ((k + ℓ) % (r ^ n)) ((k + (r ^ n) - ℓ) % (r ^ n))
      hr hn hsumlt hdifflt (by omega)

theorem radixQuantumPeriodValue_eq (r n : ℕ) (L : List ℕ) (k ℓ : ℕ)
    (hpair : radixGreedyPair r (r ^ n) L = some (k, ℓ)) :
    radixQuantumPeriodValue r n L
      = radixGreedyPeriodValue r n L
        - (radixValue r n (radixGreedyChild r (r ^ n) k ℓ) - radixExpectedChildValue r n k ℓ) := by
  have hchild : radixPeriodChildren r (r ^ n) L = [radixGreedyChild r (r ^ n) k ℓ] := by
    unfold radixPeriodChildren
    rw [hpair]
  have hstep : radixPeriodStep r (r ^ n) L
      = radixKeptLabels r L ++ [radixGreedyChild r (r ^ n) k ℓ] := by
    unfold radixPeriodStep
    rw [hchild]
  have hgreedy : radixGreedyPeriodValue r n L
      = radixListValue r n (radixKeptLabels r L)
        + radixValue r n (radixGreedyChild r (r ^ n) k ℓ) := by
    unfold radixGreedyPeriodValue
    rw [hstep, radixListValue_append]
    simp [radixListValue]
  unfold radixQuantumPeriodValue
  rw [hpair]
  rw [hgreedy]
  ring

theorem radixQuantumPeriod_gamble_eq (r n : ℕ) (L : List ℕ) (k ℓ : ℕ)
    (hr : 2 ≤ r) (hn : 1 ≤ n) (hk : k < r ^ n) (hℓ : ℓ < r ^ n)
    (hpair : radixGreedyPair r (r ^ n) L = some (k, ℓ)) :
    radixGreedyPeriodValue r n L - radixQuantumPeriodValue r n L
      = |radixValue r n ((k + ℓ) % (r ^ n))
          - radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))| / 2 := by
  have hmodel := radixQuantumPeriodValue_eq r n L k ℓ hpair
  have hmax := radixGreedyChild_value_max r n k ℓ hr hn hk hℓ
  have hE : radixExpectedChildValue r n k ℓ
      = (radixValue r n ((k + ℓ) % (r ^ n))
        + radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))) / 2 := by
    unfold radixExpectedChildValue
    rfl
  rw [hE] at hmodel
  rw [hmax] at hmodel
  set a := radixValue r n ((k + ℓ) % (r ^ n)) with ha
  set b := radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n)) with hb
  have hab : a ≥ b ∨ b ≥ a := le_total b a
  rw [hmodel]
  rcases hab with hab | hab
  · rw [abs_of_nonneg (by linarith), max_eq_left hab]
    linarith
  · rw [abs_of_nonpos (by linarith), max_eq_right hab]
    linarith

theorem radixQuantumPeriodValue_le (r n : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (L : List ℕ)
    (k ℓ : ℕ) (hpair : radixGreedyPair r (r ^ n) L = some (k, ℓ))
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) :
    radixQuantumPeriodValue r n L ≤ radixGreedyPeriodValue r n L := by
  have hmodel := radixQuantumPeriodValue_eq r n L k ℓ hpair
  have hmax := radixGreedyChild_value_max r n k ℓ hr hn hk hℓ
  have hge : radixExpectedChildValue r n k ℓ
      ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) := by
    unfold radixExpectedChildValue
    rw [hmax]
    have h1 : radixValue r n ((k + ℓ) % (r ^ n)) ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) := by
      rw [hmax]
      exact le_max_left _ _
    have h2 : radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))
        ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) := by
      rw [hmax]
      exact le_max_right _ _
    linarith
  rw [hmodel]
  linarith

theorem radixQuantumPeriod_gamble_le_one (r n : ℕ) (L : List ℕ) :
    radixGreedyPeriodValue r n L - radixQuantumPeriodValue r n L ≤ 1 := by
  cases hp : radixGreedyPair r (r ^ n) L with
  | none =>
    have hmodel : radixQuantumPeriodValue r n L = radixGreedyPeriodValue r n L := by
      unfold radixQuantumPeriodValue radixGreedyPeriodValue radixPeriodStep radixPeriodChildren
      rw [hp]
      simp [radixListValue]
    rw [hmodel]
    linarith
  | some kl =>
    obtain ⟨k, ℓ⟩ := kl
    have hmodel := radixQuantumPeriodValue_eq r n L k ℓ hp
    have hV : radixValue r n (radixGreedyChild r (r ^ n) k ℓ) ≤ 1 := radixValue_le_one _ _ _
    have hE : 0 ≤ radixExpectedChildValue r n k ℓ := by
      unfold radixExpectedChildValue
      have h1 := radixValue_pos r n ((k + ℓ) % (r ^ n))
      have h2 := radixValue_pos r n ((k + (r ^ n) - ℓ) % (r ^ n))
      linarith
    rw [hmodel]
    linarith

private theorem radix_unit_norm {I : Type*} [Fintype I] {u : ℂ} (hu : ‖u‖ = 1)
    {ξ : QState I} (hξ : Normalized ξ) : Normalized (u • ξ) := by
  unfold Normalized
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hu, one_mul]
  exact hξ

theorem radixQuantumExtract_sign {N : ℕ} [NeZero N] (s k ℓ : ZMod N)
    (u u' : ℂ) (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    (dihedralExtraction (u • dihedralQubitState N s k) (u' • dihedralQubitState N s ℓ)
        (radix_unit_norm hu (normalized_dihedralQubitState N s k))
        (radix_unit_norm hu' (normalized_dihedralQubitState N s ℓ))).map Prod.fst
      = PMF.uniformOfFintype' Bool :=
  dihedralExtraction_fair N s k ℓ u u' hu hu'

theorem radixQuantumExtract_child {N : ℕ} [NeZero N] (s k ℓ : ZMod N) :
    ∃ (xiPlus xiMinus : QState Bool) (uPlus uMinus : ℂ),
      ‖uPlus‖ = 1 ∧ ‖uMinus‖ = 1 ∧
        xiPlus = uPlus • dihedralQubitState N s (k + ℓ) ∧
        xiMinus = uMinus • dihedralQubitState N s (k - ℓ) ∧
      ∀ (b : Bool) (ξ : QState Bool) (hξ : Normalized ξ),
        (dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
          (normalized_dihedralQubitState N s k)
          (normalized_dihedralQubitState N s ℓ)) (b, ⟨ξ, hξ⟩) =
          if (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) then 1 / 2 else 0 := by
  obtain ⟨xiPlus, xiMinus, hPlus, hMinus, uPlus, uMinus, hup, hum, hxp, hxm, hlaw⟩ :=
    dihedralExtractionLaw N s k ℓ
  exact ⟨xiPlus, xiMinus, uPlus, uMinus, hup, hum, hxp, hxm, hlaw⟩

theorem radixQuantumExtract_outcome {N : ℕ} [NeZero N] (s k ℓ : ZMod N) (b : Bool)
    (ξ : QState Bool) (hξ : Normalized ξ)
    (hmass : (dihedralExtraction (dihedralQubitState N s k) (dihedralQubitState N s ℓ)
        (normalized_dihedralQubitState N s k)
        (normalized_dihedralQubitState N s ℓ)) (b, ⟨ξ, hξ⟩) ≠ 0) :
    (b = false ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ξ = u • dihedralQubitState N s (k + ℓ)) ∨
      (b = true ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ξ = u • dihedralQubitState N s (k - ℓ)) := by
  obtain ⟨xiPlus, xiMinus, hPlus, hMinus, uPlus, uMinus, hup, hum, hxp, hxm, hlaw⟩ :=
    dihedralExtractionLaw N s k ℓ
  have hlaw' := hlaw b ξ hξ
  by_cases hb : b = false
  · have hcond : (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) := by
      by_cases h : (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus)
      · exact h
      · rw [if_neg h] at hlaw'
        exact absurd hlaw' hmass
    rcases hcond with ⟨hb', hξ'⟩ | ⟨hb', hξ'⟩
    · exact Or.inl ⟨hb, uPlus, hup, by rw [← hxp, hξ']⟩
    · exact absurd hb' (by rw [hb]; exact Bool.noConfusion)
  · have hcond : (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus) := by
      by_cases h : (b = false ∧ ξ = xiPlus) ∨ (b = true ∧ ξ = xiMinus)
      · exact h
      · rw [if_neg h] at hlaw'
        exact absurd hlaw' hmass
    rcases hcond with ⟨hb', hξ'⟩ | ⟨hb', hξ'⟩
    · exact absurd hb' hb
    · exact Or.inr ⟨hb', uMinus, hum, by rw [← hxm, hξ']⟩

theorem radixQuantumExtract_phase {N : ℕ} [NeZero N] (s k ℓ : ZMod N) (b : Bool)
    (ξ : QState Bool) (hξ : Normalized ξ)
    (hchild : (b = false ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ξ = u • dihedralQubitState N s (k + ℓ)) ∨
              (b = true ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ ξ = u • dihedralQubitState N s (k - ℓ))) :
    radixBranchPhase ξ = some (dihedralQubitPhase N s (if b then k - ℓ else k + ℓ)) := by
  rcases hchild with ⟨hb, u, hu, hξeq⟩ | ⟨hb, u, hu, hξeq⟩
  · have hchild' : (if b then k - ℓ else k + ℓ) = k + ℓ := by simp [hb]
    rw [hchild']
    have hfalse : ξ false ≠ 0 := by
      rw [hξeq]
      simp only [Pi.smul_apply, smul_eq_mul, dihedralQubitState, Bool.cond_false]
      intro h
      rcases mul_eq_zero.mp h with h | h
      · have hz : ‖u‖ = 0 := by rw [h, norm_zero]
        rw [hu] at hz
        norm_num at hz
      · have hsqrt : ((1 : ℂ) / Real.sqrt 2) ≠ 0 := by
          intro h
          have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
            have h2' : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
            exact_mod_cast h2'
          rcases div_eq_zero_iff.mp h with h1 | h1
          · norm_num at h1
          · exact h2 h1
        exact hsqrt (by simpa using! h)
    have hphase : radixBranchPhase ξ = some (ξ true / ξ false) := by
      simp only [radixBranchPhase]
      split_ifs with h
      · exact absurd h hfalse
      · rfl
    rw [hphase]
    congr 1
    rw [hξeq]
    exact dihedralQubitState_phaseRatio N s (k + ℓ) u hu
  · have hchild' : (if b then k - ℓ else k + ℓ) = k - ℓ := by simp [hb]
    rw [hchild']
    have hfalse : ξ false ≠ 0 := by
      rw [hξeq]
      simp only [Pi.smul_apply, smul_eq_mul, dihedralQubitState, Bool.cond_false]
      intro h
      rcases mul_eq_zero.mp h with h | h
      · have hz : ‖u‖ = 0 := by rw [h, norm_zero]
        rw [hu] at hz
        norm_num at hz
      · have hsqrt : ((1 : ℂ) / Real.sqrt 2) ≠ 0 := by
          intro h
          have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
            have h2' : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
            exact_mod_cast h2'
          rcases div_eq_zero_iff.mp h with h1 | h1
          · norm_num at h1
          · exact h2 h1
        exact hsqrt (by simpa using! h)
    have hphase : radixBranchPhase ξ = some (ξ true / ξ false) := by
      simp only [radixBranchPhase]
      split_ifs with h
      · exact absurd h hfalse
      · rfl
    rw [hphase]
    congr 1
    rw [hξeq]
    exact dihedralQubitState_phaseRatio N s (k - ℓ) u hu

theorem radixQuantumExtract_law {N : ℕ} [NeZero N] (k ℓ : ZMod N) :
    (radixQuantumExtractLaw k ℓ) (false, k + ℓ) = 1 / 2 ∧
    (radixQuantumExtractLaw k ℓ) (true, k - ℓ) = 1 / 2 := by
  constructor
  · rw [radixQuantumExtractLaw, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have h1 : (PMF.uniformOfFintype' Bool) false = 1 / 2 := by
      rw [PMF.uniformOfFintype'_apply]; norm_num
    have h2 : (PMF.uniformOfFintype' Bool) true = 1 / 2 := by
      rw [PMF.uniformOfFintype'_apply]; norm_num
    rw [h1, h2]
    simp [PMF.pure_apply]
  · rw [radixQuantumExtractLaw, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have h1 : (PMF.uniformOfFintype' Bool) false = 1 / 2 := by
      rw [PMF.uniformOfFintype'_apply]; norm_num
    have h2 : (PMF.uniformOfFintype' Bool) true = 1 / 2 := by
      rw [PMF.uniformOfFintype'_apply]; norm_num
    rw [h1, h2]
    simp [PMF.pure_apply]

theorem radix_diff_child_val (N : ℕ) [NeZero N] (k ℓ : ZMod N) :
    (k - ℓ).val = (k.val + N - ℓ.val) % N := by
  have hklt : k.val < N := ZMod.val_lt k
  have hℓlt : ℓ.val < N := ZMod.val_lt ℓ
  by_cases h : ℓ.val ≤ k.val
  · rw [ZMod.val_sub h]
    have h2 : k.val - ℓ.val < N := by omega
    have h3 : k.val + N - ℓ.val = N + (k.val - ℓ.val) := by omega
    rw [h3]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    exact (Nat.mod_eq_of_lt h2).symm
  · rw [sub_eq_add_neg, ZMod.val_add, ZMod.neg_val']
    have hne : 0 < ℓ.val := by omega
    have h2 : N - ℓ.val < N := by omega
    rw [Nat.mod_eq_of_lt h2]
    have h4 : k.val + (N - ℓ.val) = k.val + N - ℓ.val := by omega
    rw [h4]

theorem radixExpectedChildValue_quantum (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) :
    (radixValue r n ((↑k + ↑ℓ : ZMod (r ^ n)).val)
      + radixValue r n ((↑k - ↑ℓ : ZMod (r ^ n)).val)) / 2
      = radixExpectedChildValue r n k ℓ := by
  letI : NeZero r := ⟨by omega⟩
  unfold radixExpectedChildValue
  have hkval : (↑k : ZMod (r ^ n)).val = k := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hk
  have hℓval : (↑ℓ : ZMod (r ^ n)).val = ℓ := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hℓ
  have hsum : (↑k + ↑ℓ : ZMod (r ^ n)).val = (k + ℓ) % (r ^ n) := by
    rw [ZMod.val_add, hkval, hℓval]
  have hdiff : (↑k - ↑ℓ : ZMod (r ^ n)).val = (k + (r ^ n) - ℓ) % (r ^ n) := by
    rw [radix_diff_child_val, hkval, hℓval]
  rw [hsum, hdiff]

theorem radixGreedyChild_value_ge_expected (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) :
    radixExpectedChildValue r n k ℓ ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) := by
  have hgα : radixAlpha r (radixGreedyChild r (r ^ n) k ℓ) = radixPairValue r (r ^ n) k ℓ :=
    radixGreedyChild_alpha r (r ^ n) k ℓ
  have hglt : radixGreedyChild r (r ^ n) k ℓ < r ^ n := by
    unfold radixGreedyChild
    split
    · exact Nat.mod_lt _ (by omega)
    · exact Nat.mod_lt _ (by omega)
  have hsumlt : (k + ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by omega)
  have hdifflt : (k + (r ^ n) - ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by omega)
  have hsumα : radixAlpha r ((k + ℓ) % (r ^ n)) ≤ radixAlpha r (radixGreedyChild r (r ^ n) k ℓ) := by
    rw [hgα]
    unfold radixPairValue
    exact Nat.le_max_left _ _
  have hdiffα : radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n))
      ≤ radixAlpha r (radixGreedyChild r (r ^ n) k ℓ) := by
    rw [hgα]
    unfold radixPairValue
    exact Nat.le_max_right _ _
  have hsumv : radixValue r n ((k + ℓ) % (r ^ n))
      ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) :=
    radixValue_ge_of_alpha_ge r n (radixGreedyChild r (r ^ n) k ℓ) ((k + ℓ) % (r ^ n))
      hr hn hglt hsumlt hsumα
  have hdiffv : radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n))
      ≤ radixValue r n (radixGreedyChild r (r ^ n) k ℓ) :=
    radixValue_ge_of_alpha_ge r n (radixGreedyChild r (r ^ n) k ℓ)
      ((k + (r ^ n) - ℓ) % (r ^ n)) hr hn hglt hdifflt hdiffα
  unfold radixExpectedChildValue
  linarith

theorem radixRecordFactor (N : ℕ) [NeZero N] {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) :
    ∃ γ : S → ℂ, (∑ z, ‖γ z‖ ^ 2) = 1 / (N : ℝ) ∧
      ∀ t z, dihedralRecordJoint N f ((k, t), z) = γ z * dihedralQubitState N s k t := by
  obtain ⟨_, _, h⟩ := sourceGeneralRecordLaw N S f s hf
  exact h k

theorem radixRecordPhaseRatio (N : ℕ) [NeZero N] {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) (t : Bool) (z : S) :
    (fun b => dihedralRecordJoint N f ((k,b),z)) = 0 ∨
      ∃ c : ℂ, c ≠ 0 ∧
        (fun b => dihedralRecordJoint N f ((k,b),z)) = c • (fun b => cond b (dihedralQubitPhase N s k) 1) := by
  obtain ⟨γ, _, hfactor⟩ := radixRecordFactor N f s hf k
  have hsqrt : ((1 : ℂ) / Real.sqrt 2) ≠ 0 := by
    intro h
    have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
      have h2' : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
      exact_mod_cast h2'
    rcases div_eq_zero_iff.mp h with h1 | h1
    · norm_num at h1
    · exact h2 h1
  by_cases hc : γ z = 0
  · left
    funext b
    rw [hfactor b z, hc]
    simp
  · right
    refine ⟨γ z * ((1 : ℂ) / Real.sqrt 2), ?_, ?_⟩
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact hc h
      · exact hsqrt (by simpa using! h)
    · funext b
      rw [hfactor b z]
      simp only [dihedralQubitState, Pi.smul_apply, smul_eq_mul]
      ring

theorem radixRootOfUnity_eq_stdAddChar (r : ℕ) [NeZero r] (t : ZMod r) :
    radixRootOfUnity r t.val = ZMod.stdAddChar t := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  unfold radixRootOfUnity
  congr 1
  push_cast
  ring

theorem radixRootOfUnity_injective (r : ℕ) [NeZero r] {a b : ZMod r}
    (h : radixRootOfUnity r a.val = radixRootOfUnity r b.val) : a = b := by
  rw [radixRootOfUnity_eq_stdAddChar, radixRootOfUnity_eq_stdAddChar] at h
  exact ZMod.injective_stdAddChar h

private theorem list_find?_eq_some_of_unique {α : Type} {l : List α} (p : α → Bool)
    {a : α} (ha : a ∈ l) (hpa : p a = true) (huniq : ∀ b, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
    by_cases hb : p b = true
    · have hba : b = a := huniq b hb
      subst hba
      exact List.find?_cons_of_pos (l := bs) hpa
    · have hmem : a ∈ bs := by
        simp only [List.mem_cons] at ha
        rcases ha with h | h
        · exfalso
          exact hb (h ▸ hpa)
        · exact h
      rw [List.find?_cons_of_neg hb]
      exact ih hmem

theorem radixTomographyIndex_of (r : ℕ) [NeZero r] (t : ZMod r) (χ : QState Bool)
    (hphase : radixBranchPhase χ = some (radixRootOfUnity r t.val)) :
    radixTomographyIndex r χ = some t := by
  unfold radixTomographyIndex
  rw [hphase]
  refine list_find?_eq_some_of_unique (fun t' : ZMod r => decide (radixRootOfUnity r t'.val
    = radixRootOfUnity r t.val)) ?_ ?_ ?_
  · exact Finset.mem_toList.mpr (Finset.mem_univ t)
  · rw [decide_eq_true_eq]
  · intro t' ht'
    exact radixRootOfUnity_injective r (by simpa using! ht')

theorem radixBranchPhase_of (χ : QState Bool) (hfalse : χ false ≠ 0) :
    radixBranchPhase χ = some (χ true / χ false) := by
  simp only [radixBranchPhase]
  split_ifs with h
  · exact absurd h hfalse
  · rfl

theorem radixBranchPhase_none (χ : QState Bool) (hfalse : χ false = 0) :
    radixBranchPhase χ = none := by
  simp [radixBranchPhase, hfalse]

theorem radixTomographyIndex_none (r : ℕ) [NeZero r] (χ : QState Bool)
    (h : radixBranchPhase χ = none) : radixTomographyIndex r χ = none := by
  unfold radixTomographyIndex
  rw [h]

theorem radixTomographyIndex_of_nat (r : ℕ) [NeZero r] (t : ℕ) (ht : t < r) (χ : QState Bool)
    (hphase : radixBranchPhase χ = some (radixRootOfUnity r t)) :
    radixTomographyIndex r χ = some (t : ZMod r) := by
  refine radixTomographyIndex_of r (t : ZMod r) χ ?_
  have hval : (t : ZMod r).val = t := ZMod.val_natCast_of_lt ht
  rw [hval]
  exact hphase

theorem radixRecordPhaseRatio_of (N : ℕ) [NeZero N] {S : Type} [Fintype S] [DecidableEq S]
    [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) (t : Bool) (z : S)
    (hne : (fun b => dihedralRecordJoint N f ((k,b),z)) ≠ 0) :
    (fun b => dihedralRecordJoint N f ((k,b),z)) true
      / (fun b => dihedralRecordJoint N f ((k,b),z)) false
        = dihedralQubitPhase N s k := by
  rcases radixRecordPhaseRatio N f s hf k t z with h | ⟨c, hc, heq⟩
  · exact absurd h hne
  · have hfalse : (fun b => dihedralRecordJoint N f ((k,b),z)) false
        = c * (cond false (dihedralQubitPhase N s k) 1) := by
      have h := congrFun heq false
      simpa using! h
    have htrue : (fun b => dihedralRecordJoint N f ((k,b),z)) true
        = c * (cond true (dihedralQubitPhase N s k) 1) := by
      have h := congrFun heq true
      simpa using! h
    have hcfalse : c * (cond false (dihedralQubitPhase N s k) 1) ≠ 0 := by
      simp only [Bool.cond_false]
      intro hz
      rcases mul_eq_zero.mp hz with hb | hb
      · exact hc hb
      · simp at hb
    rw [htrue, hfalse, div_eq_iff hcfalse]
    simp only [Bool.cond_true, Bool.cond_false]
    ring

noncomputable def radixRecoveryReadout {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r : ℕ) [NeZero r] (n : ℕ)
    (k : ZMod N) (z : S) : Option (ZMod r) :=
  match radixTomographyIndex r (fun b => dihedralRecordJoint N f ((k,b),z)) with
  | none => none
  | some t =>
    if h : IsUnit (radixFinalIndex r n k.val : ZMod r) then
      some (radixReadout r (radixFinalIndex r n k.val) t.val)
    else none

noncomputable def radixRecoveryDecide {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r : ℕ) [NeZero r] (n p : ℕ)
    (L : List (ZMod N × S)) : Option (ZMod r) :=
  match radixFinalRecordBy r n (fun rec : ZMod N × S => rec.1.val) L
      (radixSieveRun r N p (L.map fun rec => rec.1.val)) with
  | none => none
  | some (k, z) => radixRecoveryReadout f r n k z

noncomputable def radixRecoveryRun {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (r : ℕ) [NeZero r] (n m p : ℕ) :
    PMF (Option (ZMod r)) :=
  (radixObservedRecords f m).map fun L => radixRecoveryDecide f r n p L

theorem radixRecoveryReadout_value (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg (r ^ n) → S)
    (s : ZMod (r ^ n)) (hf : DihedralReflectionHides (r ^ n) f s)
    (k : ZMod (r ^ n)) (z : S) (hklt : k.val < r ^ n)
    (htest : radixFinalTest r n k.val) :
    radixRecoveryReadout f r n k z = none ∨
      radixRecoveryReadout f r n k z = some (s.val % r) := by
  obtain ⟨a, ha0, ha1, hka⟩ := (radixFinalState_iff r n k.val hr hn hklt).mp htest
  have hrec1 : k = ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n)) := by
    have hval : (k.val : ZMod (r ^ n)) = k := ZMod.natCast_zmod_val _
    rw [← hval, hka]
  have hphase : dihedralQubitPhase (r ^ n) s k
      = radixRootOfUnity r ((s.val * a) % r) := by
    rw [hrec1]
    exact radixFinalPhase r n hr hn s a ha1
  rcases radixRecordPhaseRatio (r ^ n) f s hf k false z with hzero | ⟨c, hc, heq⟩
  · have hzf : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false = 0 := by
      rw [hzero]
      rfl
    have hbp : radixBranchPhase (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z))
        = none := radixBranchPhase_none _ hzf
    have hidx0 : radixTomographyIndex r
        (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) = none :=
      radixTomographyIndex_none r _ hbp
    unfold radixRecoveryReadout
    rw [hidx0]
    exact Or.inl rfl
  · have hfalse : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false = c := by
      have h := congrFun heq false
      simpa using! h
    have hc0 : c ≠ 0 := hc
    have hcf : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false ≠ 0 := by
      rw [hfalse]
      exact hc0
    have htrue : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) true
        = c * dihedralQubitPhase (r ^ n) s k := by
      have h := congrFun heq true
      simpa using! h
    have hratio : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) true
        / (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false
        = dihedralQubitPhase (r ^ n) s k := by
      rw [htrue, hfalse, div_eq_iff hc0]
      ring
    have hph : radixBranchPhase (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z))
        = some (radixRootOfUnity r ((s.val * a) % r)) := by
      rw [radixBranchPhase_of _ hcf, hratio, hphase]
    have hidx : radixTomographyIndex r
        (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z))
        = some ((s.val * a) % r : ZMod r) := by
      refine radixTomographyIndex_of_nat r ((s.val * a) % r) (Nat.mod_lt _ (by omega)) _ hph
    have hidxval : radixFinalIndex r n k.val = a := by
      rw [hka]
      exact radixFinalIndex_final r n a hr ha1
    by_cases hu : IsUnit (radixFinalIndex r n k.val : ZMod r)
    · have hunit : IsUnit (a : ZMod r) := by
        rw [← hidxval]
        exact hu
      have hout : radixReadout r a ((s.val * a) % r) = s.val % r := by
        have hcorrect := radixReadout_correct r n hr s.val a hunit
        rw [radixPhaseIndex_final r n s.val a hr] at hcorrect
        exact hcorrect
      have hval : ((s.val * a) % r : ZMod r).val = (s.val * a) % r :=
        ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega))
      unfold radixRecoveryReadout
      simp only [hidx]
      rw [dif_pos hu, hidxval, hval, hout]
      exact Or.inr rfl
    · unfold radixRecoveryReadout
      simp only [hidx]
      rw [dif_neg hu]
      exact Or.inl rfl

theorem radixRecoveryDecide_value (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg (r ^ n) → S)
    (s : ZMod (r ^ n)) (hf : DihedralReflectionHides (r ^ n) f s) (p : ℕ)
    (L : List (ZMod (r ^ n) × S)) :
    radixRecoveryDecide f r n p L = none ∨
      radixRecoveryDecide f r n p L = some (s.val % r) := by
  unfold radixRecoveryDecide
  cases hfind : radixFinalRecordBy r n (fun rec : ZMod (r ^ n) × S => rec.1.val) L
      (radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val)) with
  | none => exact Or.inl rfl
  | some rec =>
    obtain ⟨k, z⟩ := rec
    unfold radixFinalRecordBy at hfind
    have hfound := List.find?_some hfind
    have hfound' : (decide (radixFinalTest r n k.val) && decide (k.val ∈
        radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val))) = true := by
      simpa only [decide_eq_true_eq] using! hfound
    have hdec : decide (radixFinalTest r n k.val) = true ∧
        decide (k.val ∈ radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val)) = true :=
      (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hfound'
    have htest : radixFinalTest r n k.val := of_decide_eq_true hdec.1
    exact radixRecoveryReadout_value r n hr hn f s hf k z k.val_lt htest

theorem radixRecoveryRun_wrong_zero (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S] (f : DihedralReg (r ^ n) → S)
    (s : ZMod (r ^ n)) (hf : DihedralReflectionHides (r ^ n) f s) (m p : ℕ)
    (u : ZMod r) (hu : u ≠ s.val % r) :
    (radixRecoveryRun f r n m p) (some u) = 0 := by
  unfold radixRecoveryRun
  rw [PMF.map_apply]
  refine ENNReal.tsum_eq_zero.2 fun L => ?_
  rcases radixRecoveryDecide_value r n hr hn f s hf p L with h | h
  · rw [h]
    simp
  · rw [h]
    have hc : u ≠ s.cast := by
      intro hh
      exact hu (by simpa using! hh)
    simp [hc]

theorem dihedralReflect_involutive (N : ℕ) (s : ZMod N) (p : DihedralReg N) :
    dihedralReflect N s (dihedralReflect N s p) = p := by
  rcases p with ⟨a, t⟩
  cases t <;> simp [dihedralReflect]

private theorem radix_mul_div (r N : ℕ) (hr : r ∣ N) : r * (N / r) = N :=
  Nat.mul_div_cancel' hr

private theorem radix_div_pos (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) : 0 < N / r := by
  have h := radix_mul_div r N hr
  by_contra h0
  have hz : N / r = 0 := Nat.eq_zero_of_not_pos h0
  have hN0 : N = 0 := by rw [← h, hz, Nat.mul_zero]
  omega

private theorem radix_pos (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) : 0 < r := by
  rcases hr with ⟨k, hk⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [hk, h, Nat.mul_zero] at hN
      omega
    · exact h
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, Nat.zero_mul] at hk
    omega
  omega

private theorem radix_le (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) : r ≤ N := by
  rcases hr with ⟨k, hk⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [hk, h, Nat.mul_zero] at hN
      omega
    · exact h
  have h1 : r ≤ r * k := by
    calc r = r * 1 := by ring
      _ ≤ r * k := Nat.mul_le_mul_left r hk0
  rw [← hk] at h1
  exact h1

theorem radixLift_val (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) (b : ℕ) (hb : b < r)
    (t : ZMod (N / r)) :
    (radixLift r N b t).val = r * t.val + b := by
  haveI : NeZero (N / r) := ⟨Nat.ne_of_gt (radix_div_pos r N hr hN)⟩
  have ht := ZMod.val_lt t
  have hmul := radix_mul_div r N hr
  have hle := radix_le r N hr hN
  rw [radixLift, ZMod.val_natCast]
  refine Nat.mod_eq_of_lt ?_
  have h3 : r * t.val + r ≤ N := by
    have h4 : t.val + 1 ≤ N / r := by omega
    calc r * t.val + r = (t.val + 1) * r := by ring
      _ ≤ (N / r) * r := Nat.mul_le_mul h4 (le_refl r)
      _ = N := by rw [Nat.mul_comm, hmul]
  omega

theorem radixEmbedding_injective (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) (b : ℕ) (hb : b < r) :
    Function.Injective (radixSubgroupEmbedding r N b) := by
  haveI : NeZero (N / r) := ⟨Nat.ne_of_gt (radix_div_pos r N hr hN)⟩
  have hmul := radix_mul_div r N hr
  have hle := radix_le r N hr hN
  rintro ⟨a, ta⟩ ⟨c, tc⟩ he
  cases ta with
  | false =>
    cases tc with
    | false =>
      have hv := congrArg (fun p : DihedralReg N => p.1.val) he
      have ha := ZMod.val_lt a
      have hc := ZMod.val_lt c
      simp only [radixSubgroupEmbedding, ZMod.val_natCast] at hv
      have h1 : r * a.val < N := by
        calc r * a.val < r * (N / r) := Nat.mul_lt_mul_of_pos_left ha (by omega : 0 < r)
          _ = N := hmul
      have h2 : r * c.val < N := by
        calc r * c.val < r * (N / r) := Nat.mul_lt_mul_of_pos_left hc (by omega : 0 < r)
          _ = N := hmul
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv
      have hval : a.val = c.val := Nat.mul_left_cancel (by omega : 0 < r) hv
      exact Prod.ext ((ZMod.val_injective (N / r)) hval) rfl
    | true => exact Bool.noConfusion (congrArg Prod.snd he)
  | true =>
    cases tc with
    | false => exact Bool.noConfusion (congrArg Prod.snd he)
    | true =>
      have hv := congrArg (fun p : DihedralReg N => p.1.val) he
      have ha := ZMod.val_lt a
      have hc := ZMod.val_lt c
      simp only [radixSubgroupEmbedding, ZMod.val_natCast] at hv
      have h1 : r * a.val + b < N := by
        have h3 : r * a.val + r ≤ N := by
          have h4 : a.val + 1 ≤ N / r := by omega
          calc r * a.val + r = (a.val + 1) * r := by ring
            _ ≤ (N / r) * r := Nat.mul_le_mul h4 (le_refl r)
            _ = N := by rw [Nat.mul_comm, hmul]
        omega
      have h2 : r * c.val + b < N := by
        have h3 : r * c.val + r ≤ N := by
          have h4 : c.val + 1 ≤ N / r := by omega
          calc r * c.val + r = (c.val + 1) * r := by ring
            _ ≤ (N / r) * r := Nat.mul_le_mul h4 (le_refl r)
            _ = N := by rw [Nat.mul_comm, hmul]
        omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv
      have hval : a.val = c.val := Nat.mul_left_cancel (by omega : 0 < r) (Nat.add_right_cancel hv)
      exact Prod.ext ((ZMod.val_injective (N / r)) hval) rfl

private theorem radix_mul_add_val (r N : ℕ) (hr : r ∣ N) (hN : 0 < N)
    (a t : ZMod (N / r)) :
    ((r * (a + t).val : ℕ) : ZMod N) = ((r * a.val + r * t.val : ℕ) : ZMod N) := by
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  haveI : NeZero (N / r) := ⟨Nat.ne_of_gt (radix_div_pos r N hr hN)⟩
  have hadd : (a + t).val = (a.val + t.val) % (N / r) := ZMod.val_add a t
  have hmul := radix_mul_div r N hr
  have hdv : (a.val + t.val) / (N / r) * (N / r) + (a.val + t.val) % (N / r)
      = a.val + t.val := by
    have h := Nat.div_add_mod (a.val + t.val) (N / r)
    calc (a.val + t.val) / (N / r) * (N / r) + (a.val + t.val) % (N / r)
        = (N / r) * ((a.val + t.val) / (N / r)) + (a.val + t.val) % (N / r) := by ring
      _ = a.val + t.val := h
  have hq : (a.val + t.val) / (N / r) * (N / r) + (a + t).val = a.val + t.val := by
    omega
  have hrw : r * (a.val + t.val) = (a.val + t.val) / (N / r) * N + r * (a + t).val := by
    calc r * (a.val + t.val)
        = r * ((a.val + t.val) / (N / r) * (N / r) + (a + t).val) :=
          congrArg (fun x => r * x) hq.symm
      _ = r * ((a.val + t.val) / (N / r) * (N / r)) + r * (a + t).val := by ring
      _ = (a.val + t.val) / (N / r) * (r * (N / r)) + r * (a + t).val := by ring
      _ = (a.val + t.val) / (N / r) * N + r * (a + t).val := by rw [hmul]
  have hkey : r * (a + t).val + N * ((a.val + t.val) / (N / r)) = r * a.val + r * t.val := by
    calc r * (a + t).val + N * ((a.val + t.val) / (N / r))
        = ((a.val + t.val) / (N / r)) * N + r * (a + t).val := by ring
      _ = r * (a.val + t.val) := hrw.symm
      _ = r * a.val + r * t.val := by ring
  apply ZMod.val_injective N
  simp only [ZMod.val_natCast]
  rw [← hkey, Nat.add_mul_mod_self_left]

theorem radixEmbedding_reflect (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) (b : ℕ)
    (t : ZMod (N / r)) (p : DihedralReg (N / r)) :
    radixSubgroupEmbedding r N b (dihedralReflect (N / r) t p)
      = dihedralReflect N (radixLift r N b t) (radixSubgroupEmbedding r N b p) := by
  rcases p with ⟨a, ta⟩
  have hfalse : ∀ a : ZMod (N / r),
      radixSubgroupEmbedding r N b (dihedralReflect (N / r) t (a, false))
        = dihedralReflect N (radixLift r N b t) (radixSubgroupEmbedding r N b (a, false)) := by
    intro a
    show ((((r * (a + t).val + b : ℕ) : ZMod N), true))
        = (((((r * a.val : ℕ) : ZMod N) + radixLift r N b t), true))
    apply Prod.ext
    · rw [radixLift]
      have h := radix_mul_add_val r N hr hN a t
      calc ((r * (a + t).val + b : ℕ) : ZMod N)
          = ((r * (a + t).val : ℕ) : ZMod N) + (b : ZMod N) := by rw [Nat.cast_add]
        _ = ((r * a.val + r * t.val : ℕ) : ZMod N) + (b : ZMod N) := by rw [h]
        _ = ((r * a.val : ℕ) : ZMod N) + ((r * t.val : ℕ) : ZMod N) + (b : ZMod N) := by
            rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
        _ = ((r * a.val : ℕ) : ZMod N) + ((r * t.val + b : ℕ) : ZMod N) := by
            rw [Nat.cast_add]; ring
    · rfl
  cases ta with
  | false => exact hfalse a
  | true =>
    have hstep := hfalse (a - t)
    have hback : dihedralReflect (N / r) t (a - t, false) = (a, true) := by
      simp [dihedralReflect, sub_add_cancel]
    rw [hback] at hstep
    have hstep' : radixSubgroupEmbedding r N b (a, true)
        = dihedralReflect N (radixLift r N b t) (radixSubgroupEmbedding r N b (a - t, false)) := hstep
    have hinv := dihedralReflect_involutive N (radixLift r N b t)
      (radixSubgroupEmbedding r N b (a - t, false))
    show (((r * (a - t).val : ℕ) : ZMod N), false)
        = dihedralReflect N (radixLift r N b t) (radixSubgroupEmbedding r N b (a, true))
    rw [hstep', hinv]
    rfl

theorem radixRestriction_hides (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) (b : ℕ) (hb : b < r)
    {S : Type} (f : DihedralReg N → S) (t : ZMod (N / r))
    (hf : DihedralReflectionHides N f (radixLift r N b t)) :
    DihedralReflectionHides (N / r) (radixRestrictedOracle r N b f) t := by
  intro p q
  change f (radixSubgroupEmbedding r N b p) = f (radixSubgroupEmbedding r N b q) ↔ _
  rw [hf, ← radixEmbedding_reflect r N hr hN b t,
    (radixEmbedding_injective r N hr hN b hb).eq_iff,
    (radixEmbedding_injective r N hr hN b hb).eq_iff]

theorem radixRestriction_hides_div (r N : ℕ) (hr : r ∣ N) (hN : 0 < N)
    {S : Type} (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) :
    DihedralReflectionHides (N / r)
      (radixRestrictedOracle r N (s.val % r) f) (s.val / r : ZMod (N / r)) := by
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  haveI : NeZero (N / r) := ⟨Nat.ne_of_gt (radix_div_pos r N hr hN)⟩
  have hs := ZMod.val_lt s
  have hmul := radix_mul_div r N hr
  have hle := radix_le r N hr hN
  have hq : s.val / r < N / r := by
    have hlt : s.val < r * (N / r) := by
      calc s.val < N := hs
        _ = r * (N / r) := hmul.symm
    exact Nat.div_lt_of_lt_mul hlt
  have ht : (((s.val / r : ℕ) : ZMod (N / r))).val = s.val / r := ZMod.val_natCast_of_lt hq
  have hlift : s = radixLift r N (s.val % r) ((s.val / r : ℕ) : ZMod (N / r)) := by
    apply ZMod.val_injective N
    have hv := radixLift_val r N hr hN (s.val % r)
      (Nat.mod_lt s.val (radix_pos r N hr hN)) ((s.val / r : ℕ) : ZMod (N / r))
    rw [radixLift, ZMod.val_natCast, ht]
    have hsum : r * (s.val / r) + s.val % r = s.val := by
      rw [Nat.add_comm]
      exact Nat.mod_add_div s.val r
    rw [hsum, Nat.mod_eq_of_lt hs]
  have hf' : DihedralReflectionHides N f
      (radixLift r N (s.val % r) ((s.val / r : ℕ) : ZMod (N / r))) := by
    rw [← hlift]
    exact hf
  exact radixRestriction_hides r N hr hN (s.val % r)
    (Nat.mod_lt s.val (radix_pos r N hr hN)) f
    ((s.val / r : ℕ) : ZMod (N / r)) hf'

theorem radixEmbedding_hidden_mem (r N : ℕ) (hr : r ∣ N) (hN : 0 < N)
    (b : ℕ) (hb : b < r) (s : ZMod N) :
    (∃ a : ZMod (N / r), radixSubgroupEmbedding r N b (a, true) = ((s.val : ZMod N), true))
      ↔ s.val % r = b := by
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  haveI : NeZero (N / r) := ⟨Nat.ne_of_gt (radix_div_pos r N hr hN)⟩
  have hs := ZMod.val_lt s
  have hmul := radix_mul_div r N hr
  have hle := radix_le r N hr hN
  constructor
  · rintro ⟨a, ha⟩
    have ha' : ((r * a.val + b : ℕ) : ZMod N) = (s.val : ZMod N) := by
      have := congrArg Prod.fst ha
      simpa [radixSubgroupEmbedding] using! this
    have hbv : (r * a.val + b : ℕ) % N = s.val % N := by
      have := congrArg ZMod.val ha'
      simpa only [ZMod.val_natCast] using! this
    have ha := ZMod.val_lt a
    have ha1 : r * a.val + b < N := by
      have h3 : r * a.val + r ≤ N := by
        have h4 : a.val + 1 ≤ N / r := by omega
        calc r * a.val + r = (a.val + 1) * r := by ring
          _ ≤ (N / r) * r := Nat.mul_le_mul h4 (le_refl r)
          _ = N := by rw [Nat.mul_comm, hmul]
      omega
    have hb1 : (r * a.val + b : ℕ) % N = r * a.val + b := Nat.mod_eq_of_lt ha1
    have hs1 : s.val % N = s.val := Nat.mod_eq_of_lt hs
    have hsum : r * a.val + b = s.val := by omega
    have : s.val % r = b := by
      calc s.val % r = (r * a.val + b) % r := by rw [hsum]
        _ = (b + a.val * r) % r := by
          rw [Nat.add_comm (r * a.val) b, Nat.mul_comm (r) (a.val)]
        _ = b % r := Nat.add_mul_mod_self_right b a.val r
        _ = b := Nat.mod_eq_of_lt hb
    exact this
  · intro h
    let t : ZMod (N / r) := (s.val / r : ℕ)
    refine ⟨t, ?_⟩
    have hq : s.val / r < N / r := by
      have hlt : s.val < r * (N / r) := by
        calc s.val < N := hs
          _ = r * (N / r) := hmul.symm
      exact Nat.div_lt_of_lt_mul hlt
    have ht : t.val = s.val / r := by
      simp only [t]
      exact ZMod.val_natCast_of_lt hq
    have hsum : r * (s.val / r) + s.val % r = s.val := by
      rw [Nat.add_comm]
      exact Nat.mod_add_div s.val r
    have h3 : r * (s.val / r) + b = s.val := by
      calc r * (s.val / r) + b = r * (s.val / r) + s.val % r := by rw [h]
        _ = s.val := hsum
    have h1 : r * (s.val / r) + b < N := by
      have h4 : s.val / r + 1 ≤ N / r := by omega
      have h5 : r * (s.val / r) + r ≤ N := by
        calc r * (s.val / r) + r = (s.val / r + 1) * r := by ring
          _ ≤ (N / r) * r := Nat.mul_le_mul h4 (le_refl r)
          _ = N := by rw [Nat.mul_comm, hmul]
      omega
    have hcast : ((r * (s.val / r) + b : ℕ) : ZMod N) = (s.val : ZMod N) := by
      apply ZMod.val_injective N
      rw [ZMod.val_natCast, h3, ZMod.val_natCast]
    simp only [radixSubgroupEmbedding]
    rw [ht, hcast]

theorem radixLevelDigit_spec (r : ℕ) (hr : 0 < r) : ∀ (s j : ℕ),
    (radixLevelDigit r s j).val = radixLevelSlope r s j % r := by
  intro s j
  induction j generalizing s with
  | zero => simp [radixLevelDigit, radixLevelSlope]
  | succ j ih =>
    rw [radixLevelDigit_succ, radixLevelSlope_succ, ih (s / r)]

theorem radixRestrictedPhaseRatio (r N : ℕ) (hr : r ∣ N) (hN : 0 < N) [NeZero (N / r)]
    {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg N → S) (s : ZMod N) (hf : DihedralReflectionHides N f s)
    (k : ZMod (N / r)) (t : Bool) (z : S) :
    (fun b => dihedralRecordJoint (N / r) (radixRestrictedOracle r N (s.val % r) f) ((k, b), z)) = 0 ∨
      ∃ c : ℂ, c ≠ 0 ∧
        (fun b => dihedralRecordJoint (N / r) (radixRestrictedOracle r N (s.val % r) f) ((k, b), z)) =
          c • (fun b => cond b (dihedralQubitPhase (N / r) (s.val / r : ZMod (N / r)) k) 1) := by
  have hhide := radixRestriction_hides_div r N hr hN f s hf
  exact radixRecordPhaseRatio (N / r) (radixRestrictedOracle r N (s.val % r) f)
    (s.val / r : ZMod (N / r)) hhide k t z

private theorem radixStep_mul_add_val (r n : ℕ) (hr : 0 < r) (a t : ZMod (r ^ n)) :
    ((r * (a + t).val : ℕ) : ZMod (r ^ (n + 1)))
      = ((r * a.val + r * t.val : ℕ) : ZMod (r ^ (n + 1))) := by
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  haveI : NeZero (r ^ n) := NeZero.pow
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  have hadd : (a + t).val = (a.val + t.val) % r ^ n := ZMod.val_add a t
  rw [hadd]
  apply ZMod.val_injective (r ^ (n + 1))
  simp only [ZMod.val_natCast]
  have hdiv := Nat.div_add_mod (a.val + t.val) (r ^ n)
  have hy : r * (a.val + t.val)
      = r * ((a.val + t.val) % r ^ n) + (a.val + t.val) / r ^ n * r ^ (n + 1) := by
    calc r * (a.val + t.val)
        = r * (r ^ n * ((a.val + t.val) / r ^ n) + (a.val + t.val) % r ^ n) := by rw [hdiv]
      _ = r * (r ^ n * ((a.val + t.val) / r ^ n)) + r * ((a.val + t.val) % r ^ n) := by
        rw [Nat.mul_add]
      _ = ((a.val + t.val) / r ^ n) * r ^ (n + 1) + r * ((a.val + t.val) % r ^ n) := by
        rw [show r * (r ^ n * ((a.val + t.val) / r ^ n)) = ((a.val + t.val) / r ^ n) * r ^ (n + 1) by
          calc r * (r ^ n * ((a.val + t.val) / r ^ n))
              = r * r ^ n * ((a.val + t.val) / r ^ n) := by rw [Nat.mul_assoc]
            _ = (r ^ n * r) * ((a.val + t.val) / r ^ n) := by rw [Nat.mul_comm r (r ^ n)]
            _ = ((a.val + t.val) / r ^ n) * r ^ (n + 1) := by
              rw [Nat.mul_comm ((a.val + t.val) / r ^ n), pow_succ]]
      _ = r * ((a.val + t.val) % r ^ n) + (a.val + t.val) / r ^ n * r ^ (n + 1) := by
        rw [Nat.add_comm]
  calc (r * ((a.val + t.val) % r ^ n)) % r ^ (n + 1)
      = (r * (a.val + t.val)) % r ^ (n + 1) := by
        rw [hy, Nat.add_mul_mod_self_right]
    _ = (r * a.val + r * t.val) % r ^ (n + 1) := by rw [Nat.mul_add]

theorem radixStepEmbedding_injective (r n : ℕ) (hr : 0 < r) (b : ℕ) (hb : b < r) :
    Function.Injective (radixStepEmbedding r n b) := by
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  haveI : NeZero (r ^ n) := NeZero.pow
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  rintro ⟨a, ta⟩ ⟨c, tc⟩ he
  cases ta with
  | false =>
    cases tc with
    | false =>
      have hv := congrArg (fun p : DihedralReg (r ^ (n + 1)) => p.1.val) he
      have ha := ZMod.val_lt a
      have hc := ZMod.val_lt c
      simp only [radixStepEmbedding, ZMod.val_natCast] at hv
      have h1 : r * a.val < r ^ (n + 1) := by
        calc r * a.val < r * r ^ n := Nat.mul_lt_mul_of_pos_left ha hr
          _ = r ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
      have h2 : r * c.val < r ^ (n + 1) := by
        calc r * c.val < r * r ^ n := Nat.mul_lt_mul_of_pos_left hc hr
          _ = r ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv
      have hval : a.val = c.val := Nat.mul_left_cancel hr hv
      exact Prod.ext ((ZMod.val_injective (r ^ n)) hval) rfl
    | true => exact Bool.noConfusion (congrArg Prod.snd he)
  | true =>
    cases tc with
    | false => exact Bool.noConfusion (congrArg Prod.snd he)
    | true =>
      have hv := congrArg (fun p : DihedralReg (r ^ (n + 1)) => p.1.val) he
      have ha := ZMod.val_lt a
      have hc := ZMod.val_lt c
      simp only [radixStepEmbedding, ZMod.val_natCast] at hv
      have h1 : r * a.val + b < r ^ (n + 1) := by
        have hb1 : r * a.val + b < r * a.val + r := by omega
        calc r * a.val + b < r * a.val + r := hb1
          _ = r * (a.val + 1) := by ring
          _ ≤ r * r ^ n := Nat.mul_le_mul (Nat.le_refl r) (Nat.succ_le_of_lt ha)
          _ = r ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
      have h2 : r * c.val + b < r ^ (n + 1) := by
        have hb1 : r * c.val + b < r * c.val + r := by omega
        calc r * c.val + b < r * c.val + r := hb1
          _ = r * (c.val + 1) := by ring
          _ ≤ r * r ^ n := Nat.mul_le_mul (Nat.le_refl r) (Nat.succ_le_of_lt hc)
          _ = r ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv
      have hval : a.val = c.val := Nat.mul_left_cancel hr (Nat.add_right_cancel hv)
      exact Prod.ext ((ZMod.val_injective (r ^ n)) hval) rfl

theorem radixStepEmbedding_reflect (r n : ℕ) (hr : 0 < r) (b : ℕ) (hb : b < r)
    (t : ZMod (r ^ n)) (p : DihedralReg (r ^ n)) :
    radixStepEmbedding r n b (dihedralReflect (r ^ n) t p)
      = dihedralReflect (r ^ (n + 1)) (radixStepLift r n b t) (radixStepEmbedding r n b p) := by
  rcases p with ⟨a, ta⟩
  have hfalse : ∀ a : ZMod (r ^ n),
      radixStepEmbedding r n b (dihedralReflect (r ^ n) t (a, false))
        = dihedralReflect (r ^ (n + 1)) (radixStepLift r n b t)
            (radixStepEmbedding r n b (a, false)) := by
    intro a
    show ((((r * (a + t).val + b : ℕ) : ZMod (r ^ (n + 1))), true))
        = (((((r * a.val : ℕ) : ZMod (r ^ (n + 1))) + radixStepLift r n b t), true))
    apply Prod.ext
    · rw [radixStepLift]
      have h := radixStep_mul_add_val r n hr a t
      calc ((r * (a + t).val + b : ℕ) : ZMod (r ^ (n + 1)))
          = ((r * (a + t).val : ℕ) : ZMod (r ^ (n + 1))) + (b : ZMod (r ^ (n + 1))) := by
            rw [Nat.cast_add]
        _ = ((r * a.val + r * t.val : ℕ) : ZMod (r ^ (n + 1))) + (b : ZMod (r ^ (n + 1))) := by rw [h]
        _ = ((r * a.val : ℕ) : ZMod (r ^ (n + 1))) + ((r * t.val : ℕ) : ZMod (r ^ (n + 1)))
            + (b : ZMod (r ^ (n + 1))) := by rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
        _ = ((r * a.val : ℕ) : ZMod (r ^ (n + 1))) + ((r * t.val + b : ℕ) : ZMod (r ^ (n + 1))) := by
            rw [Nat.cast_add]; ring
    · rfl
  cases ta with
  | false => exact hfalse a
  | true =>
    have hstep := hfalse (a - t)
    have hback : dihedralReflect (r ^ n) t (a - t, false) = (a, true) := by
      simp [dihedralReflect, sub_add_cancel]
    rw [hback] at hstep
    have hstep' : radixStepEmbedding r n b (a, true)
        = dihedralReflect (r ^ (n + 1)) (radixStepLift r n b t)
            (radixStepEmbedding r n b (a - t, false)) := hstep
    have hinv := dihedralReflect_involutive (r ^ (n + 1)) (radixStepLift r n b t)
      (radixStepEmbedding r n b (a - t, false))
    show (((r * (a - t).val : ℕ) : ZMod (r ^ (n + 1))), false)
        = dihedralReflect (r ^ (n + 1)) (radixStepLift r n b t) (radixStepEmbedding r n b (a, true))
    rw [hstep', hinv]
    rfl

theorem radixStepLift_val (r n : ℕ) (hr : 0 < r) (b : ℕ) (hb : b < r) (t : ZMod (r ^ n)) :
    (radixStepLift r n b t).val = r * t.val + b := by
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  haveI : NeZero (r ^ n) := NeZero.pow
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  have ht : t.val < r ^ n := ZMod.val_lt t
  simp only [radixStepLift, ZMod.val_natCast]
  refine Nat.mod_eq_of_lt ?_
  calc r * t.val + b < r * t.val + r := by omega
    _ = r * (t.val + 1) := by ring
    _ ≤ r * r ^ n := Nat.mul_le_mul (Nat.le_refl r) (Nat.succ_le_of_lt ht)
    _ = r ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

theorem radixStepLift_eq (r n : ℕ) (hr : 0 < r) (b : ℕ) (hb : b < r) (t : ZMod (r ^ n))
    (s : ZMod (r ^ (n + 1))) (hs : s.val = r * t.val + b) :
    radixStepLift r n b t = s := by
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  apply ZMod.val_injective (r ^ (n + 1))
  rw [radixStepLift_val r n hr b hb t]
  exact hs.symm

theorem radixStepOracle_hides (r n : ℕ) (hr : 0 < r) (b : ℕ) (hb : b < r)
    {S : Type} (f : DihedralReg (r ^ (n + 1)) → S) (t : ZMod (r ^ n))
    (hf : DihedralReflectionHides (r ^ (n + 1)) f (radixStepLift r n b t)) :
    DihedralReflectionHides (r ^ n) (radixStepOracle r n b f) t := by
  intro p q
  change f (radixStepEmbedding r n b p) = f (radixStepEmbedding r n b q) ↔ _
  rw [hf, ← radixStepEmbedding_reflect r n hr b hb t,
    (radixStepEmbedding_injective r n hr b hb).eq_iff,
    (radixStepEmbedding_injective r n hr b hb).eq_iff]

noncomputable def radixRecursionLevel {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (r : ℕ) [NeZero r] (n m p : ℕ) (f : DihedralReg (r ^ (n + 1)) → S)
    (cont : ℕ → PMF (Option (ZMod (r ^ n)))) :
    PMF (Option (ZMod (r ^ (n + 1)))) :=
  (radixObservedRecords f m).bind fun L =>
    match radixRecoveryDecide f r (n + 1) p L with
    | none => pure none
    | some b =>
      (cont b.val).bind fun rest =>
        match rest with
        | none => pure none
        | some s' => pure (some (radixStepLift r n b.val s'))

noncomputable def radixRecursionRun {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (r : ℕ) [NeZero r] : ∀ (n m p : ℕ) (f : DihedralReg (r ^ n) → S),
      PMF (Option (ZMod (r ^ n)))
  | 0, _m, _p, _f => pure (some 0)
  | (n + 1), m, p, f =>
    radixRecursionLevel r n m p f
      (fun b => radixRecursionRun r n m p (radixStepOracle r n b f))

theorem radixRecursionRun_zero {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (r : ℕ) [NeZero r] (m p : ℕ) (f : DihedralReg (r ^ 0) → S) :
    radixRecursionRun r 0 m p f = pure (some 0) := by
  rw [radixRecursionRun]

theorem radixRecursionRun_succ {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (r : ℕ) [NeZero r] (n m p : ℕ) (f : DihedralReg (r ^ (n + 1)) → S) :
    radixRecursionRun r (n + 1) m p f
      = radixRecursionLevel r n m p f
          (fun b => radixRecursionRun r n m p (radixStepOracle r n b f)) := by
  rw [radixRecursionRun]

theorem radix_pow_div (r n : ℕ) (hr : 0 < r) : r ^ (n + 1) / r = r ^ n := by
  rw [pow_succ, Nat.mul_comm (r ^ n) r, Nat.mul_div_right (r ^ n) hr]

private theorem radixStepLift_quot (r n : ℕ) (hr : 0 < r) (s : ZMod (r ^ (n + 1)))
    (hq : s.val / r < r ^ n) :
    radixStepLift r n (s.val % r) ((s.val / r : ℕ) : ZMod (r ^ n)) = s := by
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  haveI : NeZero (r ^ n) := NeZero.pow
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  have ht : ((s.val / r : ℕ) : ZMod (r ^ n)).val = s.val / r :=
    ZMod.val_natCast_of_lt hq
  apply radixStepLift_eq r n hr (s.val % r) (Nat.mod_lt s.val (by omega)) _ _
  rw [ht]
  exact (Nat.mod_add_div s.val r).symm.trans (Nat.add_comm _ _)

private theorem radixStepLift_inj (r n : ℕ) (hr : 0 < r) (b : ℕ) (hb : b < r)
    (s' t : ZMod (r ^ n)) (h : radixStepLift r n b s' = radixStepLift r n b t) : s' = t := by
  haveI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  haveI : NeZero (r ^ n) := NeZero.pow
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  apply ZMod.val_injective (r ^ n)
  have hv : (radixStepLift r n b s').val = (radixStepLift r n b t).val := congrArg ZMod.val h
  rw [radixStepLift_val r n hr b hb s', radixStepLift_val r n hr b hb t] at hv
  exact Nat.mul_left_cancel hr (Nat.add_right_cancel hv)

theorem radixRecursionLevel_wrong_zero (r : ℕ) [NeZero r] (hr : 2 ≤ r) {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (n m p : ℕ) (f : DihedralReg (r ^ (n + 1)) → S)
    (s : ZMod (r ^ (n + 1))) (hf : DihedralReflectionHides (r ^ (n + 1)) f s)
    (cont : ℕ → PMF (Option (ZMod (r ^ n))))
    (hcont : ∀ t : ZMod (r ^ n), t ≠ ((s.val / r : ℕ) : ZMod (r ^ n)) →
      (cont (s.val % r)) (some t) = 0)
    (u : ZMod (r ^ (n + 1))) (hu : u ≠ s) :
    (radixRecursionLevel r n m p f cont) (some u) = 0 := by
  haveI : NeZero (r ^ n) := NeZero.pow
  haveI : NeZero (r ^ (n + 1)) := NeZero.pow
  have hs := ZMod.val_lt s
  have hq : s.val / r < r ^ n := by
    refine Nat.div_lt_of_lt_mul ?_
    calc s.val < r ^ (n + 1) := hs
      _ = r * r ^ n := by rw [pow_succ, Nat.mul_comm]
  have hquot := radixStepLift_quot r n (by omega) s hq
  unfold radixRecursionLevel
  rw [PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun L => ?_
  cases hd : radixRecoveryDecide f r (n + 1) p L with
  | none =>
    have hz : (pure none : PMF (Option (ZMod (r ^ (n + 1))))) (some u) = 0 := by
      exact PMF.pure_apply_of_ne none (some u) (fun h => by cases h)
    simp [hz]
  | some b =>
    simp only [show (match some b with | none => pure none | some b => _) = _ from rfl]
    have hval : b.val = s.val % r := by
      rcases radixRecoveryDecide_value r (n + 1) hr (by omega) f s hf p L with h | h
      · exact absurd (hd.symm.trans h) (by simp)
      · have hb : b = ((s.val % r : ℕ) : ZMod r) := Option.some.inj (hd.symm.trans h)
        rw [hb]
        exact ZMod.val_natCast_of_lt (Nat.mod_lt s.val (by omega))
    rw [hval]
    have hsum : ((cont (s.val % r)).bind (fun rest =>
        match rest with
        | none => pure none
        | some s' => pure (some (radixStepLift r n (s.val % r) s')))) (some u) = 0 := by
      rw [PMF.bind_apply]
      refine ENNReal.tsum_eq_zero.2 fun rest => ?_
      cases rest with
      | none =>
        have hz : (pure none : PMF (Option (ZMod (r ^ (n + 1))))) (some u) = 0 := by
          exact PMF.pure_apply_of_ne none (some u) (fun h => by cases h)
        simp [hz]
      | some s' =>
        simp only [show (match some s' with | none => pure none | some s' => _) = _ from rfl]
        by_cases heq : s' = ((s.val / r : ℕ) : ZMod (r ^ n))
        · have hlift : radixStepLift r n (s.val % r) s' = s := by
            rw [heq]
            exact hquot
          by_cases he : u = radixStepLift r n (s.val % r) s'
          · exfalso
            rw [hlift] at he
            exact hu he
          · have hz : (pure (some (radixStepLift r n (s.val % r) s')) : PMF (Option (ZMod (r ^ (n + 1))))) (some u) = 0 := by
              exact PMF.pure_apply_of_ne (some (radixStepLift r n (s.val % r) s')) (some u)
                (fun h => he (Option.some.inj h))
            simp [hz]
        · have hz : (cont (s.val % r)) (some s') = 0 := hcont s' heq
          simp [hz]
    rw [hsum, mul_zero]

theorem radixRecursionRun_wrong_zero (r : ℕ) [NeZero r] (hr : 2 ≤ r) {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] :
    ∀ (n : ℕ) (f : DihedralReg (r ^ n) → S) (s : ZMod (r ^ n))
      (hf : DihedralReflectionHides (r ^ n) f s) (m p : ℕ) (u : ZMod (r ^ n)) (hu : u ≠ s),
      (radixRecursionRun r n m p f) (some u) = 0 := by
  intro n
  induction n with
  | zero =>
    intro f s hf m p u hu
    haveI : NeZero (r ^ 0) := NeZero.pow
    exfalso
    have hval : u.val = s.val := by
      have h1 := ZMod.val_lt u
      have h2 := ZMod.val_lt s
      have hr0 : r ^ 0 = 1 := pow_zero r
      have h1' : u.val < 1 := h1.trans_le (by rw [hr0])
      have h2' : s.val < 1 := h2.trans_le (by rw [hr0])
      omega
    exact hu (ZMod.val_injective _ hval)
  | succ n ih =>
    intro f s hf m p u hu
    haveI : NeZero (r ^ n) := NeZero.pow
    haveI : NeZero (r ^ (n + 1)) := NeZero.pow
    have hs := ZMod.val_lt s
    have hq : s.val / r < r ^ n := by
      refine Nat.div_lt_of_lt_mul ?_
      calc s.val < r ^ (n + 1) := hs
        _ = r * r ^ n := by rw [pow_succ, Nat.mul_comm]
    have hquot := radixStepLift_quot r n (by omega) s hq
    rw [radixRecursionRun_succ]
    refine radixRecursionLevel_wrong_zero r hr n m p f s hf
      (fun b => radixRecursionRun r n m p (radixStepOracle r n b f)) ?_ u hu
    intro t ht
    have hf' : DihedralReflectionHides (r ^ n)
        (radixStepOracle r n (s.val % r) f) ((s.val / r : ℕ) : ZMod (r ^ n)) := by
      refine radixStepOracle_hides r n (by omega) (s.val % r) (Nat.mod_lt s.val (by omega))
        f ((s.val / r : ℕ) : ZMod (r ^ n)) ?_
      rw [hquot]
      exact hf
    exact ih (radixStepOracle r n (s.val % r) f) ((s.val / r : ℕ) : ZMod (r ^ n)) hf' m p t ht

private def radix_greedyStep (r N : ℕ) (best : Option (ℕ × ℕ)) (q : ℕ × ℕ) : Option (ℕ × ℕ) :=
  match best with
  | none => some q
  | some q' =>
      if radixPairValue r N q.1 q.2 > radixPairValue r N q'.1 q'.2 then some q else best

private theorem radix_foldl_mem (r N : ℕ) :
    ∀ (ps : List (ℕ × ℕ)) (acc : Option (ℕ × ℕ)) (p : ℕ × ℕ),
      ps.foldl (radix_greedyStep r N) acc = some p →
        acc = some p ∨ p ∈ ps := by
  intro ps
  induction ps with
  | nil =>
    intro acc p h
    exact Or.inl h
  | cons q qs ih =>
    intro acc p h
    rw [List.foldl_cons] at h
    have hfold := ih (radix_greedyStep r N acc q) p h
    rcases hfold with hfold | hfold
    · cases acc with
      | none =>
        have hfold' : (some q : Option (ℕ × ℕ)) = some p := by
          simpa only [radix_greedyStep] using! hfold
        have hqp : q = p := Option.some.inj hfold'
        subst hqp
        exact Or.inr (by simp)
      | some q' =>
        by_cases hc : radixPairValue r N q.1 q.2 > radixPairValue r N q'.1 q'.2
        · have hfold' : (some q : Option (ℕ × ℕ)) = some p := by
            simpa only [radix_greedyStep, hc, if_true] using! hfold
          have hqp : q = p := Option.some.inj hfold'
          subst hqp
          exact Or.inr (by simp)
        · have hfold' : (some q' : Option (ℕ × ℕ)) = some p := by
            simpa only [radix_greedyStep, hc, if_false] using! hfold
          exact Or.inl hfold'
    · exact Or.inr (by simp [hfold])

theorem radixGreedyPair_mem (r N : ℕ) {L : List ℕ} {k ℓ : ℕ}
    (hp : radixGreedyPair r N L = some (k, ℓ)) :
    k ∈ radixMinAlphaSublist r L ∧ ℓ ∈ radixMinAlphaSublist r L ∧ k ≠ ℓ := by
  have hdef : radixGreedyPair r N L
      = (radixPairs (radixMinAlphaSublist r L)).foldl (radix_greedyStep r N) none := rfl
  have hfold : (radixPairs (radixMinAlphaSublist r L)).foldl (radix_greedyStep r N) none
      = some (k, ℓ) := by
    rw [← hdef, hp]
  have hmem : (k, ℓ) ∈ radixPairs (radixMinAlphaSublist r L) :=
    (radix_foldl_mem r N _ none _ hfold).resolve_left (by simp)
  simp only [radixPairs, List.mem_flatMap] at hmem
  obtain ⟨k', hk', hmap⟩ := hmem
  simp only [List.mem_map] at hmap
  obtain ⟨ℓ', hℓ', hfl⟩ := hmap
  simp only [List.mem_filter] at hℓ'
  obtain ⟨hℓmem, hne⟩ := hℓ'
  have hne' : ℓ' ≠ k' := by
    simpa using! hne
  injection hfl with hk'' hℓ''
  subst hk''
  subst hℓ''
  exact ⟨hk', hℓmem, Ne.symm hne'⟩

theorem radixExpectedChildValue_ge_parent (r n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hk : k < r ^ n) (hℓ : ℓ < r ^ n) (hne : k ≠ ℓ)
    (hα : radixAlpha r k = radixAlpha r ℓ) (hsum : k + ℓ ≠ r ^ n) :
    radixValue r n k ≤ radixExpectedChildValue r n k ℓ := by
  have hk'lt : (k + ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by positivity)
  have hk''lt : (k + (r ^ n) - ℓ) % (r ^ n) < r ^ n := Nat.mod_lt _ (by positivity)
  have hαadd : radixAlpha r ((k + ℓ) % (r ^ n)) ≥ radixAlpha r k :=
    radixChild_alpha_ge_add r n k ℓ hr hn hk hℓ hne hα hsum
  have hαsub : radixAlpha r ((k + (r ^ n) - ℓ) % (r ^ n)) ≥ radixAlpha r k :=
    radixChild_alpha_ge_sub r n k ℓ hr hn hk hℓ hne hα
  have hvadd : radixValue r n k ≤ radixValue r n ((k + ℓ) % (r ^ n)) :=
    radixValue_ge_of_alpha_ge r n ((k + ℓ) % (r ^ n)) k hr hn hk'lt hk hαadd
  have hvsub : radixValue r n k ≤ radixValue r n ((k + (r ^ n) - ℓ) % (r ^ n)) :=
    radixValue_ge_of_alpha_ge r n ((k + (r ^ n) - ℓ) % (r ^ n)) k hr hn hk''lt hk hαsub
  unfold radixExpectedChildValue
  linarith

theorem radixQuantumPeriodValue_step_lower {n m : ℕ} {L : List ℕ} (hn : 1 ≤ n)
    (hbound : ∀ k ∈ L, k < 3 ^ n)
    (hnonzero : ∀ k ∈ L, k ≠ 0)
    (hnodup : L.Nodup)
    (hstates : ∀ k ∈ L, ∀ ℓ ∈ L, k ≠ ℓ → k + ℓ ≠ 3 ^ n)
    (ham : radixMinAlpha 3 L + m + 1 ≤ n)
    (hgreedy : radixGreedyValue 3 (3 ^ n) L ≤ radixMinAlpha 3 L + m)
    (hm : (m : ℝ) ≤ Real.sqrt (2 * ((n - 1 - radixMinAlpha 3 L : ℕ) : ℝ))) :
    radixListValue 3 n L - 1 ≤ radixQuantumPeriodValue 3 n L := by
  have hattr : radixPeriodAttrition 3 n (radixMinAlphaSublist 3 L) ≤ 1 :=
    radixPeriodAttrition_le_one hn hbound hnonzero hnodup hstates ham hgreedy hm
  have hsub : radixListValue 3 n (radixMinAlphaSublist 3 L) ≤ 1 := by
    have h : radixListValue 3 n (radixMinAlphaSublist 3 L)
        = radixPeriodAttrition 3 n (radixMinAlphaSublist 3 L) := rfl
    rw [h]
    exact hattr
  have hpart : radixListValue 3 n (radixKeptLabels 3 L)
      + radixListValue 3 n (radixMinAlphaSublist 3 L) = radixListValue 3 n L :=
    radixListValue_partition 3 n L
  cases hp : radixGreedyPair 3 (3 ^ n) L with
  | none =>
    have hq : radixQuantumPeriodValue 3 n L = radixListValue 3 n (radixKeptLabels 3 L) := by
      unfold radixQuantumPeriodValue
      rw [hp]
    rw [hq, ← hpart]
    linarith
  | some kl =>
    obtain ⟨k, ℓ⟩ := kl
    have hq : radixQuantumPeriodValue 3 n L
        = radixListValue 3 n (radixKeptLabels 3 L) + radixExpectedChildValue 3 n k ℓ := by
      unfold radixQuantumPeriodValue
      rw [hp]
    have hE : 0 ≤ radixExpectedChildValue 3 n k ℓ := by
      unfold radixExpectedChildValue
      have h1 := radixValue_pos 3 n ((k + ℓ) % (3 ^ n))
      have h2 := radixValue_pos 3 n ((k + (3 ^ n) - ℓ) % (3 ^ n))
      linarith
    rw [hq, ← hpart]
    linarith

theorem radixQuantumPeriodValue_step_lower_pair {n m : ℕ} {L : List ℕ} {k ℓ : ℕ} (hn : 1 ≤ n)
    (hbound : ∀ j ∈ L, j < 3 ^ n)
    (hnonzero : ∀ j ∈ L, j ≠ 0)
    (hnodup : L.Nodup)
    (hstates : ∀ j ∈ L, ∀ j' ∈ L, j ≠ j' → j + j' ≠ 3 ^ n)
    (ham : radixMinAlpha 3 L + m + 1 ≤ n)
    (hgreedy : radixGreedyValue 3 (3 ^ n) L ≤ radixMinAlpha 3 L + m)
    (hm : (m : ℝ) ≤ Real.sqrt (2 * ((n - 1 - radixMinAlpha 3 L : ℕ) : ℝ)))
    (hpair : radixGreedyPair 3 (3 ^ n) L = some (k, ℓ)) :
    radixListValue 3 n L - 1 + radixValue 3 n k ≤ radixQuantumPeriodValue 3 n L := by
  have hattr : radixPeriodAttrition 3 n (radixMinAlphaSublist 3 L) ≤ 1 :=
    radixPeriodAttrition_le_one hn hbound hnonzero hnodup hstates ham hgreedy hm
  have hsub : radixListValue 3 n (radixMinAlphaSublist 3 L) ≤ 1 := by
    have h : radixListValue 3 n (radixMinAlphaSublist 3 L)
        = radixPeriodAttrition 3 n (radixMinAlphaSublist 3 L) := rfl
    rw [h]
    exact hattr
  have hpart : radixListValue 3 n (radixKeptLabels 3 L)
      + radixListValue 3 n (radixMinAlphaSublist 3 L) = radixListValue 3 n L :=
    radixListValue_partition 3 n L
  have hmem := radixGreedyPair_mem (r := 3) (N := 3 ^ n) (L := L) (k := k) (ℓ := ℓ) hpair
  have hmem1 := hmem.1
  rw [radixMinAlphaSublist, List.mem_filter] at hmem1
  obtain ⟨hsubmem, heq⟩ := hmem1
  have hmem2 := hmem.2.1
  rw [radixMinAlphaSublist, List.mem_filter] at hmem2
  obtain ⟨hsubmem', heq'⟩ := hmem2
  have hkL : k ∈ L := hsubmem
  have hℓL : ℓ ∈ L := hsubmem'
  have hαsub : radixAlpha 3 k = radixMinAlpha 3 L := by
    simp only [beq_iff_eq] at heq
    exact heq
  have hαsub' : radixAlpha 3 ℓ = radixMinAlpha 3 L := by
    simp only [beq_iff_eq] at heq'
    exact heq'
  have hα : radixAlpha 3 k = radixAlpha 3 ℓ := by
    rw [hαsub, hαsub']
  have hE : radixValue 3 n k ≤ radixExpectedChildValue 3 n k ℓ :=
    radixExpectedChildValue_ge_parent 3 n k ℓ (by omega) hn
      (hbound k hkL) (hbound ℓ hℓL) hmem.2.2 hα (hstates k hkL ℓ hℓL hmem.2.2)
  have hq : radixQuantumPeriodValue 3 n L
      = radixListValue 3 n (radixKeptLabels 3 L) + radixExpectedChildValue 3 n k ℓ := by
    unfold radixQuantumPeriodValue
    rw [hpair]
  rw [hq, ← hpart]
  linarith

theorem radixQuantumPeriodValue_avg (r n : ℕ) (L : List ℕ) :
    (radixListValue r n (radixQuantumPeriodStep r (r ^ n) false L)
      + radixListValue r n (radixQuantumPeriodStep r (r ^ n) true L)) / 2
      = radixQuantumPeriodValue r n L := by
  cases hp : radixGreedyPair r (r ^ n) L with
  | none =>
    have hstep : radixQuantumPeriodStep r (r ^ n) false L = radixKeptLabels r L := by
      unfold radixQuantumPeriodStep
      rw [hp]
    have hstep' : radixQuantumPeriodStep r (r ^ n) true L = radixKeptLabels r L := by
      unfold radixQuantumPeriodStep
      rw [hp]
    have hq : radixQuantumPeriodValue r n L = radixListValue r n (radixKeptLabels r L) := by
      unfold radixQuantumPeriodValue
      rw [hp]
    rw [hstep, hstep', hq]
    simp [radixListValue]
  | some kl =>
    obtain ⟨k, ℓ⟩ := kl
    have hstep : radixQuantumPeriodStep r (r ^ n) false L
        = radixKeptLabels r L ++ [(k + ℓ) % (r ^ n)] := by
      unfold radixQuantumPeriodStep
      rw [hp]
      simp
    have hstep' : radixQuantumPeriodStep r (r ^ n) true L
        = radixKeptLabels r L ++ [(k + r ^ n - ℓ) % (r ^ n)] := by
      unfold radixQuantumPeriodStep
      rw [hp]
      simp
    have hval : radixListValue r n (radixKeptLabels r L ++ [(k + ℓ) % (r ^ n)])
        = radixListValue r n (radixKeptLabels r L) + radixValue r n ((k + ℓ) % (r ^ n)) := by
      unfold radixListValue
      simp [List.map_append, List.sum_append]
    have hval' : radixListValue r n (radixKeptLabels r L ++ [(k + r ^ n - ℓ) % (r ^ n)])
        = radixListValue r n (radixKeptLabels r L)
          + radixValue r n ((k + r ^ n - ℓ) % (r ^ n)) := by
      unfold radixListValue
      simp [List.map_append, List.sum_append]
    have hq : radixQuantumPeriodValue r n L
        = radixListValue r n (radixKeptLabels r L) + radixExpectedChildValue r n k ℓ := by
      unfold radixQuantumPeriodValue
      rw [hp]
    rw [hstep, hstep', hval, hval', hq]
    unfold radixExpectedChildValue
    ring

theorem radixQuantumSieve_value_lower (n : ℕ) (hn : 1 ≤ n) {L : List ℕ} :
    ∀ (p : ℕ), RadixQuantumRunConditions n p L →
      radixListValue 3 n L - (p : ℝ) ≤ radixQuantumRunValue 3 n (3 ^ n) p L := by
  intro p
  induction p generalizing L with
  | zero =>
    intro hp
    rw [radixQuantumRunValue]
    linarith
  | succ p ih =>
    intro hp
    have hcond := hp
    simp only [RadixQuantumRunConditions] at hcond
    obtain ⟨hper, hbranches⟩ := hcond
    obtain ⟨m, ham, hm, hgreedy⟩ := hper.shared
    have hstep : radixListValue 3 n L - 1 ≤ radixQuantumPeriodValue 3 n L := by
      exact radixQuantumPeriodValue_step_lower hn hper.bound hper.nonzero hper.nodup
        hper.states ham hgreedy hm
    have hfalse := ih (L := radixQuantumPeriodStep 3 (3 ^ n) false L) (hbranches false)
    have htrue := ih (L := radixQuantumPeriodStep 3 (3 ^ n) true L) (hbranches true)
    have hrun : radixQuantumRunValue 3 n (3 ^ n) (p + 1) L
        = (radixQuantumRunValue 3 n (3 ^ n) p (radixQuantumPeriodStep 3 (3 ^ n) false L)
          + radixQuantumRunValue 3 n (3 ^ n) p (radixQuantumPeriodStep 3 (3 ^ n) true L)) / 2 := rfl
    have havg := radixQuantumPeriodValue_avg 3 n L
    have hpcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
    rw [hrun]
    linarith

theorem radixQuantumPeriodStep_labels_lt (r N : ℕ) (hN : 0 < N) {L : List ℕ}
    (hL : ∀ k ∈ L, k < N) (b : Bool) :
    ∀ k ∈ radixQuantumPeriodStep r N b L, k < N := by
  cases hp : radixGreedyPair r N L with
  | none =>
    have hstep : radixQuantumPeriodStep r N b L = radixKeptLabels r L := by
      simp only [radixQuantumPeriodStep, hp]
    intro k hk
    rw [hstep] at hk
    exact hL k (List.mem_filter.mp hk).1
  | some kl =>
    obtain ⟨k, ℓ⟩ := kl
    have hstep : radixQuantumPeriodStep r N b L
        = radixKeptLabels r L ++ [if b then (k + N - ℓ) % N else (k + ℓ) % N] := by
      simp only [radixQuantumPeriodStep, hp]
    intro j hj
    rw [hstep] at hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hL j (List.mem_filter.mp hj).1
    · simp only [List.mem_singleton] at hj
      subst hj
      split <;> exact Nat.mod_lt _ hN

theorem radixQuantumLeaves_labels_lt (r N : ℕ) (hN : 0 < N) (p : ℕ) {L : List ℕ}
    (hL : ∀ k ∈ L, k < N) :
    ∀ leaf ∈ radixQuantumLeaves r N p L, ∀ k ∈ leaf, k < N := by
  induction p generalizing L with
  | zero =>
    intro leaf hleaf k hk
    simp only [radixQuantumLeaves, List.mem_singleton] at hleaf
    subst hleaf
    exact hL k hk
  | succ p ih =>
    intro leaf hleaf k hk
    simp only [radixQuantumLeaves, List.mem_append] at hleaf
    rcases hleaf with hleaf | hleaf
    · exact ih (L := radixQuantumPeriodStep r N false L)
        (radixQuantumPeriodStep_labels_lt r N hN hL false) leaf hleaf k hk
    · exact ih (L := radixQuantumPeriodStep r N true L)
        (radixQuantumPeriodStep_labels_lt r N hN hL true) leaf hleaf k hk

theorem radixQuantumLeaves_length (r N : ℕ) (p : ℕ) (L : List ℕ) :
    (radixQuantumLeaves r N p L).length = 2 ^ p := by
  induction p generalizing L with
  | zero => simp [radixQuantumLeaves]
  | succ p ih =>
    simp only [radixQuantumLeaves, List.length_append]
    rw [ih, ih]
    simp only [Nat.pow_succ]
    ring

theorem radixQuantumRunValue_eq_mean (r n N : ℕ) (p : ℕ) (L : List ℕ) :
    radixQuantumRunValue r n N p L
      = ((radixQuantumLeaves r N p L).map (radixListValue r n)).sum
        / (radixQuantumLeaves r N p L).length := by
  induction p generalizing L with
  | zero =>
    simp [radixQuantumRunValue, radixQuantumLeaves, radixListValue]
  | succ p ih =>
    have hsum : ((radixQuantumLeaves r N (p + 1) L).map (radixListValue r n)).sum
        = ((radixQuantumLeaves r N p (radixQuantumPeriodStep r N false L)).map
            (radixListValue r n)).sum
          + ((radixQuantumLeaves r N p (radixQuantumPeriodStep r N true L)).map
            (radixListValue r n)).sum := by
      simp only [radixQuantumLeaves, List.map_append, List.sum_append]
    have hlen : (radixQuantumLeaves r N (p + 1) L).length
        = (radixQuantumLeaves r N p (radixQuantumPeriodStep r N false L)).length
          + (radixQuantumLeaves r N p (radixQuantumPeriodStep r N true L)).length := by
      simp only [radixQuantumLeaves, List.length_append]
    have h1 := ih (L := radixQuantumPeriodStep r N false L)
    have h2 := ih (L := radixQuantumPeriodStep r N true L)
    have hlen1 := radixQuantumLeaves_length r N p (radixQuantumPeriodStep r N false L)
    have hlen2 := radixQuantumLeaves_length r N p (radixQuantumPeriodStep r N true L)
    have hcast : ((2 : ℕ) ^ p : ℝ) = (2 : ℝ) ^ p := by push_cast; ring
    rw [radixQuantumRunValue, hsum, hlen, h1, h2, hlen1, hlen2]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    have hne : (2 : ℝ) ^ p ≠ 0 := by positivity
    field_simp
    ring

private theorem radix_listValue_sum_eq_length {n : ℕ} (ls : List (List ℕ))
    (h : ∀ leaf ∈ ls, radixListValue 3 n leaf = (leaf.length : ℝ)) :
    (ls.map (radixListValue 3 n)).sum = (ls.map (fun leaf => (leaf.length : ℝ))).sum := by
  induction ls with
  | nil => simp
  | cons leaf ls ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h leaf (List.mem_cons_self),
        ih (fun leaf' hleaf' => h leaf' (List.mem_cons_of_mem _ hleaf'))]

private theorem list_sum_eq_zero {α : Type} (ls : List α) (f : α → ℝ)
    (h : ∀ x ∈ ls, f x = 0) : (ls.map f).sum = 0 := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h x (List.mem_cons_self), ih (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))]
    simp

theorem radixQuantumSieve_final_states (n : ℕ) (hn : 1 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < 3 ^ n) (hlen : L.length = radixFreshRecords n)
    (hp : RadixQuantumRunConditions n (n - 1) L)
    (hfinal : ∀ leaf ∈ radixQuantumLeaves 3 (3 ^ n) (n - 1) L,
      ∀ k ∈ leaf, radixFinalTest 3 n k) :
    ∃ leaf ∈ radixQuantumLeaves 3 (3 ^ n) (n - 1) L, 1 ≤ leaf.length := by
  have hval_of : ∀ leaf ∈ radixQuantumLeaves 3 (3 ^ n) (n - 1) L,
      radixListValue 3 n leaf = (leaf.length : ℝ) := by
    intro leaf hleafmem
    have hbound : ∀ k ∈ leaf, k < 3 ^ n :=
      radixQuantumLeaves_labels_lt 3 (3 ^ n) (by positivity) (n - 1) hL leaf hleafmem
    exact radix_listValue_eq_card_of_final n hn hbound (hfinal leaf hleafmem)
  have hsumlen : ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).map
        (fun leaf => (leaf.length : ℝ))).sum
      = ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).map (radixListValue 3 n)).sum :=
    (radix_listValue_sum_eq_length _ hval_of).symm
  have hcount : (radixQuantumLeaves 3 (3 ^ n) (n - 1) L).length = 2 ^ (n - 1) :=
    radixQuantumLeaves_length 3 (3 ^ n) (n - 1) L
  have hcountpos : 0 < (radixQuantumLeaves 3 (3 ^ n) (n - 1) L).length := by
    rw [hcount]
    positivity
  have hcountposR : (0 : ℝ) < ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).length : ℝ) := by
    exact_mod_cast hcountpos
  have hmean := radixQuantumRunValue_eq_mean 3 n (3 ^ n) (n - 1) L
  have hval := radixQuantumSieve_value_lower n hn (n - 1) hp
  have hinit := radixInitialValue_ge n hn hL hlen
  have hpcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have h1 : ((n - 1 : ℕ) + 1 : ℕ) = n := by omega
    have h2 : (((n - 1 : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) := by rw [h1]
    have h3 : (((n - 1 : ℕ) + 1 : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hrun : (1 : ℝ) ≤ radixQuantumRunValue 3 n (3 ^ n) (n - 1) L := by
    linarith
  have hsumge : (radixQuantumLeaves 3 (3 ^ n) (n - 1) L).length
      ≤ ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).map (radixListValue 3 n)).sum := by
    have h2 : (1 : ℝ) ≤ ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).map
        (radixListValue 3 n)).sum / (radixQuantumLeaves 3 (3 ^ n) (n - 1) L).length := by
      rw [← hmean]
      exact hrun
    have h3 : (1 : ℝ) * (radixQuantumLeaves 3 (3 ^ n) (n - 1) L).length
        ≤ ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).map (radixListValue 3 n)).sum :=
      (le_div_iff₀ hcountposR).mp h2
    linarith
  by_contra hcon
  have hzeroLen : ∀ leaf ∈ radixQuantumLeaves 3 (3 ^ n) (n - 1) L, leaf.length = 0 := by
    intro leaf hleafmem
    by_contra hne
    have hpos : 1 ≤ leaf.length := by omega
    exact hcon ⟨leaf, hleafmem, hpos⟩
  have hzero : ((radixQuantumLeaves 3 (3 ^ n) (n - 1) L).map (radixListValue 3 n)).sum = 0 := by
    rw [← hsumlen]
    exact list_sum_eq_zero _ _ (fun leaf hleafmem => by
      have hlen0 : leaf.length = 0 := hzeroLen leaf hleafmem
      exact_mod_cast hlen0)
  linarith

theorem radixFinalStateLabel_alpha (r n a : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n)
    (ha0 : 0 < a) (ha1 : a < r) :
    radixAlpha r (radixFinalStateLabel r n a) = n - 1 := by
  have hrpos : 0 < r := by omega
  have hrpow : 0 < r ^ (n - 1) := Nat.pow_pos hrpos
  have hpos : 0 < a * r ^ (n - 1) := Nat.mul_pos ha0 hrpow
  have hrw : r * r ^ (n - 1) = r ^ n := by
    have h1 : r ^ n = r ^ (n - 1 + 1) := by
      congr 1
      omega
    have h2 : r ^ (n - 1 + 1) = r ^ (n - 1) * r := by rw [pow_add, pow_one]
    calc r * r ^ (n - 1) = r ^ (n - 1) * r := Nat.mul_comm _ _
      _ = r ^ (n - 1 + 1) := h2.symm
      _ = r ^ n := h1.symm
  have hlt : a * r ^ (n - 1) < r ^ n := by
    have h1 : a * r ^ (n - 1) < r * r ^ (n - 1) := (Nat.mul_lt_mul_right hrpow).2 ha1
    rw [← hrw]
    exact h1
  have hge : n - 1 ≤ radixAlpha r (a * r ^ (n - 1)) := by
    refine radixAlpha_ge_of_dvd r (a * r ^ (n - 1)) (n - 1) hr hpos ?_
    show r ^ (n - 1) ∣ a * r ^ (n - 1)
    rw [Nat.mul_comm]
    exact Nat.dvd_mul_right (r ^ (n - 1)) a
  have hle : radixAlpha r (a * r ^ (n - 1)) ≤ n - 1 :=
    radixAlpha_le r n (a * r ^ (n - 1)) hr (by omega) hlt
  have hrfl : radixFinalStateLabel r n a = a * r ^ (n - 1) := rfl
  rw [hrfl]
  omega

theorem radixFinalState_alpha (r n k : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n) (hk : k < r ^ n) :
    radixFinalTest r n k ↔ radixAlpha r k = n - 1 := by
  constructor
  · intro htest
    obtain ⟨a, ha0, ha1, hka⟩ :=
      (radixFinalState_iff r n k hr (by omega) hk).mp htest
    rw [hka]
    exact radixFinalStateLabel_alpha r n a hr hn ha0 ha1
  · intro hα
    have hkpos : 0 < k := by
      by_contra hcon
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hcon
      subst k
      simp only [radixAlpha_zero] at hα
      omega
    have hdiv : r ^ (radixAlpha r k) ∣ k := radixAlpha_dvd r k hr hkpos
    rw [hα] at hdiv
    exact ⟨hdiv, Nat.ne_of_gt hkpos⟩

theorem radixFinal_kept (r n : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < r ^ n) {k : ℕ} (hk : k ∈ L) (hfinal : radixFinalTest r n k)
    (hmin : radixMinAlpha r L < n - 1) : k ∈ radixKeptLabels r L := by
  have hα : radixAlpha r k = n - 1 :=
    (radixFinalState_alpha r n k hr hn (hL k hk)).mp hfinal
  have hle : radixMinAlpha r L ≤ radixAlpha r k := radixMinAlpha_le r L k hk
  have hne : radixAlpha r k ≠ radixMinAlpha r L := by omega
  have hbeq : (radixAlpha r k == radixMinAlpha r L) = false := by
    have hne' : ¬ (radixAlpha r k == radixMinAlpha r L) = true := by
      intro h
      exact hne (of_decide_eq_true h)
    simpa using! hne'
  unfold radixKeptLabels
  refine List.mem_filter.mpr ⟨hk, ?_⟩
  simp [hbeq]

theorem radixGreedyChild_final (r N n k ℓ : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n) (hN : N = r ^ n)
    (hklt : k < N) (hℓlt : ℓ < N)
    (hfinalk : radixFinalTest r n k) (hfinalℓ : radixFinalTest r n ℓ) (hne : k ≠ ℓ) :
    radixFinalTest r n (radixGreedyChild r N k ℓ) := by
  have hrpos : 0 < r := by omega
  have hrpow : 0 < r ^ (n - 1) := Nat.pow_pos hrpos
  have hrw : r * r ^ (n - 1) = r ^ n := by
    have h1 : r ^ n = r ^ (n - 1 + 1) := by
      congr 1
      omega
    have h2 : r ^ (n - 1 + 1) = r ^ (n - 1) * r := by rw [pow_add, pow_one]
    calc r * r ^ (n - 1) = r ^ (n - 1) * r := Nat.mul_comm _ _
      _ = r ^ (n - 1 + 1) := h2.symm
      _ = r ^ n := h1.symm
  obtain ⟨a, ha0, ha1, hka⟩ :=
    (radixFinalState_iff r n k hr (by omega) (by simpa [hN] using! hklt)).mp hfinalk
  obtain ⟨b, hb0, hb1, hkb⟩ :=
    (radixFinalState_iff r n ℓ hr (by omega) (by simpa [hN] using! hℓlt)).mp hfinalℓ
  have hab : a ≠ b := by
    intro hcon
    have hkl : k = ℓ := by rw [hka, hkb, hcon]
    exact hne hkl
  have hsub : a + r - b = a + (r - b) := by omega
  have hka' : k = a * r ^ (n - 1) := by rw [hka]; rfl
  have hkb' : ℓ = b * r ^ (n - 1) := by rw [hkb]; rfl
  have hsum : k + ℓ = (a + b) * r ^ (n - 1) := by
    rw [hka', hkb']
    show a * r ^ (n - 1) + b * r ^ (n - 1) = (a + b) * r ^ (n - 1)
    ring
  have hdiff : k + N - ℓ = (a + r - b) * r ^ (n - 1) := by
    calc k + N - ℓ = a * r ^ (n - 1) + r ^ n - b * r ^ (n - 1) := by rw [hka', hkb', hN]
      _ = a * r ^ (n - 1) + (r - b) * r ^ (n - 1) := by
        have hble : b * r ^ (n - 1) ≤ r * r ^ (n - 1) := by
          calc b * r ^ (n - 1) = r ^ (n - 1) * b := (Nat.mul_comm _ _).symm
            _ ≤ r ^ (n - 1) * r := Nat.mul_le_mul_left (r ^ (n - 1)) (Nat.le_of_lt hb1)
            _ = r * r ^ (n - 1) := (Nat.mul_comm _ _).symm
        rw [← hrw, Nat.add_sub_assoc hble, ← Nat.sub_mul]
      _ = (a + (r - b)) * r ^ (n - 1) := by ring
      _ = (a + r - b) * r ^ (n - 1) := by rw [hsub]
  have hmod1 : (k + ℓ) % N = ((a + b) % r) * r ^ (n - 1) := by
    have hdecomp : a + b = r * ((a + b) / r) + (a + b) % r :=
      (Nat.div_add_mod (a + b) r).symm
    have hmain : k + ℓ = ((a + b) % r) * r ^ (n - 1) + N * ((a + b) / r) := by
      calc k + ℓ = (a + b) * r ^ (n - 1) := hsum
        _ = (r * ((a + b) / r) + (a + b) % r) * r ^ (n - 1) := by
          nth_rewrite 1 [hdecomp]
          rfl
        _ = ((a + b) % r) * r ^ (n - 1) + N * ((a + b) / r) := by
          rw [hN, ← hrw]
          ring
    have hlt : ((a + b) % r) * r ^ (n - 1) < N := by
      have h1 : ((a + b) % r) * r ^ (n - 1) < r * r ^ (n - 1) :=
        (Nat.mul_lt_mul_right hrpow).2 (Nat.mod_lt _ hrpos)
      rw [hN, ← hrw]
      exact h1
    rw [hmain, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hmod2 : (k + N - ℓ) % N = ((a + r - b) % r) * r ^ (n - 1) := by
    have hdecomp : a + r - b = r * ((a + r - b) / r) + (a + r - b) % r :=
      (Nat.div_add_mod (a + r - b) r).symm
    have hmain : k + N - ℓ = ((a + r - b) % r) * r ^ (n - 1) + N * ((a + r - b) / r) := by
      calc k + N - ℓ = (a + r - b) * r ^ (n - 1) := hdiff
        _ = (r * ((a + r - b) / r) + (a + r - b) % r) * r ^ (n - 1) := by
          nth_rewrite 1 [hdecomp]
          rfl
        _ = ((a + r - b) % r) * r ^ (n - 1) + N * ((a + r - b) / r) := by
          rw [hN, ← hrw]
          ring
    have hlt : ((a + r - b) % r) * r ^ (n - 1) < N := by
      have h1 : ((a + r - b) % r) * r ^ (n - 1) < r * r ^ (n - 1) :=
        (Nat.mul_lt_mul_right hrpow).2 (Nat.mod_lt _ hrpos)
      rw [hN, ← hrw]
      exact h1
    rw [hmain, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hs2pos : 1 ≤ (a + r - b) % r := by
    by_cases hlt : b < a
    · have h1 : a + r - b = r + (a - b) := by omega
      have h2 : a - b < r := by omega
      rw [h1, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h2]
      omega
    · have hlt' : a < b := by omega
      have h1 : a + r - b < r := by omega
      have h2 : 0 < a + r - b := by omega
      rw [Nat.mod_eq_of_lt h1]
      omega
  have hchild2 : radixFinalTest r n ((k + N - ℓ) % N) := by
    rw [hmod2]
    show r ^ (n - 1) ∣ ((a + r - b) % r) * r ^ (n - 1)
      ∧ ((a + r - b) % r) * r ^ (n - 1) ≠ 0
    refine ⟨?_, ?_⟩
    · rw [Nat.mul_comm]
      exact Nat.dvd_mul_right (r ^ (n - 1)) _
    · exact Nat.mul_ne_zero (Nat.ne_of_gt hs2pos) (Nat.ne_of_gt hrpow)
  have hchild1lt : (k + ℓ) % N < r ^ n := by
    rw [hN]
    exact Nat.mod_lt _ (by omega)
  have hchild2lt : (k + N - ℓ) % N < r ^ n := by
    rw [hN]
    exact Nat.mod_lt _ (by omega)
  have hα1le : radixAlpha r ((k + ℓ) % N) ≤ n - 1 :=
    radixAlpha_le r n ((k + ℓ) % N) hr (by omega) hchild1lt
  have hα2 : radixAlpha r ((k + N - ℓ) % N) = n - 1 :=
    (radixFinalState_alpha r n ((k + N - ℓ) % N) hr hn hchild2lt).mp hchild2
  unfold radixGreedyChild
  by_cases h : radixAlpha r ((k + ℓ) % N) < radixAlpha r ((k + N - ℓ) % N)
  · simp only [if_pos h]
    exact hchild2
  · simp only [if_neg h]
    have hα1 : radixAlpha r ((k + ℓ) % N) = n - 1 := by omega
    exact (radixFinalState_alpha r n ((k + ℓ) % N) hr hn hchild1lt).mpr hα1

theorem radixSieveRun_has_final (r N n p : ℕ) (hr : 2 ≤ r) (hn : 2 ≤ n) (hN : N = r ^ n)
    {L : List ℕ} (hL : ∀ k ∈ L, k < N)
    (hinit : ∃ k ∈ L, radixFinalTest r n k)
    (hne : ∀ q, q ≤ p → radixSieveRun r N q L ≠ []) :
    ∃ k ∈ radixSieveRun r N p L, radixFinalTest r n k := by
  induction p with
  | zero =>
    exact hinit
  | succ p ih =>
    have hprev : ∃ k ∈ radixSieveRun r N p L, radixFinalTest r n k :=
      ih (fun q hq => hne q (by omega))
    obtain ⟨k, hk, hfinal⟩ := hprev
    have hLq1 : radixSieveRun r N (p + 1) L ≠ [] := hne (p + 1) (by omega)
    have hLlab : ∀ j ∈ radixSieveRun r N p L, j < N := fun j hj =>
      radixSieveRun_labels_lt r N (by simpa [hN] using! (show 0 < r ^ n from Nat.pow_pos (by omega : 0 < r))) hL p j hj
    by_cases hmin : radixMinAlpha r (radixSieveRun r N p L) < n - 1
    · refine ⟨k, ?_, hfinal⟩
      have hkept := radixFinal_kept r n hr hn (fun j hj => by simpa [hN] using! hLlab j hj)
        hk hfinal hmin
      rw [radixSieveRun_succ]
      unfold radixPeriodStep
      exact List.mem_append_left _ hkept
    · have hmin' : radixMinAlpha r (radixSieveRun r N p L) = n - 1 := by
        have hle : radixMinAlpha r (radixSieveRun r N p L) ≤ n - 1 := by
          have h1 : radixMinAlpha r (radixSieveRun r N p L)
              ≤ radixAlpha r k := radixMinAlpha_le r (radixSieveRun r N p L) k hk
          have h2 : radixAlpha r k ≤ n - 1 :=
            radixAlpha_le r n k hr (by omega) (by simpa [hN] using! hLlab k hk)
          omega
        omega
      have hαall : ∀ j ∈ radixSieveRun r N p L, radixAlpha r j = n - 1 := by
        intro j hj
        have h1 : radixMinAlpha r (radixSieveRun r N p L) ≤ radixAlpha r j :=
          radixMinAlpha_le r (radixSieveRun r N p L) j hj
        have h2 : radixAlpha r j ≤ n - 1 :=
          radixAlpha_le r n j hr (by omega) (by simpa [hN] using! hLlab j hj)
        omega
      cases hkept : radixKeptLabels r (radixSieveRun r N p L) with
      | cons j js =>
        have hjmem : j ∈ radixKeptLabels r (radixSieveRun r N p L) := by
          rw [hkept]
          exact List.mem_cons_self
        have hjL : j ∈ radixSieveRun r N p L := (List.mem_filter.mp hjmem).1
        have hjfinal : radixFinalTest r n j :=
          (radixFinalState_alpha r n j hr hn (by simpa [hN] using! hLlab j hjL)).mpr (hαall j hjL)
        refine ⟨j, ?_, hjfinal⟩
        rw [radixSieveRun_succ]
        unfold radixPeriodStep
        exact List.mem_append_left _ hjmem
      | nil =>
        have hchildrenne : radixPeriodChildren r N (radixSieveRun r N p L) ≠ [] := by
          intro hcon
          have hstep : radixSieveRun r N (p + 1) L = [] := by
            rw [radixSieveRun_succ]
            unfold radixPeriodStep
            rw [hkept, hcon]
            rfl
          rw [hstep] at hLq1
          exact absurd hLq1 (by simp)
        have hpair : ∃ k ℓ : ℕ, radixGreedyPair r N (radixSieveRun r N p L) = some (k, ℓ) ∧
            radixPeriodChildren r N (radixSieveRun r N p L) = [radixGreedyChild r N k ℓ] := by
          cases hg : radixGreedyPair r N (radixSieveRun r N p L) with
          | none =>
            have hfalse : False := by
              have hempty : radixPeriodChildren r N (radixSieveRun r N p L) = [] := by
                simp only [radixPeriodChildren, hg]
              rw [hempty] at hchildrenne
              exact hchildrenne rfl
            exact hfalse.elim
          | some kl =>
            obtain ⟨k, ℓ⟩ := kl
            refine ⟨k, ℓ, rfl, ?_⟩
            simp only [radixPeriodChildren, hg]
        obtain ⟨k, ℓ, hpair', hchildren⟩ := hpair
        have hmem := radixGreedyPair_mem (r := r) (N := N) (L := radixSieveRun r N p L)
          (k := k) (ℓ := ℓ) hpair'
        have hkL : k ∈ radixSieveRun r N p L := List.mem_of_mem_filter hmem.1
        have hℓL : ℓ ∈ radixSieveRun r N p L := List.mem_of_mem_filter hmem.2.1
        have hkne : k ≠ ℓ := hmem.2.2
        have hkfinal : radixFinalTest r n k :=
          (radixFinalState_alpha r n k hr hn (by simpa [hN] using! hLlab k hkL)).mpr (hαall k hkL)
        have hℓfinal : radixFinalTest r n ℓ :=
          (radixFinalState_alpha r n ℓ hr hn (by simpa [hN] using! hLlab ℓ hℓL)).mpr (hαall ℓ hℓL)
        have hchildfinal : radixFinalTest r n (radixGreedyChild r N k ℓ) :=
          radixGreedyChild_final r N n k ℓ hr hn hN (hLlab k hkL) (hLlab ℓ hℓL)
            hkfinal hℓfinal hkne
        refine ⟨radixGreedyChild r N k ℓ, ?_, hchildfinal⟩
        rw [radixSieveRun_succ]
        unfold radixPeriodStep
        rw [hkept]
        exact List.mem_append_right _ (by rw [hchildren]; simp)

theorem radixSieveRun_final_labels (n p : ℕ) (hn : 2 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < 3 ^ n)
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L))
    (hprog : radixMinAlpha 3 L + p ≥ n - 1) :
    ∀ k ∈ radixSieveRun 3 (3 ^ n) p L, radixFinalTest 3 n k := by
  have hmin : radixMinAlpha 3 (radixSieveRun 3 (3 ^ n) p L) ≥ n - 1 := by
    have h1 := radixSieveRun_minAlpha n p (by omega) hp
    omega
  intro k hk
  have hklt : k < 3 ^ n := radixSieveRun_labels_lt 3 (3 ^ n) (by positivity) hL p k hk
  have hαle : radixAlpha 3 k ≤ n - 1 := radixAlpha_le 3 n k (by omega) (by omega) hklt
  have hαge : n - 1 ≤ radixAlpha 3 k := by
    have h1 := radixMinAlpha_le 3 (radixSieveRun 3 (3 ^ n) p L) k hk
    omega
  exact (radixFinalState_alpha 3 n k (by omega) (by omega) hklt).mpr (by omega)

theorem radixSieve_final_states_of_progress (n p : ℕ) (hn : 2 ≤ n) {L : List ℕ}
    (hL : ∀ k ∈ L, k < 3 ^ n) (hinit : (n : ℝ) ≤ radixListValue 3 n L)
    (hp : ∀ q, q < p → RadixPeriodConditions n (radixSieveRun 3 (3 ^ n) q L))
    (hprog : radixMinAlpha 3 L + p ≥ n - 1) :
    1 ≤ (radixSieveRun 3 (3 ^ n) p L).length :=
  radixSieve_final_states_of_value n p (by omega) hL hinit hp
    (radixSieveRun_final_labels n p hn hL hp hprog)

theorem radixRecoveryReadout_reads (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hrp : r.Prime) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (r ^ n) → S) (s : ZMod (r ^ n))
    (hf : DihedralReflectionHides (r ^ n) f s)
    (k : ZMod (r ^ n)) (z : S) (hklt : k.val < r ^ n)
    (htest : radixFinalTest r n k.val)
    (hamp : (fun b => dihedralRecordJoint (r ^ n) f ((k, b), z)) ≠ 0) :
    radixRecoveryReadout f r n k z = some (s.val % r) := by
  obtain ⟨a, ha0, ha1, hka⟩ := (radixFinalState_iff r n k.val hr hn hklt).mp htest
  have hrec1 : k = ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n)) := by
    have hval : (k.val : ZMod (r ^ n)) = k := ZMod.natCast_zmod_val _
    rw [← hval, hka]
  have hphase : dihedralQubitPhase (r ^ n) s k
      = radixRootOfUnity r ((s.val * a) % r) := by
    rw [hrec1]
    exact radixFinalPhase r n hr hn s a ha1
  rcases radixRecordPhaseRatio (r ^ n) f s hf k false z with hzero | ⟨c, hc, heq⟩
  · exact absurd hzero hamp
  · have hfalse : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false = c := by
      have h := congrFun heq false
      simpa using! h
    have hcf : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false ≠ 0 := by
      rw [hfalse]
      exact hc
    have htrue : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) true
        = c * dihedralQubitPhase (r ^ n) s k := by
      have h := congrFun heq true
      simpa using! h
    have hratio : (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) true
        / (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z)) false
        = dihedralQubitPhase (r ^ n) s k := by
      rw [htrue, hfalse, div_eq_iff hc]
      ring
    have hph : radixBranchPhase (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z))
        = some (radixRootOfUnity r ((s.val * a) % r)) := by
      rw [radixBranchPhase_of _ hcf, hratio, hphase]
    have hidx : radixTomographyIndex r
        (fun b => dihedralRecordJoint (r ^ n) f ((k,b),z))
        = some ((s.val * a) % r : ZMod r) := by
      refine radixTomographyIndex_of_nat r ((s.val * a) % r) (Nat.mod_lt _ (by omega)) _ hph
    have hidxval : radixFinalIndex r n k.val = a := by
      rw [hka]
      exact radixFinalIndex_final r n a hr ha1
    have hunit : IsUnit (a : ZMod r) := radixFinalIndex_unit_of_prime r a hrp ha0 ha1
    have hu : IsUnit (radixFinalIndex r n k.val : ZMod r) := by
      rw [hidxval]
      exact hunit
    have hout : radixReadout r a ((s.val * a) % r) = s.val % r := by
      have hcorrect := radixReadout_correct r n hr s.val a hunit
      rw [radixPhaseIndex_final r n s.val a hr] at hcorrect
      exact hcorrect
    have hval : ((s.val * a) % r : ZMod r).val = (s.val * a) % r :=
      ZMod.val_natCast_of_lt (Nat.mod_lt _ (by omega))
    unfold radixRecoveryReadout
    simp only [hidx]
    rw [dif_pos hu, hidxval, hval, hout]
    rfl

theorem radixRecoveryDecide_reads (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hrp : r.Prime) {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (r ^ n) → S) (s : ZMod (r ^ n))
    (hf : DihedralReflectionHides (r ^ n) f s) (p : ℕ)
    (L : List (ZMod (r ^ n) × S))
    (hrec : ∃ (k : ZMod (r ^ n)) (z : S),
      radixFinalRecordBy r n (fun rec : ZMod (r ^ n) × S => rec.1.val) L
        (radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val)) = some (k, z) ∧
      (fun b => dihedralRecordJoint (r ^ n) f ((k, b), z)) ≠ 0) :
    radixRecoveryDecide f r n p L = some (s.val % r) := by
  obtain ⟨k, z, hfound, hamp⟩ := hrec
  have hLlab : ∀ j ∈ L.map (fun rec : ZMod (r ^ n) × S => rec.1.val), j < r ^ n := by
    intro j hj
    obtain ⟨rec, hrec', rfl⟩ := List.mem_map.mp hj
    exact rec.1.val_lt
  unfold radixRecoveryDecide
  rw [hfound]
  have hfound' : (decide (radixFinalTest r n k.val) && decide (k.val ∈
      radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val))) = true := by
    unfold radixFinalRecordBy at hfound
    have h := List.find?_some hfound
    simpa only [decide_eq_true_eq] using! h
  have hdec : decide (radixFinalTest r n k.val) = true ∧
      decide (k.val ∈ radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val)) = true :=
    (Bool.and_eq_true_eq_eq_true_and_eq_true _ _).mp hfound'
  have htest : radixFinalTest r n k.val := of_decide_eq_true hdec.1
  have hmem : k.val ∈ radixSieveRun r (r ^ n) p (L.map fun rec => rec.1.val) :=
    of_decide_eq_true hdec.2
  have hklt : k.val < r ^ n :=
    radixSieveRun_labels_lt r (r ^ n) (by positivity) hLlab p k.val hmem
  exact radixRecoveryReadout_reads r n hr hn hrp f s hf k z hklt htest hamp

theorem radixActualLabelLaw_uniform {N : ℕ} [NeZero N] {S : Type} [Fintype S]
    [DecidableEq S] [AddCommGroup S] (f : DihedralReg N → S) (s : ZMod N)
    (hf : DihedralReflectionHides N f s) (k : ZMod N) :
    radixActualLabelLaw f k = ENNReal.ofReal (1 / (N : ℝ)) := by
  have h := clause2_actual_label_mass f s hf k
  show actualLabelLaw f k = ENNReal.ofReal (1 / (N : ℝ))
  exact h

theorem radixFinalStateLabels_eq (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    (k : ℕ) (hk : k < r ^ n) :
    radixFinalTest r n k ↔ ∃ a : {a : ℕ // 0 < a ∧ a < r}, k = radixFinalStateLabel r n a.val := by
  rw [radixFinalState_iff r n k hr hn hk]
  constructor
  · rintro ⟨a, ha0, ha, hka⟩
    exact ⟨⟨a, ha0, ha⟩, hka⟩
  · rintro ⟨a, hka⟩
    exact ⟨a.val, a.property.1, a.property.2, hka⟩

theorem radixFinalStateLabels_card (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun k : ZMod (r ^ n) => radixFinalTest r n k.val)).card
      = r - 1 := by
  classical
  set T : Finset (ZMod (r ^ n)) :=
    Finset.univ.filter (fun k => radixFinalTest r n k.val) with hT
  set C : Finset ℕ := (Finset.range r).filter (fun a => 0 < a) with hC
  have hlt : ∀ a : ℕ, a < r → radixFinalStateLabel r n a < r ^ n := by
    intro a har
    have hr1 : 1 ≤ r := by omega
    have hpos : 0 < r ^ (n - 1) := by
      have h1 : 1 ≤ r ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hmul : a * r ^ (n - 1) ≤ (r - 1) * r ^ (n - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    calc a * r ^ (n - 1) ≤ (r - 1) * r ^ (n - 1) := hmul
      _ < r * r ^ (n - 1) := by
        have h : r - 1 < r := by omega
        simpa [Nat.mul_comm] using! Nat.mul_lt_mul_of_pos_left h hpos
      _ = r ^ n := by
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        exact Nat.mul_comm _ _
  have hcard : T.card = C.card := by
    refine (Finset.card_bij (s := C) (t := T)
      (fun a _ => ((radixFinalStateLabel r n a : ℕ) : ZMod (r ^ n))) ?_ ?_ ?_).symm
    · intro a ha
      rw [hC, Finset.mem_filter] at ha
      obtain ⟨har, hpos⟩ := ha
      have hlt' : radixFinalStateLabel r n a < r ^ n := hlt a (Finset.mem_range.mp har)
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast_of_lt hlt']
      exact (radixFinalState_iff r n (radixFinalStateLabel r n a) hr hn hlt').mpr
        ⟨a, hpos, Finset.mem_range.mp har, rfl⟩
    · intro a₁ ha₁ a₂ ha₂ h
      rw [hC, Finset.mem_filter] at ha₁ ha₂
      obtain ⟨har₁, hpos₁⟩ := ha₁
      obtain ⟨har₂, hpos₂⟩ := ha₂
      have hv₁ : radixFinalStateLabel r n a₁ < r ^ n := hlt a₁ (Finset.mem_range.mp har₁)
      have hv₂ : radixFinalStateLabel r n a₂ < r ^ n := hlt a₂ (Finset.mem_range.mp har₂)
      have hmul : radixFinalStateLabel r n a₁ = radixFinalStateLabel r n a₂ := by
        have h' : (radixFinalStateLabel r n a₁ : ℕ) = (radixFinalStateLabel r n a₂ : ℕ) := by
          have hh := congrArg ZMod.val h
          rw [ZMod.val_natCast_of_lt hv₁, ZMod.val_natCast_of_lt hv₂] at hh
          exact hh
        exact h'
      unfold radixFinalStateLabel at hmul
      have hpos : 0 < r ^ (n - 1) := by
        have h1 : 1 ≤ r ^ (n - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
      have h' : r ^ (n - 1) * a₁ = r ^ (n - 1) * a₂ := by
        simpa [Nat.mul_comm] using! hmul
      exact Nat.mul_left_cancel hpos h'
    · intro b hb
      rw [hT, Finset.mem_filter] at hb
      obtain ⟨hval, hfinal⟩ := hb
      obtain ⟨a, hba⟩ :=
        (radixFinalStateLabels_eq r n hr hn b.val (by
          have := ZMod.val_lt b
          simpa using! this)).mp hfinal
      have har : a.val < r := a.property.2
      have hpos : 0 < a.val := a.property.1
      refine ⟨a.val, ?_, ?_⟩
      · rw [hC, Finset.mem_filter]
        exact ⟨Finset.mem_range.mpr har, hpos⟩
      · have hlt' : radixFinalStateLabel r n a.val < r ^ n := hlt a.val har
        have h' : ((radixFinalStateLabel r n a.val : ℕ) : ZMod (r ^ n)).val = b.val := by
          rw [ZMod.val_natCast_of_lt hlt', hba]
        have e1 : ((radixFinalStateLabel r n a.val : ℕ) : ZMod (r ^ n))
            = (b.val : ZMod (r ^ n)) := by
          have h2 : ((radixFinalStateLabel r n a.val : ℕ) : ZMod (r ^ n))
              = (((radixFinalStateLabel r n a.val : ℕ) : ZMod (r ^ n)).val : ZMod (r ^ n)) :=
            (ZMod.natCast_zmod_val _).symm
          rw [h2, h']
        exact e1.trans (ZMod.natCast_zmod_val b)
  rw [hcard]
  have hCcard : C.card = r - 1 := by
    have hC' : C = (Finset.range r).erase 0 := by
      ext a
      simp only [hC, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨har, hpos⟩; exact ⟨by omega, har⟩
      · rintro ⟨hne, har⟩; exact ⟨har, by omega⟩
    rw [hC']
    have h0 : (0 : ℕ) ∈ Finset.range r := Finset.mem_range.mpr (by omega)
    rw [Finset.card_erase_of_mem h0, Finset.card_range]
  exact hCcard

theorem radixFinalState_mass (r n : ℕ) [NeZero r] (hr : 2 ≤ r) (hn : 1 ≤ n)
    {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (f : DihedralReg (r ^ n) → S) (s : ZMod (r ^ n))
    (hf : DihedralReflectionHides (r ^ n) f s) :
    ∑' k : ZMod (r ^ n), (radixActualLabelLaw f) k *
      massIndicator (radixFinalTest r n k.val)
      = ENNReal.ofReal (1 / ((r ^ n : ℕ) : ℝ)) * (r - 1 : ℕ) := by
  classical
  have hunif : ∀ k : ZMod (r ^ n),
      (radixActualLabelLaw f) k = ENNReal.ofReal (1 / ((r ^ n : ℕ) : ℝ)) :=
    fun k => radixActualLabelLaw_uniform f s hf k
  have hcard := radixFinalStateLabels_card r n hr hn
  set T : Finset (ZMod (r ^ n)) :=
    Finset.univ.filter (fun k => radixFinalTest r n k.val) with hT
  have hcount : (∑' k : ZMod (r ^ n), massIndicator (radixFinalTest r n k.val))
      = ((r - 1 : ℕ) : ℝ≥0∞) := by
    rw [tsum_fintype]
    have hsub : (∑ k ∈ (Finset.univ : Finset (ZMod (r ^ n))),
          massIndicator (radixFinalTest r n k.val))
        = ∑ k ∈ T, massIndicator (radixFinalTest r n k.val) := by
      refine (Finset.sum_subset (s₁ := T) (s₂ := (Finset.univ : Finset (ZMod (r ^ n))))
        (f := fun k : ZMod (r ^ n) => massIndicator (radixFinalTest r n k.val)) ?_ ?_).symm
      · exact Finset.subset_univ T
      · intro b hb hnot
        have hfalse : ¬ radixFinalTest r n b.val := by
          intro h
          apply hnot
          rw [hT, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, h⟩
        simp [massIndicator, hfalse]
    rw [hsub]
    calc (∑ k ∈ T, massIndicator (radixFinalTest r n k.val))
        = ∑ k ∈ T, (1 : ℝ≥0∞) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk' : radixFinalTest r n k.val := by
              rw [hT] at hk
              exact (Finset.mem_filter.mp hk).2
            simp [massIndicator, hk']
      _ = ((T.card : ℕ) : ℝ≥0∞) := by
            rw [Finset.sum_const]
            simp
      _ = ((r - 1 : ℕ) : ℝ≥0∞) := by rw [hcard]
  calc (∑' k : ZMod (r ^ n), (radixActualLabelLaw f) k *
        massIndicator (radixFinalTest r n k.val))
      = ∑' k : ZMod (r ^ n), ENNReal.ofReal (1 / ((r ^ n : ℕ) : ℝ)) *
        massIndicator (radixFinalTest r n k.val) := by
          apply tsum_congr
          intro k
          rw [hunif]
    _ = ENNReal.ofReal (1 / ((r ^ n : ℕ) : ℝ)) *
        ∑' k : ZMod (r ^ n), massIndicator (radixFinalTest r n k.val) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 / ((r ^ n : ℕ) : ℝ)) * (r - 1 : ℕ) := by
      rw [hcount]

end Qatlib.Concepts.HspRecovery.OpenSieve
