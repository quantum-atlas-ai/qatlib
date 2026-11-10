/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.NonabelianDefs
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open scoped ENNReal Classical

set_option autoImplicit false
set_option warningAsError false

def H0 : DihedralSubgroupData 4 := ⟨2, by omega, some 0⟩
def H2 : DihedralSubgroupData 4 := ⟨2, by omega, some 2⟩

def f4 : DihedralReg 4 → ZMod 8 := fun p => ((p.1.val % 2 : ℕ) : ZMod 8)

theorem val_two : (2 : ZMod 4).val = 2 := by decide

theorem two_mul_iff (a b : ZMod 4) :
    (∃ k : ℕ, b = a + ((k * 2 : ℕ) : ZMod 4)) ↔ a.val % 2 = b.val % 2 := by
  constructor
  · intro ⟨k, hk⟩
    have ha := ZMod.val_lt a
    have hb := ZMod.val_lt b
    apply congrArg ZMod.val at hk
    simp only [ZMod.val_add, ZMod.val_natCast] at hk
    omega
  · intro h
    refine ⟨(b.val + 4 - a.val) / 2, ?_⟩
    apply ZMod.val_injective
    have ha := ZMod.val_lt a
    have hb := ZMod.val_lt b
    simp only [ZMod.val_add, ZMod.val_natCast]
    omega

theorem two_mul_add_iff (a b : ZMod 4) :
    (∃ k : ℕ, b = a + 2 + ((k * 2 : ℕ) : ZMod 4)) ↔ a.val % 2 = b.val % 2 := by
  have hsum : (a + 2).val = (a.val + 2) % 4 := by
    have ha := ZMod.val_lt a
    simp only [ZMod.val_add, val_two]
  calc (∃ k : ℕ, b = a + 2 + ((k * 2 : ℕ) : ZMod 4))
      ↔ (∃ k : ℕ, b = (a + 2) + ((k * 2 : ℕ) : ZMod 4)) := Iff.rfl
    _ ↔ (a + 2).val % 2 = b.val % 2 := two_mul_iff (a + 2) b
    _ ↔ a.val % 2 = b.val % 2 := by
        have ha := ZMod.val_lt a
        rw [hsum]
        omega

theorem neg_two : (-(2 : ZMod 4)) = 2 := by decide

theorem two_mul_sub_iff (a b : ZMod 4) :
    (∃ k : ℕ, b = a - 2 + ((k * 2 : ℕ) : ZMod 4)) ↔ a.val % 2 = b.val % 2 := by
  have hsub : a - 2 = a + 2 := by
    rw [sub_eq_add_neg, neg_two]
  rw [hsub]
  exact two_mul_add_iff a b

theorem f4_parity (p q : DihedralReg 4) :
    f4 p = f4 q ↔ p.1.val % 2 = q.1.val % 2 := by
  rcases p with ⟨a, ta⟩
  rcases q with ⟨b, tb⟩
  simp only [f4]
  constructor
  · intro h
    apply congrArg ZMod.val at h
    simp only [ZMod.val_natCast] at h
    omega
  · intro h
    rw [h]

theorem orbit_H0 (p q : DihedralReg 4) :
    DihedralSubgroupOrbit 4 H0 p q ↔ p.1.val % 2 = q.1.val % 2 := by
  rcases p with ⟨a, ta⟩
  rcases q with ⟨b, tb⟩
  cases ta <;> cases tb
  · show (∃ k : ℕ, b = a + ((k * (4 / H0.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H0]
    exact two_mul_iff a b
  · show (∃ s : ZMod 4, H0.slope = some s ∧ ∃ k : ℕ, b = a + s + ((k * (4 / H0.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H0]
    constructor
    · intro ⟨s, hs, k, hk⟩
      have hs0 : 0 = s := Option.some.inj (by simpa using! hs)
      subst hs0
      exact (two_mul_iff a b).1 ⟨k, by simpa using! hk⟩
    · intro h
      obtain ⟨k, hk⟩ := (two_mul_iff a b).2 h
      exact ⟨0, rfl, k, by simpa using! hk⟩
  · show (∃ s : ZMod 4, H0.slope = some s ∧ ∃ k : ℕ, b = a - s + ((k * (4 / H0.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H0]
    constructor
    · intro ⟨s, hs, k, hk⟩
      have hs0 : 0 = s := Option.some.inj (by simpa using! hs)
      subst hs0
      exact (two_mul_iff a b).1 ⟨k, by simpa using! hk⟩
    · intro h
      obtain ⟨k, hk⟩ := (two_mul_iff a b).2 h
      exact ⟨0, rfl, k, by simpa using! hk⟩
  · show (∃ k : ℕ, b = a + ((k * (4 / H0.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H0]
    exact two_mul_iff a b

theorem orbit_H2 (p q : DihedralReg 4) :
    DihedralSubgroupOrbit 4 H2 p q ↔ p.1.val % 2 = q.1.val % 2 := by
  rcases p with ⟨a, ta⟩
  rcases q with ⟨b, tb⟩
  cases ta <;> cases tb
  · show (∃ k : ℕ, b = a + ((k * (4 / H2.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H2]
    exact two_mul_iff a b
  · show (∃ s : ZMod 4, H2.slope = some s ∧ ∃ k : ℕ, b = a + s + ((k * (4 / H2.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H2]
    constructor
    · intro ⟨s, hs, k, hk⟩
      have hs2 : 2 = s := Option.some.inj (by simpa using! hs)
      subst hs2
      exact (two_mul_add_iff a b).1 ⟨k, by simpa using! hk⟩
    · intro h
      obtain ⟨k, hk⟩ := (two_mul_add_iff a b).2 h
      exact ⟨2, rfl, k, by simpa using! hk⟩
  · show (∃ s : ZMod 4, H2.slope = some s ∧ ∃ k : ℕ, b = a - s + ((k * (4 / H2.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H2]
    constructor
    · intro ⟨s, hs, k, hk⟩
      have hs2 : 2 = s := Option.some.inj (by simpa using! hs)
      subst hs2
      exact (two_mul_sub_iff a b).1 ⟨k, by simpa using! hk⟩
    · intro h
      obtain ⟨k, hk⟩ := (two_mul_sub_iff a b).2 h
      exact ⟨2, rfl, k, by simpa using! hk⟩
  · show (∃ k : ℕ, b = a + ((k * (4 / H2.period) : ℕ) : ZMod 4)) ↔ _
    simp only [H2]
    exact two_mul_iff a b

theorem f4_hides_H0 : DihedralSubgroupHides f4 H0 := by
  intro p q
  rw [f4_parity p q, orbit_H0 p q]

theorem f4_hides_H2 : DihedralSubgroupHides f4 H2 := by
  intro p q
  rw [f4_parity p q, orbit_H2 p q]

theorem H0_ne_H2 : H0 ≠ H2 := by
  intro h
  have := congrArg DihedralSubgroupData.slope h
  simp [H0, H2] at this
  exact absurd this (by decide)

theorem H0_ne_trivial : H0 ≠ trivialSubgroup 4 := by
  intro h
  have := congrArg DihedralSubgroupData.period h
  simp [H0, trivialSubgroup] at this

theorem H2_ne_trivial : H2 ≠ trivialSubgroup 4 := by
  intro h
  have := congrArg DihedralSubgroupData.period h
  simp [H2, trivialSubgroup] at this

theorem not_subgroup_endpoint (lg : RecoveryLedger) : ¬ SubgroupRecoveryEndpoint 4 lg := by
  intro hex
  obtain ⟨run, _, _, _, _, hall⟩ := hex
  have hA := hall (ZMod 8) f4 H0 f4_hides_H0
  have hB := hall (ZMod 8) f4 H2 f4_hides_H2
  change (∀ o : Option (DihedralSubgroupData 4),
      o ≠ (if H0 = trivialSubgroup 4 then none else some H0) → run (ZMod 8) f4 o = 0) ∧
      ENNReal.ofReal (2 / 3) ≤ run (ZMod 8) f4 (if H0 = trivialSubgroup 4 then none else some H0) at hA
  change (∀ o : Option (DihedralSubgroupData 4),
      o ≠ (if H2 = trivialSubgroup 4 then none else some H2) → run (ZMod 8) f4 o = 0) ∧
      ENNReal.ofReal (2 / 3) ≤ run (ZMod 8) f4 (if H2 = trivialSubgroup 4 then none else some H2) at hB
  simp only [H0_ne_trivial, H2_ne_trivial, if_false] at hA hB
  have hzero : run (ZMod 8) f4 (some H2) = 0 :=
    hA.1 (some H2) (fun h => H0_ne_H2 (Option.some.inj h).symm)
  have hle := hB.2
  rw [hzero] at hle
  exact absurd hle (by norm_num)

theorem clause137_conjunct12_false :
    ¬ (∃ lg : RecoveryLedger,
        SubgroupRecoveryEndpoint (2 ^ 2) lg ∧ ShiftRecoveryEndpoint (2 ^ 2) (2 / 3) lg) := by
  intro ⟨lg, h, _⟩
  exact not_subgroup_endpoint lg h
