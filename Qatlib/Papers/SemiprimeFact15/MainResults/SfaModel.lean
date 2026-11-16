/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section


/-!
# Exact Shor postprocessing on the CRT decomposition

The two parity coordinates record the order-two parts of the two cyclic unit
groups. The remaining coordinates have odd order. In these coordinates the
multiplicative element `-1` is `((1, 1), (0, 0))`; additive `-1` in `ZMod (2q)`
is not its image. The success test below executes the actual order-halving
postprocessing, and its parity characterization is proved rather than assumed.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SemiprimeFact15.MainResults

/-- The CRT decomposition of the two cyclic groups of orders `2q₁, 2q₂`. -/
abbrev UnitModel (q1 q2 : ℕ) := (ZMod 2 × ZMod 2) × (ZMod q1 × ZMod q2)

/-- Explicit additive CRT equivalence from the paper's product of cyclic groups. -/
def unitCrt (q1 q2 : ℕ) (h1 : Odd q1) (h2 : Odd q2) :
    (ZMod (2 * q1) × ZMod (2 * q2)) ≃+ UnitModel q1 q2 := by
  let e1 := (ZMod.chineseRemainder (Nat.coprime_two_left.mpr h1)).toAddEquiv
  let e2 := (ZMod.chineseRemainder (Nat.coprime_two_left.mpr h2)).toAddEquiv
  exact
    { toFun := fun a => (((e1 a.1).1, (e2 a.2).1), ((e1 a.1).2, (e2 a.2).2))
      invFun := fun a => (e1.symm (a.1.1, a.2.1), e2.symm (a.1.2, a.2.2))
      left_inv := by
        intro a
        simp only [Prod.mk.eta, AddEquiv.symm_apply_apply]
      right_inv := by
        intro a
        simp only [AddEquiv.apply_symm_apply, Prod.mk.eta]
      map_add' := by
        intro a b
        simp only [map_add, Prod.fst_add, Prod.snd_add]
        rfl }

/-- The unique order-two elements map to the two sign bits, not additive `-1`. -/
theorem unitCrt_involution (q1 q2 : ℕ) (h1 : Odd q1) (h2 : Odd q2) :
    unitCrt q1 q2 h1 h2 ((q1 : ZMod (2 * q1)), (q2 : ZMod (2 * q2))) =
      ((1, 1), (0, 0)) := by
  have hs : ∀ q : ℕ, Odd q → (q : ZMod 2) = 1 := by
    intro q hq
    obtain ⟨t, rfl⟩ := hq.exists_bit1
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [Nat.cast_add, Nat.cast_mul]
    change (2 : ZMod 2) * (t : ZMod 2) + 1 = 1
    rw [htwo, zero_mul, zero_add]
  change (((ZMod.chineseRemainder _ (q1 : ZMod (2 * q1))).1,
      (ZMod.chineseRemainder _ (q2 : ZMod (2 * q2))).1),
    ((ZMod.chineseRemainder _ (q1 : ZMod (2 * q1))).2,
      (ZMod.chineseRemainder _ (q2 : ZMod (2 * q2))).2)) = _
  rw [map_natCast, map_natCast]
  simp only [Prod.fst_natCast, Prod.snd_natCast, ZMod.natCast_self, hs q1 h1, hs q2 h2]

/-- The actual even-order and half-power test, in additive CRT coordinates. -/
def SfaSucceeds (q1 q2 : ℕ) (a : UnitModel q1 q2) : Prop :=
  2 ∣ addOrderOf a ∧
    (addOrderOf a / 2) • a ≠ ((1, 1), (0, 0))

/-- The number of inputs accepted by the order-halving postprocessor. -/
noncomputable def sfaSuccessCount (q1 q2 : ℕ) [NeZero q1] [NeZero q2] : ℕ := by
  classical
  exact (Finset.univ.filter (SfaSucceeds q1 q2)).card

/-- Multiplying an element of order two by an odd natural leaves it unchanged. -/
private lemma odd_smul_sign {s : ℕ} (hs : Odd s) (e : ZMod 2) : s • e = e := by
  obtain ⟨t, ht⟩ := hs.exists_bit1
  rw [ht, add_nsmul, mul_nsmul]
  have he : (2 : ℕ) • e = 0 := by
    simpa using (card_nsmul_eq_zero (x := e))
  rw [he]
  simp only [nsmul_zero, one_nsmul, zero_add]

/-- The order of an element of the odd CRT component is odd. -/
private lemma odd_part_order (q1 q2 : ℕ) [NeZero q1] [NeZero q2]
    (h1 : Odd q1) (h2 : Odd q2) (b : ZMod q1 × ZMod q2) :
    Odd (addOrderOf b) := by
  have hd : addOrderOf b ∣ q1 * q2 := by
    simpa using (addOrderOf_dvd_card (x := b))
  exact Nat.coprime_two_right.mp
    ((Nat.coprime_two_right.mpr (h1.mul h2)).coprime_dvd_left hd)

/-- The executed order-halving test succeeds exactly for unequal parity bits. -/
theorem sfa_success_iff (q1 q2 : ℕ) [NeZero q1] [NeZero q2]
    (h1 : Odd q1) (h2 : Odd q2) (a : UnitModel q1 q2) :
    SfaSucceeds q1 q2 a ↔ a.1.1 ≠ a.1.2 := by
  rcases a with ⟨⟨e1, e2⟩, b⟩
  have hs : Odd (addOrderOf b) := odd_part_order q1 q2 h1 h2 b
  have hcop : Nat.Coprime 2 (addOrderOf b) := Nat.coprime_two_left.mpr hs
  have hodd := hs.not_two_dvd_nat
  have hmul : addOrderOf b • b = 0 := addOrderOf_nsmul_eq_zero b
  have hone : addOrderOf b • (1 : ZMod 2) = 1 := odd_smul_sign hs 1
  have h00 : addOrderOf ((0, 0) : ZMod 2 × ZMod 2) = 1 := by
    change addOrderOf (0 : ZMod 2 × ZMod 2) = 1
    exact addOrderOf_zero
  have h01 : addOrderOf ((0, 1) : ZMod 2 × ZMod 2) = 2 := by
    rw [Prod.addOrderOf]
    simp only [addOrderOf_zero, ZMod.addOrderOf_one, Nat.lcm_one_left]
  have h10 : addOrderOf ((1, 0) : ZMod 2 × ZMod 2) = 2 := by
    rw [Prod.addOrderOf]
    simp only [addOrderOf_zero, ZMod.addOrderOf_one, Nat.lcm_one_right]
  have h11 : addOrderOf ((1, 1) : ZMod 2 × ZMod 2) = 2 := by
    rw [Prod.addOrderOf, ZMod.addOrderOf_one, Nat.lcm_self]
  fin_cases e1 <;> fin_cases e2
  · change SfaSucceeds q1 q2 ((0, 0), b) ↔ (0 : ZMod 2) ≠ 0
    rw [SfaSucceeds, Prod.addOrderOf, h00, Nat.lcm_one_left]
    simp only [hodd, false_and, ne_eq, not_true_eq_false]
  · change SfaSucceeds q1 q2 ((0, 1), b) ↔ (0 : ZMod 2) ≠ 1
    rw [SfaSucceeds, Prod.addOrderOf, h01, hcop.lcm_eq_mul]
    simp only [dvd_mul_right, true_and, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      Prod.smul_mk, nsmul_zero, hone, hmul, Prod.mk.injEq, zero_ne_one,
      false_and, not_false_eq_true, ne_eq]
  · change SfaSucceeds q1 q2 ((1, 0), b) ↔ (1 : ZMod 2) ≠ 0
    rw [SfaSucceeds, Prod.addOrderOf, h10, hcop.lcm_eq_mul]
    simp only [dvd_mul_right, true_and, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      Prod.smul_mk, nsmul_zero, hone, hmul, Prod.mk.injEq, zero_ne_one,
      and_false, false_and, not_false_eq_true, ne_eq, one_ne_zero]
  · change SfaSucceeds q1 q2 ((1, 1), b) ↔ (1 : ZMod 2) ≠ 1
    rw [SfaSucceeds, Prod.addOrderOf, h11, hcop.lcm_eq_mul]
    simp only [dvd_mul_right, true_and, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      Prod.smul_mk, hone, hmul, ne_eq, not_true_eq_false]
    simp
    rfl

/-- The four parity sectors have equal size, and exactly two succeed. -/
theorem sfa_count_half (q1 q2 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime)
    (h1 : 2 < q1) (h2 : 2 < q2) [NeZero q1] [NeZero q2] :
    2 * sfaSuccessCount q1 q2 = Fintype.card (UnitModel q1 q2) := by
  classical
  have hp1 := hq1.odd_of_ne_two (by omega : q1 ≠ 2)
  have hp2 := hq2.odd_of_ne_two (by omega : q2 ≠ 2)
  change 2 * (Finset.univ.filter (SfaSucceeds q1 q2)).card = _
  simp only [Finset.card_filter, sfa_success_iff q1 q2 hp1 hp2]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, ZMod.card]
  rw [Fintype.sum_prod_type]
  change 2 * (∑ x : Fin 2, ∑ y : Fin 2,
    ∑ _z : ZMod q1 × ZMod q2, if x = y then 0 else 1) = 4 * (q1 * q2)
  simp only [Fin.sum_univ_two]
  simp
  omega

/-- A nonidentity input whose executed half-order test recovers a factor. -/
theorem sfa_positive :
    SfaSucceeds 3 5 ((1, 0), (1, 1)) := by
  rw [sfa_success_iff 3 5 (by decide) (by decide)]
  decide

/-- Equal nonzero parity bits give the actual Shor postprocessing failure. -/
theorem sfa_negative :
    ¬ SfaSucceeds 3 5 ((1, 1), (1, 1)) := by
  rw [sfa_success_iff 3 5 (by decide) (by decide)]
  exact fun h => h rfl

/-- Additive `-1` is not the multiplicative involution's cyclic coordinate. -/
theorem old_involution : (-1 : ZMod 6) ≠ 3 := by decide

end Qatlib.Papers.SemiprimeFact15.MainResults
