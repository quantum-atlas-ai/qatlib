/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsStat
import Mathlib.Tactic.Abel

/-!
# Hidden shift and reflection oracle reductions

This module proves the oracle promise transformations collected in `SourceOracleReductions`. It
constructs reflection promises from hidden shifts, establishes injectivity of paired reflection
values under a nontrivial doubling condition, and combines the reductions.

The reductions correspond to the setting of [Kuperberg2005], including its comparison of hidden
shift and hidden reflection problems.

## Main statements

* `source_shift_dihedral`: transforms a hidden shift into a dihedral reflection hiding promise.
* `source_shift_reflection`: constructs an abelian reflection promise.
* `sourceOracleReductions`: assembles the oracle reductions.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

/-- For a hidden shift promise, `f a = g b` holds exactly when `b = a + s`. -/
private theorem shift_cross {A S : Type*} [AddCommGroup A] {f g : A → S} {s : A}
    (h : HiddenShift f g s) (a b : A) : f a = g b ↔ b = a + s := by
  rw [h.2.2 a]
  exact h.2.1.eq_iff.trans eq_comm

/-- A hidden shift promise makes `shiftToDihedralOracle f g` hide the reflection specified by
`s`. -/
theorem source_shift_dihedral {A S : Type*} [AddCommGroup A] {f g : A → S} {s : A}
    (h : HiddenShift f g s) : AbelianReflectionHides (shiftToDihedralOracle f g) s := by
  rintro ⟨a, ta⟩ ⟨b, tb⟩
  cases ta <;> cases tb
  · simpa [shiftToDihedralOracle, abelianReflect, eq_comm] using h.1.eq_iff (a := a) (b := b)
  · simpa [shiftToDihedralOracle, abelianReflect] using shift_cross h a b
  · simpa [shiftToDihedralOracle, abelianReflect, eq_comm, eq_sub_iff_add_eq] using
      shift_cross h b a
  · simpa [shiftToDihedralOracle, abelianReflect, eq_comm] using h.2.1.eq_iff (a := a) (b := b)

/-- A hidden shift promise makes `shiftToReflectionOracle f g` satisfy the abelian reflection
promise for `s`. -/
theorem source_shift_reflection {A S : Type*} [AddCommGroup A] {f g : A → S} {s : A}
    (h : HiddenShift f g s) : AbelianReflection (shiftToReflectionOracle f g) s := by
  intro a b
  simp only [shiftToReflectionOracle, Sym2.eq_iff, h.1.eq_iff, h.2.1.eq_iff,
    neg_inj, shift_cross h]
  constructor
  · rintro (⟨hab, _⟩ | ⟨h₁, _⟩)
    · exact Or.inl hab.symm
    · exact Or.inr (by rw [h₁]; abel)
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      constructor
      · abel
      · symm
        apply (shift_cross h (- (s - a)) a).mpr
        abel

/-- For a reflection oracle, pairing values at `a` and `a - v` gives an injective map when `v +
v ≠ 0`. -/
private theorem reflection_pair_injective {A S : Type*} [AddCommGroup A]
    {h : A → S} {s v : A} (hh : AbelianReflection h s) (hv : v + v ≠ 0) :
    Function.Injective (fun a => (h a, h (a - v))) := by
  intro a b hab
  have h₁ := (hh a b).mp (congrArg Prod.fst hab)
  have h₂ := (hh (a - v) (b - v)).mp (congrArg Prod.snd hab)
  rcases h₁ with h₁ | h₁
  · exact h₁.symm
  rcases h₂ with h₂ | h₂
  · exact (add_right_cancel (show b + -v = a + -v by simpa only [sub_eq_add_neg] using h₂)).symm
  · exfalso
    apply hv
    have hx : b - v = b + v := by
      calc
        b - v = s - (a - v) := h₂
        _ = (s - a) + v := by abel
        _ = b + v := by rw [h₁]
    have he : -v = v := add_left_cancel (show b + -v = b + v by
      simpa only [sub_eq_add_neg] using hx)
    calc v + v = v + -v := by rw [he]
         _ = 0 := add_neg_cancel v

/-- The hidden shift, abelian reflection, dihedral reflection, and exponent-two Simon promise
reductions satisfy `SourceOracleReductions`. See [Kuperberg, Proposition
6.1][Kuperberg2005]. -/
theorem sourceOracleReductions : SourceOracleReductions := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A S _ f g s hh
    exact source_shift_dihedral hh
  · intro A S _ f g s hh
    exact source_shift_reflection hh
  · intro A S _ h s v hh hv
    have hi := reflection_pair_injective hh hv
    refine ⟨?_, hi, ?_⟩
    · intro a b hab
      apply neg_injective
      have hvneg : -v + -v ≠ 0 := by simpa only [← neg_add, neg_ne_zero] using hv
      apply reflection_pair_injective hh hvneg
      simpa [reflectionToShiftLeft, sub_eq_add_neg, add_comm] using hab
    · intro a
      apply Prod.ext
      · exact (hh (-a) (a + s)).mpr (Or.inr (by abel))
      · exact (hh (v - a) (a + s - v)).mpr (Or.inr (by abel))
  · intro A S _ h s hh hexp a b
    have ha : -a = a := by
      apply neg_eq_iff_add_eq_zero.mpr
      exact hexp a
    simpa [sub_eq_add_neg, ha, add_comm] using hh a b
  · intro A S _ h s hh
    refine ⟨?_, ?_, ?_⟩
    · intro a b hab
      rcases (hh (a, false) (b, false)).mp hab with he | he
      · exact (congrArg Prod.fst he).symm
      · have ht := congrArg Prod.snd he
        simp [abelianReflect] at ht
    · intro a b hab
      rcases (hh (a, true) (b, true)).mp hab with he | he
      · exact (congrArg Prod.fst he).symm
      · have ht := congrArg Prod.snd he
        simp [abelianReflect] at ht
    · intro a
      exact (hh (a, false) (a + s, true)).mpr (Or.inr rfl)

end Qatlib.Concepts.HspRecovery.ReductionCore
