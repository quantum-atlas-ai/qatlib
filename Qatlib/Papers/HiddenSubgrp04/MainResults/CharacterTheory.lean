/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
public import Qatlib.Concepts.HspRecovery.BackendAudit.CharacterTableRecoveryProbability

@[expose] public section

/-!
# Character orthogonality and subgroup Fourier sampling

This module records character orthogonality, Fourier transformation of a uniform subgroup state,
and the interaction of translations with character phases. The recovery theorem
`theorem3_13_recovery` bounds the probability that character-table decoding reconstructs the
hidden subgroup under the explicit sample-budget condition.

The development follows [Lomont2004].

## Main statements

* `theorem3_11`: The abelian Fourier transform of the uniform subgroup state equals the uniform
  state on its character annihilator.
* `theorem3_12_eq69`: Applying the Fourier transform after translation by `t` equals multiplying
  the transformed function by evaluation at `t`.
* `theorem3_13_recovery`: If `f` hides `H` and the Boolean table correctly tests character
  kernels, then m samples recover `H` with probability at least 1 − 1/|G| whenever |G|2^(−m) ≤
  1/|G|.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option autoImplicit false

open scoped BigOperators
open scoped Classical

open Matrix
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.WalkFind.UniformThree

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- The sum of a character over a finite abelian group is the group cardinality for the trivial
character and zero otherwise ([Theorem 3.9][Lomont2004]). -/
theorem theorem3_9 (G : Type*) [AddCommGroup G] [Fintype G] (χ : AddChar G ℂ) :
    (∑ g : G, χ g) = if χ = 0 then (Fintype.card G : ℂ) else 0 := by
  classical
  exact AddChar.sum_eq_ite χ

/-- The uniform subgroup amplitude function, defined as the coset state of `H` at zero. -/
def subgroupKet {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) : G → ℂ :=
  abelianCosetState H 0

/-- The amplitude function on the dual group that is constant with value 1/√|H⊥| on the
character annihilator and zero elsewhere. -/
def annihilatorKet {G : Type*} [AddCommGroup G] [Fintype G]
    (H : AddSubgroup G) : AddChar G ℂ → ℂ :=
  fun χ =>
    if χ ∈ characterAnnihilator H then
      ((Real.sqrt (Fintype.card (characterAnnihilator H) : ℝ) : ℂ))⁻¹
    else 0

/-- For positive natural numbers a and b with ba = c, the complex-cast ratio √a/√c equals 1/√b. -/
theorem sqrt_card_ratio (a b c : ℕ) (ha : 0 < a) (_hb : 0 < b) (h : b * a = c) :
    (Real.sqrt (a : ℝ) : ℂ) * ((Real.sqrt (c : ℝ) : ℂ))⁻¹ =
      ((Real.sqrt (b : ℝ) : ℂ))⁻¹ := by
  have hc : (c : ℝ) = (b : ℝ) * (a : ℝ) := by
    rw [← h]
    push_cast
    ring
  have hbnonneg : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.zero_le b
  have hsa : Real.sqrt (a : ℝ) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by exact_mod_cast ha)).ne'
  have hsq : Real.sqrt (c : ℝ) = Real.sqrt (b : ℝ) * Real.sqrt (a : ℝ) := by
    rw [hc, Real.sqrt_mul hbnonneg]
  have hreal :
      Real.sqrt (a : ℝ) * (Real.sqrt (c : ℝ))⁻¹ = (Real.sqrt (b : ℝ))⁻¹ := by
    rw [hsq, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hsa, one_mul]
  have hcast :
      ((Real.sqrt (a : ℝ) : ℂ) * ((Real.sqrt (c : ℝ) : ℂ))⁻¹) =
        ((Real.sqrt (a : ℝ) * (Real.sqrt (c : ℝ))⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, hreal]
  push_cast
  ring

/-- The abelian Fourier transform of the uniform subgroup state equals the uniform state on its
character annihilator ([Theorem 3.11][Lomont2004]). -/
theorem theorem3_11 (G : Type*) [AddCommGroup G] [Fintype G]
    (H : AddSubgroup G) :
    abelianQFT (subgroupKet H) = annihilatorKet H := by
  funext χ
  change abelianQFT (abelianCosetState H 0) χ = annihilatorKet H χ
  rw [abelianQFT_cosetState H 0 χ]
  by_cases hχ : χ ∈ characterAnnihilator H
  · rw [ite_eq_left hχ, AddChar.map_zero_eq_one, one_mul]
    simp only [annihilatorKet, hχ, ite_true]
    exact sqrt_card_ratio (Fintype.card H) (Fintype.card (characterAnnihilator H))
      (Fintype.card G)
      (Fintype.card_pos_iff.mpr ⟨0⟩)
      (Fintype.card_pos_iff.mpr ⟨0⟩)
      (card_characterAnnihilator H)
  · rw [ite_eq_right hχ]
    simp [annihilatorKet, hχ]

/-- Translation of an amplitude function by `t`, sending `x` to `u (x - t)`. -/
def translation {G : Type*} [AddCommGroup G] (t : G) (u : G → ℂ) : G → ℂ :=
  fun x => u (x - t)

/-- Pointwise multiplication of an amplitude function by the values of the character `χ`. -/
def phase {G : Type*} [AddCommGroup G] (χ : AddChar G ℂ) (u : G → ℂ) : G → ℂ :=
  fun g => χ g * u g

/-- Translation of a function on the dual group by `ψ`, sending `χ` to `v (χ - ψ)`. -/
def translationDual {G : Type*} [AddCommGroup G]
    (ψ : AddChar G ℂ) (v : AddChar G ℂ → ℂ) : AddChar G ℂ → ℂ :=
  fun χ => v (χ - ψ)

/-- Pointwise multiplication of a function on the dual group by evaluation of each character at
`t`. -/
def phaseDual {G : Type*} [AddCommGroup G]
    (t : G) (v : AddChar G ℂ → ℂ) : AddChar G ℂ → ℂ :=
  fun χ => χ t * v χ

/-- Translation and character phase multiplication commute up to the scalar `h t`, in the
displayed order ([Theorem 3.12 (Commutative laws of the G-operators)][Lomont2004]). -/
theorem theorem3_12_eq67 {G : Type*} [AddCommGroup G] (h : AddChar G ℂ) (t : G)
    (u : G → ℂ) :
    (fun g => h t * translation t (phase h u) g) = phase h (translation t u) := by
  funext g
  simp only [translation, phase]
  rw [AddChar.map_sub_eq_div]
  have ht : h t ≠ 0 := (AddChar.val_isUnit h t).ne_zero
  field_simp [ht]

/-- Applying the Fourier transform after the phase `h` equals translating the Fourier transform
by −h on the dual group ([Theorem 3.12 (Commutative laws of the G-operators)][Lomont2004]). -/
theorem theorem3_12_eq68 {G : Type*} [AddCommGroup G] [Fintype G]
    (h : AddChar G ℂ) (u : G → ℂ) :
    abelianQFT (phase h u) = translationDual (-h) (abelianQFT u) := by
  funext χ
  simp only [abelianQFT, abelianQFTMatrix, Matrix.mulVec, dotProduct, phase, translationDual,
    sub_neg_eq_add, AddChar.add_apply]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Applying the Fourier transform after translation by `t` equals multiplying the transformed
function by evaluation at `t` ([Theorem 3.12 (Commutative laws of the
G-operators)][Lomont2004]). -/
theorem theorem3_12_eq69 {G : Type*} [AddCommGroup G] [Fintype G]
    (t : G) (u : G → ℂ) :
    abelianQFT (translation t u) = phaseDual t (abelianQFT u) := by
  funext χ
  simp only [abelianQFT, abelianQFTMatrix, Matrix.mulVec, dotProduct, translation, phaseDual]
  have hshift :
      (∑ x : G, (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ * χ x * u (x - t)) =
        ∑ x : G, (Real.sqrt (Fintype.card G : ℝ) : ℂ)⁻¹ * χ (x + t) * u x := by
    refine Fintype.sum_equiv (Equiv.addRight (-t)) _ _ ?_
    intro x
    simp [sub_eq_add_neg, add_comm]
  rw [hshift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [AddChar.map_add_eq_mul]
  ring

/-- If `f` hides `H` and the Boolean table correctly tests character kernels, then m samples
recover `H` with probability at least 1 − 1/|G| whenever |G|2^(−m) ≤ 1/|G| ([Theorem 3.13
(Finite abelian HSP algorithm)][Lomont2004]). -/
theorem theorem3_13_recovery {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : G → R) (e : G ≃+ AddChar G ℂ) (tab : G → G → Bool)
    (H : AddSubgroup G) (m : ℕ) (hf : HidesSubgroup f H)
    (htab : ∀ a y, tab a y = true ↔ e a y = 1)
    (hbudget : (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹) ^ m ≤ (Fintype.card G : ℝ)⁻¹) :
    1 - (Fintype.card G : ℝ)⁻¹ ≤
      (tableGroupRecordDist f e).probEvent (L := m)
        (fun xs : Fin m → G =>
          ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G)) := by
  have h := character_table_actual_subgroup_recovery_probability (R := R) f e tab H m hf htab
  linarith

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
