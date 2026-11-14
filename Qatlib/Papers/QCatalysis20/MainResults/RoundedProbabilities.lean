/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Rounded coefficient probabilities

This module rounds all noninitial probabilities down to a denominator grid and assigns the
residual mass to the first entry. It proves nonnegativity, exact normalization, and an ℓ¹ error
budget yielding precision `2⁻μ` for `denominator n μ`. See [VonBurgEtAl2021].

## Main statements

* `rounded_l1_error`: For a probability vector with `n` tail coordinates and positive
  denominator, the total rounding error is at most `2 * n / M`.
* `actual_precision`: Rounding a probability vector with `denominator n μ` gives ℓ¹ error at
  most `2⁻μ`.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QCatalysis20.MainResults.Rounding

/-- Round the tail weights down to multiples of `1 / M` and assign the remaining mass to the
first coordinate. -/
def rounded {n : ℕ} (M : ℕ) (w : Fin (n+1)→ℝ) : Fin (n+1)→ℝ :=
  Fin.cons (1-∑i:Fin n,(Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ))
    (fun i=> (Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ))

/-- For positive denominator and nonnegative weights, each rounded tail coordinate lies between
zero and its original value. -/
theorem rounded_tail_bounds {n M : ℕ} (hM : 0<M) (w : Fin (n+1)→ℝ)
    (hw : ∀i,0≤w i) (i : Fin n) :
    0≤rounded M w i.succ ∧ rounded M w i.succ≤w i.succ := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  change 0≤(Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ) ∧ _≤w i.succ
  constructor
  · positivity
  · exact (div_le_iff₀ hm).mpr
      (by simpa [mul_comm] using Nat.floor_le (mul_nonneg hm.le (hw i.succ)))

/-- The rounded vector sums to one by the residual definition of its first coordinate. -/
theorem rounded_sum {n M : ℕ} (w : Fin (n+1)→ℝ) : ∑i,rounded M w i=1 := by
  rw [Fin.sum_univ_succ]
  simp [rounded]

/-- Rounding a probability vector with positive denominator produces nonnegative coordinates. -/
theorem rounded_nonneg {n M : ℕ} (hM : 0<M) (w : Fin (n+1)→ℝ)
    (hw : ∀i,0≤w i) (hs : ∑i,w i=1) : ∀i,0≤rounded M w i := by
  have ht : ∑i:Fin n,rounded M w i.succ≤∑i:Fin n,w i.succ :=
    Finset.sum_le_sum (fun i _=>(rounded_tail_bounds hM w hw i).2)
  have he := hs
  rw [Fin.sum_univ_succ] at he
  intro i
  refine Fin.cases ?_ (fun i=>(rounded_tail_bounds hM w hw i).1) i
  change 0≤1-∑i:Fin n,rounded M w i.succ
  linarith [hw 0]

/-- For positive denominator, the original value minus a rounded tail coordinate is at most `1 /
M`. -/
theorem rounded_tail_error {n M : ℕ} (hM : 0<M) (w : Fin (n+1)→ℝ)
    (i : Fin n) :
    w i.succ-rounded M w i.succ≤1/(M:ℝ) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have h := Nat.lt_floor_add_one ((M:ℝ)*w i.succ)
  change w i.succ-(Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ)≤1/(M:ℝ)
  apply (le_div_iff₀ hm).mpr
  field_simp at *
  nlinarith

/-- For a probability vector with `n` tail coordinates and positive denominator, the total
rounding error is at most `2 * n / M`. -/
theorem rounded_l1_error {n M : ℕ} (hM : 0<M) (w : Fin (n+1)→ℝ)
    (hw : ∀i,0≤w i) (hs : ∑i,w i=1) :
    ∑i,|rounded M w i-w i|≤2*(n:ℝ)/(M:ℝ) := by
  have he:=hs
  rw [Fin.sum_univ_succ] at he
  have ht:=Finset.sum_le_sum
      (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>(rounded_tail_bounds hM w hw i).2)
  have hhead : w 0≤rounded M w 0 := by
    change w 0≤1-∑i:Fin n,rounded M w i.succ
    linarith
  rw [Fin.sum_univ_succ,abs_of_nonneg (sub_nonneg.mpr hhead)]
  have habs : ∀i:Fin n,|rounded M w i.succ-w i.succ|=w i.succ-rounded M w i.succ :=
    by
      intro i
      rw [abs_of_nonpos (sub_nonpos.mpr (rounded_tail_bounds hM w hw i).2)]
      ring
  simp_rw [habs]
  have hsum : ∑i:Fin n,(w i.succ-rounded M w i.succ)≤(n:ℝ)/(M:ℝ) := by
    calc
      _≤∑i:Fin n,1/(M:ℝ) := Finset.sum_le_sum (fun i _=>rounded_tail_error hM w i)
      _=(n:ℝ)/(M:ℝ) := by simp [div_eq_mul_inv]
  change (1-∑i:Fin n,rounded M w i.succ)-w 0+_≤_
  rw [Finset.sum_sub_distrib] at hsum ⊢
  rw [show 2*(n:ℝ)/(M:ℝ)=2*((n:ℝ)/M) by ring]
  linarith

/-- The positive rounding denominator `2 * (n + 1) * 2^μ` for precision parameter `μ`. -/
def denominator (n μ : ℕ) : ℕ := 2*(n+1)*2^μ

/-- The chosen rounding denominator is strictly positive. -/
theorem denominator_pos (n μ : ℕ) : 0<denominator n μ := by unfold denominator;positivity

/-- Rounding a probability vector with `denominator n μ` gives ℓ¹ error at most `2⁻μ`. See
[VonBurgEtAl2021]. -/
theorem actual_precision {n : ℕ} (μ : ℕ) (w : Fin (n+1)→ℝ)
    (hw : ∀i,0≤w i) (hs : ∑i,w i=1) :
    ∑i,|rounded (denominator n μ) w i-w i|≤(2:ℝ)^(-(μ:ℤ)) := by
  apply (rounded_l1_error (denominator_pos n μ) w hw hs).trans
  rw [zpow_neg,zpow_natCast]
  have hp : (0:ℝ)<(2:ℝ)^μ := by positivity
  have hm : (0:ℝ)<2*(n+1)*(2:ℝ)^μ := by positivity
  simp only [denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
  apply (div_le_iff₀ hm).mpr
  field_simp
  norm_num

end Qatlib.Papers.QCatalysis20.MainResults.Rounding
