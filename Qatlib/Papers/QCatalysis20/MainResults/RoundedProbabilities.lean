/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QCatalysis20.MainResults.Rounding

def rounded {n : ℕ} (M : ℕ) (w : Fin (n+1)→ℝ) : Fin (n+1)→ℝ :=
  Fin.cons (1-∑i:Fin n,(Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ))
    (fun i=> (Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ))

theorem rounded_tail_bounds {n M : ℕ} (hM : 0<M) (w : Fin (n+1)→ℝ)
    (hw : ∀i,0≤w i) (i : Fin n) :
    0≤rounded M w i.succ ∧ rounded M w i.succ≤w i.succ := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  change 0≤(Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ) ∧ _≤w i.succ
  constructor
  · positivity
  · exact (div_le_iff₀ hm).mpr
      (by simpa [mul_comm] using Nat.floor_le (mul_nonneg hm.le (hw i.succ)))

theorem rounded_sum {n M : ℕ} (w : Fin (n+1)→ℝ) : ∑i,rounded M w i=1 := by
  rw [Fin.sum_univ_succ]
  simp [rounded]

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

theorem rounded_tail_error {n M : ℕ} (hM : 0<M) (w : Fin (n+1)→ℝ)
    (i : Fin n) :
    w i.succ-rounded M w i.succ≤1/(M:ℝ) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have h := Nat.lt_floor_add_one ((M:ℝ)*w i.succ)
  change w i.succ-(Nat.floor ((M:ℝ)*w i.succ):ℝ)/(M:ℝ)≤1/(M:ℝ)
  apply (le_div_iff₀ hm).mpr
  field_simp at *
  nlinarith

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

def denominator (n μ : ℕ) : ℕ := 2*(n+1)*2^μ

theorem denominator_pos (n μ : ℕ) : 0<denominator n μ := by unfold denominator;positivity

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
