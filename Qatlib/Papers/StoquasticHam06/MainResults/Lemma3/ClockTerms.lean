/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Lemma3.Basic
import Mathlib.Data.Matrix.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma3

def RealStoquastic {κ : Type*} (A : Matrix κ κ ℝ) : Prop :=
  ∀ x y, x ≠ y → A x y ≤ 0

theorem realStoquastic_add {κ : Type*} {A B : Matrix κ κ ℝ}
    (hA : RealStoquastic A) (hB : RealStoquastic B) :
    RealStoquastic (A + B) := by
  intro x y hxy
  change A x y + B x y ≤ 0
  exact add_nonpos (hA x y hxy) (hB x y hxy)

theorem realStoquastic_sum {κ : Type*} [Fintype κ] {m : ℕ}
    (A : Fin m → Matrix κ κ ℝ) (hA : ∀ a, RealStoquastic (A a)) :
    RealStoquastic (∑ a, A a) := by
  intro x y hxy
  have h1 : (∑ a, A a) x = ∑ a, A a x := Finset.sum_apply x Finset.univ A
  have h2 : (∑ a, A a x) y = ∑ a, A a x y :=
    Finset.sum_apply y Finset.univ (fun a => A a x)
  rw [show (∑ a, A a) x y = ∑ a, A a x y by rw [h1, h2]]
  exact Finset.sum_nonpos (fun a _ => hA a x y hxy)

theorem realStoquastic_diag {κ : Type*} (D : Matrix κ κ ℝ)
    (hD : ∀ x y, x ≠ y → D x y = 0) : RealStoquastic D :=
  fun x y hxy => by rw [hD x y hxy]

def minusVec (a b : Bool) : ℝ := if a = b then (1 : ℝ) / 2 else -(1 : ℝ) / 2

def hinTerm {κ : Type*} [DecidableEq κ] (z : κ) : Matrix (Bool × κ) (Bool × κ) ℝ :=
  fun p q => minusVec p.1 q.1 * (if p.2 = z then (if q.2 = z then 1 else 0) else 0)

theorem hinTerm_stoquastic {κ : Type*} [DecidableEq κ] (z : κ) :
    RealStoquastic (hinTerm z) := by
  intro p q hpq
  by_cases hp2 : p.2 = z
  · by_cases hq2 : q.2 = z
    · have hp1 : p.1 ≠ q.1 := by
        intro h
        exact hpq (Prod.ext h (by rw [hp2, hq2]))
      simp [hinTerm, minusVec, hp2, hq2, hp1]
      norm_num
    · simp [hinTerm, hp2, hq2]
  · simp [hinTerm, hp2]

def transInd {κ : Type*} [DecidableEq κ] (a b v w : κ) : ℝ :=
  if a = v ∧ b = w then 1 else 0

def couplingTerm {ι κ : Type*} [DecidableEq κ]
    (R : Matrix ι ι ℝ) (v w : κ) : Matrix (ι × κ) (ι × κ) ℝ :=
  fun p q => - (R p.1 q.1 * transInd p.2 q.2 v w + R p.1 q.1 * transInd p.2 q.2 w v)

theorem couplingTerm_stoquastic {ι κ : Type*} [DecidableEq κ]
    (R : Matrix ι ι ℝ) (hR : ∀ a b, 0 ≤ R a b) (v w : κ) (_hvw : v ≠ w) :
    RealStoquastic (couplingTerm R v w) := by
  intro p q _hpq
  unfold couplingTerm transInd
  have h1 : 0 ≤ R p.1 q.1 * (if p.2 = v ∧ q.2 = w then (1 : ℝ) else 0) :=
    mul_nonneg (hR p.1 q.1) (by split_ifs <;> norm_num)
  have h2 : 0 ≤ R p.1 q.1 * (if p.2 = w ∧ q.2 = v then (1 : ℝ) else 0) :=
    mul_nonneg (hR p.1 q.1) (by split_ifs <;> norm_num)
  linarith

theorem hevolv_stoquastic {ι κ : Type*} [DecidableEq κ]
    (D : Matrix (ι × κ) (ι × κ) ℝ) (hD : ∀ p q, p ≠ q → D p q = 0)
    (R : Matrix ι ι ℝ) (hR : ∀ a b, 0 ≤ R a b) (v w : κ) (hvw : v ≠ w) :
    RealStoquastic (fun p q => D p q + couplingTerm R v w p q) := by
  intro p q hpq
  show D p q + couplingTerm R v w p q ≤ 0
  rw [hD p q hpq, zero_add]
  exact couplingTerm_stoquastic R hR v w hvw p q hpq

theorem clock_hamiltonian_stoquastic {κ : Type*}
    (Hin Hout Hprop Hclock : Matrix κ κ ℝ)
    (hIn : RealStoquastic Hin) (hOut : RealStoquastic Hout)
    (hProp : RealStoquastic Hprop) (hClock : RealStoquastic Hclock) :
    RealStoquastic (Hin + Hout + Hprop + Hclock) :=
  realStoquastic_add (realStoquastic_add (realStoquastic_add hIn hOut) hProp) hClock

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma3
