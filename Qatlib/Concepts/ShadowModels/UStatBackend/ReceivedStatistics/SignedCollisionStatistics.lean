/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.FinitePairUStatistic
import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.GroupedPairStatistics

/-!
# Signed record laws and collision moments

This module defines finite signed record laws with uniform label marginals and prescribed
bounded signals. The residual collision kernel has a computable conditional mean and is unbiased
for a uniform mean squared residual, providing probability identities for nonlinear estimators
related to [HuangKuengPreskill2020].

## Main statements

* `signed_record_cell_mean`: the signed residual mean at a fixed label.
* `residual_collision_projection`: the conditional collision mean.
* `residual_collision_unbiased`: the mean squared residual identity.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics
noncomputable section
open scoped BigOperators

variable {S : Type*} [Fintype S] [Nonempty S]

/-- The real sign of a record bit, equal to negative one for true and positive one for false. -/
def recordSign (b : Bool) : ℝ := if b then -1 else 1

/-- The weight of a label-bit record with uniform label mass and sign bias given by `m`. -/
def signedRecordWeight (m : S → ℝ) (r : S × Bool) : ℝ :=
  (1+Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign r.2*m r.1)/(2*(Fintype.card S : ℝ))

/-- Summing the two bit weights at a fixed label gives `1 / Fintype.card S`. -/
theorem signed_record_cell_mass (m : S → ℝ) (x : S) :
    (∑ b : Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m (x,b)) = 1/(Fintype.card S : ℝ) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.sum_bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign, Bool.false_eq_true,
    if_false, if_true]
  field_simp
  ring

/-- The finite signed record distribution associated with a signal of absolute value at most
one. -/
def signedRecordLaw (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (S × Bool) where
  prob := Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m
  nonneg r := by
    have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hmx := abs_le.mp (hm r.1)
    unfold Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign
    split <;> apply div_nonneg <;> linarith
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signed_record_cell_mass]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- The signed residual weighted over the two bits at a fixed label equals the signal residual
divided by the label count. -/
theorem signed_record_cell_mean (m u : S → ℝ) (α β : ℝ) (x : S) :
    (∑ b : Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m (x,b)*(α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign b-β*u x)) =
      (α*m x-β*u x)/(Fintype.card S : ℝ) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.sum_bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign, Bool.false_eq_true,
    if_false, if_true]
  field_simp
  ring

variable [DecidableEq S]

/-- The product of two signed residuals scaled by the label count when their labels match, and
zero otherwise. -/
def residualCollision (α β : ℝ) (u : S → ℝ) (l r : S × Bool) : ℝ :=
  if l.1=r.1 then (Fintype.card S : ℝ)*
    (α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign l.2-β*u l.1)*(α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign r.2-β*u r.1) else 0

/-- Averaging the second record of the residual collision kernel gives the first signed residual
times the signal residual at its label. -/
theorem residual_collision_projection (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (l : S × Bool) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun r => Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision α β u l r) =
      (α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign l.2-β*u l.1)*(α*m l.1-β*u l.1) := by
  change (∑ r : S × Bool,
      Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m r*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision α β u l r) = _
  rw [Fintype.sum_prod_type]
  have hsite (x : S) :
      (∑ b : Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m (x,b)*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision α β u l (x,b)) =
      if x=l.1 then (α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign l.2-β*u l.1)*(α*m l.1-β*u l.1) else 0 := by
    by_cases hx : x=l.1
    · subst x
      simp only [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision, ite_true]
      calc
        _ = (Fintype.card S : ℝ)*(α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign l.2-β*u l.1)*
            (∑ b : Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m (l.1,b)*(α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign b-β*u l.1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          rw [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signed_record_cell_mean]
          have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
          field_simp
    · simp [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision,
        hx, Ne.symm hx]
  simp_rw [hsite]
  simp

/-- The mean residual collision kernel under two independent signed records equals the uniform
mean squared signal residual. -/
theorem residual_collision_unbiased (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun l =>
      (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun r => Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision α β u l r)) =
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) := by
  change (∑ l : S × Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m l *
    (Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun r => Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision α β u l r)) = _
  simp_rw [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residual_collision_projection]
  rw [Fintype.sum_prod_type]
  have hsite (x : S) :
      (∑ b : Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m (x,b)*
        ((α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign b-β*u x)*(α*m x-β*u x))) =
      (α*m x-β*u x)^2/(Fintype.card S : ℝ) := by
    calc
      _ = (∑ b : Bool, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signedRecordWeight m (x,b)*(α*Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign b-β*u x))*
          (α*m x-β*u x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.signed_record_cell_mean]; ring
  simpa only [Finset.sum_div] using (Finset.sum_congr rfl fun x _ => hsite x)

end
end Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics
