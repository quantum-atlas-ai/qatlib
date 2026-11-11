/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.GroupedPairStatistics
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option backward.isDefEq.respectTransparency false
/-!
# Signed collision statistics

Adapted from TiMidlY's BornCurrentRecords in OQ #117 at
`10c852ef09801ec0ccfea4b579a88152345dd8bc`. This module retains the independent,
reusable definitions and proofs with their original premises. Its consumer
results are verified separately; it does not assert acceptance of the full
original research problem.
-/
set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics
noncomputable section
open scoped BigOperators


variable {S : Type*} [Fintype S] [Nonempty S]

/-- Construction for record Sign in the signed collision statistics model. -/
def recordSign (b : Bool) : ℝ := if b then -1 else 1

/-- Construction for signed Record Weight in the signed collision statistics model. -/
def signedRecordWeight (m : S → ℝ) (r : S × Bool) : ℝ :=
  (1+Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign r.2*m r.1)/(2*(Fintype.card S : ℝ))

/-- The exact `signed_record_cell_mass` invariant under the original hypotheses and resource conventions. -/
theorem signed_record_cell_mass (m : S → ℝ) (x : S) :
    (∑ b : Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m (x,b)) = 1/(Fintype.card S : ℝ) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.sum_bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign, Bool.false_eq_true,
    ite_false, ite_true]
  field_simp
  ring

/-- Construction for signed Record Law in the signed collision statistics model. -/
def signedRecordLaw (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (S × Bool) where
  prob := Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m
  nonneg r := by
    have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hmx := abs_le.mp (hm r.1)
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign
    split <;> apply div_nonneg <;> linarith
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signed_record_cell_mass]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp


/-- The exact `signed_record_cell_mean` invariant under the original hypotheses and resource conventions. -/
theorem signed_record_cell_mean (m u : S → ℝ) (α β : ℝ) (x : S) :
    (∑ b : Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m (x,b)*(α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign b-β*u x)) =
      (α*m x-β*u x)/(Fintype.card S : ℝ) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Fintype.sum_bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign, Bool.false_eq_true,
    ite_false, ite_true]
  field_simp
  ring


variable [DecidableEq S]

/-- Construction for residual Collision in the signed collision statistics model. -/
def residualCollision (α β : ℝ) (u : S → ℝ) (l r : S × Bool) : ℝ :=
  if l.1=r.1 then (Fintype.card S : ℝ)*
    (α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign l.2-β*u l.1)*(α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign r.2-β*u r.1) else 0

/-- The exact `residual_collision_projection` invariant under the original hypotheses and resource conventions. -/
theorem residual_collision_projection (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (l : S × Bool) :
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun r => Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision α β u l r) =
      (α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign l.2-β*u l.1)*(α*m l.1-β*u l.1) := by
  change (∑ r : S × Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m r*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision α β u l r) = _
  rw [Fintype.sum_prod_type]
  have hsite (x : S) :
      (∑ b : Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m (x,b)*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision α β u l (x,b)) =
      if x=l.1 then (α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign l.2-β*u l.1)*(α*m l.1-β*u l.1) else 0 := by
    by_cases hx : x=l.1
    · subst x
      simp only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision, ite_true]
      calc
        _ = (Fintype.card S : ℝ)*(α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign l.2-β*u l.1)*
            (∑ b : Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m (l.1,b)*(α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign b-β*u l.1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signed_record_cell_mean]
          have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
          field_simp
    · simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision, hx, Ne.symm hx]
  simp_rw [hsite]
  simp


/-- The exact `residual_collision_unbiased` invariant under the original hypotheses and resource conventions. -/
theorem residual_collision_unbiased (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) :
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun l =>
      (Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun r => Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision α β u l r)) =
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) := by
  change (∑ l : S × Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m l *
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordLaw m hm).expect (fun r => Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residualCollision α β u l r)) = _
  simp_rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.residual_collision_projection]
  rw [Fintype.sum_prod_type]
  have hsite (x : S) :
      (∑ b : Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m (x,b)*
        ((α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign b-β*u x)*(α*m x-β*u x))) =
      (α*m x-β*u x)^2/(Fintype.card S : ℝ) := by
    calc
      _ = (∑ b : Bool, Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signedRecordWeight m (x,b)*(α*Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.recordSign b-β*u x))*
          (α*m x-β*u x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics.signed_record_cell_mean]; ring
  simpa only [Finset.sum_div] using (Finset.sum_congr rfl fun x _ => hsite x)


end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics
