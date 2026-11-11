/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.LowSpinPlan
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Function.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Low Spin Probability

Low Spin Probability constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.FiniteExecution Qatlib.Foundations.ProbabilityCore.Concentration Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Matched

variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {d : ℕ}

-- Each direction keeps its own actual shifted observation carrier. This is
/-- the OQ algorithm's fresh-copy product, not a Pauli-data replacement. -/
def bellAxisLaw (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S)
    (q : BellPlanQ) : FinDist (LowSpinBellData S d e (some q)) where
  prob ω := ∏ j : Fin d,
    (freshObservationBlocks (n:=q.records) (m:=q.records) a b c k hz (e j) q.blocks).prob (ω j)
  nonneg ω := Finset.prod_nonneg fun j _ =>
    (freshObservationBlocks a b c k hz (e j) q.blocks).nonneg (ω j)
  sum_one := by
    change (∑ ω : (j : Fin d) → Fin q.blocks → CohortObservation q.records q.records (e j),
      ∏ j : Fin d,(freshObservationBlocks a b c k hz (e j) q.blocks).prob (ω j))=1
    calc
      _ = ∏ j : Fin d,∑ w : Fin q.blocks → CohortObservation q.records q.records (e j),
          (freshObservationBlocks a b c k hz (e j) q.blocks).prob w :=
        (Fintype.prod_sum (fun (j : Fin d) w =>
          (freshObservationBlocks a b c k hz (e j) q.blocks).prob w)).symm
      _ = 1 := by
        simp_rw [fun j => (freshObservationBlocks (n:=q.records) (m:=q.records)
          a b c k hz (e j) q.blocks).sum_one]
        simp

/-- Complete original `bell_axis_expect_product` guarantee for `LowSpinProbability`; all source hypotheses and output obligations are retained. -/
theorem bell_axis_expect_product (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S) (q : BellPlanQ)
    (g : (j : Fin d) → (Fin q.blocks → CohortObservation q.records q.records (e j)) → ℝ) :
    (bellAxisLaw a b c k hz e q).expect (fun ω => ∏ j : Fin d,g j (ω j))=
      ∏ j : Fin d,(freshObservationBlocks a b c k hz (e j) q.blocks).expect (g j) := by
  change (∑ ω : (j : Fin d) → Fin q.blocks → CohortObservation q.records q.records (e j),
    (∏ j : Fin d,(freshObservationBlocks a b c k hz (e j) q.blocks).prob (ω j))*
      (∏ j : Fin d,g j (ω j)))=_
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (j : Fin d) w =>
    (freshObservationBlocks a b c k hz (e j) q.blocks).prob w*g j w)).symm

/-- Complete original `bell_axis_expect_coord` guarantee for `LowSpinProbability`; all source hypotheses and output obligations are retained. -/
theorem bell_axis_expect_coord (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S) (q : BellPlanQ)
    (j : Fin d) (f : (Fin q.blocks → CohortObservation q.records q.records (e j)) → ℝ) :
    (bellAxisLaw a b c k hz e q).expect (fun ω => f (ω j))=
      (freshObservationBlocks a b c k hz (e j) q.blocks).expect f := by
  let g : (i : Fin d) → (Fin q.blocks → CohortObservation q.records q.records (e i)) → ℝ :=
    Function.update (fun _ => fun _ => 1) j f
  have hleft (ω : LowSpinBellData S d e (some q)) :
      (∏ i : Fin d,g i (ω i))=f (ω j) := by
    rw [Finset.prod_eq_single j]
    · simp [g]
    · intro i _ hne
      simp [g,hne]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  have hright :
      (∏ i : Fin d,(freshObservationBlocks a b c k hz (e i) q.blocks).expect (g i))=
        (freshObservationBlocks a b c k hz (e j) q.blocks).expect f := by
    rw [Finset.prod_eq_single j]
    · simp [g]
    · intro i _ hne
      simp only [g,Function.update_of_ne hne]
      exact finite_expect_const (freshObservationBlocks a b c k hz (e i) q.blocks) 1
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  calc
    _ = (bellAxisLaw a b c k hz e q).expect (fun ω => ∏ i : Fin d,g i (ω i)) := by
      simp_rw [hleft]
    _ = ∏ i : Fin d,(freshObservationBlocks a b c k hz (e i) q.blocks).expect (g i) :=
      bell_axis_expect_product a b c k hz e q g
    _ = _ := hright

/-- Complete original `bell_axis_bad_mass_coord` guarantee for `LowSpinProbability`; all source hypotheses and output obligations are retained. -/
theorem bell_axis_bad_mass_coord (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S) (q : BellPlanQ)
    (j : Fin d) (f : (Fin q.blocks → CohortObservation q.records q.records (e j)) → ℝ)
    (center radius : ℝ) :
    finiteBadMass (bellAxisLaw a b c k hz e q) (fun ω => f (ω j)) center radius=
      finiteBadMass (freshObservationBlocks a b c k hz (e j) q.blocks) f center radius := by
  rw [← finite_bad_indicator_mean,← finite_bad_indicator_mean,
    bell_axis_expect_coord a b c k hz e q j
      (fun w => if radius< |f w-center| then (1 : ℝ) else 0)]

/-- Construction for low Spin Bell Law in the low spin probability model. -/
def lowSpinBellLaw (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S)
    (spin : Option BellPlanQ) : FinDist (LowSpinBellData S d e spin) :=
  match spin with
  | none =>
    { prob := fun _ => 1
      nonneg := fun _ => zero_le_one
      sum_one := by simp only [LowSpinBellData,Fintype.sum_unique] }
  | some q => bellAxisLaw a b c k hz e q

-- The original velocity components and the fresh native Bell blocks are
/-- independent groups of supplied copies. No signed-Pauli group is executed. -/
def lowSpinLaw (p : LowSpinPlanQ) (mv : Fin d → S → ℝ)
    (hmv : ∀ j x, |mv j x|≤1) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S) :
    FinDist (LowSpinData S d e p) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => velocityRawLaw p.velocity.current p.velocity.crossRecords
      p.velocity.norm (mv j) (hmv j)))
    (lowSpinBellLaw a b c k hz e p.spin)

/-- Complete original `low_spin_velocity_marginal` guarantee for `LowSpinProbability`; all source hypotheses and output obligations are retained. -/
theorem low_spin_velocity_marginal (p : LowSpinPlanQ) (mv : Fin d → S → ℝ)
    (hmv : ∀ j x, |mv j x|≤1) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S)
    (f : (Fin d → VelocityData S p.velocity.current p.velocity.crossRecords p.velocity.norm) → ℝ) :
    (lowSpinLaw p mv hmv a b c k hz e).expect (fun z => f z.1)=
      (finiteFamilyLaw (fun j => velocityRawLaw p.velocity.current p.velocity.crossRecords
        p.velocity.norm (mv j) (hmv j))).expect f :=
  independent_pair_expect_left _ _ f

/-- Complete original `low_spin_bell_marginal` guarantee for `LowSpinProbability`; all source hypotheses and output obligations are retained. -/
theorem low_spin_bell_marginal (p : LowSpinPlanQ) (mv : Fin d → S → ℝ)
    (hmv : ∀ j x, |mv j x|≤1) (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → Equiv.Perm S)
    (f : LowSpinBellData S d e p.spin → ℝ) :
    (lowSpinLaw p mv hmv a b c k hz e).expect (fun z => f z.2)=
      (lowSpinBellLaw a b c k hz e p.spin).expect f :=
  independent_pair_expect_right _ _ f

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_axis_expect_product
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_axis_expect_coord
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.bell_axis_bad_mass_coord
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_velocity_marginal
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.low_spin_bell_marginal
