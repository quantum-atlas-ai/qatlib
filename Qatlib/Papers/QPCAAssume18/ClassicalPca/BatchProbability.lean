/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.Algorithm

/-!
# Finite probability bounds for PCA batches

Provides finite event masses, dependent joint laws, and union bounds for independently sampled
coordinates. These elementary probability results combine sketch and output-access failures in
the classical PCA analysis of [Tang2021].

## Main statements

* `pca_joint_failure`: A first-stage failure bound `a` and conditional second-stage failure
  bound `b` outside the first failure event give joint failure mass at most `a + b`.
* `pca_independent_union`: If every coordinate failure has mass at most `b`, the mass of any
  coordinate failure in the independent product is at most `k * b`.

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
local instance (priority := 1000000) pcaPropDecision (P : Prop) : Decidable P :=
    Classical.propDecidable P

/-- The mass of a finite event, computed by summing probabilities over the elements satisfying
its predicate. -/
def pcaFiniteMass {X : Type} [Fintype X] (p : FinDist X) (P : X→Prop) : ℝ :=
  ∑ x∈Finset.univ.filter P,p.prob x

/-- The finite event mass equals the expectation of its indicator function. -/
theorem pcaFiniteMass_indicator {X : Type} [Fintype X] (p : FinDist X) (P : X→Prop) :
    pcaFiniteMass p P=p.expect (fun x => if P x then 1 else 0) := by
  simp only [pcaFiniteMass,FinDist.expect,Finset.sum_filter,mul_ite,mul_one,mul_zero]

/-- The mass of a finite event lies in the interval `[0, 1]`. -/
theorem pcaFiniteMass_range {X : Type} [Fintype X] (p : FinDist X) (P : X→Prop) :
    0≤pcaFiniteMass p P ∧ pcaFiniteMass p P≤1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => p.nonneg x
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => p.nonneg x)).trans_eq p.sum_one

/-- The joint distribution with mass `p.prob x * (conditional x).prob y`. -/
def pcaJointLaw {X Y : Type} [Fintype X] [Fintype Y]
    (p : FinDist X) (conditional : X→FinDist Y) : FinDist (X×Y) where
  prob z := p.prob z.1*(conditional z.1).prob z.2
  nonneg z := mul_nonneg (p.nonneg _) ((conditional _).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,(conditional _).sum_one,mul_one,p.sum_one]

/-- A first-stage failure bound `a` and conditional second-stage failure bound `b` outside the
first failure event give joint failure mass at most `a + b`. -/
theorem pca_joint_failure {X Y : Type} [Fintype X] [Fintype Y]
    (p : FinDist X) (conditional : X→FinDist Y) (BadX : X→Prop) (BadY : X→Y→Prop)
    (a b : ℝ) (hb : 0≤b) (hfirst : pcaFiniteMass p BadX≤a)
    (hsecond : ∀ x,¬BadX x→pcaFiniteMass (conditional x) (BadY x)≤b) :
    pcaFiniteMass (pcaJointLaw p conditional) (fun z => BadX z.1 ∨ BadY z.1 z.2)≤a+b := by
  rw [pcaFiniteMass_indicator]
  unfold FinDist.expect
  simp only [Fintype.sum_prod_type,pcaJointLaw]
  have hpoint (x : X) :
      (∑ y,p.prob x*(conditional x).prob y*(if BadX x ∨ BadY x y then 1 else 0))≤
      p.prob x*((if BadX x then 1 else 0)+b) := by
    rw [show (∑ y,p.prob x*(conditional x).prob y*(if BadX x ∨ BadY x y then 1 else 0))=
      p.prob x*(∑ y,(conditional x).prob y*(if BadX x ∨ BadY x y then 1 else 0)) by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring]
    apply mul_le_mul_of_nonneg_left _ (p.nonneg x)
    by_cases hx : BadX x
    · simp only [hx,true_or,if_true,mul_one,(conditional x).sum_one]
      linarith
    · simp only [hx,false_or,if_false,zero_add]
      rw [← FinDist.expect,← pcaFiniteMass_indicator]
      exact hsecond x hx
  have hsum := Finset.sum_le_sum fun x (_ : x∈Finset.univ) => hpoint x
  have heq : (∑ x,p.prob x*((if BadX x then 1 else 0)+b))=pcaFiniteMass p BadX+b := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [← FinDist.expect,← pcaFiniteMass_indicator,← Finset.sum_mul,p.sum_one,one_mul]
  calc
    _ ≤ _ := hsum
    _ = pcaFiniteMass p BadX+b := heq
    _ ≤ a+b := add_le_add hfirst (le_refl b)

attribute [-instance] pcaPropDecision

/-- For a decidable predicate, finite event mass is the sum of probabilities over the filtered
universal finite set. -/
theorem pcaFiniteMass_eq {X : Type} [Fintype X] (p : FinDist X) (P : X→Prop) [DecidablePred P] :
    pcaFiniteMass p P=∑x∈Finset.univ.filter P,p.prob x := by
  unfold pcaFiniteMass
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter]
  · intro x _
    rfl

/-- An event on one coordinate of an independent product law has the same mass as under that
coordinate's marginal law. -/
theorem pca_independent_coordinate {k : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (laws : Fin k→FinDist X) (i : Fin k) (Bad : X→Prop) :
    pcaFiniteMass (independentSampleLaw laws) (fun z => Bad (z i))=pcaFiniteMass (laws i) Bad := by
  rw [pcaFiniteMass_indicator,pcaFiniteMass_indicator]
  exact independentSampleLaw_expect_coord laws i (fun x => if Bad x then 1 else 0)

/-- If every coordinate failure has mass at most `b`, the mass of any coordinate failure in the
independent product is at most `k * b`. -/
theorem pca_independent_union {k : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (laws : Fin k→FinDist X) (Bad : Fin k→X→Prop) (b : ℝ)
    (h : ∀ i,pcaFiniteMass (laws i) (Bad i)≤b) :
    pcaFiniteMass (independentSampleLaw laws) (fun z => ∃i,Bad i (z i))≤(k:ℝ)*b := by
  have hu := fintype_union_bound_mass (independentSampleLaw laws).prob
    (independentSampleLaw laws).nonneg (fun (i : Fin k) (z : Fin k→X) => Bad i (z i))
  have hfirst : pcaFiniteMass (independentSampleLaw laws) (fun z => ∃i,Bad i (z i)) =
      ∑ω∈Finset.univ.filter (fun z => ∃i,Bad i (z i)),(independentSampleLaw laws).prob ω :=
    pcaFiniteMass_eq _ _
  rw [← hfirst] at hu
  calc
    _ ≤ ∑ i,pcaFiniteMass (independentSampleLaw laws) (fun z => Bad i (z i))  := by
      simpa only [pcaFiniteMass_eq] using! hu
    _ = ∑ i,pcaFiniteMass (laws i) (Bad i) := by simp_rw [pca_independent_coordinate]
    _ ≤ ∑ _ : Fin k,b := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

end Qatlib.Papers.QPCAAssume18.ClassicalPca
