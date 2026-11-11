/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.GroupedPairStatistics
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics
import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.RationalPiEnclosure
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor
import Mathlib.Data.List.AList
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Born Current Records

Born Current Records constructions and identities for Spinor Sampling.
-/
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Model

-- Coordinates of z - i*y*w for z,w in C^2, with y a Pauli-Y outcome.
/-- Complete original `y_record_squared_norm` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem y_record_squared_norm (a b c d e f g k y : ℝ)
    (hz : a^2+b^2+c^2+d^2=1)
    (hw : e^2+f^2+g^2+k^2=1)
    (hy : y^2=1) :
    (a+y*f)^2+(b-y*e)^2+(c+y*k)^2+(d-y*g)^2 =
      2+2*y*(a*f-b*e+c*k-d*g) := by
  linear_combination hz + y^2*hw + hy

/-- Complete original `y_record_pair_mass` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem y_record_pair_mass (J M : ℝ) (hM : M ≠ 0) :
    (2+2*J)/(4*M)+(2-2*J)/(4*M)=1/M := by
  field_simp
  ring

/-- Complete original `y_record_pair_signed_mass` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem y_record_pair_signed_mass (J M : ℝ) (hM : M ≠ 0) :
    (2+2*J)/(4*M)-(2-2*J)/(4*M)=J/M := by
  field_simp
  ring

-- This is the source spin (Z,-Y,X), not a different spin normalization.
/-- Complete original `source_spin_squared_norm` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem source_spin_squared_norm (a b c d : ℝ) :
    (a^2+b^2-c^2-d^2)^2 + (2*(c*b-a*d))^2 + (2*(a*c+b*d))^2 =
      (a^2+b^2+c^2+d^2)^2 := by
  ring

/-- Complete original `source_spin_unit` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem source_spin_unit (a b c d : ℝ) (hz : a^2+b^2+c^2+d^2=1) :
    (a^2+b^2-c^2-d^2)^2 + (2*(c*b-a*d))^2 + (2*(a*c+b*d))^2 = 1 := by
  rw [source_spin_squared_norm, hz]
  norm_num

/-- Complete original `unit_spin_distance` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem unit_spin_distance (u v w p q r : ℝ)
    (hs : u^2+v^2+w^2=1) (ht : p^2+q^2+r^2=1) :
    (u-p)^2+(v-q)^2+(w-r)^2 = 2-2*(u*p+v*q+w*r) := by
  linear_combination hs + ht

/-- Complete original `central_spin_energy` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem central_spin_energy (u v w p q r h : ℝ) (hh : h ≠ 0)
    (hs : u^2+v^2+w^2=1) (ht : p^2+q^2+r^2=1) :
    ((u-p)/(2*h))^2+((v-q)/(2*h))^2+((w-r)/(2*h))^2 =
      (1-(u*p+v*q+w*r))/(2*h^2) := by
  calc
    _ = ((u-p)^2+(v-q)^2+(w-r)^2)/(2*h)^2 := by
      simp only [div_pow]
      ring
    _ = _ := by
      rw [unit_spin_distance u v w p q r hs ht]
      field_simp

/-- Construction for int Bit in the born current records model. -/
def intBit (a : Bool) : ℤ := a.toNat

-- The diagonal phase of the 7-T CCX expansion, between its two target H gates.
/-- Complete original `toffoli_phase_polynomial` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem toffoli_phase_polynomial (a b t : Bool) :
    intBit a + intBit b + intBit t - intBit (Bool.xor a b) -
      intBit (Bool.xor a t) - intBit (Bool.xor b t) +
      intBit (Bool.xor a (Bool.xor b t)) =
      4*intBit a*intBit b*intBit t := by
  cases a <;> cases b <;> cases t <;> decide

#print axioms Qatlib.Concepts.SpinorSampling.Model.y_record_squared_norm
#print axioms Qatlib.Concepts.SpinorSampling.Model.y_record_pair_mass
#print axioms Qatlib.Concepts.SpinorSampling.Model.y_record_pair_signed_mass
#print axioms Qatlib.Concepts.SpinorSampling.Model.source_spin_squared_norm
#print axioms Qatlib.Concepts.SpinorSampling.Model.source_spin_unit
#print axioms Qatlib.Concepts.SpinorSampling.Model.unit_spin_distance
#print axioms Qatlib.Concepts.SpinorSampling.Model.central_spin_energy
#print axioms Qatlib.Concepts.SpinorSampling.Model.toffoli_phase_polynomial

/-- Complete original `normalized_inner_im_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem normalized_inner_im_bound (a b c d e f g k : ℝ)
    (hz : a^2+b^2+c^2+d^2=1) (hw : e^2+f^2+g^2+k^2=1) :
    |a*f-b*e+c*k-d*g| ≤ 1 := by
  have hp : 0 ≤ 2+2*(a*f-b*e+c*k-d*g) := by
    have h := y_record_squared_norm a b c d e f g k 1 hz hw (by norm_num)
    have hs : 0 ≤ (a+1*f)^2+(b-1*e)^2+(c+1*k)^2+(d-1*g)^2 := by
      positivity
    linarith
  have hn : 0 ≤ 2-2*(a*f-b*e+c*k-d*g) := by
    have h := y_record_squared_norm a b c d e f g k (-1) hz hw (by norm_num)
    have hs : 0 ≤ (a+(-1)*f)^2+(b-(-1)*e)^2+(c+(-1)*k)^2+(d-(-1)*g)^2 := by
      positivity
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Complete original `central_record_mean_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem central_record_mean_bound (p n : ℝ) (hp : |p| ≤ 1) (hn : |n| ≤ 1) :
    |(p-n)/2| ≤ 1 := by
  rw [abs_le] at hp hn ⊢
  constructor <;> linarith

/-- Complete original `fair_neighbor_mixture` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem fair_neighbor_mixture (p n q M : ℝ) (hM : M ≠ 0) :
    ((1+q*p)/(2*M)+(1-q*n)/(2*M))/2 =
      (1+q*((p-n)/2))/(2*M) := by
  field_simp
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.normalized_inner_im_bound
#print axioms Qatlib.Concepts.SpinorSampling.Model.central_record_mean_bound
#print axioms Qatlib.Concepts.SpinorSampling.Model.fair_neighbor_mixture

export Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.SignedCollisionStatistics (recordSign signedRecordWeight signed_record_cell_mass signedRecordLaw signed_record_cell_mean residualCollision residual_collision_projection residual_collision_unbiased)
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
export Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.GroupedPairStatistics (groupedRecordSum groupedRecordSquares grouped_product_fiber grouped_square_expansion grouped_squares_mass collision_streaming_numerator velocity_streaming_statistic)
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
export Qatlib.Concepts.MonteCarloMean.FinDistBounds.ReceivedStats.GroupedPairStatistics (groupedRecordCount shifted_product_fiber grouped_shift_expansion grouped_fixed_count spin_streaming_numerator ordered_offdiag_swap ordered_symmetrization)
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Complete original `residual_streaming_consumer` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_consumer {n : ℕ} (r : Fin n → S × Bool)
    (u : S → ℝ) (α β : ℝ) :
    let J := fun i => (r i).1
    let z := fun i => α*recordSign (r i).2-β*u (r i).1
    (Fintype.card S : ℝ)/(n*(n-1) : ℕ) *
      (∑ x : S, ((groupedRecordSum J z x)^2-groupedRecordSquares J z x)) =
      (∑ i : Fin n, ∑ j : Fin n,
        if i ≠ j then residualCollision α β u (r i) (r j) else 0)/(n*(n-1) : ℕ) := by
  dsimp only
  rw [velocity_streaming_statistic]
  have hkernel (i j : Fin n) :
      (if i ≠ j then residualCollision α β u (r i) (r j) else 0) =
      (Fintype.card S : ℝ) *
        (if i ≠ j ∧ (r i).1=(r j).1 then
          (α*recordSign (r i).2-β*u (r i).1)*(α*recordSign (r j).2-β*u (r j).1)
          else 0) := by
    by_cases hij : i=j
    · subst j
      simp
    · by_cases hsite : (r i).1=(r j).1 <;>
        simp [hij, hsite, residualCollision, mul_assoc]
  simp_rw [hkernel]
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Construction for shifted Spin Collision in the born current records model. -/
def shiftedSpinCollision (τ : S → S) (l r : S × Bool) : ℝ :=
  (Fintype.card S : ℝ)/2 *
    ((if r.1=τ l.1 then 1 else 0)+(if l.1=τ r.1 then 1 else 0))*
    recordSign l.2*recordSign r.2

/-- Complete original `spin_streaming_consumer` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_consumer {n : ℕ} (r : Fin n → S × Bool) (τ : S → S) :
    let J := fun i => (r i).1
    let z := fun i => recordSign (r i).2
    (Fintype.card S : ℝ)/(n*(n-1) : ℕ) *
      (∑ x : S, (groupedRecordSum J z x*groupedRecordSum J z (τ x) -
        if τ x=x then groupedRecordCount J x else 0)) =
      (∑ i : Fin n, ∑ j : Fin n,
        if i ≠ j then shiftedSpinCollision τ (r i) (r j) else 0)/(n*(n-1) : ℕ) := by
  dsimp only
  have hz (i : Fin n) : (recordSign (r i).2)^2=1 := by
    cases (r i).2 <;> simp [recordSign]
  rw [spin_streaming_numerator (fun i => (r i).1) (fun i => recordSign (r i).2) τ hz]
  let f := fun i j : Fin n =>
    if (r j).1=τ (r i).1 then recordSign (r i).2*recordSign (r j).2 else 0
  have hkernel (i j : Fin n) :
      (if i ≠ j then shiftedSpinCollision τ (r i) (r j) else 0) =
      (Fintype.card S : ℝ)*(if i ≠ j then (f i j+f j i)/2 else 0) := by
    dsimp only [shiftedSpinCollision, f]
    split_ifs <;> ring
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n,
        if i ≠ j then shiftedSpinCollision τ (r i) (r j) else 0) =
      (Fintype.card S : ℝ)*(∑ i : Fin n, ∑ j : Fin n, if i ≠ j then f i j else 0) := by
    calc
      _ = (Fintype.card S : ℝ)*
          (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then (f i j+f j i)/2 else 0) := by
        simp_rw [hkernel]
        simp only [Finset.mul_sum]
      _ = _ := by rw [ordered_symmetrization]
  have hmask (i j : Fin n) :
      (if i ≠ j then f i j else 0) =
      (if i ≠ j ∧ (r j).1=τ (r i).1 then recordSign (r i).2*recordSign (r j).2 else 0) := by
    by_cases hij : i=j <;> simp [f, hij]
  rw [hsum]
  simp_rw [hmask]
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_streaming_consumer
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_streaming_consumer
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Complete original `expect_distinct_coordinate_product` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem expect_distinct_coordinate_product {n : ℕ} (p : FinDist X)
    (i j : Fin n) (hij : i ≠ j) (f g : X → ℝ) :
    (∑ ω : Fin n → X, p.probOf ω*f (ω i)*g (ω j)) = p.expect f*p.expect g := by
  let q := fun k : Fin n => fun x : X =>
    if k=i then f x else if k=j then g x else 1
  have hprod (ω : Fin n → X) : (∏ k, q k (ω k)) = f (ω i)*g (ω j) := by
    rw [← Finset.prod_subset (Finset.subset_univ (insert i {j}))
      (fun k _ hk => by
        have hi : k ≠ i := by intro h; apply hk; simp [h]
        have hj : k ≠ j := by intro h; apply hk; simp [h]
        simp [q, hi, hj]),
      Finset.prod_insert (Finset.notMem_singleton.mpr hij), Finset.prod_singleton]
    simp [q, Ne.symm hij]
  have hright : (∏ k : Fin n, (∑ x : X, p.prob x*q k x)) = p.expect f*p.expect g := by
    rw [← Finset.prod_subset (Finset.subset_univ (insert i {j}))
      (fun k _ hk => by
        have hi : k ≠ i := by intro h; apply hk; simp [h]
        have hj : k ≠ j := by intro h; apply hk; simp [h]
        simpa [q, hi, hj] using p.sum_one),
      Finset.prod_insert (Finset.notMem_singleton.mpr hij), Finset.prod_singleton]
    simp [q, Ne.symm hij, FinDist.expect]
  calc
    _ = ∑ ω : Fin n → X, p.probOf ω * ∏ k, q k (ω k) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [hprod]
      ring
    _ = ∏ k : Fin n, (∑ x : X, p.prob x*q k x) := p.expect_prod q
    _ = _ := hright


/-- Complete original `expect_two_coordinates` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem expect_two_coordinates {n : ℕ} (p : FinDist X)
    (i j : Fin n) (hij : i ≠ j) (H : X → X → ℝ) :
    (∑ ω : Fin n → X, p.probOf ω*H (ω i) (ω j)) =
      p.expect (fun x => p.expect (H x)) := by
  have hexpand (ω : Fin n → X) :
      H (ω i) (ω j) = ∑ y : X, H (ω i) y*(if ω j=y then 1 else 0) := by
    simp [mul_ite]
  calc
    _ = ∑ ω : Fin n → X, p.probOf ω*
        (∑ y : X, H (ω i) y*(if ω j=y then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [← hexpand]
    _ = ∑ y : X, ∑ ω : Fin n → X,
        p.probOf ω*H (ω i) y*(if ω j=y then 1 else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = ∑ y : X, p.expect (fun x => H x y)*p.prob y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [expect_distinct_coordinate_product p i j hij (fun x => H x y) (fun x => if x=y then 1 else 0)]
      simp [FinDist.expect, mul_ite]
    _ = _ := by
      unfold FinDist.expect
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.expect_distinct_coordinate_product
#print axioms Qatlib.Concepts.SpinorSampling.Model.expect_two_coordinates
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Construction for ordered UStatistic in the born current records model. -/
def orderedUStatistic {n : ℕ} (H : X → X → ℝ) (ω : Fin n → X) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then H (ω i) (ω j) else 0))/(n*(n-1) : ℕ)

/-- Complete original `ordered_ustatistic_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ordered_ustatistic_unbiased {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hn : 2 ≤ n) :
    (∑ ω : Fin n → X, p.probOf ω*orderedUStatistic H ω) =
      p.expect (fun x => p.expect (H x)) := by
  let μ := p.expect (fun x => p.expect (H x))
  have hterm (i j : Fin n) :
      (∑ ω : Fin n → X, p.probOf ω*(if i ≠ j then H (ω i) (ω j) else 0)) =
      if i ≠ j then μ else 0 := by
    by_cases hij : i=j
    · subst j
      simp
    · simp only [ite_eq_left hij]
      exact expect_two_coordinates p i j hij H
  have hinner (i : Fin n) :
      (∑ j : Fin n, if i ≠ j then μ else 0) = (n : ℝ)*μ-μ := by
    have hsplit (j : Fin n) :
        (if i ≠ j then μ else 0) = μ-(if i=j then μ else 0) := by
      by_cases hij : i=j <;> simp [hij]
    simp_rw [hsplit, Finset.sum_sub_distrib]
    simp [nsmul_eq_mul]
  have hcount : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then μ else 0) =
      ((n*(n-1) : ℕ) : ℝ)*μ := by
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hD : (((n*(n-1) : ℕ) : ℝ)) ≠ 0 := by
    have hN : n ≠ 0 := by omega
    have hP : n-1 ≠ 0 := by omega
    exact_mod_cast Nat.mul_ne_zero hN hP
  calc
    _ = (∑ ω : Fin n → X, p.probOf ω *
        (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then H (ω i) (ω j) else 0))/(n*(n-1) : ℕ) := by
      unfold orderedUStatistic
      simp only [Finset.sum_div, mul_div_assoc]
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ ω : Fin n → X,
        p.probOf ω*(if i ≠ j then H (ω i) (ω j) else 0))/(n*(n-1) : ℕ) := by
      apply congrArg (fun a : ℝ => a/(n*(n-1) : ℕ))
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then μ else 0)/(n*(n-1) : ℕ) := by
      simp_rw [hterm]
    _ = μ := by
      rw [hcount]
      exact mul_div_cancel_left₀ μ hD

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `residual_all_samples_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_all_samples_unbiased {n : ℕ} (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hn : 2 ≤ n) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω *
      orderedUStatistic (residualCollision α β u) ω) =
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) := by
  rw [ordered_ustatistic_unbiased (signedRecordLaw m hm) (residualCollision α β u) hn]
  exact residual_collision_unbiased m u α β hm

#print axioms Qatlib.Concepts.SpinorSampling.Model.ordered_ustatistic_unbiased
#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_all_samples_unbiased
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for oriented Spin Collision in the born current records model. -/
def orientedSpinCollision (τ : S → S) (l r : S × Bool) : ℝ :=
  if r.1=τ l.1 then (Fintype.card S : ℝ)*recordSign l.2*recordSign r.2 else 0

/-- Complete original `oriented_spin_projection` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem oriented_spin_projection (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (τ : S → S) (l : S × Bool) :
    (signedRecordLaw m hm).expect (fun r => orientedSpinCollision τ l r) =
      recordSign l.2*m (τ l.1) := by
  change (∑ r : S × Bool, signedRecordWeight m r*orientedSpinCollision τ l r) = _
  rw [Fintype.sum_prod_type]
  have hcell (x : S) :
      (∑ b : Bool, signedRecordWeight m (x,b)*recordSign b) = m x/(Fintype.card S : ℝ) := by
    simpa only [one_mul, zero_mul, sub_zero] using
      (signed_record_cell_mean m (fun _ => 0) 1 0 x)
  have hsite (x : S) :
      (∑ b : Bool, signedRecordWeight m (x,b)*orientedSpinCollision τ l (x,b)) =
      if x=τ l.1 then recordSign l.2*m (τ l.1) else 0 := by
    by_cases hx : x=τ l.1
    · subst x
      simp only [orientedSpinCollision, ite_true]
      calc
        _ = (Fintype.card S : ℝ)*recordSign l.2 *
            (∑ b : Bool, signedRecordWeight m (τ l.1,b)*recordSign b) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          rw [hcell]
          have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
          field_simp
    · simp [orientedSpinCollision, hx]
  simp_rw [hsite]
  simp

/-- Complete original `oriented_spin_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem oriented_spin_unbiased (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (τ : S → S) :
    (signedRecordLaw m hm).expect (fun l =>
      (signedRecordLaw m hm).expect (fun r => orientedSpinCollision τ l r)) =
      (∑ x : S, m x*m (τ x))/(Fintype.card S : ℝ) := by
  change (∑ l : S × Bool, signedRecordWeight m l *
    (signedRecordLaw m hm).expect (fun r => orientedSpinCollision τ l r)) = _
  simp_rw [oriented_spin_projection]
  rw [Fintype.sum_prod_type]
  have hsite (x : S) :
      (∑ b : Bool, signedRecordWeight m (x,b)*(recordSign b*m (τ x))) =
      m x*m (τ x)/(Fintype.card S : ℝ) := by
    have hcell : (∑ b : Bool, signedRecordWeight m (x,b)*recordSign b) =
        m x/(Fintype.card S : ℝ) := by
      simpa only [one_mul, zero_mul, sub_zero] using
        (signed_record_cell_mean m (fun _ => 0) 1 0 x)
    calc
      _ = (∑ b : Bool, signedRecordWeight m (x,b)*recordSign b)*m (τ x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [hcell]; ring
  simpa only [Finset.sum_div] using (Finset.sum_congr rfl fun x _ => hsite x)

/-- Complete original `spin_collision_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_collision_unbiased (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (τ : S → S) :
    (signedRecordLaw m hm).expect (fun l =>
      (signedRecordLaw m hm).expect (fun r => shiftedSpinCollision τ l r)) =
      (∑ x : S, m x*m (τ x))/(Fintype.card S : ℝ) := by
  let p := signedRecordLaw m hm
  let H := orientedSpinCollision τ
  have hpoint (l r : S × Bool) : shiftedSpinCollision τ l r = (H l r+H r l)/2 := by
    dsimp only [shiftedSpinCollision, H, orientedSpinCollision]
    split_ifs <;> ring
  have hswap : p.expect (fun l => p.expect (fun r => H r l)) =
      p.expect (fun l => p.expect (fun r => H l r)) := by
    unfold FinDist.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hdiv (f : S × Bool → ℝ) : p.expect (fun x => f x/2) = p.expect f/2 := by
    unfold FinDist.expect
    simp only [mul_div_assoc, Finset.sum_div]
  have hadd (f g : S × Bool → ℝ) : p.expect (fun x => f x+g x) = p.expect f+p.expect g := by
    unfold FinDist.expect
    simp only [mul_add, Finset.sum_add_distrib]
  change p.expect (fun l => p.expect (fun r => shiftedSpinCollision τ l r)) = _
  simp_rw [hpoint, hdiv, hadd]
  rw [hswap]
  have hmean := oriented_spin_unbiased m hm τ
  change p.expect (fun l => p.expect (fun r => H l r)) = _ at hmean
  rw [hmean]
  ring

/-- Complete original `spin_all_samples_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_all_samples_unbiased {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (τ : S → S) (hn : 2 ≤ n) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω *
      orderedUStatistic (shiftedSpinCollision τ) ω) =
      (∑ x : S, m x*m (τ x))/(Fintype.card S : ℝ) := by
  rw [ordered_ustatistic_unbiased (signedRecordLaw m hm) (shiftedSpinCollision τ) hn]
  exact spin_collision_unbiased m hm τ

#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_collision_unbiased
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_all_samples_unbiased
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Complete original `product_expect_cons` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem product_expect_cons {n : ℕ} (p : FinDist X) (F : (Fin (n+1) → X) → ℝ) :
    (∑ ω : Fin (n+1) → X, p.probOf ω*F ω) =
      ∑ x : X, p.prob x*(∑ η : Fin n → X, p.probOf η*F (Fin.cons x η)) := by
  unfold FinDist.probOf
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro η _
  dsimp [Fin.consEquiv]
  ring

-- Conditional cancellation is later discharged from the centered kernel;
-- it is not a variance/success certificate supplied to an SCWF estimator.
omit [DecidableEq X] in
/-- Complete original `product_conditional_zero` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem product_conditional_zero (p : FinDist X) :
    ∀ (n : ℕ) (k : Fin n) (F : (Fin n → X) → ℝ),
      (∀ ω, (∑ x : X, p.prob x*F (Function.update ω k x))=0) →
      (∑ ω : Fin n → X, p.probOf ω*F ω)=0 := by
  have hset : (Finset.univ : Finset X).Nonempty := by
    by_contra h
    have he : (Finset.univ : Finset X)=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hs := p.sum_one
    rw [he, Finset.sum_empty] at hs
    norm_num at hs
  obtain ⟨x0, _⟩ := hset
  intro n
  induction n with
  | zero => intro k; exact Fin.elim0 k
  | succ n ih =>
    intro k F hzero
    cases k using Fin.cases with
    | zero =>
      have hupdate (x y : X) (η : Fin n → X) :
          Function.update (Fin.cons x η : Fin (n+1) → X) (0 : Fin (n+1)) y = Fin.cons y η := by
        funext i
        cases i using Fin.cases <;> simp
      have hinner (η : Fin n → X) : (∑ x : X, p.prob x*F (Fin.cons x η))=0 := by
        simpa only [hupdate] using (hzero (Fin.cons x0 η))
      rw [product_expect_cons]
      calc
        _ = ∑ η : Fin n → X, p.probOf η*(∑ x : X, p.prob x*F (Fin.cons x η)) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro η _
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = 0 := by simp_rw [hinner]; simp
    | succ k =>
      have hupdate (x y : X) (η : Fin n → X) :
          Function.update (Fin.cons x η : Fin (n+1) → X) k.succ y = Fin.cons x (Function.update η k y) := by
        funext i
        cases i using Fin.cases with
        | zero =>
          rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero k))]
          rfl
        | succ i =>
          by_cases hi : i=k
          · subst i
            rw [Function.update_self, Fin.cons_succ, Function.update_self]
          · have hi' : i.succ ≠ k.succ := by simpa using hi
            simp only [Function.update_of_ne hi', Fin.cons_succ, Function.update_of_ne hi]
      have hinner (x : X) :
          (∑ η : Fin n → X, p.probOf η*F (Fin.cons x η))=0 := by
        apply ih k (fun η => F (Fin.cons x η))
        intro η
        simpa only [hupdate] using (hzero (Fin.cons x η))
      rw [product_expect_cons]
      simp_rw [hinner]
      simp

#print axioms Qatlib.Concepts.SpinorSampling.Model.product_conditional_zero
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Construction for pair Kernel Mean in the born current records model. -/
def pairKernelMean (p : FinDist X) (H : X → X → ℝ) : ℝ :=
  p.expect (fun x => p.expect (H x))

/-- Construction for pair Kernel Projection in the born current records model. -/
def pairKernelProjection (p : FinDist X) (H : X → X → ℝ) (x : X) : ℝ :=
  p.expect (H x)

/-- Construction for centered Pair Kernel in the born current records model. -/
def centeredPairKernel (p : FinDist X) (H : X → X → ℝ) (x y : X) : ℝ :=
  H x y-pairKernelProjection p H x-pairKernelProjection p H y+pairKernelMean p H

omit [DecidableEq X] in
/-- Complete original `centered_pair_conditional_zero` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_pair_conditional_zero (p : FinDist X) (H : X → X → ℝ) (x : X) :
    p.expect (fun y => centeredPairKernel p H x y)=0 := by
  let g := pairKernelProjection p H
  let μ := pairKernelMean p H
  change p.expect (fun y => H x y-g x-g y+μ)=0
  have hc (c : ℝ) : p.expect (fun _ => c)=c := by
    unfold FinDist.expect
    rw [← Finset.sum_mul, p.sum_one, one_mul]
  calc
    _ = p.expect (H x)-p.expect (fun _ => g x)-p.expect g+p.expect (fun _ => μ) := by
      unfold FinDist.expect
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = 0 := by
      rw [hc, hc]
      change g x-g x-μ+μ=0
      ring

omit [DecidableEq X] in
/-- Complete original `centered_pair_symmetric` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_pair_symmetric (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (x y : X) :
    centeredPairKernel p H x y=centeredPairKernel p H y x := by
  unfold centeredPairKernel
  rw [hH x y]
  ring

omit [DecidableEq X] in
/-- Complete original `centered_pair_unique_endpoint_cancel` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_pair_unique_endpoint_cancel {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (i j k l : Fin n) (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    (∑ ω : Fin n → X, p.probOf ω *
      (centeredPairKernel p H (ω i) (ω j)*centeredPairKernel p H (ω k) (ω l)))=0 := by
  apply product_conditional_zero p n l
  intro ω
  simp only [Function.update_of_ne (Ne.symm hli), Function.update_of_ne (Ne.symm hlj),
    Function.update_of_ne (Ne.symm hlk), Function.update_self]
  have hzero := centered_pair_conditional_zero p H (ω k)
  change (∑ x : X, p.prob x*centeredPairKernel p H (ω k) x)=0 at hzero
  calc
    _ = centeredPairKernel p H (ω i) (ω j)*
        (∑ x : X, p.prob x*centeredPairKernel p H (ω k) x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [hzero]; ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.centered_pair_conditional_zero
#print axioms Qatlib.Concepts.SpinorSampling.Model.centered_pair_unique_endpoint_cancel
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Complete original `centered_pair_distinct_edges_cancel` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_pair_distinct_edges_cancel {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (i j k l : Fin n) (hkl : k ≠ l)
    (hsame : ¬(i=k ∧ j=l)) (hreverse : ¬(i=l ∧ j=k)) :
    (∑ ω : Fin n → X, p.probOf ω *
      (centeredPairKernel p H (ω i) (ω j)*centeredPairKernel p H (ω k) (ω l)))=0 := by
  have hswap :
      (∑ ω : Fin n → X, p.probOf ω *
        (centeredPairKernel p H (ω i) (ω j)*centeredPairKernel p H (ω k) (ω l))) =
      (∑ ω : Fin n → X, p.probOf ω *
        (centeredPairKernel p H (ω i) (ω j)*centeredPairKernel p H (ω l) (ω k))) := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [centered_pair_symmetric p H hH (ω k) (ω l)]
  by_cases hli : l=i
  · have hki : k ≠ i := by
      intro h
      exact hkl (h.trans hli.symm)
    have hkj : k ≠ j := by
      intro h
      exact hreverse ⟨hli.symm, h.symm⟩
    rw [hswap]
    exact centered_pair_unique_endpoint_cancel p H i j l k hki hkj hkl
  · by_cases hlj : l=j
    · have hkj : k ≠ j := by
        intro h
        exact hkl (h.trans hlj.symm)
      have hki : k ≠ i := by
        intro h
        exact hsame ⟨h.symm, hlj.symm⟩
      rw [hswap]
      exact centered_pair_unique_endpoint_cancel p H i j l k hki hkj hkl
    · exact centered_pair_unique_endpoint_cancel p H i j k l hli hlj (Ne.symm hkl)

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Complete original `residual_kernel_symmetric` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_kernel_symmetric (u : S → ℝ) (α β : ℝ) (l r : S × Bool) :
    residualCollision α β u l r=residualCollision α β u r l := by
  simp only [residualCollision, eq_comm]
  split_ifs <;> ring

/-- Complete original `spin_kernel_symmetric` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_kernel_symmetric (τ : S → S) (l r : S × Bool) :
    shiftedSpinCollision τ l r=shiftedSpinCollision τ r l := by
  unfold shiftedSpinCollision
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.centered_pair_distinct_edges_cancel
#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_kernel_symmetric
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_kernel_symmetric
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Complete original `offdiag_constant_sum` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem offdiag_constant_sum {n : ℕ} (c : ℝ) (hn : 1 ≤ n) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then c else 0) =
      ((n*(n-1) : ℕ) : ℝ)*c := by
  have hinner (i : Fin n) : (∑ j : Fin n, if i ≠ j then c else 0) = (n : ℝ)*c-c := by
    have hs (j : Fin n) : (if i ≠ j then c else 0) = c-(if i=j then c else 0) := by
      by_cases hij : i=j <;> simp [hij]
    simp_rw [hs, Finset.sum_sub_distrib]
    simp [nsmul_eq_mul]
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
  ring

/-- Complete original `centered_pair_edge_row` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_pair_edge_row {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (i j : Fin n) (hij : i ≠ j) :
    (∑ k : Fin n, ∑ l : Fin n, ∑ ω : Fin n → X, p.probOf ω *
      ((if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)*
       (if k ≠ l then centeredPairKernel p H (ω k) (ω l) else 0))) =
      2*p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2)) := by
  let V := p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2))
  have hterm (k l : Fin n) :
      (∑ ω : Fin n → X, p.probOf ω *
        ((if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)*
         (if k ≠ l then centeredPairKernel p H (ω k) (ω l) else 0))) =
      (if k=i ∧ l=j then V else 0)+(if k=j ∧ l=i then V else 0) := by
    by_cases hkl : k=l
    · subst l
      have hki : ¬(k=i ∧ k=j) := by rintro ⟨hi,hj⟩; exact hij (hi.symm.trans hj)
      have hkj : ¬(k=j ∧ k=i) := by rintro ⟨hj,hi⟩; exact hij (hi.symm.trans hj)
      simp only [ne_eq, not_true_eq_false, ite_false, mul_zero, Finset.sum_const_zero,
        ite_eq_right hki, ite_eq_right hkj, add_zero]
    · simp only [ite_eq_left hij, ite_eq_left hkl]
      by_cases hs : k=i ∧ l=j
      · rcases hs with ⟨hki,hlj⟩
        subst k
        subst l
        have hr : ¬(i=j ∧ j=i) := by rintro ⟨h,_⟩; exact hij h
        simp only [and_self, ite_true, ite_eq_right hr, add_zero]
        change (∑ ω : Fin n → X, p.probOf ω*
          (centeredPairKernel p H (ω i) (ω j)*centeredPairKernel p H (ω i) (ω j))) = V
        convert expect_two_coordinates p i j hij
          (fun x y => (centeredPairKernel p H x y)^2) using 1
        simp only [sq]
      · by_cases hr : k=j ∧ l=i
        · rcases hr with ⟨hkj,hli⟩
          subst k
          subst l
          have hs' : ¬(j=i ∧ i=j) := by rintro ⟨h,_⟩; exact hij h.symm
          simp only [ite_eq_right hs', and_self, ite_true, zero_add]
          have hp (ω : Fin n → X) :
              centeredPairKernel p H (ω i) (ω j)*centeredPairKernel p H (ω j) (ω i) =
                (centeredPairKernel p H (ω i) (ω j))^2 := by
            rw [centered_pair_symmetric p H hH (ω j) (ω i)]
            ring
          simp_rw [hp]
          exact expect_two_coordinates p i j hij (fun x y => (centeredPairKernel p H x y)^2)
        · simp only [ite_eq_right hs, ite_eq_right hr, zero_add]
          apply centered_pair_distinct_edges_cancel p H hH i j k l hkl
          · rintro ⟨hi,hj⟩; exact hs ⟨hi.symm,hj.symm⟩
          · rintro ⟨hi,hj⟩; exact hr ⟨hj.symm,hi.symm⟩
  simp_rw [hterm, Finset.sum_add_distrib]
  simp [ite_and]
  ring

/-- Complete original `centered_ustatistic_second_moment` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_ustatistic_second_moment {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (hn : 2 ≤ n) :
    (∑ ω : Fin n → X, p.probOf ω*(orderedUStatistic (centeredPairKernel p H) ω)^2) =
      2*p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2))/
        (n*(n-1) : ℕ) := by
  let D : ℝ := (n*(n-1) : ℕ)
  let V := p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2))
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast Nat.mul_ne_zero (by omega : n ≠ 0) (by omega : n-1 ≠ 0)
  have hsq (ω : Fin n → X) :
      (∑ i : Fin n, ∑ j : Fin n,
        if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)^2 =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ((if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)*
         (if k ≠ l then centeredPairKernel p H (ω k) (ω l) else 0)) := by
    rw [sq]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hrow (i j : Fin n) :
      (∑ k : Fin n, ∑ l : Fin n, ∑ ω : Fin n → X, p.probOf ω *
        ((if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)*
         (if k ≠ l then centeredPairKernel p H (ω k) (ω l) else 0))) =
      if i ≠ j then 2*V else 0 := by
    by_cases hij : i=j
    · subst j; simp
    · rw [ite_eq_left hij]
      exact centered_pair_edge_row p H hH i j hij
  calc
    _ = (∑ ω : Fin n → X, p.probOf ω *
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          ((if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)*
           (if k ≠ l then centeredPairKernel p H (ω k) (ω l) else 0))))/D^2 := by
      simp_rw [orderedUStatistic, div_pow, hsq]
      simp only [mul_div_assoc, Finset.sum_div, D]
    _ = (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        ∑ ω : Fin n → X, p.probOf ω *
          ((if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)*
           (if k ≠ l then centeredPairKernel p H (ω k) (ω l) else 0)))/D^2 := by
      apply congrArg (fun a : ℝ => a/D^2)
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then 2*V else 0)/D^2 := by
      simp_rw [hrow]
    _ = D*(2*V)/D^2 := by rw [offdiag_constant_sum (2*V) (by omega : 1 ≤ n)]
    _ = _ := by change D*(2*V)/D^2=2*V/D; field_simp

#print axioms Qatlib.Concepts.SpinorSampling.Model.centered_ustatistic_second_moment
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Complete original `offdiag_left_sum` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem offdiag_left_sum {n : ℕ} (f : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then f i else 0) =
      ((n : ℝ)-1)*(∑ i : Fin n, f i) := by
  have hinner (i : Fin n) :
      (∑ j : Fin n, if i ≠ j then f i else 0) = ((n : ℝ)-1)*f i := by
    have hs (j : Fin n) : (if i ≠ j then f i else 0)=f i-(if i=j then f i else 0) := by
      by_cases hij : i=j <;> simp [hij]
    simp_rw [hs, Finset.sum_sub_distrib]
    simp [nsmul_eq_mul, sub_mul]
  simp_rw [hinner]
  rw [Finset.mul_sum]

omit [DecidableEq X] in
/-- Complete original `ordered_ustatistic_decomposition` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ordered_ustatistic_decomposition {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (ω : Fin n → X) (hn : 2 ≤ n) :
    orderedUStatistic H ω-pairKernelMean p H =
      2*(FinDist.avg (pairKernelProjection p H) ω-pairKernelMean p H)+
        orderedUStatistic (centeredPairKernel p H) ω := by
  let g := pairKernelProjection p H
  let μ := pairKernelMean p H
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then H (ω i) (ω j) else 0)-
        2*((n : ℝ)-1)*(∑ i : Fin n, g (ω i))+((n*(n-1) : ℕ) : ℝ)*μ := by
    have hpoint (i j : Fin n) :
        (if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0) =
        (if i ≠ j then H (ω i) (ω j) else 0)-
        (if i ≠ j then g (ω i) else 0)-
        (if i ≠ j then g (ω j) else 0)+(if i ≠ j then μ else 0) := by
      by_cases hij : i=j
      · subst j; simp
      · simp only [ite_eq_left hij, centeredPairKernel, g, μ]
    simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [offdiag_left_sum, Finset.sum_comm (f := fun i j : Fin n => if i ≠ j then g (ω j) else 0)]
    have hr : (∑ j : Fin n, ∑ i : Fin n, if i ≠ j then g (ω j) else 0) =
        ((n : ℝ)-1)*(∑ j : Fin n, g (ω j)) := by
      simp_rw [ne_comm]
      exact offdiag_left_sum (fun j => g (ω j))
    rw [hr, offdiag_constant_sum μ (by omega : 1 ≤ n)]
    ring
  change orderedUStatistic H ω-μ=2*(FinDist.avg g ω-μ)+orderedUStatistic (centeredPairKernel p H) ω
  unfold orderedUStatistic FinDist.avg
  rw [hsum, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp
  ring

omit [DecidableEq X] in
/-- Complete original `linear_centered_pair_cancel` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem linear_centered_pair_cancel {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (f : X → ℝ) (c : ℝ)
    (k i j : Fin n) (hij : i ≠ j) :
    (∑ ω : Fin n → X, p.probOf ω *
      ((f (ω k)-c)*centeredPairKernel p H (ω i) (ω j)))=0 := by
  have hright (a b : Fin n) (hba : b ≠ a) (hbk : b ≠ k) :
      (∑ ω : Fin n → X, p.probOf ω *
        ((f (ω k)-c)*centeredPairKernel p H (ω a) (ω b)))=0 := by
    apply product_conditional_zero p n b
    intro ω
    simp only [Function.update_of_ne (Ne.symm hba), Function.update_of_ne (Ne.symm hbk),
      Function.update_self]
    have hzero := centered_pair_conditional_zero p H (ω a)
    change (∑ x : X, p.prob x*centeredPairKernel p H (ω a) x)=0 at hzero
    calc
      _ = (f (ω k)-c)*(∑ x : X, p.prob x*centeredPairKernel p H (ω a) x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hzero]; ring
  by_cases hjk : j=k
  · have hik : i ≠ k := by simpa only [← hjk] using hij
    have hswap (ω : Fin n → X) :
        centeredPairKernel p H (ω i) (ω j)=centeredPairKernel p H (ω j) (ω i) :=
      centered_pair_symmetric p H hH (ω i) (ω j)
    simp_rw [hswap]
    exact hright j i hij hik
  · exact hright i j (Ne.symm hij) hjk

#print axioms Qatlib.Concepts.SpinorSampling.Model.ordered_ustatistic_decomposition
#print axioms Qatlib.Concepts.SpinorSampling.Model.linear_centered_pair_cancel
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Complete original `linear_centered_ustatistic_orthogonal` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem linear_centered_ustatistic_orthogonal {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (f : X → ℝ) (c : ℝ) (hn : 2 ≤ n) :
    (∑ ω : Fin n → X, p.probOf ω *
      ((FinDist.avg f ω-c)*orderedUStatistic (centeredPairKernel p H) ω))=0 := by
  let D : ℝ := (n*(n-1) : ℕ)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have havg (ω : Fin n → X) : FinDist.avg f ω-c=(∑ k : Fin n, (f (ω k)-c))/(n : ℝ) := by
    unfold FinDist.avg
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hpoint (ω : Fin n → X) :
      (FinDist.avg f ω-c)*orderedUStatistic (centeredPairKernel p H) ω =
      (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        (f (ω k)-c)*(if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0))/((n : ℝ)*D) := by
    rw [havg]
    unfold orderedUStatistic
    rw [div_mul_div_comm]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rfl
  have hterm (k i j : Fin n) :
      (∑ ω : Fin n → X, p.probOf ω *
        ((f (ω k)-c)*(if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)))=0 := by
    by_cases hij : i=j
    · subst j; simp
    · simp only [ite_eq_left hij]
      exact linear_centered_pair_cancel p H hH f c k i j hij
  calc
    _ = (∑ ω : Fin n → X, p.probOf ω *
        (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          (f (ω k)-c)*(if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)))/((n : ℝ)*D) := by
      simp_rw [hpoint]
      simp only [mul_div_assoc, Finset.sum_div]
    _ = (∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ ω : Fin n → X, p.probOf ω *
        ((f (ω k)-c)*(if i ≠ j then centeredPairKernel p H (ω i) (ω j) else 0)))/((n : ℝ)*D) := by
      apply congrArg (fun a : ℝ => a/((n : ℝ)*D))
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = 0 := by simp_rw [hterm]; simp

/-- Complete original `ordered_ustatistic_hoeffding_variance` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ordered_ustatistic_hoeffding_variance {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (hn : 2 ≤ n) :
    (∑ ω : Fin n → X, p.probOf ω*(orderedUStatistic H ω-pairKernelMean p H)^2) =
      4*p.variance (pairKernelProjection p H)/(n : ℝ)+
      2*p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2))/
        (n*(n-1) : ℕ) := by
  let g := pairKernelProjection p H
  let μ := pairKernelMean p H
  have hpoly (ω : Fin n → X) :
      p.probOf ω*(orderedUStatistic H ω-μ)^2 =
      4*(p.probOf ω*(FinDist.avg g ω-μ)^2)+
      4*(p.probOf ω*((FinDist.avg g ω-μ)*orderedUStatistic (centeredPairKernel p H) ω))+
      p.probOf ω*(orderedUStatistic (centeredPairKernel p H) ω)^2 := by
    rw [ordered_ustatistic_decomposition p H ω hn]
    ring
  have hμ : μ=p.expect g := rfl
  change (∑ ω : Fin n → X, p.probOf ω*(orderedUStatistic H ω-μ)^2)=_
  simp_rw [hpoly, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [linear_centered_ustatistic_orthogonal p H hH g μ hn,
    centered_ustatistic_second_moment p H hH hn, hμ,
    p.expect_avg_sub_sq g (by omega : 0 < n)]
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.linear_centered_ustatistic_orthogonal
#print axioms Qatlib.Concepts.SpinorSampling.Model.ordered_ustatistic_hoeffding_variance
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Complete original `centered_pair_second_moment` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem centered_pair_second_moment (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) :
    p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2)) =
      p.expect (fun x => p.expect (fun y => (H x y-pairKernelMean p H)^2))-
        2*p.variance (pairKernelProjection p H) := by
  let g := pairKernelProjection p H
  let μ := pairKernelMean p H
  let V := p.expect (fun x => (g x-μ)^2)
  have hc (c : ℝ) : p.expect (fun _ => c)=c := by
    unfold FinDist.expect
    rw [← Finset.sum_mul, p.sum_one, one_mul]
  have ha (f k : X → ℝ) : p.expect (fun x => f x+k x)=p.expect f+p.expect k := by
    simp only [FinDist.expect, mul_add, Finset.sum_add_distrib]
  have hs (f k : X → ℝ) : p.expect (fun x => f x-k x)=p.expect f-p.expect k := by
    simp only [FinDist.expect, mul_sub, Finset.sum_sub_distrib]
  have hm (c : ℝ) (f : X → ℝ) : p.expect (fun x => c*f x)=c*p.expect f := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hswap (F : X → X → ℝ) :
      p.expect (fun x => p.expect (F x))=p.expect (fun x => p.expect (fun y => F y x)) := by
    unfold FinDist.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hcross :
      p.expect (fun x => p.expect (fun y => (g x-μ)*(H x y-μ)))=V := by
    have hi (x : X) : p.expect (fun y => (g x-μ)*(H x y-μ))=(g x-μ)^2 := by
      rw [hm, hs, hc]
      change (g x-μ)*(g x-μ)=(g x-μ)^2
      ring
    simp_rw [hi]
    rfl
  have hcross' :
      p.expect (fun x => p.expect (fun y => (g y-μ)*(H x y-μ)))=V := by
    rw [hswap]
    have hp (x y : X) : (g x-μ)*(H y x-μ)=(g x-μ)*(H x y-μ) := by rw [hH y x]
    simp_rw [hp]
    exact hcross
  have hzero : p.expect (fun x => g x-μ)=0 := p.sum_sub_mean g
  have hproduct : p.expect (fun x => p.expect (fun y => (g x-μ)*(g y-μ)))=0 := by
    simp_rw [hm, hzero, mul_zero]
    exact hc 0
  have hpoly (x y : X) :
      (centeredPairKernel p H x y)^2 =
      (H x y-μ)^2+(g x-μ)^2+(g y-μ)^2-
      2*((g x-μ)*(H x y-μ))-2*((g y-μ)*(H x y-μ))+2*((g x-μ)*(g y-μ)) := by
    unfold centeredPairKernel
    change (H x y-g x-g y+μ)^2=_
    ring
  have hleft : p.expect (fun x => p.expect (fun _ => (g x-μ)^2))=V := by
    simp_rw [hc]
    rfl
  have hright : p.expect (fun _ => p.expect (fun y => (g y-μ)^2))=V := hc V
  change p.expect (fun x => p.expect (fun y => (centeredPairKernel p H x y)^2))=
    p.expect (fun x => p.expect (fun y => (H x y-μ)^2))-2*V
  simp_rw [hpoly]
  simp only [ha, hs, hm 2]
  rw [hleft, hright, hcross, hcross', hproduct]
  ring

/-- Complete original `ordered_ustatistic_variance` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ordered_ustatistic_variance {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (hn : 2 ≤ n) :
    (∑ ω : Fin n → X, p.probOf ω*(orderedUStatistic H ω-pairKernelMean p H)^2) =
      4*((n : ℝ)-2)/(n*(n-1) : ℕ)*p.variance (pairKernelProjection p H)+
      2/(n*(n-1) : ℕ)*p.expect (fun x => p.expect (fun y => (H x y-pairKernelMean p H)^2)) := by
  rw [ordered_ustatistic_hoeffding_variance p H hH hn, centered_pair_second_moment p H hH]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.centered_pair_second_moment
#print axioms Qatlib.Concepts.SpinorSampling.Model.ordered_ustatistic_variance
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for residual Streaming Statistic in the born current records model. -/
def residualStreamingStatistic {n : ℕ} (u : S → ℝ) (α β : ℝ) (r : Fin n → S × Bool) : ℝ :=
  let J := fun i => (r i).1
  let z := fun i => α*recordSign (r i).2-β*u (r i).1
  (Fintype.card S : ℝ)/(n*(n-1) : ℕ) *
    (∑ x : S, ((groupedRecordSum J z x)^2-groupedRecordSquares J z x))

/-- Construction for spin Streaming Statistic in the born current records model. -/
def spinStreamingStatistic {n : ℕ} (τ : S → S) (r : Fin n → S × Bool) : ℝ :=
  let J := fun i => (r i).1
  let z := fun i => recordSign (r i).2
  (Fintype.card S : ℝ)/(n*(n-1) : ℕ) *
    (∑ x : S, (groupedRecordSum J z x*groupedRecordSum J z (τ x) -
      if τ x=x then groupedRecordCount J x else 0))

omit [Nonempty S] in
/-- Complete original `residual_streaming_eq_ordered` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_eq_ordered {n : ℕ} (u : S → ℝ) (α β : ℝ) (r : Fin n → S × Bool) :
    residualStreamingStatistic u α β r=orderedUStatistic (residualCollision α β u) r :=
  residual_streaming_consumer r u α β

omit [Nonempty S] in
/-- Complete original `spin_streaming_eq_ordered` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_eq_ordered {n : ℕ} (τ : S → S) (r : Fin n → S × Bool) :
    spinStreamingStatistic τ r=orderedUStatistic (shiftedSpinCollision τ) r :=
  spin_streaming_consumer r τ

/-- Complete original `residual_streaming_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_unbiased {n : ℕ} (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hn : 2 ≤ n) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*residualStreamingStatistic u α β ω) =
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) := by
  simp_rw [residual_streaming_eq_ordered]
  exact residual_all_samples_unbiased m u α β hm hn

/-- Complete original `spin_streaming_unbiased` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_unbiased {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (τ : S → S) (hn : 2 ≤ n) :
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*spinStreamingStatistic τ ω) =
      (∑ x : S, m x*m (τ x))/(Fintype.card S : ℝ) := by
  simp_rw [spin_streaming_eq_ordered]
  exact spin_all_samples_unbiased m hm τ hn

/-- Complete original `residual_streaming_variance` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_variance {n : ℕ} (m u : S → ℝ) (α β : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hn : 2 ≤ n) :
    let p := signedRecordLaw m hm
    let H := residualCollision α β u
    let L := (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)
    (∑ ω : Fin n → S × Bool, p.probOf ω*(residualStreamingStatistic u α β ω-L)^2) =
      4*((n : ℝ)-2)/(n*(n-1) : ℕ)*p.variance (pairKernelProjection p H)+
      2/(n*(n-1) : ℕ)*p.expect (fun x => p.expect (fun y => (H x y-L)^2)) := by
  dsimp only
  have hmean : pairKernelMean (signedRecordLaw m hm) (residualCollision α β u) =
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) :=
    residual_collision_unbiased m u α β hm
  simp_rw [residual_streaming_eq_ordered]
  rw [← hmean]
  exact ordered_ustatistic_variance (signedRecordLaw m hm) (residualCollision α β u)
    (residual_kernel_symmetric u α β) hn

/-- Complete original `spin_streaming_variance` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_variance {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (τ : S → S) (hn : 2 ≤ n) :
    let p := signedRecordLaw m hm
    let H := shiftedSpinCollision τ
    let C := (∑ x : S, m x*m (τ x))/(Fintype.card S : ℝ)
    (∑ ω : Fin n → S × Bool, p.probOf ω*(spinStreamingStatistic τ ω-C)^2) =
      4*((n : ℝ)-2)/(n*(n-1) : ℕ)*p.variance (pairKernelProjection p H)+
      2/(n*(n-1) : ℕ)*p.expect (fun x => p.expect (fun y => (H x y-C)^2)) := by
  dsimp only
  have hmean : pairKernelMean (signedRecordLaw m hm) (shiftedSpinCollision τ) =
      (∑ x : S, m x*m (τ x))/(Fintype.card S : ℝ) :=
    spin_collision_unbiased m hm τ
  simp_rw [spin_streaming_eq_ordered]
  rw [← hmean]
  exact ordered_ustatistic_variance (signedRecordLaw m hm) (shiftedSpinCollision τ)
    (spin_kernel_symmetric τ) hn

#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_streaming_unbiased
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_streaming_unbiased
#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_streaming_variance
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_streaming_variance
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X]

/-- Complete original `finite_expect_const` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_const (p : FinDist X) (c : ℝ) : p.expect (fun _ => c)=c := by
  unfold FinDist.expect
  rw [← Finset.sum_mul, p.sum_one, one_mul]

/-- Complete original `finite_expect_add` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_add (p : FinDist X) (f g : X → ℝ) :
    p.expect (fun x => f x+g x)=p.expect f+p.expect g := by
  simp only [FinDist.expect, mul_add, Finset.sum_add_distrib]

/-- Complete original `finite_expect_sub` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_sub (p : FinDist X) (f g : X → ℝ) :
    p.expect (fun x => f x-g x)=p.expect f-p.expect g := by
  simp only [FinDist.expect, mul_sub, Finset.sum_sub_distrib]

/-- Complete original `finite_expect_mul` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_mul (p : FinDist X) (c : ℝ) (f : X → ℝ) :
    p.expect (fun x => c*f x)=c*p.expect f := by
  unfold FinDist.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Complete original `finite_expect_mono` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_mono (p : FinDist X) (f g : X → ℝ) (hfg : ∀ x, f x ≤ g x) :
    p.expect f ≤ p.expect g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (p.nonneg x)

/-- Complete original `finite_expect_nonneg` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_nonneg (p : FinDist X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ p.expect f := Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hf x)

/-- Complete original `finite_variance_identity` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_variance_identity (p : FinDist X) (f : X → ℝ) :
    p.variance f=p.expect (fun x => (f x)^2)-(p.expect f)^2 := by
  have hpoly (x : X) : (f x-p.expect f)^2=(f x)^2-2*p.expect f*f x+(p.expect f)^2 := by ring
  unfold FinDist.variance
  simp_rw [hpoly]
  simp only [finite_expect_add, finite_expect_sub, finite_expect_mul, finite_expect_const]
  ring

/-- Complete original `finite_variance_le_second` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_variance_le_second (p : FinDist X) (f : X → ℝ) :
    p.variance f ≤ p.expect (fun x => (f x)^2) := by
  rw [finite_variance_identity]
  exact sub_le_self _ (sq_nonneg _)

/-- Complete original `pair_variance_identity` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pair_variance_identity (p : FinDist X) (H : X → X → ℝ) :
    p.expect (fun x => p.expect (fun y => (H x y-pairKernelMean p H)^2)) =
      p.expect (fun x => p.expect (fun y => (H x y)^2))-(pairKernelMean p H)^2 := by
  let μ := pairKernelMean p H
  have hpoly (x y : X) : (H x y-μ)^2=(H x y)^2-2*μ*H x y+μ^2 := by ring
  change p.expect (fun x => p.expect (fun y => (H x y-μ)^2))=_
  simp_rw [hpoly]
  simp only [finite_expect_add, finite_expect_sub, finite_expect_mul, finite_expect_const]
  change p.expect (fun x => p.expect (fun y => (H x y)^2))-2*μ*μ+μ^2=_
  ring

/-- Complete original `pair_variance_le_second` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pair_variance_le_second (p : FinDist X) (H : X → X → ℝ) :
    p.expect (fun x => p.expect (fun y => (H x y-pairKernelMean p H)^2)) ≤
      p.expect (fun x => p.expect (fun y => (H x y)^2)) := by
  rw [pair_variance_identity]
  exact sub_le_self _ (sq_nonneg _)

/-- Complete original `record_sign_abs` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_sign_abs (b : Bool) : |recordSign b|=1 := by cases b <;> norm_num [recordSign]

/-- Complete original `scaled_residual_abs` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem scaled_residual_abs (α β U x y : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : |x| ≤ 1) (hy : |y| ≤ U) : |α*x-β*y| ≤ α+β*U := by
  calc
    _ ≤ |α*x|+|β*y| := abs_sub _ _
    _ = α* |x|+β* |y| := by rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
    _ ≤ α+β*U := by nlinarith

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

omit [DecidableEq S] in
/-- Complete original `signed_record_site_expect` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem signed_record_site_expect (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (f : S → ℝ) :
    (signedRecordLaw m hm).expect (fun r => f r.1)=(∑ x : S, f x)/(Fintype.card S : ℝ) := by
  change (∑ r : S × Bool, signedRecordWeight m r*f r.1)=_
  rw [Fintype.sum_prod_type]
  have hcell (x : S) : (∑ b : Bool, signedRecordWeight m (x,b)*f x) = f x/(Fintype.card S : ℝ) := by
    rw [← Finset.sum_mul, signed_record_cell_mass]
    ring
  simp_rw [hcell]
  exact (Finset.sum_div _ _ _).symm

/-- Complete original `residual_projection_second_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_projection_second_bound (m u : S → ℝ) (α β U : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (signedRecordLaw m hm).expect (fun l =>
      (pairKernelProjection (signedRecordLaw m hm) (residualCollision α β u) l)^2) ≤
      (α+β*U)^2*((∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)) := by
  let p := signedRecordLaw m hm
  have hbound (l : S × Bool) :
      (pairKernelProjection p (residualCollision α β u) l)^2 ≤
        (α+β*U)^2*(α*m l.1-β*u l.1)^2 := by
    have hz := scaled_residual_abs α β U (recordSign l.2) (u l.1) hα hβ
      (le_of_eq (record_sign_abs l.2)) (hu l.1)
    have hz2 : (α*recordSign l.2-β*u l.1)^2 ≤ (α+β*U)^2 :=
      sq_le_sq.mpr (hz.trans (le_abs_self _))
    change (p.expect (fun r => residualCollision α β u l r))^2 ≤ _
    rw [residual_collision_projection, mul_pow]
    exact mul_le_mul_of_nonneg_right hz2 (sq_nonneg _)
  calc
    _ ≤ p.expect (fun l => (α+β*U)^2*(α*m l.1-β*u l.1)^2) :=
      finite_expect_mono p _ _ hbound
    _ = _ := by
      dsimp only [p]
      rw [finite_expect_mul, signed_record_site_expect m hm (fun x => (α*m x-β*u x)^2)]

/-- Complete original `residual_projection_variance_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_projection_variance_bound (m u : S → ℝ) (α β U : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (signedRecordLaw m hm).variance (pairKernelProjection (signedRecordLaw m hm) (residualCollision α β u)) ≤
      (α+β*U)^2*((∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)) :=
  (finite_variance_le_second _ _).trans (residual_projection_second_bound m u α β U hm hu hα hβ)

#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_projection_variance_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `residual_kernel_second_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_kernel_second_bound (m u : S → ℝ) (α β U : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (signedRecordLaw m hm).expect (fun l => (signedRecordLaw m hm).expect
      (fun r => (residualCollision α β u l r)^2)) ≤ (Fintype.card S : ℝ)*(α+β*U)^4 := by
  let p := signedRecordLaw m hm
  let A := α+β*U
  let M : ℝ := Fintype.card S
  have hM : M ≠ 0 := by dsimp [M]; exact_mod_cast Fintype.card_ne_zero
  have hz (l : S × Bool) : (α*recordSign l.2-β*u l.1)^2 ≤ A^2 :=
    sq_le_sq.mpr ((scaled_residual_abs α β U (recordSign l.2) (u l.1) hα hβ
      (le_of_eq (record_sign_abs l.2)) (hu l.1)).trans (le_abs_self _))
  have hpoint (l r : S × Bool) :
      (residualCollision α β u l r)^2 ≤ M^2*A^4*(if r.1=l.1 then 1 else 0) := by
    by_cases hsite : l.1=r.1
    · rw [residualCollision, ite_eq_left hsite, ite_eq_left hsite.symm, mul_one]
      calc
        _ = M^2*((α*recordSign l.2-β*u l.1)^2*(α*recordSign r.2-β*u r.1)^2) := by dsimp [M]; ring
        _ ≤ M^2*(A^2*A^2) := mul_le_mul_of_nonneg_left
          (mul_le_mul (hz l) (hz r) (sq_nonneg _) (sq_nonneg _)) (sq_nonneg M)
        _ = _ := by ring
    · simp only [residualCollision, ite_eq_right hsite, ite_eq_right (Ne.symm hsite), zero_pow (by decide : 2 ≠ 0), mul_zero]
      rfl
  have hrow (l : S × Bool) :
      p.expect (fun r => M^2*A^4*(if r.1=l.1 then 1 else 0))=M*A^4 := by
    rw [finite_expect_mul]
    have hsite : p.expect (fun r => if r.1=l.1 then (1 : ℝ) else 0)=1/M := by
      dsimp only [p]
      rw [signed_record_site_expect m hm (fun x => if x=l.1 then (1 : ℝ) else 0)]
      simp [M]
    rw [hsite]
    field_simp
  calc
    _ ≤ p.expect (fun l => p.expect (fun r => M^2*A^4*(if r.1=l.1 then 1 else 0))) :=
      finite_expect_mono p _ _ (fun l => finite_expect_mono p _ _ (hpoint l))
    _ = M*A^4 := by simp_rw [hrow]; exact finite_expect_const p _

omit [DecidableEq S] in
/-- Complete original `residual_mean_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_mean_bound (m u : S → ℝ) (α β U : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) ≤ (α+β*U)^2 := by
  rw [← signed_record_site_expect m hm (fun x => (α*m x-β*u x)^2)]
  calc
    _ ≤ (signedRecordLaw m hm).expect (fun _ => (α+β*U)^2) :=
      finite_expect_mono _ _ _ (fun r => sq_le_sq.mpr
        ((scaled_residual_abs α β U (m r.1) (u r.1) hα hβ (hm r.1) (hu r.1)).trans (le_abs_self _)))
    _ = _ := finite_expect_const _ _

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Complete original `ordered_ustatistic_variance_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ordered_ustatistic_variance_bound {n : ℕ} (p : FinDist X) (H : X → X → ℝ)
    (hH : ∀ x y, H x y=H y x) (hn : 2 ≤ n) (B D : ℝ) (hB : 0 ≤ B)
    (hg : p.variance (pairKernelProjection p H) ≤ B)
    (hD : p.expect (fun x => p.expect (fun y => (H x y)^2)) ≤ D) :
    (∑ ω : Fin n → X, p.probOf ω*(orderedUStatistic H ω-pairKernelMean p H)^2) ≤
      4*B/(n : ℝ)+2*D/(n*(n-1) : ℕ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnD : (0 : ℝ) < ((n*(n-1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n-1)
  have hc0 : 0 ≤ 4*((n : ℝ)-2)/(n*(n-1) : ℕ) := div_nonneg (by linarith) hnD.le
  have hc : 4*((n : ℝ)-2)/(n*(n-1) : ℕ) ≤ 4/(n : ℝ) := by
    rw [div_le_div_iff₀ hnD hn0, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    nlinarith
  rw [ordered_ustatistic_variance p H hH hn]
  calc
    _ ≤ (4*((n : ℝ)-2)/(n*(n-1) : ℕ))*B+(2/(n*(n-1) : ℕ))*D :=
      add_le_add (mul_le_mul_of_nonneg_left hg hc0)
        (mul_le_mul_of_nonneg_left ((pair_variance_le_second p H).trans hD) (by positivity))
    _ ≤ (4/(n : ℝ))*B+(2/(n*(n-1) : ℕ))*D :=
      add_le_add (mul_le_mul_of_nonneg_right hc hB) le_rfl
    _ = _ := by ring

/-- Complete original `residual_streaming_variance_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_variance_bound {n : ℕ} (m u : S → ℝ) (α β U : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hn : 2 ≤ n) :
    let L := (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*(residualStreamingStatistic u α β ω-L)^2) ≤
      4*(α+β*U)^4/(n : ℝ)+2*(Fintype.card S : ℝ)*(α+β*U)^4/(n*(n-1) : ℕ) := by
  dsimp only
  have hg := residual_projection_variance_bound m u α β U hm hu hα hβ
  have hL := residual_mean_bound m u α β U hm hu hα hβ
  have hg' : (signedRecordLaw m hm).variance
      (pairKernelProjection (signedRecordLaw m hm) (residualCollision α β u)) ≤ (α+β*U)^4 := by
    calc
      _ ≤ (α+β*U)^2*((∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)) := hg
      _ ≤ (α+β*U)^2*(α+β*U)^2 := mul_le_mul_of_nonneg_left hL (sq_nonneg _)
      _ = _ := by ring
  have hmean : pairKernelMean (signedRecordLaw m hm) (residualCollision α β u) =
      (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ) := residual_collision_unbiased m u α β hm
  simp_rw [residual_streaming_eq_ordered]
  rw [← hmean]
  convert ordered_ustatistic_variance_bound (signedRecordLaw m hm) (residualCollision α β u)
    (residual_kernel_symmetric u α β) hn ((α+β*U)^4) ((Fintype.card S : ℝ)*(α+β*U)^4)
    (by positivity) hg' (residual_kernel_second_bound m u α β U hm hu hα hβ) using 1
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_kernel_second_bound
#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_streaming_variance_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X]

/-- Complete original `finite_pair_expect_swap` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_pair_expect_swap (p : FinDist X) (F : X → X → ℝ) :
    p.expect (fun x => p.expect (F x))=p.expect (fun x => p.expect (fun y => F y x)) := by
  unfold FinDist.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `spin_projection_equiv` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_projection_equiv (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (e : S ≃ S) (l : S × Bool) :
    pairKernelProjection (signedRecordLaw m hm) (shiftedSpinCollision e) l =
      recordSign l.2*(m (e l.1)+m (e.symm l.1))/2 := by
  have hpoint (r : S × Bool) : shiftedSpinCollision e l r =
      (1/2 : ℝ)*(orientedSpinCollision e l r+orientedSpinCollision e.symm l r) := by
    have hi : l.1=e r.1 ↔ r.1=e.symm l.1 := by
      constructor
      · intro h; exact (e.symm_apply_eq.mpr h).symm
      · intro h; exact (e.eq_symm_apply.mp h).symm
    unfold shiftedSpinCollision orientedSpinCollision
    simp only [hi]
    split_ifs <;> ring
  change (signedRecordLaw m hm).expect (fun r => shiftedSpinCollision e l r)=_
  simp_rw [hpoint]
  rw [finite_expect_mul, finite_expect_add, oriented_spin_projection, oriented_spin_projection]
  ring

/-- Complete original `spin_projection_abs_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_projection_abs_bound (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (e : S ≃ S) (l : S × Bool) :
    |pairKernelProjection (signedRecordLaw m hm) (shiftedSpinCollision e) l| ≤ 1 := by
  rw [spin_projection_equiv, abs_div, abs_mul, record_sign_abs]
  rw [abs_two, one_mul]
  have hsum : |m (e l.1)+m (e.symm l.1)| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [hm (e l.1), hm (e.symm l.1)])
  linarith

/-- Complete original `spin_projection_variance_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_projection_variance_bound (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (e : S ≃ S) :
    (signedRecordLaw m hm).variance (pairKernelProjection (signedRecordLaw m hm) (shiftedSpinCollision e)) ≤ 1 := by
  calc
    _ ≤ (signedRecordLaw m hm).expect (fun l =>
        (pairKernelProjection (signedRecordLaw m hm) (shiftedSpinCollision e) l)^2) :=
      finite_variance_le_second _ _
    _ ≤ (signedRecordLaw m hm).expect (fun _ => 1) := finite_expect_mono _ _ _ (fun l => by
      have hsq := sq_le_sq.mpr ((spin_projection_abs_bound m hm e l).trans (le_abs_self (1 : ℝ)))
      simpa only [one_pow] using hsq)
    _ = 1 := finite_expect_const _ _

/-- Complete original `spin_kernel_second_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_kernel_second_bound (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (τ : S → S) :
    (signedRecordLaw m hm).expect (fun l => (signedRecordLaw m hm).expect
      (fun r => (shiftedSpinCollision τ l r)^2)) ≤ (Fintype.card S : ℝ) := by
  let p := signedRecordLaw m hm
  let M : ℝ := Fintype.card S
  let I := fun l r : S × Bool => if r.1=τ l.1 then (1 : ℝ) else 0
  have hM : M ≠ 0 := by dsimp [M]; exact_mod_cast Fintype.card_ne_zero
  have hpoint (l r : S × Bool) :
      (shiftedSpinCollision τ l r)^2 ≤ (M^2/2)*(I l r+I r l) := by
    dsimp only [shiftedSpinCollision, M, I]
    split_ifs <;> cases l.2 <;> cases r.2 <;> norm_num [recordSign] <;> nlinarith [sq_nonneg (Fintype.card S : ℝ)]
  have hrow (l : S × Bool) : p.expect (I l)=1/M := by
    dsimp only [p, I]
    rw [signed_record_site_expect m hm (fun x => if x=τ l.1 then (1 : ℝ) else 0)]
    simp [M]
  have hforward : p.expect (fun l => p.expect (I l))=1/M := by
    simp_rw [hrow]
    exact finite_expect_const p _
  have hreverse : p.expect (fun l => p.expect (fun r => I r l))=1/M := by
    rw [← finite_pair_expect_swap p I]
    exact hforward
  calc
    _ ≤ p.expect (fun l => p.expect (fun r => (M^2/2)*(I l r+I r l))) :=
      finite_expect_mono p _ _ (fun l => finite_expect_mono p _ _ (hpoint l))
    _ = M := by
      simp only [finite_expect_mul, finite_expect_add]
      rw [hforward, hreverse]
      field_simp
      ring

/-- Complete original `spin_streaming_variance_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_variance_bound {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (e : S ≃ S) (hn : 2 ≤ n) :
    let C := (∑ x : S, m x*m (e x))/(Fintype.card S : ℝ)
    (∑ ω : Fin n → S × Bool, (signedRecordLaw m hm).probOf ω*(spinStreamingStatistic e ω-C)^2) ≤
      4/(n : ℝ)+2*(Fintype.card S : ℝ)/(n*(n-1) : ℕ) := by
  dsimp only
  have hmean : pairKernelMean (signedRecordLaw m hm) (shiftedSpinCollision e) =
      (∑ x : S, m x*m (e x))/(Fintype.card S : ℝ) := spin_collision_unbiased m hm e
  simp_rw [spin_streaming_eq_ordered]
  rw [← hmean]
  simpa only [mul_one] using ordered_ustatistic_variance_bound (signedRecordLaw m hm) (shiftedSpinCollision e)
    (spin_kernel_symmetric e) hn 1 (Fintype.card S : ℝ) (by norm_num)
    (spin_projection_variance_bound m hm e) (spin_kernel_second_bound m hm e)

#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_projection_equiv
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_kernel_second_bound
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_streaming_variance_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- Complete original `product_chebyshev` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem product_chebyshev {n : ℕ} (p : FinDist X) (F : (Fin n → X) → ℝ)
    (c ε : ℝ) (hε : 0 < ε) :
    p.probEvent (fun ω : Fin n → X => ε < |F ω-c|) ≤
      (∑ ω : Fin n → X, p.probOf ω*(F ω-c)^2)/ε^2 := by
  have hε2 : (0 : ℝ) < ε^2 := sq_pos_of_pos hε
  have hnn (ω : Fin n → X) : 0 ≤ p.probOf ω := Finset.prod_nonneg fun _ _ => p.nonneg _
  have hstep :
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |F ω-c|), p.probOf ω) ≤
      ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |F ω-c|), p.probOf ω*(F ω-c)^2/ε^2 := by
    apply Finset.sum_le_sum
    intro ω hω
    have hlt := (Finset.mem_filter.mp hω).2
    have hs : ε^2 ≤ (F ω-c)^2 := by
      calc
        _ ≤ |F ω-c|^2 := (sq_le_sq₀ hε.le (abs_nonneg _)).mpr hlt.le
        _ = _ := sq_abs _
    calc
      _ = p.probOf ω*1 := by ring
      _ ≤ p.probOf ω*((F ω-c)^2/ε^2) := mul_le_mul_of_nonneg_left
        ((le_div_iff₀ hε2).mpr (by simpa only [one_mul] using hs)) (hnn ω)
      _ = _ := by ring
  calc
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |F ω-c|),
        p.probOf ω*(F ω-c)^2/ε^2 := hstep
    _ = (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |F ω-c|),
        p.probOf ω*(F ω-c)^2)/ε^2 := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => mul_nonneg (hnn ω) (sq_nonneg _))) hε2.le

/-- Complete original `variance_budget_small` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem variance_budget_small {n : ℕ} (B D ε : ℝ) (hn : 2 ≤ n) (hD : 0 ≤ D)
    (hε : 0 < ε) (hnB : 32*B/ε^2 ≤ (n : ℝ)) (hnD : 8*Real.sqrt D/ε ≤ (n : ℝ)) :
    4*B/(n : ℝ)+2*D/(n*(n-1) : ℕ) ≤ 3*ε^2/16 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnD0 : (0 : ℝ) < ((n*(n-1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n-1)
  have hε2 : (0 : ℝ) < ε^2 := sq_pos_of_pos hε
  have hB' : 32*B ≤ (n : ℝ)*ε^2 := (div_le_iff₀ hε2).mp hnB
  have hfirst : 4*B/(n : ℝ) ≤ ε^2/8 := by
    rw [div_le_iff₀ hn0]
    nlinarith
  have hroot : 8*Real.sqrt D ≤ (n : ℝ)*ε := (div_le_iff₀ hε).mp hnD
  have hsquared : 64*D ≤ (n : ℝ)^2*ε^2 := by
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 8*Real.sqrt D)
      (mul_nonneg hn0.le hε.le)).mpr hroot
    nlinarith [Real.sq_sqrt hD]
  have hden : (n : ℝ)^2/2 ≤ ((n*(n-1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right hden (sq_nonneg ε)
  have hsecond : 2*D/(n*(n-1) : ℕ) ≤ ε^2/16 := by
    rw [div_le_iff₀ hnD0]
    nlinarith
  calc
    _ ≤ ε^2/8+ε^2/16 := add_le_add hfirst hsecond
    _ = _ := by ring

omit [DecidableEq X] in
/-- Complete original `product_block_failure` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem product_block_failure {n : ℕ} (p : FinDist X) (F : (Fin n → X) → ℝ)
    (c B D ε : ℝ) (hn : 2 ≤ n) (hD : 0 ≤ D) (hε : 0 < ε)
    (hvar : (∑ ω : Fin n → X, p.probOf ω*(F ω-c)^2) ≤ 4*B/(n : ℝ)+2*D/(n*(n-1) : ℕ))
    (hnB : 32*B/ε^2 ≤ (n : ℝ)) (hnD : 8*Real.sqrt D/ε ≤ (n : ℝ)) :
    p.probEvent (fun ω : Fin n → X => ε < |F ω-c|) ≤ 3/16 := by
  calc
    _ ≤ (∑ ω : Fin n → X, p.probOf ω*(F ω-c)^2)/ε^2 := product_chebyshev p F c ε hε
    _ ≤ (4*B/(n : ℝ)+2*D/(n*(n-1) : ℕ))/ε^2 := div_le_div_of_nonneg_right hvar (sq_nonneg ε)
    _ ≤ 3/16 := by
      rw [div_le_iff₀ (sq_pos_of_pos hε)]
      convert variance_budget_small B D ε hn hD hε hnB hnD using 1
      ring

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `residual_streaming_block_failure` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_block_failure {n : ℕ} (m u : S → ℝ) (α β U ε : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hn : 2 ≤ n) (hε : 0 < ε) (hnB : 32*(α+β*U)^4/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+β*U)^4)/ε ≤ (n : ℝ)) :
    (signedRecordLaw m hm).probEvent (fun ω : Fin n → S × Bool =>
      ε < |residualStreamingStatistic u α β ω-(∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)|) ≤ 3/16 := by
  apply product_block_failure (signedRecordLaw m hm) (residualStreamingStatistic u α β)
    _ ((α+β*U)^4) ((Fintype.card S : ℝ)*(α+β*U)^4) ε hn (by positivity) hε
  · convert residual_streaming_variance_bound m u α β U hm hu hα hβ hn using 1
    ring
  · exact hnB
  · exact hnD

/-- Complete original `spin_streaming_block_failure` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_block_failure {n : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (e : S ≃ S) (ε : ℝ) (hn : 2 ≤ n) (hε : 0 < ε) (hnB : 32/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt (Fintype.card S : ℝ)/ε ≤ (n : ℝ)) :
    (signedRecordLaw m hm).probEvent (fun ω : Fin n → S × Bool =>
      ε < |spinStreamingStatistic e ω-(∑ x : S, m x*m (e x))/(Fintype.card S : ℝ)|) ≤ 3/16 := by
  apply product_block_failure (signedRecordLaw m hm) (spinStreamingStatistic e)
    _ 1 (Fintype.card S : ℝ) ε hn (by positivity) hε
  · simpa only [mul_one] using spin_streaming_variance_bound m hm e hn
  · simpa only [mul_one] using hnB
  · exact hnD

#print axioms Qatlib.Concepts.SpinorSampling.Model.product_chebyshev
#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_streaming_block_failure
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_streaming_block_failure
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

/-- Construction for modular Translation in the born current records model. -/
def modularTranslation (N : ℕ) (a : ZMod N) : ZMod N ≃ ZMod N where
  toFun x := x+a
  invFun y := y-a
  left_inv x := by simp
  right_inv y := by simp

/-- Construction for modular Double Shift in the born current records model. -/
def modularDoubleShift (N : ℕ) [NeZero N] : Fin N ≃ Fin N :=
  (ZMod.finEquiv N).toEquiv.trans ((modularTranslation N 2).trans (ZMod.finEquiv N).toEquiv.symm)

/-- Complete original `modular_double_shift_apply` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem modular_double_shift_apply (N : ℕ) [NeZero N] (x : Fin N) :
    (ZMod.finEquiv N) (modularDoubleShift N x)=(ZMod.finEquiv N) x+2 := by
  simp [modularDoubleShift, modularTranslation]

/-- Construction for periodic Double Shift in the born current records model. -/
def periodicDoubleShift (d N : ℕ) [NeZero N] (j : Fin d) :
    (Fin d → Fin N) ≃ (Fin d → Fin N) :=
  Equiv.piCongrRight (fun k => if k=j then modularDoubleShift N else Equiv.refl (Fin N))

/-- Complete original `periodic_double_shift_coordinates` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem periodic_double_shift_coordinates (d N : ℕ) [NeZero N] (j k : Fin d) (x : Fin d → Fin N) :
    (ZMod.finEquiv N) (periodicDoubleShift d N j x k)=
      (ZMod.finEquiv N) (x k)+(if k=j then 2 else 0) := by
  by_cases h : k=j
  · simp [periodicDoubleShift, Equiv.piCongrRight, h, modular_double_shift_apply]
  · simp [periodicDoubleShift, Equiv.piCongrRight, h]

/-- Complete original `periodic_grid_card` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem periodic_grid_card (d N : ℕ) : Fintype.card (Fin d → Fin N)=N^d := by simp

/-- Complete original `periodic_spin_block_failure` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem periodic_spin_block_failure {n : ℕ} (d N : ℕ) [NeZero N] (j : Fin d)
    (m : (Fin d → Fin N) → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (ε : ℝ) (hn : 2 ≤ n) (hε : 0 < ε) (hnB : 32/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt ((N^d : ℕ) : ℝ)/ε ≤ (n : ℝ)) :
    (signedRecordLaw m hm).probEvent (fun ω : Fin n → (Fin d → Fin N) × Bool =>
      ε < |spinStreamingStatistic (periodicDoubleShift d N j) ω-
        (∑ x : Fin d → Fin N, m x*m (periodicDoubleShift d N j x))/((N^d : ℕ) : ℝ)|) ≤ 3/16 := by
  have hcard := periodic_grid_card d N
  simpa only [hcard] using spin_streaming_block_failure m hm (periodicDoubleShift d N j) ε hn hε hnB
    (by simpa only [hcard] using hnD)

#print axioms Qatlib.Concepts.SpinorSampling.Model.periodic_double_shift_coordinates
#print axioms Qatlib.Concepts.SpinorSampling.Model.periodic_spin_block_failure
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Construction for raw Block Median in the born current records model. -/
def rawBlockMedian {K : ℕ} (f : X → ℝ) (ω : Fin K → X) : ℝ :=
  ((List.ofFn fun k => f (ω k)).mergeSort (· ≤ ·)).getD (K/2) 0

/-- Construction for finite Bad Mass in the born current records model. -/
def finiteBadMass (p : FinDist X) (f : X → ℝ) (c ε : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => ε < |f x-c|), p.prob x

omit [Fintype X] [DecidableEq X] in
/-- Complete original `raw_median_bad_count` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem raw_median_bad_count {K : ℕ} (f : X → ℝ) (ω : Fin K → X)
    (c ε : ℝ) (hK : 0 < K) (hbad : ε < |rawBlockMedian f ω-c|) :
    K-K/2 ≤ (Finset.univ.filter (fun k => ε < |f (ω k)-c|)).card := by
  let s := (List.ofFn fun k => f (ω k)).mergeSort (· ≤ ·)
  have hperm : s.Perm (List.ofFn fun k => f (ω k)) := List.mergeSort_perm _ _
  have hsorted : s.SortedLE := List.sortedLE_mergeSort
  have hlen : s.length=K := by rw [hperm.length_eq, List.length_ofFn]
  have h := FinDist.sorted_countP_ge_of_median_dev hsorted hlen hK hbad
  rw [List.Perm.countP_eq (fun x => decide (ε < |x-c|)) hperm,
    FinDist.countP_ofFn_eq_card_filter] at h
  exact h

omit [DecidableEq X] in
/-- Complete original `finite_bad_indicator_mean` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_bad_indicator_mean (p : FinDist X) (f : X → ℝ) (c ε : ℝ) :
    p.expect (fun x => if ε < |f x-c| then (1 : ℝ) else 0)=finiteBadMass p f c ε := by
  unfold FinDist.expect finiteBadMass
  rw [Finset.sum_filter]
  simp only [mul_ite, mul_one, mul_zero]

/-- Complete original `finite_median_power_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_median_power_bound {K : ℕ} (p : FinDist X) (f : X → ℝ) (c ε : ℝ)
    (hK : 0 < K) (hbad : finiteBadMass p f c ε ≤ 3/16) :
    p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-c|) ≤ (25/32 : ℝ)^K := by
  let b := fun ω : Fin K → X => (Finset.univ.filter fun k => ε < |f (ω k)-c|).card
  have hnn (ω : Fin K → X) : 0 ≤ p.probOf ω := Finset.prod_nonneg fun _ _ => p.nonneg _
  have hpoint (ω : Fin K → X) :
      (if ε < |rawBlockMedian f ω-c| then (1 : ℝ) else 0) ≤ (4 : ℝ)^(b ω)/(2 : ℝ)^K := by
    by_cases h : ε < |rawBlockMedian f ω-c|
    · rw [ite_eq_left h, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^K), one_mul]
      have hc := raw_median_bad_count f ω c ε hK h
      have hcount : K ≤ 2*b ω := by dsimp [b]; omega
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcount
      simpa only [pow_mul, show (2 : ℝ)^2=4 by norm_num] using hp
    · rw [ite_eq_right h]
      positivity
  have hpow (ω : Fin K → X) : (4 : ℝ)^(b ω)=
      ∏ k : Fin K, if ε < |f (ω k)-c| then (4 : ℝ) else 1 := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  have hfactor : p.expect (fun x => if ε < |f x-c| then (4 : ℝ) else 1) ≤ 25/16 := by
    have hp (x : X) : (if ε < |f x-c| then (4 : ℝ) else 1)=
        1+3*(if ε < |f x-c| then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [hp]
    rw [finite_expect_add, finite_expect_const, finite_expect_mul, finite_bad_indicator_mean]
    linarith
  have hmoment : (∑ ω : Fin K → X, p.probOf ω*(4 : ℝ)^(b ω)) ≤ (25/16 : ℝ)^K := by
    simp_rw [hpow]
    rw [p.expect_prod (fun (_ : Fin K) (x : X) => if ε < |f x-c| then (4 : ℝ) else 1)]
    calc
      _ ≤ ∏ _k : Fin K, (25/16 : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => finite_expect_nonneg p _ (fun x => by split_ifs <;> norm_num)) (fun _ _ => hfactor)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmass : p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-c|) =
      ∑ ω : Fin K → X, p.probOf ω*(if ε < |rawBlockMedian f ω-c| then (1 : ℝ) else 0) := by
    unfold FinDist.probEvent
    rw [Finset.sum_filter]
    simp only [mul_ite, mul_one, mul_zero]
  calc
    _ = ∑ ω : Fin K → X, p.probOf ω*(if ε < |rawBlockMedian f ω-c| then (1 : ℝ) else 0) := hmass
    _ ≤ ∑ ω : Fin K → X, p.probOf ω*((4 : ℝ)^(b ω)/(2 : ℝ)^K) :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpoint ω) (hnn ω)
    _ = (∑ ω : Fin K → X, p.probOf ω*(4 : ℝ)^(b ω))/(2 : ℝ)^K := by
      simp only [mul_div_assoc, Finset.sum_div]
    _ ≤ (25/16 : ℝ)^K/(2 : ℝ)^K := div_le_div_of_nonneg_right hmoment (by positivity)
    _ = (25/32 : ℝ)^K := by rw [← div_pow]; norm_num

/-- Complete original `finite_median_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_median_confidence {K : ℕ} (p : FinDist X) (f : X → ℝ) (c ε ρ : ℝ)
    (hK0 : 0 < K) (hρ : 0 < ρ) (hbad : finiteBadMass p f c ε ≤ 3/16)
    (hK : (128/25 : ℝ)*Real.log (1/ρ) ≤ (K : ℝ)) :
    p.probEvent (fun ω : Fin K → X => ε < |rawBlockMedian f ω-c|) ≤ ρ := by
  have hbase : (25/32 : ℝ) ≤ Real.exp (-25/128 : ℝ) := by
    have h := Real.add_one_le_exp (-25/128 : ℝ)
    linarith
  have hexp : (25/32 : ℝ)^K ≤ Real.exp (-25*(K : ℝ)/128) := by
    calc
      _ ≤ (Real.exp (-25/128 : ℝ))^K := pow_le_pow_left₀ (by norm_num) hbase K
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hlog : -25*(K : ℝ)/128 ≤ Real.log ρ := by
    rw [one_div, Real.log_inv] at hK
    linarith
  exact (finite_median_power_bound p f c ε hK0 hbad).trans
    (hexp.trans ((Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hρ)))

/-- Construction for cohort Law in the born current records model. -/
def cohortLaw (p : FinDist X) (n : ℕ) : FinDist (Fin n → X) where
  prob := p.probOf
  nonneg _ := Finset.prod_nonneg fun _ _ => p.nonneg _
  sum_one := p.sum_probOf n

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `residual_streaming_median_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_streaming_median_confidence {n K : ℕ} (m u : S → ℝ) (α β U ε ρ : ℝ)
    (hm : ∀ x, |m x| ≤ 1) (hu : ∀ x, |u x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hn : 2 ≤ n) (hε : 0 < ε) (hnB : 32*(α+β*U)^4/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+β*U)^4)/ε ≤ (n : ℝ))
    (hK0 : 0 < K) (hρ : 0 < ρ) (hK : (128/25 : ℝ)*Real.log (1/ρ) ≤ (K : ℝ)) :
    (cohortLaw (signedRecordLaw m hm) n).probEvent (fun ω : Fin K → Fin n → S × Bool =>
      ε < |rawBlockMedian (residualStreamingStatistic u α β) ω-
        (∑ x : S, (α*m x-β*u x)^2)/(Fintype.card S : ℝ)|) ≤ ρ := by
  apply finite_median_confidence _ _ _ _ ρ hK0 hρ
  · exact residual_streaming_block_failure m u α β U ε hm hu hα hβ hn hε hnB hnD
  · exact hK

/-- Complete original `spin_streaming_median_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_streaming_median_confidence {n K : ℕ} (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1)
    (e : S ≃ S) (ε ρ : ℝ) (hn : 2 ≤ n) (hε : 0 < ε) (hnB : 32/ε^2 ≤ (n : ℝ))
    (hnD : 8*Real.sqrt (Fintype.card S : ℝ)/ε ≤ (n : ℝ))
    (hK0 : 0 < K) (hρ : 0 < ρ) (hK : (128/25 : ℝ)*Real.log (1/ρ) ≤ (K : ℝ)) :
    (cohortLaw (signedRecordLaw m hm) n).probEvent (fun ω : Fin K → Fin n → S × Bool =>
      ε < |rawBlockMedian (spinStreamingStatistic e) ω-
        (∑ x : S, m x*m (e x))/(Fintype.card S : ℝ)|) ≤ ρ := by
  apply finite_median_confidence _ _ _ _ ρ hK0 hρ
  · exact spin_streaming_block_failure m hm e ε hn hε hnB hnD
  · exact hK

#print axioms Qatlib.Concepts.SpinorSampling.Model.finite_median_power_bound
#print axioms Qatlib.Concepts.SpinorSampling.Model.residual_streaming_median_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_streaming_median_confidence
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {I X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Fintype Y]

omit [DecidableEq X] in
/-- Complete original `sum_family_mass` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sum_family_mass (p : I → FinDist X) :
    (∑ ω : I → X, ∏ i : I, (p i).prob (ω i))=1 := by
  calc
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : I => (Finset.univ : Finset X)),
        ∏ i, (p i).prob (ω i) := Finset.sum_congr rfl (fun _ _ => rfl)
    _ = ∏ i : I, (∑ x : X, (p i).prob x) := (Finset.prod_univ_sum
      (t := fun _ : I => (Finset.univ : Finset X)) (f := fun i x => (p i).prob x)).symm
    _ = 1 := by simp_rw [fun i => (p i).sum_one]; simp

/-- Construction for finite Family Law in the born current records model. -/
def finiteFamilyLaw (p : I → FinDist X) : FinDist (I → X) where
  prob ω := ∏ i : I, (p i).prob (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (p i).nonneg (ω i)
  sum_one := sum_family_mass p

omit [DecidableEq X] in
/-- Complete original `finite_family_expect_product` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_family_expect_product (p : I → FinDist X) (g : I → X → ℝ) :
    (finiteFamilyLaw p).expect (fun ω => ∏ i : I, g i (ω i)) =
      ∏ i : I, (p i).expect (g i) := by
  change (∑ ω : I → X, (∏ i : I, (p i).prob (ω i))*(∏ i : I, g i (ω i)))=_
  simp_rw [← Finset.prod_mul_distrib]
  calc
    _ = ∑ ω ∈ Fintype.piFinset (fun _ : I => (Finset.univ : Finset X)),
        ∏ i : I, (p i).prob (ω i)*g i (ω i) := Finset.sum_congr rfl (fun _ _ => rfl)
    _ = ∏ i : I, (p i).expect (g i) := (Finset.prod_univ_sum
      (t := fun _ : I => (Finset.univ : Finset X)) (f := fun i x => (p i).prob x*g i x)).symm

omit [DecidableEq X] in
/-- Complete original `finite_family_expect_coord` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_family_expect_coord (p : I → FinDist X) (i : I) (f : X → ℝ) :
    (finiteFamilyLaw p).expect (fun ω => f (ω i))=(p i).expect f := by
  let g := fun k : I => fun x : X => if k=i then f x else 1
  have hleft (ω : I → X) : (∏ k : I, g k (ω k))=f (ω i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro k _ hki; simp [g, hki]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  have hright : (∏ k : I, (p k).expect (g k))=(p i).expect f := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro k _ hki; simp only [g, ite_eq_right hki]; exact finite_expect_const (p k) 1
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  calc
    _ = (finiteFamilyLaw p).expect (fun ω => ∏ k : I, g k (ω k)) := by simp_rw [hleft]
    _ = ∏ k : I, (p k).expect (g k) := finite_family_expect_product p g
    _ = _ := hright

omit [DecidableEq X] in
/-- Complete original `finite_family_bad_mass_coord` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_family_bad_mass_coord (p : I → FinDist X) (i : I) (f : X → ℝ) (c ε : ℝ) :
    finiteBadMass (finiteFamilyLaw p) (fun ω => f (ω i)) c ε=finiteBadMass (p i) f c ε := by
  rw [← finite_bad_indicator_mean, ← finite_bad_indicator_mean,
    finite_family_expect_coord p i (fun x => if ε < |f x-c| then (1 : ℝ) else 0)]

/-- Construction for independent Pair Law in the born current records model. -/
def independentPairLaw (p : FinDist X) (q : FinDist Y) : FinDist (X × Y) where
  prob z := p.prob z.1*q.prob z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, q.sum_one, mul_one]
    exact p.sum_one

omit [DecidableEq X] in
/-- Complete original `independent_pair_expect_left` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem independent_pair_expect_left (p : FinDist X) (q : FinDist Y) (f : X → ℝ) :
    (independentPairLaw p q).expect (fun z => f z.1)=p.expect f := by
  change (∑ z : X × Y, (p.prob z.1*q.prob z.2)*f z.1)=_
  rw [Fintype.sum_prod_type]
  have hrow (x : X) : (∑ y : Y, (p.prob x*q.prob y)*f x)=p.prob x*f x := by
    calc
      _ = p.prob x*f x*(∑ y : Y, q.prob y) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
      _ = _ := by rw [q.sum_one, mul_one]
  simp_rw [hrow]
  rfl

omit [DecidableEq X] in
/-- Complete original `independent_pair_expect_right` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem independent_pair_expect_right (p : FinDist X) (q : FinDist Y) (f : Y → ℝ) :
    (independentPairLaw p q).expect (fun z => f z.2)=q.expect f := by
  change (∑ z : X × Y, (p.prob z.1*q.prob z.2)*f z.2)=_
  rw [Fintype.sum_prod_type]
  have hrow (x : X) : (∑ y : Y, (p.prob x*q.prob y)*f y)=p.prob x*q.expect f := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp_rw [hrow]
  rw [← Finset.sum_mul, p.sum_one, one_mul]

omit [DecidableEq X] in
/-- Complete original `independent_pair_bad_mass_left` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem independent_pair_bad_mass_left (p : FinDist X) (q : FinDist Y) (f : X → ℝ) (c ε : ℝ) :
    finiteBadMass (independentPairLaw p q) (fun z => f z.1) c ε=finiteBadMass p f c ε := by
  rw [← finite_bad_indicator_mean, ← finite_bad_indicator_mean,
    independent_pair_expect_left p q (fun x => if ε < |f x-c| then (1 : ℝ) else 0)]

omit [DecidableEq X] in
/-- Complete original `independent_pair_bad_mass_right` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem independent_pair_bad_mass_right (p : FinDist X) (q : FinDist Y) (f : Y → ℝ) (c ε : ℝ) :
    finiteBadMass (independentPairLaw p q) (fun z => f z.2) c ε=finiteBadMass q f c ε := by
  rw [← finite_bad_indicator_mean, ← finite_bad_indicator_mean,
    independent_pair_expect_right p q (fun x => if ε < |f x-c| then (1 : ℝ) else 0)]

#print axioms Qatlib.Concepts.SpinorSampling.Model.finite_family_bad_mass_coord
#print axioms Qatlib.Concepts.SpinorSampling.Model.independent_pair_bad_mass_left
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

omit [DecidableEq I] in
/-- Complete original `finite_expect_sum` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_expect_sum (p : FinDist X) (f : I → X → ℝ) :
    p.expect (fun x => ∑ i : I, f i x)=∑ i : I, p.expect (f i) := by
  unfold FinDist.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq I] in
/-- Complete original `finite_bad_mass_from_components` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_bad_mass_from_components (p : FinDist X) (f : I → X → ℝ)
    (c ε : I → ℝ) (F : X → ℝ) (C E : ℝ)
    (hgood : ∀ x, (∀ i, |f i x-c i| ≤ ε i) → |F x-C| ≤ E) :
    finiteBadMass p F C E ≤ ∑ i : I, finiteBadMass p (f i) (c i) (ε i) := by
  have hpoint (x : X) : (if E < |F x-C| then (1 : ℝ) else 0) ≤
      ∑ i : I, if ε i < |f i x-c i| then (1 : ℝ) else 0 := by
    by_cases h : E < |F x-C|
    · rw [ite_eq_left h]
      have hex : ∃ i, ε i < |f i x-c i| := by
        by_contra! hn
        exact (not_le_of_gt h) (hgood x hn)
      obtain ⟨i,hi⟩ := hex
      calc
        _ = (if ε i < |f i x-c i| then (1 : ℝ) else 0) := by rw [ite_eq_left hi]
        _ ≤ _ := Finset.single_le_sum (f := fun k : I => if ε k < |f k x-c k| then (1 : ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  rw [← finite_bad_indicator_mean]
  calc
    _ ≤ p.expect (fun x => ∑ i : I, if ε i < |f i x-c i| then (1 : ℝ) else 0) :=
      finite_expect_mono p _ _ hpoint
    _ = _ := by rw [finite_expect_sum]; simp_rw [finite_bad_indicator_mean]

/-- Construction for interval Clip in the born current records model. -/
def intervalClip (lo hi x : ℝ) : ℝ := min hi (max lo x)

/-- Complete original `interval_clip_contract` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem interval_clip_contract (lo hi x c : ℝ) (hlo : lo ≤ c) (hhi : c ≤ hi) :
    |intervalClip lo hi x-c| ≤ |x-c| := by
  have horder : lo ≤ hi := hlo.trans hhi
  by_cases hxl : x ≤ lo
  · rw [intervalClip, max_eq_left hxl, min_eq_right horder,
      abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonpos (sub_nonpos.mpr (hxl.trans hlo))]
    linarith
  · have hlx : lo ≤ x := (lt_of_not_ge hxl).le
    rw [intervalClip, max_eq_right hlx]
    by_cases hxh : hi ≤ x
    · rw [min_eq_left hxh, abs_of_nonneg (sub_nonneg.mpr hhi),
        abs_of_nonneg (sub_nonneg.mpr (hhi.trans hxh))]
      linarith
    · rw [min_eq_right (lt_of_not_ge hxh).le]

/-- Construction for site Mean in the born current records model. -/
def siteMean {S : Type*} [Fintype S] (f : S → ℝ) : ℝ := (∑ x : S, f x)/(Fintype.card S : ℝ)

variable {S : Type*} [Fintype S] [Nonempty S]

omit [Nonempty S] in
/-- Complete original `site_mean_nonneg` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_nonneg (f : S → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ siteMean f :=
  div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

/-- Complete original `site_mean_abs_le_one` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_abs_le_one (f : S → ℝ) (hf : ∀ x, |f x| ≤ 1) : |siteMean f| ≤ 1 := by
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hsum : |∑ x : S, f x| ≤ (Fintype.card S : ℝ) := by
    calc
      _ ≤ ∑ x : S, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : S, (1 : ℝ) := Finset.sum_le_sum fun x _ => hf x
      _ = _ := by simp
  rw [siteMean, abs_div, abs_of_pos hM]
  exact (div_le_one hM).mpr hsum

omit [Fintype S] [Nonempty S] in
/-- Complete original `unit_spin_component_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem unit_spin_component_bound (m : Fin 3 → S → ℝ)
    (hs : ∀ x, ∑ a : Fin 3, (m a x)^2=1) (a : Fin 3) (x : S) : |m a x| ≤ 1 := by
  have hsq : (m a x)^2 ≤ 1 := by
    rw [← hs x]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (m b x)) (Finset.mem_univ a)
  exact abs_le_of_sq_le_sq (by simpa only [one_pow] using hsq) (by norm_num)

omit [Fintype S] [Nonempty S] in
/-- Complete original `unit_spin_dot_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem unit_spin_dot_bound (m : Fin 3 → S → ℝ)
    (hs : ∀ x, ∑ a : Fin 3, (m a x)^2=1) (x y : S) :
    |∑ a : Fin 3, m a x*m a y| ≤ 1 := by
  have hminus : (∑ a : Fin 3, (m a x-m a y)^2)=2-2*(∑ a : Fin 3, m a x*m a y) := by
    have hp (a : Fin 3) : (m a x-m a y)^2=(m a x)^2+(m a y)^2-2*(m a x*m a y) := by ring
    simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hs x, hs y]
    ring
  have hplus : (∑ a : Fin 3, (m a x+m a y)^2)=2+2*(∑ a : Fin 3, m a x*m a y) := by
    have hp (a : Fin 3) : (m a x+m a y)^2=(m a x)^2+(m a y)^2+2*(m a x*m a y) := by ring
    simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hs x, hs y]
    ring
  have hm := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (m a x-m a y))
  have hp := Finset.sum_nonneg (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) => sq_nonneg (m a x+m a y))
  rw [hminus] at hm
  rw [hplus] at hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Complete original `spin_component_mean_range` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_component_mean_range (m : Fin 3 → S → ℝ)
    (hs : ∀ x, ∑ a : Fin 3, (m a x)^2=1) (a : Fin 3) (τ : S → S) :
    |siteMean (fun x => m a x*m a (τ x))| ≤ 1 := by
  apply site_mean_abs_le_one
  intro x
  rw [abs_mul]
  calc
    _ ≤ (1 : ℝ)*1 := mul_le_mul (unit_spin_component_bound m hs a x)
      (unit_spin_component_bound m hs a (τ x)) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Complete original `spin_total_mean_range` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_total_mean_range {d : ℕ} (m : Fin 3 → S → ℝ)
    (hs : ∀ x, ∑ a : Fin 3, (m a x)^2=1) (τ : Fin d → S → S) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, siteMean (fun x => m i.1 x*m i.1 (τ i.2 x)))) ∧
    γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, siteMean (fun x => m i.1 x*m i.1 (τ i.2 x)))) ≤ 2*(d : ℝ)*γ := by
  have hsum : (∑ i : Fin 3 × Fin d, siteMean (fun x => m i.1 x*m i.1 (τ i.2 x))) =
      ∑ j : Fin d, siteMean (fun x => ∑ a : Fin 3, m a x*m a (τ j x)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    unfold siteMean
    simp only [Finset.sum_div]
    exact Finset.sum_comm
  have hbound (j : Fin d) : |siteMean (fun x => ∑ a : Fin 3, m a x*m a (τ j x))| ≤ 1 :=
    site_mean_abs_le_one _ (fun x => unit_spin_dot_bound m hs x (τ j x))
  have habs : |∑ i : Fin 3 × Fin d, siteMean (fun x => m i.1 x*m i.1 (τ i.2 x))| ≤ (d : ℝ) := by
    rw [hsum]
    calc
      _ ≤ ∑ j : Fin d, |siteMean (fun x => ∑ a : Fin 3, m a x*m a (τ j x))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ => hbound j
      _ = _ := by simp
  have hh := abs_le.mp habs
  constructor
  · exact mul_nonneg hγ (by linarith)
  · have hl : (d : ℝ)-(∑ i : Fin 3 × Fin d, siteMean (fun x => m i.1 x*m i.1 (τ i.2 x))) ≤ 2*(d : ℝ) := by linarith [hh.1]
    calc
      _ ≤ γ*(2*(d : ℝ)) := mul_le_mul_of_nonneg_left hl hγ
      _ = _ := by ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.interval_clip_contract
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_total_mean_range
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

/-- Construction for pauli Field in the born current records model. -/
def pauliField {S : Type*} (a b c d : S → ℝ) (i : Fin 3) (x : S) : ℝ :=
  if i=0 then 2*(a x*c x+b x*d x) else
    if i=1 then 2*(a x*d x-b x*c x) else a x^2+b x^2-c x^2-d x^2

/-- Complete original `pauli_field_unit` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pauli_field_unit {S : Type*} (a b c d : S → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+d x^2=1) (x : S) :
    (∑ i : Fin 3, (pauliField a b c d i x)^2)=1 := by
  simp [pauliField, Fin.sum_univ_succ]
  convert source_spin_unit (a x) (b x) (c x) (d x) (hz x) using 1
  ring

variable {I : Type*} [Fintype I]

/-- Complete original `finite_sum_error_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_sum_error_bound (f g : I → ℝ) (ε : ℝ) (h : ∀ i, |f i-g i| ≤ ε) :
    |(∑ i : I, f i)-(∑ i : I, g i)| ≤ (Fintype.card I : ℝ)*ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : I, |f i-g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : I, ε := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp [nsmul_eq_mul]

/-- Construction for combined Loss in the born current records model. -/
def combinedLoss {d : ℕ} (A γ : ℝ) (v : Fin d → ℝ) (c : Fin 3 × Fin d → ℝ) : ℝ :=
  (∑ j : Fin d, intervalClip 0 (A^2) (v j))+
    intervalClip 0 (2*(d : ℝ)*γ) (γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))))

/-- Complete original `combined_loss_error` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem combined_loss_error {d : ℕ} (A γ εv εs : ℝ) (v V : Fin d → ℝ)
    (c C : Fin 3 × Fin d → ℝ) (hγ : 0 ≤ γ)
    (hVrange : ∀ j, 0 ≤ V j ∧ V j ≤ A^2) (hCrange : ∀ i, -1 ≤ C i ∧ C i ≤ 1)
    (hRrange : 0 ≤ γ*((d : ℝ)-(∑ i, C i)) ∧ γ*((d : ℝ)-(∑ i, C i)) ≤ 2*(d : ℝ)*γ)
    (hv : ∀ j, |v j-V j| ≤ εv) (hc : ∀ i, |c i-C i| ≤ εs) :
    |combinedLoss A γ v c-((∑ j, V j)+γ*((d : ℝ)-(∑ i, C i)))| ≤
      (d : ℝ)*εv+3*(d : ℝ)*γ*εs := by
  have hvel : |(∑ j : Fin d, intervalClip 0 (A^2) (v j))-(∑ j, V j)| ≤ (d : ℝ)*εv := by
    simpa only [Fintype.card_fin] using finite_sum_error_bound
      (fun j => intervalClip 0 (A^2) (v j)) V εv
      (fun j => (interval_clip_contract 0 (A^2) (v j) (V j) (hVrange j).1 (hVrange j).2).trans (hv j))
  have hcorr : |(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))-(∑ i, C i)| ≤
      (3 : ℝ)*(d : ℝ)*εs := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] using finite_sum_error_bound
      (fun i => intervalClip (-1) 1 (c i)) C εs
      (fun i => (interval_clip_contract (-1) 1 (c i) (C i) (hCrange i).1 (hCrange i).2).trans (hc i))
  have hspin : |intervalClip 0 (2*(d : ℝ)*γ)
      (γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))))-
      γ*((d : ℝ)-(∑ i, C i))| ≤ 3*(d : ℝ)*γ*εs := by
    calc
      _ ≤ |γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i)))-
          γ*((d : ℝ)-(∑ i, C i))| := interval_clip_contract _ _ _ _ hRrange.1 hRrange.2
      _ = γ* |(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))-(∑ i, C i)| := by
        have hp : γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i)))-γ*((d : ℝ)-(∑ i, C i)) =
            -γ*((∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))-(∑ i, C i)) := by ring
        rw [hp, abs_mul, abs_neg, abs_of_nonneg hγ]
      _ ≤ γ*((3 : ℝ)*(d : ℝ)*εs) := mul_le_mul_of_nonneg_left hcorr hγ
      _ = _ := by ring
  calc
    _ = |((∑ j : Fin d, intervalClip 0 (A^2) (v j))-(∑ j, V j))+
        (intervalClip 0 (2*(d : ℝ)*γ) (γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))))-
          γ*((d : ℝ)-(∑ i, C i)))| := by unfold combinedLoss; congr 1; ring
    _ ≤ |(∑ j : Fin d, intervalClip 0 (A^2) (v j))-(∑ j, V j)|+
        |intervalClip 0 (2*(d : ℝ)*γ) (γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, intervalClip (-1) 1 (c i))))-
          γ*((d : ℝ)-(∑ i, C i))| := abs_add_le _ _
    _ ≤ _ := add_le_add hvel hspin

/-- Complete original `combined_loss_zero` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem combined_loss_zero {d : ℕ} (A : ℝ) (v : Fin d → ℝ) (c : Fin 3 × Fin d → ℝ) :
    combinedLoss A 0 v c=∑ j : Fin d, intervalClip 0 (A^2) (v j) := by simp [combinedLoss, intervalClip]

/-- Complete original `stochastic_error_budget` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem stochastic_error_budget (d : ℕ) (γ η : ℝ) (hd : 0 < d) (hγ : 0 < γ) :
    (d : ℝ)*(η/(4*(d : ℝ)))+3*(d : ℝ)*γ*min 1 (η/(12*(d : ℝ)*γ)) ≤ η/2 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hv : (d : ℝ)*(η/(4*(d : ℝ)))=η/4 := by field_simp
  have hs : 3*(d : ℝ)*γ*min 1 (η/(12*(d : ℝ)*γ)) ≤ η/4 := by
    calc
      _ ≤ 3*(d : ℝ)*γ*(η/(12*(d : ℝ)*γ)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp; ring
  rw [hv]
  linarith

/-- Complete original `stochastic_failure_budget` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem stochastic_failure_budget (d : ℕ) (δ : ℝ) (hd : 0 < d) :
    (d : ℝ)*(δ/(2*(d : ℝ)))+3*(d : ℝ)*(δ/(6*(d : ℝ)))=δ := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.pauli_field_unit
#print axioms Qatlib.Concepts.SpinorSampling.Model.combined_loss_error
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Complete original `combined_loss_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem combined_loss_confidence {d : ℕ} (pV : Fin d → FinDist X)
    (pS : Fin 3 × Fin d → FinDist Y) (fV : Fin d → X → ℝ) (fS : Fin 3 × Fin d → Y → ℝ)
    (V : Fin d → ℝ) (C : Fin 3 × Fin d → ℝ) (A γ εv εs ρv ρs : ℝ) (hγ : 0 ≤ γ)
    (hVrange : ∀ j, 0 ≤ V j ∧ V j ≤ A^2) (hCrange : ∀ i, -1 ≤ C i ∧ C i ≤ 1)
    (hRrange : 0 ≤ γ*((d : ℝ)-(∑ i, C i)) ∧ γ*((d : ℝ)-(∑ i, C i)) ≤ 2*(d : ℝ)*γ)
    (hVbad : ∀ j, finiteBadMass (pV j) (fV j) (V j) εv ≤ ρv)
    (hSbad : ∀ i, finiteBadMass (pS i) (fS i) (C i) εs ≤ ρs) :
    finiteBadMass (independentPairLaw (finiteFamilyLaw pV) (finiteFamilyLaw pS))
      (fun z => combinedLoss A γ (fun j => fV j (z.1 j)) (fun i => fS i (z.2 i)))
      ((∑ j, V j)+γ*((d : ℝ)-(∑ i, C i))) ((d : ℝ)*εv+3*(d : ℝ)*γ*εs) ≤
      (d : ℝ)*ρv+3*(d : ℝ)*ρs := by
  let q := independentPairLaw (finiteFamilyLaw pV) (finiteFamilyLaw pS)
  let f : (Fin d ⊕ (Fin 3 × Fin d)) → ((Fin d → X) × (Fin 3 × Fin d → Y)) → ℝ :=
    Sum.elim (fun j z => fV j (z.1 j)) (fun i z => fS i (z.2 i))
  let centers : (Fin d ⊕ (Fin 3 × Fin d)) → ℝ := Sum.elim V C
  let radii : (Fin d ⊕ (Fin 3 × Fin d)) → ℝ := Sum.elim (fun _ => εv) (fun _ => εs)
  have hpoint (z : (Fin d → X) × (Fin 3 × Fin d → Y))
      (h : ∀ i, |f i z-centers i| ≤ radii i) :
      |combinedLoss A γ (fun j => fV j (z.1 j)) (fun i => fS i (z.2 i))-
        ((∑ j, V j)+γ*((d : ℝ)-(∑ i, C i)))| ≤ (d : ℝ)*εv+3*(d : ℝ)*γ*εs :=
    combined_loss_error A γ εv εs _ V _ C hγ hVrange hCrange hRrange
      (fun j => h (.inl j)) (fun i => h (.inr i))
  have hVmass (j : Fin d) : finiteBadMass q (fun z => fV j (z.1 j)) (V j) εv=
      finiteBadMass (pV j) (fV j) (V j) εv := by
    dsimp only [q]
    rw [independent_pair_bad_mass_left (finiteFamilyLaw pV) (finiteFamilyLaw pS) (fun w : Fin d → X => fV j (w j)) (V j) εv,
      finite_family_bad_mass_coord pV j (fV j) (V j) εv]
  have hSmass (i : Fin 3 × Fin d) : finiteBadMass q (fun z => fS i (z.2 i)) (C i) εs=
      finiteBadMass (pS i) (fS i) (C i) εs := by
    dsimp only [q]
    rw [independent_pair_bad_mass_right (finiteFamilyLaw pV) (finiteFamilyLaw pS) (fun w : Fin 3 × Fin d → Y => fS i (w i)) (C i) εs,
      finite_family_bad_mass_coord pS i (fS i) (C i) εs]
  have hunion := finite_bad_mass_from_components q f centers radii
    (fun z => combinedLoss A γ (fun j => fV j (z.1 j)) (fun i => fS i (z.2 i)))
    ((∑ j, V j)+γ*((d : ℝ)-(∑ i, C i))) ((d : ℝ)*εv+3*(d : ℝ)*γ*εs) hpoint
  calc
    _ ≤ (∑ j : Fin d, finiteBadMass q (fun z => fV j (z.1 j)) (V j) εv)+
        (∑ i : Fin 3 × Fin d, finiteBadMass q (fun z => fS i (z.2 i)) (C i) εs) := by
      simpa only [Fintype.sum_sum_type, f, centers, radii, Sum.elim_inl, Sum.elim_inr] using hunion
    _ = (∑ j : Fin d, finiteBadMass (pV j) (fV j) (V j) εv)+
        (∑ i : Fin 3 × Fin d, finiteBadMass (pS i) (fS i) (C i) εs) := by simp_rw [hVmass, hSmass]
    _ ≤ (∑ _j : Fin d, ρv)+(∑ _i : Fin 3 × Fin d, ρs) :=
      add_le_add (Finset.sum_le_sum fun j _ => hVbad j) (Finset.sum_le_sum fun i _ => hSbad i)
    _ = _ := by simp [nsmul_eq_mul]

/-- Complete original `velocity_only_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem velocity_only_confidence {d : ℕ} (pV : Fin d → FinDist X) (fV : Fin d → X → ℝ)
    (V : Fin d → ℝ) (A εv ρv : ℝ) (hVrange : ∀ j, 0 ≤ V j ∧ V j ≤ A^2)
    (hVbad : ∀ j, finiteBadMass (pV j) (fV j) (V j) εv ≤ ρv) :
    finiteBadMass (finiteFamilyLaw pV) (fun z => ∑ j : Fin d, intervalClip 0 (A^2) (fV j (z j)))
      (∑ j, V j) ((d : ℝ)*εv) ≤ (d : ℝ)*ρv := by
  have hpoint (z : Fin d → X) (h : ∀ j, |fV j (z j)-V j| ≤ εv) :
      |(∑ j : Fin d, intervalClip 0 (A^2) (fV j (z j)))-(∑ j, V j)| ≤ (d : ℝ)*εv := by
    simpa only [Fintype.card_fin] using finite_sum_error_bound _ V εv
      (fun j => (interval_clip_contract 0 (A^2) (fV j (z j)) (V j) (hVrange j).1 (hVrange j).2).trans (h j))
  calc
    _ ≤ ∑ j : Fin d, finiteBadMass (finiteFamilyLaw pV) (fun z => fV j (z j)) (V j) εv :=
      finite_bad_mass_from_components _ _ _ _ _ _ _ hpoint
    _ = ∑ j : Fin d, finiteBadMass (pV j) (fV j) (V j) εv := by simp_rw [finite_family_bad_mass_coord]
    _ ≤ ∑ _j : Fin d, ρv := Finset.sum_le_sum fun j _ => hVbad j
    _ = _ := by simp [nsmul_eq_mul]

#print axioms Qatlib.Concepts.SpinorSampling.Model.combined_loss_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Model.velocity_only_confidence
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {X : Type*} [Fintype X]

/-- Complete original `finite_bad_mass_mono_radius` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_bad_mass_mono_radius (p : FinDist X) (F : X → ℝ) (C a b : ℝ) (hab : a ≤ b) :
    finiteBadMass p F C b ≤ finiteBadMass p F C a := by
  rw [← finite_bad_indicator_mean, ← finite_bad_indicator_mean]
  apply finite_expect_mono
  intro x
  by_cases h : b < |F x-C|
  · simp only [ite_eq_left h, ite_eq_left (hab.trans_lt h), le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

/-- Abbreviation for Total Record Data in the born current records model. -/
abbrev TotalRecordData (S : Type*) (d nv Kv ns Ks : ℕ) :=
  (Fin d → Fin Kv → Fin nv → S × Bool) × (Fin 3 × Fin d → Fin Ks → Fin ns → S × Bool)

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for total Record Law in the born current records model. -/
def totalRecordLaw {d : ℕ} (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x| ≤ 1)
    (ms : Fin 3 → S → ℝ) (hms : ∀ a x, |ms a x| ≤ 1) (nv Kv ns Ks : ℕ) :
    FinDist (TotalRecordData S d nv Kv ns Ks) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => cohortLaw (cohortLaw (signedRecordLaw (mv j) (hmv j)) nv) Kv))
    (finiteFamilyLaw (fun i : Fin 3 × Fin d => cohortLaw (cohortLaw (signedRecordLaw (ms i.1) (hms i.1)) ns) Ks))

/-- Construction for total Median Output in the born current records model. -/
def totalMedianOutput {d nv Kv ns Ks : ℕ} (u : Fin d → S → ℝ) (e : Fin d → S ≃ S)
    (α β U γ : ℝ) (z : TotalRecordData S d nv Kv ns Ks) : ℝ :=
  combinedLoss (α+β*U) γ
    (fun j => rawBlockMedian (residualStreamingStatistic (u j) α β) (z.1 j))
    (fun i => rawBlockMedian (spinStreamingStatistic (e i.2)) (z.2 i))

/-- Construction for implemented Residual Loss in the born current records model. -/
def implementedResidualLoss {d : ℕ} (mv u : Fin d → S → ℝ) (ms : Fin 3 → S → ℝ)
    (e : Fin d → S ≃ S) (α β γ : ℝ) : ℝ :=
  (∑ j : Fin d, siteMean (fun x => (α*mv j x-β*u j x)^2))+
    γ*((d : ℝ)-(∑ i : Fin 3 × Fin d, siteMean (fun x => ms i.1 x*ms i.1 (e i.2 x))))

/-- Complete original `total_median_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem total_median_confidence {d nv Kv ns Ks : ℕ}
    (mv u : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x| ≤ 1)
    (ms : Fin 3 → S → ℝ) (hs : ∀ x, ∑ a : Fin 3, (ms a x)^2=1)
    (e : Fin d → S ≃ S) (α β U γ η δ : ℝ)
    (hu : ∀ j x, |u j x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) (hnv : 2 ≤ nv) (hns : 2 ≤ ns)
    (hKv0 : 0 < Kv) (hKs0 : 0 < Ks)
    (hnvB : 32*(α+β*U)^4/(η/(4*(d : ℝ)))^2 ≤ (nv : ℝ))
    (hnvD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+β*U)^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ))
    (hnsB : 32/(min 1 (η/(12*(d : ℝ)*γ)))^2 ≤ (ns : ℝ))
    (hnsD : 8*Real.sqrt (Fintype.card S : ℝ)/(min 1 (η/(12*(d : ℝ)*γ))) ≤ (ns : ℝ))
    (hKv : (128/25 : ℝ)*Real.log (1/(δ/(2*(d : ℝ)))) ≤ (Kv : ℝ))
    (hKs : (128/25 : ℝ)*Real.log (1/(δ/(6*(d : ℝ)))) ≤ (Ks : ℝ)) :
    finiteBadMass (totalRecordLaw mv hmv ms (fun a x => unit_spin_component_bound ms hs a x) nv Kv ns Ks)
      (totalMedianOutput u e α β U γ) (implementedResidualLoss mv u ms e α β γ) (η/2) ≤ δ := by
  let εv := η/(4*(d : ℝ))
  let εs := min 1 (η/(12*(d : ℝ)*γ))
  let ρv := δ/(2*(d : ℝ))
  let ρs := δ/(6*(d : ℝ))
  let hms := fun a x => unit_spin_component_bound ms hs a x
  let pV := fun j => cohortLaw (cohortLaw (signedRecordLaw (mv j) (hmv j)) nv) Kv
  let pS := fun i : Fin 3 × Fin d => cohortLaw (cohortLaw (signedRecordLaw (ms i.1) (hms i.1)) ns) Ks
  let fV := fun j => rawBlockMedian (K := Kv) (residualStreamingStatistic (n := nv) (u j) α β)
  let fS := fun i : Fin 3 × Fin d => rawBlockMedian (K := Ks) (spinStreamingStatistic (n := ns) (e i.2))
  let V := fun j => siteMean (fun x => (α*mv j x-β*u j x)^2)
  let C := fun i : Fin 3 × Fin d => siteMean (fun x => ms i.1 x*ms i.1 (e i.2 x))
  have hεv : 0 < εv := by dsimp [εv]; positivity
  have hεs : 0 < εs := by dsimp [εs]; positivity
  have hρv : 0 < ρv := by dsimp [ρv]; positivity
  have hρs : 0 < ρs := by dsimp [ρs]; positivity
  have hVrange (j : Fin d) : 0 ≤ V j ∧ V j ≤ (α+β*U)^2 :=
    ⟨site_mean_nonneg _ (fun _ => sq_nonneg _), residual_mean_bound (mv j) (u j) α β U (hmv j) (hu j) hα hβ⟩
  have hCrange (i : Fin 3 × Fin d) : -1 ≤ C i ∧ C i ≤ 1 :=
    abs_le.mp (spin_component_mean_range ms hs i.1 (e i.2))
  have hRrange : 0 ≤ γ*((d : ℝ)-(∑ i, C i)) ∧ γ*((d : ℝ)-(∑ i, C i)) ≤ 2*(d : ℝ)*γ :=
    spin_total_mean_range ms hs (fun j => e j) γ hγ.le
  have hVbad (j : Fin d) : finiteBadMass (pV j) (fV j) (V j) εv ≤ ρv :=
    residual_streaming_median_confidence (mv j) (u j) α β U εv ρv (hmv j) (hu j) hα hβ
      hnv hεv hnvB hnvD hKv0 hρv hKv
  have hSbad (i : Fin 3 × Fin d) : finiteBadMass (pS i) (fS i) (C i) εs ≤ ρs :=
    spin_streaming_median_confidence (ms i.1) (hms i.1) (e i.2) εs ρs hns hεs hnsB hnsD hKs0 hρs hKs
  change finiteBadMass (independentPairLaw (finiteFamilyLaw pV) (finiteFamilyLaw pS))
    (fun z => combinedLoss (α+β*U) γ (fun j => fV j (z.1 j)) (fun i => fS i (z.2 i)))
    ((∑ j, V j)+γ*((d : ℝ)-(∑ i, C i))) (η/2) ≤ δ
  calc
    _ ≤ finiteBadMass (independentPairLaw (finiteFamilyLaw pV) (finiteFamilyLaw pS))
        (fun z => combinedLoss (α+β*U) γ (fun j => fV j (z.1 j)) (fun i => fS i (z.2 i)))
        ((∑ j, V j)+γ*((d : ℝ)-(∑ i, C i))) ((d : ℝ)*εv+3*(d : ℝ)*γ*εs) :=
      finite_bad_mass_mono_radius _ _ _ _ _ (stochastic_error_budget d γ η hd hγ)
    _ ≤ (d : ℝ)*ρv+3*(d : ℝ)*ρs := combined_loss_confidence pV pS fV fS V C
      (α+β*U) γ εv εs ρv ρs hγ.le hVrange hCrange hRrange hVbad hSbad
    _ = δ := stochastic_failure_budget d δ hd

#print axioms Qatlib.Concepts.SpinorSampling.Model.total_median_confidence
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for velocity Record Law in the born current records model. -/
def velocityRecordLaw {d : ℕ} (mv : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x| ≤ 1)
    (nv Kv : ℕ) : FinDist (Fin d → Fin Kv → Fin nv → S × Bool) :=
  finiteFamilyLaw (fun j => cohortLaw (cohortLaw (signedRecordLaw (mv j) (hmv j)) nv) Kv)

/-- Construction for velocity Median Output in the born current records model. -/
def velocityMedianOutput {d nv Kv : ℕ} (u : Fin d → S → ℝ) (α β U : ℝ)
    (z : Fin d → Fin Kv → Fin nv → S × Bool) : ℝ :=
  ∑ j : Fin d, intervalClip 0 ((α+β*U)^2) (rawBlockMedian (residualStreamingStatistic (u j) α β) (z j))

/-- Complete original `zero_spin_median_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem zero_spin_median_confidence {d nv Kv : ℕ} (mv u : Fin d → S → ℝ) (hmv : ∀ j x, |mv j x| ≤ 1)
    (α β U η δ : ℝ) (hu : ∀ j x, |u j x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) (hnv : 2 ≤ nv) (hKv0 : 0 < Kv)
    (hnvB : 32*(α+β*U)^4/(η/(4*(d : ℝ)))^2 ≤ (nv : ℝ))
    (hnvD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+β*U)^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ))
    (hKv : (128/25 : ℝ)*Real.log (1/(δ/(2*(d : ℝ)))) ≤ (Kv : ℝ)) :
    finiteBadMass (velocityRecordLaw mv hmv nv Kv) (velocityMedianOutput u α β U)
      (∑ j : Fin d, siteMean (fun x => (α*mv j x-β*u j x)^2)) (η/4) ≤ δ/2 := by
  let εv := η/(4*(d : ℝ))
  let ρv := δ/(2*(d : ℝ))
  let pV := fun j => cohortLaw (cohortLaw (signedRecordLaw (mv j) (hmv j)) nv) Kv
  let fV := fun j => rawBlockMedian (K := Kv) (residualStreamingStatistic (n := nv) (u j) α β)
  let V := fun j => siteMean (fun x => (α*mv j x-β*u j x)^2)
  have hεv : 0 < εv := by dsimp [εv]; positivity
  have hρv : 0 < ρv := by dsimp [ρv]; positivity
  have hVrange (j : Fin d) : 0 ≤ V j ∧ V j ≤ (α+β*U)^2 :=
    ⟨site_mean_nonneg _ (fun _ => sq_nonneg _), residual_mean_bound (mv j) (u j) α β U (hmv j) (hu j) hα hβ⟩
  have hVbad (j : Fin d) : finiteBadMass (pV j) (fV j) (V j) εv ≤ ρv :=
    residual_streaming_median_confidence (mv j) (u j) α β U εv ρv (hmv j) (hu j) hα hβ
      hnv hεv hnvB hnvD hKv0 hρv hKv
  have h := velocity_only_confidence pV fV V (α+β*U) εv ρv hVrange hVbad
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have he : (d : ℝ)*εv=η/4 := by dsimp [εv]; field_simp
  have hp : (d : ℝ)*ρv=δ/2 := by dsimp [ρv]; field_simp
  change finiteBadMass (finiteFamilyLaw pV)
    (fun z => ∑ j : Fin d, intervalClip 0 ((α+β*U)^2) (fV j (z j)))
    (∑ j : Fin d, V j) (η/4) ≤ δ/2
  simpa only [he, hp] using h

#print axioms Qatlib.Concepts.SpinorSampling.Model.zero_spin_median_confidence
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*}

/-- Construction for spinor Inner Im in the born current records model. -/
def spinorInnerIm (a b c k : S → ℝ) (x y : S) : ℝ :=
  a x*b y-b x*a y+c x*k y-k x*c y

/-- Construction for spinor Current Mean in the born current records model. -/
def spinorCurrentMean {d : ℕ} (a b c k : S → ℝ) (e : Fin d → S ≃ S) (j : Fin d) (x : S) : ℝ :=
  (spinorInnerIm a b c k x (e j x)-spinorInnerIm a b c k x ((e j).symm x))/2

/-- Complete original `spinor_current_mean_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spinor_current_mean_bound {d : ℕ} (a b c k : S → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (e : Fin d → S ≃ S) (j : Fin d) (x : S) :
    |spinorCurrentMean a b c k e j x| ≤ 1 := by
  dsimp only [spinorCurrentMean, spinorInnerIm]
  apply central_record_mean_bound
  · exact normalized_inner_im_bound _ _ _ _ _ _ _ _ (hz x) (hz (e j x))
  · exact normalized_inner_im_bound _ _ _ _ _ _ _ _ (hz x) (hz ((e j).symm x))

variable [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `spinor_total_median_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spinor_total_median_confidence {d nv Kv ns Ks : ℕ}
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → S → ℝ) (e : Fin d → S ≃ S) (α β U γ η δ : ℝ)
    (hu : ∀ j x, |u j x| ≤ U) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) (hnv : 2 ≤ nv) (hns : 2 ≤ ns)
    (hKv0 : 0 < Kv) (hKs0 : 0 < Ks)
    (hnvB : 32*(α+β*U)^4/(η/(4*(d : ℝ)))^2 ≤ (nv : ℝ))
    (hnvD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+β*U)^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ))
    (hnsB : 32/(min 1 (η/(12*(d : ℝ)*γ)))^2 ≤ (ns : ℝ))
    (hnsD : 8*Real.sqrt (Fintype.card S : ℝ)/(min 1 (η/(12*(d : ℝ)*γ))) ≤ (ns : ℝ))
    (hKv : (128/25 : ℝ)*Real.log (1/(δ/(2*(d : ℝ)))) ≤ (Kv : ℝ))
    (hKs : (128/25 : ℝ)*Real.log (1/(δ/(6*(d : ℝ)))) ≤ (Ks : ℝ)) :
    let mv := spinorCurrentMean a b c k e
    let ms := pauliField a b c k
    let e2 := fun j => (e j).trans (e j)
    finiteBadMass (totalRecordLaw mv (spinor_current_mean_bound a b c k hz e) ms
      (fun i x => unit_spin_component_bound ms (pauli_field_unit a b c k hz) i x) nv Kv ns Ks)
      (totalMedianOutput u e2 α β U γ) (implementedResidualLoss mv u ms e2 α β γ) (η/2) ≤ δ := by
  dsimp only
  exact total_median_confidence (spinorCurrentMean a b c k e) u (spinor_current_mean_bound a b c k hz e)
    (pauliField a b c k) (pauli_field_unit a b c k hz) (fun j => (e j).trans (e j)) α β U γ η δ
    hu hα hβ hγ hd hη hδ hnv hns hKv0 hKs0 hnvB hnvD hnsB hnsD hKv hKs

#print axioms Qatlib.Concepts.SpinorSampling.Model.spinor_current_mean_bound
#print axioms Qatlib.Concepts.SpinorSampling.Model.spinor_total_median_confidence
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S I : Type*} [Fintype S] [Nonempty S] [Fintype I]

/-- Complete original `site_mean_const` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_const (c : ℝ) : siteMean (fun _ : S => c)=c := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [siteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hM

omit [Nonempty S] in
/-- Complete original `site_mean_sub` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_sub (f g : S → ℝ) : siteMean (fun x => f x-g x)=siteMean f-siteMean g := by
  simp only [siteMean, Finset.sum_sub_distrib, sub_div]

omit [Nonempty S] in
/-- Complete original `site_mean_mul` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_mul (c : ℝ) (f : S → ℝ) : siteMean (fun x => c*f x)=c*siteMean f := by
  change (∑ x : S, c*f x)/(Fintype.card S : ℝ)=c*((∑ x : S, f x)/(Fintype.card S : ℝ))
  rw [← Finset.mul_sum]
  ring

omit [Nonempty S] in
/-- Complete original `site_mean_div` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_div (f : S → ℝ) (c : ℝ) : siteMean (fun x => f x/c)=siteMean f/c := by
  change (∑ x : S, f x/c)/(Fintype.card S : ℝ)=((∑ x : S, f x)/(Fintype.card S : ℝ))/c
  rw [← Finset.sum_div]
  ring

omit [Nonempty S] in
/-- Complete original `site_mean_sum` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_sum (f : I → S → ℝ) : siteMean (fun x => ∑ i : I, f i x)=∑ i : I, siteMean (f i) := by
  simp only [siteMean, Finset.sum_div]
  exact Finset.sum_comm

omit [Nonempty S] in
/-- Complete original `site_mean_comp_equiv` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_comp_equiv (f : S → ℝ) (e : S ≃ S) : siteMean (fun x => f (e x))=siteMean f := by
  unfold siteMean
  rw [e.sum_comp]

/-- Complete original `site_mean_abs_le_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem site_mean_abs_le_bound (f : S → ℝ) (C : ℝ) (hf : ∀ x, |f x| ≤ C) : |siteMean f| ≤ C := by
  have hM : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hsum : |∑ x : S, f x| ≤ (Fintype.card S : ℝ)*C := by
    calc
      _ ≤ ∑ x : S, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : S, C := Finset.sum_le_sum fun x _ => hf x
      _ = _ := by simp [nsmul_eq_mul]
  rw [siteMean, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  nlinarith

/-- Construction for source Spin Of Pauli in the born current records model. -/
def sourceSpinOfPauli (t : Fin 3 → S → ℝ) (i : Fin 3) (x : S) : ℝ :=
  if i=0 then t 2 x else if i=1 then -t 1 x else t 0 x

omit [Fintype S] [Nonempty S] in
/-- Complete original `source_pauli_difference_norm` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem source_pauli_difference_norm (t : Fin 3 → S → ℝ) (x y : S) :
    (∑ i : Fin 3, (sourceSpinOfPauli t i x-sourceSpinOfPauli t i y)^2)=
      ∑ i : Fin 3, (t i x-t i y)^2 := by
  simp [sourceSpinOfPauli, Fin.sum_univ_succ]
  ring

/-- Complete original `central_spin_mean_identity` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem central_spin_mean_identity (t : Fin 3 → S → ℝ)
    (hs : ∀ x, ∑ a : Fin 3, (t a x)^2=1) (e : S ≃ S) (h : ℝ) (hh : h ≠ 0) :
    siteMean (fun x => ∑ a : Fin 3, ((t a (e x)-t a (e.symm x))/(2*h))^2) =
      (1-(∑ a : Fin 3, siteMean (fun x => t a x*t a ((e.trans e) x))))/(2*h^2) := by
  have hnorm (x : S) : (t 0 x)^2+(t 1 x)^2+(t 2 x)^2=1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs x
  have hlocal (x : S) : (∑ a : Fin 3, ((t a (e x)-t a (e.symm x))/(2*h))^2) =
      (1-(∑ a : Fin 3, t a (e x)*t a (e.symm x)))/(2*h^2) := by
    simpa [Fin.sum_univ_succ, add_assoc] using central_spin_energy
      (t 0 (e x)) (t 1 (e x)) (t 2 (e x)) (t 0 (e.symm x)) (t 1 (e.symm x)) (t 2 (e.symm x)) h hh
      (hnorm (e x)) (hnorm (e.symm x))
  have hcross : siteMean (fun x => ∑ a : Fin 3, t a (e x)*t a (e.symm x)) =
      ∑ a : Fin 3, siteMean (fun x => t a x*t a ((e.trans e) x)) := by
    calc
      _ = siteMean (fun x => ∑ a : Fin 3, t a (e (e x))*t a x) := by
        simpa only [Equiv.symm_apply_apply] using
          (site_mean_comp_equiv (fun x => ∑ a : Fin 3, t a (e x)*t a (e.symm x)) e).symm
      _ = siteMean (fun x => ∑ a : Fin 3, t a x*t a ((e.trans e) x)) := by
        apply congrArg siteMean
        funext x
        apply Finset.sum_congr rfl
        intro a _
        rw [Equiv.trans_apply]
        ring
      _ = _ := site_mean_sum _
  simp_rw [hlocal]
  rw [site_mean_div, site_mean_sub, site_mean_const, hcross]

/-- Complete original `source_central_spin_mean_identity` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem source_central_spin_mean_identity (t : Fin 3 → S → ℝ)
    (hs : ∀ x, ∑ a : Fin 3, (t a x)^2=1) (e : S ≃ S) (h : ℝ) (hh : h ≠ 0) :
    siteMean (fun x => ∑ a : Fin 3,
      ((sourceSpinOfPauli t a (e x)-sourceSpinOfPauli t a (e.symm x))/(2*h))^2) =
      (1-(∑ a : Fin 3, siteMean (fun x => t a x*t a ((e.trans e) x))))/(2*h^2) := by
  have hpoint (x : S) : (∑ a : Fin 3,
      ((sourceSpinOfPauli t a (e x)-sourceSpinOfPauli t a (e.symm x))/(2*h))^2) =
      ∑ a : Fin 3, ((t a (e x)-t a (e.symm x))/(2*h))^2 := by
    simp only [div_pow, ← Finset.sum_div]
    rw [source_pauli_difference_norm]
  simp_rw [hpoint]
  exact central_spin_mean_identity t hs e h hh

#print axioms Qatlib.Concepts.SpinorSampling.Model.central_spin_mean_identity
#print axioms Qatlib.Concepts.SpinorSampling.Model.source_central_spin_mean_identity
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Construction for spinor Discrete Loss in the born current records model. -/
def spinorDiscreteLoss {d : ℕ} (a b c k : S → ℝ) (u : Fin d → S → ℝ)
    (e : Fin d → S ≃ S) (h κ lam : ℝ) : ℝ :=
  (∑ j : Fin d, siteMean (fun x => (κ*spinorCurrentMean a b c k e j x/h-u j x)^2/κ^2))+
  lam^2*(∑ j : Fin d, siteMean (fun x => ∑ i : Fin 3,
    ((sourceSpinOfPauli (pauliField a b c k) i (e j x)-
      sourceSpinOfPauli (pauliField a b c k) i ((e j).symm x))/(2*h))^2))

omit [DecidableEq S] in
/-- Complete original `spinor_discrete_loss_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spinor_discrete_loss_eq {d : ℕ} (a b c k : S → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (u : Fin d → S → ℝ)
    (e : Fin d → S ≃ S) (h κ lam : ℝ) (hh : h ≠ 0) (hκ : κ ≠ 0) :
    spinorDiscreteLoss a b c k u e h κ lam =
      implementedResidualLoss (spinorCurrentMean a b c k e) u (pauliField a b c k)
        (fun j => (e j).trans (e j)) (1/h) (1/κ) (lam^2/(2*h^2)) := by
  let t := pauliField a b c k
  let mv := spinorCurrentMean a b c k e
  have hs : ∀ x, ∑ i : Fin 3, (t i x)^2=1 := pauli_field_unit a b c k hz
  have hv (j : Fin d) (x : S) : (κ*mv j x/h-u j x)^2/κ^2=((1/h)*mv j x-(1/κ)*u j x)^2 := by
    field_simp
  have hlocal (j : Fin d) : siteMean (fun x => ∑ i : Fin 3,
      ((sourceSpinOfPauli t i (e j x)-sourceSpinOfPauli t i ((e j).symm x))/(2*h))^2) =
      (1-(∑ i : Fin 3, siteMean (fun x => t i x*t i ((e j).trans (e j) x))))/(2*h^2) :=
    source_central_spin_mean_identity t hs (e j) h hh
  have hspin : lam^2*(∑ j : Fin d, siteMean (fun x => ∑ i : Fin 3,
      ((sourceSpinOfPauli t i (e j x)-sourceSpinOfPauli t i ((e j).symm x))/(2*h))^2)) =
      (lam^2/(2*h^2))*((d : ℝ)-(∑ i : Fin 3 × Fin d, siteMean (fun x => t i.1 x*t i.1 ((e i.2).trans (e i.2) x)))) := by
    simp_rw [hlocal]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    ring
  change (∑ j : Fin d, siteMean (fun x => (κ*mv j x/h-u j x)^2/κ^2))+
      lam^2*(∑ j : Fin d, siteMean (fun x => ∑ i : Fin 3,
        ((sourceSpinOfPauli t i (e j x)-sourceSpinOfPauli t i ((e j).symm x))/(2*h))^2)) = _
  simp_rw [hv]
  rw [hspin]
  rfl

/-- Construction for modular Unit Shift in the born current records model. -/
def modularUnitShift (N : ℕ) [NeZero N] : Fin N ≃ Fin N :=
  (ZMod.finEquiv N).toEquiv.trans ((modularTranslation N 1).trans (ZMod.finEquiv N).toEquiv.symm)

/-- Complete original `modular_unit_shift_apply` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem modular_unit_shift_apply (N : ℕ) [NeZero N] (x : Fin N) :
    (ZMod.finEquiv N) (modularUnitShift N x)=(ZMod.finEquiv N) x+1 := by
  simp [modularUnitShift, modularTranslation]

/-- Construction for periodic Unit Shift in the born current records model. -/
def periodicUnitShift (d N : ℕ) [NeZero N] (j : Fin d) :
    (Fin d → Fin N) ≃ (Fin d → Fin N) :=
  Equiv.piCongrRight (fun k => if k=j then modularUnitShift N else Equiv.refl (Fin N))

/-- Complete original `periodic_unit_shift_coordinates` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem periodic_unit_shift_coordinates (d N : ℕ) [NeZero N] (j k : Fin d) (x : Fin d → Fin N) :
    (ZMod.finEquiv N) (periodicUnitShift d N j x k)=
      (ZMod.finEquiv N) (x k)+(if k=j then 1 else 0) := by
  by_cases hk : k=j
  · simp [periodicUnitShift, Equiv.piCongrRight, hk, modular_unit_shift_apply]
  · simp [periodicUnitShift, Equiv.piCongrRight, hk]

/-- Complete original `periodic_unit_shift_square` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem periodic_unit_shift_square (d N : ℕ) [NeZero N] (j : Fin d) :
    (periodicUnitShift d N j).trans (periodicUnitShift d N j)=periodicDoubleShift d N j := by
  apply Equiv.ext
  intro x
  funext k
  apply (ZMod.finEquiv N).injective
  change (ZMod.finEquiv N) (periodicUnitShift d N j (periodicUnitShift d N j x) k)=_
  simp only [periodic_unit_shift_coordinates, periodic_double_shift_coordinates]
  by_cases hk : k=j
  · simp only [ite_eq_left hk]
    ring
  · simp [hk]

#print axioms Qatlib.Concepts.SpinorSampling.Model.spinor_discrete_loss_eq
#print axioms Qatlib.Concepts.SpinorSampling.Model.periodic_unit_shift_square
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

/-- Complete original `squared_residual_perturbation` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem squared_residual_perturbation (v w C ε : ℝ) (hw : |w| ≤ C) (hδ : |v-w| ≤ ε) :
    |v^2-w^2| ≤ 2*C*ε+ε^2 := by
  have hC : 0 ≤ C := (abs_nonneg w).trans hw
  have hs : (v-w)^2 ≤ ε^2 := sq_le_sq.mpr (hδ.trans (le_abs_self _))
  have hm : |w| * |v-w| ≤ C*ε := mul_le_mul hw hδ (abs_nonneg _) hC
  have hp : v^2-w^2=2*w*(v-w)+(v-w)^2 := by ring
  calc
    _ = |2*w*(v-w)+(v-w)^2| := congrArg abs hp
    _ ≤ |2*w*(v-w)|+|(v-w)^2| := abs_add_le _ _
    _ = 2*(|w| * |v-w|)+(v-w)^2 := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg (v-w))]
      ring
    _ ≤ 2*(C*ε)+ε^2 := add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num)) hs
    _ = _ := by ring

/-- Complete original `residual_perturbation_abs` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_perturbation_abs (m u û α0 α1 β ea eb : ℝ) (hm : |m| ≤ 1)
    (ha : |α1-α0| ≤ ea) (hu : |û-u| ≤ eb) (hβ : 0 ≤ β) :
    |(α1*m-β*û)-(α0*m-β*u)| ≤ ea+β*eb := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha
  have hp : (α1*m-β*û)-(α0*m-β*u)=(α1-α0)*m-β*(û-u) := by ring
  rw [hp]
  calc
    _ ≤ |(α1-α0)*m|+|β*(û-u)| := abs_sub _ _
    _ = |α1-α0| * |m|+β* |û-u| := by rw [abs_mul, abs_mul, abs_of_nonneg hβ]
    _ ≤ ea*1+β*eb := add_le_add (mul_le_mul ha hm (abs_nonneg _) hea) (mul_le_mul_of_nonneg_left hu hβ)
    _ = _ := by ring

/-- Complete original `rounded_target_abs_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem rounded_target_abs_bound (u û U eb : ℝ) (hu : |u| ≤ U) (he : |û-u| ≤ eb) :
    |û| ≤ U+eb := by
  calc
    _ = |u+(û-u)| := by congr 1; ring
    _ ≤ |u|+|û-u| := abs_add_le _ _
    _ ≤ _ := add_le_add hu he

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Complete original `implemented_loss_bias_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem implemented_loss_bias_bound {d : ℕ} (mv u û : Fin d → S → ℝ)
    (α0 α1 β γ0 γ1 U C ea eb eg : ℝ) (hmv : ∀ j x, |mv j x| ≤ 1) (hu : ∀ j x, |u j x| ≤ U)
    (htarget : ∀ j x, |û j x-u j x| ≤ eb)
    (ms : Fin 3 → S → ℝ) (hs : ∀ x, ∑ i : Fin 3, (ms i x)^2=1) (e : Fin d → S ≃ S)
    (hα0 : 0 ≤ α0) (hβ : 0 ≤ β)
    (ha : |α1-α0| ≤ ea) (hg : |γ1-γ0| ≤ eg) (hC : α0+β*U ≤ C) :
    |implementedResidualLoss mv û ms e α1 β γ1-implementedResidualLoss mv u ms e α0 β γ0| ≤
      (d : ℝ)*(2*C*(ea+β*eb)+(ea+β*eb)^2)+2*(d : ℝ)*eg := by
  let E := ea+β*eb
  have hpoint (j : Fin d) (x : S) :
      |(α1*mv j x-β*û j x)^2-(α0*mv j x-β*u j x)^2| ≤ 2*C*E+E^2 :=
    squared_residual_perturbation _ _ C E
      ((scaled_residual_abs α0 β U (mv j x) (u j x) hα0 hβ (hmv j x) (hu j x)).trans hC)
      (residual_perturbation_abs (mv j x) (u j x) (û j x) α0 α1 β ea eb (hmv j x) ha (htarget j x) hβ)
  have hmean (j : Fin d) :
      |siteMean (fun x => (α1*mv j x-β*û j x)^2)-siteMean (fun x => (α0*mv j x-β*u j x)^2)| ≤ 2*C*E+E^2 := by
    rw [← site_mean_sub]
    exact site_mean_abs_le_bound _ _ (hpoint j)
  have hvel : |(∑ j : Fin d, siteMean (fun x => (α1*mv j x-β*û j x)^2))-
      (∑ j : Fin d, siteMean (fun x => (α0*mv j x-β*u j x)^2))| ≤ (d : ℝ)*(2*C*E+E^2) := by
    simpa only [Fintype.card_fin] using finite_sum_error_bound _ _ (2*C*E+E^2) hmean
  let B := (d : ℝ)-(∑ i : Fin 3 × Fin d, siteMean (fun x => ms i.1 x*ms i.1 (e i.2 x)))
  have hB : 0 ≤ B ∧ B ≤ 2*(d : ℝ) := by
    simpa only [one_mul, mul_one] using spin_total_mean_range ms hs (fun j => e j) 1 (by norm_num)
  have heg : 0 ≤ eg := (abs_nonneg _).trans hg
  have hspin : |γ1*B-γ0*B| ≤ 2*(d : ℝ)*eg := by
    calc
      _ = |γ1-γ0| *B := by rw [← sub_mul, abs_mul, abs_of_nonneg hB.1]
      _ ≤ eg*(2*(d : ℝ)) := mul_le_mul hg hB.2 hB.1 heg
      _ = _ := by ring
  change |((∑ j : Fin d, siteMean (fun x => (α1*mv j x-β*û j x)^2))+γ1*B)-
      ((∑ j : Fin d, siteMean (fun x => (α0*mv j x-β*u j x)^2))+γ0*B)| ≤ _
  calc
    _ = |((∑ j : Fin d, siteMean (fun x => (α1*mv j x-β*û j x)^2))-
        (∑ j : Fin d, siteMean (fun x => (α0*mv j x-β*u j x)^2)))+(γ1*B-γ0*B)| := by congr 1; ring
    _ ≤ |(∑ j : Fin d, siteMean (fun x => (α1*mv j x-β*û j x)^2))-
        (∑ j : Fin d, siteMean (fun x => (α0*mv j x-β*u j x)^2))|+|γ1*B-γ0*B| := abs_add_le _ _
    _ ≤ _ := add_le_add hvel hspin

variable {X : Type*} [Fintype X]

/-- Complete original `finite_bad_mass_change_center` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem finite_bad_mass_change_center (p : FinDist X) (F : X → ℝ) (C0 C1 ε0 ε1 : ℝ)
    (hbias : |C1-C0| ≤ ε1-ε0) : finiteBadMass p F C0 ε1 ≤ finiteBadMass p F C1 ε0 := by
  rw [← finite_bad_indicator_mean, ← finite_bad_indicator_mean]
  apply finite_expect_mono
  intro x
  by_cases h : ε1 < |F x-C0|
  · have hi : ε0 < |F x-C1| := by
      by_contra hn
      have hsmall : |F x-C1| ≤ ε0 := le_of_not_gt hn
      have ht : |F x-C0| ≤ |F x-C1|+|C1-C0| := by
        have hp : F x-C0=(F x-C1)+(C1-C0) := by ring
        rw [hp]
        exact abs_add_le _ _
      linarith
    simp only [ite_eq_left h, ite_eq_left hi, le_refl]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

#print axioms Qatlib.Concepts.SpinorSampling.Model.implemented_loss_bias_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

/-- Construction for precision Step in the born current records model. -/
def precisionStep (d : ℕ) (C η : ℝ) : ℝ := min (1/2) (η/(128*(d : ℝ)*(C+1)))

/-- Complete original `sufficient_bias_budget` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sufficient_bias_budget (d : ℕ) (C κ η ea eb eg : ℝ)
    (hd : 0 < d) (hC : 0 ≤ C) (hκ : 0 < κ) (hη : 0 < η) (hea : 0 ≤ ea) (heb : 0 ≤ eb)
    (hEA : ea ≤ precisionStep d C η) (hEB : eb ≤ κ*precisionStep d C η)
    (hEG : eg ≤ η/(64*(d : ℝ))) :
    (d : ℝ)*(2*C*(ea+(1/κ)*eb)+(ea+(1/κ)*eb)^2)+2*(d : ℝ)*eg ≤ η/16 := by
  let t := precisionStep d C η
  let E := ea+(1/κ)*eb
  have ht0 : 0 ≤ t := by dsimp [t, precisionStep]; positivity
  have ht1 : t ≤ 1 := by
    have hc : t ≤ 1/2 := min_le_left _ _
    linarith
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEB' : (1/κ)*eb ≤ t := by
    have hb : eb/κ ≤ t := (div_le_iff₀ hκ).mpr (by nlinarith [hEB])
    convert hb using 1
    ring
  have hE : E ≤ 2*t := by dsimp [E]; linarith [hEA]
  have hE2 : E^2 ≤ (2*t)^2 := (sq_le_sq₀ hE0 (by positivity)).mpr hE
  have ht2 : t^2 ≤ t := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hVel : 2*C*E+E^2 ≤ 4*(C+1)*t := by
    have he := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 2*C)
    nlinarith
  have hVelScaled := mul_le_mul_of_nonneg_left hVel (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hden : (0 : ℝ) < 128*(d : ℝ)*(C+1) := by positivity
  have htBudget : t*(128*(d : ℝ)*(C+1)) ≤ η := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hgBudget : eg*(64*(d : ℝ)) ≤ η := (le_div_iff₀ (by positivity)).mp hEG
  change (d : ℝ)*(2*C*E+E^2)+2*(d : ℝ)*eg ≤ η/16
  nlinarith

/-- Complete original `inverse_mesh_rational_upper` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem inverse_mesh_rational_upper (N : ℕ) : 1/(2*Real.pi/(N : ℝ)) ≤ (N : ℝ)/6 := by
  rw [one_div_div]
  have hπ : (0 : ℝ) < 2*Real.pi := by positivity
  rw [div_le_div_iff₀ hπ (by norm_num : (0 : ℝ) < 6)]
  have hm := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    (show (0 : ℝ) ≤ 2*Real.pi-6 by linarith [Real.pi_gt_three])
  nlinarith

#print axioms Qatlib.Concepts.SpinorSampling.Model.sufficient_bias_budget
#print axioms Qatlib.Concepts.SpinorSampling.Model.inverse_mesh_rational_upper
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib
variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `original_loss_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem original_loss_confidence {d nv Kv ns Ks : ℕ}
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u û : Fin d → S → ℝ) (e : Fin d → S ≃ S) (h κ lam α γ U C ea eb eg η δ : ℝ)
    (hh : 0 < h) (hκ : 0 < κ) (hα : 0 ≤ α) (hγ : 0 < γ)
    (hu : ∀ j x, |u j x| ≤ U) (htarget : ∀ j x, |û j x-u j x| ≤ eb)
    (ha : |α-1/h| ≤ ea) (hg : |γ-lam^2/(2*h^2)| ≤ eg) (hC : 1/h+(1/κ)*U ≤ C)
    (hC0 : 0 ≤ C) (heb0 : 0 ≤ eb) (hEA : ea ≤ precisionStep d C η)
    (hEB : eb ≤ κ*precisionStep d C η) (hEG : eg ≤ η/(64*(d : ℝ)))
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) (hnv : 2 ≤ nv) (hns : 2 ≤ ns)
    (hKv0 : 0 < Kv) (hKs0 : 0 < Ks)
    (hnvB : 32*(α+(1/κ)*(U+eb))^4/(η/(4*(d : ℝ)))^2 ≤ (nv : ℝ))
    (hnvD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+(1/κ)*(U+eb))^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ))
    (hnsB : 32/(min 1 (η/(12*(d : ℝ)*γ)))^2 ≤ (ns : ℝ))
    (hnsD : 8*Real.sqrt (Fintype.card S : ℝ)/(min 1 (η/(12*(d : ℝ)*γ))) ≤ (ns : ℝ))
    (hKv : (128/25 : ℝ)*Real.log (1/(δ/(2*(d : ℝ)))) ≤ (Kv : ℝ))
    (hKs : (128/25 : ℝ)*Real.log (1/(δ/(6*(d : ℝ)))) ≤ (Ks : ℝ)) :
    let mv := spinorCurrentMean a b c k e
    let ms := pauliField a b c k
    let e2 := fun j => (e j).trans (e j)
    finiteBadMass (totalRecordLaw mv (spinor_current_mean_bound a b c k hz e) ms
      (fun i x => unit_spin_component_bound ms (pauli_field_unit a b c k hz) i x) nv Kv ns Ks)
      (totalMedianOutput û e2 α (1/κ) (U+eb) γ) (spinorDiscreteLoss a b c k u e h κ lam) η ≤ δ := by
  let mv := spinorCurrentMean a b c k e
  let ms := pauliField a b c k
  let e2 := fun j => (e j).trans (e j)
  let p := totalRecordLaw mv (spinor_current_mean_bound a b c k hz e) ms
    (fun i x => unit_spin_component_bound ms (pauli_field_unit a b c k hz) i x) nv Kv ns Ks
  let F := totalMedianOutput (nv := nv) (Kv := Kv) (ns := ns) (Ks := Ks) û e2 α (1/κ) (U+eb) γ
  let L1 := implementedResidualLoss mv û ms e2 α (1/κ) γ
  have hu' (j : Fin d) (x : S) : |û j x| ≤ U+eb := rounded_target_abs_bound _ _ _ _ (hu j x) (htarget j x)
  have hβ : 0 ≤ (1 : ℝ)/κ := by positivity
  have hα0 : 0 ≤ (1 : ℝ)/h := by positivity
  have hb := sufficient_bias_budget d C κ η ea eb eg hd hC0 hκ hη
    ((abs_nonneg (α-1/h)).trans ha) heb0 hEA hEB hEG
  have hstat : finiteBadMass p F L1 (η/2) ≤ δ :=
    spinor_total_median_confidence a b c k hz û e α (1/κ) (U+eb) γ η δ
      hu' hα hβ hγ hd hη hδ hnv hns hKv0 hKs0 hnvB hnvD hnsB hnsD hKv hKs
  have hbias : |L1-spinorDiscreteLoss a b c k u e h κ lam| ≤ η/16 := by
    rw [spinor_discrete_loss_eq a b c k hz u e h κ lam hh.ne' hκ.ne']
    exact (implemented_loss_bias_bound mv u û (1/h) α (1/κ) (lam^2/(2*h^2)) γ U C ea eb eg
      (spinor_current_mean_bound a b c k hz e) hu htarget ms (pauli_field_unit a b c k hz) e2
      hα0 hβ ha hg hC).trans hb
  change finiteBadMass p F (spinorDiscreteLoss a b c k u e h κ lam) η ≤ δ
  exact (finite_bad_mass_change_center p F _ L1 (η/2) η (by linarith)).trans hstat

/-- Complete original `original_loss_confidence_zero_spin` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem original_loss_confidence_zero_spin {d nv Kv : ℕ}
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u û : Fin d → S → ℝ) (e : Fin d → S ≃ S) (h κ lam α U C ea eb eg η δ : ℝ)
    (hh : 0 < h) (hκ : 0 < κ) (hα : 0 ≤ α)
    (hu : ∀ j x, |u j x| ≤ U) (htarget : ∀ j x, |û j x-u j x| ≤ eb)
    (ha : |α-1/h| ≤ ea) (hg : |0-lam^2/(2*h^2)| ≤ eg) (hC : 1/h+(1/κ)*U ≤ C)
    (hC0 : 0 ≤ C) (heb0 : 0 ≤ eb) (hEA : ea ≤ precisionStep d C η)
    (hEB : eb ≤ κ*precisionStep d C η) (hEG : eg ≤ η/(64*(d : ℝ)))
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) (hnv : 2 ≤ nv) (hKv0 : 0 < Kv)
    (hnvB : 32*(α+(1/κ)*(U+eb))^4/(η/(4*(d : ℝ)))^2 ≤ (nv : ℝ))
    (hnvD : 8*Real.sqrt ((Fintype.card S : ℝ)*(α+(1/κ)*(U+eb))^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ))
    (hKv : (128/25 : ℝ)*Real.log (1/(δ/(2*(d : ℝ)))) ≤ (Kv : ℝ)) :
    finiteBadMass (velocityRecordLaw (spinorCurrentMean a b c k e) (spinor_current_mean_bound a b c k hz e) nv Kv)
      (velocityMedianOutput û α (1/κ) (U+eb)) (spinorDiscreteLoss a b c k u e h κ lam) η ≤ δ/2 := by
  let mv := spinorCurrentMean a b c k e
  let ms := pauliField a b c k
  let e2 := fun j => (e j).trans (e j)
  let p := velocityRecordLaw mv (spinor_current_mean_bound a b c k hz e) nv Kv
  let F := velocityMedianOutput (nv := nv) (Kv := Kv) û α (1/κ) (U+eb)
  let L1 := implementedResidualLoss mv û ms e2 α (1/κ) 0
  have hu' (j : Fin d) (x : S) : |û j x| ≤ U+eb := rounded_target_abs_bound _ _ _ _ (hu j x) (htarget j x)
  have hβ : 0 ≤ (1 : ℝ)/κ := by positivity
  have hα0 : 0 ≤ (1 : ℝ)/h := by positivity
  have hb := sufficient_bias_budget d C κ η ea eb eg hd hC0 hκ hη
    ((abs_nonneg (α-1/h)).trans ha) heb0 hEA hEB hEG
  have hstat : finiteBadMass p F L1 (η/4) ≤ δ/2 := by
    dsimp only [p, F, L1]
    simpa only [implementedResidualLoss, zero_mul, add_zero] using zero_spin_median_confidence mv û
      (spinor_current_mean_bound a b c k hz e) α (1/κ) (U+eb) η δ hu' hα hβ hd hη hδ hnv hKv0 hnvB hnvD hKv
  have hbias : |L1-spinorDiscreteLoss a b c k u e h κ lam| ≤ η/16 := by
    rw [spinor_discrete_loss_eq a b c k hz u e h κ lam hh.ne' hκ.ne']
    exact (implemented_loss_bias_bound mv u û (1/h) α (1/κ) (lam^2/(2*h^2)) 0 U C ea eb eg
      (spinor_current_mean_bound a b c k hz e) hu htarget ms (pauli_field_unit a b c k hz) e2
      hα0 hβ ha hg hC).trans hb
  change finiteBadMass p F (spinorDiscreteLoss a b c k u e h κ lam) η ≤ δ/2
  exact (finite_bad_mass_change_center p F _ L1 (η/4) η (by linarith)).trans hstat

#print axioms Qatlib.Concepts.SpinorSampling.Model.original_loss_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Model.original_loss_confidence_zero_spin
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

set_option synthInstance.maxSize 512 in
/-- Complete original `original_periodic_loss_confidence` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem original_periodic_loss_confidence {d N nv Kv ns Ks : ℕ} [NeZero N]
    (a b c k : (Fin d → Fin N) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u û : Fin d → (Fin d → Fin N) → ℝ) (κ lam α γ U ea eb eg η δ : ℝ)
    (hκ : 0 < κ) (hα : 0 ≤ α) (hγ : 0 < γ) (hU : 0 ≤ U) (heb0 : 0 ≤ eb)
    (hu : ∀ j x, |u j x| ≤ U) (htarget : ∀ j x, |û j x-u j x| ≤ eb)
    (ha : |α-1/(2*Real.pi/(N : ℝ))| ≤ ea)
    (hg : |γ-lam^2/(2*(2*Real.pi/(N : ℝ))^2)| ≤ eg)
    (hEA : ea ≤ precisionStep d ((N : ℝ)/6+(1/κ)*U) η)
    (hEB : eb ≤ κ*precisionStep d ((N : ℝ)/6+(1/κ)*U) η)
    (hEG : eg ≤ η/(64*(d : ℝ)))
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) (hnv : 2 ≤ nv) (hns : 2 ≤ ns)
    (hKv0 : 0 < Kv) (hKs0 : 0 < Ks)
    (hnvB : 32*(α+(1/κ)*(U+eb))^4/(η/(4*(d : ℝ)))^2 ≤ (nv : ℝ))
    (hnvD : 8*Real.sqrt (((N^d : ℕ) : ℝ)*(α+(1/κ)*(U+eb))^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ))
    (hnsB : 32/(min 1 (η/(12*(d : ℝ)*γ)))^2 ≤ (ns : ℝ))
    (hnsD : 8*Real.sqrt ((N^d : ℕ) : ℝ)/(min 1 (η/(12*(d : ℝ)*γ))) ≤ (ns : ℝ))
    (hKv : (128/25 : ℝ)*Real.log (1/(δ/(2*(d : ℝ)))) ≤ (Kv : ℝ))
    (hKs : (128/25 : ℝ)*Real.log (1/(δ/(6*(d : ℝ)))) ≤ (Ks : ℝ)) :
    let e := periodicUnitShift d N
    let mv := spinorCurrentMean a b c k e
    let ms := pauliField a b c k
    finiteBadMass (totalRecordLaw mv (spinor_current_mean_bound a b c k hz e) ms
      (fun i x => unit_spin_component_bound ms (pauli_field_unit a b c k hz) i x) nv Kv ns Ks)
      (totalMedianOutput û (periodicDoubleShift d N) α (1/κ) (U+eb) γ)
      (spinorDiscreteLoss a b c k u e (2*Real.pi/(N : ℝ)) κ lam) η ≤ δ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hh : 0 < 2*Real.pi/(N : ℝ) := by positivity
  have hC : 1/(2*Real.pi/(N : ℝ))+(1/κ)*U ≤ (N : ℝ)/6+(1/κ)*U :=
    add_le_add (inverse_mesh_rational_upper N) le_rfl
  have hC0 : (0 : ℝ) ≤ (N : ℝ)/6+(1/κ)*U := by positivity
  have hnD : 8*Real.sqrt ((Fintype.card (Fin d → Fin N) : ℝ)*(α+(1/κ)*(U+eb))^4)/(η/(4*(d : ℝ))) ≤ (nv : ℝ) := by
    simpa only [periodic_grid_card] using hnvD
  have hsD : 8*Real.sqrt (Fintype.card (Fin d → Fin N) : ℝ)/(min 1 (η/(12*(d : ℝ)*γ))) ≤ (ns : ℝ) := by
    simpa only [periodic_grid_card] using hnsD
  have hp := original_loss_confidence a b c k hz u û (periodicUnitShift d N) (2*Real.pi/(N : ℝ)) κ lam
    α γ U ((N : ℝ)/6+(1/κ)*U) ea eb eg η δ hh hκ hα hγ hu htarget ha hg hC hC0 heb0 hEA hEB hEG
    hd hη hδ hnv hns hKv0 hKs0 hnvB hnD hnsB hsD hKv hKs
  simpa only [periodic_unit_shift_square] using hp

#print axioms Qatlib.Concepts.SpinorSampling.Model.original_periodic_loss_confidence
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
export Qatlib.Concepts.FinitePrecision.ComputableInput.RationalPiEnclosure (atanTermQ atanPartialQ atanIntervalQ machinIntervalQ atanMagnitude atan_term_cast atan_partial_cast atan_partial_succ_cast atan_magnitude_antitone atan_magnitude_hasSum atan_interval_contains machin_interval_contains)
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
open scoped BigOperators

/-- Construction for initial Pi Terms in the born current records model. -/
def initialPiTerms (bits : ℕ) : ℕ := max 1 ((bits+8)/4)

/-- Construction for pi Candidate Q in the born current records model. -/
def piCandidateQ (bits : ℕ) : ℚ × ℚ := machinIntervalQ (initialPiTerms bits)

/-- Construction for pi Initial Iteration Q in the born current records model. -/
def piInitialIterationQ (bits : ℕ) : Option (ℚ × ℚ) :=
  let p := piCandidateQ bits
  if p.2-p.1 ≤ (1 : ℚ)/(2 : ℚ)^bits then some p else none

noncomputable section

/-- Complete original `atan_interval_width` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem atan_interval_width (a n : ℕ) (ha : 2 ≤ a) :
    ((atanIntervalQ a n).2 : ℝ)-((atanIntervalQ a n).1 : ℝ)=atanMagnitude a n := by
  simp only [atanIntervalQ, Rat.cast_min, Rat.cast_max, Rat.cast_add]
  rw [max_sub_min_eq_abs]
  have hp : (atanPartialQ a n : ℝ)+(atanTermQ a n : ℝ)-(atanPartialQ a n : ℝ) =
      (atanTermQ a n : ℝ) := by ring
  rw [hp, atan_term_cast, abs_mul, abs_pow]
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hm : 0 ≤ atanMagnitude a n := by unfold atanMagnitude; positivity
  simp [abs_of_nonneg hm]

/-- Complete original `machin_interval_width` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem machin_interval_width (n : ℕ) :
    ((machinIntervalQ n).2 : ℝ)-((machinIntervalQ n).1 : ℝ) =
      16*atanMagnitude 5 n+4*atanMagnitude 239 n := by
  have h5 := atan_interval_width 5 n (by omega)
  have h239 := atan_interval_width 239 n (by omega)
  simp only [machinIntervalQ, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
  linarith

/-- Complete original `atan_magnitude_le_five_power` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem atan_magnitude_le_five_power (a n : ℕ) (ha : 5 ≤ a) :
    atanMagnitude a n ≤ 1/(5 : ℝ)^(2*n+1) := by
  have ha5 : (5 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have ho : (1 : ℝ) ≤ ((2*n+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2*n+1)
  have hp : (5 : ℝ)^(2*n+1) ≤ (a : ℝ)^(2*n+1) := pow_le_pow_left₀ (by norm_num) ha5 _
  have hm := mul_le_mul_of_nonneg_right ho (pow_nonneg ha0 (2*n+1))
  unfold atanMagnitude
  exact one_div_le_one_div_of_le (by positivity) (hp.trans (by simpa only [one_mul] using hm))

/-- Complete original `five_power_inv_le_dyadic` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem five_power_inv_le_dyadic (n : ℕ) : 1/(5 : ℝ)^(2*n+1) ≤ 1/(2 : ℝ)^(4*n+2) := by
  have hp : (4 : ℝ)^(2*n+1) ≤ (5 : ℝ)^(2*n+1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have he : (4 : ℝ)^(2*n+1)=(2 : ℝ)^(4*n+2) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [he] at hp
  exact one_div_le_one_div_of_le (by positivity) hp

/-- Complete original `pi_candidate_width` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pi_candidate_width (bits : ℕ) :
    ((piCandidateQ bits).2 : ℝ)-((piCandidateQ bits).1 : ℝ) ≤
      (5/32 : ℝ)*(1/(2 : ℝ)^bits) := by
  let n := initialPiTerms bits
  have hn : 4*n ≥ bits+5 := by dsimp [n, initialPiTerms]; omega
  have h5 := atan_magnitude_le_five_power 5 n (by omega)
  have h239 := atan_magnitude_le_five_power 239 n (by omega)
  have hfirst : 16*atanMagnitude 5 n+4*atanMagnitude 239 n ≤ 20/(5 : ℝ)^(2*n+1) := by
    calc
      _ ≤ 16*(1/(5 : ℝ)^(2*n+1))+4*(1/(5 : ℝ)^(2*n+1)) := add_le_add
        (mul_le_mul_of_nonneg_left h5 (by norm_num)) (mul_le_mul_of_nonneg_left h239 (by norm_num))
      _ = _ := by ring
  have hpow : (2 : ℝ)^(bits+7) ≤ (2 : ℝ)^(4*n+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hinv := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ)^(bits+7)) hpow
  calc
    _ = 16*atanMagnitude 5 n+4*atanMagnitude 239 n := machin_interval_width n
    _ ≤ 20/(5 : ℝ)^(2*n+1) := hfirst
    _ ≤ 20/(2 : ℝ)^(4*n+2) := by
      have hh := mul_le_mul_of_nonneg_left (five_power_inv_le_dyadic n) (by norm_num : (0 : ℝ) ≤ 20)
      simpa only [mul_one_div] using hh
    _ ≤ 20/(2 : ℝ)^(bits+7) := by
      have hh := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 20)
      simpa only [mul_one_div] using hh
    _ = _ := by rw [pow_add]; norm_num; ring

/-- Complete original `pi_candidate_guard` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pi_candidate_guard (bits : ℕ) :
    (piCandidateQ bits).2-(piCandidateQ bits).1 ≤ (1 : ℚ)/(2 : ℚ)^bits := by
  have hw := pi_candidate_width bits
  have hle : (5/32 : ℝ)*(1/(2 : ℝ)^bits) ≤ 1/(2 : ℝ)^bits :=
    mul_le_of_le_one_left (by positivity) (by norm_num)
  have hr := hw.trans hle
  have hr' : (((piCandidateQ bits).2-(piCandidateQ bits).1 : ℚ) : ℝ) ≤
      (((1 : ℚ)/(2 : ℚ)^bits : ℚ) : ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hr
  exact Rat.cast_le.mp hr'

/-- Complete original `pi_initial_iteration_returns` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pi_initial_iteration_returns (bits : ℕ) :
    piInitialIterationQ bits=some (piCandidateQ bits) := by
  unfold piInitialIterationQ
  rw [ite_eq_left (pi_candidate_guard bits)]

/-- Complete original `pi_candidate_valid` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem pi_candidate_valid (bits : ℕ) (hb : 1 ≤ bits) :
    (3 : ℝ) < ((piCandidateQ bits).1 : ℝ) ∧
    ((piCandidateQ bits).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((piCandidateQ bits).2 : ℝ) ∧
    ((piCandidateQ bits).2 : ℝ) < 4 := by
  have hc := machin_interval_contains (initialPiTerms bits)
  have hw := pi_candidate_width bits
  have hp : (2 : ℝ)^1 ≤ (2 : ℝ)^bits := pow_le_pow_right₀ (by norm_num) hb
  have hi : 1/(2 : ℝ)^bits ≤ 1/2 := by
    simpa only [pow_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)^1) hp
  have hs : ((piCandidateQ bits).2 : ℝ)-((piCandidateQ bits).1 : ℝ) ≤ 5/64 := by nlinarith
  change ((piCandidateQ bits).1 : ℝ) ≤ Real.pi ∧ Real.pi ≤ ((piCandidateQ bits).2 : ℝ) at hc
  refine ⟨?_, hc.1, hc.2, ?_⟩ <;> linarith [Real.pi_gt_d2, Real.pi_lt_d2]

#print axioms Qatlib.Concepts.SpinorSampling.Model.pi_initial_iteration_returns
#print axioms Qatlib.Concepts.SpinorSampling.Model.pi_candidate_valid
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model

/-- Construction for precision Step Q in the born current records model. -/
def precisionStepQ (d : ℕ) (C η : ℚ) : ℚ := min (1/2) (η/(128*(d : ℚ)*(C+1)))

/-- Data and invariants for Coefficient Candidate Q in the born current records model. -/
structure CoefficientCandidateQ where
  alpha : ℚ
  beta : ℚ
  gamma : ℚ
  alphaError : ℚ
  gammaError : ℚ
  maxTargetError : ℚ
  piBits : ℕ
  deriving Repr

/-- Construction for coefficient Candidate Q in the born current records model. -/
def coefficientCandidateQ (d N bits : ℕ) (κ lam U η : ℚ) : CoefficientCandidateQ :=
  let p := piCandidateQ bits
  let alo := (N : ℚ)/2/p.2
  let ahi := (N : ℚ)/2/p.1
  let glo := lam^2*alo^2/2
  let ghi := lam^2*ahi^2/2
  let C := (N : ℚ)/6+(1/κ)*U
  { alpha := (alo+ahi)/2, beta := 1/κ, gamma := (glo+ghi)/2,
    alphaError := (ahi-alo)/2, gammaError := (ghi-glo)/2,
    maxTargetError := κ*precisionStepQ d C η, piBits := bits }

/-- Construction for coefficient Iteration Q in the born current records model. -/
def coefficientIterationQ (d N bits : ℕ) (κ lam U η : ℚ) : Option CoefficientCandidateQ :=
  let c := coefficientCandidateQ d N bits κ lam U η
  let C := (N : ℚ)/6+(1/κ)*U
  if c.alphaError ≤ precisionStepQ d C η ∧ c.gammaError ≤ η/(64*(d : ℚ)) then some c else none

noncomputable section

/-- Complete original `precision_step_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem precision_step_cast (d : ℕ) (C η : ℚ) : (precisionStepQ d C η : ℝ)=precisionStep d (C : ℝ) (η : ℝ) := by
  simp only [precisionStepQ, precisionStep, Rat.cast_min, Rat.cast_div, Rat.cast_add,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]

/-- Complete original `midpoint_error_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem midpoint_error_bound (lo hi x : ℝ) (hl : lo ≤ x) (hu : x ≤ hi) :
    |(lo+hi)/2-x| ≤ (hi-lo)/2 := by
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Complete original `inverse_pi_interval` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem inverse_pi_interval (N : ℕ) (p q : ℝ) (hp : 0 < p)
    (hl : p ≤ Real.pi) (hu : Real.pi ≤ q) :
    (N : ℝ)/2/q ≤ 1/(2*Real.pi/(N : ℝ)) ∧
      1/(2*Real.pi/(N : ℝ)) ≤ (N : ℝ)/2/p := by
  have hnum : (0 : ℝ) ≤ (N : ℝ)/2 := by positivity
  have he : 1/(2*Real.pi/(N : ℝ))=(N : ℝ)/2/Real.pi := by rw [one_div_div]; ring
  rw [he]
  exact ⟨div_le_div_of_nonneg_left hnum Real.pi_pos hu, div_le_div_of_nonneg_left hnum hp hl⟩

/-- Complete original `coefficient_candidate_errors` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_errors (d N bits : ℕ) (κ lam U η : ℚ) (hb : 1 ≤ bits) :
    |((coefficientCandidateQ d N bits κ lam U η).alpha : ℝ)-1/(2*Real.pi/(N : ℝ))| ≤
      ((coefficientCandidateQ d N bits κ lam U η).alphaError : ℝ) ∧
    |((coefficientCandidateQ d N bits κ lam U η).gamma : ℝ)-
      (lam : ℝ)^2/(2*(2*Real.pi/(N : ℝ))^2)| ≤
      ((coefficientCandidateQ d N bits κ lam U η).gammaError : ℝ) := by
  let p := piCandidateQ bits
  let lo : ℝ := (N : ℝ)/2/(p.2 : ℝ)
  let hi : ℝ := (N : ℝ)/2/(p.1 : ℝ)
  let x : ℝ := 1/(2*Real.pi/(N : ℝ))
  have hp := pi_candidate_valid bits hb
  have hlo : (0 : ℝ) < (p.1 : ℝ) := by change 0 < ((piCandidateQ bits).1 : ℝ); linarith [hp.1]
  have hhi : (0 : ℝ) < (p.2 : ℝ) := Real.pi_pos.trans_le hp.2.2.1
  have hx : lo ≤ x ∧ x ≤ hi := inverse_pi_interval N (p.1 : ℝ) (p.2 : ℝ) hlo hp.2.1 hp.2.2.1
  have hlo0 : 0 ≤ lo := by dsimp [lo]; positivity
  have hx0 : 0 ≤ x := hlo0.trans hx.1
  have hglo : (lam : ℝ)^2*lo^2/2 ≤ (lam : ℝ)^2*x^2/2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo0 hx.1 2) (sq_nonneg _)) (by norm_num)
  have hghi : (lam : ℝ)^2*x^2/2 ≤ (lam : ℝ)^2*hi^2/2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx.2 2) (sq_nonneg _)) (by norm_num)
  have hgam : (lam : ℝ)^2*x^2/2=(lam : ℝ)^2/(2*(2*Real.pi/(N : ℝ))^2) := by dsimp [x]; ring
  constructor
  · have ha := midpoint_error_bound lo hi x hx.1 hx.2
    simpa only [coefficientCandidateQ, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_natCast,
      Rat.cast_ofNat, lo, hi, x, p] using ha
  · have hg := midpoint_error_bound ((lam : ℝ)^2*lo^2/2) ((lam : ℝ)^2*hi^2/2)
      ((lam : ℝ)^2*x^2/2) hglo hghi
    rw [hgam] at hg
    simpa only [coefficientCandidateQ, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat, lo, hi, p] using hg

/-- Complete original `coefficient_candidate_beta` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_beta (d N bits : ℕ) (κ lam U η : ℚ) :
    ((coefficientCandidateQ d N bits κ lam U η).beta : ℝ)=1/(κ : ℝ) := by
  simp only [coefficientCandidateQ, Rat.cast_div, Rat.cast_one]

/-- Complete original `coefficient_iteration_sufficient` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_iteration_sufficient (d N bits : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hc : coefficientIterationQ d N bits κ lam U η=some c) :
    (c.alphaError : ℝ) ≤ precisionStep d ((N : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) ∧
    (c.gammaError : ℝ) ≤ (η : ℝ)/(64*(d : ℝ)) := by
  dsimp only [coefficientIterationQ] at hc
  split_ifs at hc with hg
  · cases hc
    constructor
    · have he := (Rat.cast_le (K := ℝ)).mpr hg.1
      simpa only [precision_step_cast, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_one, Rat.cast_ofNat] using he
    · have he := (Rat.cast_le (K := ℝ)).mpr hg.2
      simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using he

#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficient_candidate_errors
#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficient_iteration_sufficient
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section

/-- Complete original `coefficient_candidate_alpha_pos` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_alpha_pos (d N bits : ℕ) (κ lam U η : ℚ) (hN : 0 < N) (hb : 1 ≤ bits) :
    0 < (coefficientCandidateQ d N bits κ lam U η).alpha := by
  have hp := pi_candidate_valid bits hb
  have hlow : (0 : ℚ) < (piCandidateQ bits).1 := Rat.cast_pos.mp (by linarith [hp.1] : (0 : ℝ) < ((piCandidateQ bits).1 : ℝ))
  have hhigh : (0 : ℚ) < (piCandidateQ bits).2 := Rat.cast_pos.mp (Real.pi_pos.trans_le hp.2.2.1)
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  dsimp only [coefficientCandidateQ]
  positivity

/-- Complete original `coefficient_candidate_error_nonneg` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_error_nonneg (d N bits : ℕ) (κ lam U η : ℚ) (hb : 1 ≤ bits) :
    0 ≤ (coefficientCandidateQ d N bits κ lam U η).alphaError ∧
      0 ≤ (coefficientCandidateQ d N bits κ lam U η).gammaError := by
  have he := coefficient_candidate_errors d N bits κ lam U η hb
  exact ⟨Rat.cast_nonneg.mp ((abs_nonneg _).trans he.1), Rat.cast_nonneg.mp ((abs_nonneg _).trans he.2)⟩

/-- Complete original `coefficient_candidate_gamma_nonneg` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_gamma_nonneg (d N bits : ℕ) (κ lam U η : ℚ) :
    0 ≤ (coefficientCandidateQ d N bits κ lam U η).gamma := by
  dsimp only [coefficientCandidateQ]
  positivity

/-- Complete original `coefficient_candidate_gamma_zero_iff` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_gamma_zero_iff (d N bits : ℕ) (κ lam U η : ℚ) (hN : 0 < N) (hb : 1 ≤ bits) :
    (coefficientCandidateQ d N bits κ lam U η).gamma=0 ↔ lam=0 := by
  constructor
  · intro hg
    by_contra hl
    have hp := pi_candidate_valid bits hb
    have hlow : (0 : ℚ) < (piCandidateQ bits).1 := Rat.cast_pos.mp (by linarith [hp.1] : (0 : ℝ) < ((piCandidateQ bits).1 : ℝ))
    have hhigh : (0 : ℚ) < (piCandidateQ bits).2 := Rat.cast_pos.mp (Real.pi_pos.trans_le hp.2.2.1)
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have hlam : (0 : ℚ) < lam^2 := sq_pos_of_ne_zero hl
    have hpos : 0 < (coefficientCandidateQ d N bits κ lam U η).gamma := by
      dsimp only [coefficientCandidateQ]
      positivity
    linarith
  · intro hl
    subst lam
    simp [coefficientCandidateQ]

/-- Complete original `coefficient_candidate_target_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_target_bound (d N bits : ℕ) (κ lam U η : ℚ) :
    ((coefficientCandidateQ d N bits κ lam U η).maxTargetError : ℝ)=
      (κ : ℝ)*precisionStep d ((N : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) := by
  simp only [coefficientCandidateQ, Rat.cast_mul, precision_step_cast, Rat.cast_add, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]

/-- Complete original `coefficient_candidate_target_pos` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_target_pos (d N bits : ℕ) (κ lam U η : ℚ)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) :
    0 < (coefficientCandidateQ d N bits κ lam U η).maxTargetError := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  dsimp only [coefficientCandidateQ, precisionStepQ]
  positivity

#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficient_candidate_gamma_zero_iff
#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficient_candidate_target_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section

/-- Complete original `coefficient_candidate_error_rates` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_candidate_error_rates (d N bits : ℕ) (κ lam U η : ℚ) (hb : 1 ≤ bits) :
    ((coefficientCandidateQ d N bits κ lam U η).alphaError : ℝ) ≤ (N : ℝ)/(36*(2 : ℝ)^bits) ∧
    ((coefficientCandidateQ d N bits κ lam U η).gammaError : ℝ) ≤
      (lam : ℝ)^2*(N : ℝ)^2/(216*(2 : ℝ)^bits) := by
  let p := piCandidateQ bits
  let c := coefficientCandidateQ d N bits κ lam U η
  let alo : ℝ := (N : ℝ)/2/(p.2 : ℝ)
  let ahi : ℝ := (N : ℝ)/2/(p.1 : ℝ)
  let W : ℝ := (p.2 : ℝ)-(p.1 : ℝ)
  have hp := pi_candidate_valid bits hb
  have hlo : (0 : ℝ) < (p.1 : ℝ) := by linarith [hp.1]
  have hhi : (0 : ℝ) < (p.2 : ℝ) := Real.pi_pos.trans_le hp.2.2.1
  have hhi3 : (3 : ℝ) ≤ (p.2 : ℝ) := by linarith [hp.2.2.1, Real.pi_gt_three]
  have hW0 : 0 ≤ W := sub_nonneg.mpr (hp.2.1.trans hp.2.2.1)
  have hW : W ≤ 1/(2 : ℝ)^bits := (pi_candidate_width bits).trans
    (mul_le_of_le_one_left (by positivity) (by norm_num))
  have hEAhalf : (c.alphaError : ℝ)=(ahi-alo)/2 := by
    simp only [c, coefficientCandidateQ, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, alo, ahi, p]
  have hEAwidth : (c.alphaError : ℝ)=(N : ℝ)*W/(4*(p.1 : ℝ)*(p.2 : ℝ)) := by
    rw [hEAhalf]
    dsimp only [alo, ahi, W]
    field_simp
    ring
  have hprod : (3 : ℝ)*3 ≤ (p.1 : ℝ)*(p.2 : ℝ) :=
    mul_le_mul hp.1.le hhi3 (by norm_num) hlo.le
  have hden : (36 : ℝ) ≤ 4*(p.1 : ℝ)*(p.2 : ℝ) := by nlinarith
  have hEA : (c.alphaError : ℝ) ≤ (N : ℝ)/(36*(2 : ℝ)^bits) := by
    calc
      _ = (N : ℝ)*W/(4*(p.1 : ℝ)*(p.2 : ℝ)) := hEAwidth
      _ ≤ (N : ℝ)*W/36 := div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg N) hW0) (by norm_num) hden
      _ = ((N : ℝ)/36)*W := by ring
      _ ≤ ((N : ℝ)/36)*(1/(2 : ℝ)^bits) := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  have halo : alo ≤ (N : ℝ)/6 := by
    calc
      _ ≤ (N : ℝ)/2/3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hhi3
      _ = _ := by ring
  have hahi : ahi ≤ (N : ℝ)/6 := by
    calc
      _ ≤ (N : ℝ)/2/3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hp.1.le
      _ = _ := by ring
  have hsum : alo+ahi ≤ (N : ℝ)/3 := by linarith
  have hsum0 : 0 ≤ alo+ahi := by dsimp [alo, ahi]; positivity
  have hEGhalf : (c.gammaError : ℝ)=((lam : ℝ)^2*ahi^2/2-(lam : ℝ)^2*alo^2/2)/2 := by
    simp only [c, coefficientCandidateQ, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat, alo, ahi, p]
  have hEG : (c.gammaError : ℝ)=((lam : ℝ)^2/2)*((c.alphaError : ℝ)*(alo+ahi)) := by
    rw [hEGhalf, hEAhalf]
    ring
  refine ⟨hEA, ?_⟩
  calc
    _ = ((lam : ℝ)^2/2)*((c.alphaError : ℝ)*(alo+ahi)) := hEG
    _ ≤ ((lam : ℝ)^2/2)*(((N : ℝ)/(36*(2 : ℝ)^bits))*((N : ℝ)/3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hEA hsum hsum0 (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficient_candidate_error_rates
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model

/-- Complete original `coefficient_iteration_result_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_iteration_result_eq (d N bits : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hc : coefficientIterationQ d N bits κ lam U η=some c) :
    c=coefficientCandidateQ d N bits κ lam U η := by
  dsimp only [coefficientIterationQ] at hc
  split_ifs at hc
  cases hc
  rfl

noncomputable section

/-- Complete original `coefficient_iteration_valid` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_iteration_valid (d N bits : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hb : 1 ≤ bits) (hc : coefficientIterationQ d N bits κ lam U η=some c) :
    |(c.alpha : ℝ)-1/(2*Real.pi/(N : ℝ))| ≤ (c.alphaError : ℝ) ∧
    |(c.gamma : ℝ)-(lam : ℝ)^2/(2*(2*Real.pi/(N : ℝ))^2)| ≤ (c.gammaError : ℝ) ∧
    (c.beta : ℝ)=1/(κ : ℝ) ∧
    (c.maxTargetError : ℝ)=(κ : ℝ)*precisionStep d ((N : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) ∧
    (c.alphaError : ℝ) ≤ precisionStep d ((N : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) ∧
    (c.gammaError : ℝ) ≤ (η : ℝ)/(64*(d : ℝ)) := by
  have hEq := coefficient_iteration_result_eq d N bits κ lam U η c hc
  subst c
  have he := coefficient_candidate_errors d N bits κ lam U η hb
  have hs := coefficient_iteration_sufficient d N bits κ lam U η _ hc
  exact ⟨he.1, he.2, coefficient_candidate_beta d N bits κ lam U η,
    coefficient_candidate_target_bound d N bits κ lam U η, hs.1, hs.2⟩

#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficient_iteration_valid
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model

/-- Construction for ceil Int Q in the born current records model. -/
def ceilIntQ (q : ℚ) : ℤ := -(-q.num/(q.den : ℤ))

/-- Construction for ceil Nat Q in the born current records model. -/
def ceilNatQ (q : ℚ) : ℕ := (ceilIntQ q).toNat

/-- The public callers use positive arguments, as required by Python's helper. -/
def ceilLog2Q (q : ℚ) : ℕ :=
  if q ≤ 1 then 0 else
    let k := q.num.natAbs.size-q.den.size
    if (2 : ℚ)^k < q then k+1 else k

/-- Construction for median Blocks Q in the born current records model. -/
def medianBlocksQ (ρ : ℚ) : ℕ :=
  let n := max 1 (ceilNatQ ((128/25 : ℚ)*(ceilLog2Q (1/ρ) : ℚ)))
  if n%2=0 then n+1 else n

noncomputable section

/-- Complete original `ceil_int_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_int_eq (q : ℚ) : ceilIntQ q=⌈q⌉ := (Rat.ceil_def' q).symm

/-- Complete original `positive_rat_natAbs_repr` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem positive_rat_natAbs_repr (q : ℚ) (hq : 0 < q) :
    q=(q.num.natAbs : ℚ)/(q.den : ℚ) := by
  have hp : 0 < q.num := Rat.num_pos.mpr hq
  have hi : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hp.le
  have hc : (q.num.natAbs : ℚ)=(q.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hi
  rw [hc]
  exact q.num_div_den.symm

/-- Complete original `rat_gt_one_num_gt_den` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem rat_gt_one_num_gt_den (q : ℚ) (hq : 1 < q) : q.den < q.num.natAbs := by
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.pos
  have he := positive_rat_natAbs_repr q (by linarith)
  have hr : (1 : ℚ) < (q.num.natAbs : ℚ)/(q.den : ℚ) := by simpa only [← he] using hq
  have hn := (one_lt_div hd).mp hr
  exact_mod_cast hn

/-- Complete original `numerator_bit_upper` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem numerator_bit_upper (n d : ℕ) (hd : 0 < d) (hnd : d < n) :
    n ≤ 2^(n.size-d.size+1)*d := by
  have hs : d.size ≤ n.size := Nat.size_le_size hnd.le
  have hdsize : 0 < d.size := Nat.size_pos.mpr hd
  have hlower : 2^(d.size-1) ≤ d := Nat.lt_size.mp (by omega)
  have he : 2^n.size=2^(n.size-d.size+1)*2^(d.size-1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  calc
    n ≤ 2^n.size := (Nat.lt_size_self n).le
    _ = _ := he
    _ ≤ _ := Nat.mul_le_mul_left _ hlower

/-- Complete original `numerator_bit_lower` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem numerator_bit_lower (n d : ℕ) (hnd : d < n) :
    2^(n.size-d.size)*d < 2*n := by
  have hs : d.size ≤ n.size := Nat.size_le_size hnd.le
  have hnsize : 0 < n.size := Nat.size_pos.mpr (by omega)
  have hlower : 2^(n.size-1) ≤ n := Nat.lt_size.mp (by omega)
  have he : 2^n.size=2*2^(n.size-1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  calc
    _ < 2^(n.size-d.size)*2^d.size := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self d) (by positivity)
    _ = 2^n.size := by rw [← Nat.pow_add, Nat.sub_add_cancel hs]
    _ = _ := he
    _ ≤ _ := Nat.mul_le_mul_left 2 hlower

/-- Complete original `ceil_log2_power` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_log2_power (q : ℚ) : q ≤ (2 : ℚ)^(ceilLog2Q q) := by
  by_cases hq : q ≤ 1
  · simpa only [ceilLog2Q, ite_eq_left hq, pow_zero] using hq
  · have hq1 : 1 < q := lt_of_not_ge hq
    have hnd := rat_gt_one_num_gt_den q hq1
    have hnat := numerator_bit_upper q.num.natAbs q.den q.pos hnd
    have hcast : (q.num.natAbs : ℚ) ≤ (2 : ℚ)^(q.num.natAbs.size-q.den.size+1)*(q.den : ℚ) := by exact_mod_cast hnat
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.pos
    have hratio : q ≤ (2 : ℚ)^(q.num.natAbs.size-q.den.size+1) := by
      calc
        q = (q.num.natAbs : ℚ)/(q.den : ℚ) := positive_rat_natAbs_repr q (by linarith)
        _ ≤ _ := (div_le_iff₀ hd).mpr hcast
    dsimp only [ceilLog2Q]
    rw [ite_eq_right hq]
    split_ifs with hc
    · exact hratio
    · exact le_of_not_gt hc

/-- Complete original `ceil_log2_power_lt_twice` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_log2_power_lt_twice (q : ℚ) (hq : 1 < q) :
    (2 : ℚ)^(ceilLog2Q q) < 2*q := by
  have hnd := rat_gt_one_num_gt_den q hq
  have hnat := numerator_bit_lower q.num.natAbs q.den hnd
  have hcast : (2 : ℚ)^(q.num.natAbs.size-q.den.size)*(q.den : ℚ) < 2*(q.num.natAbs : ℚ) := by exact_mod_cast hnat
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.pos
  have hlow : (2 : ℚ)^(q.num.natAbs.size-q.den.size) < 2*q := by
    calc
      _ < (2*(q.num.natAbs : ℚ))/(q.den : ℚ) := (lt_div_iff₀ hd).mpr hcast
      _ = 2*((q.num.natAbs : ℚ)/(q.den : ℚ)) := by ring
      _ = 2*q := congrArg (fun x : ℚ => 2*x) (positive_rat_natAbs_repr q (by linarith)).symm
  dsimp only [ceilLog2Q]
  rw [ite_eq_right (not_le_of_gt hq)]
  split_ifs with hc
  · rw [pow_succ]
    nlinarith
  · exact hlow

/-- Complete original `ceil_log2_power_upper` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_log2_power_upper (q : ℚ) : (2 : ℚ)^(ceilLog2Q q) ≤ 2*max 1 q := by
  by_cases hq : q ≤ 1
  · simp only [ceilLog2Q, ite_eq_left hq, pow_zero, max_eq_left hq]
    norm_num
  · rw [max_eq_right (lt_of_not_ge hq).le]
    exact (ceil_log2_power_lt_twice q (lt_of_not_ge hq)).le

#print axioms Qatlib.Concepts.SpinorSampling.Model.ceil_log2_power
#print axioms Qatlib.Concepts.SpinorSampling.Model.ceil_log2_power_upper
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section

/-- Complete original `ceil_nat_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_nat_cast (q : ℚ) (hq : 0 ≤ q) : (ceilNatQ q : ℝ)=(ceilIntQ q : ℝ) := by
  have hi : 0 ≤ ceilIntQ q := by rw [ceil_int_eq]; exact Int.ceil_nonneg hq
  have he : ((ceilNatQ q : ℕ) : ℤ)=ceilIntQ q := by
    exact Int.natCast_toNat_eq_self.mpr hi
  simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) he

/-- Complete original `ceil_nat_bounds` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_nat_bounds (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ≤ (ceilNatQ q : ℝ) ∧ (ceilNatQ q : ℝ) < (q : ℝ)+1 := by
  rw [ceil_nat_cast q hq, ceil_int_eq, ← Rat.ceil_cast (α := ℝ)]
  exact ⟨Int.le_ceil _, Int.ceil_lt_add_one _⟩

/-- Complete original `ceil_log2_log_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem ceil_log2_log_bound (q : ℚ) (hq : 0 < q) : Real.log (q : ℝ) ≤ (ceilLog2Q q : ℝ) := by
  have hp : (q : ℝ) ≤ (2 : ℝ)^(ceilLog2Q q) := by exact_mod_cast ceil_log2_power q
  have hqr : (0 : ℝ) < q := Rat.cast_pos.mpr hq
  have hl := Real.log_le_log hqr hp
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ (1 : ℝ) := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (ceilLog2Q q) : (0 : ℝ) ≤ ceilLog2Q q)
  exact hl.trans (by simpa only [mul_one] using hm)

/-- Complete original `median_blocks_ge_ceil` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem median_blocks_ge_ceil (ρ : ℚ) :
    ceilNatQ ((128/25 : ℚ)*(ceilLog2Q (1/ρ) : ℚ)) ≤ medianBlocksQ ρ := by
  dsimp only [medianBlocksQ]
  split_ifs <;> omega

/-- Complete original `median_blocks_pos` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem median_blocks_pos (ρ : ℚ) : 0 < medianBlocksQ ρ := by
  dsimp only [medianBlocksQ]
  split_ifs <;> omega

/-- Complete original `median_blocks_odd` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem median_blocks_odd (ρ : ℚ) : medianBlocksQ ρ%2=1 := by
  dsimp only [medianBlocksQ]
  split_ifs <;> omega

/-- Complete original `median_blocks_budget` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem median_blocks_budget (ρ : ℚ) (hρ : 0 < ρ) :
    (128/25 : ℝ)*Real.log (1/(ρ : ℝ)) ≤ (medianBlocksQ ρ : ℝ) := by
  have hq : 0 ≤ (128/25 : ℚ)*(ceilLog2Q (1/ρ) : ℚ) := by positivity
  have hc := (ceil_nat_bounds _ hq).1
  have hc' : (128/25 : ℝ)*(ceilLog2Q (1/ρ) : ℝ) ≤
      (ceilNatQ ((128/25 : ℚ)*(ceilLog2Q (1/ρ) : ℚ)) : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hc
  have hl : Real.log (1/(ρ : ℝ)) ≤ (ceilLog2Q (1/ρ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one] using ceil_log2_log_bound (1/ρ) (by positivity)
  have hn : (ceilNatQ ((128/25 : ℚ)*(ceilLog2Q (1/ρ) : ℚ)) : ℝ) ≤ (medianBlocksQ ρ : ℝ) := by
    exact_mod_cast median_blocks_ge_ceil ρ
  exact (mul_le_mul_of_nonneg_left hl (by norm_num)).trans (hc'.trans hn)

/-- Complete original `median_blocks_upper` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem median_blocks_upper (ρ : ℚ) :
    (medianBlocksQ ρ : ℝ) ≤ (128/25 : ℝ)*(ceilLog2Q (1/ρ) : ℝ)+2 := by
  let q : ℚ := (128/25 : ℚ)*(ceilLog2Q (1/ρ) : ℚ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hc := (ceil_nat_bounds q hq).2
  have hmax : ((max 1 (ceilNatQ q) : ℕ) : ℝ) ≤ (q : ℝ)+1 := by
    by_cases hh : 1 ≤ ceilNatQ q
    · rw [max_eq_right hh]; exact hc.le
    · rw [max_eq_left (by omega)]
      have hqr : (0 : ℝ) ≤ q := Rat.cast_nonneg.mpr hq
      norm_num
      linarith
  have hn : medianBlocksQ ρ ≤ max 1 (ceilNatQ q)+1 := by
    dsimp only [medianBlocksQ, q]
    split_ifs <;> omega
  have hnr : (medianBlocksQ ρ : ℝ) ≤ ((max 1 (ceilNatQ q) : ℕ) : ℝ)+1 := by exact_mod_cast hn
  have hlast : (medianBlocksQ ρ : ℝ) ≤ (q : ℝ)+2 := by linarith
  simpa only [q, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hlast

/-- Complete original `dyadic_root_square` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem dyadic_root_square (d r : ℕ) : 2^(d*r) ≤ (2^((d*r+1)/2))^2 := by
  rw [← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)

/-- Complete original `dyadic_root_bounds` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem dyadic_root_bounds (d r : ℕ) :
    Real.sqrt ((2^(d*r) : ℕ) : ℝ) ≤ ((2^((d*r+1)/2) : ℕ) : ℝ) := by
  have hs : ((2^(d*r) : ℕ) : ℝ) ≤ (((2^((d*r+1)/2) : ℕ) : ℝ))^2 := by exact_mod_cast dyadic_root_square d r
  have hx : (0 : ℝ) ≤ ((2^(d*r) : ℕ) : ℝ) := by positivity
  have hr : (0 : ℝ) ≤ ((2^((d*r+1)/2) : ℕ) : ℝ) := by positivity
  apply le_of_sq_le_sq _ hr
  rw [Real.sq_sqrt hx]
  exact hs

/-- Complete original `dyadic_scaled_root_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem dyadic_scaled_root_bound (d r : ℕ) (A : ℝ) :
    Real.sqrt (((2^(d*r) : ℕ) : ℝ)*A^4) ≤ A^2*((2^((d*r+1)/2) : ℕ) : ℝ) := by
  have hs : ((2^(d*r) : ℕ) : ℝ) ≤ (((2^((d*r+1)/2) : ℕ) : ℝ))^2 := by exact_mod_cast dyadic_root_square d r
  have hm := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ A^4)
  apply le_of_sq_le_sq _ (by positivity)
  rw [Real.sq_sqrt (by positivity)]
  nlinarith

#print axioms Qatlib.Concepts.SpinorSampling.Model.median_blocks_budget
#print axioms Qatlib.Concepts.SpinorSampling.Model.median_blocks_odd
#print axioms Qatlib.Concepts.SpinorSampling.Model.dyadic_scaled_root_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model

/-- Construction for block Records Q in the born current records model. -/
def blockRecordsQ (B rootD ε : ℚ) : ℕ := ceilNatQ (max 2 (max (32*B/ε^2) (8*rootD/ε)))

/-- Data and invariants for Sample Plan Q in the born current records model. -/
structure SamplePlanQ where
  velocityRecords : ℕ
  velocityBlocks : ℕ
  spinRecords : ℕ
  spinBlocks : ℕ
  copies : ℕ
  targetQueries : ℕ
  controlledShifts : ℕ
  deriving Repr

/-- Construction for sample Plan Q in the born current records model. -/
def samplePlanQ (d r : ℕ) (α β bound γ η δ : ℚ) : SamplePlanQ :=
  let rootM : ℚ := (2^((d*r+1)/2) : ℕ)
  let A := α+β*bound
  let εv := η/(4*(d : ℚ))
  let nv := blockRecordsQ (A^4) (A^2*rootM) εv
  let Kv := medianBlocksQ (δ/(2*(d : ℚ)))
  let vc := d*nv*Kv
  if γ=0 then
    { velocityRecords := nv, velocityBlocks := Kv, spinRecords := 0, spinBlocks := 0,
      copies := vc, targetQueries := vc, controlledShifts := vc }
  else
    let εs := min 1 (η/(12*(d : ℚ)*γ))
    let ns := blockRecordsQ 1 rootM εs
    let Ks := medianBlocksQ (δ/(6*(d : ℚ)))
    { velocityRecords := nv, velocityBlocks := Kv, spinRecords := ns, spinBlocks := Ks,
      copies := vc+3*d*ns*Ks, targetQueries := vc, controlledShifts := vc }

noncomputable section

/-- Complete original `block_records_guards` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem block_records_guards (B rootD ε : ℚ) :
    2 ≤ blockRecordsQ B rootD ε ∧
    32*(B : ℝ)/(ε : ℝ)^2 ≤ (blockRecordsQ B rootD ε : ℝ) ∧
    8*(rootD : ℝ)/(ε : ℝ) ≤ (blockRecordsQ B rootD ε : ℝ) := by
  let q := max 2 (max (32*B/ε^2) (8*rootD/ε))
  have hq0 : (0 : ℚ) ≤ q := (by norm_num : (0 : ℚ) ≤ 2).trans (le_max_left _ _)
  have hc := (ceil_nat_bounds q hq0).1
  have h2 : (2 : ℝ) ≤ (blockRecordsQ B rootD ε : ℝ) := by
    have h2q : (2 : ℚ) ≤ q := le_max_left _ _
    have hr : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast h2q
    exact hr.trans hc
  have hBq : 32*B/ε^2 ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hDq : 8*rootD/ε ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  have hB := (Rat.cast_le (K := ℝ)).mpr hBq
  have hD := (Rat.cast_le (K := ℝ)).mpr hDq
  have hBr : 32*(B : ℝ)/(ε : ℝ)^2 ≤ (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using hB
  have hDr : 8*(rootD : ℝ)/(ε : ℝ) ≤ (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat] using hD
  exact ⟨by exact_mod_cast h2, hBr.trans hc, hDr.trans hc⟩

/-- Complete original `block_records_sqrt_guard` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem block_records_sqrt_guard (B rootD ε : ℚ) (D : ℝ) (hε : 0 < ε)
    (hroot : Real.sqrt D ≤ (rootD : ℝ)) :
    8*Real.sqrt D/(ε : ℝ) ≤ (blockRecordsQ B rootD ε : ℝ) := by
  have hεr : (0 : ℝ) < ε := Rat.cast_pos.mpr hε
  have hm := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 8)
  exact (div_le_div_of_nonneg_right hm hεr.le).trans (block_records_guards B rootD ε).2.2

/-- Complete original `sample_plan_velocity_fields` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_velocity_fields (d r : ℕ) (α β bound γ η δ : ℚ) :
    (samplePlanQ d r α β bound γ η δ).velocityRecords=
      blockRecordsQ ((α+β*bound)^4) ((α+β*bound)^2*((2^((d*r+1)/2) : ℕ) : ℚ)) (η/(4*(d : ℚ))) ∧
    (samplePlanQ d r α β bound γ η δ).velocityBlocks=medianBlocksQ (δ/(2*(d : ℚ))) := by
  by_cases hg : γ=0 <;> simp [samplePlanQ, hg]

/-- Complete original `sample_plan_spin_fields` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_spin_fields (d r : ℕ) (α β bound γ η δ : ℚ) (hγ : γ ≠ 0) :
    (samplePlanQ d r α β bound γ η δ).spinRecords=
      blockRecordsQ 1 ((2^((d*r+1)/2) : ℕ) : ℚ) (min 1 (η/(12*(d : ℚ)*γ))) ∧
    (samplePlanQ d r α β bound γ η δ).spinBlocks=medianBlocksQ (δ/(6*(d : ℚ))) := by
  simp [samplePlanQ, hγ]

/-- Complete original `sample_plan_zero_spin` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_zero_spin (d r : ℕ) (α β bound η δ : ℚ) :
    (samplePlanQ d r α β bound 0 η δ).spinRecords=0 ∧
    (samplePlanQ d r α β bound 0 η δ).spinBlocks=0 := by simp [samplePlanQ]

/-- Complete original `sample_plan_accounts` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_accounts (d r : ℕ) (α β bound γ η δ : ℚ) :
    let p := samplePlanQ d r α β bound γ η δ
    p.copies=d*p.velocityRecords*p.velocityBlocks+3*d*p.spinRecords*p.spinBlocks ∧
    p.targetQueries=d*p.velocityRecords*p.velocityBlocks ∧
    p.controlledShifts=d*p.velocityRecords*p.velocityBlocks := by
  dsimp only
  by_cases hg : γ=0 <;> simp [samplePlanQ, hg]

#print axioms Qatlib.Concepts.SpinorSampling.Model.block_records_guards
#print axioms Qatlib.Concepts.SpinorSampling.Model.sample_plan_accounts
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section

/-- Complete original `sample_plan_velocity_guards` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_velocity_guards (d r : ℕ) (α β bound γ η δ : ℚ)
    (hd : 0 < d) (hη : 0 < η) (hδ : 0 < δ) :
    let p := samplePlanQ d r α β bound γ η δ
    2 ≤ p.velocityRecords ∧
    32*((α : ℝ)+(β : ℝ)*(bound : ℝ))^4/((η : ℝ)/(4*(d : ℝ)))^2 ≤ (p.velocityRecords : ℝ) ∧
    8*Real.sqrt (((2^(d*r) : ℕ) : ℝ)*((α : ℝ)+(β : ℝ)*(bound : ℝ))^4)/((η : ℝ)/(4*(d : ℝ))) ≤ (p.velocityRecords : ℝ) ∧
    0 < p.velocityBlocks ∧ p.velocityBlocks%2=1 ∧
    (128/25 : ℝ)*Real.log (1/((δ : ℝ)/(2*(d : ℝ)))) ≤ (p.velocityBlocks : ℝ) := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hε : (0 : ℚ) < η/(4*(d : ℚ)) := by positivity
  have hρ : (0 : ℚ) < δ/(2*(d : ℚ)) := by positivity
  have hf := sample_plan_velocity_fields d r α β bound γ η δ
  dsimp only
  rw [hf.1, hf.2]
  have hn := block_records_guards ((α+β*bound)^4) ((α+β*bound)^2*((2^((d*r+1)/2) : ℕ) : ℚ)) (η/(4*(d : ℚ)))
  have hroot : Real.sqrt (((2^(d*r) : ℕ) : ℝ)*((α : ℝ)+(β : ℝ)*(bound : ℝ))^4) ≤
      (((α+β*bound)^2*((2^((d*r+1)/2) : ℕ) : ℚ) : ℚ) : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast] using
      dyadic_scaled_root_bound d r ((α : ℝ)+(β : ℝ)*(bound : ℝ))
  have hD := block_records_sqrt_guard ((α+β*bound)^4) ((α+β*bound)^2*((2^((d*r+1)/2) : ℕ) : ℚ))
    (η/(4*(d : ℚ))) _ hε hroot
  have hB : 32*((α : ℝ)+(β : ℝ)*(bound : ℝ))^4/((η : ℝ)/(4*(d : ℝ)))^2 ≤
      (blockRecordsQ ((α+β*bound)^4) ((α+β*bound)^2*((2^((d*r+1)/2) : ℕ) : ℚ)) (η/(4*(d : ℚ))) : ℝ) := by
    simpa only [Rat.cast_pow, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hn.2.1
  have hD' : 8*Real.sqrt (((2^(d*r) : ℕ) : ℝ)*((α : ℝ)+(β : ℝ)*(bound : ℝ))^4)/((η : ℝ)/(4*(d : ℝ))) ≤
      (blockRecordsQ ((α+β*bound)^4) ((α+β*bound)^2*((2^((d*r+1)/2) : ℕ) : ℚ)) (η/(4*(d : ℚ))) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hD
  have hK := median_blocks_budget (δ/(2*(d : ℚ))) hρ
  refine ⟨hn.1, hB, hD', median_blocks_pos _, median_blocks_odd _, ?_⟩
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hK

/-- Complete original `sample_plan_spin_guards` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_spin_guards (d r : ℕ) (α β bound γ η δ : ℚ)
    (hd : 0 < d) (hγ : 0 < γ) (hη : 0 < η) (hδ : 0 < δ) :
    let p := samplePlanQ d r α β bound γ η δ
    2 ≤ p.spinRecords ∧
    32/(min 1 ((η : ℝ)/(12*(d : ℝ)*(γ : ℝ))))^2 ≤ (p.spinRecords : ℝ) ∧
    8*Real.sqrt ((2^(d*r) : ℕ) : ℝ)/(min 1 ((η : ℝ)/(12*(d : ℝ)*(γ : ℝ)))) ≤ (p.spinRecords : ℝ) ∧
    0 < p.spinBlocks ∧ p.spinBlocks%2=1 ∧
    (128/25 : ℝ)*Real.log (1/((δ : ℝ)/(6*(d : ℝ)))) ≤ (p.spinBlocks : ℝ) := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hε : (0 : ℚ) < min 1 (η/(12*(d : ℚ)*γ)) := by positivity
  have hρ : (0 : ℚ) < δ/(6*(d : ℚ)) := by positivity
  have hf := sample_plan_spin_fields d r α β bound γ η δ hγ.ne'
  dsimp only
  rw [hf.1, hf.2]
  have hn := block_records_guards 1 ((2^((d*r+1)/2) : ℕ) : ℚ) (min 1 (η/(12*(d : ℚ)*γ)))
  have hroot : Real.sqrt ((2^(d*r) : ℕ) : ℝ) ≤ (((2^((d*r+1)/2) : ℕ) : ℚ) : ℝ) := by
    simpa only [Rat.cast_natCast] using dyadic_root_bounds d r
  have hD := block_records_sqrt_guard 1 ((2^((d*r+1)/2) : ℕ) : ℚ) (min 1 (η/(12*(d : ℚ)*γ))) _ hε hroot
  have hB : 32/(min 1 ((η : ℝ)/(12*(d : ℝ)*(γ : ℝ))))^2 ≤
      (blockRecordsQ 1 ((2^((d*r+1)/2) : ℕ) : ℚ) (min 1 (η/(12*(d : ℚ)*γ))) : ℝ) := by
    simpa only [Rat.cast_one, mul_one, Rat.cast_min, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hn.2.1
  have hD' : 8*Real.sqrt ((2^(d*r) : ℕ) : ℝ)/(min 1 ((η : ℝ)/(12*(d : ℝ)*(γ : ℝ)))) ≤
      (blockRecordsQ 1 ((2^((d*r+1)/2) : ℕ) : ℚ) (min 1 (η/(12*(d : ℚ)*γ))) : ℝ) := by
    simpa only [Rat.cast_min, Rat.cast_one, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hD
  have hK := median_blocks_budget (δ/(6*(d : ℚ))) hρ
  refine ⟨hn.1, hB, hD', median_blocks_pos _, median_blocks_odd _, ?_⟩
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hK

#print axioms Qatlib.Concepts.SpinorSampling.Model.sample_plan_velocity_guards
#print axioms Qatlib.Concepts.SpinorSampling.Model.sample_plan_spin_guards
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model

/-- Construction for coefficient Threshold Q in the born current records model. -/
def coefficientThresholdQ (d N : ℕ) (κ lam U η : ℚ) : ℚ :=
  let t := precisionStepQ d ((N : ℚ)/6+(1/κ)*U) η
  let g := η/(64*(d : ℚ))
  max 1 (max ((N : ℚ)/(36*t)) (lam^2*(N : ℚ)^2/(216*g)))

/-- Construction for required Pi Bits Q in the born current records model. -/
def requiredPiBitsQ (d N : ℕ) (κ lam U η : ℚ) : ℕ := ceilLog2Q (coefficientThresholdQ d N κ lam U η)

/-- Construction for precision Doublings Q in the born current records model. -/
def precisionDoublingsQ (d N : ℕ) (κ lam U η : ℚ) : ℕ :=
  ceilLog2Q (max 1 ((requiredPiBitsQ d N κ lam U η : ℚ)/16))

/-- A bounded prefix of the unchanged while loop, not a replacement stopping rule. -/
def doublingLoopQ {T : Type*} (step : ℕ → Option T) : ℕ → ℕ → Option T
  | 0, _ => none
  | fuel+1, bits =>
      match step bits with
      | some c => some c
      | none => doublingLoopQ step fuel (bits*2)

/-- Construction for coefficient Loop Q in the born current records model. -/
def coefficientLoopQ (d N : ℕ) (κ lam U η : ℚ) (fuel bits : ℕ) : Option CoefficientCandidateQ :=
  doublingLoopQ (fun b => coefficientIterationQ d N b κ lam U η) fuel bits

/-- Construction for coefficients Generated Q in the born current records model. -/
def coefficientsGeneratedQ (d N : ℕ) (κ lam U η : ℚ) : Option CoefficientCandidateQ :=
  coefficientLoopQ d N κ lam U η (precisionDoublingsQ d N κ lam U η+1) 16

noncomputable section

/-- Complete original `precision_doubling_bounds` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem precision_doubling_bounds (n : ℕ) :
    n ≤ 16*2^(ceilLog2Q (max 1 ((n : ℚ)/16))) ∧
    16*2^(ceilLog2Q (max 1 ((n : ℚ)/16))) ≤ 2*max 16 n := by
  let q := max 1 ((n : ℚ)/16)
  let j := ceilLog2Q q
  have hp := ceil_log2_power q
  have hlo : (n : ℚ)/16 ≤ (2 : ℚ)^j := (le_max_right _ _).trans hp
  have hn : (n : ℚ) ≤ 16*(2 : ℚ)^j := by
    have he := (div_le_iff₀ (by norm_num : (0 : ℚ) < 16)).mp hlo
    nlinarith
  have hq : (1 : ℚ) ≤ q := le_max_left _ _
  have hu := ceil_log2_power_upper q
  rw [max_eq_right hq] at hu
  constructor
  · exact_mod_cast hn
  · by_cases hc : n ≤ 16
    · have hqr : (n : ℚ)/16 ≤ 1 := (div_le_one (by norm_num : (0 : ℚ) < 16)).mpr (by exact_mod_cast hc)
      have he : q ≤ 1 := max_le (by norm_num) hqr
      have hh : (16 : ℚ)*(2 : ℚ)^j ≤ (2 : ℚ)*16 := by nlinarith
      have hnat : 16*2^j ≤ 2*16 := by exact_mod_cast hh
      simpa only [max_eq_left hc] using hnat
    · have hcn : (16 : ℚ) ≤ n := by exact_mod_cast (by omega : 16 ≤ n)
      have hqr : (1 : ℚ) ≤ (n : ℚ)/16 := (one_le_div (by norm_num : (0 : ℚ) < 16)).mpr hcn
      have he : q ≤ (n : ℚ)/16 := max_le hqr (le_refl _)
      have hh : (16 : ℚ)*(2 : ℚ)^j ≤ (2 : ℚ)*(n : ℚ) := by nlinarith
      have hnat : 16*2^j ≤ 2*n := by exact_mod_cast hh
      simpa only [max_eq_right (by omega : 16 ≤ n)] using hnat

/-- Complete original `coefficient_iteration_ready` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_iteration_ready (d N bits : ℕ) (κ lam U η : ℚ)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hb : 1 ≤ bits)
    (hbits : requiredPiBitsQ d N κ lam U η ≤ bits) :
    coefficientIterationQ d N bits κ lam U η=some (coefficientCandidateQ d N bits κ lam U η) := by
  let t := precisionStepQ d ((N : ℚ)/6+(1/κ)*U) η
  let g := η/(64*(d : ℚ))
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have ht : 0 < t := by dsimp [t, precisionStepQ]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hlowA : (N : ℚ)/(36*t) ≤ coefficientThresholdQ d N κ lam U η :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hlowG : lam^2*(N : ℚ)^2/(216*g) ≤ coefficientThresholdQ d N κ lam U η :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hp : coefficientThresholdQ d N κ lam U η ≤ (2 : ℚ)^bits :=
    (ceil_log2_power _).trans (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hbits)
  have hA : (N : ℚ)/(36*(2 : ℚ)^bits) ≤ t := by
    have hnum := (div_le_iff₀ (by positivity : (0 : ℚ) < 36*t)).mp (hlowA.trans hp)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hG : lam^2*(N : ℚ)^2/(216*(2 : ℚ)^bits) ≤ g := by
    have hnum := (div_le_iff₀ (by positivity : (0 : ℚ) < 216*g)).mp (hlowG.trans hp)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hAR : (N : ℝ)/(36*(2 : ℝ)^bits) ≤ (t : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hA
  have hGR : (lam : ℝ)^2*(N : ℝ)^2/(216*(2 : ℝ)^bits) ≤ (g : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hG
  have hrates := coefficient_candidate_error_rates d N bits κ lam U η hb
  have hEA : (coefficientCandidateQ d N bits κ lam U η).alphaError ≤ t := Rat.cast_le.mp (hrates.1.trans hAR)
  have hEG : (coefficientCandidateQ d N bits κ lam U η).gammaError ≤ g := Rat.cast_le.mp (hrates.2.trans hGR)
  change (if (coefficientCandidateQ d N bits κ lam U η).alphaError ≤ t ∧
      (coefficientCandidateQ d N bits κ lam U η).gammaError ≤ g then _ else _) = _
  rw [ite_eq_left ⟨hEA,hEG⟩]

/-- Complete original `doubling_loop_reaches` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem doubling_loop_reaches {T : Type*} (step : ℕ → Option T) (k bits : ℕ)
    (hlast : ∃ c, step (bits*2^k)=some c) : ∃ c, doublingLoopQ step (k+1) bits=some c := by
  induction k generalizing bits with
  | zero =>
      obtain ⟨c,hc⟩ := hlast
      have hc' : step bits=some c := by simpa only [pow_zero, mul_one] using hc
      exact ⟨c, by simp only [doublingLoopQ, hc']⟩
  | succ k ih =>
      cases hs : step bits with
      | some c => exact ⟨c, by simp only [doublingLoopQ, hs]⟩
      | none =>
          have ht : ∃ c, step ((bits*2)*2^k)=some c := by
            simpa only [pow_succ', Nat.mul_assoc] using hlast
          obtain ⟨c,hc⟩ := ih (bits*2) ht
          exact ⟨c, by simpa only [doublingLoopQ, hs] using hc⟩

/-- Complete original `coefficient_loop_reaches` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_loop_reaches (d N : ℕ) (κ lam U η : ℚ) (k bits : ℕ)
    (hlast : ∃ c, coefficientIterationQ d N (bits*2^k) κ lam U η=some c) :
    ∃ c, coefficientLoopQ d N κ lam U η (k+1) bits=some c :=
  doubling_loop_reaches _ k bits hlast

/-- Complete original `coefficients_generated_total` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficients_generated_total (d N : ℕ) (κ lam U η : ℚ)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) :
    ∃ c, coefficientsGeneratedQ d N κ lam U η=some c := by
  let j := precisionDoublingsQ d N κ lam U η
  have hb := (precision_doubling_bounds (requiredPiBitsQ d N κ lam U η)).1
  have hpos : 1 ≤ 16*2^j := by
    have he : 0 < 16*2^j := by positivity
    omega
  have hready := coefficient_iteration_ready d N (16*2^j) κ lam U η hd hκ hU hη hpos hb
  exact coefficient_loop_reaches d N κ lam U η j 16 ⟨_,hready⟩

/-- Complete original `doubling_loop_trace` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem doubling_loop_trace {T : Type*} (step : ℕ → Option T) (fuel bits : ℕ) (c : T)
    (hc : doublingLoopQ step fuel bits=some c) :
    ∃ i, i < fuel ∧ step (bits*2^i)=some c := by
  induction fuel generalizing bits with
  | zero =>
      simp only [doublingLoopQ] at hc
      cases hc
  | succ fuel ih =>
      cases hs : step bits with
      | some v =>
          have hv : v=c := Option.some.inj (by simpa only [doublingLoopQ, hs] using hc)
          have hstep : step bits=some c := by rw [← hv]; exact hs
          exact ⟨0, by omega, by simpa only [pow_zero, mul_one] using hstep⟩
      | none =>
          have ht : doublingLoopQ step fuel (bits*2)=some c := by simpa only [doublingLoopQ, hs] using hc
          obtain ⟨i,hi,hstep⟩ := ih (bits*2) ht
          exact ⟨i+1, by omega, by simpa only [pow_succ', Nat.mul_assoc] using hstep⟩

/-- Complete original `coefficient_loop_trace` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficient_loop_trace (d N : ℕ) (κ lam U η : ℚ) (fuel bits : ℕ) (c : CoefficientCandidateQ)
    (hc : coefficientLoopQ d N κ lam U η fuel bits=some c) :
    ∃ i, i < fuel ∧ c.piBits=bits*2^i ∧ coefficientIterationQ d N (bits*2^i) κ lam U η=some c := by
  obtain ⟨i,hi,hstep⟩ := doubling_loop_trace _ fuel bits c hc
  have hEq := coefficient_iteration_result_eq d N (bits*2^i) κ lam U η c hstep
  have hmeta : c.piBits=bits*2^i := by simpa only [coefficientCandidateQ] using congrArg CoefficientCandidateQ.piBits hEq
  exact ⟨i,hi,hmeta,hstep⟩

/-- Complete original `coefficients_generated_bits_bound` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficients_generated_bits_bound (d N : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d N κ lam U η=some c) :
    1 ≤ c.piBits ∧ c.piBits ≤ 2*max 16 (requiredPiBitsQ d N κ lam U η) := by
  obtain ⟨i,hi,hm,_⟩ := coefficient_loop_trace d N κ lam U η _ 16 c hc
  have hij : i ≤ precisionDoublingsQ d N κ lam U η := by omega
  have hp : 16*2^i ≤ 16*2^(precisionDoublingsQ d N κ lam U η) :=
    Nat.mul_le_mul_left 16 (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hij)
  rw [hm]
  constructor
  · have he : 0 < 16*2^i := by positivity
    omega
  · exact hp.trans (precision_doubling_bounds _).2

#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficients_generated_total
#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficients_generated_bits_bound
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section

/-- Complete original `coefficients_generated_step` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficients_generated_step (d N : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d N κ lam U η=some c) :
    coefficientIterationQ d N c.piBits κ lam U η=some c := by
  obtain ⟨_,_,hm,hstep⟩ := coefficient_loop_trace d N κ lam U η _ 16 c hc
  simpa only [← hm] using hstep

/-- Complete original `coefficients_generated_valid` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficients_generated_valid (d N : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d N κ lam U η=some c) :
    |(c.alpha : ℝ)-1/(2*Real.pi/(N : ℝ))| ≤ (c.alphaError : ℝ) ∧
    |(c.gamma : ℝ)-(lam : ℝ)^2/(2*(2*Real.pi/(N : ℝ))^2)| ≤ (c.gammaError : ℝ) ∧
    (c.beta : ℝ)=1/(κ : ℝ) ∧
    (c.maxTargetError : ℝ)=(κ : ℝ)*precisionStep d ((N : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) ∧
    (c.alphaError : ℝ) ≤ precisionStep d ((N : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) ∧
    (c.gammaError : ℝ) ≤ (η : ℝ)/(64*(d : ℝ)) :=
  coefficient_iteration_valid d N c.piBits κ lam U η c (coefficients_generated_bits_bound d N κ lam U η c hc).1
    (coefficients_generated_step d N κ lam U η c hc)

/-- Complete original `coefficients_generated_legal` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem coefficients_generated_legal (d N : ℕ) (κ lam U η : ℚ) (c : CoefficientCandidateQ)
    (hd : 0 < d) (hN : 0 < N) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η)
    (hc : coefficientsGeneratedQ d N κ lam U η=some c) :
    0 < c.alpha ∧ 0 < c.beta ∧ 0 ≤ c.gamma ∧ (c.gamma=0 ↔ lam=0) ∧ 0 < c.maxTargetError := by
  have hb := (coefficients_generated_bits_bound d N κ lam U η c hc).1
  have hstep := coefficients_generated_step d N κ lam U η c hc
  have hEq := coefficient_iteration_result_eq d N c.piBits κ lam U η c hstep
  have ha := coefficient_candidate_alpha_pos d N c.piBits κ lam U η hN hb
  have hg := coefficient_candidate_gamma_nonneg d N c.piBits κ lam U η
  have hz := coefficient_candidate_gamma_zero_iff d N c.piBits κ lam U η hN hb
  have ht := coefficient_candidate_target_pos d N c.piBits κ lam U η hd hκ hU hη
  rw [← hEq] at ha hg hz ht
  have hbeta : c.beta=1/κ := by
    have he := congrArg CoefficientCandidateQ.beta hEq
    simpa only [coefficientCandidateQ] using he
  exact ⟨ha, by rw [hbeta]; positivity, hg, hz, ht⟩

#print axioms Qatlib.Concepts.SpinorSampling.Model.coefficients_generated_valid
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

set_option synthInstance.maxSize 1024 in
/-- Complete original `generated_plan_accuracy` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem generated_plan_accuracy {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : 0 < coef.gamma)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u û : Fin d → (Fin d → Fin (2^r)) → ℝ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |û j x-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    let mv := spinorCurrentMean a b c k e
    let ms := pauliField a b c k
    finiteBadMass (totalRecordLaw mv (spinor_current_mean_bound a b c k hz e) ms
      (fun i x => unit_spin_component_bound ms (pauli_field_unit a b c k hz) i x)
      p.velocityRecords p.velocityBlocks p.spinRecords p.spinBlocks)
      (totalMedianOutput û (periodicDoubleShift d (2^r)) (coef.alpha : ℝ) (coef.beta : ℝ) ((U+eb : ℚ) : ℝ) (coef.gamma : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ) := by
  let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
  have hv := coefficients_generated_valid d (2^r) κ lam U η coef hc
  have hl := coefficients_generated_legal d (2^r) κ lam U η coef hd (by positivity) hκ hU hη hc
  have hV := sample_plan_velocity_guards d r coef.alpha coef.beta (U+eb) coef.gamma η δ hd hη hδ
  have hS := sample_plan_spin_guards d r coef.alpha coef.beta (U+eb) coef.gamma η δ hd hγ hη hδ
  have hM : (2^r)^d=2^(d*r) := by rw [← Nat.pow_mul, Nat.mul_comm]
  have hB : 32*((coef.alpha : ℝ)+(1/(κ : ℝ))*((U : ℝ)+(eb : ℝ)))^4/((η : ℝ)/(4*(d : ℝ)))^2 ≤ (p.velocityRecords : ℝ) := by
    simpa only [Rat.cast_add, hv.2.2.1] using hV.2.1
  have hD : 8*Real.sqrt ((((2^r)^d : ℕ) : ℝ)*((coef.alpha : ℝ)+(1/(κ : ℝ))*((U : ℝ)+(eb : ℝ)))^4)/
      ((η : ℝ)/(4*(d : ℝ))) ≤ (p.velocityRecords : ℝ) := by
    simpa only [hM, Rat.cast_add, hv.2.2.1] using hV.2.2.1
  have hSD : 8*Real.sqrt (((2^r)^d : ℕ) : ℝ)/(min 1 ((η : ℝ)/(12*(d : ℝ)*(coef.gamma : ℝ)))) ≤ (p.spinRecords : ℝ) := by
    simpa only [hM] using hS.2.2.1
  have hEB : (eb : ℝ) ≤ (κ : ℝ)*precisionStep d (((2^r : ℕ) : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) := by
    rw [← hv.2.2.2.1]
    exact Rat.cast_le.mpr heb
  have hp := original_periodic_loss_confidence (nv := p.velocityRecords) (Kv := p.velocityBlocks)
    (ns := p.spinRecords) (Ks := p.spinBlocks) a b c k hz u û (κ : ℝ) (lam : ℝ) (coef.alpha : ℝ) (coef.gamma : ℝ)
    (U : ℝ) (coef.alphaError : ℝ) (eb : ℝ) (coef.gammaError : ℝ) (η : ℝ) (δ : ℝ)
    (Rat.cast_pos.mpr hκ) (Rat.cast_pos.mpr hl.1).le (Rat.cast_pos.mpr hγ) (Rat.cast_nonneg.mpr hU) (Rat.cast_nonneg.mpr heb0)
    hu htarget hv.1 hv.2.1 hv.2.2.2.2.1 hEB hv.2.2.2.2.2
    hd (Rat.cast_pos.mpr hη) (Rat.cast_pos.mpr hδ) hV.1 hS.1 hV.2.2.2.1 hS.2.2.2.1
    hB hD hS.2.1 hSD hV.2.2.2.2.2 hS.2.2.2.2.2
  simpa only [Rat.cast_add, hv.2.2.1] using hp

#print axioms Qatlib.Concepts.SpinorSampling.Model.generated_plan_accuracy
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

set_option synthInstance.maxSize 1024 in
/-- Complete original `generated_plan_accuracy_zero_spin` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem generated_plan_accuracy_zero_spin {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : coef.gamma=0)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u û : Fin d → (Fin d → Fin (2^r)) → ℝ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |û j x-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    finiteBadMass (velocityRecordLaw (spinorCurrentMean a b c k e) (spinor_current_mean_bound a b c k hz e)
      p.velocityRecords p.velocityBlocks)
      (velocityMedianOutput û (coef.alpha : ℝ) (coef.beta : ℝ) ((U+eb : ℚ) : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ)/2 := by
  let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
  have hv := coefficients_generated_valid d (2^r) κ lam U η coef hc
  have hl := coefficients_generated_legal d (2^r) κ lam U η coef hd (by positivity) hκ hU hη hc
  have hV := sample_plan_velocity_guards d r coef.alpha coef.beta (U+eb) coef.gamma η δ hd hη hδ
  have hM : Fintype.card (Fin d → Fin (2^r))=2^(d*r) := by rw [periodic_grid_card, ← Nat.pow_mul, Nat.mul_comm]
  have hB : 32*((coef.alpha : ℝ)+(1/(κ : ℝ))*((U : ℝ)+(eb : ℝ)))^4/((η : ℝ)/(4*(d : ℝ)))^2 ≤ (p.velocityRecords : ℝ) := by
    simpa only [Rat.cast_add, hv.2.2.1] using hV.2.1
  have hD : 8*Real.sqrt ((Fintype.card (Fin d → Fin (2^r)) : ℝ)*((coef.alpha : ℝ)+(1/(κ : ℝ))*((U : ℝ)+(eb : ℝ)))^4)/
      ((η : ℝ)/(4*(d : ℝ))) ≤ (p.velocityRecords : ℝ) := by
    simpa only [hM, Rat.cast_add, hv.2.2.1] using hV.2.2.1
  have hEB : (eb : ℝ) ≤ (κ : ℝ)*precisionStep d (((2^r : ℕ) : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (η : ℝ) := by
    rw [← hv.2.2.2.1]
    exact Rat.cast_le.mpr heb
  have hg : |0-(lam : ℝ)^2/(2*(2*Real.pi/((2^r : ℕ) : ℝ))^2)| ≤ (coef.gammaError : ℝ) := by
    simpa only [hγ, Rat.cast_zero] using hv.2.1
  have hh : (0 : ℝ) < 2*Real.pi/((2^r : ℕ) : ℝ) := by positivity
  have hκr : (0 : ℝ) < κ := Rat.cast_pos.mpr hκ
  have hUr : (0 : ℝ) ≤ U := Rat.cast_nonneg.mpr hU
  have hC : 1/(2*Real.pi/((2^r : ℕ) : ℝ))+(1/(κ : ℝ))*(U : ℝ) ≤
      ((2^r : ℕ) : ℝ)/6+(1/(κ : ℝ))*(U : ℝ) := add_le_add (inverse_mesh_rational_upper (2^r)) le_rfl
  have hC0 : (0 : ℝ) ≤ ((2^r : ℕ) : ℝ)/6+(1/(κ : ℝ))*(U : ℝ) := by positivity
  have hp := original_loss_confidence_zero_spin (nv := p.velocityRecords) (Kv := p.velocityBlocks)
    a b c k hz u û (periodicUnitShift d (2^r)) (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)
    (coef.alpha : ℝ) (U : ℝ) (((2^r : ℕ) : ℝ)/6+(1/(κ : ℝ))*(U : ℝ)) (coef.alphaError : ℝ) (eb : ℝ) (coef.gammaError : ℝ) (η : ℝ) (δ : ℝ)
    hh hκr (Rat.cast_pos.mpr hl.1).le hu htarget hv.1 hg hC hC0 (Rat.cast_nonneg.mpr heb0)
    hv.2.2.2.2.1 hEB hv.2.2.2.2.2 hd (Rat.cast_pos.mpr hη) (Rat.cast_pos.mpr hδ) hV.1 hV.2.2.2.1
    hB hD hV.2.2.2.2.2
  simpa only [Rat.cast_add, hv.2.2.1] using hp

#print axioms Qatlib.Concepts.SpinorSampling.Model.generated_plan_accuracy_zero_spin
end
end Qatlib.Concepts.SpinorSampling.Model


namespace Qatlib.Concepts.SpinorSampling.Model
open scoped BigOperators
variable {S : Type*} [DecidableEq S]

/-- Construction for record Sign Z in the born current records model. -/
def recordSignZ (b : Bool) : ℤ := if b then -1 else 1
/-- Abbreviation for Record Counts in the born current records model. -/
abbrev RecordCounts (S : Type*) := AList (fun _ : S => ℕ × ℤ)

/-- Construction for read Record Counts in the born current records model. -/
def readRecordCounts (c : RecordCounts S) (x : S) : ℕ × ℤ := (c.lookup x).getD (0, 0)
/-- Construction for update Record Counts in the born current records model. -/
def updateRecordCounts (c : RecordCounts S) (r : S × Bool) : RecordCounts S :=
  let old := readRecordCounts c r.1
  c.insert r.1 (old.1+1, old.2+recordSignZ r.2)
/-- Construction for collect Record Counts in the born current records model. -/
def collectRecordCounts (rs : List (S × Bool)) : RecordCounts S :=
  rs.foldl updateRecordCounts ∅

/-- Complete original `read_record_counts_update` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem read_record_counts_update (c : RecordCounts S) (r : S × Bool) (x : S) :
    readRecordCounts (updateRecordCounts c r) x =
      readRecordCounts c x + if r.1=x then (1, recordSignZ r.2) else (0, 0) := by
  by_cases h : r.1=x
  · subst x
    simp [updateRecordCounts, readRecordCounts]
    rfl
  · simp [updateRecordCounts, readRecordCounts, AList.lookup_insert_ne (Ne.symm h), h]

/-- Complete original `read_record_counts_fold` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem read_record_counts_fold (rs : List (S × Bool)) (c : RecordCounts S) (x : S) :
    readRecordCounts (rs.foldl updateRecordCounts c) x =
      readRecordCounts c x + (rs.map fun r => if r.1=x then (1, recordSignZ r.2) else (0, 0)).sum := by
  induction rs generalizing c with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, read_record_counts_update, add_assoc]

/-- Complete original `read_record_counts_collect` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem read_record_counts_collect (rs : List (S × Bool)) (x : S) :
    readRecordCounts (collectRecordCounts rs) x =
      (rs.map fun r => if r.1=x then (1, recordSignZ r.2) else (0, 0)).sum := by
  rw [collectRecordCounts, read_record_counts_fold]
  simp [readRecordCounts]

/-- Complete original `record_counts_mem_fold` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_mem_fold (rs : List (S × Bool)) (c : RecordCounts S) (x : S) :
    x ∈ rs.foldl updateRecordCounts c ↔ x ∈ c ∨ x ∈ rs.map Prod.fst := by
  induction rs generalizing c with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, ih, updateRecordCounts, AList.mem_insert, List.map_cons,
      List.mem_cons]
    tauto

/-- Complete original `record_counts_keys_collect` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_keys_collect (rs : List (S × Bool)) (x : S) :
    x ∈ (collectRecordCounts rs).keys ↔ x ∈ rs.map Prod.fst := by
  rw [← AList.mem_keys, collectRecordCounts, record_counts_mem_fold]
  simp

/-- Complete original `record_counts_keys_length` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_keys_length (rs : List (S × Bool)) (c : RecordCounts S) :
    (rs.foldl updateRecordCounts c).keys.length ≤ c.keys.length+rs.length := by
  induction rs generalizing c with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h := ih (updateRecordCounts c r)
    have hup : (updateRecordCounts c r).keys.length ≤ c.keys.length+1 := by
      have he := List.length_erase_le (l := c.keys) (a := r.1)
      simp only [updateRecordCounts, AList.keys_insert, List.length_cons]
      omega
    exact h.trans (by omega)

/-- Complete original `record_counts_query_quota` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_query_quota {n : ℕ} (r : Fin n → S × Bool) :
    (collectRecordCounts (List.ofFn r)).keys.length ≤ n := by
  simpa [collectRecordCounts] using record_counts_keys_length (List.ofFn r) (∅ : RecordCounts S)

/-- Complete original `record_counts_not_mem` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_not_mem (c : RecordCounts S) (x : S) (hx : x ∉ c.keys) :
    readRecordCounts c x = (0, 0) := by
  have h : c.lookup x = none := AList.lookup_eq_none.mpr (by simpa [AList.mem_keys] using hx)
  simp [readRecordCounts, h]

variable [Fintype S]

/-- Complete original `record_counts_sparse_sum` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_sparse_sum (c : RecordCounts S) (f : S → ℚ)
    (hf : ∀ x, x ∉ c.keys → f x=0) :
    (c.keys.map f).sum = ∑ x : S, f x := by
  rw [← List.sum_toFinset _ c.keys_nodup]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  exact hf x (by simpa using hx)

/-- Complete original `record_sign_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_sign_cast (b : Bool) : ((recordSignZ b : ℤ) : ℝ)=recordSign b := by
  cases b <;> norm_num [recordSignZ, recordSign]

omit [Fintype S] in
/-- Complete original `record_counts_real` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem record_counts_real {n : ℕ} (r : Fin n → S × Bool) (x : S) :
    (((readRecordCounts (collectRecordCounts (List.ofFn r)) x).1 : ℕ) : ℝ)=
        groupedRecordCount (fun i => (r i).1) x ∧
    (((readRecordCounts (collectRecordCounts (List.ofFn r)) x).2 : ℤ) : ℝ)=
        groupedRecordSum (fun i => (r i).1) (fun i => recordSign (r i).2) x := by
  rw [read_record_counts_collect]
  simp only [List.map_ofFn, List.sum_ofFn]
  constructor
  · rw [Prod.fst_sum, Nat.cast_sum]
    unfold groupedRecordCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (r i).1=x <;> simp [h]
  · rw [Prod.snd_sum, Int.cast_sum]
    unfold groupedRecordSum
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : (r i).1=x <;> simp [h, record_sign_cast]

/-- Construction for velocity Site Q in the born current records model. -/
def velocitySiteQ (c : RecordCounts S) (u : S → ℚ) (α β : ℚ) (x : S) : ℚ :=
  let k := readRecordCounts c x
  let ux := u x
  (α*(k.2 : ℚ)-β*(k.1 : ℚ)*ux)^2-
    (α^2*(k.1 : ℚ)-2*α*β*ux*(k.2 : ℚ)+β^2*ux^2*(k.1 : ℚ))

/-- Construction for velocity Statistic Q in the born current records model. -/
def velocityStatisticQ (M : ℕ) (rs : List (S × Bool)) (u : S → ℚ) (α β : ℚ) : ℚ :=
  let c := collectRecordCounts rs
  (M : ℚ)/(rs.length*(rs.length-1) : ℕ)*(c.keys.map (velocitySiteQ c u α β)).sum

/-- Construction for spin Site Q in the born current records model. -/
def spinSiteQ (c : RecordCounts S) (τ : S → S) (x : S) : ℚ :=
  let k := readRecordCounts c x
  (k.2 : ℚ)*((readRecordCounts c (τ x)).2 : ℚ)-if τ x=x then (k.1 : ℚ) else 0

/-- Construction for spin Statistic Q in the born current records model. -/
def spinStatisticQ (M : ℕ) (rs : List (S × Bool)) (τ : S → S) : ℚ :=
  let c := collectRecordCounts rs
  (M : ℚ)/(rs.length*(rs.length-1) : ℕ)*(c.keys.map (spinSiteQ c τ)).sum

omit [Fintype S] in
/-- Complete original `residual_grouped_sum_counts` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_grouped_sum_counts {n : ℕ} (r : Fin n → S × Bool)
    (u : S → ℝ) (α β : ℝ) (x : S) :
    groupedRecordSum (fun i => (r i).1) (fun i => α*recordSign (r i).2-β*u (r i).1) x =
      α*groupedRecordSum (fun i => (r i).1) (fun i => recordSign (r i).2) x-
        β*u x*groupedRecordCount (fun i => (r i).1) x := by
  unfold groupedRecordSum groupedRecordCount
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (r i).1=x <;> simp [h]

omit [Fintype S] in
/-- Complete original `residual_grouped_squares_counts` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem residual_grouped_squares_counts {n : ℕ} (r : Fin n → S × Bool)
    (u : S → ℝ) (α β : ℝ) (x : S) :
    groupedRecordSquares (fun i => (r i).1) (fun i => α*recordSign (r i).2-β*u (r i).1) x =
      α^2*groupedRecordCount (fun i => (r i).1) x-
        2*α*β*u x*groupedRecordSum (fun i => (r i).1) (fun i => recordSign (r i).2) x+
        β^2*(u x)^2*groupedRecordCount (fun i => (r i).1) x := by
  unfold groupedRecordSquares groupedRecordSum groupedRecordCount
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (r i).1=x
  · cases hq : (r i).2 <;> simp [h, recordSign, hq] <;> ring
  · simp [h]

/-- Complete original `velocity_statistic_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem velocity_statistic_cast {n : ℕ} (r : Fin n → S × Bool)
    (u : S → ℚ) (α β : ℚ) :
    (velocityStatisticQ (Fintype.card S) (List.ofFn r) u α β : ℝ)=
      residualStreamingStatistic (fun x => (u x : ℝ)) (α : ℝ) (β : ℝ) r := by
  have hz (x : S) (hx : x ∉ (collectRecordCounts (List.ofFn r)).keys) :
      velocitySiteQ (collectRecordCounts (List.ofFn r)) u α β x=0 := by
    simp [velocitySiteQ, record_counts_not_mem _ _ hx]
  rw [velocityStatisticQ, record_counts_sparse_sum _ _ hz]
  simp only [List.length_ofFn, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_sum]
  unfold residualStreamingStatistic
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [velocitySiteQ]
  push_cast
  rw [(record_counts_real r x).1, (record_counts_real r x).2,
    residual_grouped_sum_counts r (fun y => (u y : ℝ)) (α : ℝ) (β : ℝ),
    residual_grouped_squares_counts r (fun y => (u y : ℝ)) (α : ℝ) (β : ℝ)]
  ring

/-- Complete original `spin_statistic_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_statistic_cast {n : ℕ} (r : Fin n → S × Bool) (τ : S → S) :
    (spinStatisticQ (Fintype.card S) (List.ofFn r) τ : ℝ)=spinStreamingStatistic τ r := by
  have hz (x : S) (hx : x ∉ (collectRecordCounts (List.ofFn r)).keys) :
      spinSiteQ (collectRecordCounts (List.ofFn r)) τ x=0 := by
    simp [spinSiteQ, record_counts_not_mem _ _ hx]
  rw [spinStatisticQ, record_counts_sparse_sum _ _ hz]
  simp only [List.length_ofFn, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_sum]
  unfold spinStreamingStatistic
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [spinSiteQ]
  push_cast
  simp only [apply_ite, Rat.cast_natCast, Rat.cast_zero]
  rw [(record_counts_real r x).1, (record_counts_real r x).2,
    (record_counts_real r (τ x)).2]
  by_cases h : τ x=x <;> simp [h]

end Qatlib.Concepts.SpinorSampling.Model

namespace Qatlib.Concepts.SpinorSampling.Model
open scoped BigOperators

/-- Construction for median Q in the born current records model. -/
def medianQ {K : ℕ} (f : Fin K → ℚ) : ℚ :=
  ((List.ofFn f).mergeSort (· ≤ ·)).getD (K/2) 0

/-- Complete original `median_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem median_cast {K : ℕ} (f : Fin K → ℚ) :
    (medianQ f : ℝ)=((List.ofFn fun k => (f k : ℝ)).mergeSort (· ≤ ·)).getD (K/2) 0 := by
  have hsort : ((List.ofFn f).mergeSort (· ≤ ·)).map (fun q : ℚ => (q : ℝ))=
      (List.ofFn fun k => (f k : ℝ)).mergeSort (· ≤ ·) := by
    rw [List.map_mergeSort (s := fun a b : ℝ => decide (a ≤ b))]
    · rw [List.map_ofFn]
      congr 1
    · intro a _ b _
      simp only [Rat.cast_le]
  rw [medianQ, ← hsort]
  simpa only [Rat.cast_zero] using
    (List.getD_map ((List.ofFn f).mergeSort (· ≤ ·)) (0 : ℚ) (n := K/2) (fun q : ℚ => (q : ℝ))).symm

/-- Construction for interval Clip Q in the born current records model. -/
def intervalClipQ (lo hi x : ℚ) : ℚ := min hi (max lo x)

/-- Complete original `interval_clip_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem interval_clip_cast (lo hi x : ℚ) :
    (intervalClipQ lo hi x : ℝ)=intervalClip (lo : ℝ) (hi : ℝ) (x : ℝ) := by
  simp [intervalClipQ, intervalClip]

/-- Construction for combined Loss Q in the born current records model. -/
def combinedLossQ {d : ℕ} (A γ : ℚ) (v : Fin d → ℚ) (c : Fin 3 × Fin d → ℚ) : ℚ :=
  let V := ∑ j : Fin d, intervalClipQ 0 (A^2) (v j)
  if γ=0 then V else
    V+intervalClipQ 0 (2*(d : ℚ)*γ) (γ*((d : ℚ)-(∑ i : Fin 3 × Fin d, intervalClipQ (-1) 1 (c i))))

/-- Complete original `combined_loss_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem combined_loss_cast {d : ℕ} (A γ : ℚ) (v : Fin d → ℚ) (c : Fin 3 × Fin d → ℚ) :
    (combinedLossQ A γ v c : ℝ)=combinedLoss (A : ℝ) (γ : ℝ)
      (fun j => (v j : ℝ)) (fun i => (c i : ℝ)) := by
  by_cases hγ : γ=0
  · subst γ
    simp [combinedLossQ, combinedLoss, interval_clip_cast, intervalClip]
  · simp [combinedLossQ, hγ, combinedLoss, interval_clip_cast]
end Qatlib.Concepts.SpinorSampling.Model

namespace Qatlib.Concepts.SpinorSampling.Model
open scoped BigOperators

/-- Construction for raw Block Median Q in the born current records model. -/
def rawBlockMedianQ {X : Type*} {K : ℕ} (f : X → ℚ) (ω : Fin K → X) : ℚ :=
  medianQ (fun k => f (ω k))

/-- Complete original `raw_block_median_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem raw_block_median_cast {X : Type*} {K : ℕ} (f : X → ℚ) (ω : Fin K → X) :
    (rawBlockMedianQ f ω : ℝ)=rawBlockMedian (fun x => (f x : ℝ)) ω := median_cast _

variable {S : Type*} [DecidableEq S]

/-- Construction for total Median Output Q in the born current records model. -/
def totalMedianOutputQ {d nv Kv ns Ks : ℕ} (M : ℕ) (u : Fin d → S → ℚ)
    (e : Fin d → S → S) (α β U γ : ℚ) (z : TotalRecordData S d nv Kv ns Ks) : ℚ :=
  combinedLossQ (α+β*U) γ
    (fun j => rawBlockMedianQ (fun r => velocityStatisticQ M (List.ofFn r) (u j) α β) (z.1 j))
    (fun i => rawBlockMedianQ (fun r => spinStatisticQ M (List.ofFn r) (e i.2)) (z.2 i))

/-- Construction for velocity Only Output Q in the born current records model. -/
def velocityOnlyOutputQ {d nv Kv : ℕ} (M : ℕ) (u : Fin d → S → ℚ) (α β U : ℚ)
    (z : Fin d → Fin Kv → Fin nv → S × Bool) : ℚ :=
  ∑ j : Fin d, intervalClipQ 0 ((α+β*U)^2)
    (rawBlockMedianQ (fun r => velocityStatisticQ M (List.ofFn r) (u j) α β) (z j))

variable [Fintype S]

/-- Complete original `total_median_output_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem total_median_output_cast {d nv Kv ns Ks : ℕ} (u : Fin d → S → ℚ)
    (e : Fin d → S ≃ S) (α β U γ : ℚ) (z : TotalRecordData S d nv Kv ns Ks) :
    (totalMedianOutputQ (Fintype.card S) u (fun j => e j) α β U γ z : ℝ)=
      totalMedianOutput (fun j x => (u j x : ℝ)) e (α : ℝ) (β : ℝ) (U : ℝ) (γ : ℝ) z := by
  simp only [totalMedianOutputQ, combined_loss_cast, raw_block_median_cast]
  simp_rw [velocity_statistic_cast, spin_statistic_cast]
  simp only [Rat.cast_add, Rat.cast_mul, totalMedianOutput]

/-- Complete original `velocity_only_output_cast` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem velocity_only_output_cast {d nv Kv : ℕ} (u : Fin d → S → ℚ) (α β U : ℚ)
    (z : Fin d → Fin Kv → Fin nv → S × Bool) :
    (velocityOnlyOutputQ (Fintype.card S) u α β U z : ℝ)=
      ∑ j : Fin d, intervalClip 0 (((α : ℝ)+(β : ℝ)*(U : ℝ))^2)
        (rawBlockMedian (residualStreamingStatistic (fun x => (u j x : ℝ)) (α : ℝ) (β : ℝ)) (z j)) := by
  simp only [velocityOnlyOutputQ, Rat.cast_sum, interval_clip_cast, Rat.cast_zero,
    Rat.cast_pow, Rat.cast_add, Rat.cast_mul, raw_block_median_cast]
  simp_rw [velocity_statistic_cast]
end Qatlib.Concepts.SpinorSampling.Model

namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

set_option synthInstance.maxSize 1024 in
/-- Complete original `executed_plan_accuracy` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem executed_plan_accuracy {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : 0 < coef.gamma)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    let mv := spinorCurrentMean a b c k e
    let ms := pauliField a b c k
    finiteBadMass (totalRecordLaw mv (spinor_current_mean_bound a b c k hz e) ms
      (fun i x => unit_spin_component_bound ms (pauli_field_unit a b c k hz) i x)
      p.velocityRecords p.velocityBlocks p.spinRecords p.spinBlocks)
      (fun z => (totalMedianOutputQ (2^(d*r)) û (fun j => periodicDoubleShift d (2^r) j) coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ) := by
  let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
  have hM : Fintype.card (Fin d → Fin (2^r))=2^(d*r) := by rw [periodic_grid_card, ← Nat.pow_mul, Nat.mul_comm]
  have hout (z : TotalRecordData (Fin d → Fin (2^r)) d p.velocityRecords p.velocityBlocks p.spinRecords p.spinBlocks) : (totalMedianOutputQ (2^(d*r)) û (fun j => periodicDoubleShift d (2^r) j) coef.alpha coef.beta (U+eb) coef.gamma z : ℝ)=totalMedianOutput (fun j x => (û j x : ℝ)) (periodicDoubleShift d (2^r)) (coef.alpha : ℝ) (coef.beta : ℝ) ((U+eb : ℚ) : ℝ) (coef.gamma : ℝ) z := by simpa only [hM] using total_median_output_cast û (periodicDoubleShift d (2^r)) coef.alpha coef.beta (U+eb) coef.gamma z
  dsimp only
  simp_rw [hout]
  exact generated_plan_accuracy κ lam U η δ eb coef hc hd hκ hU hη hδ heb0 heb hγ a b c k hz u (fun j x => (û j x : ℝ)) hu htarget

#print axioms Qatlib.Concepts.SpinorSampling.Model.executed_plan_accuracy
end
end Qatlib.Concepts.SpinorSampling.Model

namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

set_option synthInstance.maxSize 1024 in
/-- Complete original `executed_plan_accuracy_zero_spin` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem executed_plan_accuracy_zero_spin {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : coef.gamma=0)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    finiteBadMass (velocityRecordLaw (spinorCurrentMean a b c k e) (spinor_current_mean_bound a b c k hz e)
      p.velocityRecords p.velocityBlocks)
      (fun z => (velocityOnlyOutputQ (2^(d*r)) û coef.alpha coef.beta (U+eb) z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ)/2 := by
  let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
  have hM : Fintype.card (Fin d → Fin (2^r))=2^(d*r) := by rw [periodic_grid_card, ← Nat.pow_mul, Nat.mul_comm]
  have hout (z : Fin d → Fin p.velocityBlocks → Fin p.velocityRecords → (Fin d → Fin (2^r)) × Bool) : (velocityOnlyOutputQ (2^(d*r)) û coef.alpha coef.beta (U+eb) z : ℝ)=velocityMedianOutput (fun j x => (û j x : ℝ)) (coef.alpha : ℝ) (coef.beta : ℝ) ((U+eb : ℚ) : ℝ) z := by simpa only [hM, velocityMedianOutput] using velocity_only_output_cast û coef.alpha coef.beta (U+eb) z
  dsimp only
  simp_rw [hout]
  exact generated_plan_accuracy_zero_spin κ lam U η δ eb coef hc hd hκ hU hη hδ heb0 heb hγ a b c k hz u (fun j x => (û j x : ℝ)) hu htarget

#print axioms Qatlib.Concepts.SpinorSampling.Model.executed_plan_accuracy_zero_spin
end
end Qatlib.Concepts.SpinorSampling.Model

#print axioms Qatlib.Concepts.SpinorSampling.Model.read_record_counts_fold

#print axioms Qatlib.Concepts.SpinorSampling.Model.read_record_counts_collect

#print axioms Qatlib.Concepts.SpinorSampling.Model.record_counts_keys_collect

#print axioms Qatlib.Concepts.SpinorSampling.Model.record_counts_query_quota

#print axioms Qatlib.Concepts.SpinorSampling.Model.record_counts_real

#print axioms Qatlib.Concepts.SpinorSampling.Model.velocity_statistic_cast

#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_statistic_cast

#print axioms Qatlib.Concepts.SpinorSampling.Model.median_cast

#print axioms Qatlib.Concepts.SpinorSampling.Model.combined_loss_cast

#print axioms Qatlib.Concepts.SpinorSampling.Model.total_median_output_cast

#print axioms Qatlib.Concepts.SpinorSampling.Model.velocity_only_output_cast

namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

/-- Literal H and S† on the readout qubit; A contains all other wires. -/
def readoutH {A : Type*} (f : Bool → A → ℂ) (b : Bool) (x : A) : ℂ :=
  (f false x + (if b then -1 else 1)*f true x)/(Real.sqrt 2 : ℂ)

/-- Construction for readout Sdg in the born current records model. -/
def readoutSdg {A : Type*} (f : Bool → A → ℂ) (b : Bool) (x : A) : ℂ :=
  (if b then -Complex.I else 1)*f b x

/-- Complete original `readout_h_apply_gate` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem readout_h_apply_gate {A : Type*} (f : Bool → A → ℂ) (b : Bool) (x : A) :
    readoutH f b x = ApplyGate Hadamard (fun q => f q x) b := by
  cases b <;> simp [readoutH, ApplyGate, Hadamard, Matrix.mulVec,
    dotProduct, div_eq_mul_inv] <;> ring

/-- Construction for readout Sdg Matrix in the born current records model. -/
def readoutSdgMatrix : Matrix Bool Bool ℂ :=
  Matrix.diagonal (fun b => if b then -Complex.I else 1)

/-- Complete original `readout_sdg_apply_gate` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem readout_sdg_apply_gate {A : Type*} (f : Bool → A → ℂ) (b : Bool) (x : A) :
    readoutSdg f b x = ApplyGate readoutSdgMatrix (fun q => f q x) b := by
  simp [readoutSdg, ApplyGate, readoutSdgMatrix, Matrix.mulVec_diagonal]

/-- Basis permutation p acts by pullback p⁻¹ on amplitudes, on the true branch. -/
def controlledSite {S : Type*} (p : S ≃ S)
    (f : Bool → S × Bool → ℂ) (b : Bool) (x : S × Bool) : ℂ :=
  f b (if b then (p.symm x.1,x.2) else x)

/-- Construction for controlled Site Basis in the born current records model. -/
def controlledSiteBasis {S : Type*} (p : S ≃ S) :
    Bool × (S × Bool) ≃ Bool × (S × Bool) where
  toFun r := (r.1,if r.1 then (p r.2.1,r.2.2) else r.2)
  invFun r := (r.1,if r.1 then (p.symm r.2.1,r.2.2) else r.2)
  left_inv r := by rcases r with ⟨b,x,spin⟩; cases b <;> simp
  right_inv r := by rcases r with ⟨b,x,spin⟩; cases b <;> simp

-- This uses p⁻¹, not an involutive-permutation lemma: N>=8 shifts need it.
/-- Complete original `controlled_site_apply_gate` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem controlled_site_apply_gate {S : Type*} [Fintype S] [DecidableEq S]
    (p : S ≃ S) (f : Bool → S × Bool → ℂ) (b : Bool) (x : S × Bool) :
    ApplyGate (permMatrix (controlledSiteBasis p)) (fun r => f r.1 r.2) (b,x) =
      controlledSite p f b x := by
  unfold ApplyGate permMatrix Matrix.mulVec dotProduct
  rw [Finset.sum_eq_single ((controlledSiteBasis p).symm (b,x))]
  · cases b <;> simp [controlledSiteBasis, controlledSite]
  · intro j _ hj
    have hne : (b,x) ≠ controlledSiteBasis p j := by
      intro h
      exact hj (by simpa using (congrArg (controlledSiteBasis p).symm h).symm)
    simp [hne]
  · simp

/-- Construction for complex Spinor in the born current records model. -/
def complexSpinor {S : Type*} (a b c k : S → ℝ) (x : S) (spin : Bool) : ℂ :=
  if spin then ⟨c x,k x⟩ else ⟨a x,b x⟩

/-- Construction for supplied Spin State in the born current records model. -/
def suppliedSpinState {S : Type*} [Fintype S] (a b c k : S → ℝ)
    (spin : Bool) (x : S) : ℂ :=
  complexSpinor a b c k x spin/(Real.sqrt (Fintype.card S : ℝ) : ℂ)

/-- Construction for supplied Ancilla State in the born current records model. -/
def suppliedAncillaState {S : Type*} [Fintype S] (a b c k : S → ℝ)
    (test : Bool) (x : S × Bool) : ℂ :=
  if test then 0 else suppliedSpinState a b c k x.2 x.1

/-- e is the neighbor map: the emitted basis shift is e⁻¹. -/
def velocityGateState {S : Type*} [Fintype S] (a b c k : S → ℝ) (e : S ≃ S) :
    Bool → S × Bool → ℂ :=
  readoutH (readoutSdg (controlledSite e.symm (readoutH (suppliedAncillaState a b c k))))

/-- Complete original `velocity_gate_amplitude` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem velocity_gate_amplitude {S : Type*} [Fintype S]
    (a b c k : S → ℝ) (e : S ≃ S) (test : Bool) (x : S) (spin : Bool) :
    velocityGateState a b c k e test (x,spin) =
      (complexSpinor a b c k x spin - Complex.I*(recordSign test : ℂ)*
        complexSpinor a b c k (e x) spin)/
        (2*(Real.sqrt (Fintype.card S : ℝ) : ℂ)) := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  cases test <;>
    simp only [velocityGateState, readoutH, readoutSdg, controlledSite,
      suppliedAncillaState, suppliedSpinState, recordSign,
      Bool.false_eq_true, ite_false, ite_true, Equiv.symm_symm, Complex.ofReal_one,
      Complex.ofReal_neg, mul_zero, add_zero, one_mul] <;>
    field_simp [hn] <;> ring_nf <;> simp only [hs]

/-- Complete original `norm_sq_y_interference` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem norm_sq_y_interference (z w : ℂ) (y : ℝ) :
    Complex.normSq (z-Complex.I*(y : ℂ)*w) =
      Complex.normSq z+y^2*Complex.normSq w+2*y*(starRingEnd ℂ z*w).im := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Construction for velocity Born Mass in the born current records model. -/
def velocityBornMass {S : Type*} [Fintype S] (a b c k : S → ℝ)
    (e : S ≃ S) (r : S × Bool) : ℝ :=
  ∑ spin : Bool, BornProb (velocityGateState a b c k e r.2) (r.1,spin)

/-- Complete original `velocity_born_mass` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem velocity_born_mass {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (e : S ≃ S) (r : S × Bool) :
    velocityBornMass a b c k e r =
      signedRecordWeight (fun x => spinorInnerIm a b c k x (e x)) r := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hden : Complex.normSq (2*(Real.sqrt (Fintype.card S : ℝ) : ℂ)) =
      4*(Fintype.card S : ℝ) := by
    rw [Complex.normSq_mul]
    norm_num [Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [velocityBornMass, BornProb, Complex.sq_norm, velocity_gate_amplitude,
    Complex.normSq_div, hden, norm_sq_y_interference, Fintype.sum_bool]
  cases r with
  | mk x test =>
    have hx := hz x
    have he := hz (e x)
    cases test <;>
      simp only [complexSpinor, signedRecordWeight, recordSign, spinorInnerIm,
        Bool.false_eq_true, ite_false, ite_true, Complex.normSq_apply,
        Complex.mul_im, Complex.conj_re, Complex.conj_im] <;>
      field_simp <;> nlinarith

/-- Fair R is external classical randomness; R=-1 flips the observed sign. -/
def currentBornMass {S : Type*} [Fintype S] (a b c k : S → ℝ)
    (e : S ≃ S) (r : S × Bool) : ℝ :=
  (velocityBornMass a b c k e r + velocityBornMass a b c k e.symm (r.1,!r.2))/2

/-- Complete original `current_born_mass` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem current_born_mass {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (e : S ≃ S) (r : S × Bool) :
    currentBornMass a b c k e r =
      signedRecordWeight (fun x =>
        (spinorInnerIm a b c k x (e x)-spinorInnerIm a b c k x (e.symm x))/2) r := by
  rw [currentBornMass, velocity_born_mass a b c k hz, velocity_born_mass a b c k hz]
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rcases r with ⟨x,test⟩
  cases test <;> simp only [signedRecordWeight, recordSign, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ite_false, ite_true] <;>
    field_simp <;> ring

/-- Construction for spin Gate State in the born current records model. -/
def spinGateState {S : Type*} [Fintype S] (a b c k : S → ℝ) (p : Fin 3) :
    Bool → S → ℂ :=
  if p=0 then readoutH (suppliedSpinState a b c k) else
    if p=1 then readoutH (readoutSdg (suppliedSpinState a b c k)) else
      suppliedSpinState a b c k

/-- Construction for spin Born Mass in the born current records model. -/
def spinBornMass {S : Type*} [Fintype S] (a b c k : S → ℝ)
    (p : Fin 3) (r : S × Bool) : ℝ :=
  BornProb (spinGateState a b c k p r.2) r.1

/-- Complete original `spin_born_mass` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_born_mass {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (p : Fin 3) (r : S × Bool) :
    spinBornMass a b c k p r = signedRecordWeight (pauliField a b c k p) r := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rcases r with ⟨x,test⟩
  have hx := hz x
  unfold spinBornMass BornProb
  rw [Complex.sq_norm]
  fin_cases p <;> cases test <;>
    simp [spinGateState, suppliedSpinState, complexSpinor,
      readoutH, readoutSdg, signedRecordWeight, recordSign, pauliField,
      ← mul_div_assoc, ← add_div, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card S)),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] <;>
    field_simp [hM] <;> nlinarith

/-- Complete original `supplied_spin_state_normalized` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem supplied_spin_state_normalized {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    Normalized (fun r : S × Bool => suppliedSpinState a b c k r.2 r.1) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hden : Complex.normSq (Real.sqrt (Fintype.card S : ℝ) : ℂ) =
      (Fintype.card S : ℝ) := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hsite (x : S) : (∑ spin : Bool, Complex.normSq (complexSpinor a b c k x spin))=1 := by
    simpa [Fintype.sum_bool, complexSpinor, Complex.normSq_apply, pow_two, add_comm, add_left_comm,
      add_assoc] using hz x
  simp only [Normalized, Fintype.sum_prod_type, Complex.sq_norm, suppliedSpinState,
    Complex.normSq_div, hden, ← Finset.sum_div, hsite]
  simp [nsmul_eq_mul, hM]

/-- Complete original `velocity_gate_state_normalized` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem velocity_gate_state_normalized {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (e : S ≃ S) :
    Normalized (fun r : S × (Bool × Bool) => velocityGateState a b c k e r.2.1 (r.1,r.2.2)) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Normalized
  simp only [Fintype.sum_prod_type]
  change (∑ x : S, ∑ test : Bool, velocityBornMass a b c k e (x,test))=1
  simp_rw [velocity_born_mass a b c k hz, signed_record_cell_mass]
  simp [nsmul_eq_mul, hM]

/-- Complete original `spin_gate_state_normalized` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_gate_state_normalized {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (p : Fin 3) :
    Normalized (fun r : S × Bool => spinGateState a b c k p r.2 r.1) := by
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Normalized
  rw [Fintype.sum_prod_type]
  change (∑ x : S, ∑ test : Bool, spinBornMass a b c k p (x,test))=1
  simp_rw [spin_born_mass a b c k hz, signed_record_cell_mass]
  simp [nsmul_eq_mul, hM]

/-- Construction for current Circuit Law in the born current records model. -/
def currentCircuitLaw {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (e : S ≃ S) :
    FinDist (S × Bool) where
  prob := currentBornMass a b c k e
  nonneg r := by
    unfold currentBornMass velocityBornMass BornProb
    positivity
  sum_one := by
    simp_rw [current_born_mass a b c k hz]
    rw [Fintype.sum_prod_type]
    simp_rw [signed_record_cell_mass]
    have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [nsmul_eq_mul, hM]

/-- Construction for spin Circuit Law in the born current records model. -/
def spinCircuitLaw {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (p : Fin 3) :
    FinDist (S × Bool) where
  prob := spinBornMass a b c k p
  nonneg r := sq_nonneg _
  sum_one := by
    simp_rw [spin_born_mass a b c k hz]
    rw [Fintype.sum_prod_type]
    simp_rw [signed_record_cell_mass]
    have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [nsmul_eq_mul, hM]

/-- Complete original `circuit_record_law_ext` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
private theorem circuit_record_law_ext {X : Type*} [Fintype X] (p q : FinDist X)
    (h : ∀ x, p.prob x=q.prob x) : p=q := by
  cases p with
  | mk p hp hs =>
    cases q with
    | mk q hq ht =>
      have he : p=q := funext h
      subst q
      rfl

/-- Complete original `current_circuit_law_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem current_circuit_law_eq {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (e : S ≃ S)
    (hm : ∀ x, |(spinorInnerIm a b c k x (e x)-spinorInnerIm a b c k x (e.symm x))/2| ≤ 1) :
    currentCircuitLaw a b c k hz e = signedRecordLaw
      (fun x => (spinorInnerIm a b c k x (e x)-spinorInnerIm a b c k x (e.symm x))/2) hm := by
  apply circuit_record_law_ext
  exact current_born_mass a b c k hz e

/-- Complete original `spin_circuit_law_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem spin_circuit_law_eq {S : Type*} [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) (p : Fin 3)
    (hm : ∀ x, |pauliField a b c k p x| ≤ 1) :
    spinCircuitLaw a b c k hz p = signedRecordLaw (pauliField a b c k p) hm := by
  apply circuit_record_law_ext
  exact spin_born_mass a b c k hz p

/-- Complete fresh-copy cohorts use the Born masses above, not assumed means. -/
def circuitTotalRecordLaw {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (e : Fin d → S ≃ S) (nv Kv ns Ks : ℕ) :
    FinDist (TotalRecordData S d nv Kv ns Ks) :=
  independentPairLaw
    (finiteFamilyLaw (fun j => cohortLaw (cohortLaw (currentCircuitLaw a b c k hz (e j)) nv) Kv))
    (finiteFamilyLaw (fun i : Fin 3 × Fin d =>
      cohortLaw (cohortLaw (spinCircuitLaw a b c k hz i.1) ns) Ks))

/-- Complete original `circuit_total_record_law_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem circuit_total_record_law_eq {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (e : Fin d → S ≃ S) (nv Kv ns Ks : ℕ) :
    circuitTotalRecordLaw a b c k hz e nv Kv ns Ks =
      totalRecordLaw (spinorCurrentMean a b c k e) (spinor_current_mean_bound a b c k hz e)
        (pauliField a b c k) (fun i x =>
          unit_spin_component_bound (pauliField a b c k) (pauli_field_unit a b c k hz) i x)
        nv Kv ns Ks := by
  have hv (j : Fin d) := current_circuit_law_eq a b c k hz (e j)
    (spinor_current_mean_bound a b c k hz e j)
  have hs (i : Fin 3) := spin_circuit_law_eq a b c k hz i
    (unit_spin_component_bound (pauliField a b c k) (pauli_field_unit a b c k hz) i)
  simp only [circuitTotalRecordLaw, totalRecordLaw, hv, hs]
  rfl

/-- Construction for circuit Velocity Record Law in the born current records model. -/
def circuitVelocityRecordLaw {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (e : Fin d → S ≃ S) (nv Kv : ℕ) :
    FinDist (Fin d → Fin Kv → Fin nv → S × Bool) :=
  finiteFamilyLaw (fun j => cohortLaw (cohortLaw (currentCircuitLaw a b c k hz (e j)) nv) Kv)

/-- Complete original `circuit_velocity_record_law_eq` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem circuit_velocity_record_law_eq {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    {d : ℕ} (a b c k : S → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (e : Fin d → S ≃ S) (nv Kv : ℕ) :
    circuitVelocityRecordLaw a b c k hz e nv Kv =
      velocityRecordLaw (spinorCurrentMean a b c k e) (spinor_current_mean_bound a b c k hz e) nv Kv := by
  have hv (j : Fin d) := current_circuit_law_eq a b c k hz (e j)
    (spinor_current_mean_bound a b c k hz e j)
  simp only [circuitVelocityRecordLaw, velocityRecordLaw, hv]
  rfl

end
end Qatlib.Concepts.SpinorSampling.Model

namespace Qatlib.Concepts.SpinorSampling.Model
noncomputable section
open scoped BigOperators
open Qatlib

set_option synthInstance.maxSize 1024 in
/-- Complete original `circuit_executed_plan_accuracy` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem circuit_executed_plan_accuracy {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : 0 < coef.gamma)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    finiteBadMass (circuitTotalRecordLaw a b c k hz e p.velocityRecords p.velocityBlocks p.spinRecords p.spinBlocks)
      (fun z => (totalMedianOutputQ (2^(d*r)) û (fun j => periodicDoubleShift d (2^r) j) coef.alpha coef.beta (U+eb) coef.gamma z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ) := by
  simpa only [circuit_total_record_law_eq] using
    executed_plan_accuracy κ lam U η δ eb coef hc hd hκ hU hη hδ heb0 heb hγ a b c k hz u û hu htarget

set_option synthInstance.maxSize 1024 in
/-- Complete original `circuit_executed_plan_accuracy_zero_spin` guarantee for `BornCurrentRecords`; all source hypotheses and output obligations are retained. -/
theorem circuit_executed_plan_accuracy_zero_spin {d r : ℕ} (κ lam U η δ eb : ℚ) (coef : CoefficientCandidateQ)
    (hc : coefficientsGeneratedQ d (2^r) κ lam U η=some coef)
    (hd : 0 < d) (hκ : 0 < κ) (hU : 0 ≤ U) (hη : 0 < η) (hδ : 0 < δ)
    (heb0 : 0 ≤ eb) (heb : eb ≤ coef.maxTargetError) (hγ : coef.gamma=0)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1)
    (u : Fin d → (Fin d → Fin (2^r)) → ℝ) (û : Fin d → (Fin d → Fin (2^r)) → ℚ)
    (hu : ∀ j x, |u j x| ≤ (U : ℝ)) (htarget : ∀ j x, |(û j x : ℝ)-u j x| ≤ (eb : ℝ)) :
    let p := samplePlanQ d r coef.alpha coef.beta (U+eb) coef.gamma η δ
    let e := periodicUnitShift d (2^r)
    finiteBadMass (circuitVelocityRecordLaw a b c k hz e p.velocityRecords p.velocityBlocks)
      (fun z => (velocityOnlyOutputQ (2^(d*r)) û coef.alpha coef.beta (U+eb) z : ℝ))
      (spinorDiscreteLoss a b c k u e (2*Real.pi/((2^r : ℕ) : ℝ)) (κ : ℝ) (lam : ℝ)) (η : ℝ) ≤ (δ : ℝ)/2 := by
  simpa only [circuit_velocity_record_law_eq] using
    executed_plan_accuracy_zero_spin κ lam U η δ eb coef hc hd hκ hU hη hδ heb0 heb hγ a b c k hz u û hu htarget

end
end Qatlib.Concepts.SpinorSampling.Model

#print axioms Qatlib.Concepts.SpinorSampling.Model.readout_h_apply_gate
#print axioms Qatlib.Concepts.SpinorSampling.Model.readout_sdg_apply_gate
#print axioms Qatlib.Concepts.SpinorSampling.Model.controlled_site_apply_gate
#print axioms Qatlib.Concepts.SpinorSampling.Model.velocity_gate_amplitude
#print axioms Qatlib.Concepts.SpinorSampling.Model.norm_sq_y_interference
#print axioms Qatlib.Concepts.SpinorSampling.Model.velocity_born_mass
#print axioms Qatlib.Concepts.SpinorSampling.Model.current_born_mass
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_born_mass
#print axioms Qatlib.Concepts.SpinorSampling.Model.supplied_spin_state_normalized
#print axioms Qatlib.Concepts.SpinorSampling.Model.velocity_gate_state_normalized
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_gate_state_normalized
#print axioms Qatlib.Concepts.SpinorSampling.Model.current_circuit_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.Model.spin_circuit_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.Model.circuit_total_record_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.Model.circuit_velocity_record_law_eq
#print axioms Qatlib.Concepts.SpinorSampling.Model.circuit_executed_plan_accuracy
#print axioms Qatlib.Concepts.SpinorSampling.Model.circuit_executed_plan_accuracy_zero_spin
