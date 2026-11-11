/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPilotScalar

set_option backward.isDefEq.respectTransparency false

/-!
Target-box projection of the uniform-address signed record law. The hit rate
and conditional sign mean are derived by summing the actual joint masses;
iid transport then transfers the empty-box risk bound to rational counters
that only read the observed records. B × A describes equal-size boxes.
Identification with the original grid's translated patch-key partition and
native physical layout, three-coordinate aggregation and compiled axes are
separate obligations; this is not the complete trained-loss endpoint.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.PilotProjection
noncomputable section
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- Construction for push Law in the partial address pilot projection model. -/
def pushLaw {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (d : FinDist X) (g : X → Y) : FinDist Y where
  prob y := ∑ x,if g x=y then d.prob x else 0
  nonneg y := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact d.nonneg x
    · exact le_rfl
  sum_one := by
    rw [Finset.sum_comm]
    simpa using d.sum_one

/-- Complete original `push_expect` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem push_expect {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (d : FinDist X) (g : X → Y) (f : Y → ℝ) :
    (pushLaw d g).expect f=d.expect (fun x => f (g x)) := by
  simp only [FinDist.expect,pushLaw,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_eq_single (g x)]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- Complete original `iid_push_expect` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem iid_push_expect {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (d : FinDist X) (g : X → Y) (n : ℕ) :
    ∀ F : (Fin n → Y) → ℝ,
      (∑ ω : Fin n → X,d.probOf ω*F (fun i => g (ω i)))=
      ∑ η : Fin n → Y,(pushLaw d g).probOf η*F η := by
  induction n with
  | zero =>
    intro F
    simp [FinDist.probOf]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro F
    rw [product_expect_cons,product_expect_cons]
    have hmap (x : X) (ω : Fin n → X) :
        (fun i : Fin (n+1) => g ((Fin.cons x ω : Fin (n+1) → X) i))=
          (Fin.cons (g x) (fun j : Fin n => g (ω j)) : Fin (n+1) → Y) := by
      funext i
      cases i using Fin.cases <;> rfl
    simp_rw [hmap]
    have hinner (x : X) :
        (∑ ω : Fin n → X,d.probOf ω*F (Fin.cons (g x) (fun j => g (ω j))))=
        ∑ η : Fin n → Y,(pushLaw d g).probOf η*F (Fin.cons (g x) η) :=
      ih (fun η => F (Fin.cons (g x) η))
    simp_rw [hinner]
    exact (push_expect d g (fun y => ∑ η : Fin n → Y,
      (pushLaw d g).probOf η*F (Fin.cons y η))).symm

variable {B A : Type*} [Fintype B] [Fintype A] [Nonempty B] [Nonempty A]
  [DecidableEq B] [DecidableEq A]

/-- Construction for collapse in the partial address pilot projection model. -/
def collapse (b : B) (r : (B × A) × Bool) : Option Bool :=
  if r.1.1=b then some r.2 else none

/-- Construction for box Mean in the partial address pilot projection model. -/
def boxMean (m : B × A → ℝ) (b : B) : ℝ :=
  (∑ a : A,m (b,a))/(Fintype.card A : ℝ)

omit [DecidableEq A] in
/-- Complete original `collapse_some_prob` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem collapse_some_prob (m : B × A → ℝ) (hm : ∀ x,|m x| ≤ 1) (b : B) (bit : Bool) :
    (pushLaw (signedRecordLaw m hm) (collapse b)).prob (some bit)=
      ∑ a : A,signedRecordWeight m ((b,a),bit) := by
  simp only [pushLaw,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · simp [collapse]
    rfl
  · intro b' _ hne
    simp [collapse,hne]
  · simp

omit [Fintype B] [Nonempty B] [DecidableEq B] [DecidableEq A] in
/-- Complete original `box_mean_bound` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem box_mean_bound (m : B × A → ℝ) (hm : ∀ x,|m x| ≤ 1) (b : B) :
    |boxMean m b| ≤ 1 := by
  have hA : (0 : ℝ)<Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hlo : -(Fintype.card A : ℝ) ≤ ∑ a : A,m (b,a) := by
    calc
      _ = ∑ _ : A,(-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun a _ => (abs_le.mp (hm (b,a))).1
  have hhi : (∑ a : A,m (b,a)) ≤ (Fintype.card A : ℝ) := by
    calc
      _ ≤ ∑ _ : A,(1 : ℝ) := Finset.sum_le_sum fun a _ => (abs_le.mp (hm (b,a))).2
      _ = _ := by simp
  apply abs_le.mpr
  constructor
  · exact (le_div_iff₀ hA).mpr (by simpa using hlo)
  · exact (div_le_iff₀ hA).mpr (by simpa using hhi)

omit [DecidableEq B] [DecidableEq A] in
/-- Complete original `box_sign_mass` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem box_sign_mass (m : B × A → ℝ) (b : B) (bit : Bool) :
    (∑ a : A,signedRecordWeight m ((b,a),bit))=
      (1+bitSign bit*boxMean m b)/(2*(Fintype.card B : ℝ)) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [signedRecordWeight,Fintype.card_prod,Nat.cast_mul,boxMean]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  simp only [mul_one]
  change ((Fintype.card A : ℝ)+bitSign bit*(∑ a : A,m (b,a)))/
    (2*((Fintype.card B : ℝ)*(Fintype.card A : ℝ)))=_
  field_simp

/-- Construction for hit Rate in the partial address pilot projection model. -/
def hitRate (B : Type*) [Fintype B] : ℝ := 1/(Fintype.card B : ℝ)

omit [Fintype A] [Nonempty A] [DecidableEq B] [DecidableEq A] in
/-- Complete original `hit_rate_bounds` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem hit_rate_bounds : 0<hitRate B ∧ hitRate B ≤ 1 := by
  have hB : (0 : ℝ)<Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hB1 : (1 : ℝ) ≤ Fintype.card B := by exact_mod_cast Fintype.card_pos
  constructor
  · exact one_div_pos.mpr hB
  · exact (div_le_one hB).mpr hB1

omit [DecidableEq A] in
/-- Complete original `collapsed_prob` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem collapsed_prob (m : B × A → ℝ) (hm : ∀ x,|m x| ≤ 1) (b : B) (out : Option Bool) :
    (pushLaw (signedRecordLaw m hm) (collapse b)).prob out=
      PilotScalar.weight (hitRate B) (boxMean m b) out := by
  have hs (bit : Bool) : (pushLaw (signedRecordLaw m hm) (collapse b)).prob (some bit)=
      PilotScalar.weight (hitRate B) (boxMean m b) (some bit) := by
    rw [collapse_some_prob,box_sign_mass]
    simp only [PilotScalar.weight,hitRate]
    ring
  cases out with
  | some bit => exact hs bit
  | none =>
    have hsum := (pushLaw (signedRecordLaw m hm) (collapse b)).sum_one
    simp only [Fintype.sum_option,Fintype.sum_bool,hs] at hsum
    have hw : PilotScalar.weight (hitRate B) (boxMean m b) none+
        (PilotScalar.weight (hitRate B) (boxMean m b) (some true)+
          PilotScalar.weight (hitRate B) (boxMean m b) (some false))=1 := by
      norm_num [PilotScalar.weight,bitSign]
      ring
    linarith

omit [DecidableEq B] [DecidableEq A] in
/-- Complete original `hit_rate_box_ratio` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem hit_rate_box_ratio : hitRate B=(Fintype.card A : ℝ)/
    ((Fintype.card B : ℝ)*(Fintype.card A : ℝ)) := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold hitRate
  field_simp

omit [DecidableEq A] in
/-- Complete original `target_box_risk` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem target_box_risk (m : B × A → ℝ) (hm : ∀ x,|m x| ≤ 1) (b : B) (n : ℕ) :
    (∑ ω : Fin n → (B × A) × Bool,(signedRecordLaw m hm).probOf ω*
      (PilotScalar.empirical (fun i => collapse b (ω i))-boxMean m b)^2) ≤
      2*(Fintype.card B : ℝ)/((n : ℝ)+1) := by
  have hp := hit_rate_bounds (B := B)
  have hμ := box_mean_bound m hm b
  let d := PilotScalar.law (hitRate B) (boxMean m b) ⟨hp.1.le,hp.2⟩ hμ
  have he (η : Fin n → Option Bool) :
      (pushLaw (signedRecordLaw m hm) (collapse b)).probOf η=d.probOf η := by
    unfold FinDist.probOf
    apply Finset.prod_congr rfl
    intro i _
    exact collapsed_prob m hm b (η i)
  calc
    _ = ∑ η : Fin n → Option Bool,(pushLaw (signedRecordLaw m hm) (collapse b)).probOf η*
        (PilotScalar.empirical η-boxMean m b)^2 := by
      exact iid_push_expect (signedRecordLaw m hm) (collapse b) n
        (fun η : Fin n → Option Bool => (PilotScalar.empirical η-boxMean m b)^2)
    _ = PilotScalar.total d (fun η : Fin n → Option Bool => (PilotScalar.empirical η-boxMean m b)^2) := by
      simp only [he,PilotScalar.total]
    _ ≤ 2/(hitRate B*((n : ℝ)+1)) :=
      PilotScalar.scalar_pilot_risk (hitRate B) (boxMean m b) ⟨hp.1.le,hp.2⟩ hμ hp.1 n
    _ = _ := by
      have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hn : (n : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
      unfold hitRate
      field_simp

/-- Construction for counter N in the partial address pilot projection model. -/
def counterN {n : ℕ} (b : B) (ω : Fin n → (B × A) × Bool) : ℕ :=
  ∑ i,(if (ω i).1.1=b then 1 else 0)

/-- Construction for counter Z in the partial address pilot projection model. -/
def counterZ {n : ℕ} (b : B) (ω : Fin n → (B × A) × Bool) : ℤ :=
  ∑ i,(if (ω i).1.1=b then if (ω i).2 then -1 else 1 else 0)

/-- Construction for counter Mean Q in the partial address pilot projection model. -/
def counterMeanQ {n : ℕ} (b : B) (ω : Fin n → (B × A) × Bool) : ℚ :=
  (counterZ b ω : ℚ)/(counterN b ω : ℚ)

omit [Fintype B] [Fintype A] [Nonempty B] [Nonempty A] [DecidableEq A] in
/-- Complete original `collapsed_count` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem collapsed_count {n : ℕ} (b : B) (ω : Fin n → (B × A) × Bool) :
    PilotScalar.count (fun i => collapse b (ω i))=counterN b ω := by
  unfold PilotScalar.count counterN
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (ω i).1.1=b <;> simp [collapse,PilotScalar.hit,h]

omit [Fintype B] [Fintype A] [Nonempty B] [Nonempty A] [DecidableEq A] in
/-- Complete original `collapsed_sign_sum` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem collapsed_sign_sum {n : ℕ} (b : B) (ω : Fin n → (B × A) × Bool) :
    (∑ i : Fin n,PilotScalar.sign (collapse b (ω i)))=(counterZ b ω : ℝ) := by
  simp only [counterZ,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (ω i).1.1=b <;> simp [collapse,PilotScalar.sign,bitSign,h]

omit [Fintype B] [Fintype A] [Nonempty B] [Nonempty A] [DecidableEq A] in
/-- Complete original `counter_mean_cast` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem counter_mean_cast {n : ℕ} (b : B) (ω : Fin n → (B × A) × Bool) :
    (counterMeanQ b ω : ℝ)=PilotScalar.empirical (fun i => collapse b (ω i)) := by
  simp only [counterMeanQ,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,
    PilotScalar.empirical,collapsed_count,collapsed_sign_sum]

omit [DecidableEq A] in
/-- Complete original `counter_mean_risk` guarantee for `PartialAddressPilotProjection`; all source hypotheses and output obligations are retained. -/
theorem counter_mean_risk (m : B × A → ℝ) (hm : ∀ x,|m x| ≤ 1) (b : B) (n : ℕ) :
    (∑ ω : Fin n → (B × A) × Bool,(signedRecordLaw m hm).probOf ω*
      ((counterMeanQ b ω : ℝ)-boxMean m b)^2) ≤
      2*(Fintype.card B : ℝ)/((n : ℝ)+1) := by
  simpa only [counter_mean_cast] using target_box_risk m hm b n

#print axioms push_expect
#print axioms iid_push_expect
#print axioms collapse_some_prob
#print axioms box_mean_bound
#print axioms box_sign_mass
#print axioms hit_rate_bounds
#print axioms collapsed_prob
#print axioms hit_rate_box_ratio
#print axioms target_box_risk
#print axioms collapsed_count
#print axioms collapsed_sign_sum
#print axioms counter_mean_cast
#print axioms counter_mean_risk
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.PilotProjection
