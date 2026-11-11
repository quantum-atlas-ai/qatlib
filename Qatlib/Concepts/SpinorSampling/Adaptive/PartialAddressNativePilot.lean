/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressGridPatch
import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressPilotVector

set_option backward.isDefEq.respectTransparency false

/-!
Transport the original supplied-state/native Pauli pilot law through the
explicit translated grid partition to actual rational counters. The resulting
three-coordinate tail uses the literal pilot count and an actual conditional
box mean, without free success/hit-rate certificates. Bloch lengths follow
from pointwise normalization. This is the pilot component: matching-edge
Poincare, finite H/T compiler certificates and the trained full-loss endpoint
remain separate obligations.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.NativePilot
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open PilotProjection
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  [DecidableEq X] [DecidableEq Y]

/-- Construction for record Equiv in the partial address native pilot model. -/
def recordEquiv (e : X ≃ Y) : (X × Bool) ≃ (Y × Bool) := e.prodCongr (Equiv.refl Bool)

omit [Nonempty X] [Nonempty Y] [DecidableEq X] [DecidableEq Y] in
/-- Complete original `record_weight_relabel` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem record_weight_relabel (e : X ≃ Y) (m : X → ℝ) (z : Y × Bool) :
    signedRecordWeight m ((recordEquiv e).symm z)=
      signedRecordWeight (fun y => m (e.symm y)) z := by
  have hc : Fintype.card X=Fintype.card Y := Fintype.card_congr e
  change (1+recordSign z.2*m (e.symm z.1))/(2*(Fintype.card X : ℝ))=_
  rw [hc]
  rfl

#print axioms record_weight_relabel
end

noncomputable section
variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] in
/-- Complete original `push_equiv_prob` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem push_equiv_prob (e : X ≃ Y) (p : FinDist X) (y : Y) :
    (pushLaw p e).prob y=p.prob (e.symm y) := by
  change (∑ x : X,if e x=y then p.prob x else 0)=_
  rw [Finset.sum_eq_single (e.symm y)]
  · simp
  · intro x _ hx
    have hn : e x ≠ y := by
      intro h
      exact hx (e.injective (h.trans (e.apply_symm_apply y).symm))
    simp only [ite_eq_right hn]
  · simp

/-- Complete original `independent_relabel` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem independent_relabel {n : ℕ} (e : X ≃ Y) (p : Fin n → FinDist X)
    (F : (Fin n → Y) → ℝ) :
    (independentSampleLaw p).expect (fun ω => F (fun i => e (ω i)))=
      (independentSampleLaw (fun i => pushLaw (p i) e)).expect F := by
  let E : (Fin n → X) ≃ (Fin n → Y) := Equiv.piCongrRight (fun _ => e)
  unfold FinDist.expect
  calc
    _ = ∑ η : Fin n → Y,(independentSampleLaw p).prob (E.symm η)*F η := by
      rw [← E.symm.sum_comp (fun ω =>
        (independentSampleLaw p).prob ω*F (fun i => e (ω i)))]
      apply Finset.sum_congr rfl
      intro η _
      have hh : (fun i => e (E.symm η i))=η := by
        funext i
        exact e.apply_symm_apply (η i)
      rw [hh]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro η _
      simp only [independentSampleLaw,push_equiv_prob]
      rfl

#print axioms push_equiv_prob
#print axioms independent_relabel
end
noncomputable section
open NativeBridge

/-- Complete original `law_ext` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
private theorem law_ext {Z : Type*} [Fintype Z] (p q : FinDist Z)
    (h : ∀ z,p.prob z=q.prob z) : p=q := by
  cases p with
  | mk p hp hs =>
    cases q with
    | mk q hq ht =>
      have he : p=q := funext h
      subst q
      rfl

variable {B A : Type} [Fintype B] [Fintype A] [Nonempty B] [Nonempty A]
  [DecidableEq B] [DecidableEq A]

/-- Construction for sample Equiv in the partial address native pilot model. -/
def sampleEquiv {X Y : Type} (e : X ≃ Y) (n : ℕ) :
    (Fin n → X × Bool) ≃ (Fin n → Y × Bool) :=
  Equiv.piCongrRight (fun _ => recordEquiv e)

/-- Construction for original Training in the partial address native pilot model. -/
def originalTraining (d r : ℕ) (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (n : ℕ) :
    FinDist (Fin 3 → Fin n → (Fin d → Fin (2^r)) × Bool) :=
  independentSampleLaw (fun h : Fin 3 =>
    independentSampleLaw (fun _ : Fin n => nativeSpinLaw d r h a b c k hz))

/-- Construction for actual Fields in the partial address native pilot model. -/
def actualFields {d r : ℕ} (e : (Fin d → Fin (2^r)) ≃ B × A)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) : Fin 3 → B × A → ℝ :=
  fun h y => pauliField a b c k h (e.symm y)

omit [Fintype B] [Fintype A] [Nonempty B] [Nonempty A] [DecidableEq B] [DecidableEq A] in
/-- Complete original `actual_fields_bound` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem actual_fields_bound {d r : ℕ} (e : (Fin d → Fin (2^r)) ≃ B × A)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) : ∀ h y,|actualFields e a b c k h y| ≤ 1 := by
  intro h y
  exact unit_spin_component_bound (pauliField a b c k) (pauli_field_unit a b c k hz) h (e.symm y)

/-- Complete original `original_cohort_relabel` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem original_cohort_relabel {d r : ℕ} (e : (Fin d → Fin (2^r)) ≃ B × A)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (h : Fin 3) (n : ℕ) :
    pushLaw (independentSampleLaw (fun _ : Fin n => nativeSpinLaw d r h a b c k hz))
      (sampleEquiv e n)=
    independentSampleLaw (fun _ : Fin n =>
      signedRecordLaw (actualFields e a b c k h) (actual_fields_bound e a b c k hz h)) := by
  apply law_ext
  intro η
  rw [push_equiv_prob]
  change (∏ i : Fin n,nativeSpinWeight d r h a b c k ((recordEquiv e).symm (η i)))=
    ∏ i : Fin n,signedRecordWeight (actualFields e a b c k h) (η i)
  apply Finset.prod_congr rfl
  intro i _
  rw [native_spin_weight_eq d r h a b c k hz]
  exact record_weight_relabel e (pauliField a b c k h) (η i)

/-- Complete original `original_training_relabel` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem original_training_relabel {d r : ℕ} (e : (Fin d → Fin (2^r)) ≃ B × A)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (n : ℕ)
    (F : (Fin 3 → Fin n → (B × A) × Bool) → ℝ) :
    (originalTraining d r a b c k hz n).expect
      (fun Ω => F (fun h i => recordEquiv e (Ω h i)))=
    (PilotVector.trainingLaw (actualFields e a b c k) (actual_fields_bound e a b c k hz) n).expect F := by
  unfold originalTraining
  change (independentSampleLaw (fun h : Fin 3 =>
    independentSampleLaw (fun _ : Fin n => nativeSpinLaw d r h a b c k hz))).expect
      (fun Ω => F (fun h => sampleEquiv e n (Ω h)))=_
  rw [independent_relabel]
  simp_rw [original_cohort_relabel]
  rfl

/-- Complete original `original_pilot_tail` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem original_pilot_tail {d r : ℕ} (e : (Fin d → Fin (2^r)) ≃ B × A)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (α τ : ℚ) (hα : 0<α) (hτ : 0<τ) :
    (originalTraining d r a b c k hz (PilotVector.pilotCountQ (Fintype.card B) α τ)).expect
      (fun Ω => if (τ : ℝ)/16<
        PilotVector.averageError (actualFields e a b c k) (fun h i => recordEquiv e (Ω h i))
        then 1 else 0) ≤ (α : ℝ) := by
  have ht := original_training_relabel e a b c k hz
    (PilotVector.pilotCountQ (Fintype.card B) α τ)
    (fun Ω => if (τ : ℝ)/16<PilotVector.averageError (actualFields e a b c k) Ω then 1 else 0)
  rw [ht]
  exact PilotVector.pilot_error_tail (actualFields e a b c k) (actual_fields_bound e a b c k hz) α τ hα hτ

#print axioms actual_fields_bound
#print axioms original_cohort_relabel
#print axioms original_training_relabel
#print axioms original_pilot_tail
end

noncomputable section
/-- Complete original `grid_pilot_tail` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem grid_pilot_tail (C ell : ℕ) [NeZero C] [NeZero ell] [NeZero (C*ell)]
    (d r : ℕ) (hN : 2^r=C*ell*2) (offset : Fin d → Fin (C*ell))
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (α τ : ℚ) (hα : 0<α) (hτ : 0<τ) :
    let e := GridPatch.nativeGridEquiv C ell d r hN offset
    (originalTraining d r a b c k hz (PilotVector.pilotCountQ ((2*C)^d) α τ)).expect
      (fun Ω => if (τ : ℝ)/16<
        PilotVector.averageError (actualFields e a b c k) (fun h i => recordEquiv e (Ω h i))
        then 1 else 0) ≤ (α : ℝ) := by
  dsimp only
  have h := original_pilot_tail (GridPatch.nativeGridEquiv C ell d r hN offset) a b c k hz α τ hα hτ
  have hb : Fintype.card (Fin d → Fin 2 × Fin C)=(2*C)^d := by simp
  rw [hb] at h
  exact h

#print axioms grid_pilot_tail
end
noncomputable section
open PilotVector AxisRisk
variable {B A : Type} [Fintype B] [Fintype A] [Nonempty A]

omit [Fintype B] in
/-- Complete original `mean_bloch_length` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem mean_bloch_length (m : Fin 3 → B × A → ℝ)
    (hu : ∀ x,∑ h : Fin 3,(m h x)^2=1) (b : B) :
    length (boxVector m b) ≤ 1 := by
  have hp : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  have hmean (h : Fin 3) : (boxMean (m h) b)^2 ≤
      (∑ a : A,(m h (b,a))^2)/(Fintype.card A : ℝ) := by
    have hs : (∑ a : A,m h (b,a))^2 ≤
        (∑ a : A,(m h (b,a))^2)*(Fintype.card A : ℝ) := by
      simpa only [Finset.sum_const,Finset.card_univ,one_pow,nsmul_eq_mul,mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a : A => m h (b,a)) (fun _ => (1 : ℝ))
    unfold boxMean
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hp 2) hp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs hp.le]
  have hd : dot (boxVector m b) (boxVector m b) ≤ 1 := by
    calc
      _ = ∑ h : Fin 3,(boxMean (m h) b)^2 := by simp only [dot,boxVector,pow_two]
      _ ≤ ∑ h : Fin 3,(∑ a : A,(m h (b,a))^2)/(Fintype.card A : ℝ) :=
        Finset.sum_le_sum fun h _ => hmean h
      _ = (∑ a : A,∑ h : Fin 3,(m h (b,a))^2)/(Fintype.card A : ℝ) := by
        rw [← Finset.sum_div,Finset.sum_comm]
      _ = 1 := by simp_rw [hu]; simp [ne_of_gt hp]
  nlinarith [length_sq (boxVector m b)]

omit [Fintype B] in
/-- Complete original `actual_box_length` guarantee for `PartialAddressNativePilot`; all source hypotheses and output obligations are retained. -/
theorem actual_box_length {d r : ℕ} (e : (Fin d → Fin (2^r)) ≃ B × A)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (box : B) :
    length (boxVector (actualFields e a b c k) box) ≤ 1 := by
  apply mean_bloch_length
  intro x
  exact pauli_field_unit a b c k hz (e.symm x)

#print axioms mean_bloch_length
#print axioms actual_box_length
end
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.NativePilot
