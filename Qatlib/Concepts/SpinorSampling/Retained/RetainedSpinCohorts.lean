/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Retained.RetainedSpinInstrument
public import Qatlib.Concepts.SpinorSampling.Matching.MatchedMeasurementNoise
public import Mathlib.Logic.Equiv.Set

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Spin Cohorts

Retained Spin Cohorts constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib Matched

/-- Construction for spin Tensor in the retained spin cohorts model. -/
def spinTensor {W : Type*} [Fintype W] (u : W → Bool → ℂ) (σ : W → Bool) : ℂ :=
  ∏ w : W,u w (σ w)

/-- Summing a product of coordinate weights over all assignments factors into the product of the sums over each coordinate. -/
theorem sum_tensor_weights {W X : Type*} [Fintype W] [DecidableEq W] [Fintype X]
    (f : W → X → ℝ) :
    (∑ σ : W → X,∏ w : W,f w (σ w))=∏ w : W,∑ x : X,f w x := by
  calc
    _ = ∑ σ ∈ Fintype.piFinset (fun _ : W => (Finset.univ : Finset X)),
        ∏ w : W,f w (σ w) := Finset.sum_congr rfl (fun _ _ => rfl)
    _ = _ := (Finset.prod_univ_sum (t := fun _ : W => (Finset.univ : Finset X))
      (f := f)).symm

/-- The spin tensor is normalized if every wire's qubit amplitude has unit mass. -/
theorem spin_tensor_normalized {W : Type*} [Fintype W] [DecidableEq W]
    (u : W → Bool → ℂ) (hu : ∀ w,qubitMass (u w)=1) : Normalized (spinTensor u) := by
  unfold Normalized
  simp only [Complex.sq_norm,spinTensor,map_prod]
  rw [sum_tensor_weights (fun w b => Complex.normSq (u w b))]
  have h (w : W) : (∑ b : Bool,Complex.normSq (u w b))=1 := by
    simpa only [Fintype.sum_bool,qubitMass,add_comm] using hu w
  simp_rw [h]
  simp

/-- Construction for captured Cohort Amplitude in the retained spin cohorts model. -/
def capturedCohortAmplitude {S : Type*} [Fintype S] {n : ℕ}
    (a b c k : S → ℝ) (J : Fin n → S) (σ : Fin n → Bool) : ℂ :=
  ∏ i : Fin n,suppliedSpinState a b c k (σ i) (J i)

/-- For normalized site spinors, the total squared amplitude of any specified n-address cohort is M⁻ⁿ, where M is the number of sites. -/
theorem cohort_address_mass {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (J : Fin n → S) :
    (∑ σ : Fin n → Bool,Complex.normSq (capturedCohortAmplitude a b c k J σ))=
      (1/(Fintype.card S : ℝ))^n := by
  simp only [capturedCohortAmplitude,map_prod]
  rw [sum_tensor_weights (fun i spin => Complex.normSq (suppliedSpinState a b c k spin (J i)))]
  have h (i : Fin n) : (∑ spin : Bool,Complex.normSq
      (suppliedSpinState a b c k spin (J i)))=1/(Fintype.card S : ℝ) := by
    have hi := complex_spinor_mass a b c k hz (J i)
    simp only [suppliedSpinState,Complex.normSq_div,Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card S))]
    rw [← Finset.sum_div]
    have hs : (∑ spin : Bool,Complex.normSq (complexSpinor a b c k (J i) spin))=1 := by
      simpa only [Fintype.sum_bool,qubitMass,add_comm] using hi
    rw [hs]
  simp_rw [h]
  simp

/-- Scaling the captured cohort amplitude by the nth power of the square root of the site count gives the tensor of spinors at the specified addresses. -/
theorem retained_cohort_amplitude {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
    (a b c k : S → ℝ) (J : Fin n → S) (σ : Fin n → Bool) :
    (Real.sqrt (Fintype.card S : ℝ) : ℂ)^n*capturedCohortAmplitude a b c k J σ=
      spinTensor (fun i => complexSpinor a b c k (J i)) σ := by
  have hM : (Fintype.card S : ℝ)>0 := by exact_mod_cast Fintype.card_pos
  have hr : (Real.sqrt (Fintype.card S : ℝ) : ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have h (i : Fin n) : (Real.sqrt (Fintype.card S : ℝ) : ℂ)*
      suppliedSpinState a b c k (σ i) (J i)=complexSpinor a b c k (J i) (σ i) := by
    dsimp [suppliedSpinState]
    field_simp
  calc
    _ = (∏ _ : Fin n,(Real.sqrt (Fintype.card S : ℝ) : ℂ))*
        (∏ i : Fin n,suppliedSpinState a b c k (σ i) (J i)) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,capturedCohortAmplitude]
    _ = ∏ i : Fin n,(Real.sqrt (Fintype.card S : ℝ) : ℂ)*
        suppliedSpinState a b c k (σ i) (J i) := (Finset.prod_mul_distrib).symm
    _ = _ := by simp_rw [h]; rfl

/-- For normalized site spinors, scaling the captured n-record amplitude by the nth power of the square root of the site count gives a normalized retained spin state. -/
theorem retained_cohort_normalized {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
    (a b c k : S → ℝ) (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1) (J : Fin n → S) :
    Normalized (fun σ => (Real.sqrt (Fintype.card S : ℝ) : ℂ)^n*
      capturedCohortAmplitude a b c k J σ) := by
  simp_rw [retained_cohort_amplitude]
  exact spin_tensor_normalized _ (fun i => complex_spinor_mass a b c k hz (J i))

/-- Construction for unused Wires in the retained spin cohorts model. -/
def unusedWires {I W : Type*} (e : I → W) := {w : W // ¬∃ i,e i=w}

/-- Typeclass instance for unused Wires Fintype in the retained spin cohorts model. -/
noncomputable instance unusedWiresFintype {I W : Type*} [Fintype W] (e : I → W) :
    Fintype (unusedWires e) := by
  unfold unusedWires
  exact Fintype.ofFinite _

/-- Construction for wire Partition in the retained spin cohorts model. -/
def wirePartition {I W : Type*} (e : I → W) (he : Function.Injective e) :
    (I ⊕ unusedWires e) ≃ W :=
  (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun w => ∃ i,e i=w))

/-- The wire partition sends a selected index to its image under the injective wire assignment. -/
@[simp] theorem wire_partition_left {I W : Type*} (e : I → W) (he : Function.Injective e) (i : I) :
    wirePartition e he (Sum.inl i)=e i := rfl

/-- The wire partition sends an unused-wire index to the underlying wire itself. -/
@[simp] theorem wire_partition_right {I W : Type*} (e : I → W) (he : Function.Injective e)
    (w : unusedWires e) : wirePartition e he (Sum.inr w)=w.val := rfl

/-- The product over all physical wires factors into the product over the image of the injective assignment and the product over unused wires. -/
theorem product_wire_partition {I W : Type*} [Fintype I] [Fintype W]
    (e : I → W) (he : Function.Injective e) (f : W → ℂ) :
    (∏ w : W,f w)=(∏ i : I,f (e i))*(∏ w : unusedWires e,f w.val) := by
  calc
    _ = ∏ z : I ⊕ unusedWires e,f (wirePartition e he z) :=
      (Equiv.prod_comp (wirePartition e he) f).symm
    _ = _ := by rw [Fintype.prod_sum_type]; rfl

/-- Construction for pair Physical Wire in the retained spin cohorts model. -/
def pairPhysicalWire {S : Type} [DecidableEq S] {n m : ℕ}
    (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (z : matchedSites J K τ × Bool) : Fin n ⊕ Fin m :=
  if z.2 then Sum.inr (rightMatchIndex J K τ z.1) else Sum.inl (leftMatchIndex J K τ z.1)

/-- An injective site map ensures that the selected endpoints of all matched pairs map to distinct physical wires in the disjoint union of the cohorts. -/
theorem pair_physical_wire_injective {S : Type} [DecidableEq S] {n m : ℕ}
    (J : Fin n → S) (K : Fin m → S) (τ : S → S) (hτ : Function.Injective τ) :
    Function.Injective (pairPhysicalWire J K τ) := by
  rintro ⟨x,b⟩ ⟨y,c⟩ h
  cases b <;> cases c <;> dsimp only [pairPhysicalWire] at h
  · have hxy := left_match_index_injective J K τ (Sum.inl.inj h)
    exact Prod.ext hxy rfl
  · cases h
  · cases h
  · have hxy := right_match_index_injective J K τ hτ (Sum.inr.inj h)
    exact Prod.ext hxy rfl

/-- Construction for tagged Spin in the retained spin cohorts model. -/
def taggedSpin {S : Type*} {n m : ℕ} (a b c k : S → ℝ)
    (J : Fin n → S) (K : Fin m → S) : (Fin n ⊕ Fin m) → Bool → ℂ :=
  Sum.elim (fun i => complexSpinor a b c k (J i)) (fun i => complexSpinor a b c k (K i))

/-- With an injective wire assignment, the spin tensor amplitude is the product of both endpoint amplitudes for each pair and the single-wire amplitudes on unused wires. -/
theorem spin_tensor_pair_partition {I W : Type*} [Fintype I] [Fintype W]
    (e : I × Bool → W) (he : Function.Injective e) (u : W → Bool → ℂ) (σ : W → Bool) :
    spinTensor u σ=
      (∏ i : I,u (e (i,false)) (σ (e (i,false)))*u (e (i,true)) (σ (e (i,true))))*
        (∏ w : unusedWires e,u w.val (σ w.val)) := by
  rw [spinTensor,product_wire_partition e he]
  congr 1
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  rw [Fintype.prod_bool]
  exact mul_comm _ _

/-- For an injective site map, the tagged cohort amplitude is the product of two-spin amplitudes at the selected matched endpoints and the original amplitudes on unused wires. -/
theorem selected_pair_input_factorization {S : Type} [DecidableEq S] {n m : ℕ}
    (a b c k : S → ℝ) (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (hτ : Function.Injective τ) (σ : (Fin n ⊕ Fin m) → Bool) :
    spinTensor (taggedSpin a b c k J K) σ=
      (∏ x : matchedSites J K τ,
        pairInput (complexSpinor a b c k x) (complexSpinor a b c k (τ x))
          (pairReg (σ (Sum.inl (leftMatchIndex J K τ x)))
            (σ (Sum.inr (rightMatchIndex J K τ x)))))*
      (∏ w : unusedWires (pairPhysicalWire J K τ),taggedSpin a b c k J K w.val (σ w.val)) := by
  refine (spin_tensor_pair_partition (pairPhysicalWire J K τ)
    (pair_physical_wire_injective J K τ hτ) (taggedSpin a b c k J K) σ).trans ?_
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  simp [pairPhysicalWire,taggedSpin,left_match_address,right_match_address,pairInput]

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.spin_tensor_normalized
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.cohort_address_mass
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.retained_cohort_amplitude
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.retained_cohort_normalized
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.product_wire_partition
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pair_physical_wire_injective
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.selected_pair_input_factorization
