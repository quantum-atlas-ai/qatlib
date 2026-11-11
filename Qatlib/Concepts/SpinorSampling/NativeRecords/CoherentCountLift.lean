/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.KnownCountPermutation
import Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhaseIsometry

set_option backward.isDefEq.respectTransparency false

/-!
# Coherent Count Lift

The actual finite fiber of complete address sequences with the reference multiplicities.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
open Qatlib.Concepts.SpinorSampling.NativeRecords.KnownCountPermutation
open Qatlib.Concepts.SpinorSampling.NativeRecords.LabelPhase

/-- The actual finite fiber of complete address sequences with the reference multiplicities. -/
abbrev CountFiber {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) :=
  {x : Fin Q → A // ∀ a,multiplicity x a=multiplicity y a}

/-- The coherent lift is a fixed matrix built only from known label-preserving permutations. -/
def orbitMatrix {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) :
    Matrix (CountFiber y × (Fin Q → Bool)) (Fin Q → Bool) ℂ :=
  controlledEmbedding (fun x : CountFiber y => (spinPermutation x.val y x.property).permMatrix ℂ)

/-- The actual coherent count-fiber matrix is isometric on the entire unknown input spin register. -/
theorem orbitMatrix_isometry {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) :
    (orbitMatrix y).conjTranspose*orbitMatrix y=1 := by
  let : Nonempty (CountFiber y) := ⟨⟨y,fun _ => rfl⟩⟩
  exact controlled_permutation_isometry (fun x : CountFiber y => spinPermutation x.val y x.property)

/-- The same known coherent lift transports every unknown site-spin family to all actual sequences in the count fiber. -/
theorem orbitMatrix_apply {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (y : Fin Q → A) (u : A → Bool → ℂ) (x : CountFiber y) (s : Fin Q → Bool) :
    (orbitMatrix y*ᵥ(fun t => copyAmplitude u Q (fun j => (y j,t j)))) (x,s)=
      orbitCoefficient (I := CountFiber y)*copyAmplitude u Q (fun j => (x.val j,s j)) := by
  rw [orbitMatrix,controlled_embedding_apply,spinPermutation_apply]

/-- The same coherent lift occupies the entire original physical copy basis, with zero amplitude outside its actual count fiber. -/
def fullOrbitMatrix {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) :
    Matrix (Fin Q → A × Bool) (Fin Q → Bool) ℂ := fun z t =>
  if h : ∀ a,multiplicity (fun j => (z j).1) a=multiplicity y a then
    orbitMatrix y (⟨(fun j => (z j).1),h⟩,(fun j => (z j).2)) t else 0

/-- The full original-coordinate lift preserves the Gram matrix on every input spin vector. -/
theorem fullOrbitMatrix_isometry {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ} (y : Fin Q → A) :
    (fullOrbitMatrix y).conjTranspose*fullOrbitMatrix y=1 := by
  ext i j
  change (∑ z : Fin Q → A × Bool,star (fullOrbitMatrix y z i)*fullOrbitMatrix y z j)=
    (1 : Matrix (Fin Q → Bool) (Fin Q → Bool) ℂ) i j
  calc _ = ∑ x : Fin Q → A,∑ s : Fin Q → Bool,
      star (fullOrbitMatrix y (fun k => (x k,s k)) i)*fullOrbitMatrix y (fun k => (x k,s k)) j := by
        have h := (Equiv.arrowProdEquivProdArrow (Fin Q) (fun _ => A) (fun _ => Bool)).symm.sum_comp
          (fun z : Fin Q → A × Bool => star (fullOrbitMatrix y z i)*fullOrbitMatrix y z j)
        simpa only [Fintype.sum_prod_type,Equiv.arrowProdEquivProdArrow,Equiv.coe_fn_symm_mk] using h.symm
       _ = ∑ x : Fin Q → A,if h : ∀ a,multiplicity x a=multiplicity y a then
          (∑ s : Fin Q → Bool,star (orbitMatrix y (⟨x,h⟩,s) i)*orbitMatrix y (⟨x,h⟩,s) j) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : ∀ a,multiplicity x a=multiplicity y a <;> simp [fullOrbitMatrix,h]
       _ = ∑ x : CountFiber y,∑ s : Fin Q → Bool,
          star (orbitMatrix y (x,s) i)*orbitMatrix y (x,s) j := by
        rw [Finset.sum_dite]
        simp only [Finset.sum_const_zero,add_zero]
        exact (Equiv.subtypeEquivRight (by simp)).sum_comp
          (fun x : CountFiber y => ∑ s : Fin Q → Bool,
            star (orbitMatrix y (x,s) i)*orbitMatrix y (x,s) j)
       _ = _ := by
        have h := congrArg (fun M : Matrix (Fin Q → Bool) (Fin Q → Bool) ℂ => M i j) (orbitMatrix_isometry y)
        simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type] using h

/-- The same hypothesis-independent full matrix transports the literal unknown spin tensor to every supported original address sequence. -/
theorem fullOrbitMatrix_apply {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (y : Fin Q → A) (u : A → Bool → ℂ) (z : Fin Q → A × Bool) :
    (fullOrbitMatrix y*ᵥ(fun t => copyAmplitude u Q (fun j => (y j,t j)))) z=
      if (∀ a,multiplicity (fun j => (z j).1) a=multiplicity y a) then
        orbitCoefficient (I := CountFiber y)*copyAmplitude u Q z else 0 := by
  by_cases h : ∀ a,multiplicity (fun j => (z j).1) a=multiplicity y a
  · simpa only [fullOrbitMatrix,Matrix.mulVec,dotProduct,dite_eq_left h,ite_eq_left h] using
      orbitMatrix_apply y u ⟨(fun j => (z j).1),h⟩ (fun j => (z j).2)
  · simp [fullOrbitMatrix,Matrix.mulVec,dotProduct,h]

/-- Equal actual multiplicities give literally equivalent address fibers and the same finite fiber size. -/
theorem countFiber_card_eq {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a) :
    Fintype.card (CountFiber x)=Fintype.card (CountFiber y) := by
  have he (z : Fin Q → A) : (∀ a,multiplicity z a=multiplicity x a) ↔
      (∀ a,multiplicity z a=multiplicity y a) := by
    constructor
    · intro hz a
      exact (hz a).trans (h a)
    · intro hz a
      exact (hz a).trans (h a).symm
  exact Fintype.card_congr (Equiv.subtypeEquivRight he)

/-- The constructed coherent coefficient is constant on each actual address-count fiber. -/
theorem orbitCoefficient_eq {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x y : Fin Q → A) (h : ∀ a,multiplicity x a=multiplicity y a) :
    orbitCoefficient (I := CountFiber x)=orbitCoefficient (I := CountFiber y) := by
  unfold orbitCoefficient
  rw [countFiber_card_eq x y h]

/-- Averaging over all actual reference sequences counts each coherent multiplicity block exactly once. -/
theorem countFiber_kernel {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x z : Fin Q → A) :
    (∑ y : Fin Q → A,if (∀ a,multiplicity x a=multiplicity y a) ∧
      (∀ a,multiplicity z a=multiplicity y a) then
        star (orbitCoefficient (I := CountFiber y))*orbitCoefficient (I := CountFiber y) else 0)=
      if (∀ a,multiplicity x a=multiplicity z a) then 1 else 0 := by
  by_cases hxz : ∀ a,multiplicity x a=multiplicity z a
  · rw [ite_eq_left hxz]
    have hterm (y : Fin Q → A) :
        (if (∀ a,multiplicity x a=multiplicity y a) ∧ (∀ a,multiplicity z a=multiplicity y a) then
          star (orbitCoefficient (I := CountFiber y))*orbitCoefficient (I := CountFiber y) else 0)=
            if (∀ a,multiplicity y a=multiplicity x a) then
              star (orbitCoefficient (I := CountFiber x))*orbitCoefficient (I := CountFiber x) else 0 := by
      by_cases hy : ∀ a,multiplicity y a=multiplicity x a
      · have hxy : ∀ a,multiplicity x a=multiplicity y a := fun a => (hy a).symm
        have hzy : ∀ a,multiplicity z a=multiplicity y a := fun a => (hxz a).symm.trans (hxy a)
        have hboth : (∀ a,multiplicity x a=multiplicity y a) ∧
            (∀ a,multiplicity z a=multiplicity y a) := ⟨hxy,hzy⟩
        simp only [ite_eq_left hboth,ite_eq_left hy,orbitCoefficient_eq y x hy]
      · have hn : ¬((∀ a,multiplicity x a=multiplicity y a) ∧ (∀ a,multiplicity z a=multiplicity y a)) :=
          fun h => hy (fun a => (h.1 a).symm)
        simp only [ite_eq_right hn,ite_eq_right hy]
    simp_rw [hterm]
    have hs : (∑ y : Fin Q → A,if (∀ a,multiplicity y a=multiplicity x a) then
        star (orbitCoefficient (I := CountFiber x))*orbitCoefficient (I := CountFiber x) else 0)=
          (Fintype.card (CountFiber x) : ℂ)*
            (star (orbitCoefficient (I := CountFiber x))*orbitCoefficient (I := CountFiber x)) := by
      rw [←Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [←Fintype.card_subtype (fun y : Fin Q → A => ∀ a,multiplicity y a=multiplicity x a)]
    rw [hs]
    let : Nonempty (CountFiber x) := ⟨⟨x,fun _ => rfl⟩⟩
    exact orbit_coefficient_normalization
  · rw [ite_eq_right hxz]
    apply Finset.sum_eq_zero
    intro y _
    apply ite_eq_right
    intro h
    exact hxz (fun a => (h.1 a).trans (h.2 a).symm)

/-- The literal averaged lift reproduces the full shared-phase matrix kernel, retaining all unknown spin amplitudes. -/
theorem fullOrbitMatrix_average_entry {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (u : A → Bool → ℂ) (γ : ℂ) (z w : Fin Q → A × Bool) :
    (∑ y : Fin Q → A,γ*
      (fullOrbitMatrix y*ᵥ(fun t => copyAmplitude u Q (fun j => (y j,t j)))) z*
      star ((fullOrbitMatrix y*ᵥ(fun t => copyAmplitude u Q (fun j => (y j,t j)))) w))=
        γ*(if (∀ a,multiplicity (fun j => (z j).1) a=multiplicity (fun j => (w j).1) a) then 1 else 0)*
          copyAmplitude u Q z*star (copyAmplitude u Q w) := by
  have ht (y : Fin Q → A) :
      γ*(fullOrbitMatrix y*ᵥ(fun t => copyAmplitude u Q (fun j => (y j,t j)))) z*
        star ((fullOrbitMatrix y*ᵥ(fun t => copyAmplitude u Q (fun j => (y j,t j)))) w)=
      (if (∀ a,multiplicity (fun j => (z j).1) a=multiplicity y a) ∧
        (∀ a,multiplicity (fun j => (w j).1) a=multiplicity y a) then
          star (orbitCoefficient (I := CountFiber y))*orbitCoefficient (I := CountFiber y) else 0)*
        (γ*copyAmplitude u Q z*star (copyAmplitude u Q w)) := by
    rw [fullOrbitMatrix_apply,fullOrbitMatrix_apply]
    by_cases hz : ∀ a,multiplicity (fun j => (z j).1) a=multiplicity y a
    · by_cases hw : ∀ a,multiplicity (fun j => (w j).1) a=multiplicity y a
      · simp [hz,hw,star_mul]
        ring
      · simp [hz,hw]
    · by_cases hw : ∀ a,multiplicity (fun j => (w j).1) a=multiplicity y a
      · simp [hz,hw]
      · simp [hz,hw]
  calc
    _ = (∑ y : Fin Q → A,if (∀ a,multiplicity (fun j => (z j).1) a=multiplicity y a) ∧
        (∀ a,multiplicity (fun j => (w j).1) a=multiplicity y a) then
          star (orbitCoefficient (I := CountFiber y))*orbitCoefficient (I := CountFiber y) else 0)*
        (γ*copyAmplitude u Q z*star (copyAmplitude u Q w)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      exact ht y
    _ = _ := by
      rw [countFiber_kernel]
      ring

end Qatlib.Concepts.SpinorSampling.NativeRecords.CoherentCountLift
