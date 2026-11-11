/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.RetainedBellFlat

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Retained Bell Joint

Retained Bell Joint constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
noncomputable section
open scoped BigOperators Classical
open Qatlib ShiftCircuit NativeBridge

variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- Only a mathematical coordinate equivalence; it is not a routing operation. -/
def assemblePairBits (e : I × Bool → Fin N) (he : Function.Injective e)
    (ω : (I → Reg 2) × (unusedWires e → Bool)) : Reg N := fun w =>
  match (wirePartition e he).symm w with
  | .inl (i,b) => ω.1 i (if b then 1 else 0)
  | .inr v => ω.2 v

omit [Fintype I] [DecidableEq I] in
/-- Complete original `assemble_selected` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem assemble_selected (e : I × Bool → Fin N) (he : Function.Injective e)
    (ω : (I → Reg 2) × (unusedWires e → Bool)) (i : I) (b : Bool) :
    assemblePairBits e he ω (e (i,b))=ω.1 i (if b then 1 else 0) := by
  have hs : (wirePartition e he).symm (e (i,b))=Sum.inl (i,b) :=
    (Equiv.symm_apply_eq (wirePartition e he)).mpr rfl
  simp only [assemblePairBits,hs]

omit [Fintype I] [DecidableEq I] in
/-- Complete original `assemble_unused` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem assemble_unused (e : I × Bool → Fin N) (he : Function.Injective e)
    (ω : (I → Reg 2) × (unusedWires e → Bool)) (w : unusedWires e) :
    assemblePairBits e he ω w.val=ω.2 w := by
  have hs : (wirePartition e he).symm w.val=Sum.inr w :=
    (Equiv.symm_apply_eq (wirePartition e he)).mpr rfl
  simp only [assemblePairBits,hs]

/-- Construction for pair Basis in the retained bell joint model. -/
def pairBasis (e : I × Bool → Fin N) (he : Function.Injective e) :
    Reg N ≃ (I → Reg 2) × (unusedWires e → Bool) where
  toFun σ := (pairSite e σ,fun w => σ w.val)
  invFun := assemblePairBits e he
  left_inv σ := by
    funext w
    obtain ⟨z,rfl⟩ := (wirePartition e he).surjective w
    cases z with
    | inl p =>
      obtain ⟨i,b⟩ := p
      change assemblePairBits e he (pairSite e σ,fun v => σ v.val) (e (i,b))=_
      rw [assemble_selected]
      cases b <;> rfl
    | inr v =>
      exact assemble_unused e he _ v
  right_inv ω := by
    apply Prod.ext
    · funext i
      change pairSite e (assemblePairBits e he ω) i=ω.1 i
      rw [pairSite,assemble_selected,assemble_selected]
      exact pair_reg_eta (ω.1 i)
    · funext w
      exact assemble_unused e he ω w

omit [DecidableEq I] in
/-- Complete original `pair_basis_state` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem pair_basis_state (e : I × Bool → Fin N) (he : Function.Injective e)
    (f : I → QState (Reg 2)) (u : unusedWires e → Bool → ℂ)
    (ω : (I → Reg 2) × (unusedWires e → Bool)) :
    pairedState e f u ((pairBasis e he).symm ω)=
      (∏ i : I,f i (ω.1 i))*(∏ w : unusedWires e,u w (ω.2 w)) := by
  have h := (pairBasis e he).apply_symm_apply ω
  have hp := congrArg Prod.fst h
  have hu := congrArg Prod.snd h
  change (∏ i : I,f i (((pairBasis e he) ((pairBasis e he).symm ω)).1 i))*
    (∏ w : unusedWires e,u w (((pairBasis e he) ((pairBasis e he).symm ω)).2 w))=_
  rw [hp,hu]

/-- Construction for pair Hits in the retained bell joint model. -/
def pairHits (e : I × Bool → Fin N) (σ : Reg N) : I → Bool :=
  fun i => isBellHit (pairSite e σ i)

omit [Fintype I] [DecidableEq I] in
/-- Complete original `pair_basis_hits` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem pair_basis_hits (e : I × Bool → Fin N) (he : Function.Injective e)
    (ω : (I → Reg 2) × (unusedWires e → Bool)) :
    pairHits e ((pairBasis e he).symm ω)=(fun i => isBellHit (ω.1 i)) := by
  have h := congrArg Prod.fst ((pairBasis e he).apply_symm_apply ω)
  change (fun i => isBellHit (((pairBasis e he) ((pairBasis e he).symm ω)).1 i))=_
  rw [h]

-- The unused outcomes are summed, never conditioned on or supplied as data.
/-- Complete original `paired_hit_mass` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem paired_hit_mass (e : I × Bool → Fin N) (he : Function.Injective e)
    (f : I → QState (Reg 2)) (u : unusedWires e → Bool → ℂ)
    (hu : ∀ w,qubitMass (u w)=1) (z : I → Bool) :
    (∑ σ : Reg N,if pairHits e σ=z then BornProb (pairedState e f u) σ else 0)=
      ∏ i : I,∑ r : Reg 2,if isBellHit r=z i then BornProb (f i) r else 0 := by
  rw [← Fintype.sum_equiv (pairBasis e he).symm
    (fun ω => if pairHits e ((pairBasis e he).symm ω)=z then
      BornProb (pairedState e f u) ((pairBasis e he).symm ω) else 0)
    (fun σ => if pairHits e σ=z then BornProb (pairedState e f u) σ else 0) (fun _ => rfl)]
  simp_rw [pair_basis_hits,BornProb,pair_basis_state,Complex.sq_norm,map_mul,map_prod]
  have hind (r : I → Reg 2) :
      (if (fun i => isBellHit (r i))=z then ∏ i : I,Complex.normSq (f i (r i)) else 0)=
        ∏ i : I,if isBellHit (r i)=z i then Complex.normSq (f i (r i)) else 0 := by
    by_cases h : (fun i => isBellHit (r i))=z
    · rw [ite_eq_left h]
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_left (congrFun h i)]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i,isBellHit (r i)≠z i := by
        by_contra hh
        apply h
        funext i
        exact not_not.mp (not_exists.mp hh i)
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right hi
  have hsum : (∑ η : unusedWires e → Bool,∏ w : unusedWires e,
      Complex.normSq (u w (η w)))=1 := by
    have hn := spin_tensor_normalized u hu
    simpa only [Normalized,spinTensor,Complex.sq_norm,map_prod] using hn
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ r : I → Reg 2,(if (fun i => isBellHit (r i))=z then
        ∏ i : I,Complex.normSq (f i (r i)) else 0)*
        (∑ η : unusedWires e → Bool,∏ w : unusedWires e,Complex.normSq (u w (η w))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η _
      split_ifs <;> simp
    _ = ∑ r : I → Reg 2,∏ i : I,
        if isBellHit (r i)=z i then Complex.normSq (f i (r i)) else 0 := by
      simp_rw [hsum,mul_one,hind]
    _ = _ := sum_tensor_weights (fun i r =>
      if isBellHit r=z i then Complex.normSq (f i r) else 0)

/-- This is the full flat native Run followed by the actual readout pushforward. -/
def nativePairHitMass (e : I × Bool → Fin N) (l : List I) (u : Fin N → Bool → ℂ)
    (z : I → Bool) : ℝ :=
  ∑ σ : Reg N,if pairHits e σ=z then
    BornProb (Run (1 : Matrix (Reg N) (Reg N) ℂ) (pairProgram e l) (spinTensor u)) σ else 0

/-- Complete original `native_pair_hit_product` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem native_pair_hit_product (e : I × Bool → Fin N) (he : Function.Injective e)
    (l : List I) (hl : l.Nodup) (hall : ∀ i,i∈l) (u : Fin N → Bool → ℂ)
    (hu : ∀ w,qubitMass (u w)=1) (z : I → Bool) :
    nativePairHitMass e l u z=
      ∏ i : I,(bellEventLaw (u (e (i,false))) (u (e (i,true)))
        (hu _) (hu _)).prob (z i) := by
  have hin : spinTensor u=pairedState e
      (fun i => pairInput (u (e (i,false))) (u (e (i,true)))) (fun w => u w.val) := by
    funext σ
    exact spin_tensor_pair_partition e he u σ
  have hrun := pair_program_transport e he l hl
    (fun i => pairInput (u (e (i,false))) (u (e (i,true)))) (fun w => u w.val)
  simp only [ite_eq_left (hall _)] at hrun
  unfold nativePairHitMass
  rw [hin,hrun]
  exact paired_hit_mass e he _ _ (fun w => hu w.val) z


/-- Construction for native Pair Hit Law in the retained bell joint model. -/
def nativePairHitLaw (e : I × Bool → Fin N) (he : Function.Injective e)
    (l : List I) (hl : l.Nodup) (hall : ∀ i,i∈l) (u : Fin N → Bool → ℂ)
    (hu : ∀ w,qubitMass (u w)=1) : FinDist (I → Bool) where
  prob := nativePairHitMass e l u
  nonneg z := Finset.sum_nonneg fun σ _ => by
    split_ifs
    · exact sq_nonneg _
    · exact le_refl _
  sum_one := by
    simp_rw [native_pair_hit_product e he l hl hall u hu]
    exact sum_family_mass _

/-- Complete original `native_pair_hit_enumeration` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem native_pair_hit_enumeration (e : I × Bool → Fin N) (he : Function.Injective e)
    (l k : List I) (hl : l.Nodup) (hk : k.Nodup) (hall : ∀ i,i∈l) (hkal : ∀ i,i∈k)
    (u : Fin N → Bool → ℂ) (hu : ∀ w,qubitMass (u w)=1) (z : I → Bool) :
    nativePairHitMass e l u z=nativePairHitMass e k u z := by
  rw [native_pair_hit_product e he l hl hall u hu,
    native_pair_hit_product e he k hk hkal u hu]

open Matched

variable {S : Type} [DecidableEq S] {n m : ℕ}

/-- Construction for matched Physical Fin in the retained bell joint model. -/
def matchedPhysicalFin (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (z : matchedSites J K τ × Bool) : Fin (n+m) :=
  finSumFinEquiv (pairPhysicalWire J K τ z)

/-- Construction for flat Cohort Address in the retained bell joint model. -/
def flatCohortAddress (J : Fin n → S) (K : Fin m → S) (w : Fin (n+m)) : S :=
  Sum.elim J K (finSumFinEquiv.symm w)

/-- Construction for flat Cohort Spin in the retained bell joint model. -/
def flatCohortSpin (a b c k : S → ℝ) (J : Fin n → S) (K : Fin m → S) :
    Fin (n+m) → Bool → ℂ := fun w => complexSpinor a b c k (flatCohortAddress J K w)

omit [Fintype I] [DecidableEq I] in
/-- Complete original `matched_physical_fin_injective` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem matched_physical_fin_injective (J : Fin n → S) (K : Fin m → S) (τ : S → S)
    (hτ : Function.Injective τ) : Function.Injective (matchedPhysicalFin J K τ) :=
  finSumFinEquiv.injective.comp (pair_physical_wire_injective J K τ hτ)

omit [Fintype I] [DecidableEq I] in
/-- Complete original `flat_cohort_left` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem flat_cohort_left (a b c k : S → ℝ) (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (x : matchedSites J K τ) :
    flatCohortSpin a b c k J K (matchedPhysicalFin J K τ (x,false))=complexSpinor a b c k x := by
  simp [flatCohortSpin,flatCohortAddress,matchedPhysicalFin,pairPhysicalWire,left_match_address]

omit [Fintype I] [DecidableEq I] in
/-- Complete original `flat_cohort_right` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem flat_cohort_right (a b c k : S → ℝ) (J : Fin n → S) (K : Fin m → S)
    (τ : S → S) (x : matchedSites J K τ) :
    flatCohortSpin a b c k J K (matchedPhysicalFin J K τ (x,true))=complexSpinor a b c k (τ x) := by
  simp [flatCohortSpin,flatCohortAddress,matchedPhysicalFin,pairPhysicalWire,right_match_address]

omit [Fintype I] [DecidableEq I] in
/-- Complete original `native_matched_hit_product` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem native_matched_hit_product (a b c k : S → ℝ)
    (hz : ∀ x,a x^2+b x^2+c x^2+k x^2=1)
    (J : Fin n → S) (K : Fin m → S) (τ : S → S) (hτ : Function.Injective τ)
    (l : List (matchedSites J K τ)) (hl : l.Nodup) (hall : ∀ x,x∈l)
    (z : matchedSites J K τ → Bool) :
    nativePairHitMass (matchedPhysicalFin J K τ) l (flatCohortSpin a b c k J K) z=
      ∏ x : matchedSites J K τ,(bellEventLaw (complexSpinor a b c k x)
        (complexSpinor a b c k (τ x)) (complex_spinor_mass a b c k hz x)
          (complex_spinor_mass a b c k hz (τ x))).prob (z x) := by
  have h := native_pair_hit_product (matchedPhysicalFin J K τ)
    (matched_physical_fin_injective J K τ hτ) l hl hall (flatCohortSpin a b c k J K)
    (fun w => complex_spinor_mass a b c k hz (flatCohortAddress J K w)) z
  simpa only [flat_cohort_left,flat_cohort_right] using h

omit [Fintype I] [DecidableEq I] [DecidableEq S] in
/-- Complete original `flat_cohort_from_address_projection` guarantee for `RetainedBellJoint`; all source hypotheses and output obligations are retained. -/
theorem flat_cohort_from_address_projection [Fintype S] [Nonempty S]
    (a b c k : S → ℝ) (J : Fin n → S) (K : Fin m → S) (σ : Reg (n+m)) :
    (Real.sqrt (Fintype.card S : ℝ) : ℂ)^(n+m)*
      capturedCohortAmplitude a b c k (flatCohortAddress J K) σ=
        spinTensor (flatCohortSpin a b c k J K) σ :=
  retained_cohort_amplitude a b c k (flatCohortAddress J K) σ

end
end Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.pairBasis
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.paired_hit_mass
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_pair_hit_product

#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.nativePairHitLaw
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_pair_hit_enumeration
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.native_matched_hit_product
#print axioms Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin.flat_cohort_from_address_projection
