/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Shared Copy Phases

Exactly Q+1 roots, sampled once per physical input and retained across every supplied copy.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- Exactly Q+1 roots, sampled once per physical input and retained across every supplied copy. -/
def rootPhase (Q : ℕ) (k : Fin (Q+1)) : ℂ :=
  Complex.exp (2*Real.pi*Complex.I/(Q+1 : ℕ))^k.val

/-- The actual chosen phase generator has exact order Q+1. -/
theorem phaseRoot_primitive (Q : ℕ) :
    IsPrimitiveRoot (Complex.exp (2*Real.pi*Complex.I/(Q+1 : ℕ))) (Q+1) :=
  Complex.isPrimitiveRoot_exp (Q+1) (by omega)

/-- Every actual shared local phase has modulus one. -/
theorem rootPhase_norm (Q : ℕ) (k : Fin (Q+1)) : ‖rootPhase Q k‖=1 := by
  simp only [rootPhase,norm_pow,(phaseRoot_primitive Q).norm'_eq_one (by omega),one_pow]

/-- Finite Fourier orthogonality resolves all multiplicities occurring in Q copies. -/
theorem local_moment (Q a b : ℕ) (ha : a ≤ Q) (hb : b ≤ Q) :
    (∑ k : Fin (Q+1),(1/(Q+1 : ℕ) : ℂ)*
      (rootPhase Q k)^a*star ((rootPhase Q k)^b))=
        if a=b then 1 else 0 := by
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/(Q+1 : ℕ))
  have hz := phaseRoot_primitive Q
  have hz0 : ζ≠0 := (hz.isUnit (by omega)).ne_zero
  have hzunit : ‖ζ‖=1 := hz.norm'_eq_one (by omega)
  have hn : (Q+1 : ℂ)≠0 := by exact_mod_cast (show Q+1≠0 by omega)
  have hterm (k : Fin (Q+1)) :
      (rootPhase Q k)^a*star ((rootPhase Q k)^b)=(ζ^a/ζ^b)^k.val := by
    have hc : star (ζ^(k.val*b))=(ζ^(k.val*b))⁻¹ := by
      exact (Complex.inv_eq_conj (by rw [norm_pow,hzunit,one_pow])).symm
    simp only [rootPhase,←pow_mul]
    change ζ^(k.val*a)*star (ζ^(k.val*b))=(ζ^a/ζ^b)^k.val
    rw [hc,div_pow,←pow_mul,←pow_mul,Nat.mul_comm a k.val,Nat.mul_comm b k.val]
    rfl
  have hsum : (∑ k : Fin (Q+1),(1/(Q+1 : ℕ) : ℂ)*
      (rootPhase Q k)^a*star ((rootPhase Q k)^b))=
        (1/(Q+1 : ℕ) : ℂ)*(∑ k : Fin (Q+1),(ζ^a/ζ^b)^k.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc,hterm]
  rw [hsum]
  by_cases hab : a=b
  · subst b
    simp [hz0,hn]
  · rw [ite_eq_right hab]
    have hr : ζ^a/ζ^b≠1 := by
      intro h
      have he : ζ^a=ζ^b := (div_eq_one_iff_eq (pow_ne_zero _ hz0)).mp h
      exact hab (hz.pow_inj (by omega) (by omega) he)
    have hp : (ζ^a/ζ^b)^(Q+1)=1 := by
      rw [div_pow,←pow_mul,←pow_mul,Nat.mul_comm a (Q+1),Nat.mul_comm b (Q+1),
        pow_mul,pow_mul,hz.pow_eq_one,one_pow,one_pow,div_self (by norm_num : (1 : ℂ)≠0)]
    have hg := geom_sum_mul (ζ^a/ζ^b) (Q+1)
    rw [hp,sub_self] at hg
    have hzero : (∑ k ∈ Finset.range (Q+1),(ζ^a/ζ^b)^k)=0 :=
      (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hr)
    have hs : (∑ k : Fin (Q+1),(ζ^a/ζ^b)^k.val)=0 := by
      simpa only [Fin.sum_univ_eq_sum_range] using hzero
    rw [hs,mul_zero]

/-- The actual number of occurrences of one address in the complete supplied copy sequence. -/
def multiplicity {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x : Fin Q → A) (a : A) : ℕ := Fintype.card {j : Fin Q // x j=a}

/-- Every actual address count is at most the total supplied copy count. -/
theorem multiplicity_le {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x : Fin Q → A) (a : A) : multiplicity x a ≤ Q := by
  simpa only [multiplicity,Fintype.card_fin] using
    (Fintype.card_subtype_le (fun j : Fin Q => x j=a))

/-- The actual copywise phase product groups into the true address multiplicities. -/
theorem phase_product_counts {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}
    (x : Fin Q → A) (z : A → ℂ) :
    (∏ j,z (x j))=∏ a,z a^(multiplicity x a) := by
  simpa only [Finset.prod_const,Finset.card_univ,multiplicity] using
    (Fintype.prod_fiberwise' x z).symm

/-- The complete uniform finite phase prior samples each local phase once per input. -/
def phaseMean {A : Type*} [Fintype A] (Q : ℕ) (f : (A → Fin (Q+1)) → ℂ) : ℂ :=
  ∑ ω,(∏ _a : A,(1/(Q+1 : ℕ) : ℂ))*f ω

/-- Independence is across sites; the same phase is retained across all supplied copies. -/
theorem phaseMean_prod {A : Type*} [Fintype A] (Q : ℕ) (f : A → Fin (Q+1) → ℂ) :
    phaseMean Q (fun ω => ∏ a,f a (ω a))=
      ∏ a,∑ k : Fin (Q+1),(1/(Q+1 : ℕ) : ℂ)*f a k := by
  unfold phaseMean
  simp_rw [←Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum (t := fun _ : A => (Finset.univ : Finset (Fin (Q+1))))
    (f := fun a k => (1/(Q+1 : ℕ) : ℂ)*f a k)).symm

/-- The actual shared-phase average preserves exactly equal address multiplicities at arbitrary fixed Q. -/
theorem shared_copy_character {A : Type*} [Fintype A] [DecidableEq A] (Q : ℕ)
    (x y : Fin Q → A) :
    phaseMean Q (fun ω => (∏ j,rootPhase Q (ω (x j)))*star (∏ j,rootPhase Q (ω (y j))))=
      if (∀ a,multiplicity x a=multiplicity y a) then 1 else 0 := by
  let f : A → Fin (Q+1) → ℂ := fun a k =>
    (rootPhase Q k)^(multiplicity x a)*star ((rootPhase Q k)^(multiplicity y a))
  have hf (ω : A → Fin (Q+1)) : (∏ a,f a (ω a))=
      (∏ j,rootPhase Q (ω (x j)))*star (∏ j,rootPhase Q (ω (y j))) := by
    rw [phase_product_counts x (fun a => rootPhase Q (ω a)),
      phase_product_counts y (fun a => rootPhase Q (ω a))]
    simp only [f,Finset.prod_mul_distrib,star_prod]
  have hfun : (fun ω : A → Fin (Q+1) =>
      (∏ j,rootPhase Q (ω (x j)))*star (∏ j,rootPhase Q (ω (y j))))=
        fun ω => ∏ a,f a (ω a) := by
    funext ω
    exact (hf ω).symm
  rw [hfun,phaseMean_prod]
  have hlocal (a : A) : (∑ k : Fin (Q+1),(1/(Q+1 : ℕ) : ℂ)*f a k)=
      if multiplicity x a=multiplicity y a then 1 else 0 := by
    simpa only [f,mul_assoc] using local_moment Q _ _ (multiplicity_le x a) (multiplicity_le y a)
  simp_rw [hlocal]
  by_cases h : ∀ a,multiplicity x a=multiplicity y a
  · simp [h]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨a,ha⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)

end Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

namespace Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- The unphased amplitude of Q identical complete supplied copies. -/
def copyAmplitude {A B : Type*} (ψ : A → B → ℂ) (Q : ℕ) (x : Fin Q → A × B) : ℂ :=
  ∏ j,ψ (x j).1 (x j).2

/-- The actual tensor amplitude uses one local phase assignment shared by every supplied copy. -/
def sharedPhasedCopyAmplitude {A B : Type*} (ψ : A → B → ℂ) (Q : ℕ)
    (ω : A → Fin (Q+1)) (x : Fin Q → A × B) : ℂ :=
  ∏ j,rootPhase Q (ω (x j).1)*ψ (x j).1 (x j).2

/-- The shared phase prior factors out a fixed complex amplitude without resampling any site. -/
theorem phaseMean_mul_const {A : Type*} [Fintype A] (Q : ℕ)
    (f : (A → Fin (Q+1)) → ℂ) (c : ℂ) :
    phaseMean Q (fun ω => f ω*c)=phaseMean Q f*c := by
  unfold phaseMean
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- A literal entry of the actual shared-phase averaged copy density vanishes exactly between different address multiplicities. -/
theorem shared_phase_density_entry {A B : Type*} [Fintype A] [DecidableEq A]
    (ψ : A → B → ℂ) (Q : ℕ) (x y : Fin Q → A × B) :
    phaseMean Q (fun ω => sharedPhasedCopyAmplitude ψ Q ω x*
      star (sharedPhasedCopyAmplitude ψ Q ω y))=
        (if (∀ a,multiplicity (fun j => (x j).1) a=multiplicity (fun j => (y j).1) a)
          then 1 else 0)*copyAmplitude ψ Q x*star (copyAmplitude ψ Q y) := by
  have hf (ω : A → Fin (Q+1)) (z : Fin Q → A × B) :
      sharedPhasedCopyAmplitude ψ Q ω z=
        (∏ j,rootPhase Q (ω (z j).1))*copyAmplitude ψ Q z := by
    simp only [sharedPhasedCopyAmplitude,copyAmplitude,Finset.prod_mul_distrib]
  have he (ω : A → Fin (Q+1)) :
      sharedPhasedCopyAmplitude ψ Q ω x*star (sharedPhasedCopyAmplitude ψ Q ω y)=
        ((∏ j,rootPhase Q (ω (x j).1))*star (∏ j,rootPhase Q (ω (y j).1)))*
          (copyAmplitude ψ Q x*star (copyAmplitude ψ Q y)) := by
    rw [hf ω x,hf ω y,star_mul]
    ring
  have hfun : (fun ω => sharedPhasedCopyAmplitude ψ Q ω x*star (sharedPhasedCopyAmplitude ψ Q ω y))=
      (fun ω => ((∏ j,rootPhase Q (ω (x j).1))*star (∏ j,rootPhase Q (ω (y j).1)))*
        (copyAmplitude ψ Q x*star (copyAmplitude ψ Q y))) := by
    funext ω
    exact he ω
  rw [hfun,phaseMean_mul_const,shared_copy_character]
  ring

/-- Every single shared-phase realization gives a normalized actual Q-copy physical vector. -/
theorem sharedPhasedCopyAmplitude_normalized {A B : Type*} [Fintype A] [Fintype B]
    (ψ : A → B → ℂ) (hψ : Normalized (fun z : A × B => ψ z.1 z.2))
    (Q : ℕ) (ω : A → Fin (Q+1)) :
    Normalized (sharedPhasedCopyAmplitude ψ Q ω) := by
  have hs : (∑ z : A × B,‖rootPhase Q (ω z.1)*ψ z.1 z.2‖^2)=1 := by
    simpa only [Normalized,norm_mul,rootPhase_norm,one_mul] using hψ
  change (∑ x : Fin Q → A × B,‖∏ j : Fin Q,rootPhase Q (ω (x j).1)*ψ (x j).1 (x j).2‖^2)=1
  simp only [norm_prod,←Finset.prod_pow]
  calc _ = ∏ _j : Fin Q,∑ z : A × B,‖rootPhase Q (ω z.1)*ψ z.1 z.2‖^2 :=
        (Fintype.prod_sum (fun (_j : Fin Q) (z : A × B) => ‖rootPhase Q (ω z.1)*ψ z.1 z.2‖^2)).symm
       _ = 1 := by simp only [hs,Finset.prod_const_one]

end Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases
