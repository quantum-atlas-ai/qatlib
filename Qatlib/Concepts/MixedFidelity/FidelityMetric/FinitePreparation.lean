/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

open Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

/-!
# Finite Preparation

A classical label is replaced with its normalized state by an actual rectangular Kraus operator.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
open Qatlib
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- A classical label is replaced with its normalized state by an actual rectangular Kraus operator. -/
def preparationKraus {D E : ℕ} (ψ : Fin D → QState (Fin E)) (i : Fin D) :
    Matrix (Fin E) (Fin D) ℂ := fun u j => if j=i then ψ i u else 0

/-- The Gram matrix of each actual preparation operator is exactly its original classical label projector. -/
theorem preparationKraus_gram_entry {D E : ℕ} (ψ : Fin D → QState (Fin E))
    (hψ : ∀ i,Normalized (ψ i)) (i j k : Fin D) :
    ((preparationKraus ψ i).conjTranspose*preparationKraus ψ i) j k=
      if j=i ∧ k=i then 1 else 0 := by
  have hi : (∑ u : Fin E, star (ψ i u)*ψ i u)=(1 : ℂ) := by
    simpa only [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Pi.star_apply] using (normalized_iff_inner_self (ψ i)).mp (hψ i)
  by_cases hj : j=i
  · subst j
    by_cases hk : k=i
    · subst k
      simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,preparationKraus] using hi
    · simp [Matrix.mul_apply,Matrix.conjTranspose_apply,preparationKraus,hk]
  · simp [Matrix.mul_apply,Matrix.conjTranspose_apply,preparationKraus,hj]

/-- The same fixed preparation family is trace preserving on the entire input matrix space. -/
theorem preparationKraus_complete {D E : ℕ} (ψ : Fin D → QState (Fin E))
    (hψ : ∀ i,Normalized (ψ i)) :
    ∑ i,(preparationKraus ψ i).conjTranspose*preparationKraus ψ i=1 := by
  ext j k
  simp only [Matrix.sum_apply,preparationKraus_gram_entry ψ hψ,Matrix.one_apply]
  by_cases h : j=k
  · subst k
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    rintro ⟨hj,hk⟩
    exact h (hj.trans hk.symm)

/-- One hypothesis-independent finite CPTP source channel prepares the specified state family from classical labels. -/
def preparationChannel {D E : ℕ} (ψ : Fin D → QState (Fin E))
    (hψ : ∀ i,Normalized (ψ i)) : QuantumChannel D E :=
  (Instrument.ofKraus (preparationKraus ψ) (preparationKraus_complete ψ hψ)).forget

/-- The constructed source channel sends a diagonal law to the literal mixture of the same prepared pure states. -/
theorem preparationChannel_diagonal {D E : ℕ} (ψ : Fin D → QState (Fin E))
    (hψ : ∀ i,Normalized (ψ i)) (p : Fin D → ℝ) :
    (preparationChannel ψ hψ).map (diagDensity p)=
      ∑ i,(p i : ℂ) • outerProduct (ψ i) := by
  rw [preparationChannel,Instrument.forget_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Instrument.ofKraus_branch]
  ext u v
  simp [preparationKraus,diagDensity,Matrix.mul_apply,Matrix.conjTranspose_apply,
    outerProduct,Matrix.diagonal_apply,apply_ite]
  ring

/-- Every genuine classical probability law gives a positive trace-one diagonal input. -/
theorem diagonal_density {D : ℕ} {p : Fin D → ℝ} (hp : IsProbVector p) :
    IsDensityOperator (diagDensity p) := by
  constructor
  · rw [diagDensity,Matrix.posSemidef_diagonal_iff]
    intro i
    exact_mod_cast hp.1 i
  · simp only [diagDensity,Matrix.trace_diagonal]
    exact_mod_cast hp.2

/-- The literal prepared mixtures retain at least their classical input affinity under the same actual CPTP channel. -/
theorem preparation_affinity_lower {D E : ℕ} (ψ : Fin D → QState (Fin E))
    (hψ : ∀ i,Normalized (ψ i)) {p q : Fin D → ℝ}
    (hp : IsProbVector p) (hq : IsProbVector q) :
    (∑ i,Real.sqrt (p i*q i)) ≤
      Froot (∑ i,(p i : ℂ) • outerProduct (ψ i))
        (∑ i,(q i : ℂ) • outerProduct (ψ i)) := by
  have hρ := diagonal_density hp
  have hσ := diagonal_density hq
  have hdiag := (g1 D (diagDensity p) (diagDensity q) hρ hσ).2.2.2.2.2.1 p q hp hq
  have h := froot_channel_le (preparationChannel ψ hψ) hρ hσ
  rw [hdiag,preparationChannel_diagonal,preparationChannel_diagonal] at h
  exact h

/-- The four actual sign-pair probabilities, with the same ordering under both hypotheses. -/
def signPairLaw (ρ : ℝ) (i : Fin 4) : ℝ :=
  if i.val=0 ∨ i.val=3 then (1+ρ)/4 else (1-ρ)/4

/-- Every sign-pair correlation in the closed unit interval defines an actual normalized law. -/
theorem signPairLaw_prob (ρ : ℝ) (hlo : -1≤ρ) (hhi : ρ≤1) :
    IsProbVector (signPairLaw ρ) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [signPairLaw] <;> linarith
  · norm_num [Fin.sum_univ_succ,signPairLaw]
    ring

/-- Bounded correlations give a strictly positive classical affinity without any state-dependent certificate. -/
theorem signPairLaw_affinity (a ρ ξ : ℝ) (ha1 : a<1)
    (hρ : |ρ|≤a) (hξ : |ξ|≤a) :
    1-a ≤ ∑ i : Fin 4,Real.sqrt (signPairLaw ρ i*signPairLaw ξ i) := by
  let c : ℝ := (1-a)/4
  have hc : 0≤c := by dsimp [c]; linarith
  have hpoint (t : ℝ) (ht : |t|≤a) (i : Fin 4) : c ≤ signPairLaw t i := by
    obtain ⟨htlo,hthi⟩ := abs_le.mp ht
    unfold signPairLaw
    split_ifs <;> dsimp [c] <;> linarith
  have hi (i : Fin 4) : c≤Real.sqrt (signPairLaw ρ i*signPairLaw ξ i) := by
    have hp := hpoint ρ hρ i
    have hq := hpoint ξ hξ i
    calc c=Real.sqrt (c*c) := (Real.sqrt_mul_self hc).symm
         _ ≤ _ := Real.sqrt_le_sqrt (mul_le_mul hp hq hc (hc.trans hp))
  calc 1-a=∑ _i : Fin 4,c := by norm_num [Fin.sum_univ_succ,c]; ring
       _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

/-- Every fixed normalized four-state preparation family has root fidelity at least one minus the public correlation radius. -/
theorem prepared_signPair_fidelity_lower {E : ℕ} (ψ : Fin 4 → QState (Fin E))
    (hψ : ∀ i,Normalized (ψ i)) (a ρ ξ : ℝ) (ha1 : a<1)
    (hρ : |ρ|≤a) (hξ : |ξ|≤a) :
    1-a ≤ Froot (∑ i,(signPairLaw ρ i : ℂ) • outerProduct (ψ i))
      (∑ i,(signPairLaw ξ i : ℂ) • outerProduct (ψ i)) := by
  have hρb := abs_le.mp hρ
  have hξb := abs_le.mp hξ
  exact (signPairLaw_affinity a ρ ξ ha1 hρ hξ).trans
    (preparation_affinity_lower ψ hψ
      (signPairLaw_prob ρ (by linarith) (by linarith))
      (signPairLaw_prob ξ (by linarith) (by linarith)))

end Qatlib.Concepts.MixedFidelity.FidelityMetric.FinitePreparation
