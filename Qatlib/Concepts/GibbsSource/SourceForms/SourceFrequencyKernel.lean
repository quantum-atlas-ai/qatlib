/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FrequencyPushforward

@[expose] public section


/-! # Zero source plain form with repeated frequency labels

The existing Gaussian kernel theorem applies to distinct frequencies. A
finite pushforward makes those frequencies distinct without discarding any
original transition. The source weight and its physical half are kept by
the already proved source-family thermal transport.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- Source-weight version of the existing distinct-frequency kernel theorem.
No positivity assumption on the input matrix `ρ` is used. -/
theorem ckgSourcePlainForm_re_eq_zero_iff_of_injective {β : ℝ}
    (hβ : 0 < β) {m : ℕ} (ν : Fin m → ℝ) (hν : Function.Injective ν)
    (ρ : Operator D) (A : Fin m → Operator D) (X : Operator D) :
    (ckgSourcePlainForm β ρ ν A X).re = 0 ↔
      ∀ a, parentFactor ρ (A a) X = 0 := by
  rw [ckgSourcePlainForm_eq_smulFamily β ρ ν A X,
    ckgWplainForm_eq_zero_iff hβ ν hν]
  simp only [parentFactor_smul]
  constructor
  · intro h a
    have hc : (Real.exp (β * ν a / 4) : ℂ) ≠ 0 := by
      exact_mod_cast Real.exp_ne_zero (β * ν a / 4)
    exact (smul_eq_zero.mp (h a)).resolve_left hc
  · intro h a
    rw [h a, smul_zero]

/-- Exact grouped criterion. Repeated original labels are allowed; only the
frequency values of the buckets are required to be distinct. Empty buckets
cause no problem, so the label map need not be surjective. -/
theorem ckgSourcePlainForm_re_eq_zero_iff_pushforward {β : ℝ}
    (hβ : 0 < β) {m : ℕ} (f : ι → Fin m) (ν : Fin m → ℝ)
    (hν : Function.Injective ν) (ρ : Operator D) (A : ι → Operator D)
    (X : Operator D) :
    (ckgSourcePlainForm β ρ (ν ∘ f) A X).re = 0 ↔
      ∀ k, parentFactor ρ (frequencyBucket f A k) X = 0 := by
  change (wplainForm (fun a b => ckgSourceWeight β (ν (f a)) (ν (f b)))
    ρ A X).re = 0 ↔ _
  rw [wplainForm_pushforward f (fun k l => ckgSourceWeight β (ν k) (ν l))]
  exact ckgSourcePlainForm_re_eq_zero_iff_of_injective hβ ν hν ρ
    (frequencyBucket f A) X

/-- Zero source energy implies the first-order factor of the reconstructed
proposal vanishes. Frequencies may repeat, the finite label type is arbitrary,
and no input positive-definiteness or target kernel premise is supplied. -/
theorem ckgSourcePlainForm_re_eq_zero_imp_parentFactor_sum {β : ℝ}
    (hβ : 0 < β) (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D)
    (X : Operator D) (hzero : (ckgSourcePlainForm β ρ ν A X).re = 0) :
    parentFactor ρ (∑ a, A a) X = 0 := by
  classical
  let S : Finset ℝ := Finset.univ.image ν
  let e : ↥S ≃ Fin (Fintype.card ↥S) := Fintype.equivFin ↥S
  let f : ι → Fin (Fintype.card ↥S) := fun a => e ⟨ν a, by
    change ν a ∈ Finset.univ.image ν
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  let u : Fin (Fintype.card ↥S) → ℝ := fun k => (e.symm k).val
  have hu : Function.Injective u := by
    intro k l hkl
    apply e.symm.injective
    exact Subtype.ext hkl
  have huf : u ∘ f = ν := by
    funext a
    change ((e.symm (f a) : ↥S) : ℝ) = ν a
    simp only [f, Equiv.symm_apply_apply]
  have hz : (ckgSourcePlainForm β ρ (u ∘ f) A X).re = 0 := by
    rw [huf]
    exact hzero
  have hb : ∀ k, parentFactor ρ (frequencyBucket f A k) X = 0 :=
    (ckgSourcePlainForm_re_eq_zero_iff_pushforward hβ f u hu ρ A X).mp hz
  calc
    parentFactor ρ (∑ a, A a) X =
        parentFactor ρ (∑ k, frequencyBucket f A k) X := by
      rw [frequencyBucket_sum]
    _ = ∑ k, parentFactor ρ (frequencyBucket f A k) X :=
      parentFactor_sum ρ (frequencyBucket f A) X
    _ = 0 := Finset.sum_eq_zero fun k _ => hb k

/-- In the completely degenerate frequency case the exact zero condition is
the factor of the total proposal, rather than its separate labelled terms. -/
theorem ckgSourcePlainForm_re_eq_zero_iff_of_constant {β : ℝ}
    (hβ : 0 < β) (ρ : Operator D) (ω : ℝ) (A : ι → Operator D)
    (X : Operator D) :
    (ckgSourcePlainForm β ρ (fun _ : ι => ω) A X).re = 0 ↔
      parentFactor ρ (∑ a, A a) X = 0 := by
  classical
  let f : ι → Fin 1 := fun _ => 0
  have hν : Function.Injective (fun _ : Fin 1 => ω) :=
    fun a b _ => Subsingleton.elim a b
  constructor
  · exact ckgSourcePlainForm_re_eq_zero_imp_parentFactor_sum hβ ρ
      (fun _ : ι => ω) A X
  · intro h
    apply (ckgSourcePlainForm_re_eq_zero_iff_pushforward hβ f
      (fun _ : Fin 1 => ω) hν ρ A X).mpr
    intro k
    have hk : k = 0 := Subsingleton.elim k 0
    subst k
    simpa [frequencyBucket, f] using h

end Qatlib.Concepts.GibbsSource.SourceForms
