/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeAndOr
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Positivity

@[expose] public section


/-! # Coefficients of actual Boolean-cube bounded multilinear polynomials

Demand: Ambainis--Childs--Liu, arXiv1012.3174v3 Lemma 15.
Restriction to a monomial's support is implemented by killCompl. A finite
enumeration makes the full-variable Mobius theorem applicable while
preserving the original arbitrary-universe variable type.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.CubeCoeff
open MvPolynomial
universe u

/-- Extend a valuation by zero on every variable outside an actual injective coordinate family. -/
def extendZero {I : Type} {σ : Type u} (f : I → σ) (hf : Function.Injective f)
    (x : I → ℝ) (a : σ) : ℝ :=
  if h : a ∈ Set.range f then x ((Equiv.ofInjective f hf).symm ⟨a,h⟩) else 0

/-- Zero-extension of a Boolean valuation remains Boolean at every original coordinate. -/
theorem extendBool {I : Type} {σ : Type u} (f : I → σ) (hf : Function.Injective f)
    (x : I → ℝ) (hx : ∀ i, x i=0 ∨ x i=1) :
    ∀ a, extendZero f hf x a=0 ∨ extendZero f hf x a=1 := by
  intro a
  unfold extendZero
  split_ifs
  · exact hx _
  · exact Or.inl rfl

/-- Evaluating the actual restricted polynomial is exactly evaluation at the zero-extended original input. -/
theorem restrictEval {I : Type} {σ : Type u} (f : I → σ) (hf : Function.Injective f)
    (p : MvPolynomial σ ℝ) (x : I → ℝ) :
    eval x (p.killCompl hf) = eval (extendZero f hf x) p := by
  have he : (aeval x : MvPolynomial I ℝ →ₐ[ℝ] ℝ).comp (killCompl hf) =
      aeval (extendZero f hf x) := by
    rw [killCompl, comp_aeval]
    congr 1
    funext a
    by_cases h : a ∈ Set.range f <;> simp [extendZero, h]
  simpa only [AlgHom.comp_apply, aeval_eq_eval] using
    congrArg (fun h : MvPolynomial σ ℝ →ₐ[ℝ] ℝ => h p) he

/-- Restriction preserves the actual coefficientwise multilinearity condition. -/
theorem restrictMulti {I : Type} {σ : Type u} (f : I → σ) (hf : Function.Injective f)
    (p : MvPolynomial σ ℝ)
    (hp : ∀ e : σ →₀ ℕ, p.coeff e ≠ 0 → ∀ a, e a ≤ 1) :
    ∀ e : I →₀ ℕ, (p.killCompl hf).coeff e ≠ 0 → ∀ i, e i ≤ 1 := by
  intro e he i
  rw [coeff_killCompl] at he
  have h := hp (e.mapDomain f) he (f i)
  simpa only [Finsupp.mapDomain_apply_of_injective hf] using h

/-- Mobius inversion bounds the full-variable coefficient by the actual number of Boolean subsets. -/
theorem topBound {I : Type} [Fintype I] [DecidableEq I] (p : MvPolynomial I ℝ)
    (hp : ∀ e : I →₀ ℕ, p.coeff e ≠ 0 → ∀ i, e i ≤ 1)
    (hb : ∀ x : I → ℝ, (∀ i, x i=0 ∨ x i=1) → |eval x p| ≤ 1) :
    |p.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1)| ≤
      (2 : ℝ)^(Fintype.card I) := by
  rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.mobius_top_coefficient p hp]
  calc
    |∑ S ∈ Finset.univ.powerset, (-1 : ℝ)^((Finset.univ\S).card)*
        eval (fun i => if i∈S then 1 else 0) p| ≤
      ∑ S ∈ Finset.univ.powerset,
        |(-1 : ℝ)^((Finset.univ\S).card)*eval (fun i => if i∈S then 1 else 0) p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ (Finset.univ : Finset I).powerset, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro S _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      apply hb
      intro i
      by_cases h : i∈S <;> simp [h]
    _ = (2 : ℝ)^(Fintype.card I) := by simp

/-- Every genuine nonzero monomial coefficient is bounded by two to the size of its support. -/
theorem coeffBound {σ : Type u} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (hp : ∀ e : σ →₀ ℕ, p.coeff e ≠ 0 → ∀ a, e a ≤ 1)
    (hb : ∀ x : σ → ℝ, (∀ a, x a=0 ∨ x a=1) → |eval x p| ≤ 1)
    (d : σ →₀ ℕ) : |p.coeff d| ≤ (2 : ℝ)^d.support.card := by
  by_cases hc : p.coeff d=0
  · rw [hc, abs_zero]
    positivity
  let D := {a : σ // a ∈ d.support}
  let f : Fin (Fintype.card D) → σ := fun i => ((Fintype.equivFin D).symm i).val
  have hf : Function.Injective f := Subtype.val_injective.comp (Fintype.equivFin D).symm.injective
  let top : Fin (Fintype.card D) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  have hm : top.mapDomain f=d := by
    ext a
    by_cases ha : a ∈ d.support
    · let i : Fin (Fintype.card D) := (Fintype.equivFin D) ⟨a,ha⟩
      have hi : f i=a := by simp [f, i]
      rw [← hi, Finsupp.mapDomain_apply_of_injective hf]
      have hpos : 0 < d (f i) := Nat.pos_of_ne_zero (by
        rw [hi]
        exact Finsupp.mem_support_iff.mp ha)
      have hle := hp d hc (f i)
      change 1=d (f i)
      omega
    · have hn : a ∉ Set.range f := by
        rintro ⟨i,hi⟩
        apply ha
        exact hi ▸ ((Fintype.equivFin D).symm i).property
      rw [Finsupp.mapDomain_of_notMem_range top a hn]
      by_contra h
      exact ha (Finsupp.mem_support_iff.mpr (Ne.symm h))
  have hcoef : (p.killCompl hf).coeff top=p.coeff d := by
    rw [coeff_killCompl, hm]
  have hval : ∀ x : Fin (Fintype.card D) → ℝ,
      (∀ i, x i=0 ∨ x i=1) → |eval x (p.killCompl hf)| ≤ 1 := by
    intro x hx
    rw [restrictEval]
    exact hb _ (extendBool f hf x hx)
  have h := topBound (p.killCompl hf) (restrictMulti f hf p hp) hval
  simp only [Fintype.card_fin] at h
  change |(p.killCompl hf).coeff top| ≤ (2 : ℝ)^(Fintype.card D) at h
  rw [hcoef] at h
  simpa only [D, Fintype.card_coe] using h

end Qatlib.Concepts.QueryComplexity.DegreeMethod.CubeCoeff
