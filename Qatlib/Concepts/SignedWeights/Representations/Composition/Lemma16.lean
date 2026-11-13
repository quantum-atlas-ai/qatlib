/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Norms and Eigenvectors of Composed Witnesses

This module exposes the matrix norm and eigenvector calculations underlying the adversary
composition construction in [HoyerLeeSpalek2007]. For Hermitian outer and inner matrices whose
inner entries vanish on equal-output pairs, the operator norm of `weightedAdvGamma` is the outer
norm times the product of the inner norms.

The explicit product vector evaluates the outer vector on the inner output word and multiplies
it by the inner vector coordinates. The eigenvector statements retain their respective
nonzero-vector and positive-inner-norm hypotheses.

## Main statements

- `lemma16_norm_eq` gives the product formula for the operator norm.
* `lemma16_product_eigenvector` verifies the explicit product eigenvector and its extremal
  eigenvalue magnitude.
* `lemma16_principal_eigenvector_exists` supplies a nonzero norm-attaining eigenvector when all
  inner norms are positive.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007], Negative weights make adversaries
  stronger, Lemma 16.
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Composition

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp

noncomputable section

/-- For Hermitian factors whose inner entries vanish on equal-output pairs, the norm of
`weightedAdvGamma` is the outer norm times the product of the inner norms, as in Lemma 16 of
[HoyerLeeSpalek2007]. -/
theorem lemma16_norm_eq
    {k : ℕ} {X : Fin k → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool)
    (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hGf : Gf.IsHermitian) (hGg : ∀ i, (Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i), g i u = g i v → Gg i u v = 0) :
    ‖weightedAdvGamma g f Gf Gg‖ = ‖Gf‖ * ∏ i, ‖Gg i‖ :=
  weightedAdvGamma_norm_eq g f Gf Gg hGf hGg hzg

/-- Given an extremal outer eigenvector and inner eigenvectors with eigenvalues equal to the
inner norms, their nonzero product vector is an eigenvector of `weightedAdvGamma`. Its
eigenvalue is the outer eigenvalue times the product of inner norms and has magnitude equal
to the composed norm, as in [HoyerLeeSpalek2007]. -/
theorem lemma16_product_eigenvector
    {k : ℕ} {X : Fin k → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hGf : Gf.IsHermitian) (hGg : ∀ i, (Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i), g i u = g i v → Gg i u v = 0)
    (uf : QState (Fin k → Bool)) (ui : ∀ i, QState (X i)) (lamf : ℝ)
    (hef : Gf *ᵥ uf = (lamf : ℂ) • uf) (habsf : |lamf| = ‖Gf‖)
    (hei : ∀ i, Gg i *ᵥ ui i = ((‖Gg i‖ : ℝ) : ℂ) • ui i) :
    (fun x : (i : Fin k) → X i =>
        uf (fun i => g i (x i)) * ∏ i, ui i (x i)) ≠ 0 →
      weightedAdvGamma g f Gf Gg *ᵥ
          (fun x : (i : Fin k) → X i =>
            uf (fun i => g i (x i)) * ∏ i, ui i (x i)) =
        ((lamf * ∏ i, ‖Gg i‖ : ℝ) : ℂ) •
          (fun x : (i : Fin k) → X i =>
            uf (fun i => g i (x i)) * ∏ i, ui i (x i)) ∧
      |lamf * ∏ i, ‖Gg i‖| = ‖weightedAdvGamma g f Gf Gg‖ := by
  intro _
  classical
  let e : ((i : Fin k) → X i) → (Fin k → Bool) := fun x i => g i (x i)
  let r : ℝ := ∏ i, ‖Gg i‖
  constructor
  · funext x
    change (∑ y : (i : Fin k) → X i,
      Gf (e x) (e y) * (∏ i, (diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) (y i)) *
        (uf (e y) * ∏ i, ui i (y i))) =
      ((lamf * r : ℝ) : ℂ) * (uf (e x) * ∏ i, ui i (x i))
    calc
      _ = ∑ y : (i : Fin k) → X i, (Gf (e x) (e y) * uf (e y)) *
          ∏ i, ((diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) (y i) * ui i (y i)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.prod_mul_distrib]
        ring
      _ = ∑ s : Fin k → Bool, (Gf (e x) s * uf s) *
          ∏ i, (‖Gg i‖ : ℂ) * ui i (x i) := by
        have hsum := weightedAdv_sum_by_outputs g (fun s => Gf (e x) s * uf s)
          (fun i y => (diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) y * ui i y)
        change (∑ y : (i : Fin k) → X i,
          (Gf (e x) (e y) * uf (e y)) *
            ∏ i, ((diagonal (fun _ : X i => (‖Gg i‖ : ℂ)) + Gg i) (x i) (y i) * ui i (y i))) = _
        rw [hsum]
        simp_rw [weightedAdv_factor_fiber_action (g _) (Gg _) (hzg _) (ui _) (hei _)]
      _ = (∑ s : Fin k → Bool, Gf (e x) s * uf s) * ∏ i, (‖Gg i‖ : ℂ) * ui i (x i) := by
        rw [Finset.sum_mul]
      _ = (lamf : ℂ) * uf (e x) * ∏ i, (‖Gg i‖ : ℂ) * ui i (x i) := by
        have he := congrFun hef (e x)
        change (∑ s : Fin k → Bool, Gf (e x) s * uf s) = (lamf : ℂ) * uf (e x) at he
        rw [he]
      _ = _ := by
        simp only [Finset.prod_mul_distrib, r, Complex.ofReal_mul, Complex.ofReal_prod]
        ring
  · rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg (Gg i))),
      habsf, weightedAdvGamma_norm_eq g f Gf Gg hGf hGg hzg]

/-- When the Hermitian inner factors have positive norms and vanish on equal-output pairs, the
composed matrix has a nonzero eigenvector whose eigenvalue magnitude is the outer norm times
the product of inner norms, as in [HoyerLeeSpalek2007]. -/
theorem lemma16_principal_eigenvector_exists
    {k : ℕ} {X : Fin k → Type}
    [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (g : ∀ i, X i → Bool) (f : (Fin k → Bool) → Bool)
    (Gf : Matrix (Fin k → Bool) (Fin k → Bool) ℂ)
    (Gg : ∀ i, Matrix (X i) (X i) ℂ)
    (hGf : Gf.IsHermitian) (hGg : ∀ i, (Gg i).IsHermitian)
    (hzg : ∀ (i : Fin k) (u v : X i), g i u = g i v → Gg i u v = 0)
    (hpos : ∀ i, 0 < ‖Gg i‖) :
    ∃ (dh : QState ((i : Fin k) → X i)) (lam : ℝ), dh ≠ 0 ∧
      weightedAdvGamma g f Gf Gg *ᵥ dh = (lam : ℂ) • dh ∧
      |lam| = ‖Gf‖ * ∏ i, ‖Gg i‖ :=
  weightedAdvGamma_product_eigenvector g f Gf Gg hGf hGg hzg hpos

end

end Qatlib.Concepts.SignedWeights.Representations.Composition
