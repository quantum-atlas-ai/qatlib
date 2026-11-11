/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# NegWeights06, Lemma 16 — spectral norm and principal eigenvector of the composition

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Definition 6 and Lemma 16, §6.1, printed page 16:

For the composed adversary matrix `Γh` of Definition 6 and principal unit
eigenvectors `δf`, `δgi` of the component matrices,

`‖Γh‖ = ‖Γf‖ · ∏ᵢ ‖Γgi‖`, and `δh[x] = δf[x̃] · ∏ᵢ δgi[xᵢ]` is a principal
eigenvector of `Γh`.

The frozen construction `weightedAdvGamma` folds the diagonal blocks `‖Γg‖•I`
into the factor `‖Γg‖•I + Γg` (entrywise identical to Definition 6 because the
same-output entries of `Γg` vanish).  The norm equality is the frozen
`weightedAdvGamma_norm_eq`; the product eigenvector identity is re-derived from
the frozen fiber-action and output-sum reorganizations, with the printed
eigenvalue `λf · ∏ᵢ ‖Γgi‖`.  The existence of a nonzero principal eigenvector
is the frozen `weightedAdvGamma_product_eigenvector` (valid when every block has
positive spectral norm).
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.Composition

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp

noncomputable section

/-- **Lemma 16, spectral-norm equality (printed Definition 6).**
For Boolean outer function `f`, Boolean blocks `g`, and Hermitian component
matrices `Gf`, `Gg` vanishing on same-output pairs,
`‖weightedAdvGamma g f Gf Gg‖ = ‖Gf‖ · ∏ᵢ ‖Gg i‖`.

This is the first assertion of quant-ph/0611054v2 Lemma 16 (p. 16); the frozen
`weightedAdvGamma` is Definition 6 with the diagonal block convention. -/
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

/-- **Lemma 16, product principal eigenvector.**
Let `δf` be a principal eigenvector of `Gf` with eigenvalue `λf` satisfying
`|λf| = ‖Gf‖`, and let `δgi` be principal eigenvectors of `Gg i` with eigenvalue
`‖Gg i‖` (the positive-norm principal eigenvalue).  If the product vector
`δh[x] = δf[e(x)] · ∏ᵢ δgi[xᵢ]`, where `e(x) = fun i => g i (x i)`, is nonzero,
then it is a principal eigenvector of `Γh` with eigenvalue `λf · ∏ᵢ ‖Gg i‖`,
and that eigenvalue has absolute value `‖Γh‖`.

This is the second assertion of quant-ph/0611054v2 Lemma 16 (p. 16).  The
frozen `weightedAdv_factor_fiber_action` supplies the two-color fiber action
and `weightedAdv_sum_by_outputs` supplies the reorganization by the outer
Boolean output tuple. -/
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

/-- **Lemma 16, existence of a nonzero principal eigenvector.**
When every block has positive spectral norm, `Γh` has a nonzero principal
eigenvector whose eigenvalue has absolute value `‖Γf‖ · ∏ᵢ ‖Γgi‖`.

This is the frozen `weightedAdvGamma_product_eigenvector`; combined with
`lemma16_product_eigenvector` it gives the printed statement that the product
`δh` is a principal eigenvector. -/
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

end Qatlib.Papers.NegWeights06.MainResults.Composition
