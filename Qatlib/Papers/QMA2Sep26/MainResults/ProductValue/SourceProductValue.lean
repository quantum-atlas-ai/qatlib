/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMA2Sep26.MainResults.SourceModel
import Mathlib.GroupTheory.Perm.Fin

set_option backward.isDefEq.respectTransparency false

/-!
# Product Value Bound for the Four-Copy Antisymmetric Projector

This module formalizes Lemma 4.1 of Bostanci, Grewal, Haferkamp, Huang, Hwang,
Natarajan, and Nirkhe showing that for every local dimension `d ≥ 4`, the
bipartite product value `hSep(Π_d^-)` of the four-register antisymmetric
projector across the `(12 | 34)` cut is at most `1 / 3`.

## Main statements

* `reducedForm_numeric_bound`: numerical inequality closing the reduced-form
  estimate `6 v = 1 - 4 t + s ≤ 2`.
* `productValue_le_of_bound`: supremum bridge from `productValueBound P c` to
  `productValue P ≤ c`.
* `lemma41_antisymmetric_productValue`: Lemma 4.1,
  `productValue (antisymProjector d) ≤ 1 / 3` for `4 ≤ d`.
* `lemma41_pointwise`: pointwise form `productValueBound (antisymProjector d) (1 / 3)`.

## References

* [Bostanci et al., 2026][BostanciEtAl2026], Section 4.1, Lemma 4.1, pp. 10--11.
-/

namespace Qatlib.Papers.QMA2Sep26.MainResults

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath

noncomputable section

private theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, f σ = ∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, σ)) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]

private theorem sum_two {d : ℕ} {M : Type*} [AddCommMonoid M]
    (f : (Fin 2 → Fin d) → M) :
    ∑ x, f x = ∑ i, ∑ j, f ![i, j] := by
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin d)).symm, Fintype.sum_prod_type]
  rfl

private theorem sum_tuple_succ {d n : ℕ} (f : (Fin (n + 1) → Fin d) → ℂ) :
    ∑ x, f x = ∑ i, ∑ x : Fin n → Fin d, f (Fin.cons i x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

private def sum4 {d : ℕ} (f : Fin d → Fin d → Fin d → Fin d → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, f i j k l

private theorem sum_four {d : ℕ} (f : (Fin 4 → Fin d) → ℂ) :
    ∑ x, f x = sum4 (fun i j k l => f ![i, j, k, l]) := by
  simp only [sum_tuple_succ, Fintype.sum_unique, sum4]
  rfl

private theorem sum4_swap12 {d : ℕ} (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    sum4 f = sum4 (fun i j k l => f j i k l) := by
  exact Finset.sum_comm

private theorem sum4_swap34 {d : ℕ} (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    sum4 f = sum4 (fun i j k l => f i j l k) := by
  unfold sum4
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

private theorem sum4_swap23 {d : ℕ} (f : Fin d → Fin d → Fin d → Fin d → ℂ) :
    sum4 f = sum4 (fun i j k l => f i k j l) := by
  unfold sum4
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

private theorem decompose_apply_two {n : ℕ} (p : Fin (n + 3))
    (σ : Equiv.Perm (Fin (n + 2))) :
    Equiv.Perm.decomposeFin.symm (p, σ) 2 = Equiv.swap 0 p (σ 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ σ p 1

private theorem decompose_apply_three {n : ℕ} (p : Fin (n + 4))
    (σ : Equiv.Perm (Fin (n + 3))) :
    Equiv.Perm.decomposeFin.symm (p, σ) 3 = Equiv.swap 0 p (σ 2).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ σ p 2

private def antiPart {d : ℕ} (α : QState (Fin 2 → Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => (α ![i, j] - α ![j, i]) / 2

private theorem antiPart_skew {d : ℕ} (α : QState (Fin 2 → Fin d)) (i j : Fin d) :
    antiPart α i j = -antiPart α j i := by
  unfold antiPart
  ring

private def wedge {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (i j k l : Fin d) : ℂ :=
  A i j * B k l - A i k * B j l + A i l * B j k +
    A j k * B i l - A j l * B i k + A k l * B i j

private theorem antisym_action {d : ℕ} (α β : QState (Fin 2 → Fin d))
    (x : Fin 4 → Fin d) :
    (antisymProjector d *ᵥ tensorPair α β) x =
      (1 / 6 : ℂ) * wedge (antiPart α) (antiPart β) (x 0) (x 1) (x 2) (x 3) := by
  classical
  have ht (y : Fin 4 → Fin d) :
      tensorPair α β y = α ![y 0, y 1] * β ![y 2, y 3] := by
    change α (fun i => y (leftReg i)) * β (fun i => y (rightReg i)) = _
    congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hp (σ : Equiv.Perm (Fin 4)) :
      (permMatrix (d := d) σ *ᵥ tensorPair α β) x =
        α ![x (σ 0), x (σ 1)] * β ![x (σ 2), x (σ 3)] := by
    change (∑ y, (if y = (fun k => x (σ k)) then (1 : ℂ) else 0) *
      tensorPair α β y) = _
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact ht (fun k => x (σ k))
  simp only [antisymProjector, Matrix.smul_mulVec, Matrix.sum_mulVec, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, hp]
  simp only [sum_perm_succ, Fin.sum_univ_succ,
    Fintype.sum_unique, permSignC, Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_one,
    decompose_apply_two, decompose_apply_three]
  norm_num [Equiv.swap_apply_def, wedge, antiPart]
  ring

private theorem antiPart_norm_le {d : ℕ} (α : QState (Fin 2 → Fin d)) :
    (∑ i, ∑ j, ‖antiPart α i j‖ ^ 2) ≤ ∑ x, ‖α x‖ ^ 2 := by
  have hp (z w : ℂ) : ‖(z - w) / 2‖ ^ 2 ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im]
    nlinarith [sq_nonneg (z.re + w.re), sq_nonneg (z.im + w.im)]
  rw [sum_two]
  calc
    _ ≤ ∑ i, ∑ j, (‖α ![i, j]‖ ^ 2 + ‖α ![j, i]‖ ^ 2) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp _ _
    _ = ∑ i, ∑ j, ‖α ![i, j]‖ ^ 2 := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => ‖α ![j, i]‖ ^ 2)]
      ring

private theorem frobenius_cauchy {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    ‖∑ i, ∑ j, star (A i j) * B i j‖ ^ 2 ≤
      (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  have h := norm_sum_le Finset.univ (fun p : Fin d × Fin d => star (A p.1 p.2) * B p.1 p.2)
  simp only [norm_mul, norm_star] at h
  have hn : 0 ≤ ∑ p : Fin d × Fin d, ‖A p.1 p.2‖ * ‖B p.1 p.2‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg _) hn).2 h
  simpa only [Fintype.sum_prod_type] using
    hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : Fin d × Fin d => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖))

private theorem wedge_skew12 {d : ℕ} (α β : QState (Fin 2 → Fin d))
    (i j k l : Fin d) :
    wedge (antiPart α) (antiPart β) j i k l =
      -wedge (antiPart α) (antiPart β) i j k l := by
  unfold wedge
  rw [antiPart_skew α j i, antiPart_skew β j i]
  ring

private theorem wedge_skew34 {d : ℕ} (α β : QState (Fin 2 → Fin d))
    (i j k l : Fin d) :
    wedge (antiPart α) (antiPart β) i j l k =
      -wedge (antiPart α) (antiPart β) i j k l := by
  unfold wedge
  rw [antiPart_skew β l k, antiPart_skew α l k]
  ring

private theorem pair_anti {d : ℕ} (α : QState (Fin 2 → Fin d))
    (F : Matrix (Fin d) (Fin d) ℂ) (hF : ∀ i j, F j i = -F i j) :
    (∑ i, ∑ j, star (α ![i, j]) * F i j) =
      ∑ i, ∑ j, star (antiPart α i j) * F i j := by
  have hs : (∑ i, ∑ j, star (α ![j, i]) * F i j) =
      -(∑ i, ∑ j, star (α ![i, j]) * F i j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hF i j, mul_neg]
  simp only [antiPart, star_div₀, star_sub, star_ofNat, div_mul_eq_mul_div,
    sub_mul, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hs]
  ring

private theorem wedge_project_bra {d : ℕ} (α β : QState (Fin 2 → Fin d)) :
    sum4 (fun i j k l => star (α ![i, j] * β ![k, l]) *
      wedge (antiPart α) (antiPart β) i j k l) =
    sum4 (fun i j k l => star (antiPart α i j * antiPart β k l) *
      wedge (antiPart α) (antiPart β) i j k l) := by
  unfold sum4
  simp only [star_mul']
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [pair_anti α _ (by
    intro i j
    simp only [wedge_skew12 α β i j, mul_neg, Finset.sum_neg_distrib])]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact pair_anti β _ (fun k l => wedge_skew34 α β i j k l)

private theorem sum4_congr {d : ℕ} {f g : Fin d → Fin d → Fin d → Fin d → ℂ}
    (h : ∀ i j k l, f i j k l = g i j k l) : sum4 f = sum4 g := by
  unfold sum4
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.sum_congr rfl fun l _ => h i j k l

private def crossMass {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖∑ k, A i k * star (B j k)‖ ^ 2

private theorem star_norm (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  simpa only [RCLike.star_def, Complex.ofReal_pow] using Complex.conj_mul' z

private theorem cross_identity {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (β : QState (Fin 2 → Fin d)) :
    sum4 (fun i j k l => star (A i j * antiPart β k l) *
      (A i k * antiPart β j l)) = (crossMass A (antiPart β) : ℂ) := by
  rw [sum4_swap34, sum4_swap23]
  calc
    _ = sum4 (fun i j k l => (star (A i k) * antiPart β j k) *
        (A i l * star (antiPart β j l))) := by
      apply sum4_congr
      intro i j k l
      rw [antiPart_skew β l j, antiPart_skew β k j]
      simp only [star_mul', star_neg]
      ring
    _ = (crossMass A (antiPart β) : ℂ) := by
      simp only [sum4, crossMass, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul_sum]
      have he : (∑ k, star (A i k) * antiPart β j k) =
          star (∑ k, A i k * star (antiPart β j k)) := by
        simp only [star_sum, star_mul', star_star]
      rw [he]
      exact star_norm _

private theorem direct_identity {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    sum4 (fun i j k l => star (A i j * B k l) * (A i j * B k l)) =
      (((∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ k, ∑ l, ‖B k l‖ ^ 2) : ℝ) : ℂ) := by
  simp only [sum4, star_norm, norm_mul, mul_pow, Complex.ofReal_mul,
    Complex.ofReal_sum]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

private theorem exchange_identity {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    sum4 (fun i j k l => star (A i j * B k l) * (A k l * B i j)) =
      ((‖∑ i, ∑ j, star (A i j) * B i j‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = (∑ i, ∑ j, star (A i j) * B i j) *
        (∑ k, ∑ l, star (B k l) * A k l) := by
      simp only [sum4, Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply sum4_congr
      intro i j k l
      simp only [star_mul']
      ring
    _ = (∑ i, ∑ j, star (A i j) * B i j) *
        star (∑ i, ∑ j, star (A i j) * B i j) := by
      congr 1
      simp only [star_sum, star_mul', star_star]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [mul_comm]; exact star_norm _

private theorem wedge_identity {d : ℕ} (α β : QState (Fin 2 → Fin d)) :
    sum4 (fun i j k l => star (antiPart α i j * antiPart β k l) *
      wedge (antiPart α) (antiPart β) i j k l) =
      (((∑ i, ∑ j, ‖antiPart α i j‖ ^ 2) * (∑ k, ∑ l, ‖antiPart β k l‖ ^ 2) +
        ‖∑ i, ∑ j, star (antiPart α i j) * antiPart β i j‖ ^ 2 -
        4 * crossMass (antiPart α) (antiPart β) : ℝ) : ℂ) := by
  let A := antiPart α
  let B := antiPart β
  let C := sum4 (fun i j k l => star (A i j * B k l) * (A i k * B j l))
  have hc : C = (crossMass A B : ℂ) := cross_identity A β
  have h₂ : sum4 (fun i j k l => star (A i j * B k l) * (A i l * B j k)) = -C := by
    rw [sum4_swap34]
    calc
      _ = sum4 (fun i j k l => -(star (A i j * B k l) * (A i k * B j l))) := by
        apply sum4_congr
        intro i j k l
        change star (A i j * antiPart β l k) * (A i k * B j l) = _
        rw [antiPart_skew β l k]
        simp only [mul_neg, star_neg, neg_mul]
        rfl
      _ = -C := by simp only [sum4, C, Finset.sum_neg_distrib]
  have h₃ : sum4 (fun i j k l => star (A i j * B k l) * (A j k * B i l)) = -C := by
    rw [sum4_swap12]
    calc
      _ = sum4 (fun i j k l => -(star (A i j * B k l) * (A i k * B j l))) := by
        apply sum4_congr
        intro i j k l
        change star (antiPart α j i * B k l) * (A i k * B j l) = _
        rw [antiPart_skew α j i]
        simp only [neg_mul, star_neg]
        rfl
      _ = -C := by simp only [sum4, C, Finset.sum_neg_distrib]
  have h₄ : sum4 (fun i j k l => star (A i j * B k l) * (A j l * B i k)) = C := by
    rw [sum4_swap12, sum4_swap34]
    apply sum4_congr
    intro i j k l
    change star (antiPart α j i * antiPart β l k) * (A i k * B j l) = _
    rw [antiPart_skew α j i, antiPart_skew β l k, neg_mul_neg]
  have he := exchange_identity A B
  have hd := direct_identity A B
  change sum4 (fun i j k l => star (A i j * B k l) * wedge A B i j k l) = _
  simp only [wedge, mul_add, mul_sub, sum4, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at ⊢
  change _ - C + _ + _ - _ + _ = _
  simp only [sum4] at h₂ h₃ h₄ hd he
  rw [h₂, h₃, h₄, hd, he, hc]
  push_cast
  ring

/-- Closing numerical inequality of Lemma 4.1: if `6 * v = 1 - 4 * t + s` with
`0 ≤ t` and `s ≤ 1`, then `v ≤ 1 / 3`. -/
theorem reducedForm_numeric_bound {v t s : ℝ}
    (ht : 0 ≤ t) (hs : s ≤ 1) (hid : 6 * v = 1 - 4 * t + s) : v ≤ 1 / 3 := by
  linarith

/-- If every normalized product state has quadratic form at most `c`, then the
product value supremum is at most `c`. -/
theorem productValue_le_of_bound {d : ℕ} {P : Matrix (Fin 4 → Fin d) (Fin 4 → Fin d) ℂ}
    {c : ℝ} (hb : productValueBound P c)
    (hne : ∃ α β : QState (Fin 2 → Fin d), Normalized α ∧ Normalized β) :
    productValue P ≤ c := by
  refine csSup_le ?_ ?_
  · obtain ⟨α, β, hα, hβ⟩ := hne
    exact ⟨_, realQuadForm_mem_productValue_range hα hβ⟩
  · rintro x ⟨α, β, hα, hβ, rfl⟩
    exact hb α β hα hβ

/-- Lemma 4.1, pointwise form: every normalized product state has quadratic form
at most `1 / 3` against `antisymProjector d` when `4 ≤ d`. -/
theorem lemma41_pointwise (d : ℕ) (hd : 4 ≤ d) :
    productValueBound (d := d) (antisymProjector d) (1 / 3) := by
  refine (And.left ⟨?_, hd⟩)
  intro α β hα hβ
  have ht (x : Fin 4 → Fin d) :
      tensorPair α β x = α ![x 0, x 1] * β ![x 2, x 3] := by
    change α (fun i => x (leftReg i)) * β (fun i => x (rightReg i)) = _
    congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl
  have hquad : quadForm (antisymProjector d) (tensorPair α β) =
      (1 / 6 : ℂ) *
        (((∑ i, ∑ j, ‖antiPart α i j‖ ^ 2) * (∑ k, ∑ l, ‖antiPart β k l‖ ^ 2) +
          ‖∑ i, ∑ j, star (antiPart α i j) * antiPart β i j‖ ^ 2 -
          4 * crossMass (antiPart α) (antiPart β) : ℝ) : ℂ) := by
    calc
      _ = ∑ x, star (tensorPair α β x) * ((1 / 6 : ℂ) *
          wedge (antiPart α) (antiPart β) (x 0) (x 1) (x 2) (x 3)) := by
        simp only [quadForm, dotProduct, Pi.star_apply, antisym_action]
      _ = (1 / 6 : ℂ) * sum4 (fun i j k l => star (α ![i, j] * β ![k, l]) *
          wedge (antiPart α) (antiPart β) i j k l) := by
        rw [sum_four]
        simp only [sum4, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        rw [ht]
        change star (α ![i, j] * β ![k, l]) *
          ((1 / 6 : ℂ) * wedge (antiPart α) (antiPart β) i j k l) = _
        ring
      _ = _ := by rw [wedge_project_bra, wedge_identity]
  have hid : 6 * realQuadForm (antisymProjector d) (tensorPair α β) =
      (∑ i, ∑ j, ‖antiPart α i j‖ ^ 2) * (∑ k, ∑ l, ‖antiPart β k l‖ ^ 2) +
        ‖∑ i, ∑ j, star (antiPart α i j) * antiPart β i j‖ ^ 2 -
        4 * crossMass (antiPart α) (antiPart β) := by
    unfold realQuadForm
    rw [hquad, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    norm_num [Complex.div_re]
    ring
  have ha := antiPart_norm_le α
  have hb := antiPart_norm_le β
  rw [hα] at ha
  rw [hβ] at hb
  have hb₀ : 0 ≤ ∑ i, ∑ j, ‖antiPart β i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hab : (∑ i, ∑ j, ‖antiPart α i j‖ ^ 2) *
      (∑ k, ∑ l, ‖antiPart β k l‖ ^ 2) ≤ 1 := by
    calc
      _ ≤ 1 * (∑ k, ∑ l, ‖antiPart β k l‖ ^ 2) :=
        mul_le_mul_of_nonneg_right ha hb₀
      _ ≤ 1 := by simpa only [one_mul] using hb
  have hs := (frobenius_cauchy (antiPart α) (antiPart β)).trans hab
  have hc : 0 ≤ crossMass (antiPart α) (antiPart β) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

/-- Lemma 4.1: for every `d ≥ 4`, the product value of the four-copy
antisymmetric projector across `(12 | 34)` is at most `1 / 3`. -/
theorem lemma41_antisymmetric_productValue (d : ℕ) (hd : 4 ≤ d) :
    productValue (d := d) (antisymProjector d) ≤ 1 / 3 := by
  classical
  apply productValue_le_of_bound (lemma41_pointwise d hd)
  let x₀ : Fin 2 → Fin d := fun _ => ⟨0, by omega⟩
  exact ⟨Ket x₀, Ket x₀, normalized_ket x₀, normalized_ket x₀⟩

end

end Qatlib.Papers.QMA2Sep26.MainResults
