/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Matrix.Order
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization

/-!
# Filtered Gram factorization certificates

This module defines finite witness certificates for filtered gamma-two factorizations and proves
their budget laws. It also relates real overlaps of normalized state families to Gram-difference
certificates and converts such certificates to approximate unitary alignment after finite
padding, following [LeeEtAl2011].

## Main statements

* `gramFilteredCert`: filtered factorization with bounded squared witness masses.
* `gramFilteredCert_hadamard_le`: removing an absorbed Schur factor multiplies certificate
  budgets.
* `gram_unitary_overlap_of_filteredCert`: an unfiltered Gram-difference certificate gives a
  common padded unitary with a real-overlap bound.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GramRealization

namespace Qatlib.Concepts.GramQueryCore.FilteredCert

open Matrix

set_option autoImplicit false

section Definitions

variable {X H : Type}

/-- The all-ones complex matrix, used as the single filter for unfiltered Gram factorizations. -/
def gramFilterAllOnes : Matrix X X ℂ := fun _ _ => 1

/-- The Boolean input-difference filter, equal to zero when inputs agree at coordinate `j` and
one otherwise. See [Lee et al., Definition 3.2][LeeEtAl2011]. -/
def gramFilterDelta {n : ℕ} (input : X → Fin n → Bool) : Fin n → Matrix X X ℂ :=
  fun j x y => if input x j = input y j then (0 : ℂ) else 1

/-- The Gram matrix of a finite-dimensional state family, with entry `(x,y)` equal to the inner
product of `ρ x` and `ρ y`. -/
noncomputable def gramStateMatrix {H : Type} [Fintype H] {X : Type}
    (ρ : X → QState H) : Matrix X X ℂ :=
  fun x y => Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y)

/-- The existence of finite-dimensional left and right witnesses whose filtered inner products
reconstruct `A` and whose squared masses at each input are at most `W`. This is the budgeted
factorization formulation associated with [Lee et al., Definition 3.1][LeeEtAl2011]. -/
def gramFilteredCert {n : ℕ} (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (W : ℝ) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (u v : Fin n → X → Q → ℂ),
    (∀ x, ∑ j, ∑ q, Complex.normSq (u j x q) ≤ W) ∧
      (∀ y, ∑ j, ∑ q, Complex.normSq (v j y q) ≤ W) ∧
      ∀ x y, A x y = ∑ j, Z j x y * (star (u j x) ⬝ᵥ v j y)

end Definitions

/-- A filtered factorization certificate remains valid when its budget is increased. -/
theorem gramFilteredCert_mono {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W W' : ℝ}
    (h : gramFilteredCert A Z W) (hWW' : W ≤ W') : gramFilteredCert A Z W' := by
  rcases h with ⟨Q, hQ, u, v, hu, hv, huv⟩
  exact ⟨Q, hQ, u, v, fun x => (hu x).trans hWW', fun y => (hv y).trans hWW', huv⟩

/-- The zero matrix has a filtered factorization certificate at every nonnegative budget for any
filter family. -/
theorem gramFilteredCert_zero {X : Type} {n : ℕ} (Z : Fin n → Matrix X X ℂ)
    {W : ℝ} (hW : 0 ≤ W) : gramFilteredCert 0 Z W := by
  refine ⟨Fin 0, inferInstance, fun _ _ _ => 0, fun _ _ _ => 0, ?_, ?_, ?_⟩
  · simpa using! fun _ : X => hW
  · simpa using! fun _ : X => hW
  · intro x y
    simp [dotProduct]

/-- Certificates for two matrices with the same filters combine into a certificate for their sum
with the sum of the budgets. See [Lee et al., Lemma A.2][LeeEtAl2011]. -/
theorem gramFilteredCert_add {X : Type} {n : ℕ} {A B : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W₁ W₂ : ℝ}
    (hA : gramFilteredCert A Z W₁) (hB : gramFilteredCert B Z W₂) :
    gramFilteredCert (A + B) Z (W₁ + W₂) := by
  classical
  rcases hA with ⟨Q, hQ, u, v, hu, hv, huv⟩
  rcases hB with ⟨Q', hQ', u', v', hu', hv', huv'⟩
  refine ⟨Q ⊕ Q', inferInstance,
    fun j x => Sum.elim (u j x) (u' j x),
    fun j y => Sum.elim (v j y) (v' j y), ?_, ?_, ?_⟩
  · intro x
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
      using! add_le_add (hu x) (hu' x)
  · intro y
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
      using! add_le_add (hv y) (hv' y)
  · intro x y
    simp only [Matrix.add_apply, huv, huv', dotProduct, Pi.star_apply,
      Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_add,
      Finset.sum_add_distrib]

/-- Negating the target matrix preserves the filtered certificate budget. -/
theorem gramFilteredCert_neg {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W : ℝ} (h : gramFilteredCert A Z W) :
    gramFilteredCert (-A) Z W := by
  rcases h with ⟨Q, hQ, u, v, hu, hv, huv⟩
  refine ⟨Q, hQ, u, fun j y q => -v j y q, hu, ?_, ?_⟩
  · simpa only [Complex.normSq_neg] using! hv
  · intro x y
    simp only [Matrix.neg_apply, huv, dotProduct, mul_neg, Finset.sum_neg_distrib]

/-- Scaling a target matrix by a nonnegative real `c` scales a filtered certificate budget by
`c`. -/
private theorem gramFilteredCert_smul_nonneg {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W : ℝ} (c : ℝ) (hc : 0 ≤ c)
    (h : gramFilteredCert A Z W) : gramFilteredCert (c • A) Z (c * W) := by
  rcases h with ⟨Q, hQ, u, v, hu, hv, huv⟩
  let s : ℂ := (Real.sqrt c : ℂ)
  have hs : Complex.normSq s = c := by
    simp only [s, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt hc
  have hss : star s * s = (c : ℂ) := by
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
    exact congrArg Complex.ofReal hs
  refine ⟨Q, hQ, fun j x q => s * u j x q, fun j y q => s * v j y q, ?_, ?_, ?_⟩
  · intro x
    simpa only [Complex.normSq_mul, hs, ← Finset.mul_sum]
      using! mul_le_mul_of_nonneg_left (hu x) hc
  · intro y
    simpa only [Complex.normSq_mul, hs, ← Finset.mul_sum]
      using! mul_le_mul_of_nonneg_left (hv y) hc
  · intro x y
    change (c : ℂ) * A x y = _
    rw [huv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dotProduct, Pi.star_apply, star_mul]
    rw [show (∑ q, star (u j x q) * star s * (s * v j y q)) =
        (star s * s) * ∑ q, star (u j x q) * v j y q by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring, hss]
    ring

/-- Scaling a target matrix by a real `c` scales the filtered certificate budget by `|c|`. See
[Lee et al., Lemma A.2][LeeEtAl2011]. -/
theorem gramFilteredCert_smul {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W : ℝ} (c : ℝ)
    (h : gramFilteredCert A Z W) : gramFilteredCert (c • A) Z (|c| * W) := by
  by_cases hc : 0 ≤ c
  · simpa only [abs_of_nonneg hc] using! gramFilteredCert_smul_nonneg c hc h
  · have hc' : 0 ≤ -c := by linarith
    have hs := gramFilteredCert_neg (gramFilteredCert_smul_nonneg (-c) hc' h)
    simpa only [abs_of_neg (lt_of_not_ge hc), neg_smul, neg_neg] using! hs

/-- A certificate for `A` with filters `Z j * B` and an unfiltered certificate for `B` give a
certificate for `A` with filters `Z` and the product budget. See [Lee et al., Equation
(3.2)][LeeEtAl2011]. -/
theorem gramFilteredCert_hadamard_le {X : Type} {n : ℕ} {A B : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W W' : ℝ}
    (hA : gramFilteredCert A (fun j x y => Z j x y * B x y) W)
    (hB : gramFilteredCert B (fun _ : Fin 1 => gramFilterAllOnes) W') :
    gramFilteredCert A Z (W * W') := by
  classical
  rcases hA with ⟨Q, hQ, u, v, hu, hv, huv⟩
  rcases hB with ⟨P, hP, p, q, hp, hq, hpq⟩
  simp only [Fin.sum_univ_one, gramFilterAllOnes, one_mul] at hp hq hpq
  refine ⟨Q × P, inferInstance,
    fun j x st => u j x st.1 * p 0 x st.2,
    fun j y st => v j y st.1 * q 0 y st.2, ?_, ?_, ?_⟩
  · intro x
    have hux : 0 ≤ ∑ j, ∑ s, Complex.normSq (u j x s) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => Complex.normSq_nonneg _
    have hpx : 0 ≤ ∑ t, Complex.normSq (p 0 x t) :=
      Finset.sum_nonneg fun t _ => Complex.normSq_nonneg _
    have hWx : 0 ≤ W := hux.trans (hu x)
    simpa only [Fintype.sum_prod_type, Complex.normSq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul] using! mul_le_mul (hu x) (hp x) hpx hWx
  · intro y
    have hvy : 0 ≤ ∑ j, ∑ s, Complex.normSq (v j y s) :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => Complex.normSq_nonneg _
    have hqy : 0 ≤ ∑ t, Complex.normSq (q 0 y t) :=
      Finset.sum_nonneg fun t _ => Complex.normSq_nonneg _
    have hWy : 0 ≤ W := hvy.trans (hv y)
    simpa only [Fintype.sum_prod_type, Complex.normSq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul] using! mul_le_mul (hv y) (hq y) hqy hWy
  · intro x y
    rw [huv]
    apply Finset.sum_congr rfl
    intro j _
    (try dsimp only)
    rw [hpq]
    simp only [dotProduct, Pi.star_apply, star_mul, Fintype.sum_prod_type]
    have ht : (∑ s, star (u j x s) * v j y s) *
        (∑ t, star (p 0 x t) * q 0 y t) =
        ∑ s, ∑ t, star (p 0 x t) * star (u j x s) * (v j y s * q 0 y t) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [← ht]
    ring

/-- The sum of squared complex magnitudes of a finite state vector. -/
private noncomputable def fgMass {H : Type} [Fintype H] (ψ : QState H) : ℝ :=
  ∑ i, Complex.normSq (ψ i)

/-- The squared mass of a finite state vector is nonnegative. -/
private theorem fgMass_nonneg {H : Type} [Fintype H] (ψ : QState H) : 0 ≤ fgMass ψ :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (ψ i)

/-- A normalized finite state vector has squared mass one. -/
private theorem fgMass_normalized {H : Type} [Fintype H] {ψ : QState H}
    (hψ : Normalized ψ) : fgMass ψ = 1 := by
  simpa only [fgMass, Complex.normSq_eq_norm_sq] using! hψ

/-- The squared mass of a real linear combination is the sum of the squared-coefficient masses
and twice the coefficient product times the real overlap. -/
private theorem fgMass_combination {H : Type} [Fintype H] (ψ φ : QState H) (a b : ℝ) :
    fgMass (fun i => (a : ℂ) * ψ i + (b : ℂ) * φ i) =
      a ^ 2 * fgMass ψ + b ^ 2 * fgMass φ + 2 * a * b * (Qatlib.Foundations.PureStateMath.Inner ψ φ).re := by
  classical
  have he (z w : ℂ) : Complex.normSq ((a : ℂ) * z + (b : ℂ) * w) =
      a ^ 2 * Complex.normSq z + b ^ 2 * Complex.normSq w +
        2 * a * b * (star z * w).re := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      RCLike.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp only [fgMass, he, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show (Qatlib.Foundations.PureStateMath.Inner ψ φ).re = ∑ i, (star (ψ i) * φ i).re by
    simp [inner_apply, RCLike.star_def]]

/-- Expands the inner product of two real linear combinations into the four pairwise inner
products with their coefficient products. -/
private theorem fg_inner_combination {H : Type} [Fintype H]
    (ψ φ ξ η : QState H) (a b c d : ℝ) :
    Qatlib.Foundations.PureStateMath.Inner (fun i => (a : ℂ) * ψ i + (b : ℂ) * φ i)
      (fun i => (c : ℂ) * ξ i + (d : ℂ) * η i) =
      ((a * c : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner ψ ξ + ((a * d : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner ψ η +
      ((b * c : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner φ ξ + ((b * d : ℝ) : ℂ) * Qatlib.Foundations.PureStateMath.Inner φ η := by
  classical
  simp only [inner_apply, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [show (∑ i, ((a : ℂ) * (starRingEnd ℂ) (ψ i) +
      (b : ℂ) * (starRingEnd ℂ) (φ i)) * ((c : ℂ) * ξ i + (d : ℂ) * η i)) =
      ∑ i, (((a : ℂ) * c) * ((starRingEnd ℂ) (ψ i) * ξ i) +
        ((a : ℂ) * d) * ((starRingEnd ℂ) (ψ i) * η i) +
        ((b : ℂ) * c) * ((starRingEnd ℂ) (φ i) * ξ i) +
        ((b : ℂ) * d) * ((starRingEnd ℂ) (φ i) * η i)) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- A finite state vector with zero squared mass is the zero vector. -/
private theorem fgMass_eq_zero {H : Type} [Fintype H] {ψ : QState H}
    (hψ : fgMass ψ = 0) : ψ = 0 := by
  classical
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => Complex.normSq_nonneg (ψ i))).mp hψ
  funext i
  exact Complex.normSq_eq_zero.mp (hz i (Finset.mem_univ i))

set_option maxHeartbeats 1000000 in

/-- For normalized state families with real overlaps at least `sqrt (1-ε)` and `0 ≤ ε ≤ 1`,
their Gram difference has a single-all-ones-filter certificate with budget `2*sqrt ε`. See
[Lee et al., Lemma 4.8][LeeEtAl2011]. -/
theorem gramFilteredCert_of_realPart_overlap {H X : Type} [Fintype H] [Fintype X]
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ρ σ : X → QState H)
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (hov : ∀ x, Real.sqrt (1 - ε) ≤ (Qatlib.Foundations.PureStateMath.Inner (ρ x) (σ x)).re) :
    gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) (2 * Real.sqrt ε) := by
  classical
  by_cases hz : ε = 0
  · have heq : ρ = σ := by
      funext x
      have hm := fgMass_combination (ρ x) (σ x) 1 (-1)
      have hn := fgMass_nonneg (fun i => (1 : ℂ) * ρ x i + (-1 : ℂ) * σ x i)
      have ho := hov x
      simp only [hz, sub_zero, Real.sqrt_one] at ho
      rw [fgMass_normalized (hρ x), fgMass_normalized (hσ x)] at hm
      norm_num only [Complex.ofReal_one, Complex.ofReal_neg, one_pow, neg_one_sq,
        one_mul, mul_one] at hm
      have hm0 : fgMass (fun i => (1 : ℂ) * ρ x i + (-1 : ℂ) * σ x i) = 0 := by
        simp only [one_mul, neg_one_mul] at hm hn ⊢
        nlinarith
      have hv := fgMass_eq_zero hm0
      funext i
      have hi := congrFun hv i
      simp only [one_mul, neg_mul, Pi.zero_apply] at hi
      linear_combination hi
    rw [heq, sub_self]
    exact gramFilteredCert_zero _ (by positivity)
  · let r := Real.sqrt (1 - ε)
    let d := Real.sqrt ε
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hr2 : r ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
    have hd : 0 < d := Real.sqrt_pos_of_pos (lt_of_le_of_ne hε (Ne.symm hz))
    have hd2 : d ^ 2 = ε := Real.sq_sqrt hε
    have hden : 0 < 1 + r := by linarith
    let a := Real.sqrt (d / (2 * (1 + r)))
    let b := Real.sqrt ((1 + r) / (2 * d))
    have ha : 0 ≤ a := Real.sqrt_nonneg _
    have hb : 0 ≤ b := Real.sqrt_nonneg _
    have ha2 : a ^ 2 = d / (2 * (1 + r)) := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = (1 + r) / (2 * d) := Real.sq_sqrt (by positivity)
    have hab : 2 * a * b = 1 := by
      have hp : a ^ 2 * b ^ 2 = 1 / 4 := by
        rw [ha2, hb2]
        field_simp
        norm_num
      nlinarith [mul_nonneg ha hb]
    have hcoef : a ^ 2 ≤ b ^ 2 := by
      rw [ha2, hb2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hbound (o : ℝ) (ho : r ≤ o) :
        a ^ 2 * (2 + 2 * o) + b ^ 2 * (2 - 2 * o) ≤ 2 * d := by
      have he : a ^ 2 * (2 + 2 * r) + b ^ 2 * (2 - 2 * r) = 2 * d := by
        rw [ha2, hb2]
        field_simp
        nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) (sub_nonneg.mpr ho)]
    let p (x : X) (i : H) := (a : ℂ) * (ρ x i + σ x i)
    let q (x : X) (i : H) := (b : ℂ) * (ρ x i - σ x i)
    have hmass (x : X) : fgMass (p x) + fgMass (q x) ≤ 2 * d := by
      have hp : p x = fun i => (a : ℂ) * ρ x i + (a : ℂ) * σ x i := by
        funext i; dsimp [p]; ring
      have hq : q x = fun i => (b : ℂ) * ρ x i + ((-b : ℝ) : ℂ) * σ x i := by
        funext i; dsimp [q]; push_cast; ring
      rw [hp, hq, fgMass_combination, fgMass_combination,
        fgMass_normalized (hρ x), fgMass_normalized (hσ x)]
      have ho : r ≤ (Qatlib.Foundations.PureStateMath.Inner (ρ x) (σ x)).re := hov x
      nlinarith [hbound _ ho]
    refine ⟨H ⊕ H, inferInstance, fun _ x => Sum.elim (p x) (q x),
      fun _ y => Sum.elim (q y) (p y), ?_, ?_, ?_⟩
    · intro x
      simpa only [Fin.sum_univ_one, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr] using! hmass x
    · intro y
      simpa only [Fin.sum_univ_one, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, add_comm] using! hmass y
    · intro x y
      simp only [Fin.sum_univ_one, gramFilterAllOnes, one_mul, dotProduct,
        Pi.star_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      have habc : (2 : ℂ) * (a : ℂ) * (b : ℂ) = 1 := by exact_mod_cast hab
      change Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) =
        Qatlib.Foundations.PureStateMath.Inner (p x) (q y) + Qatlib.Foundations.PureStateMath.Inner (q x) (p y)
      have hp (z : X) : p z = fun i => (a : ℂ) * ρ z i + (a : ℂ) * σ z i := by
        funext i; dsimp [p]; ring
      have hq (z : X) : q z = fun i => (b : ℂ) * ρ z i + ((-b : ℝ) : ℂ) * σ z i := by
        funext i; dsimp [q]; push_cast; ring
      rw [hp, hq, hq, hp, fg_inner_combination, fg_inner_combination]
      push_cast
      linear_combination -(Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y)) * habc

/-- The squared mass of a state vector equals the real part of its inner product with itself. -/
private theorem fgMass_inner_self {H : Type} [Fintype H] (ψ : QState H) :
    fgMass ψ = (Qatlib.Foundations.PureStateMath.Inner ψ ψ).re := by
  classical
  rw [inner_self, ← Complex.ofReal_sum, Complex.ofReal_re]
  simp only [fgMass, Complex.normSq_eq_norm_sq]

/-- Conjugating an inner product exchanges its two arguments. -/
private theorem fg_inner_conj {H : Type} [Fintype H] (ψ φ : QState H) :
    star (Qatlib.Foundations.PureStateMath.Inner ψ φ) = Qatlib.Foundations.PureStateMath.Inner φ ψ := by
  classical
  simp only [inner_apply, RCLike.star_def, map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The inner product of direct-sum state vectors equals the sum of the inner products of their
components. -/
private theorem fg_inner_sum {H K : Type} [Fintype H] [Fintype K]
    (a b : QState H) (p q : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (Sum.elim a p) (Sum.elim b q) = Qatlib.Foundations.PureStateMath.Inner a b + Qatlib.Foundations.PureStateMath.Inner p q := by
  classical
  simp only [inner_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- The real part of a finite-state inner product is at most the product of the square roots of
the squared masses. -/
private theorem fg_re_inner_le {H : Type} [Fintype H] (a b : QState H) :
    (Qatlib.Foundations.PureStateMath.Inner a b).re ≤ Real.sqrt (fgMass a) * Real.sqrt (fgMass b) := by
  classical
  apply (Complex.re_le_norm _).trans
  rw [← inner_euclidean_fromVec]
  simpa only [EuclideanSpace.norm_eq, toEuclidean_fromVec_apply,
    fgMass, Complex.normSq_eq_norm_sq] using!
    norm_inner_le_norm (toEuclidean_fromVec a) (toEuclidean_fromVec b)

set_option maxHeartbeats 1000000 in

/-- An all-ones-filter certificate of budget `ε ≥ 0` for the Gram difference of normalized
families yields a finite padding and a common unitary whose aligned real overlaps are at
least `1-sqrt (2*ε)`. See [Lee et al., Lemma 4.8][LeeEtAl2011]. -/
theorem gram_unitary_overlap_of_filteredCert {H X : Type}
    [Fintype H] [DecidableEq H] [Fintype X] [DecidableEq X]
    {ε : ℝ} (hε : 0 ≤ ε) (ρ σ : X → QState H)
    (hρ : ∀ x, Normalized (ρ x)) (hσ : ∀ x, Normalized (σ x))
    (hcert : gramFilteredCert (gramStateMatrix ρ - gramStateMatrix σ)
      (fun _ : Fin 1 => gramFilterAllOnes) ε) :
    ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (U : Matrix (H ⊕ K) (H ⊕ K) ℂ),
      U ∈ Matrix.unitaryGroup (H ⊕ K) ℂ ∧
      ∀ x, 1 - Real.sqrt (2 * ε) ≤ (Qatlib.Foundations.PureStateMath.Inner
        (ApplyGate U (Sum.elim (ρ x) (0 : K → ℂ)))
        (Sum.elim (σ x) (0 : K → ℂ))).re := by
  classical
  rcases hcert with ⟨K, hK, u, v, hu, hv, huv⟩
  simp only [Fin.sum_univ_one, gramFilterAllOnes, one_mul] at hu hv huv
  let α := u 0
  let β := v 0
  have hab (x y : X) : Qatlib.Foundations.PureStateMath.Inner (α x) (β y) = Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) :=
    (huv x y).symm
  have hba (x y : X) : Qatlib.Foundations.PureStateMath.Inner (β x) (α y) = Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) := by
    rw [← fg_inner_conj, hab]
    simp only [star_sub, fg_inner_conj]
  have hdiag (x : X) : Qatlib.Foundations.PureStateMath.Inner (α x) (β x) = 0 := by
    rw [hab, (normalized_iff_inner_self _).mp (hρ x),
      (normalized_iff_inner_self _).mp (hσ x), sub_self]
  let p (x : X) (k : K) := ((1 / 2 : ℝ) : ℂ) * α x k + ((-1 / 2 : ℝ) : ℂ) * β x k
  let q (x : X) (k : K) := ((1 / 2 : ℝ) : ℂ) * α x k + ((1 / 2 : ℝ) : ℂ) * β x k
  have hp (x : X) : fgMass (p x) ≤ ε / 2 := by
    have hm := fgMass_combination (α x) (β x) (1 / 2) (-1 / 2)
    rw [hdiag, Complex.zero_re] at hm
    have hux : fgMass (α x) ≤ ε := hu x
    have hvx : fgMass (β x) ≤ ε := hv x
    change fgMass (fun k => _) ≤ ε / 2
    nlinarith only [hm, hux, hvx]
  have hq (x : X) : fgMass (q x) ≤ ε / 2 := by
    have hm := fgMass_combination (α x) (β x) (1 / 2) (1 / 2)
    rw [hdiag, Complex.zero_re] at hm
    have hux : fgMass (α x) ≤ ε := hu x
    have hvx : fgMass (β x) ≤ ε := hv x
    change fgMass (fun k => _) ≤ ε / 2
    nlinarith only [hm, hux, hvx]
  have hgram (x y : X) : Qatlib.Foundations.PureStateMath.Inner (q x) (q y) - Qatlib.Foundations.PureStateMath.Inner (p x) (p y) =
      Qatlib.Foundations.PureStateMath.Inner (ρ x) (ρ y) - Qatlib.Foundations.PureStateMath.Inner (σ x) (σ y) := by
    dsimp only [p, q]
    rw [fg_inner_combination, fg_inner_combination, hab, hba]
    norm_num
    ring
  let V : Matrix (H ⊕ K) X ℂ := fun i x => Sum.elim (ρ x) (p x) i
  let W : Matrix (H ⊕ K) X ℂ := fun i x => Sum.elim (σ x) (q x) i
  have hVW : Vᴴ * V = Wᴴ * W := by
    ext x y
    change Qatlib.Foundations.PureStateMath.Inner (Sum.elim (ρ x) (p x)) (Sum.elim (ρ y) (p y)) =
      Qatlib.Foundations.PureStateMath.Inner (Sum.elim (σ x) (q x)) (Sum.elim (σ y) (q y))
    rw [fg_inner_sum, fg_inner_sum]
    linear_combination -(hgram x y)
  obtain ⟨U, hU, hUV⟩ := gram_equal_actual_unitary_transport (H ⊕ K) X V W hVW
  refine ⟨K, hK, inferInstance, U, hU, ?_⟩
  intro x
  let a : QState (H ⊕ K) := Sum.elim (ρ x) 0
  let b : QState (H ⊕ K) := Sum.elim (σ x) 0
  let e : QState (H ⊕ K) := Sum.elim 0 (p x)
  have hact : ApplyGate U (a + e) = Sum.elim (σ x) (q x) := by
    have he : a + e = fun i => V i x := by
      funext i
      cases i <;> simp [a, e, V]
    rw [he]
    funext i
    exact congrFun (congrFun hUV i) x
  have heqb : Qatlib.Foundations.PureStateMath.Inner (ApplyGate U a) b = 1 - Qatlib.Foundations.PureStateMath.Inner (ApplyGate U e) b := by
    have hs : ApplyGate U (a + e) = ApplyGate U a + ApplyGate U e :=
      Matrix.mulVec_add U a e
    have hi := congrArg (fun z => Qatlib.Foundations.PureStateMath.Inner z b) hact

    rw [hs] at hi
    have hadd : Qatlib.Foundations.PureStateMath.Inner (ApplyGate U a + ApplyGate U e) b =
        Qatlib.Foundations.PureStateMath.Inner (ApplyGate U a) b + Qatlib.Foundations.PureStateMath.Inner (ApplyGate U e) b := by
      simp [Qatlib.Foundations.PureStateMath.Inner, star_add, add_dotProduct]
    rw [hadd] at hi
    have hr : Qatlib.Foundations.PureStateMath.Inner (Sum.elim (σ x) (q x)) b = 1 := by
      rw [fg_inner_sum]
      simpa [Qatlib.Foundations.PureStateMath.Inner] using!
          (normalized_iff_inner_self _).mp (hσ x)
    rw [hr] at hi
    linear_combination hi
  have hem : fgMass (ApplyGate U e) = fgMass (p x) := by
    change (∑ i, Complex.normSq ((U *ᵥ e) i)) = _
    rw [sum_normSq_mulVec_of_mem_unitaryGroup hU]
    simp [e, Fintype.sum_sum_type, fgMass]
  have hbm : fgMass b = 1 := by
    simpa [b, Fintype.sum_sum_type, fgMass] using! fgMass_normalized (hσ x)
  have heinner := fg_re_inner_le (ApplyGate U e) b
  rw [hem, hbm, Real.sqrt_one, mul_one] at heinner
  have hsqrt : Real.sqrt (fgMass (p x)) ≤ Real.sqrt (2 * ε) :=
    Real.sqrt_le_sqrt (by linarith [hp x])
  change 1 - Real.sqrt (2 * ε) ≤ (Qatlib.Foundations.PureStateMath.Inner (ApplyGate U a) b).re
  rw [heqb, Complex.sub_re, Complex.one_re]
  linarith

end Qatlib.Concepts.GramQueryCore.FilteredCert
