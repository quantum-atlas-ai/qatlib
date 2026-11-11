/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6 — coefficients of the subtree state in the symmetric basis

Fixed source: arXiv:2505.07929v2, Lemma 6, Appendix VI, PDF pp. 42–43,
eqs. (B194)–(B195).

Expanding the `D`-th tensor power of the subtree state of eq. (B187) in the symmetric
(number-state) basis of Definition 13 gives, for every occupation vector
`(n_l)_{0 ≤ l ≤ p'}` with `∑_l n_l = D`, the coefficient (eq. (B194))

  `(∏_{l≥1} c_l^{n_l}) D^{-½∑_{l≥1} n_l} binom(D; (n_l))^{1/2}`,

where `c_l = -i ∑_j L_{l,j} γ_j a_j` (`l` a mode index, `j` a layer index).  For every
fixed (`D`-independent) occupation vector `(n_l)_{l≥1}` the coefficient of the number state
`|n_1, …, n_{p'}⟩_{Δ-1,D}` converges as `D → ∞` (eq. (B195)):

  `→ ∏_{l≥1} (1/√(n_l!)) c_l^{n_l}`.

This file states the convergence part (B195), at the level of the explicit scalar
coefficient sequence `symmetricCoefficient`; the number states themselves are not
modelled (they are not needed for the coefficient limit).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.SpinBosonQAOA26.MainResults.SymmetricBasisExpansion

/-- The amplitude `c_l = -i ∑_{1≤j≤p} L_{l,j} γ_j a_j` multiplying the number state in the
`l`-th mode (eqs. (B194), (B195)). -/
def modeAmplitude {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (γ : Fin p → ℝ)
    (a : Fin p → ℝ) (l : Fin p') : ℂ :=
  -Complex.I * ∑ j : Fin p, L l j * (γ j : ℂ) * (a j : ℂ)

/-- The occupation vector `(n_1, …, n_{p'}; n_0)` extended to `Fin (p'+1)` by putting
`n_0 = D - ∑_l n_l` in the last slot (eq. (B194)). -/
def occupationWithRest {p' : ℕ} (n : Fin p' → ℕ) (D : ℕ) : Fin (p' + 1) → ℕ :=
  fun i => if h : i.val < p' then n ⟨i.val, h⟩ else D - ∑ l, n l

/-- The coefficient of the number state `|n_1, …, n_{p'}⟩_{Δ-1,D}` in the symmetric-basis
expansion of eq. (B194):
`(∏_l c_l^{n_l}) D^{-½∑_l n_l} binom(D; (n_l))^{1/2}`. -/
def symmetricCoefficient {p' : ℕ} (c : Fin p' → ℂ) (n : Fin p' → ℕ) (D : ℕ) : ℂ :=
  (Real.sqrt
      (Nat.multinomial (Finset.univ : Finset (Fin (p' + 1))) (occupationWithRest n D) : ℝ) : ℂ)
    * ((((Real.sqrt (D : ℝ))⁻¹ : ℝ)) : ℂ) ^ (∑ l, n l)
    * ∏ l, c l ^ (n l)

/-- **Lemma 6**, eq. (B195) of arXiv:2505.07929v2 (PDF p. 43): for every fixed occupation
vector `(n_l)_{l≥1}`, the coefficient of the number state `|n_1, …, n_{p'}⟩_{Δ-1,D}` in
the symmetric-basis expansion of the subtree state converges as `D → ∞` to

  `∏_{l≥1} (1/√(n_l!)) c_l^{n_l}`.

The convergence is over the explicit coefficient sequence `symmetricCoefficient` with
`c_l = modeAmplitude L γ a l` (the paper's `c_l = -i ∑_j L_{l,j} γ_j a_j`); the multinomial
asymptotics `binom(D; n) D^{-N} → 1/∏ n_l!` at fixed `N = ∑_l n_l` is the content. -/
theorem lemma6_symmetric_basis_limit
    {p' p : ℕ} (L : Matrix (Fin p') (Fin p) ℂ) (γ : Fin p → ℝ) (a : Fin p → ℝ)
    (n : Fin p' → ℕ) :
    Filter.Tendsto (fun D : ℕ => symmetricCoefficient (modeAmplitude L γ a) n D)
      Filter.atTop
      (nhds (∏ l : Fin p',
        (((Real.sqrt ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
          (modeAmplitude L γ a l) ^ (n l))) := by
  classical
  -- The two halves of the occupation vector: the `Fin p'` modes and the rest slot.
  have hcastlt : ∀ (D : ℕ) (i : Fin p'),
      occupationWithRest n D (Fin.castAdd 1 i) = n i := by
    intro D i
    have hlt : (Fin.castAdd 1 i).val < p' := by simpa using i.isLt
    have hfin : (⟨(Fin.castAdd 1 i).val, hlt⟩ : Fin p') = i := Fin.ext (by simp)
    simp only [occupationWithRest, dif_pos hlt, hfin]
  have hnatadd : ∀ (D : ℕ) (i : Fin 1),
      occupationWithRest n D (Fin.natAdd p' i) = D - ∑ l, n l := by
    intro D i
    have hge : ¬ (Fin.natAdd p' i).val < p' := by
      simp only [Fin.val_natAdd]
      omega
    simp only [occupationWithRest, dif_neg hge]
  -- The occupation vector sums to `D` as soon as `D` is large enough.
  have hoccsum : ∀ D : ℕ, ∑ l, n l ≤ D →
      ∑ i : Fin (p'+1), occupationWithRest n D i = D := by
    intro D hD
    rw [Fin.sum_univ_add, Finset.sum_congr rfl (fun (i : Fin p') _ => hcastlt D i),
      Finset.sum_congr rfl (fun (i : Fin 1) _ => hnatadd D i)]
    have h1 : ∑ i : Fin 1, (D - ∑ l, n l) = D - ∑ l, n l := by simp
    rw [h1]
    exact Nat.add_sub_cancel' hD
  have hfact : ∀ D : ℕ, ∑ l, n l ≤ D →
      ∏ i : Fin (p'+1), Nat.factorial (occupationWithRest n D i)
        = (∏ l : Fin p', Nat.factorial (n l)) * Nat.factorial (D - ∑ l, n l) := by
    intro D hD
    rw [Fin.prod_univ_add, Finset.prod_congr rfl (fun (i : Fin p') _ => by rw [hcastlt D i]),
      Finset.prod_congr rfl (fun (i : Fin 1) _ => by rw [hnatadd D i])]
    have h1 : ∏ i : Fin 1, Nat.factorial (D - ∑ l, n l) = Nat.factorial (D - ∑ l, n l) := by
      simp
    rw [h1]
  -- The multinomial identity of eq. (B194), for `D ≥ ∑ n_l`.
  have hID : ∀ D : ℕ, ∑ l, n l ≤ D →
      (∏ l : Fin p', Nat.factorial (n l)) * Nat.factorial (D - ∑ l, n l)
        * Nat.multinomial (Finset.univ : Finset (Fin (p'+1))) (occupationWithRest n D)
        = Nat.factorial D := by
    intro D hD
    have h1 := Nat.multinomial_spec (Finset.univ : Finset (Fin (p'+1)))
      (occupationWithRest n D)
    rw [hoccsum D hD, hfact D hD] at h1
    exact h1
  -- The falling factorial fills the same gap.
  have hdf : ∀ D : ℕ, ∑ l, n l ≤ D →
      Nat.factorial (D - ∑ l, n l) * Nat.descFactorial D (∑ l, n l) = Nat.factorial D :=
    fun D hD => Nat.factorial_mul_descFactorial hD
  -- Multinomial asymptotics, part 1: `D↓N / D^N → 1` for fixed `N`, by induction on `N`.
  have hd : ∀ N : ℕ, Filter.Tendsto (fun D : ℕ =>
      ((Nat.descFactorial D N : ℕ) : ℝ) / ((D : ℕ) : ℝ) ^ N) Filter.atTop (nhds 1) := by
    intro N
    induction N with
    | zero =>
        have hz : (fun D : ℕ => ((Nat.descFactorial D 0 : ℕ) : ℝ) / ((D : ℕ) : ℝ) ^ 0)
            = fun _ : ℕ => 1 := by
          funext D
          simp [Nat.descFactorial_zero]
        rw [hz]
        exact tendsto_const_nhds
    | succ N ih =>
        have h1 : ∀ D : ℕ, ((Nat.descFactorial D (N + 1) : ℕ) : ℝ)
            = ((Nat.descFactorial D N : ℕ) : ℝ) * ((D - N : ℕ) : ℝ) := by
          intro D
          rw [Nat.descFactorial_succ]
          push_cast
          ring
        have h2 : Filter.Tendsto (fun D : ℕ => ((D - N : ℕ) : ℝ) / ((D : ℕ) : ℝ))
            Filter.atTop (nhds 1) := by
          have heq : (fun D : ℕ => ((D - N : ℕ) : ℝ) / ((D : ℕ) : ℝ))
              =ᶠ[Filter.atTop] fun D : ℕ => 1 - (N : ℝ) / ((D : ℕ) : ℝ) := by
            filter_upwards [Filter.eventually_ge_atTop (max N 1)] with D hD
            have hND : N ≤ D := by omega
            have hD0 : ((D : ℕ) : ℝ) ≠ 0 := by
              have h1D : (1 : ℕ) ≤ D := by omega
              have : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast h1D
              linarith
            rw [Nat.cast_sub hND]
            field_simp
          refine Filter.Tendsto.congr' heq.symm ?_
          have hinv : Filter.Tendsto (fun D : ℕ => ((D : ℕ) : ℝ)⁻¹) Filter.atTop (nhds 0) :=
            tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
          have hdiv : Filter.Tendsto (fun D : ℕ => (N : ℝ) / ((D : ℕ) : ℝ))
              Filter.atTop (nhds 0) := by
            simpa [div_eq_inv_mul, mul_comm] using hinv.mul_const (N : ℝ)
          simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdiv
        refine Filter.Tendsto.congr'
          (f₁ := fun D : ℕ => (((Nat.descFactorial D N : ℕ) : ℝ) / ((D : ℕ) : ℝ) ^ N)
            * (((D - N : ℕ) : ℝ) / ((D : ℕ) : ℝ))) ?_ ?_
        · filter_upwards [Filter.eventually_ge_atTop 1] with D hD1
          have hD0 : ((D : ℕ) : ℝ) ≠ 0 := by
            have : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast hD1
            linarith
          have hDn : ((D : ℕ) : ℝ) ^ N ≠ 0 := pow_ne_zero N hD0
          rw [h1 D, pow_succ]
          field_simp
        · simpa only [one_mul] using ih.mul h2
  -- Multinomial asymptotics, part 2: the multinomial ratio itself.
  have hcore : Filter.Tendsto (fun D : ℕ =>
      ((Nat.multinomial (Finset.univ : Finset (Fin (p'+1))) (occupationWithRest n D)) : ℝ)
        / ((D : ℕ) : ℝ) ^ (∑ l, n l)) Filter.atTop
      (nhds ((∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹)) := by
    have hQpos : (0 : ℝ) < ∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ) :=
      Finset.prod_pos fun l _ => by positivity
    have heq : (fun D : ℕ =>
          ((Nat.multinomial (Finset.univ : Finset (Fin (p'+1))) (occupationWithRest n D)) : ℝ)
            / ((D : ℕ) : ℝ) ^ (∑ l, n l))
        =ᶠ[Filter.atTop] fun D : ℕ =>
          (((Nat.descFactorial D (∑ l, n l) : ℕ) : ℝ)
            / ((D : ℕ) : ℝ) ^ (∑ l, n l))
            / (∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop (max (∑ l, n l) 1)] with D hD
      have hND : ∑ l, n l ≤ D := by omega
      have h1D : (1 : ℕ) ≤ D := by omega
      have hD0 : ((D : ℕ) : ℝ) ≠ 0 := by
        have : (1 : ℝ) ≤ ((D : ℕ) : ℝ) := by exact_mod_cast h1D
        linarith
      have hDn : ((D : ℕ) : ℝ) ^ (∑ l, n l) ≠ 0 := pow_ne_zero _ hD0
      have hFn : ((Nat.factorial (D - ∑ l, n l) : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hkey : (∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))
            * ((Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
                (occupationWithRest n D) : ℕ) : ℝ)
          = ((Nat.descFactorial D (∑ l, n l) : ℕ) : ℝ) := by
        have eNat := (hID D hND).trans (hdf D hND).symm
        have e1r : (((∏ l : Fin p', Nat.factorial (n l)) * Nat.factorial (D - ∑ l, n l)
              * Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
                (occupationWithRest n D) : ℕ) : ℝ)
            = ((Nat.factorial (D - ∑ l, n l)
              * Nat.descFactorial D (∑ l, n l) : ℕ) : ℝ) :=
          congrArg ((↑) : ℕ → ℝ) eNat
        push_cast at e1r
        have hlhs : ((Nat.factorial (D - ∑ l, n l) : ℕ) : ℝ)
              * ((∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))
                * ((Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
                    (occupationWithRest n D) : ℕ) : ℝ))
            = ((Nat.factorial (D - ∑ l, n l) : ℕ) : ℝ)
              * ((Nat.descFactorial D (∑ l, n l) : ℕ) : ℝ) := by
          rw [← mul_assoc, mul_comm ((Nat.factorial (D - ∑ l, n l) : ℕ) : ℝ)
            (∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))]
          exact e1r
        exact mul_left_cancel₀ hFn hlhs
      rw [← hkey]
      field_simp
    refine Filter.Tendsto.congr' heq.symm ?_
    simpa using (hd (∑ l, n l)).div_const
      (∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))
  -- `√ (x ^ m) = (√ x) ^ m` on the nonnegative reals.
  have hsqrtpow : ∀ (x : ℝ) (m : ℕ), 0 ≤ x → Real.sqrt (x ^ m) = (Real.sqrt x) ^ m := by
    intro x m hx
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg hx m) x, ih, pow_succ]
  -- The coefficient, eventually rewritten around `√(multinomial / D^N)`.
  have hcoef : (fun D : ℕ => symmetricCoefficient (modeAmplitude L γ a) n D)
      =ᶠ[Filter.atTop] fun D : ℕ =>
        (Real.sqrt (((Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
          (occupationWithRest n D) : ℕ) : ℝ) / ((D : ℕ) : ℝ) ^ (∑ l, n l)) : ℂ)
          * ∏ l : Fin p', (modeAmplitude L γ a l) ^ (n l) := by
    filter_upwards [Filter.eventually_ge_atTop (max (∑ l, n l) 1)] with D hD
    have h1D : (1 : ℕ) ≤ D := by omega
    have hDpos : (0 : ℝ) ≤ ((D : ℕ) : ℝ) := Nat.cast_nonneg _
    have hM : (0 : ℝ) ≤ ((Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
        (occupationWithRest n D) : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [symmetricCoefficient, mul_assoc, ← Complex.ofReal_pow, ← mul_assoc,
      ← Complex.ofReal_mul, div_eq_mul_inv,
      Real.sqrt_mul hM ((((D : ℕ) : ℝ) ^ (∑ l, n l))⁻¹),
      Real.sqrt_inv, hsqrtpow _ _ hDpos, inv_pow]
  -- Push the real limit through `√` and the embedding `ℝ → ℂ`, then multiply.
  refine Filter.Tendsto.congr' hcoef.symm ?_
  have hsq2 : Filter.Tendsto (fun D : ℕ =>
      Real.sqrt (((Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
        (occupationWithRest n D) : ℕ) : ℝ) / ((D : ℕ) : ℝ) ^ (∑ l, n l))) Filter.atTop
      (nhds (Real.sqrt ((∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hcore
  have hL : (((Real.sqrt ((∏ l : Fin p', ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹)) : ℝ) : ℂ)
      = ∏ l : Fin p', (((Real.sqrt ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [Real.sqrt_inv, Complex.ofReal_inv,
      Real.sqrt_prod Finset.univ (fun l _ => Nat.cast_nonneg _),
      Complex.ofReal_prod Finset.univ (fun l => Real.sqrt ((Nat.factorial (n l) : ℕ) : ℝ)),
      ← prod_inv_distrib]
    simp only [← Complex.ofReal_inv]
  have hcast2 : Filter.Tendsto (fun D : ℕ =>
      ((Real.sqrt (((Nat.multinomial (Finset.univ : Finset (Fin (p'+1)))
        (occupationWithRest n D) : ℕ) : ℝ) / ((D : ℕ) : ℝ) ^ (∑ l, n l)) : ℝ) : ℂ))
      Filter.atTop
      (nhds (∏ l : Fin p', (((Real.sqrt ((Nat.factorial (n l) : ℕ) : ℝ))⁻¹ : ℝ) : ℂ))) := by
    have h0 := Complex.continuous_ofReal.continuousAt.tendsto.comp hsq2
    rw [hL] at h0
    exact h0
  rw [Finset.prod_mul_distrib]
  exact hcast2.mul_const (∏ l : Fin p', (modeAmplitude L γ a l) ^ (n l))

end Qatlib.Papers.SpinBosonQAOA26.MainResults.SymmetricBasisExpansion
