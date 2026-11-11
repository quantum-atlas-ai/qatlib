/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreRule
import Qatlib.Concepts.LchsSimulation.Quadrature.CompositeGaussAlgebra

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 14: the source coefficient mass is `O(‖b‖_{L¹})`

Lemma 14 of arXiv:2312.03916v2 (p. 20, Eq. (75)) bounds the total absolute mass of
the source-side coefficients `c'_{q,m} = (h₂/2) · w'_q · ‖b(s_{q,m})‖` appearing in
the discretization Eq. (72).  Since `‖b‖` is the only datum entering `c'`, the bound
is a composite Gauss–Legendre error estimate for `s ↦ ‖b(s)‖` on `[0,T]`.

The theorem below keeps the paper's composite cell picture and returns the printed
shape `∑_{q,m} |c'_{q,m}| ≤ ‖b‖_{L¹} + remainder`, together with the corollary that a
remainder no larger than `‖b‖_{L¹}` (the regime fixed by Lemma 13) gives the
advertised `O(‖b‖_{L¹})` bound with constant two.  The single-cell classical
Gauss–Legendre data (positive weights, `2Q-1` exactness and the closed form for the
squared node polynomial) is an explicit premise, exactly as for the frozen Lemma 11
formalization.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LinDynamics23.Quadrature

open Set MeasureTheory
open Qatlib.Concepts.LchsSimulation.Quadrature
open scoped BigOperators

/-- The composite source coefficient mass of printed Eq. (72),
`∑_{q,m} |c'_{q,m}| = ∑_{q,m} (h/2) · w'_q · ‖b(s_{q,m})‖`, with `h = T/M` and the
affinely transported Gauss nodes `s_{q,m} = h · (m + (node q + 1)/2)`. -/
noncomputable def sourceCoefficientMass {I : Type} [Fintype I] (b : ℝ → I → ℂ) (T : ℝ) (M Q : ℕ)
    (node weight : Fin Q → ℝ) : ℝ :=
  let h : ℝ := T / (M : ℝ)
  ∑ m : Fin M, ∑ q : Fin Q,
    (h / 2) * weight q * ‖b (h * ((m : ℝ) + (node q + 1) / 2))‖

/-- The remainder produced by the composite Gauss rule applied to `s ↦ ‖b(s)‖`:
`M` cells times the single-cell Davis–Rabinowitz bound. -/
noncomputable def sourceMassRemainder (T D : ℝ) (M Q : ℕ) : ℝ :=
  let h : ℝ := T / (M : ℝ)
  (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
    (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) * D)

/-- **Lemma 14**, Eq. (75), in remainder form: the actual composite source
coefficient mass is bounded by the `L¹` norm of the source plus the composite
Gauss remainder.  The hypotheses are the paper's smoothness of `b` together with a
uniform bound `D` on the `2Q`-th derivative of `s ↦ ‖b(s)‖` on `[0,T]`. -/
theorem lemma14_source_coefficient_mass {I : Type} [Fintype I]
    (b : ℝ → I → ℂ) (T D : ℝ) (M Q : ℕ) (node weight : Fin Q → ℝ)
    (hT : 0 < T) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hcont : Continuous (fun s : ℝ => ‖b s‖))
    (hsmooth : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) (fun s : ℝ => ‖b s‖))
    (hD : ∀ k : ℝ, |iteratedDeriv (2 * Q) (fun s : ℝ => ‖b s‖) k| ≤ D)
    (_hw : ∀ q, 0 < weight q)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q))
    (homega : (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2)) :
    sourceCoefficientMass b T M Q node weight ≤
      (∫ s in (0 : ℝ)..T, ‖b s‖) + sourceMassRemainder T D M Q := by
  dsimp only [sourceCoefficientMass, sourceMassRemainder]
  set h : ℝ := T / (M : ℝ) with hh
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hpos : 0 < h := by rw [hh]; positivity
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  set g : ℝ → ℝ := fun s => ‖b s‖ with hgdef
  have hgcont : Continuous g := hcont
  have hgcd : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) g := hsmooth
  have hderiv : ∀ k : ℝ, |iteratedDeriv (2 * Q) g k| ≤ D := hD
  have hCnonneg : 0 ≤ ((Q.factorial : ℝ) ^ 4) /
      (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) := by positivity
  have hD0 : 0 ≤ D := (abs_nonneg (iteratedDeriv (2 * Q) g 0)).trans (hderiv 0)
  have hsup : ∀ a : ℝ, (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) g k|) ≤ D := by
    intro a
    refine ciSup_le (fun k => ?_)
    by_cases hk : k ∈ Icc a (a + h)
    · haveI : Nonempty (k ∈ Icc a (a + h)) := ⟨hk⟩
      exact ciSup_le (fun _ => hderiv k)
    · haveI : IsEmpty (k ∈ Icc a (a + h)) := ⟨fun hj => hk hj⟩
      rw [iSup_of_empty', Real.sSup_empty]
      exact hD0
  have hrpow : h ^ ((2 : ℝ) * Q + 1) = h ^ (2 * Q + 1) := by
    have hc : ((2 : ℝ) * Q + 1) = ((2 * Q + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hc, Real.rpow_natCast]
  have hcell : ∀ m : Fin M,
      ∑ q, (h / 2) * weight q * g (h * ((m : ℝ) + (node q + 1) / 2)) ≤
        (∫ x in h * (m : ℝ)..h * ((m : ℝ) + 1), g x) +
          (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) * D) := by
    intro m
    set a : ℝ := h * (m : ℝ) with hadef
    have hcellx : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
        ∫ x in a..a + h, p.eval x =
          ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2) :=
      fun p hp => gauss_cell_rule_affine_exact Q a h node weight hexact p hp
    have homegacell := gauss_cell_omega Q a h node hpos homega
    have hG2 := gauss_legendre_cell_error_bound Q a h node weight g hQ hpos hcellx
      homegacell hgcd
    rw [hrpow] at hG2
    have hupper := (abs_sub_le_iff.mp hG2).2
    have hE : (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
        (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) g k|)) ≤
        (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) * D) :=
      mul_le_mul_of_nonneg_left (hsup a) (by positivity)
    have hnodes : ∀ q : Fin Q,
        a + h * (node q + 1) / 2 = h * ((m : ℝ) + (node q + 1) / 2) := by
      intro q; rw [hadef]; ring
    have hsum : ∑ q, (h / 2) * weight q * g (a + h * (node q + 1) / 2) =
        ∑ q, (h / 2) * weight q * g (h * ((m : ℝ) + (node q + 1) / 2)) :=
      Finset.sum_congr rfl (fun q _ => by rw [hnodes q])
    have hup : h * ((m : ℝ) + 1) = a + h := by rw [hadef]; ring
    rw [hup]
    rw [← hsum]
    linarith [hupper, hE]
  have hpart : ∀ (n : ℕ), (∑ m ∈ Finset.range n,
      ∫ x in h * (m : ℝ)..h * ((m : ℝ) + 1), g x) = ∫ x in (0 : ℝ)..h * (n : ℝ), g x := by
    intro n
    induction n with
    | zero => simp [intervalIntegral.integral_same]
    | succ n ih =>
        have hjoin : (∫ x in (0 : ℝ)..h * (n : ℝ), g x)
            + ∫ x in h * (n : ℝ)..h * ((n : ℝ) + 1), g x
            = ∫ x in (0 : ℝ)..h * ((n : ℝ) + 1), g x :=
          intervalIntegral.integral_add_adjacent_intervals
            (hgcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)
        rw [Finset.sum_range_succ, ih, hjoin, Nat.cast_succ]
  have hcells : (∑ m : Fin M, ∫ x in h * (m : ℝ)..h * ((m : ℝ) + 1), g x) =
      ∫ x in (0 : ℝ)..T, g x := by
    rw [Fin.sum_univ_eq_sum_range
      (fun n : ℕ => ∫ x in h * (n : ℝ)..h * ((n : ℝ) + 1), g x) M, hpart M]
    have hMh : h * (M : ℝ) = T := by rw [hh]; field_simp
    rw [hMh]
  calc (∑ m : Fin M, ∑ q : Fin Q,
        (h / 2) * weight q * g (h * ((m : ℝ) + (node q + 1) / 2)))
      ≤ ∑ m : Fin M, ((∫ x in h * (m : ℝ)..h * ((m : ℝ) + 1), g x) +
          (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) * D)) :=
        Finset.sum_le_sum (fun m _ => hcell m)
    _ = (∑ m : Fin M, ∫ x in h * (m : ℝ)..h * ((m : ℝ) + 1), g x) +
          (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) * D) := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (∫ x in (0 : ℝ)..T, g x) +
          (M : ℝ) * (((Q.factorial : ℝ) ^ 4 * h ^ (2 * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) * D) := by
        rw [hcells]
    _ = _ := by rw [hgdef]

/-- **Lemma 14**, Eq. (75), in the advertised `O(‖b‖_{L¹})` form: whenever the
composite Gauss remainder is no larger than the `L¹` mass of the source — the
regime fixed by the Lemma 13 choices of `h₂` and `Q₂` — the coefficient mass is at
most twice `‖b‖_{L¹}`. -/
theorem lemma14_source_coefficient_mass_two_mul {I : Type} [Fintype I]
    (b : ℝ → I → ℂ) (T D : ℝ) (M Q : ℕ) (node weight : Fin Q → ℝ)
    (hT : 0 < T) (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hcont : Continuous (fun s : ℝ => ‖b s‖))
    (hsmooth : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) (fun s : ℝ => ‖b s‖))
    (hD : ∀ k : ℝ, |iteratedDeriv (2 * Q) (fun s : ℝ => ‖b s‖) k| ≤ D)
    (hw : ∀ q, 0 < weight q)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q))
    (homega : (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2))
    (hsmall : sourceMassRemainder T D M Q ≤ ∫ s in (0 : ℝ)..T, ‖b s‖) :
    sourceCoefficientMass b T M Q node weight ≤ 2 * (∫ s in (0 : ℝ)..T, ‖b s‖) := by
  have h := lemma14_source_coefficient_mass b T D M Q node weight hT hQ hM hcont
    hsmooth hD hw hexact homega
  linarith

end Qatlib.Papers.LinDynamics23.Quadrature
