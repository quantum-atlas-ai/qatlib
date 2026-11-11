/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# ViscositySol25 — sampling / preparation costs of point and gradient estimation

Paper: arXiv:2512.07919 (fixed version), "Quantum algorithms for viscosity solutions
to nonlinear Hamilton-Jacobi equations based on an entropy penalisation method".

This module covers the sampling-cost claims:

* Lemma 12, Eq. (46), p.14 — point value, analog (claim `c004`);
* Lemma 13, Eq. (47), p.14 — point value, digital (claim `c005`);
* Lemma 14, Eq. (55), p.17 — gradient, analog (claim `c006`);
* Lemma 15, Eq. (61), p.18 — gradient, digital (claim `c007`);
* Lemma 17, Eq. (65)-(67), p.20 — minimum `Smin`, analog (claim `c008`);
* Lemma 18, Eq. (70), p.21 — minimum `Smin`, digital (claim `c009`).

## Modeling note

The paper reduces each of these to an amplitude-estimation / repetition count of the
standard form `N = ln(1/δ)/ζ²` in the *sampling error* `ζ`, then exhibits the sampling
error forced by the total-error budget `ε = εmin + ζ` (or the overlap-normalised
budget).  We model the repetition count by

`repetitions ζ δ = ln(1/δ)/ζ²`

which is the standard amplitude-estimation / median-of-means sample complexity
(absorbing the algorithm's constant).  The theorems below prove the exact
*rational-algebraic scaling* the paper asserts: substituting the lemma's sampling
error into `repetitions` reproduces the closed form printed in the lemma.  The
concentration-theoretic step (that `repetitions` repetitions suffice for confidence
`1−δ`) is the standard AE primitive and is not re-derived; the state-overlap /
post-selection factors `J`, `1/φ` that the paper's `O(·)` absorbs are kept explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ViscositySol25.MainResults.PrecisionEstimation

/-- Standard amplitude-estimation / median-of-means repetition count: to estimate a
quantity to standard error `ζ` with failure probability `δ` costs `ln(1/δ)/ζ²`
repetitions (constant absorbed by the caller). -/
noncomputable def repetitions (ζ δ : ℝ) : ℝ := Real.log (1 / δ) / ζ ^ 2

/-! ## c004 — Lemma 12 (analog point value) -/

/-- **Lemma 12, Eq. (46), p.14 (claim `c004`).**

The total error is `ε = εmin + ζ` with the sampling error `ζ` of the linear forms
`−ν ln|⟨xa|u⟩|²`, `−ν ln‖u‖²`.  Because the logarithms carry a factor `ν`, the
sampling error translates into a *log-error* `ζ = (ε − εmin)/(ν·J)` where `J` is the
state-overlap factor.  The number of preparations is
`ln(1/δ)·ν²·J²/(ε − εmin)² = J² · O(ln(1/δ)ν²/(ε − εmin)²)`, i.e. the paper's
`O(ln(1/δ)ν²/(ε−εmin)²)` with the constant `J²` absorbed. -/
theorem lemma12_preparations
    (ν J δ ε εmin : ℝ) (hν : 0 < ν) (hJ : 0 < J) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : 0 < ε - εmin) :
    repetitions ((ε - εmin) / (ν * J)) δ
      ≤ J ^ 2 * (Real.log (1 / δ) * ν ^ 2 / (ε - εmin) ^ 2) := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hJ0 : J ≠ 0 := ne_of_gt hJ
  have hg0 : ε - εmin ≠ 0 := ne_of_gt hgap
  refine le_of_eq ?_
  unfold repetitions
  set L : ℝ := Real.log (1 / δ)
  field_simp [hν0, hJ0, hg0]

/-- **Lemma 13, Eq. (47), p.14 (claim `c005`).**

Digital protocol.  The discretisation only changes `εmin` (it additionally contains
the finite-`Nx` error); the sampling reduction is identical to Lemma 12, giving the
same `O(ln(1/δ)ν²/(ε−εmin)²)` preparation count (`1/Nx = O(√(εmin/d))` is the
digital `εmin` hypothesis in the paper). -/
theorem lemma13_preparations
    (ν J δ ε εmin : ℝ) (hν : 0 < ν) (hJ : 0 < J) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : 0 < ε - εmin) :
    repetitions ((ε - εmin) / (ν * J)) δ
      ≤ J ^ 2 * (Real.log (1 / δ) * ν ^ 2 / (ε - εmin) ^ 2) :=
  lemma12_preparations ν J δ ε εmin hν hJ hδ hδ1 hgap

/-! ## c006 — Lemma 14 (analog gradient) -/

/-- **Lemma 14, Eq. (55), p.17 (claim `c006`).**

Gradient estimation: the allowed sampling error is `ζ = (ε − εmin)/√d` (the extra
`√d` converts the `l₂` gradient error to the `max` norm, Eq. (55)).  The ancilla
measurement precision is `γ = κ·ζ`, so the number of `|Ψ⟩` states is
`ln(1/δ)/γ² = d·ln(1/δ)/(κ²(ε−εmin)²)`.  Each `|Ψ⟩` costs `1/φ` preparations of
`|u(t)⟩` (`φ = φcoh` success probability), giving the paper's
`O(d ln(1/δ)/(κ²(ε−εmin)²))` with the constant `1/φ` absorbed. -/
theorem lemma14_gradient_preparations
    (κ d φ δ ε εmin : ℝ) (hκ : 0 < κ) (hd : 0 < d) (hφ : 0 < φ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : 0 < ε - εmin) :
    repetitions (κ * ((ε - εmin) / Real.sqrt d)) δ / φ
      ≤ (1 / φ) * (d * Real.log (1 / δ) / (κ ^ 2 * (ε - εmin) ^ 2)) := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hsd : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
  have hg0 : ε - εmin ≠ 0 := ne_of_gt hgap
  have hφ0 : φ ≠ 0 := ne_of_gt hφ
  refine le_of_eq ?_
  unfold repetitions
  set L : ℝ := Real.log (1 / δ)
  rw [show (κ * ((ε - εmin) / Real.sqrt d)) ^ 2
        = κ ^ 2 * (ε - εmin) ^ 2 / d by
      rw [mul_pow, div_pow, Real.sq_sqrt (le_of_lt hd)]
      ring]
  field_simp [hκ0, hsd, hg0, hφ0]

/-- **Lemma 15, Eq. (61), p.18 (claim `c007`).**

Digital gradient.  Same sampling reduction as Lemma 14, with the discretisation
error folded into `εmin = d^{3/2}/Nx`; the preparation count is the same
`O(d ln(1/δ)/(κ²(ε−εmin)²))` (`ν = O(εmin²/d²)`, `1/Nx = O(εmin/d^{3/2})`). -/
theorem lemma15_gradient_preparations
    (κ d φ δ ε εmin : ℝ) (hκ : 0 < κ) (hd : 0 < d) (hφ : 0 < φ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : 0 < ε - εmin) :
    repetitions (κ * ((ε - εmin) / Real.sqrt d)) δ / φ
      ≤ (1 / φ) * (d * Real.log (1 / δ) / (κ ^ 2 * (ε - εmin) ^ 2)) :=
  lemma14_gradient_preparations κ d φ δ ε εmin hκ hd hφ hδ hδ1 hgap

/-! ## c008 — Lemma 17 (analog minimum `Smin`) -/

/-- **Lemma 17, Eq. (65)-(67), p.20 (claim `c008`).**

The normalisation estimate `−ν ln‖u(t)‖²` has log-error `ν·εnorm/‖u(t)‖²`
(Eq. (67)); with `ζ = ν·εnorm/‖u(t)‖²` and `εnorm = εS* − εmin` we have
`εnorm = ζ·‖u(t)‖²/ν`, so the repetition count `ln(1/δ)/εnorm²` equals
`ln(1/δ)·ν²/(‖u(t)‖⁴·(εS*−εmin)²)`, the paper's Eq. (65). -/
theorem lemma17_minimum_preparations
    (ν unorm δ εS εmin : ℝ) (hν : 0 < ν) (hu : 0 < unorm)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : 0 < εS - εmin) :
    repetitions ((εS - εmin) * unorm ^ 2 / ν) δ
      ≤ Real.log (1 / δ) * ν ^ 2 / (unorm ^ 4 * (εS - εmin) ^ 2) := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hu0 : unorm ≠ 0 := ne_of_gt hu
  have hg0 : εS - εmin ≠ 0 := ne_of_gt hgap
  refine le_of_eq ?_
  unfold repetitions
  set L : ℝ := Real.log (1 / δ)
  field_simp [hν0, hu0, hg0]

/-- **Lemma 18, Eq. (70), p.21 (claim `c009`).**

Digital minimum.  Same cost form as Lemma 17; the digital choice is `ν = 1/Nx⁴`
with `εmin = √ν·d + ν·d·ln(1/ν)/4`. -/
theorem lemma18_minimum_preparations
    (ν unorm δ εS εmin : ℝ) (hν : 0 < ν) (hu : 0 < unorm)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : 0 < εS - εmin) :
    repetitions ((εS - εmin) * unorm ^ 2 / ν) δ
      ≤ Real.log (1 / δ) * ν ^ 2 / (unorm ^ 4 * (εS - εmin) ^ 2) :=
  lemma17_minimum_preparations ν unorm δ εS εmin hν hu hδ hδ1 hgap

/-- **Lemma 18, digital `ν`/`εmin` relation, p.21.**  With `ν = 1/Nx⁴` the minimum
error `εmin = √ν·d + ν·d·ln(1/ν)/4` becomes `d/Nx² + d·ln(Nx)/Nx⁴`, the paper's
`∼ d/Nx²`.  This is the algebraic content of "the constant `ν` … can be chosen
`ν = 1/Nx⁴`". -/
theorem lemma18_digital_epsilon_min
    (Nx d : ℝ) (hNx : 0 < Nx) :
    Real.sqrt (1 / Nx ^ 4) * d + (1 / Nx ^ 4) * d * Real.log (1 / (1 / Nx ^ 4)) / 4
      = d / Nx ^ 2 + d * Real.log Nx / Nx ^ 4 := by
  have hNx0 : Nx ≠ 0 := ne_of_gt hNx
  have hsq : Real.sqrt (1 / Nx ^ 4) = 1 / Nx ^ 2 := by
    rw [show (1 : ℝ) / Nx ^ 4 = (1 / Nx ^ 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  rw [show Real.log (1 / (1 / Nx ^ 4)) = 4 * Real.log Nx by
    rw [one_div_one_div]
    rw [show Nx ^ 4 = Nx ^ (4 : ℕ) by norm_num]
    rw [Real.log_pow]; push_cast; ring]
  field_simp

/-! ## c009 — Lemma 18, Eq. (69): LogSumExp proximity to the minimum -/

/-- **Lemma 18, Eq. (69), p.21 (claim `c009`).**

The digital readout of the minimum `Smin` rests on the LogSumExp sandwich: for
finitely many values `S j` and entropy weight `ν > 0`, the normalisation-based
soft minimum `−ν ln (∑_j e^{−S_j/ν})` deviates from the true minimum by at most
`ν ln N`, where `N` is the number of terms.  We prove the two-sided bound for any
lower bound `m` of the `S j` that is attained at some index of the Finset `s`:
the attaining term forces `∑_j e^{−S_j/ν} ≥ e^{−m/ν}` while all `N` terms are
individually at most `e^{−m/ν}`, giving `0 ≤ ν ln(∑_j e^{−S_j/ν}) + m ≤ ν ln N`. -/
theorem lemma18_logsumexp_bound
    {ι : Type*} (s : Finset ι) (S : ι → ℝ) (ν m : ℝ)
    (hν : 0 < ν) (hne : s.Nonempty)
    (hmin : ∀ j ∈ s, m ≤ S j) (hach : ∃ j₀ ∈ s, S j₀ = m) :
    |ν * Real.log (∑ j ∈ s, Real.exp (-(S j / ν))) + m|
      ≤ ν * Real.log (s.card : ℝ) := by
  obtain ⟨j₀, hj₀mem, hj₀⟩ := hach
  have hfpos : ∀ j ∈ s, 0 < Real.exp (-(S j / ν)) := fun j _ => Real.exp_pos _
  have hsumpos : 0 < ∑ j ∈ s, Real.exp (-(S j / ν)) :=
    Finset.sum_pos' (fun j hj => le_of_lt (hfpos j hj)) ⟨j₀, hj₀mem, hfpos j₀ hj₀mem⟩
  -- Lower sandwich: the attaining term forces the sum above `e^{-m/ν}`.
  have hlow : Real.exp (-(m / ν)) ≤ ∑ j ∈ s, Real.exp (-(S j / ν)) := by
    have h := Finset.single_le_sum (fun j hj => le_of_lt (hfpos j hj)) hj₀mem
    rwa [hj₀] at h
  have key1 : -(m / ν) ≤ Real.log (∑ j ∈ s, Real.exp (-(S j / ν))) := by
    have h := Real.log_le_log (Real.exp_pos _) hlow
    rwa [Real.log_exp] at h
  -- Upper sandwich: every term is at most `e^{-m/ν}`, so the sum is at most `N • e^{-m/ν}`.
  have hterm : ∀ j ∈ s, Real.exp (-(S j / ν)) ≤ Real.exp (-(m / ν)) := by
    intro j hj
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    rw [div_le_div_iff₀ hν hν]
    exact mul_le_mul_of_nonneg_right (hmin j hj) hν.le
  have hsumle : ∑ j ∈ s, Real.exp (-(S j / ν)) ≤ (s.card : ℝ) * Real.exp (-(m / ν)) := by
    calc ∑ j ∈ s, Real.exp (-(S j / ν))
        ≤ ∑ _j ∈ s, Real.exp (-(m / ν)) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * Real.exp (-(m / ν)) := by simp [Finset.sum_const]
  have key2 : Real.log (∑ j ∈ s, Real.exp (-(S j / ν)))
      ≤ Real.log (s.card : ℝ) + -(m / ν) := by
    have h := Real.log_le_log hsumpos hsumle
    have hcardne : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (s.card_pos.mpr hne).ne'
    rwa [Real.log_mul hcardne (Real.exp_pos _).ne', Real.log_exp] at h
  -- Assemble the two-sided bound.
  have h1card : (1 : ℝ) ≤ (s.card : ℝ) := by
    have h : 1 ≤ s.card := s.card_pos.mpr hne
    exact_mod_cast h
  have hlogN : 0 ≤ ν * Real.log (s.card : ℝ) :=
    mul_nonneg hν.le (Real.log_nonneg h1card)
  have hme : ν * (-(m / ν)) = -m := by field_simp [ne_of_gt hν]
  rw [abs_le]
  constructor
  · have hstep : ν * (-(m / ν)) ≤ ν * Real.log (∑ j ∈ s, Real.exp (-(S j / ν))) :=
      mul_le_mul_of_nonneg_left key1 hν.le
    linarith
  · have hstep : ν * Real.log (∑ j ∈ s, Real.exp (-(S j / ν)))
        ≤ ν * (Real.log (s.card : ℝ) + -(m / ν)) :=
      mul_le_mul_of_nonneg_left key2 hν.le
    have hring : ν * (Real.log (s.card : ℝ) + -(m / ν))
        = ν * Real.log (s.card : ℝ) - m := by rw [mul_add, hme]; ring
    linarith

end Qatlib.Papers.ViscositySol25.MainResults.PrecisionEstimation
