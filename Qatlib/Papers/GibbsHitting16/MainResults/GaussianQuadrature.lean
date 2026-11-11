/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Gibbs-state preparation: Gaussian (Hubbard--Stratonovich) quadrature

Chowdhury--Somma, *Quantum algorithms for Gibbs sampling and hitting-time estimation*,
arXiv:1603.02940v1, Lemma 1 (Eqs. (26)-(27)) and the analytic estimates of Eqs. (29)-(36).

The Gibbs state is prepared through the Hubbard--Stratonovich representation
`e^{-βH/2} = (1/√(2π)) ∫ dy e^{-y²/2} e^{-i y √β H̃}` (Eq. (24)) truncated to a finite
Gaussian quadrature `X'` in the eigenbasis of `H̃`. This file formalises the analytic core:
Poisson summation for the Gaussian lattice sum, the geometric tail estimates for the
lattice (`k`-sum) and for the truncation (`j`-sum), and the resulting bound
`‖X' - e^{-βH̃²/2}‖ ≤ ε'/2` on every spectral parameter, which is Lemma 1 of the paper.

The passage from this per-eigenvalue statement to the state-level statement (the paper's
"for all states `|φ⟩`") and the algorithm of Theorem 1 (gate complexity, amplitude
amplification) are not formalised here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.GibbsHitting16.MainResults

open Complex

/-- One term of the discrete approximation `X'` of Lemma 1, without the outer `δ` factor:
`exp (-(j δ)^2 / 2) * exp (-i (j δ) u)`. -/
def gaussTerm (δ u : ℝ) (j : ℤ) : ℂ :=
  Complex.exp (-((((j : ℝ) * δ : ℝ) : ℂ) ^ 2 / 2)) *
    Complex.exp ((-(((j : ℝ) * δ) * u) : ℝ) * Complex.I)

/-- Every term of the Gaussian lattice sum has norm `exp (-(jδ)²/2)`. -/
lemma norm_gaussTerm (δ u : ℝ) (j : ℤ) :
    ‖gaussTerm δ u j‖ = Real.exp (-(((j : ℝ) * δ) ^ 2) / 2) := by
  have harg : (-((((j : ℝ) * δ : ℝ) : ℂ) ^ 2 / 2)) =
      ((-((((j : ℝ) * δ) ^ 2) / 2)) : ℝ) := by
    push_cast
    ring
  unfold gaussTerm
  rw [harg, ← Complex.ofReal_exp, Complex.norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 1
  ring

/-- Gaussian weights `exp (-(c n²))` are summable over `ℕ`. -/
lemma summable_exp_neg_mul_sq_nat {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ 2))) := by
  have hg : Summable (fun n : ℕ => Real.exp (-c) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos (-c)).le (Real.exp_lt_one_iff.mpr (by linarith))
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h3 : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right h1 h2
    have h4 : c * (n : ℝ) ≤ c * ((n : ℝ) * (n : ℝ)) := mul_le_mul_of_nonneg_left h3 hc.le
    linarith

/-- Gaussian weights `exp (-(c n²))` are summable over `ℤ`. -/
lemma summable_exp_neg_mul_sq_int {c : ℝ} (hc : 0 < c) :
    Summable (fun j : ℤ => Real.exp (-(c * ((j : ℝ)) ^ 2))) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine (summable_exp_neg_mul_sq_nat hc).congr (fun n => ?_)
    push_cast
    ring_nf
  · refine (summable_exp_neg_mul_sq_nat hc).congr (fun n => ?_)
    push_cast
    ring_nf

/-- The lattice sum defining `X'` is summable for every `δ > 0`. -/
lemma summable_gaussTerm (δ u : ℝ) (hδ : 0 < δ) : Summable (gaussTerm δ u) := by
  refine Summable.of_norm_bounded (g := fun j : ℤ => Real.exp (-((δ ^ 2 / 2) * (j : ℝ) ^ 2)))
    (summable_exp_neg_mul_sq_int (by positivity)) (fun j => ?_)
  rw [norm_gaussTerm]
  refine Real.exp_le_exp.mpr ?_
  have h2 : (0:ℝ) ≤ (j:ℝ)^2 := sq_nonneg _
  nlinarith

/-- Poisson summation for the Gaussian (paper Eq. (29)) expressed as an identity for the
discrete sum used in Lemma 1: the exact discrete sum equals a shifted-lattice Gaussian sum. -/
lemma tsum_gaussTerm (δ : ℝ) (hδ : 0 < δ) (u : ℝ) :
    (∑' j : ℤ, gaussTerm δ u j) =
      ((Real.sqrt (2 * Real.pi) / δ : ℝ) : ℂ) *
        (∑' k : ℤ, Complex.exp (-((((u + 2 * Real.pi * (k : ℝ) / δ : ℝ)) : ℂ) ^ 2 / 2))) := by
  set A : ℂ := ((δ ^ 2 / (2 * Real.pi) : ℝ) : ℂ) with hA
  set B : ℂ := (-(Complex.I * (δ : ℂ) * (u : ℂ) / (2 * (Real.pi : ℂ)))) with hB
  have hII : Complex.I ^ 2 = -1 := Complex.I_sq
  have hAr : A.re = δ ^ 2 / (2 * Real.pi) := by
    rw [hA, Complex.ofReal_re]
  have hApos : 0 < A.re := by rw [hAr]; positivity
  have htheta := Complex.tsum_exp_neg_quadratic (a := A) (b := B) hApos
  have hL : (∑' j : ℤ, gaussTerm δ u j) =
      ∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ)) := by
    apply tsum_congr
    intro n
    rw [gaussTerm, ← Complex.exp_add]
    congr 1
    rw [hA, hB]
    push_cast
    field_simp
  rw [hL, htheta]
  congr 1
  · rw [hA]
    have hx : (0 : ℝ) ≤ δ ^ 2 / (2 * Real.pi) := by positivity
    have hcast : ((δ ^ 2 / (2 * Real.pi) : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) =
        ((δ / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cpow hx (1 / 2), ← Real.sqrt_eq_rpow]
      congr 1
      rw [Real.sqrt_div (sq_nonneg δ), Real.sqrt_sq hδ.le]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, hcast, one_div,
      ← Complex.ofReal_inv]
    congr 1
    have hsp : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  · apply tsum_congr
    intro k
    congr 1
    have hIB : Complex.I * B = (δ : ℂ) * (u : ℂ) / (2 * (Real.pi : ℂ)) := by
      rw [hB]
      field_simp
      rw [hII]
      ring
    rw [hA, hIB]
    push_cast
    have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
    have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring

/-! ## The finite quadrature sum `X'` and the full Gaussian sum -/

/-- The finite quadrature sum `X'` of Lemma 1 (paper Eq. (26)) evaluated on the spectral
parameter `u = √β x̃`: `(1/√(2π)) δ Σ_{j=-J}^{J} exp(-(jδ)^2/2) exp(-i j δ u)`. -/
def quadSum (δ u : ℝ) (J : ℕ) : ℂ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ((δ : ℂ) * ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), gaussTerm δ u j)

/-- The untruncated (`J = ∞`) version of `X'`, used as an intermediate object. -/
def fullSum (δ u : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ((δ : ℂ) * ∑' j : ℤ, gaussTerm δ u j)

/-- The symmetric integer interval sum splits into its centre and the two one-sided `ℕ`-tails. -/
lemma sum_Icc_split (f : ℤ → ℂ) (J : ℕ) :
    ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), f j =
      f 0 + ∑ i ∈ Finset.range J, (f ((i : ℤ) + 1) + f (-((i : ℤ) + 1))) := by
  induction J with
  | zero => simp
  | succ N ih =>
    push_cast
    rw [Finset.sum_Icc_succ_eq_add_endpoints, ih, Finset.sum_range_succ]
    ring

/-- The finite sum minus the untruncated sum is the sum of the two one-sided tails, indexed
by `ℕ` (the paper's truncation estimate after Eq. (31)). -/
lemma sum_Icc_sub_tsum (f : ℤ → ℂ) (J : ℕ) (hf : Summable f) :
    (∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), f j) - (∑' j : ℤ, f j) =
      -((∑' i : ℕ, f ((i : ℤ) + 1 + J)) + (∑' i : ℕ, f (-((i : ℤ) + 1 + J)))) := by
  have hpos : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    ((summable_nat_add_iff 1).mpr ((summable_int_iff_summable_nat_and_neg.mp hf).1)).congr
      (fun n => by push_cast; ring_nf)
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    ((summable_nat_add_iff 1).mpr ((summable_int_iff_summable_nat_and_neg.mp hf).2)).congr
      (fun n => by push_cast; ring_nf)
  have hsg := Summable.sum_add_tsum_nat_add J hpos
  have hsh := Summable.sum_add_tsum_nat_add J hneg
  have hsplit := tsum_int_eq_zero_add_tsum_pnat hf
  have hp : (∑' n : ℕ+, f ((n : ℕ) : ℤ)) = ∑' n : ℕ, f ((n : ℤ) + 1) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ => f ((m : ℤ)))]
    apply tsum_congr; intro n; push_cast; ring_nf
  have hn : (∑' n : ℕ+, f (-((n : ℕ) : ℤ))) = ∑' n : ℕ, f (-((n : ℤ) + 1)) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ => f (-((m : ℤ))))]
    apply tsum_congr; intro n; push_cast; ring_nf
  have e1 : (∑' (i : ℕ), f ((i : ℤ) + 1 + J)) = ∑' i : ℕ, f ((↑(i + J) : ℤ) + 1) := by
    apply tsum_congr; intro i; push_cast; ring_nf
  have e2 : (∑' (i : ℕ), f (-((i : ℤ) + 1 + J))) = ∑' i : ℕ, f (-((↑(i + J) : ℤ) + 1)) := by
    apply tsum_congr; intro i; push_cast; ring_nf
  rw [sum_Icc_split, hsplit, hp, hn, e1, e2, ← hsg, ← hsh, Finset.sum_add_distrib]
  ring


/-! ## Tail bounds -/

/-- The one-sided geometric tail `∑_{i≥1} r^i` equals `r / (1 - r)`. -/
lemma tsum_geom_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' i : ℕ, r ^ (i + 1)) = r * (1 - r)⁻¹ := by
  rw [show (fun i : ℕ => r ^ (i + 1)) = fun i : ℕ => r * r ^ i by
    funext i; rw [pow_succ]; ring]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]

/-- The shifted Gaussian weights occurring in the Poisson-sum error are summable. -/
lemma summable_tailWeight_shift (δ u : ℝ) (hδ : 0 < δ) :
    Summable (fun k : ℤ => Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2)) := by
  have hc : 0 < (2 * Real.pi / δ) ^ 2 / 4 := by positivity
  refine Summable.of_norm_bounded
    (g := fun k : ℤ => Real.exp (u ^ 2) * Real.exp (-(((2 * Real.pi / δ) ^ 2 / 4) * (k : ℝ) ^ 2)))
    ((summable_exp_neg_mul_sq_int hc).mul_left _) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc' : (0:ℝ) < 2 * Real.pi / δ := by positivity
  have hkey : -((u + (2*Real.pi/δ) * (k:ℝ))^2)/2 ≤ u^2/2 - ((2*Real.pi/δ)^2/8) * (k:ℝ)^2 := by
    nlinarith [sq_nonneg ((2*Real.pi/δ) * (k:ℝ) + 2*u)]
  have he : (u + 2*Real.pi*(k:ℝ)/δ) = ((2*Real.pi/δ) * (k:ℝ) + u) := by ring
  rw [he]
  nlinarith [hkey]

/-- The untruncated quadrature sum equals the shifted-lattice Gaussian sum (paper Eq. (33)). -/
lemma fullSum_eq_tsum (δ : ℝ) (hδ : 0 < δ) (u : ℝ) :
    fullSum δ u =
      ((∑' k : ℤ, Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2) : ℝ) : ℂ) := by
  have harg : ∀ k : ℤ, (-((((u + 2 * Real.pi * (k : ℝ) / δ : ℝ)) : ℂ) ^ 2 / 2)) =
      ((-(((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2) : ℝ) : ℂ) := by
    intro k; push_cast; ring
  have hc : ((Real.sqrt (2 * Real.pi) : ℂ))⁻¹ *
      ((δ : ℂ) * ((Real.sqrt (2 * Real.pi) / δ : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
    congr 1
    have hsp : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    field_simp
  unfold fullSum
  rw [tsum_gaussTerm δ hδ u]
  have hS : (∑' k : ℤ, Complex.exp (-((((u + 2 * Real.pi * (k : ℝ) / δ : ℝ)) : ℂ) ^ 2 / 2)))
      = ((∑' k : ℤ, Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro k
    rw [harg, ← Complex.ofReal_exp]
    congr 2
    ring
  rw [hS]
  simp only [Complex.ofReal_inv]
  calc ((Real.sqrt (2 * Real.pi) : ℂ))⁻¹ *
        ((δ : ℂ) * (((Real.sqrt (2 * Real.pi) / δ : ℝ) : ℂ) *
          ↑(∑' k : ℤ, Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2))))
      = (((Real.sqrt (2 * Real.pi) : ℂ))⁻¹ * ((δ : ℂ) * ((Real.sqrt (2 * Real.pi) / δ : ℝ) : ℂ))) *
          ↑(∑' k : ℤ, Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2)) := by ring
    _ = ↑(∑' k : ℤ, Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2)) := by
        rw [hc, one_mul]

/-- One of the two one-sided lattice tails in the Poisson-sum error is dominated by the
geometric majorant `q/(1-q)` with `q = exp (-r²/2)` (paper Eq. (30)-(32)). -/
lemma pnat_tail_le (Δ u r : ℝ) (hr : 0 < r) (hΔr : r ≤ Δ) (hu : |u| + r ≤ Δ) :
    (∑' n : ℕ+, Real.exp (-((u + Δ * (n : ℕ)) ^ 2) / 2)) ≤
      Real.exp (-(r ^ 2) / 2) * (1 - Real.exp (-(r ^ 2) / 2))⁻¹ := by
  set q : ℝ := Real.exp (-(r ^ 2) / 2) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have h : (0:ℝ) < r ^ 2 := by positivity
    linarith
  rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ => Real.exp (-((u + Δ * (m : ℝ)) ^ 2) / 2))]
  have hterm : ∀ n : ℕ, Real.exp (-((u + Δ * (↑(n + 1) : ℝ)) ^ 2) / 2) ≤ q ^ (n + 1) := by
    intro n
    push_cast
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hn1 : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith
    have hle : ((n : ℝ) + 1) * r ≤ u + Δ * ((n : ℝ) + 1) := by
      have h2 : r ≤ Δ := hΔr
      have h3 : (0:ℝ) ≤ (n:ℝ) * (Δ - r) := mul_nonneg hn0 (by linarith)
      nlinarith [le_abs_self u, neg_abs_le u]
    have h0 : (0:ℝ) ≤ ((n:ℝ)+1) * r := by positivity
    have hsq : (((n : ℝ) + 1) * r) ^ 2 ≤ (u + Δ * ((n : ℝ) + 1)) ^ 2 := by nlinarith [hle, h0]
    have hsq1 : ((n : ℝ) + 1) * (r ^ 2) ≤ (((n : ℝ) + 1) * r) ^ 2 := by nlinarith [h0]
    rw [hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith [hsq, hsq1]
  have hsum : Summable (fun n : ℕ => Real.exp (-((u + Δ * (↑(n + 1) : ℝ)) ^ 2) / 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hterm
      ((summable_geometric_of_lt_one hq0 hq1).comp_injective (fun a b h => by omega))
  have hg : Summable (fun n : ℕ => q ^ (n + 1)) := by
    refine ((summable_geometric_of_lt_one hq0 hq1).mul_left q).congr (fun n => ?_)
    rw [pow_succ]; ring
  calc (∑' n : ℕ, Real.exp (-((u + Δ * (↑(n + 1) : ℝ)) ^ 2) / 2))
      ≤ ∑' n : ℕ, q ^ (n + 1) := Summable.tsum_le_tsum hterm hsum hg
    _ = q * (1 - q)⁻¹ := tsum_geom_tail hq0 hq1

/-- The Poisson-summation error of the untruncated sum (paper Eq. (32)-(33)). -/
lemma alias_error_le (δ u : ℝ) (hδ : 0 < δ) {r : ℝ} (hr : 0 < r)
    (hu : |u| + r ≤ 2 * Real.pi / δ) :
    ‖fullSum δ u - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ≤
      2 * (Real.exp (-(r ^ 2) / 2) * (1 - Real.exp (-(r ^ 2) / 2))⁻¹) := by
  set Δ := 2 * Real.pi / δ with hΔ
  have hΔr : r ≤ Δ := by linarith [abs_nonneg u, hu]
  have hu' : |u| + r ≤ Δ := by rw [hΔ]; exact hu
  rw [fullSum_eq_tsum δ hδ u]
  set t : ℤ → ℝ := fun k => Real.exp (-((u + 2 * Real.pi * (k : ℝ) / δ) ^ 2) / 2) with ht
  have htsum : Summable t := by rw [ht]; exact summable_tailWeight_shift δ u hδ
  have hsplit := tsum_int_eq_zero_add_tsum_pnat htsum
  have hz : t 0 = Real.exp (-(u ^ 2) / 2) := by
    rw [ht]; simp
  have hpos' : (∑' n : ℕ+, t (n : ℕ)) = (∑' n : ℕ+, Real.exp (-((u + Δ * (n : ℕ)) ^ 2) / 2)) := by
    apply tsum_congr; intro n; rw [ht, hΔ]; push_cast; ring
  have hneg' : (∑' n : ℕ+, t (-(n : ℕ))) =
      (∑' n : ℕ+, Real.exp (-(((-u) + Δ * (n : ℕ)) ^ 2) / 2)) := by
    apply tsum_congr; intro n; rw [ht, hΔ]; push_cast; ring
  have hb : (∑' n : ℕ+, Real.exp (-((u + Δ * (n : ℕ)) ^ 2) / 2)) ≤
      Real.exp (-(r ^ 2) / 2) * (1 - Real.exp (-(r ^ 2) / 2))⁻¹ :=
    pnat_tail_le Δ u r hr hΔr hu'
  have hb' : (∑' n : ℕ+, Real.exp (-(((-u) + Δ * (n : ℕ)) ^ 2) / 2)) ≤
      Real.exp (-(r ^ 2) / 2) * (1 - Real.exp (-(r ^ 2) / 2))⁻¹ :=
    pnat_tail_le Δ (-u) r hr hΔr (by rwa [abs_neg])
  have hA : (∑' k : ℤ, t k) - t 0 =
      (∑' n : ℕ+, Real.exp (-((u + Δ * (n : ℕ)) ^ 2) / 2)) +
        (∑' n : ℕ+, Real.exp (-(((-u) + Δ * (n : ℕ)) ^ 2) / 2)) := by
    rw [hsplit, hz, hpos', hneg']
    ring
  have hgoal : ((∑' k : ℤ, t k) : ℂ) - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ) =
      (((∑' n : ℕ+, Real.exp (-((u + Δ * (n : ℕ)) ^ 2) / 2)) +
        (∑' n : ℕ+, Real.exp (-(((-u) + Δ * (n : ℕ)) ^ 2) / 2)) : ℝ) : ℂ) := by
    rw [← hz, ← Complex.ofReal_tsum, ← Complex.ofReal_sub, hA]
  rw [Complex.ofReal_tsum, hgoal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith [hb, hb']


/-! ## Truncation of the `j`-sum -/

/-- Bound the discarded Gaussian samples by a geometric tail. -/
lemma nsum_trunc_tail_le (δ : ℝ) (hδ : 0 < δ) {J : ℕ} (hJ : 1 ≤ J) :
    (∑' i : ℕ, Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2)) ≤
      Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
        (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) * (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) := by
  have hJ1 : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ
  set y : ℝ := (J:ℝ) * δ with hy
  set q0 : ℝ := Real.exp (-(y ^ 2) / 2) with hq
  set rt : ℝ := Real.exp (-(y * δ / 2)) with hr
  have hrt0 : 0 ≤ rt := (Real.exp_pos _).le
  have hrt1 : rt < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have : (0:ℝ) < y * δ := mul_pos (by rw [hy]; positivity) hδ
    linarith
  have hterm : ∀ i : ℕ, Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2) ≤ q0 * rt ^ (i + 1) := by
    intro i
    have hi : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    have hJi : (J:ℝ) ≤ (i:ℝ) + 1 + J := by linarith
    have hm : (0:ℝ) ≤ (i:ℝ) + 1 + J := by linarith
    have hkey : Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2) ≤
        Real.exp (-(y * δ / 2) * ((i:ℝ) + 1 + J)) := by
      apply Real.exp_le_exp.mpr
      have h2 : 0 ≤ (i:ℝ) + 1 + J := hm
      have h3 : 0 ≤ δ := hδ.le
      have h4 : y = (J:ℝ) * δ := hy
      nlinarith [hJi, hm, hδ, sq_nonneg (((i:ℝ) + 1 + J) * δ - y), mul_nonneg h2 h3]
    have hval : q0 * rt ^ (i + 1) = Real.exp (-(y * δ / 2) * ((i:ℝ) + 1 + J)) := by
      rw [hq, hr, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      nlinarith
    rw [hval]
    exact hkey
  have hgeo : Summable (fun i : ℕ => q0 * rt ^ (i + 1)) := by
    refine ((summable_geometric_of_lt_one hrt0 hrt1).mul_left (q0 * rt)).congr (fun i => ?_)
    rw [pow_succ]; ring
  have hsum : Summable (fun i : ℕ => Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2)) :=
    Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le) hterm hgeo
  calc (∑' i : ℕ, Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2))
      ≤ ∑' i : ℕ, q0 * rt ^ (i + 1) := Summable.tsum_le_tsum hterm hsum hgeo
    _ = q0 * (rt * (1 - rt)⁻¹) := by
        rw [tsum_mul_left]
        congr 1
        simpa using tsum_geom_tail hrt0 hrt1
    _ = Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
        (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) * (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) := by
        rw [hq, hr, hy, pow_two]
        ring_nf


/-! ## Bound on the truncation error of `X'` -/

/-- For `x ≥ 0`, the elementary estimate `x/(1+x) ≤ 1 - exp (-x)` holds. -/
lemma one_sub_exp_neg_ge (x : ℝ) (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  have hle : (1:ℝ) + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : (Real.exp x)⁻¹ ≤ (1 + x)⁻¹ := inv_anti₀ hpos hle
  have h1 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have heq : (1:ℝ) - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp
    ring
  rw [h1]
  linarith [h2, heq]

/-- Truncating the `j`-sum at `|j| ≤ J` changes the Gaussian sum by at most the two lattice tails of the paper's Eq. (31)/Eq. (36) estimate. -/
lemma norm_quadSum_sub_fullSum_le (δ : ℝ) (hδ : 0 < δ) (u : ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    ‖quadSum δ u J - fullSum δ u‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * δ *
      (2 * (Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
        (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
          (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹))) := by
  set B : ℝ := Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
        (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
          (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) with hB
  have hdec := sum_Icc_sub_tsum (gaussTerm δ u) J (summable_gaussTerm δ u hδ)
  have hdiff : quadSum δ u J - fullSum δ u =
      (((Real.sqrt (2 * Real.pi))⁻¹ : ℂ) * (δ : ℂ)) *
        ((∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), gaussTerm δ u j) -
          (∑' j : ℤ, gaussTerm δ u j)) := by
    unfold quadSum fullSum
    rw [← mul_sub, ← mul_sub, mul_assoc, Complex.ofReal_inv]
  have hnormeq : ∀ i : ℕ, ‖gaussTerm δ u ((i : ℤ) + 1 + J)‖ =
      Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2) := by
    intro i
    rw [norm_gaussTerm]
    congr 1
    push_cast
    ring
  have hnormeq' : ∀ i : ℕ, ‖gaussTerm δ u (-((i : ℤ) + 1 + J))‖ =
      Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2) := by
    intro i
    rw [norm_gaussTerm]
    congr 1
    push_cast
    ring
  have hinj : Function.Injective (fun i : ℕ => ((i : ℤ) + 1 + J)) := by
    intro a b h
    have h2 : (a : ℤ) = (b : ℤ) := by linarith
    exact_mod_cast h2
  have hsum1 : Summable (fun i : ℕ => gaussTerm δ u ((i : ℤ) + 1 + J)) :=
    (summable_gaussTerm δ u hδ).comp_injective hinj
  have hinj2 : Function.Injective (fun i : ℕ => -((i : ℤ) + 1 + J)) := by
    intro a b h
    have h1 : (a : ℤ) + 1 + (J : ℤ) = (b : ℤ) + 1 + (J : ℤ) := by
      simpa using neg_inj.mp h
    have h2 : (a : ℤ) = (b : ℤ) := by linarith
    exact_mod_cast h2
  have hsum2 : Summable (fun i : ℕ => gaussTerm δ u (-((i : ℤ) + 1 + J))) :=
    (summable_gaussTerm δ u hδ).comp_injective hinj2
  have htail1 : ‖∑' i : ℕ, gaussTerm δ u ((i : ℤ) + 1 + J)‖ ≤ B := by
    calc ‖∑' i : ℕ, gaussTerm δ u ((i : ℤ) + 1 + J)‖
        ≤ ∑' i : ℕ, ‖gaussTerm δ u ((i : ℤ) + 1 + J)‖ :=
          norm_tsum_le_tsum_norm hsum1.norm
      _ = ∑' i : ℕ, Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2) := by
          simp only [hnormeq]
      _ ≤ B := hB ▸ nsum_trunc_tail_le δ hδ hJ
  have htail2 : ‖∑' i : ℕ, gaussTerm δ u (-((i : ℤ) + 1 + J))‖ ≤ B := by
    calc ‖∑' i : ℕ, gaussTerm δ u (-((i : ℤ) + 1 + J))‖
        ≤ ∑' i : ℕ, ‖gaussTerm δ u (-((i : ℤ) + 1 + J))‖ :=
          norm_tsum_le_tsum_norm hsum2.norm
      _ = ∑' i : ℕ, Real.exp (-((((i : ℝ) + 1 + J) * δ) ^ 2) / 2) := by
          simp only [hnormeq']
      _ ≤ B := hB ▸ nsum_trunc_tail_le δ hδ hJ
  rw [hdiff, norm_mul, norm_mul]
  have hc1 : ‖(((Real.sqrt (2 * Real.pi)) : ℂ))⁻¹‖ = (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hc2 : ‖(δ : ℂ)‖ = δ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  rw [hc1, hc2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [hdec, norm_neg]
  calc ‖(∑' i : ℕ, gaussTerm δ u ((i : ℤ) + 1 + J)) + (∑' i : ℕ, gaussTerm δ u (-((i : ℤ) + 1 + J)))‖
      ≤ ‖∑' i : ℕ, gaussTerm δ u ((i : ℤ) + 1 + J)‖ +
        ‖∑' i : ℕ, gaussTerm δ u (-((i : ℤ) + 1 + J))‖ := norm_add_le _ _
    _ ≤ B + B := add_le_add htail1 htail2
    _ = 2 * (Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
        (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
          (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹)) := by rw [hB]; ring


/-! ## Explicit `ε'` bounds -/

/-- For `ε' > 0`, `exp (-log (1/ε')) = ε'`. -/
lemma exp_neg_two_log (ε' : ℝ) (hε' : 0 < ε') :
    Real.exp (-(Real.log (1 / ε'))) = ε' := by
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

/-- For `ε' ≤ 1/100`, `(√(log (1/ε')))² = log (1/ε')`. -/
lemma sqrt_log_sq (ε' : ℝ) (hε' : 0 < ε') (hε'100 : ε' ≤ 1 / 100) :
    Real.sqrt (Real.log (1 / ε')) ^ 2 = Real.log (1 / ε') := by
  refine Real.sq_sqrt ?_
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ hε']
  linarith

/-- With `r = 2√(log (1/ε'))` the Poisson-sum error is at most `ε'/4`, matching Eq. (32). -/
lemma alias_bound_eps {ε' r : ℝ} (hε' : 0 < ε') (hε'100 : ε' ≤ 1 / 100)
    (hr : r = 2 * Real.sqrt (Real.log (1 / ε'))) :
    2 * (Real.exp (-(r ^ 2) / 2) * (1 - Real.exp (-(r ^ 2) / 2))⁻¹) ≤ ε' / 4 := by
  have hsqL := sqrt_log_sq ε' hε' hε'100
  have hexpneg := exp_neg_two_log ε' hε'
  have hq : Real.exp (-(r ^ 2) / 2) = ε' ^ 2 := by
    rw [hr]
    have hsq2 : (2 * Real.sqrt (Real.log (1 / ε'))) ^ 2 / 2 = 2 * Real.log (1 / ε') := by
      nlinarith [hsqL]
    rw [show -(2 * Real.sqrt (Real.log (1 / ε'))) ^ 2 / 2 = -(2 * Real.log (1 / ε')) by linarith]
    rw [show -(2 * Real.log (1 / ε')) = -(Real.log (1 / ε')) + -(Real.log (1 / ε')) by ring,
      Real.exp_add, hexpneg]
    ring
  rw [hq]
  have hpos : (0:ℝ) < 1 - ε' ^ 2 := by nlinarith
  have hsmall : ε' ^ 2 ≤ 1 / 2 := by nlinarith
  have h1 : ε' ^ 2 * (1 - ε' ^ 2)⁻¹ ≤ 2 * ε' ^ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith
  have h2 : 4 * ε' ^ 2 ≤ ε' / 4 := by nlinarith
  linarith

/-- Under the paper's parameter choices the truncation error is at most `ε'/4`, matching Eq. (31). -/
lemma trunc_bound_eps {ε' δ m : ℝ} {J : ℕ} (hε' : 0 < ε') (hε'100 : ε' ≤ 1 / 100)
    (hδ : 0 < δ) (hJ : 1 ≤ J) (hm : 2 ≤ m)
    (hL : 4 ≤ Real.log (1 / ε'))
    (halias : m + 2 * Real.sqrt (Real.log (1 / ε')) ≤ 2 * Real.pi / δ)
    (htrunc : 2 * Real.sqrt (Real.log (1 / ε')) ≤ (J : ℝ) * δ) :
    (Real.sqrt (2 * Real.pi))⁻¹ * δ *
      (2 * (Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
        (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
          (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹))) ≤ ε' / 4 := by
  have hsqL := sqrt_log_sq ε' hε' hε'100
  have hexpneg := exp_neg_two_log ε' hε'
  have hL0 : (0:ℝ) ≤ Real.log (1 / ε') := by linarith
  have hsqrtpos : (0:ℝ) < Real.sqrt (Real.log (1 / ε')) := by
    have : (0:ℝ) < Real.log (1 / ε') := by linarith
    exact Real.sqrt_pos.mpr this
  have hsqrt2 : (2:ℝ) ≤ Real.sqrt (Real.log (1 / ε')) := by
    rw [Real.le_sqrt (by norm_num) hL0]
    linarith
  have hJ1 : (0:ℝ) < (J:ℝ) := by exact_mod_cast hJ
  have hy : (0:ℝ) < (J:ℝ) * δ := mul_pos hJ1 hδ
  -- weight bound
  have hq0 : Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) ≤ ε' ^ 2 := by
    have hmono : Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) ≤
        Real.exp (-((2 * Real.sqrt (Real.log (1 / ε'))) ^ 2) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hy, htrunc]
    have heq : Real.exp (-((2 * Real.sqrt (Real.log (1 / ε'))) ^ 2) / 2) = ε' ^ 2 := by
      rw [show -((2 * Real.sqrt (Real.log (1 / ε'))) ^ 2) / 2 = -(2 * Real.log (1 / ε')) by
        nlinarith [hsqL],
        show -(2 * Real.log (1 / ε')) = -(Real.log (1 / ε')) + -(Real.log (1 / ε')) by ring,
        Real.exp_add, hexpneg]
      ring
    linarith
  -- geometric factor
  have hrt0 : (0:ℝ) < Real.exp (-((J : ℝ) * δ ^ 2 / 2)) := Real.exp_pos _
  have hxpos : (0:ℝ) < (J:ℝ) * δ ^ 2 / 2 := by positivity
  have hone : ((J:ℝ) * δ ^ 2 / 2) / (1 + (J:ℝ) * δ ^ 2 / 2) ≤
      1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)) := one_sub_exp_neg_ge _ hxpos.le
  have hab : (0:ℝ) < ((J:ℝ) * δ ^ 2 / 2) / (1 + (J:ℝ) * δ ^ 2 / 2) := by positivity
  have hrt1 : Real.exp (-((J : ℝ) * δ ^ 2 / 2)) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    linarith
  have hpos1 : (0:ℝ) < 1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)) := by linarith
  have hinv : 1 / (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2))) ≤
      (1 + (J:ℝ) * δ ^ 2 / 2) / ((J:ℝ) * δ ^ 2 / 2) := by
    have h := one_div_le_one_div_of_le hab hone
    rwa [one_div_div] at h
  have hgeo : δ * (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
      (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) ≤ 2 / ((J:ℝ) * δ) + δ := by
    have h3 : δ * (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
        (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) ≤
        δ * ((1 + (J:ℝ) * δ ^ 2 / 2) / ((J:ℝ) * δ ^ 2 / 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ hδ.le
      calc Real.exp (-((J : ℝ) * δ ^ 2 / 2)) * (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹
          ≤ 1 * (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹ :=
            mul_le_mul_of_nonneg_right hrt1.le (inv_pos.mpr hpos1).le
        _ = (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹ := one_mul _
        _ ≤ (1 + (J:ℝ) * δ ^ 2 / 2) / ((J:ℝ) * δ ^ 2 / 2) := by
            rw [← one_div]; exact hinv
    have h4 : δ * ((1 + (J:ℝ) * δ ^ 2 / 2) / ((J:ℝ) * δ ^ 2 / 2)) = 2 / ((J:ℝ) * δ) + δ := by
      field_simp
    linarith
  have h2y : 2 / ((J:ℝ) * δ) ≤ 1 / Real.sqrt (Real.log (1 / ε')) := by
    rw [div_le_div_iff₀ hy hsqrtpos]
    nlinarith [htrunc]
  have hδub : δ ≤ Real.pi / Real.sqrt (Real.log (1 / ε')) := by
    have hmul := mul_le_mul_of_nonneg_right halias hδ.le
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul
    rw [le_div_iff₀ hsqrtpos]
    nlinarith
  have hsmall : δ * (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
      (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) ≤ 5 / 2 := by
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have h1 : 1 / Real.sqrt (Real.log (1 / ε')) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hsqrt2
    have h2 : Real.pi / Real.sqrt (Real.log (1 / ε')) ≤ 2 := by
      rw [div_le_iff₀ hsqrtpos]
      nlinarith
    linarith [hgeo, h2y, hδub]
  have h5 : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := by
    have h6 : (1:ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) h6
    simpa using this
  have hnn : (0:ℝ) ≤ Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
      (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi))⁻¹ * δ *
        (2 * (Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
          (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
            (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹)))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (2 * Real.exp (-(((J : ℝ) * δ) ^ 2) / 2)) *
          (δ * (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
            (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹)) := by ring
    _ ≤ 1 * (2 * ε' ^ 2) * (5 / 2) := by
        have h2e : 2 * Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) ≤ 2 * ε' ^ 2 := by linarith
        have h1' : (Real.sqrt (2 * Real.pi))⁻¹ * (2 * Real.exp (-(((J : ℝ) * δ) ^ 2) / 2)) ≤
            1 * (2 * ε' ^ 2) := by
          have := mul_le_mul h5 h2e (by positivity) (by norm_num)
          linarith
        have hc0 : (0:ℝ) ≤ δ * (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
            (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹) := by positivity
        have hb0 : (0:ℝ) ≤ 1 * (2 * ε' ^ 2) := by positivity
        exact mul_le_mul h1' hsmall hc0 hb0
    _ = 5 * ε' ^ 2 := by ring
    _ ≤ ε' / 4 := by
        have h9 : ε' ^ 2 ≤ ε' / 100 := by nlinarith
        nlinarith


/-- **Lemma 1** of Chowdhury--Somma, arXiv:1603.02940v1, Eqs. (26)-(27).

Let `H̃` be the auxiliary Hamiltonian of the paper with spectral parameter `x̃`, `u = √β x̃`,
and let `m` bound `√β ‖H̃‖`. If `X'` is the finite Gaussian quadrature with step `δ` and
half-width `J`, and the paper's parameter conditions hold
(`m ≥ 2`, `2π/δ ≥ m + 2√(log (1/ε'))` i.e. Eq. (30), `Jδ ≥ 2√(log (1/ε'))` i.e. Eq. (36)),
then `X'` approximates `e^{-β x̃²/2}` within `ε'/2`. -/
theorem lemma1_quadrature_bound {u m ε' δ : ℝ} {J : ℕ}
    (hm : 2 ≤ m) (hu : |u| ≤ m) (hε' : 0 < ε') (hε'100 : ε' ≤ 1 / 100)
    (hL : 4 ≤ Real.log (1 / ε')) (hδ : 0 < δ) (hJ : 1 ≤ J)
    (halias : m + 2 * Real.sqrt (Real.log (1 / ε')) ≤ 2 * Real.pi / δ)
    (htrunc : 2 * Real.sqrt (Real.log (1 / ε')) ≤ (J : ℝ) * δ) :
    ‖quadSum δ u J - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ ≤ ε' / 2 := by
  have hr : (0:ℝ) < 2 * Real.sqrt (Real.log (1 / ε')) := by positivity
  have hali := alias_error_le δ u hδ (r := 2 * Real.sqrt (Real.log (1 / ε'))) hr
    (by linarith [hu, halias])
  have hali' :
      2 * (Real.exp (-(2 * Real.sqrt (Real.log (1 / ε'))) ^ 2 / 2) *
        (1 - Real.exp (-(2 * Real.sqrt (Real.log (1 / ε'))) ^ 2 / 2))⁻¹) ≤ ε' / 4 :=
    alias_bound_eps hε' hε'100 rfl
  have htr := norm_quadSum_sub_fullSum_le δ hδ u hJ
  have htr' :
      (Real.sqrt (2 * Real.pi))⁻¹ * δ *
        (2 * (Real.exp (-(((J : ℝ) * δ) ^ 2) / 2) *
          (Real.exp (-((J : ℝ) * δ ^ 2 / 2)) *
            (1 - Real.exp (-((J : ℝ) * δ ^ 2 / 2)))⁻¹))) ≤ ε' / 4 :=
    trunc_bound_eps hε' hε'100 hδ hJ hm hL halias htrunc
  have hsplit : ‖quadSum δ u J - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ =
      ‖(quadSum δ u J - fullSum δ u) +
        (fullSum δ u - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ))‖ := by ring_nf
  calc ‖quadSum δ u J - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖
      ≤ ‖quadSum δ u J - fullSum δ u‖ +
        ‖fullSum δ u - ((Real.exp (-(u ^ 2) / 2) : ℝ) : ℂ)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε' / 4 + ε' / 4 := add_le_add (le_trans htr htr') (le_trans hali hali')
    _ = ε' / 2 := by ring

end Qatlib.Papers.GibbsHitting16.MainResults
