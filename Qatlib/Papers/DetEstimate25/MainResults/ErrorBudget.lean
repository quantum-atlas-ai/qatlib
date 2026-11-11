/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DetEstimate25.MainResults.SpectrumStats
import Qatlib.Concepts.KrausCompile.BornMoments.IndependentShots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false

/-! Error budget for
"A quantum algorithm for estimating the determinant"
(arXiv:2504.11049, 2025), main text Eq. (2) and Appendix C.

The paper estimates the log-determinant `alpha = sum log lam_j` by
quantum spectral sampling: phase estimation supplies noisy
eigenvalue samples with `|lamT j - lam j| <= dlam`, Monte Carlo
averaging over `N` uniform spectral samples gives the estimator
`(n/N) * sum_l log lamT (j_l)`, and the root-mean-square error is
bounded by the systematic (phase-estimation) plus the statistical
(Monte-Carlo) contribution.

This block proves, over the finite-distribution framework
`FinDist` of the Concepts layer:

- `logdet_relerr_le` (**c002**, Eq. (2)): the relative rmse obeys
  `err / |alpha| <= (1/|mu|) (2*k*dlam/(1-2*k*dlam) + delta/sqrt N)`
  with `mu` the spectral log-mean and `delta` the spectral
  log-deviation (Appendix C, Eqs. (DEF122), (Errore1), (DDF323)).
- `spectralsum_relerr_le` (**c003**, Eq. (4)): the identical budget
  for a general spectral sum `F = sum f(lam_j)` with Lipschitz
  systematic error `|fT j - f j| <= L * dlam`.

The mathematical core is exact finite arithmetic: expectation and
variance of the scaled sample mean under the uniform spectral law
(`mcEst_mean`, `mcEst_rmse_exact`), the deterministic per-sample
log-sensitivity bound (`log_perturb_bound`), and Minkowski
composition of the two error sources (`mc_noisy_rmse_le`).

Restricted: the eigenvalue list enters abstractly as `Fin n -> R`
with spectrum bounds; the noisy sampler enters through the pointwise
perturbation hypothesis; the matrix and QRAM layers are outside.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DetEstimate25.MainResults
open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.KrausCompile.BornMoments

/-! ## The uniform spectral sampling law and its statistics -/

/-- Uniform law on the eigenvalue indices: quantum phase estimation
applied to the fully mixed state samples the spectrum with mass
`1/n` per index. -/
def uniformLaw {n : ℕ} (hn : 0 < n) : FinDist (Fin n) where
  prob := fun _ => (n : ℝ) ⁻¹
  nonneg := by
    intro i
    positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_inv_cancel₀ (by exact_mod_cast hn.ne')]

/-- The uniform law assigns mass `1/n` to every eigenvalue index. -/
theorem uniformLaw_prob {n : ℕ} (hn : 0 < n) (j : Fin n) :
    (uniformLaw hn).prob j = (n : ℝ) ⁻¹ := rfl

/-- The empirical mean of an observable over the spectrum. -/
def meanOf {n : ℕ} (_hn : 0 < n) (f : Fin n → ℝ) : ℝ := (∑ j, f j) / n

/-- The empirical variance of an observable over the spectrum. -/
def varOf {n : ℕ} (_hn : 0 < n) (f : Fin n → ℝ) : ℝ :=
  (∑ j, (f j - meanOf _hn f) ^ 2) / n

/-- Variances are nonnegative. -/
theorem varOf_nonneg {n : ℕ} (_hn : 0 < n) (f : Fin n → ℝ) : 0 ≤ varOf _hn f :=
  div_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (by positivity)

/-- The uniform expectation is the spectral mean. -/
theorem uniform_expect {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    (uniformLaw hn).expect f = meanOf hn f := by
  rw [show (uniformLaw hn).expect f = ∑ j, (n : ℝ) ⁻¹ * f j from rfl, meanOf,
    Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => inv_mul_eq_div _ _)

/-- The uniform variance is the spectral variance. -/
theorem uniform_variance {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    (uniformLaw hn).variance f = varOf hn f := by
  simp only [FinDist.variance, uniform_expect]
  rfl

/-- The spectral log-mean is the uniform-law mean of the
log-spectrum. -/
theorem mu_eq_meanOf {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) :
    mu lam = meanOf hn (fun j => Real.log (lam j)) := rfl

/-- The spectral log-variance equals the uniform-law variance of the
log-spectrum. -/
theorem deltaSq_eq_varOf {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) :
    deltaSq lam = varOf hn (fun j => Real.log (lam j)) := rfl

/-- The log-determinant is `n` times the spectral log-mean. -/
theorem alpha_eq {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) :
    alpha lam = (n : ℝ) * mu lam := by
  rw [mu]
  field_simp [alpha, hn.ne']

/-! ## Finite-distribution helpers -/

/-- Scalar multiples commute with finite expectation. -/
theorem expect_scale {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) {N : ℕ} (c : ℝ) (h : (Fin N → X) → ℝ) :
    (iidLaw p N).expect (fun ω => c * h ω) = c * (iidLaw p N).expect h := by
  show ∑ ω : Fin N → X, p.probOf ω * (c * h ω) = c * ∑ ω : Fin N → X, p.probOf ω * h ω
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- Constants integrate to themselves. -/
theorem expect_const {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) {N : ℕ} (c : ℝ) :
    (iidLaw p N).expect (fun _ : Fin N → X => c) = c := by
  show ∑ ω : Fin N → X, p.probOf ω * c = c
  rw [← Finset.sum_mul, FinDist.sum_probOf]
  ring

/-- Nonnegative products give nonnegative expectations. -/
theorem expect_nonneg {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (h : X → ℝ) (hn : ∀ x, 0 ≤ h x) :
    0 ≤ p.expect h :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hn x))

/-- The product masses of the uniform law are nonnegative. -/
theorem uniform_probOf_nonneg {n : ℕ} (hn : 0 < n) {N : ℕ}
    (ω : Fin N → Fin n) : 0 ≤ (uniformLaw hn).probOf ω :=
  Finset.prod_nonneg (fun i _ => (uniformLaw hn).nonneg (ω i))

/-- Cauchy–Schwarz for finite laws: the mean absolute value is at most
the root mean square (`E|Y| ≤ √(E Y²)`). -/
theorem expect_abs_le_sqrt {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (Y : X → ℝ) :
    p.expect (fun x => |Y x|) ≤ Real.sqrt (p.expect (fun x => (Y x) ^ 2)) := by
  have hpair : ∀ i j : X, (p.prob i * |Y i|) * (p.prob j * |Y j|)
      ≤ (p.prob i * (Y i) ^ 2 * p.prob j + p.prob i * (p.prob j * (Y j) ^ 2)) / 2 := by
    intro i j
    have hnn : 0 ≤ p.prob i * p.prob j := mul_nonneg (p.nonneg i) (p.nonneg j)
    have e1 : (|Y i|) ^ 2 = (Y i) ^ 2 := sq_abs _
    have e2 : (|Y j|) ^ 2 = (Y j) ^ 2 := sq_abs _
    have h4 : 0 ≤ (|Y i| - |Y j|) ^ 2 := sq_nonneg _
    have h3 : 2 * |Y i| * |Y j| ≤ (Y i) ^ 2 + (Y j) ^ 2 := by
      nlinarith [h4, e1, e2]
    calc (p.prob i * |Y i|) * (p.prob j * |Y j|)
        = (p.prob i * p.prob j) * (|Y i| * |Y j|) := by ring
      _ ≤ (p.prob i * p.prob j) * (((Y i) ^ 2 + (Y j) ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hnn
          linarith
      _ = (p.prob i * (Y i) ^ 2 * p.prob j + p.prob i * (p.prob j * (Y j) ^ 2)) / 2 := by
          ring
  have hA : ∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j
      = (∑ i, p.prob i * (Y i) ^ 2) * (∑ j : X, p.prob j) := by
    rw [← Finset.sum_mul_sum]
  have hB : ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)
      = (∑ i, p.prob i) * (∑ j : X, p.prob j * (Y j) ^ 2) := by
    rw [← Finset.sum_mul_sum]
  have hraw : ∑ x, p.prob x * |Y x| ≤ Real.sqrt (∑ x, p.prob x * (Y x) ^ 2) := by
    have hexp : (∑ x, p.prob x * |Y x|) ^ 2
        = ∑ i, ∑ j, p.prob i * |Y i| * (p.prob j * |Y j|) := by
      rw [sq, Finset.sum_mul_sum]
    have hpull : ∀ (s : Finset X) (F : X → ℝ) (c : ℝ),
        ∑ i ∈ s, (c * F i) = c * ∑ i ∈ s, F i := by
      intro s F c
      rw [Finset.mul_sum]
    have hsplit : ∑ i, ∑ j, ((p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) / 2)
        = ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) / 2 := by
      have e1 : ∀ i : X, ∑ j, ((p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) / 2)
          = 2⁻¹ * ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) := by
        intro i
        have hhelp := hpull Finset.univ (fun j => p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) 2⁻¹
        simpa [div_eq_inv_mul] using hhelp
      have e2 : ∑ i, (2⁻¹ * ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)))
          = 2⁻¹ * ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) :=
        hpull Finset.univ (fun i => ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2))) 2⁻¹
      have hstep1 : ∑ i, ∑ j, ((p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) / 2)
          = 2⁻¹ * ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) :=
        calc ∑ i, ∑ j, ((p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) / 2)
            = ∑ i, (2⁻¹ * ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2))) :=
              Finset.sum_congr rfl (fun i _ => e1 i)
          _ = 2⁻¹ * ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) := e2
      have hsplit2 : ∀ (s : Finset X) (F G : X → ℝ),
          ∑ i ∈ s, (F i + G i) = (∑ i ∈ s, F i) + ∑ i ∈ s, G i := fun s F G =>
        Finset.sum_add_distrib (f := F) (g := G)
      have einner : ∀ i : X, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2))
          = (∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ j, p.prob i * (p.prob j * (Y j) ^ 2) :=
        fun i => hsplit2 Finset.univ (fun j => p.prob i * (Y i) ^ 2 * p.prob j)
          (fun j => p.prob i * (p.prob j * (Y j) ^ 2))
      have eouter : ∑ i, ((∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ j, p.prob i * (p.prob j * (Y j) ^ 2))
          = ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) :=
        hsplit2 Finset.univ (fun i => ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
          (fun i => ∑ j, p.prob i * (p.prob j * (Y j) ^ 2))
      have hstep2 : ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2))
          = ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) :=
        calc ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2))
            = ∑ i, ((∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) :=
              Finset.sum_congr rfl (fun i _ => einner i)
          _ = ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) := eouter
      calc (∑ i, ∑ j, ((p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) / 2))
          = 2⁻¹ * ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
            + p.prob i * (p.prob j * (Y j) ^ 2)) := hstep1
        _ = 2⁻¹ * ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) := by rw [hstep2]
        _ = ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) / 2 := by
              rw [div_eq_inv_mul]
    have hsq : (∑ x, p.prob x * |Y x|) ^ 2 ≤ (∑ x, p.prob x * (Y x) ^ 2) * (∑ x, p.prob x) := by
      rw [hexp]
      calc ∑ i, ∑ j, p.prob i * |Y i| * (p.prob j * |Y j|)
          ≤ ∑ i, ∑ j, (p.prob i * (Y i) ^ 2 * p.prob j
              + p.prob i * (p.prob j * (Y j) ^ 2)) / 2 :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hpair i j))
        _ = ((∑ i, ∑ j, p.prob i * (Y i) ^ 2 * p.prob j)
            + ∑ i, ∑ j, p.prob i * (p.prob j * (Y j) ^ 2)) / 2 := by
            rw [hsplit]
        _ = (∑ x, p.prob x * (Y x) ^ 2) * (∑ x, p.prob x) := by
            rw [hA, hB, p.sum_one]
            ring
    rw [p.sum_one, mul_one] at hsq
    have hnn2 : 0 ≤ ∑ x, p.prob x * |Y x| :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (abs_nonneg _))
    calc ∑ x, p.prob x * |Y x|
        = Real.sqrt ((∑ x, p.prob x * |Y x|) ^ 2) := (Real.sqrt_sq hnn2).symm
      _ ≤ Real.sqrt (∑ x, p.prob x * (Y x) ^ 2) := Real.sqrt_le_sqrt hsq
  exact hraw

/-! ## The Monte-Carlo spectral-sum estimator -/

/-- The Monte-Carlo estimator `(n/N) ∑_ℓ g (ω_ℓ)` of `n` times the
spectral mean of `g`: for the log-spectrum this is the paper's
`alpha_est` (Eq. EST1). -/
def mcEst {n : ℕ} (g : Fin n → ℝ) {N : ℕ} (ω : Fin N → Fin n) : ℝ :=
  (n : ℝ) / N * ∑ ℓ, g (ω ℓ)

/-- The estimator is `n` times the plain sample average. -/
theorem mcEst_eq_avg {n : ℕ} {N : ℕ}
    (g : Fin n → ℝ) (ω : Fin N → Fin n) :
    mcEst g ω = (n : ℝ) * FinDist.avg g ω := by
  rw [mcEst, FinDist.avg, div_mul_eq_mul_div, mul_div_assoc]

/-- The ideal estimator is unbiased for `n` times the spectral mean
(`⟨alpha_est⟩ = alpha`, Eq. asympt1). -/
theorem mcEst_mean {n : ℕ} (hn : 0 < n) {N : ℕ} (hN : 0 < N)
    (f : Fin n → ℝ) :
    (iidLaw (uniformLaw hn) N).expect (mcEst f) = (n : ℝ) * meanOf hn f := by
  have h1 : ∀ ω : Fin N → Fin n, mcEst f ω = (n : ℝ) * FinDist.avg f ω :=
    fun ω => mcEst_eq_avg f ω
  have h2 : (iidLaw (uniformLaw hn) N).expect (FinDist.avg f) = meanOf hn f := by
    show ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω * FinDist.avg f ω = _
    rw [FinDist.expect_avg (uniformLaw hn) f hN]
    exact uniform_expect hn f
  calc (iidLaw (uniformLaw hn) N).expect (mcEst f)
      = (iidLaw (uniformLaw hn) N).expect (fun ω => (n : ℝ) * FinDist.avg f ω) :=
        congrArg _ (funext h1)
    _ = (n : ℝ) * (iidLaw (uniformLaw hn) N).expect (FinDist.avg f) :=
        expect_scale _ _ _
    _ = (n : ℝ) * meanOf hn f := by rw [h2]

/-- The exact statistical rmse of the ideal estimator: the variance is
reduced by the sample count (`Delta alpha_mc = n Delta / sqrt N`,
Eq. asympt). -/
theorem mcEst_rmse_exact {n : ℕ} (hn : 0 < n) {N : ℕ} (hN : 0 < N)
    (f : Fin n → ℝ) :
    (iidLaw (uniformLaw hn) N).expect (fun ω => (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2)
      = (n : ℝ) ^ 2 * varOf hn f / N := by
  have hY : ∀ ω : Fin N → Fin n,
      mcEst f ω - (n : ℝ) * meanOf hn f
        = (n : ℝ) * (FinDist.avg f ω - (uniformLaw hn).expect f) := by
    intro ω
    rw [mcEst_eq_avg f ω, uniform_expect hn f]
    ring
  have hpeSum : ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2
      = (n : ℝ) ^ 2 * ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
          * (FinDist.avg f ω - (uniformLaw hn).expect f) ^ 2 := by
    rw [show (∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
            * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2)
          = ∑ ω : Fin N → Fin n, (n : ℝ) ^ 2 * ((uniformLaw hn).probOf ω
              * (FinDist.avg f ω - (uniformLaw hn).expect f) ^ 2) from
        Finset.sum_congr rfl (fun ω _ => by rw [hY ω]; ring)]
    rw [← Finset.mul_sum]
  show ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
      * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2 = _
  rw [hpeSum, FinDist.expect_avg_sub_sq (uniformLaw hn) f hN, uniform_variance hn f]
  ring

/-- Triangle inequality for the absolute value on `ℝ`. -/
theorem abs_tri (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  apply abs_le.2
  constructor
  · linarith [(abs_le.mp (le_refl (|a|))).1, (abs_le.mp (le_refl (|b|))).1]
  · linarith [(abs_le.mp (le_refl (|a|))).2, (abs_le.mp (le_refl (|b|))).2]

/-- **Minkowski composition of the two error sources**: if every
per-index value of `g` differs from `f` by at most `e` (the
systematic, phase-estimation error) then the noisy Monte-Carlo
estimator of `g` has second moment at most `(n*(e + sqrt(varOf f)/sqrt N))²`
— the systematic plus the statistical contribution
(Eq. (Errore) with the deterministic bound (NEW1)). -/
theorem mc_noisy_rmse_le {n : ℕ} (hn : 0 < n) {N : ℕ} (hN : 0 < N)
    (f g : Fin n → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hsys : ∀ j, |g j - f j| ≤ e) :
    (iidLaw (uniformLaw hn) N).expect
      (fun ω => (mcEst g ω - (n : ℝ) * meanOf hn f) ^ 2)
      ≤ ((n : ℝ) * (e + Real.sqrt (varOf hn f) / Real.sqrt N)) ^ 2 := by
  have hpnn : ∀ ω : Fin N → Fin n, 0 ≤ (uniformLaw hn).probOf ω :=
    fun ω => uniform_probOf_nonneg hn (N := N) ω
  -- the systematic per-sample deviation of the estimator
  have hsysp : ∀ ω : Fin N → Fin n, |mcEst g ω - mcEst f ω| ≤ (n : ℝ) * e := by
    intro ω
    rw [mcEst, mcEst, ← mul_sub]
    rw [← show ∑ ℓ, (g (ω ℓ) - f (ω ℓ)) = ∑ ℓ, g (ω ℓ) - ∑ ℓ, f (ω ℓ) from
      Finset.sum_sub_distrib (fun ℓ => g (ω ℓ)) (fun ℓ => f (ω ℓ))]
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc (n : ℝ) / N * |∑ ℓ, (g (ω ℓ) - f (ω ℓ))|
        ≤ (n : ℝ) / N * ∑ ℓ, |g (ω ℓ) - f (ω ℓ)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (n : ℝ) / N * ∑ ℓ : Fin N, e :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun ℓ _ => hsys (ω ℓ))) (by positivity)
      _ ≤ (n : ℝ) / N * ((N : ℝ) * e) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simp
      _ = (n : ℝ) * e := by
          have hNcast : ((N : ℝ)) ≠ 0 := by exact_mod_cast hN.ne'
          field_simp
  -- pointwise domination by the two-error decomposition
  have hpw : ∀ ω : Fin N → Fin n,
      (mcEst g ω - (n : ℝ) * meanOf hn f) ^ 2
        ≤ ((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2 := by
    intro ω
    have hsplit : mcEst g ω - (n : ℝ) * meanOf hn f
        = (mcEst g ω - mcEst f ω) + (mcEst f ω - (n : ℝ) * meanOf hn f) := by ring
    have hR : (0 : ℝ) ≤ (n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f| :=
      add_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)) he) (abs_nonneg _)
    have hfin : |mcEst g ω - (n : ℝ) * meanOf hn f|
        ≤ (n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f| := by
      rw [hsplit]
      calc |(mcEst g ω - mcEst f ω) + (mcEst f ω - (n : ℝ) * meanOf hn f)|
          ≤ |mcEst g ω - mcEst f ω| + |mcEst f ω - (n : ℝ) * meanOf hn f| :=
            abs_tri _ _
        _ ≤ (n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f| := by
            linarith [hsysp ω]
    exact (sq_le_sq).2 (by
      rw [abs_of_nonneg hR]
      exact hfin)
  -- statistical moments of the ideal estimator
  have hEY2 : (iidLaw (uniformLaw hn) N).expect
      (fun ω => (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2)
      = (n : ℝ) ^ 2 * varOf hn f / N := mcEst_rmse_exact hn hN f
  have hEabs : (iidLaw (uniformLaw hn) N).expect
      (fun ω => |mcEst f ω - (n : ℝ) * meanOf hn f|)
      ≤ (n : ℝ) * Real.sqrt (varOf hn f) / Real.sqrt N := by
    refine le_trans (expect_abs_le_sqrt _ _) ?_
    rw [hEY2,
      Real.sqrt_div (mul_nonneg (sq_nonneg (n : ℝ)) (varOf_nonneg hn f)),
      Real.sqrt_mul (sq_nonneg (n : ℝ)) (varOf hn f),
      Real.sqrt_sq (by positivity)]
  -- linearity of the dominating expectation
  have hline : (iidLaw (uniformLaw hn) N).expect
      (fun ω => ((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2)
      = ((n : ℝ) * e) ^ 2
        + 2 * (n : ℝ) * e * (iidLaw (uniformLaw hn) N).expect
            (fun ω => |mcEst f ω - (n : ℝ) * meanOf hn f|)
        + (n : ℝ) ^ 2 * varOf hn f / N := by
    show ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
        * (((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2) = _
    have hpe : ∀ ω : Fin N → Fin n,
        (uniformLaw hn).probOf ω
            * (((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2)
        = (uniformLaw hn).probOf ω * ((n : ℝ) * e) ^ 2
          + ((uniformLaw hn).probOf ω
              * (2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|)
            + (uniformLaw hn).probOf ω
              * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2) := by
      intro ω
      linear_combination (uniformLaw hn).probOf ω
        * (sq_abs (mcEst f ω - (n : ℝ) * meanOf hn f))
    have hpeSum : ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
            * (((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2)
        = ∑ ω : Fin N → Fin n, ((uniformLaw hn).probOf ω * ((n : ℝ) * e) ^ 2
          + ((uniformLaw hn).probOf ω
              * (2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|)
            + (uniformLaw hn).probOf ω
              * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2)) :=
      Finset.sum_congr rfl (fun ω _ => hpe ω)
    have hsplit : ∑ ω : Fin N → Fin n, ((uniformLaw hn).probOf ω * ((n : ℝ) * e) ^ 2
          + ((uniformLaw hn).probOf ω
              * (2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|)
          + (uniformLaw hn).probOf ω
              * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2))
        = (∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω * ((n : ℝ) * e) ^ 2)
          + ((∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
              * (2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|))
          + ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
              * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2) := by
      have h1 : ∀ (s : Finset (Fin N → Fin n))
          (F G H : (Fin N → Fin n) → ℝ),
          ∑ ω ∈ s, (F ω + (G ω + H ω))
            = (∑ ω ∈ s, F ω) + ((∑ ω ∈ s, G ω) + ∑ ω ∈ s, H ω) := by
        intro s F G H
        rw [Finset.sum_add_distrib (f := fun ω => F ω) (g := fun ω => G ω + H ω),
            Finset.sum_add_distrib (f := fun ω => G ω) (g := fun ω => H ω)]
      exact h1 Finset.univ _ _ _
    rw [hpeSum, hsplit]
    have hconst : ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω * ((n : ℝ) * e) ^ 2
        = ((n : ℝ) * e) ^ 2 :=
      expect_const (uniformLaw hn) (((n : ℝ) * e) ^ 2)
    have hmid : ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
          * (2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|)
        = 2 * (n : ℝ) * e * (iidLaw (uniformLaw hn) N).expect
            (fun ω => |mcEst f ω - (n : ℝ) * meanOf hn f|) := by
      rw [show (∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
            * (2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|))
            = (iidLaw (uniformLaw hn) N).expect
              (fun ω => 2 * (n : ℝ) * e * |mcEst f ω - (n : ℝ) * meanOf hn f|) from rfl]
      rw [expect_scale]
    have hlast : ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
          * (mcEst f ω - (n : ℝ) * meanOf hn f) ^ 2
        = (n : ℝ) ^ 2 * varOf hn f / N := hEY2
    rw [hconst, hmid, hlast]
    ring
  -- assemble
  have h2n : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
  have hk : (0 : ℝ) ≤ 2 * (n : ℝ) * e := mul_nonneg h2n he
  have hEabs0 : (0 : ℝ) ≤ (iidLaw (uniformLaw hn) N).expect
      (fun ω => |mcEst f ω - (n : ℝ) * meanOf hn f|) :=
    expect_nonneg _ _ (fun ω => abs_nonneg _)
  calc (iidLaw (uniformLaw hn) N).expect
        (fun ω => (mcEst g ω - (n : ℝ) * meanOf hn f) ^ 2)
      ≤ (iidLaw (uniformLaw hn) N).expect
          (fun ω => ((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2) := by
        show ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω * (mcEst g ω - (n : ℝ) * meanOf hn f) ^ 2
            ≤ ∑ ω : Fin N → Fin n, (uniformLaw hn).probOf ω
                * (((n : ℝ) * e + |mcEst f ω - (n : ℝ) * meanOf hn f|) ^ 2)
        exact Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left (hpw ω) (hpnn ω))
    _ = ((n : ℝ) * e) ^ 2
          + 2 * (n : ℝ) * e * (iidLaw (uniformLaw hn) N).expect
              (fun ω => |mcEst f ω - (n : ℝ) * meanOf hn f|)
          + (n : ℝ) ^ 2 * varOf hn f / N := hline
    _ ≤ ((n : ℝ) * e) ^ 2
          + 2 * (n : ℝ) * e * ((n : ℝ) * Real.sqrt (varOf hn f) / Real.sqrt N)
          + (n : ℝ) ^ 2 * varOf hn f / N :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hEabs hk)) le_rfl
    _ = ((n : ℝ) * (e + Real.sqrt (varOf hn f) / Real.sqrt N)) ^ 2 := by
        have key : (Real.sqrt (varOf hn f) / Real.sqrt (N : ℝ)) ^ 2
            = varOf hn f / (N : ℝ) := by
          rw [div_pow, Real.sq_sqrt (varOf_nonneg hn f), Real.sq_sqrt (by positivity)]
        rw [show ((n : ℝ) ^ 2 * varOf hn f / (N : ℝ))
            = (n : ℝ) ^ 2 * (Real.sqrt (varOf hn f) / Real.sqrt (N : ℝ)) ^ 2 from by
          rw [key]
          ring]
        ring

/-! ## Log-sensitivity of the eigenvalue estimates -/

/-- Perturbing a positive value by at most `d < x` changes its
logarithm by at most `d / (x - d)` (Appendix C, Eq. (DEF122)). -/
theorem log_perturb_bound {x y d : ℝ} (hd : 0 ≤ d) (hx : d < x)
    (hy : |y - x| ≤ d) :
    |Real.log y - Real.log x| ≤ d / (x - d) := by
  have hx0 : 0 < x - d := by linarith
  have hyle : y ≤ x + d := by linarith [(abs_le.mp hy).2]
  have hyge : x - d ≤ y := by linarith [(abs_le.mp hy).1]
  have hypos : 0 < y := by linarith
  have hxpos : 0 < x := by linarith
  rcases lt_or_ge y x with hxy | hxy
  · rw [abs_of_nonpos (by
      have := Real.log_le_log hypos (le_of_lt hxy)
      linarith), neg_sub]
    have hxd : 0 < x - d := hx0
    have hxdne : x - d ≠ 0 := ne_of_gt hxd
    calc Real.log x - Real.log y ≤ Real.log x - Real.log (x - d) := by
          have h1 := Real.log_le_log hxd hyge
          linarith
      _ = Real.log (1 + d / (x - d)) := by
          rw [← Real.log_div (ne_of_gt hxpos) hxdne]
          congr 1
          field_simp [hxdne]
          ring
      _ ≤ d / (x - d) := by
          have hdx : (0 : ℝ) ≤ d / (x - d) := div_nonneg hd (le_of_lt hx0)
          have hw : (0 : ℝ) < 1 + d / (x - d) := by linarith
          have h1 := Real.log_le_sub_one_of_pos hw
          have h2 : (1 + d / (x - d)) - 1 = d / (x - d) := by ring
          linarith
  · rw [abs_of_nonneg (by
      have := Real.log_le_log hxpos hxy
      linarith)]
    calc Real.log y - Real.log x ≤ Real.log (x + d) - Real.log x := by
          have h1 := Real.log_le_log hypos hyle
          linarith
      _ = Real.log (1 + d / x) := by
          have hxdp : (0 : ℝ) < x + d := by linarith
          rw [← Real.log_div (ne_of_gt hxdp) (ne_of_gt hxpos)]
          congr 1
          field_simp [ne_of_gt hxpos]
      _ ≤ d / x := by
          have hdx : (0 : ℝ) ≤ d / x := div_nonneg hd (le_of_lt hxpos)
          have hw : (0 : ℝ) < 1 + d / x := by linarith
          have h1 := Real.log_le_sub_one_of_pos hw
          have h2 : (1 + d / x) - 1 = d / x := by ring
          linarith
      _ ≤ d / (x - d) := by
          rw [div_le_div_iff₀ hxpos hx0]
          exact mul_le_mul_of_nonneg_left (by linarith) hd

/-! ## c002: relative error of the log-determinant estimator -/

/-- **c002 (Eq. (2) / DDF323)**: the relative rmse of the noisy
log-determinant estimator is bounded by the systematic
phase-estimation term `2κdlam/(1-2κdlam)` plus the statistical
Monte-Carlo term `delta/sqrt N`, normalized by `|mu|`. -/
theorem logdet_relerr_le {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    {k dlam : ℝ} (hk : 1 ≤ k) (hdk : 2 * k * dlam < 1)
    (lam lamT : Fin n → ℝ)
    (hlo : ∀ j, 1 / (2 * k) ≤ lam j)
    (hnoise : ∀ j, |lamT j - lam j| ≤ dlam) :
    Real.sqrt ((iidLaw (uniformLaw hn) N).expect
        (fun ω => (mcEst (fun j => Real.log (lamT j)) ω - alpha lam) ^ 2)) / |alpha lam|
      ≤ (1 / |mu lam|) * (2 * k * dlam / (1 - 2 * k * dlam) + delta lam / Real.sqrt N) := by
  have hkpos : 0 < k := by linarith
  have h2k : 0 < 2 * k := by positivity
  have h2knn : (0 : ℝ) ≤ 2 * k := le_of_lt h2k
  have hden : 0 < 1 - 2 * k * dlam := by linarith
  have hdlampos : 0 ≤ dlam := le_trans (abs_nonneg _) (hnoise ⟨0, hn⟩)
  have hdlamlt : dlam < 1 / (2 * k) := by
    rw [lt_div_iff₀ h2k]
    nlinarith [mul_pos hkpos hden]
  have hmin : ∀ j, dlam < lam j := by
    intro j
    have h3 := hdlamlt
    have h4 := hlo j
    linarith
  have hsens : ∀ j, |Real.log (lamT j) - Real.log (lam j)|
      ≤ 2 * k * dlam / (1 - 2 * k * dlam) := by
    intro j
    have h1 := log_perturb_bound hdlampos (hmin j) (hnoise j)
    have h2 : (1 - 2 * k * dlam) / (2 * k) ≤ lam j - dlam := by
      have h5 : (1 : ℝ) ≤ 2 * k * lam j := by
        have h6 := (div_le_iff₀ h2k).mp (hlo j)
        linarith
      rw [div_le_iff₀ h2k]
      nlinarith [h5]
    have h3 : (0 : ℝ) < (1 - 2 * k * dlam) / (2 * k) := div_pos hden h2k
    have h4 : (0 : ℝ) < lam j - dlam := by linarith
    calc |Real.log (lamT j) - Real.log (lam j)| ≤ dlam / (lam j - dlam) := h1
      _ ≤ dlam / ((1 - 2 * k * dlam) / (2 * k)) := by
          rw [div_le_div_iff₀ h4 h3]
          exact mul_le_mul_of_nonneg_left h2 hdlampos
      _ = 2 * k * dlam / (1 - 2 * k * dlam) := by
          have hdenne : (1 - 2 * k * dlam) ≠ 0 := ne_of_gt hden
          have h2kne : (2 * k : ℝ) ≠ 0 := ne_of_gt h2k
          field_simp [hdenne, h2kne]
  have hmain := mc_noisy_rmse_le hn hN (fun j => Real.log (lam j))
    (fun j => Real.log (lamT j)) (2 * k * dlam / (1 - 2 * k * dlam))
    (div_nonneg (mul_nonneg h2knn hdlampos) (le_of_lt hden)) hsens
  have hmean : (n : ℝ) * meanOf hn (fun j => Real.log (lam j)) = alpha lam := by
    rw [← mu_eq_meanOf hn lam, alpha_eq hn lam]
  have hvar : varOf hn (fun j => Real.log (lam j)) = deltaSq lam := (deltaSq_eq_varOf hn lam).symm
  rw [hmean, hvar] at hmain
  have hdeltanonneg : 0 ≤ delta lam := Real.sqrt_nonneg _
  have hRnonneg : 0 ≤ (n : ℝ) * (2 * k * dlam / (1 - 2 * k * dlam) + delta lam / Real.sqrt N) := by
    refine mul_nonneg (by positivity) ?_
    refine add_nonneg (div_nonneg (mul_nonneg h2knn hdlampos) (le_of_lt hden)) ?_
    exact div_nonneg hdeltanonneg (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt ((iidLaw (uniformLaw hn) N).expect
      (fun ω => (mcEst (fun j => Real.log (lamT j)) ω - alpha lam) ^ 2))
      ≤ (n : ℝ) * (2 * k * dlam / (1 - 2 * k * dlam) + delta lam / Real.sqrt N) :=
    le_trans (Real.sqrt_le_sqrt hmain) (le_of_eq (Real.sqrt_sq hRnonneg))
  have halpha : |alpha lam| = (n : ℝ) * |mu lam| := by
    rw [alpha_eq hn lam, abs_mul, abs_of_nonneg (by positivity)]
  rw [halpha]
  calc Real.sqrt ((iidLaw (uniformLaw hn) N).expect
        (fun ω => (mcEst (fun j => Real.log (lamT j)) ω - alpha lam) ^ 2))
        / ((n : ℝ) * |mu lam|)
      = (Real.sqrt ((iidLaw (uniformLaw hn) N).expect
          (fun ω => (mcEst (fun j => Real.log (lamT j)) ω - alpha lam) ^ 2)) / (n : ℝ))
        / |mu lam| := by ring
    _ ≤ (((n : ℝ) * (2 * k * dlam / (1 - 2 * k * dlam) + delta lam / Real.sqrt N)) / (n : ℝ))
        / |mu lam| := by
        refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
        exact div_le_div_of_nonneg_right hsqrt (by positivity)
    _ = (2 * k * dlam / (1 - 2 * k * dlam) + delta lam / Real.sqrt N) / |mu lam| := by
        field_simp
    _ = (1 / |mu lam|) * (2 * k * dlam / (1 - 2 * k * dlam) + delta lam / Real.sqrt N) := by
        ring

/-! ## c003: relative error of a general spectral-sum estimator -/

/-- **c003 (Eq. (4) / ddd)**: the same budget for the spectral sum
`F = ∑ f(lam j)` of a non-negative observable with Lipschitz
systematic error: the relative rmse is bounded by `L*dlam` plus the
statistical term `sqrt(varOf f)/sqrt N`, normalized by the mean. -/
theorem spectralsum_relerr_le {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (f fT : Fin n → ℝ) (L dlam : ℝ)
    (hlip : ∀ j, |fT j - f j| ≤ L * dlam)
    (hmeanpos : 0 < meanOf hn f) :
    Real.sqrt ((iidLaw (uniformLaw hn) N).expect
        (fun ω => (mcEst fT ω - (n : ℝ) * meanOf hn f) ^ 2)) / |(n : ℝ) * meanOf hn f|
      ≤ (1 / meanOf hn f)
          * (L * dlam + Real.sqrt (varOf hn f) / Real.sqrt N) := by
  have hLd : 0 ≤ L * dlam := by
    have := abs_nonneg (fT ⟨0, hn⟩ - f ⟨0, hn⟩)
    linarith [hlip ⟨0, hn⟩, abs_nonneg (fT ⟨0, hn⟩ - f ⟨0, hn⟩)]
  have hmain := mc_noisy_rmse_le hn hN f fT (L * dlam) hLd hlip
  have hRnonneg : 0 ≤ (n : ℝ) * (L * dlam + Real.sqrt (varOf hn f) / Real.sqrt N) := by
    refine mul_nonneg (by positivity) ?_
    exact add_nonneg hLd (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt ((iidLaw (uniformLaw hn) N).expect
      (fun ω => (mcEst fT ω - (n : ℝ) * meanOf hn f) ^ 2))
      ≤ (n : ℝ) * (L * dlam + Real.sqrt (varOf hn f) / Real.sqrt N) :=
    le_trans (Real.sqrt_le_sqrt hmain) (le_of_eq (Real.sqrt_sq hRnonneg))
  have habs : |(n : ℝ) * meanOf hn f| = (n : ℝ) * meanOf hn f := by
    rw [abs_mul, abs_of_pos (by positivity), abs_of_pos hmeanpos]
  rw [habs]
  calc Real.sqrt ((iidLaw (uniformLaw hn) N).expect
        (fun ω => (mcEst fT ω - (n : ℝ) * meanOf hn f) ^ 2))
        / ((n : ℝ) * meanOf hn f)
      = (Real.sqrt ((iidLaw (uniformLaw hn) N).expect
          (fun ω => (mcEst fT ω - (n : ℝ) * meanOf hn f) ^ 2)) / (n : ℝ))
        / meanOf hn f := by ring
    _ ≤ (((n : ℝ) * (L * dlam + Real.sqrt (varOf hn f) / Real.sqrt N)) / (n : ℝ))
        / meanOf hn f := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hmeanpos)
        exact div_le_div_of_nonneg_right hsqrt (by positivity)
    _ = (L * dlam + Real.sqrt (varOf hn f) / Real.sqrt N) / meanOf hn f := by
        field_simp
    _ = (1 / meanOf hn f) * (L * dlam + Real.sqrt (varOf hn f) / Real.sqrt N) := by
        ring

end Qatlib.Papers.DetEstimate25.MainResults
