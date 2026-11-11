/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation

/-!
# Variance certification from a rational pilot

The fold `pilotMoments` computes empirical first and second moments using rational arithmetic. A
padded empirical variance `pilotVarianceUpper` and rational square-root bracket determine the
scale `pilotScale` and the dyadic accuracy parameter `pilotPrecision`.

Accurate pilot moments certify a scale above the true standard deviation; finite Born sampling
bounds control failure of this certificate. These estimates support adaptive variance scaling
for quantum Monte Carlo mean estimation as in [Montanaro2015].

## Main statements

* `unknown_variance_pilot_good_moments_certificate`: accurate moments certify a sufficient scale
  with an upper bound.
* `unknown_variance_pilot_computed_precision_and_worst_path`: the computed precision meets its
  error target and a uniform cap.
* `unknown_variance_pilot_actual_born_certificate_failure`: certificate failure has probability
  at most 2/(Nν²).

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.MonteCarloMean.PilotVariance
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option warningAsError false

/-- The rational empirical mean and second moment of `N` observations, together with a count
accumulated by the same fold. -/
def pilotMoments {I : Type} (N : ℕ) (f : I  → ℚ) (omega : Fin N  → I) : ℚ ×ℚ ×ℕ :=
  let z :=
      (List.finRange N).foldl (fun z i => (z.1+f (omega i),z.2.1+(f (omega i))^2,z.2.2+1)) (0,0,0)
  (z.1/N,z.2.1/N,z.2.2)

/-- The empirical second moment minus the squared empirical mean, clipped below at zero and then
padded by `3 * nu`. -/
def pilotVarianceUpper {I : Type} (N : ℕ) (f : I  → ℚ) (nu : ℚ) (omega : Fin N  → I) : ℚ :=
  max 0 ((pilotMoments N f omega).2.1-(pilotMoments N f omega).1^2)+3*nu

/-- Twice the upper rational square-root bracket endpoint for one quarter of the padded
empirical variance. -/
def pilotScale {I : Type} (N h : ℕ) (f : I  → ℚ) (nu : ℚ) (omega : Fin N  → I) : ℚ :=
  2*(rationalSqrtBracket (pilotVarianceUpper N f nu omega/4) h).2.1

/-- The maximum of four and the base-two ceiling logarithm of one plus the nonnegative integer
ceiling of eight times the pilot scale divided by `eps`. -/
def pilotPrecision {I : Type} (N h : ℕ) (f : I  → ℚ) (nu eps : ℚ) (omega : Fin N  → I) : ℕ :=
  max 4 (Nat.clog 2 ((⌈8*pilotScale N h f nu omega/eps⌉ : ℤ).toNat+1))

set_option maxHeartbeats 2000000

/-- The moment-accumulation fold adds the payoff sum, squared-payoff sum, and list length to its
three initial accumulators. -/
private theorem pilot_fold {J : Type} (l : List J) (g : J → ℚ) (a b : ℚ) (n : ℕ) :
    l.foldl (fun z i => (z.1 + g i, z.2.1 + (g i)^2, z.2.2 + 1)) (a,b,n) =
      (a + (l.map g).sum, b + (l.map (fun i => (g i)^2)).sum, n + l.length) := by
  induction l generalizing a b n with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    apply Prod.ext
    · (try dsimp only); ring
    · apply Prod.ext
      · (try dsimp only); ring
      · (try dsimp only); omega

/-- The pilot fold returns the sample mean, sample second moment, and the exact observation
count `N`. -/
theorem pilotMoments_eq {I : Type} (N : ℕ) (f : I → ℚ) (omega : Fin N → I) :
    pilotMoments N f omega =
      ((∑ i, f (omega i))/N, (∑ i, (f (omega i))^2)/N, N) := by
  unfold pilotMoments
  rw [pilot_fold]
  simp [← List.ofFn_eq_map, List.sum_ofFn]

/-- For a nonempty record and payoffs bounded in absolute value by one, the empirical mean has
absolute value at most one and the empirical second moment lies in [0, 1]. -/
private theorem pilot_moment_bounds {I : Type} (N : ℕ) (f : I → ℚ) (omega : Fin N → I)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) :
    |(pilotMoments N f omega).1| ≤ 1 ∧ 0 ≤ (pilotMoments N f omega).2.1 ∧
      (pilotMoments N f omega).2.1 ≤ 1 := by
  rw [pilotMoments_eq]
  (try dsimp only)
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hs : |∑ i, f (omega i)| ≤ (N : ℚ) := calc
    _ ≤ ∑ i, |f (omega i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℚ) := Finset.sum_le_sum fun i _ => hf _
    _ = _ := by simp
  refine ⟨?_, div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hn.le, ?_⟩
  · rw [abs_div, abs_of_pos hn, div_le_one hn]; exact hs
  · rw [div_le_one hn]
    calc
      _ ≤ ∑ _i : Fin N, (1 : ℚ) := Finset.sum_le_sum fun i _ => by
        have ha := abs_le.mp (hf (omega i)); nlinarith
      _ = _ := by simp

/-- Under the bounded-payoff and pilot-margin hypotheses, the fold counts `N` samples, the
variance proxy lies in [0, 4], and the positive scale is at most two and approximates the
proxy square root from above within 2/2^h. -/
theorem unknown_variance_pilot_native_moments_and_scale
    (I : Type) (N h : ℕ) (f : I → ℚ) (nu : ℚ) (omega : Fin N → I)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) :
    (pilotMoments N f omega).2.2 = N ∧ |(pilotMoments N f omega).1| ≤ 1 ∧
    0 ≤ pilotVarianceUpper N f nu omega ∧ pilotVarianceUpper N f nu omega ≤ 4 ∧
    0 < pilotScale N h f nu omega ∧ pilotScale N h f nu omega ≤ 2 ∧
    Real.sqrt (pilotVarianceUpper N f nu omega : ℝ) ≤ (pilotScale N h f nu omega : ℝ) ∧
    (pilotScale N h f nu omega : ℝ) ≤
      Real.sqrt (pilotVarianceUpper N f nu omega : ℝ) + 2/(2:ℝ)^h := by
  obtain ⟨hm, hs0, hs1⟩ := pilot_moment_bounds N f omega hN hf
  have hu0 : 0 < pilotVarianceUpper N f nu omega := by
    unfold pilotVarianceUpper; have := le_max_left 0 ((pilotMoments N f omega).2.1 - (pilotMoments N f omega).1^2); linarith
  have hu1 : pilotVarianceUpper N f nu omega ≤ 4 := by
    unfold pilotVarianceUpper
    have hh : max 0 ((pilotMoments N f omega).2.1 - (pilotMoments N f omega).1^2) ≤ 1 :=
      max_le (by norm_num) (by nlinarith [sq_nonneg (pilotMoments N f omega).1])
    linarith
  have hb := rational_sqrt_bracket_actual_interval_and_comparisons
    (pilotVarianceUpper N f nu omega / 4) h (by positivity) (by linarith)
  (try dsimp only at hb)
  obtain ⟨hl, hlu, hu, hlq, hqu, hw, _, _⟩ := hb
  have hup : 0 < (rationalSqrtBracket (pilotVarianceUpper N f nu omega / 4) h).2.1 := by
    nlinarith
  have hspos : 0 < pilotScale N h f nu omega := by unfold pilotScale; positivity
  have hsmax : pilotScale N h f nu omega ≤ 2 := by unfold pilotScale; linarith
  have hsq : (pilotVarianceUpper N f nu omega : ℝ) ≤ (pilotScale N h f nu omega : ℝ)^2 := by
    have hh : pilotVarianceUpper N f nu omega ≤ (pilotScale N h f nu omega)^2 := by
      unfold pilotScale; nlinarith
    exact_mod_cast hh
  have hlqr : (2 * ((rationalSqrtBracket (pilotVarianceUpper N f nu omega / 4) h).1 : ℝ))^2 ≤
      (pilotVarianceUpper N f nu omega : ℝ) := by
    have hh : (2 * (rationalSqrtBracket (pilotVarianceUpper N f nu omega / 4) h).1)^2 ≤
      pilotVarianceUpper N f nu omega := by nlinarith
    exact_mod_cast hh
  have hwidth : (pilotScale N h f nu omega : ℝ) =
      2 * ((rationalSqrtBracket (pilotVarianceUpper N f nu omega / 4) h).1 : ℝ) + 2/(2:ℝ)^h := by
    have hh := congrArg (fun q : ℚ => (q : ℝ)) hw
    push_cast at hh
    unfold pilotScale; push_cast
    calc
      _ = 2 * ((rationalSqrtBracket (pilotVarianceUpper N f nu omega / 4) h).1 : ℝ) + 2 * (1 / (2 : ℝ)^h) := by linarith
      _ = _ := by ring
  have hur : (0 : ℝ) ≤ pilotVarianceUpper N f nu omega := by exact_mod_cast hu0.le
  have hsr : (0 : ℝ) < pilotScale N h f nu omega := by exact_mod_cast hspos
  have hlr : (0 : ℝ) ≤ (rationalSqrtBracket (pilotVarianceUpper N f nu omega / 4) h).1 := by
    exact_mod_cast hl
  refine ⟨by simp [pilotMoments_eq], hm, hu0.le, hu1, hspos, hsmax, ?_, ?_⟩
  · nlinarith [Real.sq_sqrt hur, Real.sqrt_nonneg (pilotVarianceUpper N f nu omega : ℝ)]
  · rw [hwidth]; nlinarith [Real.sq_sqrt hur,
      Real.sqrt_nonneg (pilotVarianceUpper N f nu omega : ℝ)]

/-- A payoff bounded in absolute value by one has mean with absolute value at most one, second
moment at most one, and variance in [0, 1]. -/
private theorem pilot_expect_bounds {I : Type} [Fintype I] [DecidableEq I]
    (p : FinDist I) (f : I → ℝ) (hf : ∀ i, |f i| ≤ 1) :
    |p.expect f| ≤ 1 ∧ p.expect (fun i => f i ^ 2) ≤ 1 ∧ 0 ≤ p.variance f ∧ p.variance f ≤ 1 := by
  have hm : |p.expect f| ≤ 1 := calc
    _ ≤ ∑ i, |p.prob i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p.prob i * |f i| := by simp_rw [abs_mul, abs_of_nonneg (p.nonneg _)]
    _ ≤ ∑ i, p.prob i := Finset.sum_le_sum fun i _ => by nlinarith [p.nonneg i, hf i]
    _ = 1 := p.sum_one
  have hs : p.expect (fun i => f i ^ 2) ≤ 1 := calc
    _ ≤ ∑ i, p.prob i := Finset.sum_le_sum fun i _ => by
      have hi := abs_le.mp (hf i)
      exact mul_le_of_le_one_right (p.nonneg i) (by nlinarith)
    _ = 1 := p.sum_one
  have hv : 0 ≤ p.variance f := Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg _) (sq_nonneg _)
  have he := SignedMean.shifted_second_moment p f 0
  simp only [sub_zero] at he
  change (∑ i, p.prob i * f i^2) ≤ 1 at hs
  exact ⟨hm, hs, hv, by nlinarith [sq_nonneg (p.expect f)]⟩

/-- If both pilot moments approximate the true moments within `nu`, the squared pilot scale
bounds the true variance and the scale is at most sqrt(variance + 6nu) + 2/2^h. -/
theorem unknown_variance_pilot_good_moments_certificate
    (I : Type) [Fintype I] [DecidableEq I] (p : FinDist I) (N h : ℕ) (f : I → ℚ)
    (nu : ℚ) (omega : Fin N → I) (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1/4)
    (hm : |((pilotMoments N f omega).1 : ℝ) - p.expect (fun i => (f i : ℝ))| ≤ (nu : ℝ))
    (hs : |((pilotMoments N f omega).2.1 : ℝ) - p.expect (fun i => (f i : ℝ)^2)| ≤ (nu : ℝ)) :
    p.variance (fun i => (f i : ℝ)) ≤ (pilotScale N h f nu omega : ℝ)^2 ∧
    (pilotScale N h f nu omega : ℝ) ≤
      Real.sqrt (p.variance (fun i => (f i : ℝ)) + 6*nu) + 2/(2:ℝ)^h := by
  have hg := unknown_variance_pilot_native_moments_and_scale I N h f nu omega hN hf hnu hnu1
  have hfr : ∀ i, |(f i : ℝ)| ≤ 1 := fun i => by exact_mod_cast hf i
  obtain ⟨hmu, _, hv0, _⟩ := pilot_expect_bounds p (fun i => (f i : ℝ)) hfr
  have hcr : |((pilotMoments N f omega).1 : ℝ)| ≤ 1 := by exact_mod_cast hg.2.1
  have hdiff : |((pilotMoments N f omega).1 : ℝ)^2 - (p.expect (fun i => (f i : ℝ)))^2| ≤ 2*(nu : ℝ) := by
    have hh : |((pilotMoments N f omega).1 : ℝ)^2 - (p.expect (fun i => (f i : ℝ)))^2| =
        |((pilotMoments N f omega).1 : ℝ) - p.expect (fun i => (f i : ℝ))| *
        |((pilotMoments N f omega).1 : ℝ) + p.expect (fun i => (f i : ℝ))| := by
      rw [← abs_mul]; congr 1; ring
    rw [hh]
    have hb : |((pilotMoments N f omega).1 : ℝ) + p.expect (fun i => (f i : ℝ))| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith)
    nlinarith [abs_nonneg (((pilotMoments N f omega).1 : ℝ) - p.expect (fun i => (f i : ℝ)))]
  have he := SignedMean.shifted_second_moment p (fun i => (f i : ℝ)) 0
  simp only [sub_zero] at he
  have hU : (pilotVarianceUpper N f nu omega : ℝ) =
      max 0 (((pilotMoments N f omega).2.1 : ℝ) - ((pilotMoments N f omega).1 : ℝ)^2) + 3*(nu : ℝ) := by
    simp [pilotVarianceUpper]
  have hlo : p.variance (fun i => (f i : ℝ)) ≤ (pilotVarianceUpper N f nu omega : ℝ) := by
    rw [hU]; have := le_max_right (0 : ℝ) (((pilotMoments N f omega).2.1 : ℝ) - ((pilotMoments N f omega).1 : ℝ)^2)
    have hd := abs_le.mp hdiff; have hss := abs_le.mp hs
    change (∑ i, p.prob i * (f i : ℝ)^2) = _ at he
    change |((pilotMoments N f omega).2.1 : ℝ) - (∑ i, p.prob i * (f i : ℝ)^2)| ≤ _ at hs
    have hss := abs_le.mp hs
    linarith
  have hhi : (pilotVarianceUpper N f nu omega : ℝ) ≤ p.variance (fun i => (f i : ℝ)) + 6*(nu : ℝ) := by
    rw [hU]
    have hd := abs_le.mp hdiff
    change (∑ i, p.prob i * (f i : ℝ)^2) = _ at he
    change |((pilotMoments N f omega).2.1 : ℝ) - (∑ i, p.prob i * (f i : ℝ)^2)| ≤ _ at hs
    have hss := abs_le.mp hs
    have hnr : (0 : ℝ) < nu := by exact_mod_cast hnu
    rcases max_cases (0 : ℝ)
        (((pilotMoments N f omega).2.1 : ℝ) - ((pilotMoments N f omega).1 : ℝ)^2) with ⟨hh, _⟩ | ⟨hh, _⟩ <;> rw [hh] <;> linarith
  refine ⟨?_, hg.2.2.2.2.2.2.2.trans (add_le_add (Real.sqrt_le_sqrt hhi) le_rfl)⟩
  have hroot := hg.2.2.2.2.2.2.1
  have hU0 : (0 : ℝ) ≤ pilotVarianceUpper N f nu omega := by exact_mod_cast hg.2.2.1
  nlinarith [Real.sq_sqrt hU0, Real.sqrt_nonneg (pilotVarianceUpper N f nu omega : ℝ)]

/-- The selected precision is at least four, makes eight times the pilot scale times
2^(-precision) at most `eps`, and satisfies the stated uniform logarithmic cap. -/
theorem unknown_variance_pilot_computed_precision_and_worst_path
    (I : Type) (N h : ℕ) (f : I → ℚ) (nu eps : ℚ) (omega : Fin N → I)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) (heps : 0 < eps) :
    4 ≤ pilotPrecision N h f nu eps omega ∧
    8*(pilotScale N h f nu omega : ℝ)*(1/2:ℝ)^(pilotPrecision N h f nu eps omega) ≤ (eps : ℝ) ∧
    pilotPrecision N h f nu eps omega ≤ max 4 (Nat.clog 2 ((⌈16/eps⌉ : ℤ).toNat+1)) := by
  have hg := unknown_variance_pilot_native_moments_and_scale I N h f nu omega hN hf hnu hnu1
  have hs := hg.2.2.2.2.1
  have hs2 := hg.2.2.2.2.2.1
  have hceil : 8*pilotScale N h f nu omega/eps ≤
      (((⌈8*pilotScale N h f nu omega/eps⌉ : ℤ).toNat+1 : ℕ) : ℚ) := by
    have hc := Int.le_ceil (8*pilotScale N h f nu omega/eps)
    have ht := Int.self_le_toNat (⌈8*pilotScale N h f nu omega/eps⌉ : ℤ)
    have htr : ((⌈8*pilotScale N h f nu omega/eps⌉ : ℤ) : ℚ) ≤
        (((⌈8*pilotScale N h f nu omega/eps⌉ : ℤ).toNat : ℕ) : ℚ) := by exact_mod_cast ht
    push_cast; linarith
  have hn : ((⌈8*pilotScale N h f nu omega/eps⌉ : ℤ).toNat+1) ≤
      2 ^ pilotPrecision N h f nu eps omega :=
    (Nat.le_pow_clog (by norm_num : 1 < 2) _).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_max_right _ _))
  have hpow : 8*(pilotScale N h f nu omega : ℝ) ≤ (eps : ℝ) * 2 ^ pilotPrecision N h f nu eps omega := by
    have hh : 8*pilotScale N h f nu omega/eps ≤ (2 : ℚ)^pilotPrecision N h f nu eps omega :=
      hceil.trans (by exact_mod_cast hn)
    have hh' := (div_le_iff₀ heps).mp hh
    exact_mod_cast (by simpa only [mul_comm] using! hh' : 8*pilotScale N h f nu omega ≤ eps*(2 : ℚ)^pilotPrecision N h f nu eps omega)
  refine ⟨Nat.le_max_left _ _, ?_, ?_⟩
  · rw [div_pow, one_pow, ← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ pilotPrecision N h f nu eps omega)).mpr
    exact hpow
  · apply max_le_max (le_refl 4)
    apply Nat.clog_mono_right
    apply Nat.add_le_add_right
    apply Int.toNat_le_toNat
    apply Int.ceil_mono
    apply (div_le_div_iff_of_pos_right heps).mpr
    linarith

/-- The real coercions of the rational pilot moments equal the finite-record averages of the
real payoff and its square. -/
theorem pilotMoments_cast_avg {I : Type} [Fintype I] [DecidableEq I]
    (N : ℕ) (f : I → ℚ) (omega : Fin N → I) :
    ((pilotMoments N f omega).1 : ℝ) = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) omega ∧
    ((pilotMoments N f omega).2.1 : ℝ) = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) omega := by
  rw [pilotMoments_eq]
  simp [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg]

/-- For independent Born pilot observations under the bounded-payoff and margin hypotheses, the
probability that the squared selected scale is below the true variance is at most 2/(N·nu²). -/
theorem unknown_variance_pilot_actual_born_certificate_failure
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I) (N h : ℕ)
    (f : I → ℚ) (nu : ℚ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hN : 0 < N) (hf : ∀ i, |f i| ≤ 1) (hnu : 0 < nu) (hnu1 : nu ≤ 1/4) :
    let p := signedMeanSource A j hA;
    (∑ omega ∈ Finset.univ.filter (fun omega : Fin N → I =>
      (pilotScale N h f nu omega : ℝ)^2 < p.variance (fun i => (f i : ℝ))), p.probOf omega)
      ≤ 2/((N : ℝ)*(nu : ℝ)^2) := by
  classical
  let p := signedMeanSource A j hA
  let E :=
      fun omega : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)) omega - p.expect (fun i => (f i : ℝ))|
  let F :=
      fun omega : Fin N → I => (nu : ℝ) < |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (fun i => (f i : ℝ)^2) omega - p.expect (fun i => (f i : ℝ)^2)|
  have hnur : (0 : ℝ) < nu := by exact_mod_cast hnu
  have hd : (0 : ℝ) < (N : ℝ)*(nu : ℝ)^2 := by positivity
  have hfr : ∀ i, |(f i : ℝ)| ≤ 1 := fun i => by exact_mod_cast hf i
  have hfs : ∀ i, |(f i : ℝ)^2| ≤ 1 := by
    intro i; rw [abs_of_nonneg (sq_nonneg _)]; have := abs_le.mp (hfr i); nlinarith
  have he : p.probEvent E ≤ 1/((N : ℝ)*(nu : ℝ)^2) :=
    (p.chebyshev_avg (fun i => (f i : ℝ)) hN nu hnur).trans
      (div_le_div_of_nonneg_right (pilot_expect_bounds p _ hfr).2.2.2 hd.le)
  have hff : p.probEvent F ≤ 1/((N : ℝ)*(nu : ℝ)^2) :=
    (p.chebyshev_avg (fun i => (f i : ℝ)^2) hN nu hnur).trans
      (div_le_div_of_nonneg_right (pilot_expect_bounds p _ hfs).2.2.2 hd.le)
  have hinc : ∀ omega : Fin N → I,
      (pilotScale N h f nu omega : ℝ)^2 < p.variance (fun i => (f i : ℝ)) → E omega ∨ F omega := by
    intro omega hb
    by_contra hn
    have hh : ¬ E omega ∧ ¬ F omega := not_or.mp hn
    have hm := pilotMoments_cast_avg N f omega
    have hg := unknown_variance_pilot_good_moments_certificate I p N h f nu omega hN hf hnu hnu1
      (by rw [hm.1]; exact le_of_not_gt hh.1) (by rw [hm.2]; exact le_of_not_gt hh.2)
    exact (not_lt_of_ge hg.1) hb
  calc
    _ ≤ p.probEvent (fun omega => E omega ∨ F omega) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro omega ho
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc omega (Finset.mem_filter.mp ho).2⟩
      · intro omega _ _; exact Finset.prod_nonneg fun i _ => p.nonneg _
    _ ≤ p.probEvent E + p.probEvent F := by
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro omega _
      have hn : 0 ≤ p.probOf omega := Finset.prod_nonneg fun i _ => p.nonneg _
      by_cases he : E omega <;> by_cases hf : F omega <;>
        dsimp only [E, F] at he hf ⊢ <;> simp only [he, hf, if_true, if_false, or_true, true_or,
            false_or] <;> linarith
    _ ≤ 2/((N : ℝ)*(nu : ℝ)^2) := by
      calc
        _ ≤ 1/((N : ℝ)*(nu : ℝ)^2) + 1/((N : ℝ)*(nu : ℝ)^2) := add_le_add he hff
        _ = _ := by ring

end Qatlib.Concepts.MonteCarloMean.PilotVariance
