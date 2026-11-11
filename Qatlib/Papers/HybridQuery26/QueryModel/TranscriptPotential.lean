/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Transcript potential and the one-block progress inequality (HybridQuery26 §3)

Source: Ambainis–Gilyén–Kokainis, *Tight bounds for hybrid quantum-classical query
algorithms*, arXiv:2610.06803v1, §3 "Transcripts and progress measure", eqs. (2)–(4)
and Lemma 1.

For a hybrid algorithm and two oracles `U₀, U₁` the paper writes `p_h`, `q_h` for the
probabilities of the classical transcript `h` under `U₀` and `U₁`, and uses the
χ²-type potential

`M(p, q) = ∑_z (p_z − q_z)² / (2 (p_z + q_z))`   (eq. (2))

as a progress measure.  This module formalises the potential itself together with the
list of analytic facts that the lower-bound argument consumes:

* `potential_nonneg`, `potential_comm`, `potential_self` — elementary structure;
* `one_sub_potential` — the identity `1 − M(p,q) = ∑_z 2 p_z q_z / (p_z + q_z)` for
  probability distributions, which is the form in which the paper's proof of Lemma 1
  uses `M`;
* `tv_sq_le_potential` — the Cauchy–Schwarz bound `TV(p,q)² ≤ M(p,q)` of §3, hence
  bounded error (`TV ≥ 1/3`) forces `M_T ≥ 1/9`;
* `inner_norm_sq_le_one_sub_potential`, `one_sub_state_distance_sq_le_inner_norm_sq`
  and `potential_le_state_distance_sq` — for the Born distributions of two normalised
  states `|ψ₀⟩, |ψ₁⟩` measured in a common orthonormal basis, the potential is at most
  the squared Hilbert distance `‖ |ψ₀⟩ − |ψ₁⟩ ‖²`;
* `one_block_progress_le` — Lemma 1: conditioning on a history `h` whose posterior
  weight for `U₀` is `a`, the one-block increment of the conditional progress obeys
  `M_{t+1}(h) − M_t(h) ≤ (1 − M_t(h)) ‖ |ψ₀⟩ − |ψ₁⟩ ‖²`.

The measurement is the computational-basis read-out of the repository's
`QState`/`BornProb` vocabulary, i.e. the paper's "common final measurement" restricted
to a basis measurement.  This module contains no algorithm, no cost accounting and no
claim; it only supplies the analytic core of the §3 framework.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.HybridQuery26.QueryModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

/-! ## §1 The transcript potential -/

/-- **The transcript potential of eq. (2).** For two transcript distributions `p` and
`q` on the same finite transcript set, `M(p,q) = ∑_z (p_z − q_z)² / (2 (p_z + q_z))`;
the summand of an index with `p_z = q_z = 0` is zero, which is Lean's `x / 0 = 0`. -/
noncomputable def potential (p q : I → ℝ) : ℝ :=
  ∑ z, (p z - q z) ^ 2 / (2 * (p z + q z))

/-- The potential of two nonnegative weight functions is nonnegative. -/
theorem potential_nonneg (p q : I → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z) :
    0 ≤ potential p q := by
  unfold potential
  refine Finset.sum_nonneg fun z _ => ?_
  exact div_nonneg (sq_nonneg _) (by linarith [hp z, hq z])

/-- The potential is symmetric in its two arguments. -/
theorem potential_comm (p q : I → ℝ) : potential p q = potential q p := by
  unfold potential
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [show q z - p z = -(p z - q z) by ring, show q z + p z = p z + q z by ring]
  ring

/-- The potential of a distribution with itself vanishes. -/
theorem potential_self (p : I → ℝ) : potential p p = 0 := by
  unfold potential
  simp

/-- **The complementary form of the potential.** For probability distributions
`∑_z p_z = ∑_z q_z = 1`, `1 − M(p,q) = ∑_z 2 p_z q_z / (p_z + q_z)`: pointwise this is
`(p − q)² / (2 (p + q)) = (p + q)/2 − 2 p q / (p + q)`. -/
theorem one_sub_potential (p q : I → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (hp1 : ∑ z, p z = 1) (hq1 : ∑ z, q z = 1) :
    1 - potential p q = ∑ z, 2 * (p z * q z) / (p z + q z) := by
  have hterm : ∀ z, (p z - q z) ^ 2 / (2 * (p z + q z))
      = (p z + q z) / 2 - 2 * (p z * q z) / (p z + q z) := by
    intro z
    by_cases h : p z + q z = 0
    · have hp0 : p z = 0 := by linarith [hp z, hq z]
      have hq0 : q z = 0 := by linarith [hp z, hq z]
      rw [hp0, hq0]
      norm_num
    · field_simp
      ring
  rw [potential, Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_sub_distrib]
  have hsum : ∑ z, (p z + q z) / 2 = 1 := by
    have h1 : ∑ z, (p z + q z) = 2 := by
      rw [Finset.sum_add_distrib, hp1, hq1]
      norm_num
    rw [← Finset.sum_div, h1]
    norm_num
  rw [hsum]
  ring

/-! ## §2 Cauchy–Schwarz: `TV² ≤ M` and the affinity bound -/

/-- **Weighted Cauchy–Schwarz for square roots.** For nonnegative `u, v` the squared sum
of `√(u_z v_z)` is at most the product of the sums. -/
theorem sq_sum_sqrt_mul_le (u v : I → ℝ) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z) :
    (∑ z, Real.sqrt (u z * v z)) ^ 2 ≤ (∑ z, u z) * (∑ z, v z) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun z => Real.sqrt (u z)) (fun z => Real.sqrt (v z))
  have hL : (∑ z, Real.sqrt (u z) * Real.sqrt (v z)) = ∑ z, Real.sqrt (u z * v z) :=
    Finset.sum_congr rfl fun z _ => (Real.sqrt_mul (hu z) (v z)).symm
  have hR : (∑ z, Real.sqrt (u z) ^ 2) = ∑ z, u z :=
    Finset.sum_congr rfl fun z _ => Real.sq_sqrt (hu z)
  have hR' : (∑ z, Real.sqrt (v z) ^ 2) = ∑ z, v z :=
    Finset.sum_congr rfl fun z _ => Real.sq_sqrt (hv z)
  rw [← hL, ← hR, ← hR']
  exact h

/-- **The total-variation bound of §3.** For probability distributions with
`∑_z (p_z + q_z) = 2`, the squared total variation distance `(½ ∑_z |p_z − q_z|)²` is at
most the potential `M(p,q)`; in particular `TV ≥ 1/3` forces `M ≥ 1/9`. -/
theorem tv_sq_le_potential (p q : I → ℝ) (hp : ∀ z, 0 ≤ p z) (hq : ∀ z, 0 ≤ q z)
    (hsum : ∑ z, (p z + q z) = 2) :
    ((∑ z, |p z - q z|) / 2) ^ 2 ≤ potential p q := by
  have hu : ∀ z, 0 ≤ (p z + q z) / 2 := fun z => by linarith [hp z, hq z]
  have hv : ∀ z, 0 ≤ (p z - q z) ^ 2 / (2 * (p z + q z)) := fun z =>
    div_nonneg (sq_nonneg _) (by linarith [hp z, hq z])
  have hcs := sq_sum_sqrt_mul_le (fun z => (p z + q z) / 2)
    (fun z => (p z - q z) ^ 2 / (2 * (p z + q z))) hu hv
  have hterm : ∀ z, ((p z + q z) / 2) * ((p z - q z) ^ 2 / (2 * (p z + q z)))
      = ((p z - q z) / 2) ^ 2 := by
    intro z
    by_cases h : p z + q z = 0
    · have hp0 : p z = 0 := by linarith [hp z, hq z]
      have hq0 : q z = 0 := by linarith [hp z, hq z]
      rw [hp0, hq0]
      norm_num
    · field_simp
  have hsq : (∑ z, Real.sqrt (((p z + q z) / 2) * ((p z - q z) ^ 2 / (2 * (p z + q z)))))
      = ∑ z, |p z - q z| / 2 := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hterm z, Real.sqrt_sq_eq_abs, abs_div]
    norm_num
  have hsum' : (∑ z, (p z + q z) / 2) = 1 := by
    rw [← Finset.sum_div, hsum]
    norm_num
  have hsplit : (∑ z, |p z - q z|) / 2 = ∑ z, |p z - q z| / 2 := Finset.sum_div ..
  calc ((∑ z, |p z - q z|) / 2) ^ 2
      = (∑ z, |p z - q z| / 2) ^ 2 := by rw [hsplit]
    _ = (∑ z, Real.sqrt (((p z + q z) / 2) * ((p z - q z) ^ 2 / (2 * (p z + q z))))) ^ 2 := by
        rw [← hsq]
    _ ≤ (∑ z, (p z + q z) / 2) * (∑ z, (p z - q z) ^ 2 / (2 * (p z + q z))) := hcs
    _ = potential p q := by rw [hsum', one_mul]; simp [potential]

/-- **Bounded error forces a constant potential.** If two transcript distributions are at
total variation distance at least `1/3` (the §3 consequence of error at most `1/3` and
`∑_z (p_z + q_z) = 2`), then `M(p,q) ≥ 1/9`. -/
theorem potential_ge_one_ninth_of_tv (p q : I → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hq : ∀ z, 0 ≤ q z) (hsum : ∑ z, (p z + q z) = 2)
    (htv : 1 / 3 ≤ (∑ z, |p z - q z|) / 2) : 1 / 9 ≤ potential p q := by
  have h := tv_sq_le_potential p q hp hq hsum
  nlinarith

/-- The square root of a product of Born probabilities is the product of the moduli of
the amplitudes. -/
theorem sqrt_born_mul (ψ0 ψ1 : QState I) (z : I) :
    Real.sqrt (BornProb ψ0 z * BornProb ψ1 z) = ‖ψ0 z‖ * ‖ψ1 z‖ := by
  rw [BornProb, BornProb, ← mul_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-- The modulus of the inner product is bounded by the sum of the products of the moduli
of the amplitudes (triangle inequality). -/
theorem inner_norm_le_sum_mul (ψ0 ψ1 : QState I) :
    ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ≤ ∑ z, ‖ψ0 z‖ * ‖ψ1 z‖ := by
  calc ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖
      ≤ ∑ z, ‖ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ := norm_sum_le _ _
    _ = ∑ z, ‖ψ0 z‖ * ‖ψ1 z‖ := by
        refine Finset.sum_congr rfl fun z _ => ?_
        simp

/-! ## §3 Born statistics of two states -/

/-- **The affinity bound.** For normalised states, the squared affinity
`(∑_z √(p_z q_z))²` of their Born distributions is at most `1 − M(p,q)`. -/
theorem sum_sqrt_born_sq_le_one_sub_potential (ψ0 ψ1 : QState I)
    (h0 : Normalized ψ0) (h1 : Normalized ψ1) :
    (∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z)) ^ 2
      ≤ 1 - potential (BornProb ψ0) (BornProb ψ1) := by
  have hp : ∀ z, 0 ≤ BornProb ψ0 z := fun z => bornProb_nonneg ψ0 z
  have hq : ∀ z, 0 ≤ BornProb ψ1 z := fun z => bornProb_nonneg ψ1 z
  have hp1 : ∑ z, BornProb ψ0 z = 1 := h0
  have hq1 : ∑ z, BornProb ψ1 z = 1 := h1
  have hu : ∀ z, 0 ≤ (BornProb ψ0 z + BornProb ψ1 z) / 2 := fun z => by
    linarith [hp z, hq z]
  have hv : ∀ z, 0 ≤ 2 * (BornProb ψ0 z * BornProb ψ1 z) / (BornProb ψ0 z + BornProb ψ1 z) :=
    fun z => div_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hp z) (hq z)))
      (by linarith [hp z, hq z])
  have hcs := sq_sum_sqrt_mul_le
    (fun z => (BornProb ψ0 z + BornProb ψ1 z) / 2)
    (fun z => 2 * (BornProb ψ0 z * BornProb ψ1 z) / (BornProb ψ0 z + BornProb ψ1 z)) hu hv
  have hterm : ∀ z, ((BornProb ψ0 z + BornProb ψ1 z) / 2)
      * (2 * (BornProb ψ0 z * BornProb ψ1 z) / (BornProb ψ0 z + BornProb ψ1 z))
      = BornProb ψ0 z * BornProb ψ1 z := by
    intro z
    by_cases h : BornProb ψ0 z + BornProb ψ1 z = 0
    · have h0z : BornProb ψ0 z = 0 := by linarith [hp z, hq z]
      have h1z : BornProb ψ1 z = 0 := by linarith [hp z, hq z]
      rw [h0z, h1z]
      norm_num
    · field_simp
  have hsq : (∑ z, Real.sqrt (((BornProb ψ0 z + BornProb ψ1 z) / 2)
        * (2 * (BornProb ψ0 z * BornProb ψ1 z) / (BornProb ψ0 z + BornProb ψ1 z))))
      = ∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hterm z]
  have hsum : (∑ z, (BornProb ψ0 z + BornProb ψ1 z) / 2) = 1 := by
    have h1 : ∑ z, (BornProb ψ0 z + BornProb ψ1 z) = 2 := by
      rw [Finset.sum_add_distrib, hp1, hq1]
      norm_num
    rw [← Finset.sum_div, h1]
    norm_num
  have hone : 1 - potential (BornProb ψ0) (BornProb ψ1)
      = ∑ z, 2 * (BornProb ψ0 z * BornProb ψ1 z) / (BornProb ψ0 z + BornProb ψ1 z) :=
    one_sub_potential _ _ hp hq hp1 hq1
  rw [hsq, hsum, one_mul, ← hone] at hcs
  exact hcs

/-- **The potential against the overlap.** For normalised states, the squared modulus of
the inner product `∑_z ψ₀(z) conj ψ₁(z)` plus the potential is at most `1`. -/
theorem inner_norm_sq_le_one_sub_potential (ψ0 ψ1 : QState I)
    (h0 : Normalized ψ0) (h1 : Normalized ψ1) :
    ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2
      ≤ 1 - potential (BornProb ψ0) (BornProb ψ1) := by
  have hin := inner_norm_le_sum_mul ψ0 ψ1
  have hnn : 0 ≤ ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ := norm_nonneg _
  have hsum : 0 ≤ ∑ z, ‖ψ0 z‖ * ‖ψ1 z‖ :=
    Finset.sum_nonneg fun z _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsquare : (∑ z, ‖ψ0 z‖ * ‖ψ1 z‖) ^ 2
      = (∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z)) ^ 2 := by
    rw [← Finset.sum_congr rfl fun z _ => sqrt_born_mul ψ0 ψ1 z]
  have hsq_le : ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2
      ≤ (∑ z, ‖ψ0 z‖ * ‖ψ1 z‖) ^ 2 := pow_le_pow_left₀ hnn hin 2
  calc ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2
      ≤ (∑ z, ‖ψ0 z‖ * ‖ψ1 z‖) ^ 2 := hsq_le
    _ = (∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z)) ^ 2 := hsquare
    _ ≤ 1 - potential (BornProb ψ0) (BornProb ψ1) :=
        sum_sqrt_born_sq_le_one_sub_potential ψ0 ψ1 h0 h1

/-- **The squared distance formula.** For normalised amplitude vectors,
`‖|ψ₀⟩ − |ψ₁⟩‖² = ∑_z ‖ψ₀(z) − ψ₁(z)‖² = 2 − 2 Re ∑_z ψ₀(z) conj ψ₁(z)`. -/
theorem norm_sub_sq_toEuclidean (ψ0 ψ1 : QState I) (h0 : Normalized ψ0)
    (h1 : Normalized ψ1) :
    ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2
      = 2 - 2 * (∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)).re := by
  have hpt : ∀ z, ‖ψ0 z - ψ1 z‖ ^ 2
      = ‖ψ0 z‖ ^ 2 + ‖ψ1 z‖ ^ 2 - 2 * (ψ0 z * (starRingEnd ℂ) (ψ1 z)).re := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  have htransport : toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1
      = toEuclidean_fromVec (ψ0 - ψ1) := rfl
  rw [htransport, norm_toEuclidean_fromVec_sq]
  simp only [Pi.sub_apply]
  rw [Finset.sum_congr rfl fun z _ => hpt z]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hs : ∑ z, 2 * (ψ0 z * (starRingEnd ℂ) (ψ1 z)).re
      = 2 * (∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)).re := by
    rw [Complex.re_sum, ← Finset.mul_sum]
  rw [hs, h0, h1]
  ring

/-- **The distance against the overlap.** For normalised states,
`1 − ‖|ψ₀⟩ − |ψ₁⟩‖² ≤ |⟨ψ₀|ψ₁⟩|²`: the squared distance is `2 − 2 Re⟨ψ₀|ψ₁⟩` and
`(1 − |⟨ψ₀|ψ₁⟩|)² ≥ 0` upgrades `2 − 2 |⟨ψ₀|ψ₁⟩|` to `1 − |⟨ψ₀|ψ₁⟩|²`. -/
theorem one_sub_state_distance_sq_le_inner_norm_sq (ψ0 ψ1 : QState I)
    (h0 : Normalized ψ0) (h1 : Normalized ψ1) :
    1 - ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2
      ≤ ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2 := by
  have hnorm := norm_sub_sq_toEuclidean ψ0 ψ1 h0 h1
  set c := ∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z) with hc
  have hnorm' : ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 = 2 - 2 * c.re := by
    rw [hnorm, hc]
  have hre : c.re ≤ ‖c‖ := Complex.re_le_norm c
  have hsq : 0 ≤ (1 - ‖c‖) ^ 2 := sq_nonneg _
  have hquad : 2 * ‖c‖ - 1 ≤ ‖c‖ ^ 2 := by nlinarith [hsq]
  rw [hnorm']
  calc 1 - (2 - 2 * c.re) = 2 * c.re - 1 := by ring
    _ ≤ 2 * ‖c‖ - 1 := by linarith
    _ ≤ ‖c‖ ^ 2 := hquad

/-- **The potential is dominated by the squared state distance.** For normalised states,
`M(p,q) ≤ ‖|ψ₀⟩ − |ψ₁⟩‖²` where `p, q` are their Born distributions: the last step of the
proof of Lemma 1. -/
theorem potential_le_state_distance_sq (ψ0 ψ1 : QState I)
    (h0 : Normalized ψ0) (h1 : Normalized ψ1) :
    potential (BornProb ψ0) (BornProb ψ1)
      ≤ ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 := by
  have hinner := inner_norm_sq_le_one_sub_potential ψ0 ψ1 h0 h1
  have hdist := one_sub_state_distance_sq_le_inner_norm_sq ψ0 ψ1 h0 h1
  linarith

/-! ## §4 The one-block progress inequality (Lemma 1) -/

/-- **Conditional one-block progress `M_{t+1}(h)` of §3.** Given the posterior weight `a`
of `U₀` after the history `h` and the Born distributions `r`, `s` of the next block's
measurement outcome under `U₀` and `U₁`, the conditional progress is
`∑_z (a r_z − (1 − a) s_z)² / (a r_z + (1 − a) s_z)`. -/
noncomputable def conditionalProgress (a : ℝ) (r s : I → ℝ) : ℝ :=
  ∑ z, (a * r z - (1 - a) * s z) ^ 2 / (a * r z + (1 - a) * s z)

/-- **The complementary conditional progress.** `1 − M_{t+1}(h)` equals
`4 a (1 − a) ∑_z r_z s_z / w_z` with the mixture weights `w_z = a r_z + (1 − a) s_z`, the
identity that the proof of Lemma 1 uses. -/
theorem one_sub_conditionalProgress (a : ℝ) (r s : I → ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hr : ∀ z, 0 ≤ r z) (hs : ∀ z, 0 ≤ s z)
    (hr1 : ∑ z, r z = 1) (hs1 : ∑ z, s z = 1) :
    1 - conditionalProgress a r s
      = 4 * a * (1 - a) * ∑ z, r z * s z / (a * r z + (1 - a) * s z) := by
  have hterm : ∀ z, (a * r z - (1 - a) * s z) ^ 2 / (a * r z + (1 - a) * s z)
      = (a * r z + (1 - a) * s z)
        - 4 * a * (1 - a) * (r z * s z) / (a * r z + (1 - a) * s z) := by
    intro z
    by_cases h : a * r z + (1 - a) * s z = 0
    · have hX : 0 ≤ a * r z := mul_nonneg ha0 (hr z)
      have hY : 0 ≤ (1 - a) * s z := mul_nonneg (by linarith) (hs z)
      have hX0 : a * r z = 0 := by linarith
      have hY0 : (1 - a) * s z = 0 := by linarith
      rw [hX0, hY0]
      norm_num
    · field_simp
      ring
  rw [conditionalProgress, Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_sub_distrib]
  have hsum : ∑ z, (a * r z + (1 - a) * s z) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr1, hs1]
    ring
  rw [hsum, Finset.mul_sum]
  ring_nf

/-- **The affinity against the mixture reciprocal.** For probability distributions `r, s`
and a posterior weight `a ∈ [0,1]`, the squared affinity is at most
`∑_z r_z s_z / (a r_z + (1 − a) s_z)`, the weighted Cauchy–Schwarz step of the proof of
Lemma 1. -/
theorem affinity_sq_le_mixture_sum (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r s : I → ℝ)
    (hr : ∀ z, 0 ≤ r z) (hs : ∀ z, 0 ≤ s z)
    (hr1 : ∑ z, r z = 1) (hs1 : ∑ z, s z = 1) :
    (∑ z, Real.sqrt (r z * s z)) ^ 2
      ≤ ∑ z, r z * s z / (a * r z + (1 - a) * s z) := by
  have hu : ∀ z, 0 ≤ a * r z + (1 - a) * s z := fun z =>
    add_nonneg (mul_nonneg ha0 (hr z)) (mul_nonneg (by linarith) (hs z))
  have hv : ∀ z, 0 ≤ r z * s z / (a * r z + (1 - a) * s z) := fun z =>
    div_nonneg (mul_nonneg (hr z) (hs z)) (hu z)
  have hcs := sq_sum_sqrt_mul_le (fun z => a * r z + (1 - a) * s z)
    (fun z => r z * s z / (a * r z + (1 - a) * s z)) hu hv
  have hterm : ∀ z, Real.sqrt ((a * r z + (1 - a) * s z)
      * (r z * s z / (a * r z + (1 - a) * s z))) = Real.sqrt (r z * s z) := by
    intro z
    by_cases h : a * r z + (1 - a) * s z = 0
    · have hX : a * r z = 0 := by
        have hX0 : 0 ≤ a * r z := mul_nonneg ha0 (hr z)
        have hY0 : 0 ≤ (1 - a) * s z := mul_nonneg (by linarith) (hs z)
        linarith
      have hY : (1 - a) * s z = 0 := by
        have hX0 : 0 ≤ a * r z := mul_nonneg ha0 (hr z)
        have hY0 : 0 ≤ (1 - a) * s z := mul_nonneg (by linarith) (hs z)
        linarith
      have hrs : r z * s z = 0 := by
        by_cases ha : a = 0
        · have hs0 : s z = 0 := by
            have hY' := hY
            rw [ha, sub_zero, one_mul] at hY'
            exact hY'
          rw [hs0, mul_zero]
        · have hr0 : r z = 0 := by
            rcases mul_eq_zero.mp hX with h | h
            · exact absurd h ha
            · exact h
          rw [hr0, zero_mul]
      rw [hrs]
      simp
    · field_simp
  have hsq : (∑ z, Real.sqrt ((a * r z + (1 - a) * s z)
        * (r z * s z / (a * r z + (1 - a) * s z))))
      = ∑ z, Real.sqrt (r z * s z) := Finset.sum_congr rfl fun z _ => hterm z
  have hsum : ∑ z, (a * r z + (1 - a) * s z) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hr1, hs1]
    ring
  rw [hsq, hsum, one_mul] at hcs
  exact hcs

/-- **Lemma 1 of §3 (one-block progress inequality).** Let `h` be a history whose
posterior weight for `U₀` is `a ∈ [0,1]`, and let `|ψ₀⟩`, `|ψ₁⟩` be the normalised states
immediately before the block's final measurement under the two oracles.  Then the
increment of the conditional progress is bounded by
`M_{t+1}(h) − M_t(h) ≤ (1 − M_t(h)) ‖|ψ₀⟩ − |ψ₁⟩‖²`, where `M_t(h) = (2a − 1)²`. -/
theorem one_block_progress_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ψ0 ψ1 : QState I) (h0 : Normalized ψ0) (h1 : Normalized ψ1) :
    conditionalProgress a (BornProb ψ0) (BornProb ψ1) - (2 * a - 1) ^ 2
      ≤ (1 - (2 * a - 1) ^ 2)
        * ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 := by
  have hp : ∀ z, 0 ≤ BornProb ψ0 z := fun z => bornProb_nonneg ψ0 z
  have hq : ∀ z, 0 ≤ BornProb ψ1 z := fun z => bornProb_nonneg ψ1 z
  have hp1 : ∑ z, BornProb ψ0 z = 1 := h0
  have hq1 : ∑ z, BornProb ψ1 z = 1 := h1
  have hcomp := one_sub_conditionalProgress a (BornProb ψ0) (BornProb ψ1)
    ha0 ha1 hp hq hp1 hq1
  have haff := affinity_sq_le_mixture_sum a ha0 ha1 (BornProb ψ0) (BornProb ψ1)
    hp hq hp1 hq1
  have hinner := inner_norm_sq_le_one_sub_potential ψ0 ψ1 h0 h1
  have hdist := one_sub_state_distance_sq_le_inner_norm_sq ψ0 ψ1 h0 h1
  set d2 := ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 with hd2
  set A := ∑ z, BornProb ψ0 z * BornProb ψ1 z / (a * BornProb ψ0 z + (1 - a) * BornProb ψ1 z)
    with hA
  have hgeom : 1 - (2 * a - 1) ^ 2 = 4 * a * (1 - a) := by ring
  have hnonneg : 0 ≤ 4 * a * (1 - a) := by
    have : 0 ≤ 1 - a := by linarith
    positivity
  have hA_ge : 1 - d2 ≤ A := by
    have h1 : 1 - d2 ≤ ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2 := hdist
    have h2 : (∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z)) ^ 2 ≤ A := haff
    have h3 : ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2
        ≤ (∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z)) ^ 2 := by
      have hin := inner_norm_le_sum_mul ψ0 ψ1
      have hnn : 0 ≤ ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ := norm_nonneg _
      have hsquare : (∑ z, ‖ψ0 z‖ * ‖ψ1 z‖) ^ 2
          = (∑ z, Real.sqrt (BornProb ψ0 z * BornProb ψ1 z)) ^ 2 := by
        rw [← Finset.sum_congr rfl fun z _ => sqrt_born_mul ψ0 ψ1 z]
      rw [← hsquare]
      exact pow_le_pow_left₀ hnn hin 2
    linarith
  calc conditionalProgress a (BornProb ψ0) (BornProb ψ1) - (2 * a - 1) ^ 2
      = 1 - (2 * a - 1) ^ 2 - (1 - conditionalProgress a (BornProb ψ0) (BornProb ψ1)) := by
        ring
    _ = 4 * a * (1 - a) - 4 * a * (1 - a) * A := by rw [hcomp, hgeom]
    _ ≤ 4 * a * (1 - a) - 4 * a * (1 - a) * (1 - d2) := by nlinarith
    _ = (1 - (2 * a - 1) ^ 2) * d2 := by rw [hgeom]; ring

/-- **Lemma 1 with a query-distance budget.** If the two pre-measurement states are within
`r ε` in Hilbert distance (Lemma 2 applied inside the block), the one-block increment is at
most `(r ε)²`, which is the form consumed by the proof of Theorem 1. -/
theorem one_block_progress_le_query (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ψ0 ψ1 : QState I) (h0 : Normalized ψ0) (h1 : Normalized ψ1) (r ε : ℝ)
    (hε : 0 ≤ ε) (hr : 0 ≤ r)
    (hclose : ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ≤ r * ε) :
    conditionalProgress a (BornProb ψ0) (BornProb ψ1) - (2 * a - 1) ^ 2 ≤ (r * ε) ^ 2 := by
  have hmain := one_block_progress_le a ha0 ha1 ψ0 ψ1 h0 h1
  have hd2 : ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 ≤ (r * ε) ^ 2 := by
    have hnn : 0 ≤ ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ := norm_nonneg _
    have hrm : 0 ≤ r * ε := mul_nonneg hr hε
    nlinarith
  have hcoef_le_one : 1 - (2 * a - 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (2 * a - 1)]
  have hcoef_nn : 0 ≤ 1 - (2 * a - 1) ^ 2 := by
    have h1 : 2 * a - 1 ≤ 1 := by linarith
    have h2 : -1 ≤ 2 * a - 1 := by linarith
    nlinarith [sq_nonneg (2 * a - 1)]
  have hd2nn : 0 ≤ ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 := by positivity
  have hstep := mul_le_mul hcoef_le_one hd2 hd2nn zero_le_one
  rw [one_mul] at hstep
  linarith

end Qatlib.Papers.HybridQuery26.QueryModel
