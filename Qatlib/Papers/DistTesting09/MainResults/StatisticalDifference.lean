/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistTesting09.MainResults.Defs
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.DistTesting09.MainResults.Defs
set_option warningAsError false

namespace Qatlib.Papers.DistTesting09.MainResults.StatisticalDifference

variable {N : ℕ}

def midpoint (p q : Dist N) : Dist N where
  prob i := (p.prob i + q.prob i) / 2
  nonneg i := by
    have hp := p.nonneg i
    have hq := q.nonneg i
    linarith
  sum_one := by
    calc ∑ i, (p.prob i + q.prob i) / 2
        = ∑ i, ((p.prob i + q.prob i) * (1 / 2)) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, (p.prob i + q.prob i)) * (1 / 2) := by rw [Finset.sum_mul]
      _ = (∑ i, p.prob i + ∑ i, q.prob i) * (1 / 2) := by rw [Finset.sum_add_distrib]
      _ = (1 + 1) * (1 / 2) := by rw [p.sum_one, q.sum_one]
      _ = 1 := by norm_num

@[simp] theorem midpoint_prob (p q : Dist N) (i : Fin N) :
    (midpoint p q).prob i = (p.prob i + q.prob i) / 2 := rfl

def xRatio (p q : Dist N) (i : Fin N) : ℝ :=
  if p.prob i + q.prob i = 0 then 0 else |p.prob i - q.prob i| / (p.prob i + q.prob i)

theorem xRatio_nonneg (p q : Dist N) (i : Fin N) : 0 ≤ xRatio p q i := by
  unfold xRatio
  split_ifs with h
  · norm_num
  · exact div_nonneg (abs_nonneg _) (by linarith [p.nonneg i, q.nonneg i])

theorem xRatio_le_one (p q : Dist N) (i : Fin N) : xRatio p q i ≤ 1 := by
  unfold xRatio
  split_ifs with h
  · norm_num
  · have hp := p.nonneg i
    have hq := q.nonneg i
    have hpq : 0 < p.prob i + q.prob i :=
      lt_of_le_of_ne (by linarith) (Ne.symm h)
    rw [div_le_one hpq, abs_le]
    constructor <;> linarith

theorem midpoint_expect_xRatio (p q : Dist N) :
    (midpoint p q).expect (fun i => xRatio p q i) = (1 / 2) * l1 p q := by
  rw [l1]
  have hterm : ∀ i : Fin N,
      (midpoint p q).prob i * xRatio p q i = (1 / 2) * |p.prob i - q.prob i| := by
    intro i
    have hp := p.nonneg i
    have hq := q.nonneg i
    unfold xRatio
    by_cases h : p.prob i + q.prob i = 0
    · have hp0 : p.prob i = 0 := by linarith
      have hq0 : q.prob i = 0 := by linarith
      simp [midpoint_prob, hp0, hq0]
    · rw [midpoint_prob, if_neg h]
      field_simp
  calc (midpoint p q).expect (fun i => xRatio p q i)
      = ∑ i, (1 / 2) * |p.prob i - q.prob i| := by
        simp only [FinDist.expect]
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = (1 / 2) * ∑ i, |p.prob i - q.prob i| := by rw [Finset.mul_sum]

theorem l1_le_two (p q : Dist N) : l1 p q ≤ 2 := by
  unfold l1
  have hterm : ∀ i : Fin N, |p.prob i - q.prob i| ≤ p.prob i + q.prob i := by
    intro i
    have hp := p.nonneg i
    have hq := q.nonneg i
    rw [abs_le]
    constructor <;> linarith
  calc ∑ i, |p.prob i - q.prob i| ≤ ∑ i, (p.prob i + q.prob i) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = 2 := by
        rw [Finset.sum_add_distrib, p.sum_one, q.sum_one]
        norm_num

theorem midpoint_variance_xRatio_le (p q : Dist N) :
    (midpoint p q).variance (fun i => xRatio p q i) ≤ 1 := by
  rw [FinDist.variance_eq_expect_sq_sub]
  have hsq_le : (midpoint p q).expect (fun i => (xRatio p q i) ^ 2)
      ≤ (midpoint p q).expect (fun i => xRatio p q i) := by
    simp only [FinDist.expect]
    exact Finset.sum_le_sum fun i _ => by
      have h0 := xRatio_nonneg p q i
      have h1 := xRatio_le_one p q i
      exact mul_le_mul_of_nonneg_left (by nlinarith) ((midpoint p q).nonneg i)
  have hmean : (midpoint p q).expect (fun i => xRatio p q i) ≤ 1 := by
    rw [midpoint_expect_xRatio]
    have := l1_le_two p q
    linarith
  nlinarith [le_trans hsq_le hmean,
    sq_nonneg ((midpoint p q).expect (fun i => xRatio p q i))]

def xBar (p q : Dist N) {n : ℕ} (S : Fin n → Fin N) : ℝ :=
  (1 / (n : ℝ)) * ∑ a, xRatio p q (S a)

theorem lemma1_mean_concentration [NeZero N] (p q : Dist N) (ε τ : ℝ)
    (hε : 0 < ε) (hτ : 0 < τ) (n : ℕ) (hn : 0 < n)
    (hnbig : 27 / (τ * ε ^ 2) ≤ (n : ℝ)) :
    (midpoint p q).probEvent (L := n) (fun S => ε / 3 ≤ |xBar p q S - (1 / 2) * l1 p q|)
      ≤ τ / 3 := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := hnpos.ne'
  have ht : 0 < ε / 3 := by linarith
  have hfun : (fun S : Fin n → Fin N => xBar p q S)
      = weightedSum (fun _ : Fin n => (1 / (n : ℝ))) (fun _ (i : Fin N) => xRatio p q i) := by
    funext S
    simp only [xBar, weightedSum, Finset.mul_sum]
  have hexp : (independent (fun _ : Fin n => midpoint p q)).expect (fun S => xBar p q S)
      = (1 / 2) * l1 p q := by
    rw [hfun,
      Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    have hsum : (∑ a : Fin n,
          (1 / (n : ℝ)) * ((fun _ : Fin n => midpoint p q) a).expect
            ((fun _ (i : Fin N) => xRatio p q i) a))
        = (1 / 2) * l1 p q := by
      have hc : ∀ a : Fin n,
          (1 / (n : ℝ)) * ((fun _ : Fin n => midpoint p q) a).expect
            ((fun _ (i : Fin N) => xRatio p q i) a)
            = (1 / (n : ℝ)) * ((1 / 2) * l1 p q) := by
        intro a
        show (1 / (n : ℝ)) * (midpoint p q).expect (fun i => xRatio p q i)
            = (1 / (n : ℝ)) * ((1 / 2) * l1 p q)
        rw [midpoint_expect_xRatio]
      calc (∑ a : Fin n,
            (1 / (n : ℝ)) * ((fun _ : Fin n => midpoint p q) a).expect
              ((fun _ (i : Fin N) => xRatio p q i) a))
          = ∑ _a : Fin n, (1 / (n : ℝ)) * ((1 / 2) * l1 p q) :=
            Finset.sum_congr rfl fun a _ => hc a
        _ = (1 / 2) * l1 p q := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp [hne]
    exact hsum
  have hvar : (independent (fun _ : Fin n => midpoint p q)).variance (fun S => xBar p q S)
      ≤ 1 / (n : ℝ) := by
    rw [hfun,
      Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_variance]
    have hb : ∀ a : Fin n, (midpoint p q).variance (fun i => xRatio p q i) ≤ 1 :=
      fun _ => midpoint_variance_xRatio_le p q
    calc (∑ a : Fin n, (1 / (n : ℝ)) ^ 2
          * (midpoint p q).variance (fun i => xRatio p q i))
        ≤ ∑ _a : Fin n, (1 / (n : ℝ)) ^ 2 * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hb a) (by positivity)
      _ = 1 / (n : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
            mul_one]
          field_simp [hne]
  have hcheb := chebyshev (independent (fun _ : Fin n => midpoint p q))
    (fun S => xBar p q S) (ε / 3) ht
  rw [hexp] at hcheb
  have hkey : 27 ≤ (n : ℝ) * τ * ε ^ 2 := by
    have h := hnbig
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < τ * ε ^ 2)] at h
    linarith
  have hcheb' : eventMass (independent (fun _ : Fin n => midpoint p q))
      (fun S => ε / 3 ≤ |xBar p q S - (1 / 2) * l1 p q|) ≤ τ / 3 := by
    calc eventMass (independent (fun _ : Fin n => midpoint p q))
          (fun S => ε / 3 ≤ |xBar p q S - (1 / 2) * l1 p q|)
        ≤ ((independent (fun _ : Fin n => midpoint p q)).variance (fun S => xBar p q S))
            / (ε / 3) ^ 2 := hcheb
      _ ≤ (1 / (n : ℝ)) / (ε / 3) ^ 2 :=
          div_le_div_of_nonneg_right hvar (by positivity)
      _ ≤ τ / 3 := by
          have h1 : (1 / (n : ℝ)) / (ε / 3) ^ 2 = 9 / ((n : ℝ) * ε ^ 2) := by
            field_simp [hne, hε.ne']
            ring
          rw [h1, div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * ε ^ 2)]
          nlinarith
  have hgoal : eventMass (independent (fun _ : Fin n => midpoint p q))
      (fun S : Fin n → Fin N => ε / 3 ≤ |xBar p q S - (1 / 2) * l1 p q|) ≤ τ / 3 := hcheb'
  rwa [eventMass_independent_const] at hgoal

theorem lemma1_estdist [NeZero N] (p q : Dist N) (ε τ : ℝ) (hε : 0 < ε) (hτ : 0 < τ)
    (n : ℕ) (hn : 0 < n) (hnbig : 27 / (τ * ε ^ 2) ≤ (n : ℝ))
    (xhat : (Fin n → Fin N) → ℝ)
    (hclose : ∀ S, |xhat S - xBar p q S| ≤ ε / 3) :
    1 - τ ≤ (midpoint p q).probEvent (L := n)
      (fun S => |xhat S - (1 / 2) * l1 p q| < ε) := by
  classical
  have hbad := lemma1_mean_concentration p q ε τ hε hτ n hn hnbig
  have hsub : ∀ S : Fin n → Fin N,
      ¬ (|xhat S - (1 / 2) * l1 p q| < ε) →
        ε / 3 ≤ |xBar p q S - (1 / 2) * l1 p q| := by
    intro S hS
    have h1 : ε ≤ |xhat S - (1 / 2) * l1 p q| := not_lt.mp hS
    have h2 := hclose S
    have h3 := abs_add_le (xhat S - xBar p q S) (xBar p q S - (1 / 2) * l1 p q)
    have h4 : (xhat S - xBar p q S) + (xBar p q S - (1 / 2) * l1 p q)
        = xhat S - (1 / 2) * l1 p q := by ring
    rw [h4] at h3
    linarith
  have hle : (midpoint p q).probEvent (L := n)
      (fun S => ¬ (|xhat S - (1 / 2) * l1 p q| < ε)) ≤ τ / 3 :=
    le_trans (probEvent_mono (midpoint p q) _ _ hsub) hbad
  have hcompl := probEvent_compl (M := n) (midpoint p q)
    (fun S => |xhat S - (1 / 2) * l1 p q| < ε)
  linarith

theorem prop1_ratio_lipschitz (p q pt qt δ : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 5)
    (hp' : |pt - p| ≤ δ * p) (hq' : |qt - q| ≤ δ * q)
    (hs : 0 < p + q) (hs' : 0 < pt + qt) :
    |(p - q) / (p + q) - (pt - qt) / (pt + qt)| ≤ 5 * δ := by
  have hpq0 : (0 : ℝ) ≤ p + q := le_of_lt hs
  have hδ1 : δ < 1 := by linarith
  have ha : 0 ≤ δ * p := mul_nonneg hδ0 hp
  have hb : 0 ≤ δ * q := mul_nonneg hδ0 hq

  have hAabs : |p - q| ≤ p + q := by
    rw [abs_le]
    constructor <;> linarith

  have hrs : |(pt + qt) - (p + q)| ≤ δ * (p + q) := by
    have he : (pt + qt) - (p + q) = (pt - p) + (qt - q) := by ring
    rw [he]
    calc |(pt - p) + (qt - q)| ≤ |pt - p| + |qt - q| := abs_add_le _ _
      _ ≤ δ * p + δ * q := add_le_add hp' hq'
      _ = δ * (p + q) := by ring

  have hAA : |(pt - qt) - (p - q)| ≤ δ * (p + q) := by
    have he : (pt - qt) - (p - q) = (pt - p) - (qt - q) := by ring
    rw [he]
    have h1 : |(pt - p) - (qt - q)| ≤ |pt - p| + |qt - q| := by
      have h := abs_add_le (pt - p) (-(qt - q))
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using! h
    calc |(pt - p) - (qt - q)| ≤ |pt - p| + |qt - q| := h1
      _ ≤ δ * p + δ * q := add_le_add hp' hq'
      _ = δ * (p + q) := by ring

  have hnum : |(p - q) * (pt + qt) - (pt - qt) * (p + q)| ≤ 2 * δ * (p + q) ^ 2 := by
    have he : (p - q) * (pt + qt) - (pt - qt) * (p + q)
        = (p - q) * ((pt + qt) - (p + q)) - ((pt - qt) - (p - q)) * (p + q) := by ring
    rw [he]
    have h1 : |(p - q) * ((pt + qt) - (p + q))| ≤ (p + q) * (δ * (p + q)) := by
      rw [abs_mul]
      exact mul_le_mul hAabs hrs (abs_nonneg _) hpq0
    have h2 : |((pt - qt) - (p - q)) * (p + q)| ≤ (δ * (p + q)) * (p + q) := by
      rw [abs_mul, abs_of_nonneg hpq0]
      exact mul_le_mul hAA (le_refl _) hpq0 (mul_nonneg hδ0 hpq0)
    have hsplit : |(p - q) * ((pt + qt) - (p + q)) - ((pt - qt) - (p - q)) * (p + q)|
        ≤ |(p - q) * ((pt + qt) - (p + q))| + |((pt - qt) - (p - q)) * (p + q)| := by
      have h := abs_add_le ((p - q) * ((pt + qt) - (p + q)))
        (-(((pt - qt) - (p - q)) * (p + q)))
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using! h
    calc |(p - q) * ((pt + qt) - (p + q)) - ((pt - qt) - (p - q)) * (p + q)|
        ≤ |(p - q) * ((pt + qt) - (p + q))| + |((pt - qt) - (p - q)) * (p + q)| := hsplit
      _ ≤ (p + q) * (δ * (p + q)) + (δ * (p + q)) * (p + q) := add_le_add h1 h2
      _ = 2 * δ * (p + q) ^ 2 := by ring

  have hrlb : (1 - δ) * (p + q) ≤ pt + qt := by
    have h := (abs_le.mp hrs).1
    nlinarith

  have hden : 0 < (p + q) * (pt + qt) := mul_pos hs hs'
  have h2δ : 2 * δ * (p + q) ^ 2 ≤ 5 * δ * ((p + q) * (pt + qt)) := by
    have hfac : 0 ≤ δ * (3 - 5 * δ) * (p + q) ^ 2 := by
      apply mul_nonneg
      · apply mul_nonneg hδ0
        linarith
      · exact sq_nonneg _
    have hstep : 2 * δ * (p + q) ^ 2 ≤ 5 * δ * ((1 - δ) * (p + q) ^ 2) := by
      nlinarith
    have hstep2 : 5 * δ * ((1 - δ) * (p + q) ^ 2) ≤ 5 * δ * ((p + q) * (pt + qt)) := by
      have he : (1 - δ) * (p + q) ^ 2 = (p + q) * ((1 - δ) * (p + q)) := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrlb hpq0)
        (by linarith)
    linarith
  calc |(p - q) / (p + q) - (pt - qt) / (pt + qt)|
      = |(p - q) * (pt + qt) - (pt - qt) * (p + q)| / ((p + q) * (pt + qt)) := by
        rw [div_sub_div _ _ hs.ne' hs'.ne', abs_div, abs_of_pos hden,
          show (p - q) * (pt + qt) - (p + q) * (pt - qt)
            = (p - q) * (pt + qt) - (pt - qt) * (p + q) by ring]
    _ ≤ (2 * δ * (p + q) ^ 2) / ((p + q) * (pt + qt)) :=
        div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (5 * δ * ((p + q) * (pt + qt))) / ((p + q) * (pt + qt)) :=
        div_le_div_of_nonneg_right h2δ hden.le
    _ = 5 * δ := by
        field_simp

def estProbEst {M : ℕ} (A : Finset (Fin N)) (S : Fin M → Fin N) : ℝ :=
  (∑ a, if S a ∈ A then (1 : ℝ) else 0) / (M : ℝ)

theorem theorem5_estprob [NeZero N] (p : Dist N) (A : Finset (Fin N))
    (M : ℕ) (hM : 0 < M) (δ ω : ℝ) (hδ : 0 < δ) (hω : 0 < ω)
    (hMbound : (∑ x ∈ A, p.prob x) / (ω * δ ^ 2) ≤ (M : ℝ)) :
    1 - ω ≤ p.probEvent (L := M)
      (fun S => |estProbEst (M := M) A S - ∑ x ∈ A, p.prob x| ≤ δ) := by
  classical
  set μ : ℝ := ∑ x ∈ A, p.prob x with hμ
  let f : Fin N → ℝ := fun x => if x ∈ A then (1 : ℝ) else 0
  have hfexp : p.expect f = μ := by
    rw [hμ]
    simpa [f] using! (expect_indicator p A)
  have hvar : p.variance f ≤ μ := by
    rw [hμ]
    simpa [f] using! (indicator_variance_le p A)
  have hcheb := p.chebyshev_avg f hM δ hδ
  have hcheb' : p.probEvent (L := M) (fun S => δ < |estProbEst (M := M) A S - μ|)
      ≤ p.variance f / ((M : ℝ) * δ ^ 2) := by
    simpa [estProbEst, FinDist.avg, f, hfexp] using! hcheb
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hden : (0 : ℝ) < (M : ℝ) * δ ^ 2 := mul_pos hMpos hδ2
  have hωδ : (0 : ℝ) < ω * δ ^ 2 := mul_pos hω hδ2
  have h1 : μ ≤ (M : ℝ) * (ω * δ ^ 2) := (div_le_iff₀ hωδ).mp hMbound
  have h2 : μ / ((M : ℝ) * δ ^ 2) ≤ ω := by
    rw [div_le_iff₀ hden]
    nlinarith [h1]
  have htail : p.probEvent (L := M)
      (fun S => δ < |estProbEst (M := M) A S - μ|) ≤ ω :=
    le_trans hcheb' (le_trans (div_le_div_of_nonneg_right hvar hden.le) h2)
  have hcompl := probEvent_compl (M := M) p
    (fun S => |estProbEst (M := M) A S - μ| ≤ δ)
  have heq : p.probEvent (L := M)
        (fun S => ¬ |estProbEst (M := M) A S - μ| ≤ δ)
      = p.probEvent (L := M) (fun S => δ < |estProbEst (M := M) A S - μ|) := by
    apply le_antisymm
    · apply probEvent_mono
      intro S hS
      exact not_le.mp hS
    · apply probEvent_mono
      intro S hS
      exact not_le.mpr hS
  rw [heq] at hcompl
  linarith [hcompl, htail]

theorem theorem1_statistical_difference [NeZero N] (ε τ : ℝ) (hε : 0 < ε) (hτ : 0 < τ) :
    ∃ (n Mq : ℝ), 0 < n ∧ 27 / (τ * ε ^ 2) ≤ n ∧ 0 < Mq ∧
      Real.sqrt (N : ℝ) / (ε ^ 6 * τ ^ 4) ≤ Mq ∧
      2 * n * Mq ≤ 64 * Real.sqrt (N : ℝ) / (τ ^ 5 * ε ^ 8) := by
  have hN : (0 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hτ5 : (0 : ℝ) < τ ^ 5 := by positivity
  have hε8 : (0 : ℝ) < ε ^ 8 := by positivity
  have hε6 : (0 : ℝ) < ε ^ 6 := by positivity
  have hε4 : (0 : ℝ) < ε ^ 4 := by positivity
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hτε : (0 : ℝ) < τ * ε ^ 2 := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  refine ⟨27 / (τ * ε ^ 2), Real.sqrt (N : ℝ) / (ε ^ 6 * τ ^ 4),
    div_pos (by norm_num) (by positivity), le_refl _,
    div_pos hsqrt (by positivity), le_refl _, ?_⟩
  have hcalc : 2 * (27 / (τ * ε ^ 2)) * (Real.sqrt (N : ℝ) / (ε ^ 6 * τ ^ 4))
      = 54 * Real.sqrt (N : ℝ) / (τ ^ 5 * ε ^ 8) := by
    field_simp [hτ.ne', hε.ne']
    ring
  rw [hcalc]
  exact div_le_div_of_nonneg_right (by nlinarith [hN]) (by positivity)

end Qatlib.Papers.DistTesting09.MainResults.StatisticalDifference
