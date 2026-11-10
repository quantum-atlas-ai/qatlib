/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistTesting09.MainResults.Defs
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Papers.DistTesting09.MainResults.Defs
set_option warningAsError false

namespace Qatlib.Papers.DistTesting09.MainResults.Uniformity

variable {N M : ℕ}

def alpha (ε : ℝ) : ℝ := 256 / ε ^ 4

def fewBig (p : Dist N) (M : ℕ) (ε : ℝ) : Prop := wBig p M ≤ alpha ε / (M : ℝ)

def manyBig (p : Dist N) (M : ℕ) (ε : ℝ) : Prop := alpha ε / (M : ℝ) < wBig p M

theorem sampleSum_eq_weightedSum (p : Dist N) (S : Fin M → Fin N) :
    sampleSum p S = weightedSum (fun _ : Fin M => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x) S := by
  simp [sampleSum, weightedSum]

theorem expect_sampleSum (p : Dist N) :
    (independent (fun _ : Fin M => p)).expect (fun S => sampleSum p S) = (M : ℝ) * inner p p := by
  rw [show (fun S : Fin M → Fin N => sampleSum p S)
      = weightedSum (fun _ : Fin M => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x) from
    funext fun S => sampleSum_eq_weightedSum p S]
  rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
  have h1 : p.expect p.prob = inner p p := rfl
  simp only [one_mul, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem sampleSum_chebyshev (p : Dist N) (t : ℝ) (ht : 0 < t) :
    p.probEvent (L := M) (fun S => t ≤ |sampleSum p S - (M : ℝ) * inner p p|)
      ≤ ((M : ℝ) * p.variance p.prob) / t ^ 2 := by
  classical
  have h := Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_chebyshev (fun _ : Fin M => p)
    (fun _ => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x) t ht
  have hexp : (independent (fun _ : Fin M => p)).expect
      (weightedSum (fun _ : Fin M => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x))
      = (M : ℝ) * inner p p := by
    rw [Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
    have h1 : p.expect p.prob = inner p p := rfl
    simp only [one_mul, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hvar : (∑ _i : Fin M, (1 : ℝ) ^ 2 * p.variance p.prob)
      = (M : ℝ) * p.variance p.prob := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsumexp : (∑ i : Fin M, (fun _ : Fin M => (1 : ℝ)) i
        * FinDist.expect ((fun _ : Fin M => p) i) ((fun _ (x : Fin N) => p.prob x) i))
      = (M : ℝ) * inner p p := by
    have h1 : ∀ _i : Fin M, FinDist.expect ((fun _ : Fin M => p) _i)
        ((fun _ (x : Fin N) => p.prob x) _i) = inner p p := fun _ => rfl
    calc (∑ i : Fin M, (fun _ : Fin M => (1 : ℝ)) i
          * FinDist.expect ((fun _ : Fin M => p) i) ((fun _ (x : Fin N) => p.prob x) i))
        = ∑ _i : Fin M, inner p p :=
          Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring
      _ = (M : ℝ) * inner p p := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcongr : ∀ {E F : (Fin M → Fin N) → Prop} [DecidablePred E] [DecidablePred F],
      (∀ ω, E ω ↔ F ω) →
        eventMass (independent (fun _ : Fin M => p)) E
          = eventMass (independent (fun _ : Fin M => p)) F := by
    intro E F _ _ hEF
    simp only [eventMass]
    apply Finset.sum_congr
    · apply Finset.filter_congr
      intro x _
      exact hEF x
    · intro x _
      rfl
  have hpred : eventMass (independent (fun _ : Fin M => p))
      (fun ω => t ≤ |weightedSum (fun _ : Fin M => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x) ω
        - (∑ i : Fin M, (fun _ : Fin M => (1 : ℝ)) i
            * FinDist.expect ((fun _ : Fin M => p) i) ((fun _ (x : Fin N) => p.prob x) i))|)
      = eventMass (independent (fun _ : Fin M => p))
      (fun ω => t ≤ |weightedSum (fun _ : Fin M => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x) ω
        - (M : ℝ) * inner p p|) :=
    hcongr (fun _ => by rw [hsumexp])
  have hev : ∀ ω : Fin M → Fin N,
      t ≤ |weightedSum (fun _ : Fin M => (1 : ℝ)) (fun _ (x : Fin N) => p.prob x) ω
        - (M : ℝ) * inner p p|
      ↔ t ≤ |sampleSum p ω - (M : ℝ) * inner p p| := by
    intro ω
    rw [sampleSum_eq_weightedSum p ω]
  rw [hpred, hcongr hev, eventMass_independent_const] at h
  simpa [hvar, one_pow, one_mul] using! h

theorem lemma3_no_big [NeZero N] (p : Dist N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM : 0 < M) (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hnu : nonuniform ε p) (hnb : noBigElements p M) :
    (3 : ℝ) / 4 ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hεne : ε ≠ 0 := hε.ne'

  have hP := prop2_inner_lower ε p hε.le hnu
  have hPpos : 0 < inner p p :=
    lt_of_lt_of_le (div_pos (by positivity) hNpos) hP
  have hNP : 1 ≤ (N : ℝ) * inner p p := by
    have h2 := (div_le_iff₀ hNpos).mp hP
    nlinarith [h2, sq_nonneg ε]

  have hvar := variance_id_le p (1 / (2 * (M : ℝ) ^ 2)) hnb
  have hvarM : (M : ℝ) * p.variance p.prob ≤ inner p p / (2 * (M : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hvar hMpos.le
    calc (M : ℝ) * p.variance p.prob
        ≤ (M : ℝ) * ((1 / (2 * (M : ℝ) ^ 2)) * inner p p) := this
      _ = inner p p / (2 * (M : ℝ)) := by
          field_simp [hMne]

  have hMeq : (M : ℝ) ^ 3 * ε ^ 4 = 32 * (N : ℝ) := by
    rw [hM3]
    field_simp [hεne]
  have hMeq' : ε ^ 4 * (M : ℝ) ^ 3 = 32 * (N : ℝ) := by
    rw [mul_comm]; exact hMeq

  set E : ℝ := (M : ℝ) * inner p p with hE
  set t : ℝ := (ε ^ 2 / 4) * E with ht
  have hEpos : 0 < E := mul_pos hMpos hPpos
  have htpos : 0 < t := by
    rw [ht]
    exact mul_pos (div_pos (pow_pos hε 2) (by norm_num)) hEpos
  have hcheb := sampleSum_chebyshev (M := M) p t htpos
  have ht2 : t ^ 2 = (ε ^ 4 / 16) * E ^ 2 := by
    rw [ht]; ring

  have hratio : ((M : ℝ) * p.variance p.prob) / t ^ 2 ≤ (1 : ℝ) / 4 := by
    have hsuff : inner p p / (2 * (M : ℝ)) ≤ (1 / 4) * t ^ 2 := by
      have hprod : inner p p ≤ (N : ℝ) * inner p p * inner p p := by
        have := mul_le_mul_of_nonneg_right hNP (le_of_lt hPpos)
        simpa [mul_assoc] using! this
      have hkey : 32 * inner p p ≤ 64 * (M : ℝ) * ((1 / 4) * t ^ 2) := by
        rw [ht2, hE]
        have hkey2 : ε ^ 4 * (M : ℝ) ^ 3 = 32 * (N : ℝ) := hMeq'
        nlinarith [hkey2, hNP, hprod, hPpos, hMpos]
      calc inner p p / (2 * (M : ℝ)) = (32 * inner p p) / (64 * (M : ℝ)) := by
            field_simp [hMne]; ring
        _ ≤ (64 * (M : ℝ) * ((1 / 4) * t ^ 2)) / (64 * (M : ℝ)) :=
            div_le_div_of_nonneg_right hkey (by linarith [hMpos])
        _ = (1 / 4) * t ^ 2 := by
            rw [div_eq_iff (mul_ne_zero (by norm_num) hMne)]
            ring
    rw [div_le_iff₀ (pow_pos htpos 2)]
    linarith [hvarM, hsuff]

  have hthr : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ E - t := by
    have hcoef : (1 + ε ^ 2 / 2) ≤ (1 - ε ^ 2 / 4) * (1 + ε ^ 2) := by
      have hε2le : ε ^ 2 ≤ 1 := by nlinarith [hε.le, hε1]
      have hkey4 : 0 ≤ ε ^ 2 * (1 - ε ^ 2) :=
        mul_nonneg (sq_nonneg ε) (by linarith)
      nlinarith [hkey4]
    have hcoefnn : 0 ≤ 1 - ε ^ 2 / 4 := by nlinarith [sq_nonneg ε, hε.le, hε1]
    have hMNonneg : (0 : ℝ) ≤ (M : ℝ) / (N : ℝ) := div_nonneg hMpos.le hNpos.le
    have h2 : (1 + ε ^ 2 / 2) * ((M : ℝ) / (N : ℝ))
        ≤ (1 - ε ^ 2 / 4) * (1 + ε ^ 2) * ((M : ℝ) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef hMNonneg
    have hElb : (1 + ε ^ 2) * ((M : ℝ) / (N : ℝ)) ≤ E := by
      have h3 := mul_le_mul_of_nonneg_left hP hMpos.le
      calc (1 + ε ^ 2) * ((M : ℝ) / (N : ℝ)) = (M : ℝ) * ((1 + ε ^ 2) / (N : ℝ)) := by ring
        _ ≤ (M : ℝ) * inner p p := h3
        _ = E := hE.symm
    have h4 : (1 - ε ^ 2 / 4) * (1 + ε ^ 2) * ((M : ℝ) / (N : ℝ)) ≤ E - t := by
      have h5 : (1 - ε ^ 2 / 4) * ((1 + ε ^ 2) * ((M : ℝ) / (N : ℝ)))
          ≤ (1 - ε ^ 2 / 4) * E := mul_le_mul_of_nonneg_left hElb hcoefnn
      have h6 : (1 - ε ^ 2 / 4) * E = E - t := by rw [ht]; ring
      calc (1 - ε ^ 2 / 4) * (1 + ε ^ 2) * ((M : ℝ) / (N : ℝ))
          = (1 - ε ^ 2 / 4) * ((1 + ε ^ 2) * ((M : ℝ) / (N : ℝ))) := by ring
        _ ≤ (1 - ε ^ 2 / 4) * E := h5
        _ = E - t := h6
    calc (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)
        = (1 + ε ^ 2 / 2) * ((M : ℝ) / (N : ℝ)) := by ring
      _ ≤ (1 - ε ^ 2 / 4) * (1 + ε ^ 2) * ((M : ℝ) / (N : ℝ)) := h2
      _ ≤ E - t := h4
  have hincl : ∀ S : Fin M → Fin N,
      ¬ ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S) →
        t ≤ |sampleSum p S - E| := by
    intro S hS
    have hlt : sampleSum p S < (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) := not_le.mp hS
    have hlt' : sampleSum p S < E - t := lt_of_lt_of_le hlt hthr
    have hpos : 0 < E - sampleSum p S := by linarith
    rw [abs_sub_comm, abs_of_pos hpos]
    linarith

  have hfail : p.probEvent (L := M)
      (fun S => ¬ ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)) ≤ (1 : ℝ) / 4 := by
    have hmono : p.probEvent (L := M)
        (fun S => ¬ ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S))
        ≤ p.probEvent (L := M) (fun S => t ≤ |sampleSum p S - E|) :=
      probEvent_mono p _ _ hincl
    have hcheb' : p.probEvent (L := M) (fun S => t ≤ |sampleSum p S - E|) ≤ (1 : ℝ) / 4 :=
      le_trans hcheb hratio
    linarith

  have hcompl := probEvent_compl (M := M) p
    (fun S => (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)
  have hlt : p.probEvent (L := M)
      (fun S => ¬ ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)) ≤ (1 : ℝ) / 4 := hfail
  unfold probSampleSumGe
  linarith

theorem hitCount_expect (p : Dist N) (B : Finset (Fin N)) :
    (independent (fun _ : Fin M => p)).expect (fun S => hitCount B S)
      = (M : ℝ) * (∑ x ∈ B, p.prob x) := by
  have hfun : (fun S : Fin M → Fin N => hitCount B S)
      = weightedSum (fun _ : Fin M => (1 : ℝ))
          (fun _ (x : Fin N) => if x ∈ B then (1 : ℝ) else 0) := by
    funext S
    simp [hitCount, weightedSum]
  rw [hfun,
      Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_expectation]
  have h1 : p.expect (fun x => if x ∈ B then (1 : ℝ) else 0) = ∑ x ∈ B, p.prob x :=
    expect_indicator p B
  rw [h1]
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem hitCount_variance_le (p : Dist N) (B : Finset (Fin N)) :
    (independent (fun _ : Fin M => p)).variance (fun S => hitCount B S)
      ≤ (M : ℝ) * (∑ x ∈ B, p.prob x) := by
  have hfun : (fun S : Fin M → Fin N => hitCount B S)
      = weightedSum (fun _ : Fin M => (1 : ℝ))
          (fun _ (x : Fin N) => if x ∈ B then (1 : ℝ) else 0) := by
    funext S
    simp [hitCount, weightedSum]
  rw [hfun,
      Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces.independent_weighted_variance]
  calc (∑ _i : Fin M, (1 : ℝ) ^ 2
        * p.variance (fun x => if x ∈ B then (1 : ℝ) else 0))
      = ∑ _i : Fin M, p.variance (fun x => if x ∈ B then (1 : ℝ) else 0) := by
        simp
    _ ≤ ∑ _i : Fin M, ∑ x ∈ B, p.prob x :=
        Finset.sum_le_sum fun _ _ => indicator_variance_le p B
    _ = (M : ℝ) * (∑ x ∈ B, p.prob x) := by
        simp [Finset.sum_const, nsmul_eq_mul]

theorem lemma5_many_big [NeZero N] (p : Dist N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM : 0 < M) (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hmany : manyBig p M ε) :
    (1 : ℝ) / 2 ≤ probSampleSumGe p M (2 * (M : ℝ) / (N : ℝ)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hαpos : 0 < alpha ε := by rw [alpha]; positivity
  have hα8 : (8 : ℝ) ≤ alpha ε := by
    have h4 : ε ^ 4 ≤ 1 := pow_le_one₀ hε.le hε1
    rw [alpha, le_div_iff₀ (pow_pos hε 4)]
    nlinarith
  set w : ℝ := wBig p M with hw
  have hwval : w = ∑ x ∈ bigSet p M, p.prob x := by rw [hw]; rfl
  have hmany' : alpha ε / (M : ℝ) < w := hmany
  have hMw : (M : ℝ) * w > alpha ε := by
    have h := (div_lt_iff₀ hMpos).mp hmany'
    linarith
  have hwpos : 0 < w := by
    have h : 0 < alpha ε / (M : ℝ) := div_pos hαpos hMpos
    linarith

  have hexp : (independent (fun _ : Fin M => p)).expect (fun S => hitCount (bigSet p M) S)
      = (M : ℝ) * w := by
    rw [hitCount_expect, hwval]
  have hvar : (independent (fun _ : Fin M => p)).variance (fun S => hitCount (bigSet p M) S)
      ≤ (M : ℝ) * w := by
    rw [hwval]
    exact hitCount_variance_le p (bigSet p M)

  have hMwpos : 0 < (M : ℝ) * w := mul_pos hMpos hwpos
  have hcheb := chebyshev (independent (fun _ : Fin M => p))
    (fun S => hitCount (bigSet p M) S) ((M : ℝ) * w / 2) (by linarith)
  have hMwne : (M : ℝ) * w ≠ 0 := hMwpos.ne'
  rw [hexp] at hcheb
  have hratio : ((M : ℝ) * w) / ((M : ℝ) * w / 2) ^ 2 ≤ (1 : ℝ) / 2 := by
    have h4 : ((M : ℝ) * w) / ((M : ℝ) * w / 2) ^ 2 = 4 / ((M : ℝ) * w) := by
      field_simp [hMwne]
      ring
    rw [h4, div_le_iff₀ hMwpos]
    nlinarith [hMw, hα8]
  have hcheb' : eventMass (independent (fun _ : Fin M => p))
      (fun S => (M : ℝ) * w / 2 ≤ |hitCount (bigSet p M) S - (M : ℝ) * w|)
      ≤ (1 : ℝ) / 2 := by
    calc eventMass (independent (fun _ : Fin M => p))
          (fun S => (M : ℝ) * w / 2 ≤ |hitCount (bigSet p M) S - (M : ℝ) * w|)
        ≤ ((independent (fun _ : Fin M => p)).variance (fun S => hitCount (bigSet p M) S))
            / ((M : ℝ) * w / 2) ^ 2 := hcheb
      _ ≤ ((M : ℝ) * w) / ((M : ℝ) * w / 2) ^ 2 :=
          div_le_div_of_nonneg_right hvar (by positivity)
      _ ≤ (1 : ℝ) / 2 := hratio

  have hsub₁ : ∀ S : Fin M → Fin N,
      hitCount (bigSet p M) S < alpha ε / 2 →
        (M : ℝ) * w / 2 ≤ |hitCount (bigSet p M) S - (M : ℝ) * w| := by
    intro S hS
    have hlt : hitCount (bigSet p M) S < (M : ℝ) * w := by nlinarith [hS, hMw]
    have hhalf : 2 * hitCount (bigSet p M) S < (M : ℝ) * w := by nlinarith [hS, hMw]
    have hpos : 0 < (M : ℝ) * w - hitCount (bigSet p M) S := by linarith
    rw [abs_sub_comm, abs_of_pos hpos]
    linarith
  have hfail : p.probEvent (L := M)
      (fun S => hitCount (bigSet p M) S < alpha ε / 2) ≤ (1 : ℝ) / 2 := by
    rw [← eventMass_independent_const p
      (fun S : Fin M → Fin N => hitCount (bigSet p M) S < alpha ε / 2)]
    exact le_trans (eventMass_mono _ _ _ hsub₁) hcheb'

  have hM3' : (M : ℝ) ^ 3 * ε ^ 4 = 32 * (N : ℝ) := by
    rw [hM3]; field_simp [hεne]
  have hthr : 2 * (M : ℝ) / (N : ℝ) = 64 / (ε ^ 4 * (M : ℝ) ^ 2) := by
    have hN32 : 32 * (N : ℝ) = (M : ℝ) ^ 3 * ε ^ 4 := by linarith [hM3']
    field_simp [hNne, hεne, hMne]
    nlinarith [hN32]

  have hsub₂ : ∀ S : Fin M → Fin N,
      alpha ε / 2 ≤ hitCount (bigSet p M) S →
        2 * (M : ℝ) / (N : ℝ) ≤ sampleSum p S := by
    intro S hS
    have hpoint : ∀ a : Fin M,
        (if S a ∈ bigSet p M then (1 : ℝ) / (2 * (M : ℝ) ^ 2) else 0) ≤ p.prob (S a) := by
      intro a
      by_cases ha : S a ∈ bigSet p M
      · simp only [ha, if_true]
        exact le_of_lt (Finset.mem_filter.mp ha).2
      · simp only [ha, if_false]
        exact p.nonneg _
    have hsum_le : (∑ a, (if S a ∈ bigSet p M then (1 : ℝ) / (2 * (M : ℝ) ^ 2) else 0))
        ≤ sampleSum p S := Finset.sum_le_sum fun a _ => hpoint a
    have hpull : (∑ a, (if S a ∈ bigSet p M then (1 : ℝ) / (2 * (M : ℝ) ^ 2) else 0))
        = (1 / (2 * (M : ℝ) ^ 2)) * hitCount (bigSet p M) S := by
      simp only [hitCount]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by
        by_cases ha : S a ∈ bigSet p M <;> simp [ha]
    rw [hpull] at hsum_le
    have hval : (1 / (2 * (M : ℝ) ^ 2)) * (alpha ε / 2) = 64 / (ε ^ 4 * (M : ℝ) ^ 2) := by
      rw [alpha]; field_simp [hMne, hεne]; ring
    have h1 : (1 / (2 * (M : ℝ) ^ 2)) * (alpha ε / 2)
        ≤ (1 / (2 * (M : ℝ) ^ 2)) * hitCount (bigSet p M) S :=
      mul_le_mul_of_nonneg_left hS (le_of_lt (div_pos one_pos
        (by nlinarith [hMpos] : (0 : ℝ) < 2 * (M : ℝ) ^ 2)))
    rw [hthr]
    linarith

  have hge : (1 : ℝ) / 2 ≤ p.probEvent (L := M)
      (fun S => alpha ε / 2 ≤ hitCount (bigSet p M) S) := by
    have hcompl := probEvent_compl (M := M) p
      (fun S => alpha ε / 2 ≤ hitCount (bigSet p M) S)
    have hlt : p.probEvent (L := M)
        (fun S => ¬ (alpha ε / 2 ≤ hitCount (bigSet p M) S)) ≤ (1 : ℝ) / 2 := by
      have heq : p.probEvent (L := M)
            (fun S => ¬ (alpha ε / 2 ≤ hitCount (bigSet p M) S))
          = p.probEvent (L := M)
            (fun S => hitCount (bigSet p M) S < alpha ε / 2) := by
        apply le_antisymm
        · apply probEvent_mono
          intro S hS
          exact not_le.mp hS
        · apply probEvent_mono
          intro S hS
          exact not_le.mpr hS
      rw [heq]
      exact hfail
    linarith
  unfold probSampleSumGe
  exact le_trans hge (probEvent_mono p _ _ hsub₂)

theorem prop3_renormalize_nonuniform [NeZero N] (p : Dist N) (ε : ℝ)
    (h : massOf p (bigSet p M) < 1) (hnu : nonuniform ε p) :
    nonuniform (ε - 2 * wBig p M) (renormalizeOff p (bigSet p M) h) := by
  unfold nonuniform at *
  have htri := l1_triangle p (renormalizeOff p (bigSet p M) h) (uniform N)
  have hle := l1_renormalizeOff_le p (bigSet p M) h
  have hw : massOf p (bigSet p M) = wBig p M := rfl
  linarith

theorem correction_small (ε : ℝ) (hε : 0 < ε) (hM : 0 < M)
    (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hNbig : (2 : ℝ) ^ 25 ≤ ε ^ 11 * (N : ℝ)) :
    4 * alpha ε ≤ ε * (M : ℝ) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hεne : ε ≠ 0 := hε.ne'
  have hcube : (ε ^ 5 * (M : ℝ)) ^ 3 = 32 * (ε ^ 11 * (N : ℝ)) := by
    rw [mul_pow, hM3]
    field_simp [hεne] <;> ring
  have h2 : (1024 : ℝ) ^ 3 ≤ (ε ^ 5 * (M : ℝ)) ^ 3 := by
    rw [hcube]
    have h1024 : (1024 : ℝ) ^ 3 = 2 ^ 30 := by norm_num
    rw [h1024]
    nlinarith [hNbig]
  have hnn : 0 ≤ ε ^ 5 * (M : ℝ) := by positivity
  have h3 : (1024 : ℝ) ≤ ε ^ 5 * (M : ℝ) :=
    (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1024) hnn
      (by norm_num : (3 : ℕ) ≠ 0)).mp h2
  rw [alpha, show 4 * (256 / ε ^ 4) = 1024 / ε ^ 4 by ring]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 4)]
  nlinarith [h3]

theorem prop3_half [NeZero N] (p : Dist N) (ε : ℝ) (hM : 0 < M)
    (hfew : fewBig p M ε) (hcorr : 4 * alpha ε ≤ ε * (M : ℝ)) :
    ε / 2 ≤ ε - 2 * wBig p M := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h1 : 2 * wBig p M ≤ 2 * (alpha ε / (M : ℝ)) := by
    have hf : wBig p M ≤ alpha ε / (M : ℝ) := hfew
    linarith
  have h2 : 2 * (alpha ε / (M : ℝ)) ≤ ε / 2 := by
    rw [show 2 * (alpha ε / (M : ℝ)) = (2 * alpha ε) / (M : ℝ) by ring]
    rw [div_le_iff₀ hMpos]
    nlinarith [hcorr]
  linarith

theorem lemma2_main [NeZero N] (p : Dist N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hM : 0 < M) (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hnu : nonuniform ε p)
    (hcase : noBigElements p M ∨ manyBig p M ε) :
    (1 : ℝ) / 2 * Real.exp (-(alpha ε))
      ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := by
  have hαpos : 0 < alpha ε := by rw [alpha]; positivity
  have hexp1 : Real.exp (-(alpha ε)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rcases hcase with hnb | hmany
  · have h3 := lemma3_no_big p ε hε hε1 hM hM3 hnu hnb
    have hhalf : (1 : ℝ) / 2 * Real.exp (-(alpha ε)) ≤ 3 / 4 := by
      nlinarith [hexp1]
    linarith
  · have h5 := lemma5_many_big p ε hε hε1 hM hM3 hmany
    have hmono : probSampleSumGe p M (2 * (M : ℝ) / (N : ℝ))
        ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := by
      apply probEvent_mono
      intro S hS
      have hstep : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ 2 * (M : ℝ) / (N : ℝ) := by
        have hcoef : (1 + ε ^ 2 / 2) ≤ 2 := by nlinarith [sq_nonneg ε, hε1]
        have hMN : (0 : ℝ) ≤ (M : ℝ) / (N : ℝ) := by positivity
        calc (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)
            = (1 + ε ^ 2 / 2) * ((M : ℝ) / (N : ℝ)) := by ring
          _ ≤ 2 * ((M : ℝ) / (N : ℝ)) := mul_le_mul_of_nonneg_right hcoef hMN
          _ = 2 * (M : ℝ) / (N : ℝ) := by ring
      exact le_trans hstep hS
    have hhalf : (1 : ℝ) / 2 * Real.exp (-(alpha ε)) ≤ 1 / 2 := by
      nlinarith [hexp1]
    linarith

theorem probEvent_avoid_eq (p : Dist N) (B : Finset (Fin N))
    (h : massOf p B < 1) (M : ℕ) (E : (Fin M → Fin N) → Prop) [DecidablePred E]
    (hE : ∀ S, E S → ∀ a, S a ∉ B) :
    p.probEvent (L := M) E
      = (1 - massOf p B) ^ M *
        (renormalizeOff p B h).probEvent (L := M) E := by
  classical
  have hw : 0 < 1 - massOf p B := by linarith [h]
  have hfac : ∀ S : Fin M → Fin N, E S → ∀ a : Fin M,
      p.prob (S a) = (1 - massOf p B) * (renormalizeOff p B h).prob (S a) := by
    intro S hS a
    have hmem : S a ∉ B := hE S hS a
    simp only [renormalizeOff, hmem, if_false]
    field_simp
  have hpoint : ∀ S : Fin M → Fin N, E S →
      p.probOf S = (1 - massOf p B) ^ M * (renormalizeOff p B h).probOf S := by
    intro S hS
    simp only [FinDist.probOf]
    calc ∏ a, p.prob (S a)
        = ∏ a, ((1 - massOf p B) * (renormalizeOff p B h).prob (S a)) :=
          Finset.prod_congr rfl fun a _ => hfac S hS a
      _ = (∏ _a : Fin M, (1 - massOf p B))
            * ∏ a, (renormalizeOff p B h).prob (S a) := Finset.prod_mul_distrib
      _ = (1 - massOf p B) ^ M
            * ∏ a, (renormalizeOff p B h).prob (S a) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [FinDist.probEvent]
  calc ∑ S ∈ Finset.univ.filter E, p.probOf S
      = ∑ S ∈ Finset.univ.filter E,
          (1 - massOf p B) ^ M * (renormalizeOff p B h).probOf S :=
        Finset.sum_congr rfl fun S hS => hpoint S (Finset.mem_filter.mp hS).2
    _ = (1 - massOf p B) ^ M *
          ∑ S ∈ Finset.univ.filter E, (renormalizeOff p B h).probOf S :=
        (Finset.mul_sum _ _ _).symm

theorem log_one_sub_ge_neg_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.log (1 - x) ≥ -(2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hinv : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp
    ring
  have hxle : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hpos]
    nlinarith
  rw [hinv] at h
  linarith

theorem pow_one_sub_ge_exp_neg (w : ℝ) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) (M : ℕ) :
    Real.exp (-(2 * (M : ℝ) * w)) ≤ (1 - w) ^ M := by
  have hpos : 0 < 1 - w := by linarith
  have hxlog : -(2 * (M : ℝ) * w) ≤ Real.log ((1 - w) ^ M) := by
    rw [Real.log_pow]
    have h := log_one_sub_ge_neg_two_mul hw0 hw
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := by positivity
    nlinarith [h, hMnn]
  exact (Real.le_log_iff_exp_le (pow_pos hpos M)).mp hxlog

theorem few_big_threshold (ε w : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hw0 : 0 ≤ w) (hw : w ≤ ε ^ 2 / 64) :
    (1 + ε ^ 2 / 2) / (1 - w)
      ≤ (1 - (ε - 2 * w) ^ 2 / 4) * (1 + (ε - 2 * w) ^ 2) := by
  have h1w : 0 < 1 - w := by nlinarith
  rw [div_le_iff₀ h1w]
  have h1wlo : 1 - ε ^ 2 / 64 ≤ 1 - w := by linarith
  have h2w : 2 * w ≤ ε ^ 2 / 32 := by nlinarith
  have hee0 : 0 ≤ ε - ε ^ 2 / 32 := by nlinarith
  have he0 : 0 ≤ ε - 2 * w := by nlinarith
  have hge : ε - ε ^ 2 / 32 ≤ ε - 2 * w := by linarith
  have he2min : (ε - ε ^ 2 / 32) ^ 2 ≤ (ε - 2 * w) ^ 2 := by
    nlinarith [hee0, he0, hge]
  have hle : ε - 2 * w ≤ ε := by nlinarith
  have he2le : (ε - 2 * w) ^ 2 ≤ ε ^ 2 := by
    nlinarith [he0, hε.le, hle]
  have h1e2 : 3 / 4 ≤ 1 - (ε - 2 * w) ^ 2 := by nlinarith [he2le, hε2, hε.le]
  have hslack : (3 / 16) * (ε - ε ^ 2 / 32) ^ 2
      ≤ (ε - 2 * w) ^ 2 * (1 - (ε - 2 * w) ^ 2) / 4 := by
    nlinarith [he2min, he2le, h1e2, sq_nonneg (ε - 2 * w)]
  have hcore : 1 + ε ^ 2 / 2
      ≤ (1 - ε ^ 2 / 64) * (1 + (ε - ε ^ 2 / 32) ^ 2 / 2
          + (3 / 16) * (ε - ε ^ 2 / 32) ^ 2) := by
    nlinarith [sq_nonneg (ε - ε ^ 2 / 32), sq_nonneg ε, hε.le, hε2, sq_nonneg (ε ^ 2)]
  have hsmall0 : 0 ≤ 1 + (ε - ε ^ 2 / 32) ^ 2 / 2 + (3 / 16) * (ε - ε ^ 2 / 32) ^ 2 := by
    nlinarith [sq_nonneg (ε - ε ^ 2 / 32)]
  have hstep : (1 - ε ^ 2 / 64) * (1 + (ε - ε ^ 2 / 32) ^ 2 / 2
        + (3 / 16) * (ε - ε ^ 2 / 32) ^ 2)
      ≤ (1 - w) * (1 + (ε - 2 * w) ^ 2 / 2 + (ε - 2 * w) ^ 2 * (1 - (ε - 2 * w) ^ 2) / 4) := by
    apply mul_le_mul
    · exact h1wlo
    · nlinarith [he2min, hslack]
    · exact hsmall0
    · exact h1w.le
  have hfin : (1 - w) * (1 + (ε - 2 * w) ^ 2 / 2 + (ε - 2 * w) ^ 2 * (1 - (ε - 2 * w) ^ 2) / 4)
      = (1 - w) * (1 - (ε - 2 * w) ^ 2 / 4) * (1 + (ε - 2 * w) ^ 2) := by
    ring
  rw [hfin] at hstep
  linarith [hcore, hstep]

theorem few_big_ratio (ε w : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hw0 : 0 ≤ w) (hw : w ≤ ε ^ 2 / 64) :
    ε ^ 4 / (4 * (1 - w) * (ε - 2 * w) ^ 4) ≤ 1 / 2 := by
  have hw1 : w ≤ 1 / 256 := by nlinarith
  have h1w : 0 < 1 - w := by linarith
  have he : 0 < ε - 2 * w := by nlinarith
  have hden : 0 < 4 * (1 - w) * (ε - 2 * w) ^ 4 := by positivity
  rw [div_le_iff₀ hden]
  have h2w : 2 * w ≤ ε / 64 := by nlinarith
  have hep : 63 * ε / 64 ≤ ε - 2 * w := by linarith
  have h1wl : 255 / 256 ≤ 1 - w := by linarith
  have hpow : (63 * ε / 64) ^ 4 ≤ (ε - 2 * w) ^ 4 :=
    pow_le_pow_left₀ (by linarith [hε.le] : (0 : ℝ) ≤ 63 * ε / 64) hep 4
  have hprod : (255 / 256) * (63 * ε / 64) ^ 4 ≤ (1 - w) * (ε - 2 * w) ^ 4 :=
    mul_le_mul h1wl hpow (by positivity) (by linarith)
  have hbase : (1 : ℝ) ≤ 2 * (255 / 256) * (63 / 64) ^ 4 := by norm_num
  nlinarith [hprod, hbase, pow_pos hε 4]

theorem theorem2_repetition_bound (α : ℝ) (hα : 0 ≤ α) (L : ℕ) (pper : ℝ)
    (hpper0 : 0 ≤ pper) (hpper1 : pper ≤ 1)
    (hpper : (1 : ℝ) / 2 * Real.exp (-α) ≤ pper)
    (hnumeric : (1 - (1 : ℝ) / 2 * Real.exp (-α)) ^ L ≤ (1 : ℝ) / 6) :
    (5 : ℝ) / 6 ≤ 1 - (1 - pper) ^ L := by
  have hexp1 : Real.exp (-α) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx1 : (1 : ℝ) / 2 * Real.exp (-α) ≤ 1 := by linarith
  have hmono : (1 - pper) ^ L ≤ (1 - (1 : ℝ) / 2 * Real.exp (-α)) ^ L := by
    apply pow_le_pow_left₀ (by linarith)
    linarith
  linarith

theorem theorem2_uniformity [NeZero N] (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (M K L : ℕ), 0 < M ∧ 0 < K ∧ 0 < L ∧
      (M : ℝ) ^ 3 ≤ 32 * (N : ℝ) / ε ^ 4 ∧
      (K : ℝ) ^ 3 ≤ (Real.exp (alpha ε)) ^ 3 * (N : ℝ) / ε ^ 4 ∧
      (4 : ℝ) * Real.exp (alpha ε) ≤ (L : ℝ) ∧
      (L : ℝ) ≤ 4 * Real.exp (alpha ε) + 1 := by
  have hαpos : 0 < alpha ε := by rw [alpha]; positivity
  have hε4 : 0 < ε ^ 4 := pow_pos hε 4
  have hε4le : ε ^ 4 ≤ 1 := pow_le_one₀ (n := 4) hε.le hε1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have h1M : ((1 : ℕ) : ℝ) ^ 3 ≤ 32 * (N : ℝ) / ε ^ 4 := by
    have h32 : (1 : ℝ) ≤ 32 * (N : ℝ) / ε ^ 4 := by
      rw [le_div_iff₀ hε4]
      nlinarith [hN1, hε4le]
    simpa using! h32
  have h1K : ((1 : ℕ) : ℝ) ^ 3 ≤ (Real.exp (alpha ε)) ^ 3 * (N : ℝ) / ε ^ 4 := by
    have he1 : (1 : ℝ) ≤ Real.exp (alpha ε) := Real.one_le_exp (le_of_lt hαpos)
    have hpow : (1 : ℝ) ≤ (Real.exp (alpha ε)) ^ 3 := by
      calc (1 : ℝ) = 1 ^ 3 := by ring
        _ ≤ (Real.exp (alpha ε)) ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
    have h32 : (1 : ℝ) ≤ (Real.exp (alpha ε)) ^ 3 * (N : ℝ) / ε ^ 4 := by
      rw [le_div_iff₀ hε4]
      nlinarith [hpow, hN1, hε4le]
    simpa using! h32
  have hceilpos : 0 < Nat.ceil (4 * Real.exp (alpha ε)) := by
    apply Nat.ceil_pos.mpr
    positivity
  have hleceil : (4 : ℝ) * Real.exp (alpha ε) ≤ (Nat.ceil (4 * Real.exp (alpha ε)) : ℝ) :=
    Nat.le_ceil _
  have hltceil : (Nat.ceil (4 * Real.exp (alpha ε)) : ℝ) ≤ 4 * Real.exp (alpha ε) + 1 := by
    have hx : (0 : ℝ) ≤ 4 * Real.exp (alpha ε) := by positivity
    have h := Nat.ceil_lt_add_one hx
    linarith
  refine ⟨1, 1, Nat.ceil (4 * Real.exp (alpha ε)), by norm_num, by norm_num,
    hceilpos, h1M, h1K, hleceil, hltceil⟩

theorem inner_self_ge_inv [NeZero N] (p : Dist N) : (N : ℝ)⁻¹ ≤ inner p p := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ : Fin N => (1 : ℝ)) (fun i => p.prob i)
  have hconst : (∑ _i : Fin N, ((1 : ℝ)) ^ 2) = (N : ℝ) := by
    simp [Finset.sum_const, Fintype.card_fin]
  have hone : (∑ i : Fin N, (1 : ℝ) * p.prob i) = 1 := by
    simpa using! p.sum_one
  have hin : inner p p = ∑ i, p.prob i ^ 2 := by
    show (∑ i, p.prob i * p.prob i) = ∑ i, p.prob i ^ 2
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmain : (1 : ℝ) ≤ (N : ℝ) * ∑ i, p.prob i ^ 2 := by
    have h := hcs
    rw [hconst, hone, one_pow] at h
    linarith [h]
  rw [hin, show (N : ℝ)⁻¹ = 1 / (N : ℝ) by rw [one_div]]
  exact (div_le_iff₀ hNpos).mpr (by nlinarith [hmain])

theorem renormalizeOff_le_sup (p : Dist N) (B : Finset (Fin N))
    (h : massOf p B < 1) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ i, i ∉ B → p.prob i ≤ D)
    (i : Fin N) : (renormalizeOff p B h).prob i ≤ D / (1 - massOf p B) := by
  have h1w : 0 < 1 - massOf p B := by linarith [h]
  by_cases hi : i ∈ B
  · have hz : (renormalizeOff p B h).prob i = 0 := by simp [renormalizeOff, hi]
    rw [hz]
    exact div_nonneg hD0 h1w.le
  · have hval : (renormalizeOff p B h).prob i = p.prob i / (1 - massOf p B) := by
      simp [renormalizeOff, hi]
    rw [hval]
    exact div_le_div_of_nonneg_right (hD i hi) h1w.le

theorem probEvent_congr_of_probOf_zero (p : Dist N) (M : ℕ)
    (E F : (Fin M → Fin N) → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ S, E S ≠ F S → p.probOf S = 0) :
    p.probEvent (L := M) E = p.probEvent (L := M) F := by
  classical
  have hpt : ∀ S : Fin M → Fin N,
      (if E S then p.probOf S else 0) = (if F S then p.probOf S else 0) := by
    intro S
    by_cases hE : E S <;> by_cases hF : F S
    · simp [hE, hF]
    · have : E S ≠ F S := by simp [hE, hF]
      simp [hE, hF, h S this]
    · have : E S ≠ F S := by simp [hE, hF]
      simp [hE, hF, h S this]
    · simp [hE, hF]
  have hEe : p.probEvent (L := M) E = ∑ S, if E S then p.probOf S else 0 := by
    simp only [FinDist.probEvent]
    rw [Finset.sum_filter]
  have hFe : p.probEvent (L := M) F = ∑ S, if F S then p.probOf S else 0 := by
    simp only [FinDist.probEvent]
    rw [Finset.sum_filter]
  rw [hEe, hFe]
  exact Finset.sum_congr rfl fun S _ => hpt S

theorem probSampleSumGe_of_thr [NeZero N] (p : Dist N) (thr ε' : ℝ)
    (hε' : 0 < ε') (M : ℕ) (hM : 0 < M) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ i, p.prob i ≤ D) (hnu : nonuniform ε' p)
    (hthr : thr ≤ (1 - ε' ^ 2 / 4) * ((M : ℝ) * inner p p)) :
    p.probEvent (L := M) (fun S => ¬ (thr ≤ sampleSum p S))
      ≤ 16 * D * (N : ℝ) / (ε' ^ 4 * (M : ℝ)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hε'ne : ε' ≠ 0 := hε'.ne'
  have hε'2 : 0 < ε' ^ 2 := by positivity
  have hP := prop2_inner_lower ε' p hε'.le hnu
  have hPpos : 0 < inner p p :=
    lt_of_lt_of_le (div_pos (by positivity) hNpos) hP
  set E : ℝ := (M : ℝ) * inner p p with hE
  have hEpos : 0 < E := mul_pos hMpos hPpos
  set t : ℝ := (ε' ^ 2 / 4) * E with ht
  have htpos : 0 < t := mul_pos (by positivity) hEpos
  have hcheb := sampleSum_chebyshev (M := M) p t htpos
  have hvarD : p.variance p.prob ≤ D * inner p p := variance_id_le p D hD
  have hratio : ((M : ℝ) * p.variance p.prob) / t ^ 2
      ≤ 16 * D / (ε' ^ 4 * (M : ℝ) * inner p p) := by
    have ht2 : t ^ 2 = (ε' ^ 4 / 16) * E ^ 2 := by rw [ht]; ring
    calc ((M : ℝ) * p.variance p.prob) / t ^ 2
        = ((M : ℝ) * p.variance p.prob) / ((ε' ^ 4 / 16) * E ^ 2) := by rw [ht2]
      _ ≤ ((M : ℝ) * (D * inner p p)) / ((ε' ^ 4 / 16) * E ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvarD hMpos.le)
            (by positivity)
      _ = 16 * D / (ε' ^ 4 * (M : ℝ) * inner p p) := by
          rw [hE]
          field_simp
  have hfail : p.probEvent (L := M) (fun S => ¬ (thr ≤ sampleSum p S))
      ≤ p.probEvent (L := M) (fun S => t ≤ |sampleSum p S - E|) := by
    apply probEvent_mono
    intro S hS
    have hlt : sampleSum p S < thr := not_le.mp hS
    have hthr' : thr ≤ E - t := by
      have hEt : (1 - ε' ^ 2 / 4) * E = E - t := by rw [ht]; ring
      rw [← hEt]; exact hthr
    have hlt' : sampleSum p S < E - t := lt_of_lt_of_le hlt hthr'
    have hpos : 0 < E - sampleSum p S := by linarith
    rw [abs_sub_comm, abs_of_pos hpos]
    linarith
  have hstep : 16 * D / (ε' ^ 4 * (M : ℝ) * inner p p)
      ≤ 16 * D * (N : ℝ) / (ε' ^ 4 * (M : ℝ)) := by
    have hNinner : (1 : ℝ) ≤ (N : ℝ) * inner p p := by
      have h := inner_self_ge_inv (N := N) p
      rw [show (N : ℝ)⁻¹ = 1 / (N : ℝ) by rw [one_div]] at h
      have h2 := (div_le_iff₀ hNpos).mp h
      linarith [h2]
    have hden : 0 < ε' ^ 4 * (M : ℝ) := by positivity
    have hinv : 1 / inner p p ≤ (N : ℝ) := by
      rw [div_le_iff₀ hPpos]
      linarith [hNinner]
    calc 16 * D / (ε' ^ 4 * (M : ℝ) * inner p p)
        = (16 * D / (ε' ^ 4 * (M : ℝ))) * (1 / inner p p) := by
          field_simp
      _ ≤ (16 * D / (ε' ^ 4 * (M : ℝ))) * (N : ℝ) := by
          apply mul_le_mul_of_nonneg_left hinv
          positivity
      _ = 16 * D * (N : ℝ) / (ε' ^ 4 * (M : ℝ)) := by ring
  calc p.probEvent (L := M) (fun S => ¬ (thr ≤ sampleSum p S))
      ≤ p.probEvent (L := M) (fun S => t ≤ |sampleSum p S - E|) := hfail
    _ ≤ ((M : ℝ) * p.variance p.prob) / t ^ 2 := hcheb
    _ ≤ 16 * D / (ε' ^ 4 * (M : ℝ) * inner p p) := hratio
    _ ≤ 16 * D * (N : ℝ) / (ε' ^ 4 * (M : ℝ)) := hstep

theorem wBig_nonneg (p : Dist N) (M : ℕ) : 0 ≤ wBig p M :=
  Finset.sum_nonneg fun i _ => p.nonneg i

theorem sampleSum_renormalizeOff (p : Dist N) (B : Finset (Fin N))
    (h : massOf p B < 1) (S : Fin M → Fin N) (hS : ∀ a, S a ∉ B) :
    sampleSum (renormalizeOff p B h) S = sampleSum p S / (1 - massOf p B) := by
  simp only [sampleSum]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by
    rw [show (renormalizeOff p B h).prob (S a) = p.prob (S a) / (1 - massOf p B) from by
      simp [renormalizeOff, hS a], div_eq_mul_inv]

theorem probOf_eq_zero_of_coord_zero (q : Dist N) (S : Fin M → Fin N)
    (h : ∃ a, q.prob (S a) = 0) : q.probOf S = 0 := by
  obtain ⟨a, ha⟩ := h
  simp only [FinDist.probOf]
  exact Finset.prod_eq_zero (Finset.mem_univ a) ha

theorem renormalizeOff_probOf_of_not_avoid (p : Dist N) (B : Finset (Fin N))
    (h : massOf p B < 1) (S : Fin M → Fin N) (hS : ¬ ∀ a, S a ∉ B) :
    (renormalizeOff p B h).probOf S = 0 := by
  apply probOf_eq_zero_of_coord_zero
  push_neg at hS
  obtain ⟨a, ha⟩ := hS
  exact ⟨a, by simp [renormalizeOff, ha]⟩

theorem wBig_le_eps_sq (p : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hM : 0 < M) (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hfew : fewBig p M ε) (hNlarge : (2 : ℝ) ^ 37 ≤ ε ^ 14 * (N : ℝ)) :
    wBig p M ≤ ε ^ 2 / 64 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcube : (ε ^ 6 * (M : ℝ)) ^ 3 = 32 * (ε ^ 14 * (N : ℝ)) := by
    rw [mul_pow, hM3]
    field_simp [hε.ne']
  have h2 : ((16384 : ℝ)) ^ 3 ≤ (ε ^ 6 * (M : ℝ)) ^ 3 := by
    rw [hcube]
    have hpow : ((16384 : ℝ)) ^ 3 = (2 : ℝ) ^ 42 := by norm_num
    rw [hpow]
    nlinarith [hNlarge]
  have hnn : 0 ≤ ε ^ 6 * (M : ℝ) := by positivity
  have h3 : (16384 : ℝ) ≤ ε ^ 6 * (M : ℝ) :=
    (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 16384) hnn
      (by norm_num : (3 : ℕ) ≠ 0)).mp h2
  have hden : 0 < ε ^ 4 * (M : ℝ) := by positivity
  have hstep : 256 / (ε ^ 4 * (M : ℝ)) ≤ ε ^ 2 / 64 := by
    rw [div_le_iff₀ hden]
    nlinarith [h3]
  calc wBig p M ≤ alpha ε / (M : ℝ) := hfew
    _ = 256 / ε ^ 4 / (M : ℝ) := by rw [alpha]
    _ = 256 / (ε ^ 4 * (M : ℝ)) := by rw [div_div]
    _ ≤ ε ^ 2 / 64 := hstep

theorem lemma4_few_big [NeZero N] (p : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hM : 0 < M)
    (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hnu : nonuniform ε p) (hfew : fewBig p M ε)
    (hNlarge : (2 : ℝ) ^ 37 ≤ ε ^ 14 * (N : ℝ)) :
    (1 - wBig p M) ^ M * (1 / 2)
      ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hw64 : wBig p M ≤ ε ^ 2 / 64 := wBig_le_eps_sq p ε hε hM hM3 hfew hNlarge
  have hw0 : 0 ≤ wBig p M := wBig_nonneg p M
  have hw1 : wBig p M < 1 := by nlinarith [hw64, hε.le, hε2]
  have h1w : 0 < 1 - wBig p M := by linarith
  have hε'pos : 0 < ε - 2 * wBig p M := by nlinarith [hw64, hε, hε2]
  set B : Finset (Fin N) := bigSet p M with hBdef
  have hmass : massOf p B = wBig p M := rfl
  have hwB1 : massOf p B < 1 := by rw [hmass]; exact hw1
  set q : Dist N := renormalizeOff p B hwB1 with hqdef
  have hqnu : nonuniform (ε - 2 * wBig p M) q := by
    have h := prop3_renormalize_nonuniform p ε hwB1 hnu
    simpa only [q] using! h

  have hD0 : 0 ≤ (1 : ℝ) / (2 * (M : ℝ) ^ 2) := by positivity
  have hDoff : ∀ i, i ∉ B → p.prob i ≤ 1 / (2 * (M : ℝ) ^ 2) := by
    intro i hi
    by_contra hcon
    have hlt : (1 : ℝ) / (2 * (M : ℝ) ^ 2) < p.prob i := not_le.mp hcon
    have hmem : i ∈ bigSet p M := by
      simp only [bigSet]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩
    exact hi (by rw [hBdef]; exact hmem)
  have hD : ∀ i, q.prob i ≤ (1 / (2 * (M : ℝ) ^ 2)) / (1 - wBig p M) := by
    intro i
    have h := renormalizeOff_le_sup p B hwB1 (1 / (2 * (M : ℝ) ^ 2)) hD0 hDoff i
    simpa only [q, hmass] using! h

  have he'le : ε - 2 * wBig p M ≤ 1 / 2 := by nlinarith [hw0, hε2]
  have hfac : 0 ≤ 1 - (ε - 2 * wBig p M) ^ 2 / 4 := by nlinarith [hε'pos, he'le]
  have hthr : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
      ≤ (1 - (ε - 2 * wBig p M) ^ 2 / 4) * ((M : ℝ) * inner q q) := by
    have hPlow := prop2_inner_lower (ε - 2 * wBig p M) q hε'pos.le hqnu
    have hMPlow : (M : ℝ) * ((1 + (ε - 2 * wBig p M) ^ 2) / (N : ℝ))
        ≤ (M : ℝ) * inner q q :=
      mul_le_mul_of_nonneg_left hPlow hMpos.le
    have hstep1 : (1 - (ε - 2 * wBig p M) ^ 2 / 4)
          * ((M : ℝ) * ((1 + (ε - 2 * wBig p M) ^ 2) / (N : ℝ)))
        ≤ (1 - (ε - 2 * wBig p M) ^ 2 / 4) * ((M : ℝ) * inner q q) :=
      mul_le_mul_of_nonneg_left hMPlow hfac
    have hnum := few_big_threshold ε (wBig p M) hε hε2 hw0 hw64
    have hMN : (0 : ℝ) ≤ (M : ℝ) / (N : ℝ) := div_nonneg hMpos.le hNpos.le
    have hstep2 : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
        ≤ ((1 - (ε - 2 * wBig p M) ^ 2 / 4) * (1 + (ε - 2 * wBig p M) ^ 2))
            * ((M : ℝ) / (N : ℝ)) := by
      have hE : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
          = ((1 + ε ^ 2 / 2) / (1 - wBig p M)) * ((M : ℝ) / (N : ℝ)) := by ring_nf
      rw [hE]
      exact mul_le_mul_of_nonneg_right hnum hMN
    have hstep3 : ((1 - (ε - 2 * wBig p M) ^ 2 / 4) * (1 + (ε - 2 * wBig p M) ^ 2))
            * ((M : ℝ) / (N : ℝ))
        = (1 - (ε - 2 * wBig p M) ^ 2 / 4)
            * ((M : ℝ) * ((1 + (ε - 2 * wBig p M) ^ 2) / (N : ℝ))) := by ring_nf
    calc (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
        ≤ ((1 - (ε - 2 * wBig p M) ^ 2 / 4) * (1 + (ε - 2 * wBig p M) ^ 2))
            * ((M : ℝ) / (N : ℝ)) := hstep2
      _ = (1 - (ε - 2 * wBig p M) ^ 2 / 4)
            * ((M : ℝ) * ((1 + (ε - 2 * wBig p M) ^ 2) / (N : ℝ))) := hstep3
      _ ≤ (1 - (ε - 2 * wBig p M) ^ 2 / 4) * ((M : ℝ) * inner q q) := hstep1

  have hcheb := probSampleSumGe_of_thr q
    ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M))
    (ε - 2 * wBig p M) hε'pos M hM
    ((1 / (2 * (M : ℝ) ^ 2)) / (1 - wBig p M)) (div_nonneg hD0 h1w.le) hD hqnu hthr
  have hratio : 16 * ((1 / (2 * (M : ℝ) ^ 2)) / (1 - wBig p M)) * (N : ℝ)
      / ((ε - 2 * wBig p M) ^ 4 * (M : ℝ)) ≤ 1 / 2 := by
    have hkey : 16 * ((1 / (2 * (M : ℝ) ^ 2)) / (1 - wBig p M)) * (N : ℝ)
        / ((ε - 2 * wBig p M) ^ 4 * (M : ℝ))
        = ε ^ 4 / (4 * (1 - wBig p M) * (ε - 2 * wBig p M) ^ 4) := by
      have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
      have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
      have hSne : ε - 2 * wBig p M ≠ 0 := hε'pos.ne'
      have hden : 4 * (1 - wBig p M) * (ε - 2 * wBig p M) ^ 4 ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) h1w.ne') (pow_ne_zero 4 hSne)
      have hε4 : ε ^ 4 = 32 * (N : ℝ) / (M : ℝ) ^ 3 := by
        rw [hM3]
        field_simp [hNne]
      rw [eq_div_iff hden, hε4]
      field_simp
      ring
    rw [hkey]
    exact few_big_ratio ε (wBig p M) hε hε2 hw0 hw64
  have hPq : (1 : ℝ) / 2
      ≤ probSampleSumGe q M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)) := by
    simp only [probSampleSumGe]
    have hc := probEvent_compl (M := M) q
      (fun S => (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M) ≤ sampleSum q S)
    have hle : q.probEvent (L := M)
        (fun S => ¬ ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M) ≤ sampleSum q S))
        ≤ 1 / 2 := le_trans hcheb hratio
    linarith [hc, hle]

  have hPY : q.probEvent (L := M)
        (fun S => (∀ a, S a ∉ B) ∧
          ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M) ≤ sampleSum q S))
      = q.probEvent (L := M)
        (fun S => (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M) ≤ sampleSum q S) := by
    apply probEvent_congr_of_probOf_zero
    intro S hne
    by_cases hav : ∀ a, S a ∉ B
    · exact absurd (propext ⟨fun h => h.2, fun h => ⟨hav, h⟩⟩) hne
    · exact renormalizeOff_probOf_of_not_avoid p B hwB1 S hav
  have hPP' : q.probEvent (L := M)
        (fun S => (∀ a, S a ∉ B) ∧
          ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S))
      = q.probEvent (L := M)
        (fun S => (∀ a, S a ∉ B) ∧
          ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M) ≤ sampleSum q S)) := by
    apply probEvent_congr_of_probOf_zero
    intro S hne
    by_cases hav : ∀ a, S a ∉ B
    · exfalso
      apply hne
      apply propext
      constructor
      · intro h
        have hs := sampleSum_renormalizeOff p B hwB1 S hav
        have hle : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
            ≤ sampleSum p S / (1 - wBig p M) := by
          have hE : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
              = ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) / (1 - wBig p M) := by ring_nf
          rw [hE]
          exact div_le_div_of_nonneg_right h.2 h1w.le
        refine ⟨hav, ?_⟩
        rw [hs, hmass]
        exact hle
      · intro h
        have hs := sampleSum_renormalizeOff p B hwB1 S hav
        have hle : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S := by
          rw [hs, hmass] at h
          have hE : (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M)
              = ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) / (1 - wBig p M) := by ring_nf
          rw [hE] at h
          exact (div_le_div_iff_of_pos_right h1w).mp h.2
        exact ⟨hav, hle⟩
    · exact renormalizeOff_probOf_of_not_avoid p B hwB1 S hav
  have hcond := probEvent_avoid_eq p B hwB1 M
    (fun S => (∀ a, S a ∉ B) ∧
      ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S))
    (fun S hS => hS.1)
  have hmono : p.probEvent (L := M)
        (fun S => (∀ a, S a ∉ B) ∧
          ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S))
      ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := by
    simp only [probSampleSumGe]
    apply probEvent_mono
    intro S hS
    exact hS.2
  have hqY : (1 : ℝ) / 2 ≤ q.probEvent (L := M)
      (fun S => (1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) / (1 - wBig p M) ≤ sampleSum q S) := by
    simpa only [probSampleSumGe] using! hPq
  have hPr : (1 : ℝ) / 2 ≤ q.probEvent (L := M)
      (fun S => (∀ a, S a ∉ B) ∧
        ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)) := by
    rw [hPP', hPY]
    exact hqY
  have hprod : (1 - wBig p M) ^ M * (1 / 2)
      ≤ (1 - wBig p M) ^ M * q.probEvent (L := M)
          (fun S => (∀ a, S a ∉ B) ∧
            ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)) :=
    mul_le_mul_of_nonneg_left hPr (pow_nonneg h1w.le M)
  calc (1 - wBig p M) ^ M * (1 / 2)
      ≤ (1 - wBig p M) ^ M * q.probEvent (L := M)
          (fun S => (∀ a, S a ∉ B) ∧
            ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)) := hprod
    _ = p.probEvent (L := M)
          (fun S => (∀ a, S a ∉ B) ∧
            ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ) ≤ sampleSum p S)) := by
        rw [hcond, hmass]
    _ ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := hmono

theorem lemma4_few_big_exp [NeZero N] (p : Dist N) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hM : 0 < M)
    (hM3 : (M : ℝ) ^ 3 = 32 * (N : ℝ) / ε ^ 4)
    (hnu : nonuniform ε p) (hfew : fewBig p M ε)
    (hNlarge : (2 : ℝ) ^ 37 ≤ ε ^ 14 * (N : ℝ)) :
    (1 : ℝ) / 2 * Real.exp (-(2 * alpha ε))
      ≤ probSampleSumGe p M ((1 + ε ^ 2 / 2) * (M : ℝ) / (N : ℝ)) := by
  have hmain := lemma4_few_big p ε hε hε2 hM hM3 hnu hfew hNlarge
  have hw64 : wBig p M ≤ ε ^ 2 / 64 := wBig_le_eps_sq p ε hε hM hM3 hfew hNlarge
  have hw0 : 0 ≤ wBig p M := wBig_nonneg p M
  have hw12 : wBig p M ≤ 1 / 2 := by nlinarith [hw64, hε.le, hε2]
  have hg : Real.exp (-(2 * (M : ℝ) * wBig p M)) ≤ (1 - wBig p M) ^ M :=
    pow_one_sub_ge_exp_neg (wBig p M) hw0 hw12 M
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMw : (M : ℝ) * wBig p M ≤ alpha ε := by
    have h1 : (M : ℝ) * wBig p M ≤ (M : ℝ) * (alpha ε / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hfew hMpos.le
    have h2 : (M : ℝ) * (alpha ε / (M : ℝ)) = alpha ε := by
      field_simp
    linarith
  have hmono : Real.exp (-(2 * alpha ε)) ≤ Real.exp (-(2 * (M : ℝ) * wBig p M)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hMw]
  have hexp : Real.exp (-(2 * alpha ε)) ≤ (1 - wBig p M) ^ M := le_trans hmono hg
  have hhalf : (1 : ℝ) / 2 * Real.exp (-(2 * alpha ε))
      ≤ (1 - wBig p M) ^ M * (1 / 2) := by
    have := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith [this]
  linarith [hhalf, hmain]

end Qatlib.Papers.DistTesting09.MainResults.Uniformity
