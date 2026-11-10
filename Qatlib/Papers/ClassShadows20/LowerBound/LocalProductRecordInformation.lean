/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qatlib.Papers.ClassShadows20.LowerBound
open Qatlib
open scoped Classical BigOperators

lemma local_log_ratio_upper (p w : ℝ) (hp : 0 ≤ p) (hw : 0 < w) :
    p * Real.log (p / w) ≤ p^2 / w - p := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp
  · calc
      _ ≤ p * (p / w - 1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos hp hw)) hp.le
      _ = _ := by ring

lemma local_moment_log_budget {I : Type} [Fintype I]
    (α p : I → ℝ) (hα : ∀ i, 0 ≤ α i) (hp : ∀ i, 0 ≤ p i)
    (w v : ℝ) (hw : 0 ≤ w)
    (hmean : ∑ i, α i * p i = w)
    (hsecond : ∑ i, α i * (p i)^2 ≤ w^2 * (1 + v)) :
    ∑ i, α i * (p i * Real.log (p i / w)) ≤ w * v := by
  rcases hw.eq_or_lt with hw | hw
  · rw [← hw] at hmean hsecond ⊢
    have hz : ∀ i, α i * p i = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j _ => mul_nonneg (hα j) (hp j))
        (Finset.mem_univ i)
      rw [hmean] at hi
      exact le_antisymm hi (mul_nonneg (hα i) (hp i))
    simp only [← mul_assoc, hz, zero_mul, Finset.sum_const_zero, le_refl]
  · calc
      _ ≤ ∑ i, α i * ((p i)^2 / w - p i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (local_log_ratio_upper _ _ (hp i) hw) (hα i)
      _ = (∑ i, α i * (p i)^2) / w - w := by
        simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib,
          ← Finset.sum_div, hmean]
      _ ≤ (w^2 * (1 + v)) / w - w := sub_le_sub_right
        (div_le_div_of_nonneg_right hsecond hw.le) w
      _ = w * v := by field_simp; ring

lemma local_entropy_score_bound {I : Type} [Fintype I]
    (p r c : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i)
    (hc : ∀ i, 0 < c i) (hsupport : ∀ i, 0 < p i → 0 < r i)
    (hpsum : ∑ i, p i = 1) (hscore : ∑ i, r i * c i ≤ 1) :
    ∑ i, p i * Real.log (c i) ≤ ∑ i, p i * Real.log (p i / r i) := by
  have hpoint : ∀ i, p i * Real.log (c i) + p i - r i * c i ≤
      p i * Real.log (p i / r i) := by
    intro i
    rcases (hp i).eq_or_lt with hpi | hpi
    · rw [← hpi]
      simpa using neg_nonpos.mpr (mul_nonneg (hr i) (hc i).le)
    · have hri := hsupport i hpi
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos hri (hc i)) hpi)
      have hh := mul_le_mul_of_nonneg_left hlog hpi.le
      rw [Real.log_div (mul_ne_zero hri.ne' (hc i).ne') hpi.ne',
        Real.log_mul hri.ne' (hc i).ne'] at hh
      rw [Real.log_div hpi.ne' hri.ne']
      have hdiv : p i * (r i * c i / p i - 1) = r i * c i - p i := by
        field_simp
      rw [hdiv] at hh
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hpsum] at hsum
  linarith

lemma local_entropy_event_lower {I : Type} [Fintype I]
    (p r : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 ≤ r i)
    (hsupport : ∀ i, 0 < p i → 0 < r i)
    (hpsum : ∑ i, p i = 1) (hrsum : ∑ i, r i = 1)
    (E : I → Prop) [DecidablePred E] (M : ℝ) (hM : 1 ≤ M)
    (hE : (∑ i ∈ Finset.univ.filter E, r i) = 1 / M) (δ : ℝ)
    (hgood : 1 - δ ≤ ∑ i ∈ Finset.univ.filter E, p i) :
    (1 - δ) * Real.log M - 1 ≤ ∑ i, p i * Real.log (p i / r i) := by
  have hm : 0 < M := lt_of_lt_of_le zero_lt_one hM
  let c : I → ℝ := fun i => if E i then M / 2 else 1 / 2
  have hc : ∀ i, 0 < c i := by intro i; dsimp [c]; split_ifs <;> positivity
  have hrpoint : ∀ i, r i * c i = ((M - 1) / 2) * (if E i then r i else 0) + (1/2)*r i := by
    intro i
    dsimp [c]
    split_ifs <;> ring
  have hscore : ∑ i, r i * c i ≤ 1 := by
    simp_rw [hrpoint]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.sum_filter, hE, hrsum]
    have heq : (M - 1)/2*(1/M)+(1/2)*1 = 1-1/(2*M) := by field_simp; ring
    rw [heq]
    have : 0 ≤ 1/(2*M) := by positivity
    linarith
  have h := local_entropy_score_bound p r c hp hr hc hsupport hpsum hscore
  have hloghalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have hppoint : ∀ i, p i * Real.log (c i) =
      (if E i then p i else 0) * Real.log M - p i * Real.log 2 := by
    intro i
    dsimp [c]
    split_ifs
    · rw [Real.log_div hm.ne' (by norm_num)]
      ring
    · rw [hloghalf]
      ring
  simp_rw [hppoint] at h
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.sum_filter, hpsum, one_mul] at h
  have hl : 0 ≤ Real.log M := Real.log_nonneg hM
  have hgood' := mul_le_mul_of_nonneg_right hgood hl
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this
    exact this
  linarith

lemma local_product_log_ratio {N : ℕ} {O : Type} [Fintype O] [DecidableEq O]
    (q w : Fin N → FinDist O)
    (hsupport : ∀ j o, 0 < (q j).prob o → 0 < (w j).prob o) :
    (∑ ω, (independentSampleLaw q).prob ω *
      Real.log ((independentSampleLaw q).prob ω / (independentSampleLaw w).prob ω)) =
      ∑ j, ∑ o, (q j).prob o * Real.log ((q j).prob o / (w j).prob o) := by
  have hpoint : ∀ ω,
      (independentSampleLaw q).prob ω *
        Real.log ((independentSampleLaw q).prob ω / (independentSampleLaw w).prob ω) =
      (independentSampleLaw q).prob ω *
        (∑ j, Real.log ((q j).prob (ω j) / (w j).prob (ω j))) := by
    intro ω
    by_cases hz : (independentSampleLaw q).prob ω = 0
    · simp [hz]
    · have hq : ∀ j, (q j).prob (ω j) ≠ 0 := by
        intro j hj
        apply hz
        exact Finset.prod_eq_zero (Finset.mem_univ j) hj
      have hw : ∀ j, (w j).prob (ω j) ≠ 0 := by
        intro j
        exact (hsupport j (ω j) (lt_of_le_of_ne ((q j).nonneg _) (Ne.symm (hq j)))).ne'
      congr 1
      change Real.log ((∏ j, (q j).prob (ω j)) / (∏ j, (w j).prob (ω j))) = _
      rw [← Finset.prod_div_distrib, Real.log_prod (fun j _ => div_ne_zero (hq j) (hw j))]
  simp_rw [hpoint, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact independentSampleLaw_expect_coord q j (fun o => Real.log ((q j).prob o / (w j).prob o))

lemma local_product_record_moment_fano_supported
    (M N : ℕ) (U O : Type) [Fintype U] [Fintype O]
    (μ : FinDist U) (w : Fin N → FinDist O)
    (q : Fin M → U → Fin N → FinDist O) (v δ : ℝ) (hv : 0 ≤ v)
    (hmean : ∀ j o, (1 / (M : ℝ)) * ∑ x, ∑ u, μ.prob u * (q x u j).prob o = (w j).prob o)
    (hsecond : ∀ j o, (1 / (M : ℝ)) * ∑ x, ∑ u,
      μ.prob u * ((q x u j).prob o)^2 ≤ ((w j).prob o)^2 * (1 + v))
    (dec : U → (Fin N → O) → Fin M)
    (hgood : ∀ x u, 0 < μ.prob u → 1 - δ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => dec u ω = x),
      ∏ j, (q x u j).prob (ω j)) :
    (N : ℝ) * v ≥ (1 - δ) * Real.log (M : ℝ) - 1 := by
  classical
  by_cases hM : M ≤ 1
  · have hm : M = 0 ∨ M = 1 := by omega
    rcases hm with rfl | rfl <;> simp only [Nat.cast_zero, Nat.cast_one,
      Real.log_zero, Real.log_one, mul_zero, zero_sub]
    all_goals have hnv : 0 ≤ (N:ℝ)*v := mul_nonneg (Nat.cast_nonneg N) hv
    all_goals linarith
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  let α : Fin M × U → ℝ := fun i => μ.prob i.2 / M
  have hα : ∀ i, 0 ≤ α i := fun i => div_nonneg (μ.nonneg i.2) hMpos.le
  have hαsum : ∑ i, α i = 1 := by
    simp only [α, Fintype.sum_prod_type, ← Finset.sum_div, μ.sum_one]
    simp [hMpos.ne']
  have hmean' : ∀ j o, (∑ i, α i * (q i.1 i.2 j).prob o) = (w j).prob o := by
    intro j o
    simp only [α, Fintype.sum_prod_type, div_mul_eq_mul_div, ← Finset.sum_div]
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hmean j o
  have hsecond' : ∀ j o, (∑ i, α i * ((q i.1 i.2 j).prob o)^2) ≤ ((w j).prob o)^2 * (1 + v) := by
    intro j o
    simp only [α, Fintype.sum_prod_type, div_mul_eq_mul_div, ← Finset.sum_div]
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hsecond j o
  have hsupport : ∀ i, 0 < α i → ∀ j o, 0 < (q i.1 i.2 j).prob o → 0 < (w j).prob o := by
    intro i hi j o hq
    have hh := Finset.single_le_sum
      (fun z _ => mul_nonneg (hα z) ((q z.1 z.2 j).nonneg o)) (Finset.mem_univ i)
    rw [hmean' j o] at hh
    exact lt_of_lt_of_le (mul_pos hi hq) hh
  have hshot : ∀ j, ∑ i, α i * (∑ o,
      (q i.1 i.2 j).prob o * Real.log ((q i.1 i.2 j).prob o / (w j).prob o)) ≤ v := by
    intro j
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ o, (w j).prob o * v := by
        apply Finset.sum_le_sum
        intro o _
        exact local_moment_log_budget α (fun i => (q i.1 i.2 j).prob o) hα
          (fun i => (q i.1 i.2 j).nonneg o) _ _ ((w j).nonneg o)
          (hmean' j o) (hsecond' j o)
      _ = v := by rw [← Finset.sum_mul, (w j).sum_one, one_mul]
  let Q : Fin M × U → FinDist (Fin N → O) := fun i => independentSampleLaw (q i.1 i.2)
  let R : FinDist (Fin N → O) := independentSampleLaw w
  have hrecord : ∑ i, α i * (∑ ω, (Q i).prob ω * Real.log ((Q i).prob ω / R.prob ω)) ≤ (N : ℝ)*v := by
    have hi : ∀ i, α i * (∑ ω, (Q i).prob ω * Real.log ((Q i).prob ω / R.prob ω)) =
        α i * (∑ j, ∑ o, (q i.1 i.2 j).prob o * Real.log ((q i.1 i.2 j).prob o / (w j).prob o)) := by
      intro i
      by_cases hz : α i = 0
      · simp [hz]
      · rw [local_product_log_ratio (q i.1 i.2) w (hsupport i (lt_of_le_of_ne (hα i) (Ne.symm hz)))]
    simp_rw [hi]
    rw [Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _), Finset.sum_comm]
    calc
      _ ≤ ∑ _j : Fin N, v := Finset.sum_le_sum (fun j _ => hshot j)
      _ = _ := by simp
  let p : (Fin M × U) × (Fin N → O) → ℝ := fun z => α z.1 * (Q z.1).prob z.2
  let r : (Fin M × U) × (Fin N → O) → ℝ := fun z => α z.1 * R.prob z.2
  have hp : ∀ z, 0 ≤ p z := fun z => mul_nonneg (hα z.1) ((Q z.1).nonneg z.2)
  have hr : ∀ z, 0 ≤ r z := fun z => mul_nonneg (hα z.1) (R.nonneg z.2)
  have hpsum : ∑ z, p z = 1 := by
    simp only [p, Fintype.sum_prod_type, ← Finset.mul_sum, FinDist.sum_one, mul_one, hαsum]
  have hrsum : ∑ z, r z = 1 := by
    simp only [r, Fintype.sum_prod_type, ← Finset.mul_sum, FinDist.sum_one, mul_one, hαsum]
  have hsupportjoint : ∀ z, 0 < p z → 0 < r z := by
    intro z hz
    have hai : 0 < α z.1 := pos_of_mul_pos_left hz ((Q z.1).nonneg z.2)
    have hqi : 0 < (Q z.1).prob z.2 := pos_of_mul_pos_right hz (hα z.1)
    apply mul_pos hai
    change 0 < ∏ j, (w j).prob (z.2 j)
    apply Finset.prod_pos
    intro j _
    apply hsupport z.1 hai
    have hn : (q z.1.1 z.1.2 j).prob (z.2 j) ≠ 0 := by
      intro hn
      have hzero : (Q z.1).prob z.2 = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hn
      exact hqi.ne' hzero
    exact lt_of_le_of_ne ((q z.1.1 z.1.2 j).nonneg _) (Ne.symm hn)

  have hjoint : (∑ z, p z * Real.log (p z / r z)) ≤ (N : ℝ)*v := by
    have hi : ∀ z, p z * Real.log (p z / r z) =
        α z.1 * ((Q z.1).prob z.2 * Real.log ((Q z.1).prob z.2 / R.prob z.2)) := by
      intro z
      by_cases hz : α z.1 = 0
      · simp [p, r, hz]
      · dsimp [p, r]
        rw [mul_div_mul_left _ _ hz]
        ring
    simp_rw [hi]
    simpa only [Fintype.sum_prod_type, ← Finset.mul_sum] using hrecord
  let E : ((Fin M × U) × (Fin N → O)) → Prop := fun z => dec z.1.2 z.2 = z.1.1
  have hE : ∑ z ∈ Finset.univ.filter E, r z = 1/(M:ℝ) := by
    rw [Finset.sum_filter]
    simp only [r, α, Fintype.sum_prod_type]
    change (∑ x, ∑ u, ∑ ω, if dec u ω = x then μ.prob u / M * R.prob ω else 0) = _
    rw [Finset.sum_comm]
    have hswap : ∀ u, (∑ x, ∑ ω, if dec u ω = x then μ.prob u / M * R.prob ω else 0) =
        ∑ ω, ∑ x, if dec u ω = x then μ.prob u / M * R.prob ω else 0 := fun u => Finset.sum_comm
    simp_rw [hswap]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [← Finset.mul_sum, R.sum_one, mul_one, ← Finset.sum_div, μ.sum_one]
  have hgoodjoint : 1-δ ≤ ∑ z ∈ Finset.univ.filter E, p z := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    have hsum : (∑ i, ∑ ω, if E (i,ω) then p (i,ω) else 0) =
        ∑ i, α i * (∑ ω ∈ Finset.univ.filter (fun ω => dec i.2 ω = i.1), (Q i).prob ω) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      dsimp [E, p]
      split_ifs <;> simp
    rw [hsum]
    calc
      _ = ∑ i, α i * (1-δ) := by rw [← Finset.sum_mul, hαsum, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hz : α i = 0
        · simp [hz]
        · have hai : 0 < α i := lt_of_le_of_ne (hα i) (Ne.symm hz)
          have hμi : 0 < μ.prob i.2 := (div_pos_iff_of_pos_right hMpos).mp hai
          exact mul_le_mul_of_nonneg_left (hgood i.1 i.2 hμi) (hα i)
  have hl := local_entropy_event_lower p r hp hr hsupportjoint hpsum hrsum E
    (M:ℝ) (by exact_mod_cast (by omega : 1 ≤ M)) hE δ hgoodjoint
  exact hl.trans hjoint

theorem local_product_record_moment_fano :
∀ (M N : ℕ) (U O : Type) [Fintype U] [Fintype O]
    (μ : FinDist U) (w : Fin N → FinDist O)
    (q : Fin M → U → Fin N → FinDist O) (v δ : ℝ), 0 ≤ v →
    (∀ j o, (1 / (M : ℝ)) * ∑ x, ∑ u, μ.prob u * (q x u j).prob o = (w j).prob o) →
    (∀ j o, (1 / (M : ℝ)) * ∑ x, ∑ u,
      μ.prob u * ((q x u j).prob o)^2 ≤ ((w j).prob o)^2 * (1 + v)) →
    ∀ dec : U → (Fin N → O) → Fin M,
    (∀ x u, 1 - δ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => dec u ω = x),
      ∏ j, (q x u j).prob (ω j)) →
    (N : ℝ) * v ≥ (1 - δ) * Real.log (M : ℝ) - 1 := by
  intro M N U O _ _ μ w q v δ hv hm hs dec hg
  exact local_product_record_moment_fano_supported M N U O μ w q v δ hv hm hs dec
    (fun x u _ => hg x u)
end Qatlib.Papers.ClassShadows20.LowerBound
