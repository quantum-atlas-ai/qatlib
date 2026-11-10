/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.FSOracleDefs
import Qatlib.Papers.JuntaLearning07.MainResults.ParsevalIdentity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped BigOperators

variable {n : ℕ}

def noHitSet (n : ℕ) (i : Fin n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => i ∉ S)

@[simp] theorem mem_noHitSet {n : ℕ} {i : Fin n} {S : Finset (Fin n)} :
    S ∈ noHitSet n i ↔ i ∉ S := by
  simp [noHitSet]

theorem fsProb_eq_sum (f : (Fin n → Bool) → Bool) (T : ℕ)
    (E : (Fin T → Finset (Fin n)) → Prop) [DecidablePred E] :
    fsProb f T E =
      ∑ s : Fin T → Finset (Fin n), (if E s then ∏ t : Fin T, fsWeight f (s t) else 0) := by
  classical
  simp only [fsProb]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : E s <;> simp [h]

theorem fsProb_univ_one (f : (Fin n → Bool) → Bool) (T : ℕ) :
    (∑ s : Fin T → Finset (Fin n), ∏ t : Fin T, fsWeight f (s t)) = 1 := by
  classical
  have huniv : Fintype.piFinset (fun _ : Fin T => (Finset.univ : Finset (Finset (Fin n))))
      = (Finset.univ : Finset (Fin T → Finset (Fin n))) := by
    ext s
    simp
  rw [huniv.symm]
  rw [Finset.sum_prod_piFinset]
  simp [fsWeight_total f]

theorem fsProb_true (f : (Fin n → Bool) → Bool) (T : ℕ) :
    fsProb f T (fun _ => True) = 1 := by
  classical
  rw [fsProb_eq_sum]
  rw [show (∑ s : Fin T → Finset (Fin n),
          (if (fun _ => True) s then ∏ t : Fin T, fsWeight f (s t) else 0))
        = ∑ s : Fin T → Finset (Fin n), ∏ t : Fin T, fsWeight f (s t) from by
      apply Finset.sum_congr rfl
      intro s _
      simp]
  exact fsProb_univ_one f T

theorem fsProb_mono (f : (Fin n → Bool) → Bool) (T : ℕ)
    {E E' : (Fin T → Finset (Fin n)) → Prop} (h : ∀ s, E s → E' s) :
    fsProb f T E ≤ fsProb f T E' := by
  classical
  rw [fsProb_eq_sum, fsProb_eq_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hE : E s
  · rw [if_pos hE, if_pos (h s hE)]
  · rw [if_neg hE]
    by_cases hE' : E' s
    · rw [if_pos hE']
      exact Finset.prod_nonneg (fun t _ => fsWeight_nonneg f (s t))
    · rw [if_neg hE']

theorem fsProb_congr (f : (Fin n → Bool) → Bool) (T : ℕ)
    {E E' : (Fin T → Finset (Fin n)) → Prop} (h : ∀ s, E s ↔ E' s) :
    fsProb f T E = fsProb f T E' := by
  classical
  rw [fsProb_eq_sum, fsProb_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hE : E s
  · rw [if_pos hE, if_pos ((h s).mp hE)]
  · rw [if_neg hE, if_neg (fun h' => hE ((h s).mpr h'))]

theorem fsProb_exists_le (f : (Fin n → Bool) → Bool) (T : ℕ) (I : Finset (Fin n))
    (P : Fin n → (Fin T → Finset (Fin n)) → Prop) :
    fsProb f T (fun s => ∃ i ∈ I, P i s) ≤ ∑ i ∈ I, fsProb f T (P i) := by
  classical
  set E : (Fin T → Finset (Fin n)) → Prop := fun s => ∃ i ∈ I, P i s with hE
  have step : ∀ s : Fin T → Finset (Fin n),
      (if E s then ∏ t : Fin T, fsWeight f (s t) else 0)
        ≤ ∑ i ∈ I, (if P i s then ∏ t : Fin T, fsWeight f (s t) else 0) := by
    intro s
    simp only [hE]
    by_cases h : ∃ i ∈ I, P i s
    · rw [if_pos h]
      obtain ⟨i0, hi0, hP0⟩ := h
      have hnn : ∀ i ∈ I, 0 ≤ (if P i s then ∏ t : Fin T, fsWeight f (s t) else 0) := by
        intro i _
        by_cases hP : P i s
        · rw [if_pos hP]; exact Finset.prod_nonneg (fun t _ => fsWeight_nonneg f (s t))
        · rw [if_neg hP]
      calc ∏ t : Fin T, fsWeight f (s t)
          = (if P i0 s then ∏ t : Fin T, fsWeight f (s t) else 0) := by rw [if_pos hP0]
        _ ≤ ∑ i ∈ I, (if P i s then ∏ t : Fin T, fsWeight f (s t) else 0) :=
            Finset.single_le_sum hnn hi0
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun i _ => by
        by_cases hP : P i s
        · rw [if_pos hP]; exact Finset.prod_nonneg (fun t _ => fsWeight_nonneg f (s t))
        · rw [if_neg hP])
  conv_lhs => rw [fsProb_eq_sum]
  calc (∑ s : Fin T → Finset (Fin n),
          (if E s then ∏ t : Fin T, fsWeight f (s t) else 0))
      ≤ ∑ s : Fin T → Finset (Fin n),
          ∑ i ∈ I, (if P i s then ∏ t : Fin T, fsWeight f (s t) else 0) :=
          Finset.sum_le_sum (fun s _ => step s)
    _ = ∑ i ∈ I, ∑ s : Fin T → Finset (Fin n),
          (if P i s then ∏ t : Fin T, fsWeight f (s t) else 0) := Finset.sum_comm
    _ = ∑ i ∈ I, fsProb f T (P i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [fsProb_eq_sum]

theorem fsProb_compl (f : (Fin n → Bool) → Bool) (T : ℕ)
    (E : (Fin T → Finset (Fin n)) → Prop) :
    fsProb f T (fun s => ¬ E s) = 1 - fsProb f T E := by
  classical
  have hsum : fsProb f T (fun s => ¬ E s) + fsProb f T E = 1 := by
    rw [fsProb_eq_sum, fsProb_eq_sum]
    rw [← Finset.sum_add_distrib]
    rw [show (∑ s : Fin T → Finset (Fin n),
        ((if ¬ E s then ∏ t : Fin T, fsWeight f (s t) else 0) +
          (if E s then ∏ t : Fin T, fsWeight f (s t) else 0)))
        = ∑ s : Fin T → Finset (Fin n), ∏ t : Fin T, fsWeight f (s t) from by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hE : E s <;> simp [hE]]
    exact fsProb_univ_one f T
  linarith

theorem fsProb_miss (f : (Fin n → Bool) → Bool) (i : Fin n) (T : ℕ) :
    fsProb f T (fun s => ∀ t, i ∉ s t) =
      (∑ S ∈ noHitSet n i, fsWeight f S) ^ T := by
  classical
  set E : (Fin T → Finset (Fin n)) → Prop := fun s => ∀ t, i ∉ s t with hE
  have hpi : Finset.univ.filter E = Fintype.piFinset (fun _ : Fin T => noHitSet n i) := by
    ext s
    rw [Finset.mem_filter]
    simp [hE, noHitSet, Fintype.mem_piFinset]
  rw [fsProb_eq_sum]
  rw [Finset.sum_pow']
  have hLHS : (∑ s : Fin T → Finset (Fin n),
        (if E s then ∏ t : Fin T, fsWeight f (s t) else 0))
      = ∑ s ∈ Fintype.piFinset (fun _ : Fin T => noHitSet n i),
          ∏ t : Fin T, fsWeight f (s t) := by
    rw [← Finset.sum_filter]
    rw [hpi]
  rw [hLHS]

theorem sum_noHit_fsWeight (f : (Fin n → Bool) → Bool) (i : Fin n) :
    ∑ S ∈ noHitSet n i, fsWeight f S = 1 - boolInfluence f i := by
  classical
  have htotal := fsWeight_total f
  have hinf := boolInfluence_eq_sum_fsWeight f i
  have hnoHit : ∑ S ∈ noHitSet n i, fsWeight f S
      = ∑ S : Finset (Fin n), (if i ∈ S then 0 else fsWeight f S) := by
    simp only [noHitSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : i ∈ S <;> simp [h]
  have hsub : (∑ S : Finset (Fin n), (if i ∈ S then 0 else fsWeight f S))
      = (∑ S : Finset (Fin n), fsWeight f S)
        - ∑ S : Finset (Fin n), (if i ∈ S then fsWeight f S else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : i ∈ S <;> simp [h]
  rw [hnoHit, hsub, htotal, hinf]

theorem boolInfluence_le_one (f : (Fin n → Bool) → Bool) (i : Fin n) :
    boolInfluence f i ≤ 1 := by
  unfold boolInfluence uniformExpect
  have hsum_le : (∑ x : Fin n → Bool,
        (if f x = f (cubeFlip x i) then (0 : ℝ) else 1))
      ≤ ∑ _x : Fin n → Bool, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro x _
    split_ifs <;> norm_num
  have hcard : (∑ _x : Fin n → Bool, (1 : ℝ)) = (2 : ℝ) ^ n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
    simp
  rw [hcard] at hsum_le
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool,
          (if f x = f (cubeFlip x i) then (0 : ℝ) else 1)
      ≤ ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n := by
        apply mul_le_mul_of_nonneg_left hsum_le
        positivity
    _ = 1 := by rw [inv_mul_cancel₀ (by positivity)]

theorem boolInfluence_eq_zero_of_not_depends {I : Finset (Fin n)}
    {f : (Fin n → Bool) → Bool} (hdep : dependsOnlyOn I f) {i : Fin n}
    (hi : i ∉ I) : boolInfluence f i = 0 := by
  classical
  unfold boolInfluence uniformExpect
  have hzero : ∀ x : Fin n → Bool, f (cubeFlip x i) = f x := by
    intro x
    exact hdep _ _ (by
      intro j hj
      have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
      simp [cubeFlip, hji])
  simp [hzero]

theorem transcriptUnion_pos_influence {N : ℕ} {f : (Fin n → Bool) → Bool}
    (s : Fin N → Finset (Fin n)) (hpos : ∀ t, 0 < fsWeight f (s t)) :
    ∀ j ∈ transcriptUnion s, 0 < boolInfluence f j := by
  intro j hj
  rw [mem_transcriptUnion] at hj
  obtain ⟨t, ht⟩ := hj
  exact boolInfluence_pos_of_mem_fsWeight f ht (hpos t)

theorem influence_identification_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (I : Finset (Fin n)),
      dependsOnlyOn I f → 0 < I.card →
      ∃ N : ℕ, (N : ℝ) ≤ C * ε⁻¹ * (Real.log (I.card : ℝ) + 1) ∧
        (9 / 10 : ℝ) ≤ fsProb f N
          (fun s => ∀ i : Fin n, ε ≤ boolInfluence f i → i ∈ transcriptUnion s) ∧
        (∀ s : Fin N → Finset (Fin n), (∀ t, 0 < fsWeight f (s t)) →
          ∀ j ∈ transcriptUnion s, 0 < boolInfluence f j) := by
  refine ⟨100, by norm_num, ?_⟩
  intro n f I hdep hI

  set L : ℝ := Real.log (10 * (I.card : ℝ)) with hL
  set x : ℝ := ε⁻¹ * L with hx
  set N : ℕ := ⌈x⌉₊ with hN
  have hIpos : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hI
  have hI1 : (1 : ℝ) ≤ (I.card : ℝ) := by
    have h : 1 ≤ I.card := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hI)
    exact_mod_cast h
  have hlogI : 0 ≤ Real.log (I.card : ℝ) := Real.log_nonneg hI1
  have hLnonneg : 0 ≤ L := by
    rw [hL]
    apply Real.log_nonneg
    nlinarith [hI1]
  have hinvpos : 0 < ε⁻¹ := by positivity
  have hxnonneg : 0 ≤ x := by
    rw [hx]
    exact mul_nonneg (le_of_lt hinvpos) hLnonneg
  have hinvge : 1 ≤ ε⁻¹ := by
    rw [← one_div]
    exact (one_le_div hε).mpr hε1
  have hNge : x ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil x
  have hNlt : (N : ℝ) < x + 1 := by rw [hN]; exact Nat.ceil_lt_add_one hxnonneg

  have hlogmul : Real.log (10 * (I.card : ℝ))
      = Real.log 10 + Real.log (I.card : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hIpos)]
  have hlog10 : Real.log 10 ≤ 9 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 by norm_num)
    linarith
  have hNbound : (N : ℝ) ≤ 100 * ε⁻¹ * (Real.log (I.card : ℝ) + 1) := by
    have h1 : (N : ℝ) ≤ x + 1 := le_of_lt hNlt
    have h2 : x = ε⁻¹ * (Real.log 10 + Real.log (I.card : ℝ)) := by
      rw [hx, hL, hlogmul]
    have h3 : ε⁻¹ * (Real.log 10 + Real.log (I.card : ℝ))
        ≤ ε⁻¹ * (9 + Real.log (I.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hinvpos)
    calc (N : ℝ) ≤ x + 1 := h1
      _ = ε⁻¹ * (Real.log 10 + Real.log (I.card : ℝ)) + 1 := by rw [h2]
      _ ≤ ε⁻¹ * (9 + Real.log (I.card : ℝ)) + ε⁻¹ := by linarith
      _ = ε⁻¹ * ((9 + Real.log (I.card : ℝ)) + 1) := by ring
      _ ≤ ε⁻¹ * (100 * (Real.log (I.card : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hinvpos)
          nlinarith [hlogI]
      _ = 100 * ε⁻¹ * (Real.log (I.card : ℝ) + 1) := by ring

  have htail : (1 - ε) ^ N ≤ 1 / (10 * (I.card : ℝ)) := by
    have hbase : 1 - ε ≤ Real.exp (-ε) := by
      linarith [Real.add_one_le_exp (-ε)]
    have hbase_nonneg : 0 ≤ 1 - ε := by linarith
    have hstep1 : (1 - ε) ^ N ≤ (Real.exp (-ε)) ^ N :=
      pow_le_pow_left₀ hbase_nonneg hbase N
    have hstep2 : (Real.exp (-ε)) ^ N = Real.exp (-(ε * (N : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hlogle : L ≤ ε * (N : ℝ) := by
      have hmul : ε * x ≤ ε * (N : ℝ) := mul_le_mul_of_nonneg_left hNge (le_of_lt hε)
      have hxe : ε * x = L := by
        rw [hx, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
      rwa [hxe] at hmul
    have hexp_le : Real.exp (-(ε * (N : ℝ))) ≤ Real.exp (-L) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hexpL : Real.exp (-L) = 1 / (10 * (I.card : ℝ)) := by
      rw [hL, Real.exp_neg, Real.exp_log (show (0 : ℝ) < 10 * (I.card : ℝ) by positivity),
        one_div]
    calc (1 - ε) ^ N ≤ (Real.exp (-ε)) ^ N := hstep1
      _ = Real.exp (-(ε * (N : ℝ))) := hstep2
      _ ≤ Real.exp (-L) := hexp_le
      _ = 1 / (10 * (I.card : ℝ)) := hexpL

  have hfail_le : fsProb f N
      (fun s => ¬ (∀ i : Fin n, ε ≤ boolInfluence f i → i ∈ transcriptUnion s)) ≤ 1 / 10 := by

    have hneg : ∀ s : Fin N → Finset (Fin n),
        (¬ (∀ i : Fin n, ε ≤ boolInfluence f i → i ∈ transcriptUnion s))
          ↔ ∃ i ∈ I, ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s := by
      intro s
      constructor
      · intro h
        push Not at h
        obtain ⟨i, hi, hmem⟩ := h
        refine ⟨i, ?_, hi, hmem⟩
        by_contra hni
        have hz : boolInfluence f i = 0 := boolInfluence_eq_zero_of_not_depends hdep hni
        rw [hz] at hi
        linarith
      · rintro ⟨i, _, hi, hmem⟩ hcon
        exact hmem (hcon i hi)
    rw [fsProb_congr f N hneg]
    have hunion : fsProb f N
        (fun s => ∃ i ∈ I, ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s)
        ≤ ∑ i ∈ I, fsProb f N (fun s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s) :=
      fsProb_exists_le f N I (fun i s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s)
    have hterm : ∀ i ∈ I,
        fsProb f N (fun s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s)
          ≤ (1 - ε) ^ N := by
      intro i _
      by_cases hInf : ε ≤ boolInfluence f i
      · calc fsProb f N (fun s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s)
            ≤ fsProb f N (fun s => i ∉ transcriptUnion s) :=
              fsProb_mono f N (E := fun s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s)
                (E' := fun s => i ∉ transcriptUnion s) (fun s hs => hs.2)
          _ = fsProb f N (fun s => ∀ t, i ∉ s t) :=
              fsProb_congr f N (fun s => by rw [mem_transcriptUnion]; simp)
          _ = (∑ S ∈ noHitSet n i, fsWeight f S) ^ N := fsProb_miss f i N
          _ = (1 - boolInfluence f i) ^ N := by rw [sum_noHit_fsWeight]
          _ ≤ (1 - ε) ^ N :=
              pow_le_pow_left₀ (by linarith [boolInfluence_le_one f i]) (by linarith) N
      · have hzero : fsProb f N
            (fun s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s) = 0 := by
          rw [fsProb_eq_sum]
          apply Finset.sum_eq_zero
          intro s _
          rw [if_neg]
          exact fun h => hInf h.1
        rw [hzero]
        exact pow_nonneg (by linarith) N
    calc fsProb f N
          (fun s => ∃ i ∈ I, ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s)
        ≤ ∑ i ∈ I, fsProb f N (fun s => ε ≤ boolInfluence f i ∧ i ∉ transcriptUnion s) :=
          hunion
      _ ≤ ∑ i ∈ I, (1 - ε) ^ N := Finset.sum_le_sum hterm
      _ = (I.card : ℝ) * (1 - ε) ^ N := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (I.card : ℝ) * (1 / (10 * (I.card : ℝ))) := by
          apply mul_le_mul_of_nonneg_left htail
          positivity
      _ = 1 / 10 := by
          have hne : (I.card : ℝ) ≠ 0 := ne_of_gt hIpos
          field_simp
  refine ⟨N, hNbound, ?_, ?_⟩
  · have hc := fsProb_compl f N
      (fun s => ∀ i : Fin n, ε ≤ boolInfluence f i → i ∈ transcriptUnion s)
    rw [hc] at hfail_le
    linarith
  · intro s hpos
    exact transcriptUnion_pos_influence s hpos

end Qatlib.Papers.JuntaLearning07.MainResults
