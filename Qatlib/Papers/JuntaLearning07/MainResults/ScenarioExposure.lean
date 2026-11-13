/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.InfluenceIdentification
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# Exposing influential coordinates by Fourier sampling

This module bounds the probability that repeated Fourier samples fail to reveal a prescribed set
of influential coordinates in the learning and scenario arguments of [AticiServedio2007]. If
every coordinate in `J` has influence at least a positive `ε`, `exposure_union_bound` bounds the
probability that any coordinate remains unseen after `T` samples by `J.card * (1 - ε) ^ T`.

The exponential version `exposure_union_bound_exp` converts this to `J.card * exp (-(ε * T))`.
`exposure_success` then turns a failure bound of `1 / 10` into probability at least `9 / 10`
that every coordinate has appeared.

## Main statements

- `exposure_union_bound` combines individual miss probabilities by a union bound.
- `exposure_union_bound_exp` gives exponential decay with the number of samples.
* `exposure_success` guarantees simultaneous exposure with probability at least `9 / 10` under
  the stated numerical condition.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- If each coordinate in `J` has influence at least a positive `ε`, the probability that some
coordinate of `J` is absent from all `T` Fourier samples is at most `J.card * (1 - ε) ^ T`. -/
theorem exposure_union_bound {f : (Fin n → Bool) → Bool} {J : Finset (Fin n)}
    {ε : ℝ} (_hε : 0 < ε) (hinf : ∀ i ∈ J, ε ≤ boolInfluence f i) (T : ℕ) :
    fsProb f T (fun s => ∃ i ∈ J, ∀ t, i ∉ s t) ≤ (J.card : ℝ) * (1 - ε) ^ T := by
  classical
  have hmiss : fsProb f T (fun s => ∃ i ∈ J, ∀ t, i ∉ s t)
      ≤ ∑ i ∈ J, fsProb f T (fun s => ∀ t, i ∉ s t) :=
    fsProb_exists_le f T J (fun i s => ∀ t, i ∉ s t)
  have hterm : ∀ i ∈ J, fsProb f T (fun s => ∀ t, i ∉ s t) ≤ (1 - ε) ^ T := by
    intro i hi
    rw [fsProb_miss, sum_noHit_fsWeight]
    apply pow_le_pow_left₀
    · linarith [boolInfluence_le_one f i]
    · linarith [hinf i hi]
  calc fsProb f T (fun s => ∃ i ∈ J, ∀ t, i ∉ s t)
      ≤ ∑ i ∈ J, fsProb f T (fun s => ∀ t, i ∉ s t) := hmiss
    _ ≤ ∑ _i ∈ J, (1 - ε) ^ T := Finset.sum_le_sum hterm
    _ = (J.card : ℝ) * (1 - ε) ^ T := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- If each coordinate in `J` has influence at least a positive `ε`, the probability that some
coordinate is never sampled is at most `J.card * exp (-(ε * T))`. -/
theorem exposure_union_bound_exp {f : (Fin n → Bool) → Bool} {J : Finset (Fin n)}
    {ε : ℝ} (hε : 0 < ε) (hinf : ∀ i ∈ J, ε ≤ boolInfluence f i) (T : ℕ) :
    fsProb f T (fun s => ∃ i ∈ J, ∀ t, i ∉ s t) ≤ (J.card : ℝ) * Real.exp (-(ε * T)) := by
  have hbase := exposure_union_bound hε hinf T
  rcases Finset.eq_empty_or_nonempty J with hJ | hJ
  · rw [hJ] at hbase ⊢
    simpa using! hbase
  · obtain ⟨i, hi⟩ := hJ
    have hεle : ε ≤ 1 := le_trans (hinf i hi) (boolInfluence_le_one f i)
    have h0 : (0 : ℝ) ≤ 1 - ε := by linarith
    have hpow : (1 - ε) ^ T ≤ Real.exp (-(ε * T)) := by
      have hle : (1 - ε) ≤ Real.exp (-ε) := Real.one_sub_le_exp_neg ε
      have hpow1 : (1 - ε) ^ T ≤ Real.exp (-ε) ^ T := pow_le_pow_left₀ h0 hle T
      calc (1 - ε) ^ T ≤ Real.exp (-ε) ^ T := hpow1
        _ = Real.exp (-(ε * (T : ℝ))) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
    have hcard : (0 : ℝ) ≤ (J.card : ℝ) := by positivity
    calc fsProb f T (fun s => ∃ i ∈ J, ∀ t, i ∉ s t)
        ≤ (J.card : ℝ) * (1 - ε) ^ T := hbase
      _ ≤ (J.card : ℝ) * Real.exp (-(ε * T)) :=
          mul_le_mul_of_nonneg_left hpow hcard

/-- If every coordinate in `J` has influence at least a positive `ε` and `J.card * (1 - ε) ^ T ≤
1 / 10`, then all coordinates of `J` appear among the Fourier samples with probability at
least `9 / 10`. -/
theorem exposure_success {f : (Fin n → Bool) → Bool} {J : Finset (Fin n)}
    {ε : ℝ} (hε : 0 < ε) (hinf : ∀ i ∈ J, ε ≤ boolInfluence f i) {T : ℕ}
    (hT : (J.card : ℝ) * (1 - ε) ^ T ≤ 1 / 10) :
    (9 / 10 : ℝ) ≤ fsProb f T (fun s => ∀ i ∈ J, ∃ t, i ∈ s t) := by
  classical
  have hfail := exposure_union_bound hε hinf T
  have hcompl : fsProb f T (fun s => ¬ ∀ i ∈ J, ∃ t, i ∈ s t) =
      1 - fsProb f T (fun s => ∀ i ∈ J, ∃ t, i ∈ s t) :=
    fsProb_compl f T (fun s => ∀ i ∈ J, ∃ t, i ∈ s t)
  have hcongr : fsProb f T (fun s => ¬ ∀ i ∈ J, ∃ t, i ∈ s t) =
      fsProb f T (fun s => ∃ i ∈ J, ∀ t, i ∉ s t) :=
    fsProb_congr f T (fun s => by
      constructor
      · intro h
        by_contra hcon
        apply h
        intro i hi
        by_contra hni
        exact hcon ⟨i, hi, fun t ht => hni ⟨t, ht⟩⟩
      · rintro ⟨i, hi, h⟩ hcon
        obtain ⟨t, ht⟩ := hcon i hi
        exact h t ht)
  rw [← hcongr, hcompl] at hfail
  linarith

end Qatlib.Papers.JuntaLearning07.MainResults
