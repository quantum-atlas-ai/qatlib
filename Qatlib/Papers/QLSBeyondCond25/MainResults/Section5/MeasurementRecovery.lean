/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper layer for *A New Quantum Algorithm for Linear Systems beyond the Condition Number*
(QLSBeyondCond25), fixed source version arXiv:2510.05588v3.

This file covers c011, Lemma 5.6 (page 29-30), *Recovery of Boolean Solution via Measurements*:
for a hidden set `S ⊆ U` of size `h`, measuring the state
`|z⟩ = (1/√h) Σ_{i=1}^h |H_i⟩` with `|H_i⟩ = (1/√C(h,i)) Σ_{T ∈ S_i} |T⟩` returns a uniformly
random nonempty subset `T ⊆ S`; each `x ∈ S` is contained in the outcome with probability
`(h+1)/(2h) > 1/2` (page 29), hence `t = O(log(n/δ))` measurements recover `S` with probability
at least `1 - δ` (page 30, geometric tail plus union bound).

Formalised content:

* `lemma56_inclusion_probability` — the probability computation
  `Σ_{i<h} (1/h)·((i+1)/h) = (h+1)/(2h)` (page 29);
* `lemma56_union_bound` — the union bound
  `Pr[∃x ∈ S missed] ≤ Σ_{x∈S} Pr[x missed]` for an arbitrary finite weights family;
* `lemma56_sample_count` — the sample-count computation `h·(1-p)^t ≤ δ` for `t ≥ log₂(n/δ)`
  and `p ≥ 1/2`, `h ≤ n` (page 30);
* `lemma56_measurement_recovery` — Lemma 5.6 proper, combining the three above.

The independence of the measurements enters only through the hypothesis `hmiss` (per-element miss
probability after `t` independent samples equals `(1-p)^t`); the paper's measurement model is not
formalised as a probability space, see the docstrings.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Classical

namespace Qatlib.Papers.QLSBeyondCond25.MainResults.Section5

/-! ## The inclusion probability (page 29) -/

/-- Lemma 5.6, probability computation (page 29): a uniformly random size-`i` subset of a set of
size `h` contains a fixed element with probability `i/h`, and `i` is uniform on `{1,…,h}`, so
`Pr[x ∈ T] = Σ_{i=1}^{h} (1/h)·(i/h) = (h+1)/(2h)`. -/
theorem lemma56_inclusion_probability (h : ℕ) (hh : 1 ≤ h) :
    (∑ i ∈ Finset.range h, (1 / (h : ℝ)) * (((i : ℝ) + 1) / (h : ℝ)))
      = ((h : ℝ) + 1) / (2 * (h : ℝ)) := by
  have hhR : (h : ℝ) ≠ 0 := by
    have : h ≠ 0 := by omega
    exact_mod_cast this
  have hid : ∀ m : ℕ, (∑ i ∈ Finset.range m, ((i : ℝ) + 1)) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hstep : (∑ i ∈ Finset.range h, (1 / (h : ℝ)) * (((i : ℝ) + 1) / (h : ℝ)))
      = (1 / (h : ℝ) ^ 2) * (∑ i ∈ Finset.range h, ((i : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hstep, hid h]
  field_simp

/-! ## The union bound (page 30) -/

/-- An element `x` is *never measured* by the outcome sequence `σ` (an outcome per measurement). -/
def MissedAll {α ι : Type*} (x : α) (σ : ι → Finset α) : Prop := ∀ j, x ∉ σ j

/-- Union bound at the end of the proof of Lemma 5.6 (page 30): for nonnegative weights `w` on a
finite outcome space, the probability of the event "some `x ∈ S` never occurs" is at most the sum
over `x ∈ S` of the probabilities that `x` never occurs. -/
theorem lemma56_union_bound {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset α) (w : β → ℝ) (miss : α → β → Prop)
    (hw : ∀ b, 0 ≤ w b) :
    (∑ b ∈ Finset.univ.filter (fun b => ∃ x ∈ S, miss x b), w b)
      ≤ ∑ x ∈ S, ∑ b ∈ Finset.univ.filter (fun b => miss x b), w b := by
  classical
  have h1 : (∑ b ∈ Finset.univ.filter (fun b => ∃ x ∈ S, miss x b), w b)
      ≤ ∑ b ∈ Finset.univ, w b * (∑ x ∈ S, if miss x b then (1 : ℝ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hb : ∃ x ∈ S, miss x b
    · rw [if_pos hb]
      obtain ⟨x, hxS, hxb⟩ := hb
      have hle : (1 : ℝ) ≤ ∑ x ∈ S, if miss x b then (1 : ℝ) else 0 := by
        have hmem := Finset.single_le_sum
          (f := fun y => if miss y b then (1 : ℝ) else 0)
          (fun i _ => by positivity) hxS
        simpa [hxb] using hmem
      calc w b = w b * 1 := (mul_one _).symm
        _ ≤ w b * (∑ x ∈ S, if miss x b then (1 : ℝ) else 0) :=
            mul_le_mul_of_nonneg_left hle (hw b)
    · rw [if_neg hb]
      exact mul_nonneg (hw b) (Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num)
  have h2 : (∑ b ∈ Finset.univ, w b * (∑ x ∈ S, if miss x b then (1 : ℝ) else 0))
      = ∑ x ∈ S, ∑ b ∈ Finset.univ, w b * (if miss x b then (1 : ℝ) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have h3 : ∀ x ∈ S, (∑ b ∈ Finset.univ, w b * (if miss x b then (1 : ℝ) else 0))
      = ∑ b ∈ Finset.univ.filter (fun b => miss x b), w b := by
    intro x _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  calc (∑ b ∈ Finset.univ.filter (fun b => ∃ x ∈ S, miss x b), w b)
      ≤ ∑ b ∈ Finset.univ, w b * (∑ x ∈ S, if miss x b then (1 : ℝ) else 0) := h1
    _ = ∑ x ∈ S, ∑ b ∈ Finset.univ, w b * (if miss x b then (1 : ℝ) else 0) := h2
    _ = ∑ x ∈ S, ∑ b ∈ Finset.univ.filter (fun b => miss x b), w b :=
        Finset.sum_congr rfl fun x hx => h3 x hx

/-! ## The geometric tail computation (page 30) -/

/-- Lemma 5.6, sample count (page 30): if each element of `S` is missed by a given measurement with
probability `1 - p` where `p ≥ 1/2`, then after `t` measurements with `log(n/δ) ≤ t·log 2`
(so `t = ⌈log₂(n/δ)⌉` suffices) the union bound `h·(1-p)^t` is at most `δ`, using `h ≤ n`. -/
theorem lemma56_sample_count {h n t : ℕ} {δ p : ℝ}
    (hhn : (h : ℝ) ≤ (n : ℝ)) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hp : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (ht : Real.log ((n : ℝ) / δ) ≤ (t : ℝ) * Real.log 2) :
    (h : ℝ) * (1 - p) ^ t ≤ δ := by
  have hp0 : 0 ≤ 1 - p := by linarith
  have h1 : (1 - p) ^ t ≤ (1 / 2 : ℝ) ^ t :=
    pow_le_pow_left₀ hp0 (by linarith : (1 : ℝ) - p ≤ 1 / 2) t
  have h2 : (1 / 2 : ℝ) ^ t = ((2 : ℝ) ^ t)⁻¹ := by
    rw [← inv_pow]
    norm_num
  have hpos : 0 < (n : ℝ) / δ := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have h3 : (n : ℝ) / δ ≤ Real.exp ((t : ℝ) * Real.log 2) := by
    rw [← Real.log_le_log_iff hpos (Real.exp_pos _), Real.log_exp]
    exact ht
  have h4 : Real.exp ((t : ℝ) * Real.log 2) = (2 : ℝ) ^ t := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h3' : (n : ℝ) / δ ≤ (2 : ℝ) ^ t := by rw [← h4]; exact h3
  have hpow : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  have h5 : ((2 : ℝ) ^ t)⁻¹ ≤ δ / (n : ℝ) := by
    have := (inv_le_inv₀ hpow hpos).mpr h3'
    rwa [inv_div] at this
  have h6 : (h : ℝ) * (1 - p) ^ t ≤ (h : ℝ) * ((2 : ℝ) ^ t)⁻¹ := by
    rw [h2] at h1
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h)
  have h7 : (h : ℝ) * (δ / (n : ℝ)) ≤ δ := by
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← mul_div_assoc, div_le_iff₀ hn']
    nlinarith [hhn, hδ.le]
  calc (h : ℝ) * (1 - p) ^ t ≤ (h : ℝ) * ((2 : ℝ) ^ t)⁻¹ := h6
    _ ≤ (h : ℝ) * (δ / (n : ℝ)) := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg h)
    _ ≤ δ := h7

/-! ## Lemma 5.6 -/

/-- Lemma 5.6 (page 29-30), *Recovery of Boolean Solution via Measurements*: let `S` be the hidden
set and let `w` be the distribution of the joint outcome of `t` measurements of `|z⟩` (so
`w ≥ 0` and `Σ w = 1`).  Each `x ∈ S` is missed with probability at most `(1 - (h+1)/(2h))^t`
(independence of the measurements, page 29), and the sample count satisfies
`h·(1 - (h+1)/(2h))^t ≤ δ` (`lemma56_sample_count`).  Then with probability at least `1 - δ`
every element of `S` occurs in some outcome, i.e. `S` is recovered.

The probability space is left abstract: `w` and `hw`/`hw1` are the sample distribution and
`hmiss` is the per-element tail bound derived from independence in the paper.  The union bound
and the sample-count arithmetic are proved in `lemma56_union_bound` and `lemma56_sample_count`. -/
theorem lemma56_measurement_recovery {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (t : ℕ) (δ : ℝ) (w : (Fin t → Finset α) → ℝ)
    (hw : ∀ σ, 0 ≤ w σ)
    (hmiss : ∀ x ∈ S,
      (∑ σ ∈ Finset.univ.filter (fun σ => MissedAll x σ), w σ)
        ≤ (1 - ((S.card : ℝ) + 1) / (2 * (S.card : ℝ))) ^ t)
    (htail : (S.card : ℝ) * (1 - ((S.card : ℝ) + 1) / (2 * (S.card : ℝ))) ^ t ≤ δ) :
    (∑ σ ∈ Finset.univ.filter (fun σ => ∃ x ∈ S, MissedAll x σ), w σ) ≤ δ := by
  classical
  have h := lemma56_union_bound S w (MissedAll (α := α) (ι := Fin t)) hw
  refine le_trans h ?_
  refine le_trans (Finset.sum_le_sum hmiss) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact htail

end Qatlib.Papers.QLSBeyondCond25.MainResults.Section5
