/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WildcardSrch12.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# WildcardSrch12 — Lemma 4: CGT with `k = 1` needs one quantum query

Ambainis–Montanaro, arXiv:1210.1148v4 (fixed 20 May 2013), §4, Lemma 4, p. 7–8:

> "If `k = 1`, CGT can be solved exactly using one quantum query."

The paper's algorithm: prepare the uniform superposition over all `S ⊆ [n]`,
apply the CGT oracle (phase `(-1)^{Q_x(S)}`), and apply Hadamard gates to every
qubit of the first register.  Its content is the Walsh–Hadamard transform of the
phase function `(-1)^{Q_x(S)}`; since `|x| ≤ 1` the OR `Q_x(S)` equals the XOR
`x·S` (paper: "if `|x| ≤ 1`, then for any `s`, `⋁_i x_i s_i = x·s`"), and the
inverse Walsh transform of the character `S ↦ (-1)^{x·S}` is the point mass at
`x` (Walsh orthogonality).

This file proves, over the actual `BitStr n = Fin n → Bool` carrier:

* `cgt_or_eq_xor_of_weight_le_one` — OR of the selected bits equals XOR when the
  string has Hamming weight at most one;
* `walsh_orthogonality` — `Σ_S (-1)^{S·u} (-1)^{S·v} = 2^n` if `u = v`, else `0`;
* `lemma4_one_query_exact` — the transformed amplitude is the point mass at `x`.

Boundary: the one oracle call is the phase oracle used in the amplitude
computation; the surrounding Hadamard gates are not synthesized as explicit
`Matrix (CGTReg n r) (CGTReg n r) ℂ` factors here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Concepts.MbqcFlow.FlowDecision

namespace Qatlib.Papers.WildcardSrch12.MainResults.OneQueryCGT

open Qatlib.Papers.WildcardSrch12.MainResults

/-- The Walsh kernel `(-1)^{u·v} = ∏_i (-1)^{u_i v_i}` on `BitStr n`, written as a
real sign.  It is symmetric in `u` and `v`. -/
def walshKernel {n : ℕ} (u v : BitStr n) : ℝ :=
  ∏ i, if u i && v i then (-1 : ℝ) else 1

/-- The Walsh kernel is symmetric. -/
theorem walshKernel_comm {n : ℕ} (u v : BitStr n) :
    walshKernel u v = walshKernel v u := by
  unfold walshKernel
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hu : u i <;> by_cases hv : v i <;> simp [hu, hv]

/-- The XOR of the bits of `x` selected by `S`, as a parity (`card % 2 = 1`).
This is the decidable form of "an odd number of selected bits is `true`". -/
abbrev xorParity {n : ℕ} (x : BitStr n) (S : Finset (Fin n)) : Prop :=
  (S.filter (fun i => x i)).card % 2 = 1

/-- The product of the coordinate signs is `-1` exactly when an odd number of
coordinates carry `x i = S i = true`. -/
theorem sign_prod_eq {n : ℕ} (x S : BitStr n) :
    (∏ i, if x i && S i then (-1 : ℝ) else 1)
      = if Odd (Finset.univ.filter (fun i => x i && S i)).card then -1 else 1 := by
  classical
  set T : Finset (Fin n) := Finset.univ.filter (fun i => x i && S i) with hT
  have h1 : (∏ i : Fin n, if x i && S i then (-1 : ℝ) else 1)
      = ∏ i : Fin n, if i ∈ T then (-1 : ℝ) else 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : x i && S i
    · have hmem : i ∈ T := by
        rw [hT, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa using h⟩
      simp [h, hmem]
    · have hmem : i ∉ T := by
        rw [hT, Finset.mem_filter]
        rintro ⟨-, hh⟩
        exact h hh
      simp [h, hmem]
  rw [h1, Finset.prod_ite_mem_eq T (fun _ => (-1 : ℝ)), Finset.prod_const]
  by_cases hodd : Odd T.card
  · rw [if_pos hodd]
    exact Odd.neg_one_pow hodd
  · rw [if_neg hodd]
    rcases Nat.even_or_odd T.card with he | ho
    · exact Even.neg_one_pow he
    · exact absurd ho hodd

/-- **OR = XOR at weight one** (paper p. 8): if `|x| ≤ 1`, then on any subset `S`
the CGT response `Q_x(S)` (an OR of selected bits) equals the XOR of the selected
bits.  Consequently the oracle phase `(-1)^{Q_x(S)}` is the character
`(-1)^{x·S}`. -/
theorem cgt_or_eq_xor_of_weight_le_one {n : ℕ} (x : BitStr n) (S : Finset (Fin n))
    (hx : bitWeight x ≤ 1) :
    cgtReply x S = decide (xorParity x S) := by
  classical
  unfold cgtReply xorParity
  rw [decide_eq_decide]
  constructor
  · rintro ⟨i, hiS, hxi⟩
    -- the filtered set contains `i`; `x` has at most one true bit, so its
    -- cardinality is exactly one
    have hle : (S.filter (fun j => x j)).card ≤ 1 := by
      have hsub : S.filter (fun j => x j) ⊆ Finset.univ.filter (fun j => x j) := by
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hj).2⟩
      calc (S.filter (fun j => x j)).card
          ≤ (Finset.univ.filter (fun j => x j)).card := Finset.card_le_card hsub
        _ = bitWeight x := rfl
        _ ≤ 1 := hx
    have hpos : 0 < (S.filter (fun j => x j)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hxi⟩⟩
    have hone : (S.filter (fun j => x j)).card = 1 := by omega
    omega
  · intro hodd
    obtain ⟨j, hjS, hxj⟩ : ∃ j ∈ S, x j = true := by
      by_contra hc
      push Not at hc
      have hempty : S.filter (fun j => x j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hjS
        simp [hc j hjS]
      rw [hempty] at hodd
      simp at hodd
    exact ⟨j, hjS, hxj⟩

/-- The character product factors into coordinate-wise two-point sums. -/
theorem prod_kernel_eq_sum {n : ℕ} (u v : BitStr n) :
    (∏ i, if u i = v i then (2 : ℝ) else 0)
      = ∑ s : BitStr n, ∏ i, (if u i && s i then (-1 : ℝ) else 1)
          * (if v i && s i then (-1 : ℝ) else 1) := by
  classical
  rw [← Fintype.prod_sum (κ := fun _ : Fin n => Bool)
    (f := fun i b => (if u i && b then (-1 : ℝ) else 1) * (if v i && b then (-1 : ℝ) else 1))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases huv : u i = v i
  · rw [huv]
    by_cases hv : v i <;> norm_num [hv]
  · rw [if_neg huv]
    have hcases : (u i = true ∧ v i = false) ∨ (u i = false ∧ v i = true) := by
      rcases hu : u i with _ | _ <;> rcases hv : v i with _ | _ <;> simp_all
    rcases hcases with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simp [hu, hv]
    · simp [hu, hv]

/-- **Walsh orthogonality on the Boolean cube**: the character matrix is
`2^n` times the identity. -/
theorem walsh_orthogonality {n : ℕ} (u v : BitStr n) :
    (∑ s : BitStr n, walshKernel u s * walshKernel v s)
      = if u = v then ((2 : ℝ) ^ n) else 0 := by
  classical
  have hker : ∀ s : BitStr n, walshKernel u s * walshKernel v s
      = ∏ i, ((if u i && s i then (-1 : ℝ) else 1)
          * (if v i && s i then (-1 : ℝ) else 1)) := by
    intro s
    unfold walshKernel
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun s _ => hker s), ← prod_kernel_eq_sum]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl]
    simp [Finset.prod_const]
  · rw [if_neg huv]
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ v i := Function.ne_iff.mp huv
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The inverse Walsh–Hadamard transform of a sign function on `BitStr n`
(normalized by `2^{-n}`), i.e. the amplitude of `|y⟩` after the paper's
Hadamard step. -/
noncomputable def walshTransform {n : ℕ} (f : BitStr n → ℝ) (y : BitStr n) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ s : BitStr n, f s * walshKernel s y

/-- The oracle phase function `S ↦ (-1)^{Q_x(S)}` of Lemma 4, where the query
string `S` is identified with its set of `true` coordinates. -/
noncomputable def cgtPhaseFunction {n : ℕ} (x : BitStr n) (S : BitStr n) : ℝ :=
  if cgtReply x (Finset.univ.filter (fun i => S i)) then (-1 : ℝ) else 1

/-- At weight at most one the oracle phase function is the character
`S ↦ (-1)^{x·S}`. -/
theorem cgtPhaseFunction_eq_walshKernel {n : ℕ} (x : BitStr n)
    (hx : bitWeight x ≤ 1) (S : BitStr n) :
    cgtPhaseFunction x S = walshKernel x S := by
  classical
  unfold cgtPhaseFunction walshKernel
  rw [sign_prod_eq]
  -- the OR over the selected coordinates fires exactly when the parity of the
  -- intersection with the support of `x` is odd, because `x` has at most one
  -- true coordinate in total
  set T : Finset (Fin n) := Finset.univ.filter (fun i => x i && S i) with hT
  by_cases h : cgtReply x (Finset.univ.filter (fun i => S i))
  · rw [if_pos h, if_pos (by
      have hex : ∃ i ∈ Finset.univ.filter (fun i => S i), x i = true :=
        of_decide_eq_true (by simpa [cgtReply] using h)
      obtain ⟨i, hiS, hxi⟩ := hex
      have hSi : S i = true := (Finset.mem_filter.mp hiS).2
      have hmem : i ∈ T := by
        simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
        simp [hxi, hSi]
      have hle : T.card ≤ 1 := by
        have hsub : T ⊆ Finset.univ.filter (fun j => x j) := by
          intro j hj
          simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp at hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩
        calc T.card ≤ (Finset.univ.filter (fun j => x j)).card := Finset.card_le_card hsub
          _ = bitWeight x := rfl
          _ ≤ 1 := hx
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨i, hmem⟩
      exact ⟨0, by omega⟩)]
  · rw [if_neg h, if_neg (by
      intro hodd
      -- an odd cardinality forces a selected `true` coordinate
      have hpos : 0 < T.card := Nat.pos_of_ne_zero (by
        rintro h0
        rw [h0] at hodd
        simp at hodd)
      obtain ⟨i, hmem⟩ := Finset.card_pos.mp hpos
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      simp at hmem
      have hSi : S i = true := hmem.2
      have hxi : x i = true := hmem.1
      have hex : ∃ i ∈ Finset.univ.filter (fun i => S i), x i = true :=
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSi⟩, hxi⟩
      have : cgtReply x (Finset.univ.filter (fun i => S i)) = true := by
        simp only [cgtReply, decide_eq_true_eq]
        exact hex
      exact h this)]

/-- The paper's amplitude computation (Lemma 4): the phase function's Walsh
transform is the point mass at `x`, so measuring after the Hadamard step returns
`x` with probability one. -/
theorem lemma4_one_query_exact {n : ℕ} (x : BitStr n) (y : BitStr n)
    (hx : bitWeight x ≤ 1) :
    walshTransform (cgtPhaseFunction x) y = if y = x then 1 else 0 := by
  classical
  unfold walshTransform
  rw [Finset.sum_congr rfl (fun s _ => by rw [cgtPhaseFunction_eq_walshKernel x hx s])]
  rw [Finset.sum_congr rfl (fun s _ => by rw [walshKernel_comm s y])]
  rw [walsh_orthogonality]
  by_cases hyx : y = x
  · rw [if_pos hyx, if_pos hyx.symm]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    field_simp
  · rw [if_neg hyx, if_neg (Ne.symm hyx), mul_zero]

end Qatlib.Papers.WildcardSrch12.MainResults.OneQueryCGT
