/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IQPBornShen26.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# c002 — Theorem 3.2: variance of IQP characteristic function values

Shen–Pielawa–Dunjko–Wang, arXiv:2602.11042v2.
Theorem 3.2 (printed p. 6, Eq. (3) = appendix Eq. (18)): under the symmetric
i.i.d. initialization of Assumption 3.1 (each `θ_j` drawn independently from a
marginal symmetric about `0`), for a fixed frequency `a ≠ 0` the characteristic
function value admits the variance closed form

`Var_θ[C_θ^a] = Σ_{J∈Ξ^a} μ^{|J|} ν^{m_a−|J|} − κ^{2 m_a}`,

where `m_a = |S^a|`, `μ = E[sin²(2θ)]`, `ν = E[cos²(2θ)]`, `κ = E[cos(2θ)]`.

The Lean proof works with the commutation decomposition (22)
`C_θ^a = Σ_{J∈Ξ^a} R_J(θ)` as the definition of the formalized characteristic
function (`charFunIQP`).  All expectations factor over coordinates by the
Fubini identity `MeasureTheory.integral_fintype_prod_eq_prod` for the product
measure `m^D`; every off-diagonal term `E[R_J R_K]`, `J ≠ K`, contains an odd
sine factor from the symmetric difference `J Δ K` whose expectation vanishes
by symmetry of the marginal, and `E[R_J]` vanishes for `J ≠ ∅` for the same
reason.  What remains is exactly the stated formula.  The gate-commutation
derivation of Eq. (22) itself (Eqs. (20)–(22), following Eq. (27) of [15]) is
the external interface; the sign function `η` is constrained by `η_J² = 1`.
The moment-form version `theorem3_2_var_charFun_moments` below takes the two
vanishing odd moments as hypotheses, so that non-symmetric marginals with the
same vanishing moments (e.g. the uniform distribution on `[0, 2π)`, used for
Theorem 3.8) can instantiate it.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory Qatlib.Papers.IQPBornShen26.MainResults

namespace Qatlib.Papers.IQPBornShen26.MainResults.CharVariance

variable {D n : ℕ} (s : Fin D → (Fin n → ZMod 2)) (a : Fin n → ZMod 2)
  (η : Finset (Fin D) → ℝ)

/-- Membership in `Ξ^a` implies subset of the generator support `S^a`. -/
lemma subset_of_mem_zeroSumSets {J : Finset (Fin D)} (hJ : J ∈ zeroSumSets s a) :
    J ⊆ supportGen s a :=
  Finset.mem_powerset.1 (Finset.mem_filter.1 hJ).1

/-- The empty set is always a zero-sum subset. -/
lemma empty_mem_zeroSumSets : (∅ : Finset (Fin D)) ∈ zeroSumSets s a :=
  Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.empty_subset (supportGen s a)),
    Finset.sum_empty⟩

/-- A sign constrained by `η_J² = 1` has absolute value one. -/
lemma abs_eq_one_of_sq_eq_one {c : ℝ} (h : c * c = 1) : |c| = 1 := by
  have h0 : 0 ≤ |c| := abs_nonneg c
  have h1 : |c| * |c| = 1 := by rw [← abs_mul, h, abs_one]
  nlinarith

/-- A finite product of factors bounded by one in absolute value. -/
lemma abs_prod_le_one {ι : Type*} [DecidableEq ι] {t : Finset ι} {f : ι → ℝ}
    (h : ∀ j ∈ t, |f j| ≤ 1) :
    |∏ j ∈ t, f j| ≤ 1 := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert x tx hx ih =>
      rw [Finset.prod_insert hx, abs_mul]
      have ha := h x (Finset.mem_insert.2 (Or.inl rfl))
      have hb := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      calc |f x| * |∏ j ∈ tx, f j|
          ≤ |f x| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = |f x| := mul_one _
        _ ≤ 1 := ha

/-- Odd functions integrate to zero under a marginal symmetric about `0`
(Assumption 3.1 of arXiv:2602.11042v2: `Pr(θ = v) = Pr(θ = −v)`). -/
lemma integral_odd_eq_zero {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsymm : Measure.map (fun x : ℝ => -x) m = m) {f : ℝ → ℝ}
    (hf : Measurable f) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x, f x ∂m = 0 := by
  have h1 : ∫ x, f x ∂(Measure.map (fun x : ℝ => -x) m) = ∫ x, f (-x) ∂m :=
    integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable
  have h2 : ∫ x, f x ∂m = ∫ x, f x ∂(Measure.map (fun x : ℝ => -x) m) := by
    rw [hsymm]
  rw [h1, funext hodd, integral_neg] at h2
  linarith

/-- The per-coordinate factor of the summand `R_J` extended by `1` outside the
generator support, so that `R_J(θ) = η_J ∏_j factorSC J j (θ_j)`. -/
def factorSC (J : Finset (Fin D)) (j : Fin D) (x : ℝ) : ℝ :=
  if j ∈ J then Real.sin (2 * x)
  else if j ∈ supportGen s a then Real.cos (2 * x) else 1

/-- Two-way split of a product of per-coordinate factors: constant `cP` on `P`,
`cR` on `R`, and `1` elsewhere, for disjoint `P`, `R`. -/
lemma prod_two_way {ι : Type*} [Fintype ι] [DecidableEq ι] (P R : Finset ι)
    (g : ι → ℝ) (cP cR : ℝ) (hd : Disjoint P R)
    (hP : ∀ j ∈ P, g j = cP) (hR : ∀ j ∈ R, g j = cR)
    (hoff : ∀ j, j ∉ P → j ∉ R → g j = 1) :
    ∏ j, g j = cP ^ P.card * cR ^ R.card := by
  have hoff' : ∀ j ∈ Finset.univ, j ∉ P ∪ R → g j = 1 := by
    intro j _ hj
    exact hoff j (fun h => hj (Finset.mem_union.2 (Or.inl h)))
      (fun h => hj (Finset.mem_union.2 (Or.inr h)))
  rw [← Finset.prod_subset (Finset.subset_univ _) hoff',
    Finset.prod_union hd, Finset.prod_congr rfl hP, Finset.prod_congr rfl hR,
    Finset.prod_const, Finset.prod_const]

variable {s a η}

/-- Product form of the summand `R_J` over all coordinates (Eq. (22) of
arXiv:2602.11042v2, with the factors outside `S^a` trivially `1`). -/
lemma termR_eq_prod {J : Finset (Fin D)} (_hJ : J ⊆ supportGen s a) (θ : Fin D → ℝ) :
    termR s a η J θ = η J * ∏ j, factorSC s a J j (θ j) := by
  have hval : ∀ j ∈ J, factorSC s a J j (θ j) = Real.sin (2 * θ j) := by
    intro j hj
    simp only [factorSC]
    exact if_pos hj
  have hcos : ∀ j ∈ supportGen s a \ J, factorSC s a J j (θ j) = Real.cos (2 * θ j) := by
    intro j hj
    simp only [factorSC]
    rw [if_neg (Finset.mem_sdiff.1 hj).2, if_pos (Finset.mem_sdiff.1 hj).1]
  have hone : ∀ j ∈ Finset.univ, j ∉ J ∪ (supportGen s a \ J) →
      factorSC s a J j (θ j) = 1 := by
    intro j _ hj
    have h1 : j ∉ J := fun h => hj (Finset.mem_union.2 (Or.inl h))
    have h2 : j ∉ supportGen s a :=
      fun h => hj (Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.2 ⟨h, h1⟩)))
    simp only [factorSC]
    rw [if_neg h1, if_neg h2]
  have hsplit : (∏ j, factorSC s a J j (θ j))
      = (∏ j ∈ J, Real.sin (2 * θ j)) * ∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j) := by
    rw [← Finset.prod_subset (Finset.subset_univ _) hone,
      Finset.prod_union (Finset.disjoint_right.2 fun a ha => (Finset.mem_sdiff.1 ha).2),
      Finset.prod_congr rfl hval, Finset.prod_congr rfl hcos]
  simp only [termR]
  rw [hsplit]
  exact mul_assoc _ _ _

/-- Vanishing odd moments under the symmetric marginal of Assumption 3.1. -/
lemma integral_sin_eq_zero {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsymm : Measure.map (fun x : ℝ => -x) m = m) :
    ∫ x, Real.sin (2 * x) ∂m = 0 :=
  integral_odd_eq_zero hsymm
    ((Real.continuous_sin.comp (by continuity)).measurable)
    (fun x => by simp [Real.sin_neg])

/-- The sine-cosine product has zero integral under a symmetric probability measure. -/
lemma integral_sin_cos_eq_zero {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsymm : Measure.map (fun x : ℝ => -x) m = m) :
    ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m = 0 :=
  integral_odd_eq_zero hsymm
    (((Real.continuous_sin.mul Real.continuous_cos).comp
      (by continuity)).measurable)
    (fun x => by simp [neg_mul, Real.sin_neg, Real.cos_neg])

/-- The summand `R_J` is bounded by one in absolute value whenever `η_J = ±1`
(paper's `η_J ∈ {−1,1}`, arXiv:2602.11042v2 Eq. (22)). -/
lemma abs_termR_le_one {J : Finset (Fin D)} (hηJ : η J * η J = 1) (θ : Fin D → ℝ) :
    |termR s a η J θ| ≤ 1 := by
  have hcosb : ∀ x : ℝ, |Real.cos x| ≤ 1 := fun x =>
    abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  have h2 := abs_prod_le_one (ι := Fin D) (t := J)
    (f := fun j => Real.sin (2 * θ j)) (fun j _ => Real.abs_sin_le_one _)
  have h3 := abs_prod_le_one (ι := Fin D) (t := supportGen s a \ J)
    (f := fun j => Real.cos (2 * θ j)) (fun j _ => hcosb _)
  have hnonneg2 : 0 ≤ |∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j)| := abs_nonneg _
  have hnonneg1 : 0 ≤ |∏ j ∈ J, Real.sin (2 * θ j)| := abs_nonneg _
  have hyz : |∏ j ∈ J, Real.sin (2 * θ j)|
      * |∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j)| ≤ 1 := by
    calc |∏ j ∈ J, Real.sin (2 * θ j)|
        * |∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j)|
        ≤ |∏ j ∈ J, Real.sin (2 * θ j)| * 1 :=
          mul_le_mul_of_nonneg_left h3 hnonneg1
      _ = |∏ j ∈ J, Real.sin (2 * θ j)| := mul_one _
      _ ≤ 1 := h2
  have h01 : |η J| = 1 := abs_eq_one_of_sq_eq_one hηJ
  unfold termR
  rw [abs_mul, abs_mul]
  calc |η J| * |∏ j ∈ J, Real.sin (2 * θ j)|
        * |∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j)|
      = 1 * (|∏ j ∈ J, Real.sin (2 * θ j)|
          * |∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j)|) := by
            rw [h01]; ring
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hyz (by norm_num : (0:ℝ) ≤ 1)
    _ = 1 := by norm_num

/-- Expectation of a single summand: `E[R_J]` vanishes unless `J = ∅`, when it
equals `η_∅ κ^{m_a}` with `κ = E[cos(2θ)]` (odd-sine factors vanish under
Assumption 3.1; arXiv:2602.11042v2, proof of Theorem 3.2). -/
lemma integral_termR_eq {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsin : ∫ x, Real.sin (2 * x) ∂m = 0)
    {J : Finset (Fin D)} (hJ : J ⊆ supportGen s a) :
    ∫ θ, termR s a η J θ ∂(Measure.pi fun _ : Fin D => m) =
      if J = ∅ then η J * (∫ x, Real.cos (2 * x) ∂m) ^ (supportGen s a).card else 0 := by
  have hfac : ∀ j : Fin D, ∫ x, factorSC s a J j x ∂m
      = if j ∈ J then ∫ x, Real.sin (2 * x) ∂m
        else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ∂m else 1 := by
    intro j
    simp only [factorSC]
    by_cases h1 : j ∈ J
    · simp only [if_pos h1]
    · by_cases h2 : j ∈ supportGen s a
      · simp only [if_neg h1, if_pos h2]
      · simp only [if_neg h1, if_neg h2, integral_const, probReal_univ, one_smul]
  simp only [termR_eq_prod (η := η) hJ]
  rw [integral_const_mul, integral_fintype_prod_eq_prod]
  simp only [hfac]
  by_cases hJ0 : J = ∅
  · subst hJ0
    rw [if_pos rfl]
    have hsplit := prod_two_way (∅ : Finset (Fin D)) (supportGen s a)
      (fun j => if j ∈ (∅ : Finset (Fin D)) then ∫ x, Real.sin (2 * x) ∂m
        else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ∂m else 1)
      (∫ x, Real.sin (2 * x) ∂m) (∫ x, Real.cos (2 * x) ∂m)
      (Finset.disjoint_right.2 fun a ha => Finset.notMem_empty a)
      (fun j hj => absurd hj (Finset.notMem_empty j))
      (fun j hj => if_pos hj)
      (fun j _ hj => if_neg hj)
    rw [hsplit, Finset.card_empty, pow_zero, one_mul]
  · rw [if_neg hJ0, hsin]
    obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.2 hJ0
    have hzero : (∏ j, if j ∈ J then (0:ℝ)
        else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ∂m else 1) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) (if_pos hj₀)
    rw [hzero, mul_zero]

/-- Expectation of a product of two summands: `E[R_J R_K]` vanishes for
`J ≠ K` (an odd sine factor from `J Δ K` has vanishing expectation), and for
`J = K` equals `η_J² μ^{|J|} ν^{|S^a∖J|}` with `μ = E[sin²(2θ)]`,
`ν = E[cos²(2θ)]` (arXiv:2602.11042v2, proof of Theorem 3.2, Eq. (23)). -/
lemma integral_termR_mul {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsc : ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m = 0)
    {J K : Finset (Fin D)} (hJ : J ⊆ supportGen s a) (hK : K ⊆ supportGen s a) :
    ∫ θ, termR s a η J θ * termR s a η K θ ∂(Measure.pi fun _ : Fin D => m) =
      if J = K then η J * η K * (∫ x, Real.sin (2 * x) ^ 2 ∂m) ^ J.card
          * (∫ x, Real.cos (2 * x) ^ 2 ∂m) ^ ((supportGen s a \ J).card) else 0 := by
  have hpair : ∀ θ : Fin D → ℝ, termR s a η J θ * termR s a η K θ
      = η J * η K * ∏ j, (factorSC s a J j (θ j) * factorSC s a K j (θ j)) := by
    intro θ
    rw [termR_eq_prod (η := η) hJ, termR_eq_prod (η := η) hK]
    have hA : (∏ j, factorSC s a J j (θ j)) * ∏ j, factorSC s a K j (θ j)
        = ∏ j, (factorSC s a J j (θ j) * factorSC s a K j (θ j)) :=
      Finset.prod_mul_distrib.symm
    have hB : (η J * ∏ j, factorSC s a J j (θ j)) * (η K * ∏ j, factorSC s a K j (θ j))
        = η J * η K * ((∏ j, factorSC s a J j (θ j)) * ∏ j, factorSC s a K j (θ j)) := by
      ring
    rw [hB, hA]
  have hfac : ∀ j : Fin D, ∫ x, factorSC s a J j x * factorSC s a K j x ∂m
      = if j ∈ J then if j ∈ K then ∫ x, Real.sin (2 * x) ^ 2 ∂m
          else ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
        else if j ∈ K then ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
        else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ^ 2 ∂m else 1 := by
    intro j
    simp only [factorSC]
    by_cases h1 : j ∈ J
    · by_cases h2 : j ∈ K
      · simp only [if_pos h1, if_pos h2]
        congr 1
        exact funext fun x => (pow_two _).symm
      · have hS : j ∈ supportGen s a := hJ h1
        simp only [if_pos h1, if_neg h2, if_pos hS]
    · by_cases h2 : j ∈ K
      · simp only [if_neg h1, if_pos h2, if_pos (hK h2)]
        congr 1
        exact funext fun x => mul_comm _ _
      · simp only [if_neg h1, if_neg h2]
        by_cases hS : j ∈ supportGen s a
        · simp only [if_pos hS]
          congr 1
          exact funext fun x => (pow_two _).symm
        · simp only [if_neg hS, one_mul, integral_const, probReal_univ, one_smul]
  have hbridge : ∀ θ : Fin D → ℝ, ∏ j, factorSC s a J j (θ j) * factorSC s a K j (θ j)
      = ∏ j, (factorSC s a J j * factorSC s a K j) (θ j) := fun θ => rfl
  have key : ∫ θ : Fin D → ℝ, ∏ j, (factorSC s a J j * factorSC s a K j) (θ j)
      ∂(Measure.pi fun _ : Fin D => m)
      = ∏ j, ∫ x, (factorSC s a J j * factorSC s a K j) x ∂m :=
    integral_fintype_prod_eq_prod (fun j x => factorSC s a J j x * factorSC s a K j x)
  rw [funext hpair, integral_const_mul, funext hbridge, key]
  simp only [Pi.mul_apply]
  simp only [hfac]
  by_cases hJK : J = K
  · subst hJK
    rw [if_pos rfl]
    have hJnot : ∀ j ∈ supportGen s a \ J, j ∉ J := fun j hj => (Finset.mem_sdiff.1 hj).2
    have hsplit := prod_two_way J (supportGen s a \ J)
      (fun j => if j ∈ J then if j ∈ J then ∫ x, Real.sin (2 * x) ^ 2 ∂m
          else ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
        else if j ∈ J then ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
        else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ^ 2 ∂m else 1)
      (∫ x, Real.sin (2 * x) ^ 2 ∂m) (∫ x, Real.cos (2 * x) ^ 2 ∂m)
      (Finset.disjoint_right.2 fun aJ ha => (Finset.mem_sdiff.1 ha).2)
      (fun j hj => by simp only [if_pos hj])
      (fun j hj => by
        simp only [if_neg (hJnot j hj), if_pos (Finset.mem_sdiff.1 hj).1])
      (by intro j h1 h2
          have hS : j ∉ supportGen s a := fun h => h2 (Finset.mem_sdiff.2 ⟨h, h1⟩)
          simp only [if_neg h1, if_neg hS])
    rw [hsplit]
    ring
  · rw [if_neg hJK]
    by_cases hne : (J \ K).Nonempty
    · obtain ⟨j₀, hj₀⟩ := hne
      have hzero : (∏ j, if j ∈ J then if j ∈ K then ∫ x, Real.sin (2 * x) ^ 2 ∂m
          else ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
        else if j ∈ K then ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
        else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ^ 2 ∂m else 1) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
        rw [if_pos (Finset.mem_sdiff.1 hj₀).1, if_neg (Finset.mem_sdiff.1 hj₀).2,
          hsc]
      rw [hzero, mul_zero]
    · by_cases hne2 : (K \ J).Nonempty
      · obtain ⟨j₀, hj₀⟩ := hne2
        have hzero : (∏ j, if j ∈ J then if j ∈ K then ∫ x, Real.sin (2 * x) ^ 2 ∂m
            else ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
          else if j ∈ K then ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m
          else if j ∈ supportGen s a then ∫ x, Real.cos (2 * x) ^ 2 ∂m else 1) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
          rw [if_neg (Finset.mem_sdiff.1 hj₀).2, if_pos (Finset.mem_sdiff.1 hj₀).1,
            hsc]
        rw [hzero, mul_zero]
      · exfalso
        have e1 : J \ K = ∅ := by
          by_contra hc
          exact hne (Finset.nonempty_iff_ne_empty.2 hc)
        have e2 : K \ J = ∅ := by
          by_contra hc
          exact hne2 (Finset.nonempty_iff_ne_empty.2 hc)
        apply hJK
        apply Finset.Subset.antisymm
        · intro j hj
          by_contra hjK
          have hmem : j ∈ J \ K := Finset.mem_sdiff.2 ⟨hj, hjK⟩
          rw [e1] at hmem
          exact absurd hmem (by simp)
        · intro j hj
          by_contra hjJ
          have hmem : j ∈ K \ J := Finset.mem_sdiff.2 ⟨hj, hjJ⟩
          rw [e2] at hmem
          exact absurd hmem (by simp)

/-- Theorem 3.2 (arXiv:2602.11042v2, p. 6, Eq. (3) = Eq. (18)): under the
symmetric i.i.d. initialization of Assumption 3.1, for a fixed frequency `a`,
the variance of the IQP characteristic function value is

`Var_θ[C_θ^a] = Σ_{J∈Ξ^a} μ^{|J|} ν^{m_a−|J|} − κ^{2m_a}`,

with `m_a = |S^a|`, `μ = E[sin²(2θ)]`, `ν = E[cos²(2θ)]`, `κ = E[cos(2θ)]`.

The formalization takes the commutation decomposition (22) as definitional
(`charFunIQP`) and the sign constraint `η_J² = 1` as the interface to the
gate-commutation derivation; the symmetry of the marginal enters as
`Measure.map (fun x => -x) m = m`.  All expectation computations (factorization
over coordinates, vanishing odd moments, diagonalization of `E[R_J R_K]`) are
carried out in full. -/
theorem theorem3_2_var_charFun_moments {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsin : ∫ x, Real.sin (2 * x) ∂m = 0)
    (hsc : ∫ x, Real.sin (2 * x) * Real.cos (2 * x) ∂m = 0)
    (hη : ∀ J ∈ zeroSumSets s a, η J * η J = 1) :
    ProbabilityTheory.variance (charFunIQP s a η) (Measure.pi fun _ : Fin D => m)
      = ∑ J ∈ zeroSumSets s a,
          (∫ x, Real.sin (2 * x) ^ 2 ∂m) ^ J.card
            * (∫ x, Real.cos (2 * x) ^ 2 ∂m) ^ ((supportGen s a \ J).card)
        - (∫ x, Real.cos (2 * x) ∂m) ^ (2 * (supportGen s a).card) := by
  have hmR : ∀ (J : Finset (Fin D)), AEStronglyMeasurable (termR s a η J)
      (Measure.pi fun _ : Fin D => m) := by
    intro J
    have hf : ∀ j : Fin D, AEStronglyMeasurable (fun θ : Fin D → ℝ => Real.sin (2 * θ j))
        (Measure.pi fun _ : Fin D => m) :=
      fun j => ((Real.continuous_sin.comp (continuous_const.mul (continuous_apply j))).measurable).aestronglyMeasurable
    have hg : ∀ j : Fin D, AEStronglyMeasurable (fun θ : Fin D → ℝ => Real.cos (2 * θ j))
        (Measure.pi fun _ : Fin D => m) :=
      fun j => ((Real.continuous_cos.comp (continuous_const.mul (continuous_apply j))).measurable).aestronglyMeasurable
    unfold termR
    have hp1 : AEStronglyMeasurable (fun θ : Fin D → ℝ => ∏ j ∈ J, Real.sin (2 * θ j))
        (Measure.pi fun _ : Fin D => m) :=
      (Finset.aestronglyMeasurable_prod J fun j _ => hf j).congr
        (Filter.Eventually.of_forall fun θ => Finset.prod_apply θ _ _)
    have hp2 : AEStronglyMeasurable (fun θ : Fin D → ℝ =>
        ∏ j ∈ supportGen s a \ J, Real.cos (2 * θ j))
        (Measure.pi fun _ : Fin D => m) :=
      (Finset.aestronglyMeasurable_prod _ fun j _ => hg j).congr
        (Filter.Eventually.of_forall fun θ => Finset.prod_apply θ _ _)
    exact (measurable_const.aestronglyMeasurable.mul hp1).mul hp2
  have hInt : ∀ J ∈ zeroSumSets s a,
      Integrable (termR s a η J) (Measure.pi fun _ : Fin D => m) := by
    intro J hJ
    exact (MemLp.of_bound (hmR J) 1
      (Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs]; exact abs_termR_le_one (s := s) (a := a) (hη J hJ) θ)).integrable le_rfl
  have hInt2 : ∀ J ∈ zeroSumSets s a, ∀ K ∈ zeroSumSets s a,
      Integrable (fun θ => termR s a η J θ * termR s a η K θ)
        (Measure.pi fun _ : Fin D => m) := by
    intro J hJ K hK
    have hbnd : ∀ θ : Fin D → ℝ, ‖termR s a η J θ * termR s a η K θ‖ ≤ 1 := by
      intro θ
      have h1 := abs_termR_le_one (s := s) (a := a) (hη J hJ) θ
      have h2 := abs_termR_le_one (s := s) (a := a) (hη K hK) θ
      rw [Real.norm_eq_abs, abs_mul]
      calc |termR s a η J θ| * |termR s a η K θ|
          ≤ |termR s a η J θ| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right h1 (by norm_num)
        _ = 1 := by norm_num
    exact (MemLp.of_bound ((hmR J).mul (hmR K)) 1
      (Filter.Eventually.of_forall hbnd)).integrable le_rfl
  have hbdd : ∀ θ : Fin D → ℝ, |charFunIQP s a η θ| ≤ (zeroSumSets s a).card := by
    intro θ
    simp only [charFunIQP]
    calc |∑ J ∈ zeroSumSets s a, termR s a η J θ|
        ≤ ∑ J ∈ zeroSumSets s a, |termR s a η J θ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ J ∈ zeroSumSets s a, 1 := Finset.sum_le_sum fun J hJ =>
          abs_termR_le_one (hη J hJ) θ
      _ = (zeroSumSets s a).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hLpC : MemLp (charFunIQP s a η) 2 (Measure.pi fun _ : Fin D => m) :=
    MemLp.of_bound ((Finset.aestronglyMeasurable_sum (zeroSumSets s a)
        fun J _ => hmR J).congr
      (Filter.Eventually.of_forall fun θ => Finset.sum_apply θ _ _))
      (zeroSumSets s a).card
      (Filter.Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hbdd θ)
  have hEC : ∫ θ, charFunIQP s a η θ ∂(Measure.pi fun _ : Fin D => m)
      = η ∅ * (∫ x, Real.cos (2 * x) ∂m) ^ (supportGen s a).card := by
    simp only [charFunIQP]
    rw [integral_finsetSum (zeroSumSets s a) fun J hJ => hInt J hJ,
      Finset.sum_eq_single (∅ : Finset (Fin D))
        (fun K hK hne => by
          rw [integral_termR_eq hsin (subset_of_mem_zeroSumSets s a hK), if_neg hne])
        (fun h => (h (empty_mem_zeroSumSets s a)).elim),
      integral_termR_eq hsin (subset_of_mem_zeroSumSets s a (empty_mem_zeroSumSets s a)),
      if_pos rfl]
  have hEC2 : ∫ θ, (charFunIQP s a η θ) ^ 2 ∂(Measure.pi fun _ : Fin D => m)
      = ∑ J ∈ zeroSumSets s a,
          (∫ x, Real.sin (2 * x) ^ 2 ∂m) ^ J.card
            * (∫ x, Real.cos (2 * x) ^ 2 ∂m) ^ ((supportGen s a \ J).card) := by
    have hpt : ∀ θ : Fin D → ℝ, (charFunIQP s a η θ) ^ 2
        = ∑ J ∈ zeroSumSets s a, ∑ K ∈ zeroSumSets s a, termR s a η J θ * termR s a η K θ := by
      intro θ
      simp only [charFunIQP, pow_two]
      rw [Finset.sum_mul_sum]
    have hinner : ∀ J ∈ zeroSumSets s a,
        Integrable (fun θ => ∑ K ∈ zeroSumSets s a, termR s a η J θ * termR s a η K θ)
          (Measure.pi fun _ : Fin D => m) := by
        intro J hJ
        refine (integrable_finsetSum' (zeroSumSets s a) fun K hK => hInt2 J hJ K hK).congr ?_
        filter_upwards with θ
        exact Finset.sum_apply θ _ _
    rw [funext hpt, integral_finsetSum _ fun J hJ => hinner J hJ]
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [integral_finsetSum _ fun K hK => hInt2 J hJ K hK,
      Finset.sum_eq_single J
        (fun K hK hne => by
          rw [integral_termR_mul hsc (subset_of_mem_zeroSumSets s a hJ)
            (subset_of_mem_zeroSumSets s a hK), if_neg hne.symm])
        (fun h => (h hJ).elim),
      integral_termR_mul hsc (subset_of_mem_zeroSumSets s a hJ)
        (subset_of_mem_zeroSumSets s a hJ),
      if_pos rfl, hη J hJ, one_mul]
  have hpow : ∀ θ : Fin D → ℝ, (charFunIQP s a η ^ 2) θ = (charFunIQP s a η θ) ^ 2 :=
    fun θ => rfl
  rw [ProbabilityTheory.variance_eq_sub hLpC, funext hpow, hEC2, hEC]
  congr 1
  have hη2 : η ∅ * η ∅ = 1 := hη ∅ (empty_mem_zeroSumSets s a)
  rw [mul_pow, pow_two, hη2, one_mul, ← pow_mul, Nat.mul_comm]

/-- Theorem 3.2 under the symmetric marginal of Assumption 3.1: the two
vanishing odd moments follow from neg-symmetry of the marginal
(`integral_sin_eq_zero`, `integral_sin_cos_eq_zero`). -/
theorem theorem3_2_var_charFun {m : Measure ℝ} [IsProbabilityMeasure m]
    (hsymm : Measure.map (fun x : ℝ => -x) m = m)
    (hη : ∀ J ∈ zeroSumSets s a, η J * η J = 1) :
    ProbabilityTheory.variance (charFunIQP s a η) (Measure.pi fun _ : Fin D => m)
      = ∑ J ∈ zeroSumSets s a,
          (∫ x, Real.sin (2 * x) ^ 2 ∂m) ^ J.card
            * (∫ x, Real.cos (2 * x) ^ 2 ∂m) ^ ((supportGen s a \ J).card)
        - (∫ x, Real.cos (2 * x) ∂m) ^ (2 * (supportGen s a).card) :=
  theorem3_2_var_charFun_moments (integral_sin_eq_zero hsymm)
    (integral_sin_cos_eq_zero hsymm) hη

end Qatlib.Papers.IQPBornShen26.MainResults.CharVariance
