/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12: existence of a detectable adjacent-threshold gap

Formalises the telescoping core of Lemma 12 of Liu--Shaydulin--Niroula et al.,
*Certified randomness using a trapped-ion quantum processor*, fixed
arXiv:2503.20498v1, Lemma 12 and Eq. I.28, p. 6 (Lemma 5.5 of the companion
reference [2] is the external argument the paper cites).

Statement (paper).  For `T ≥ (16/ε) log(N/ε)` there exists `j ∈ [T/2]` such
that

  `μ1(1/2 + j/T) ≥ (1 + ε/2) · μ0(1/2 + (j-1)/T)`.       (I.28)

Formalisation.  The paper's proof telescopes the contrapositive: if every
adjacent pair fails (I.28), then Eq. I.27 gives

  `μ0(τ_j) < ((1+ε/2)/(1+ε)) μ0(τ_{j-1}) ≤ (1-ε/4) μ0(τ_{j-1})`,

so `μ0(1)` drops below `((1+ε/2)/(1+ε))^{T/2} μ0(1/2)`, contradicting the
base-case bound.  We formalise the telescoping induction and the contradiction
outright.  The base-case comparison is taken in the equivalent strengthened
form

  `((1+ε/2)/(1+ε))^{T/2} · μ0(1/2) ≤ μ0(1)`,

which is the only estimate the paper imports from Lemma 5.5 of [2]; the
numeric derivation of this comparison from `exp(-εT/8)` and the hypothesis
`T ≥ (16/ε) log(N/ε)` is not repeated.  The no-case expectations are taken
nonnegative (`μ0 τ ≥ 0`), as they are expectations of indicators in the paper.

The theorem also assumes `2 ≤ T`, so that the grid index `j = 1` exists; the
paper's lower bound on `T` gives this in every application (`N ≥ 2`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.ThresholdGapExistence

/-- **Lemma 12, telescoping core** (Eq. I.28).  Under the ratio bound Eq. I.27,
monotonicity of the no-case expectation, nonnegativity and the strengthened
base-case comparison, some adjacent grid threshold exhibits a multiplicative
`(1+ε/2)` gap. -/
theorem lemma12_threshold_gap (eps : ℝ) (T N : ℕ) (mu1 mu0 : ℝ → ℝ)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hT : (16 / eps) * Real.log ((N : ℝ) / eps) ≤ (T : ℝ))
    (hT2 : 2 ≤ T)
    (hmu0_nonneg : ∀ tau, 0 ≤ mu0 tau)
    (hRatio : ∀ tau ∈ Set.Icc (1 / 2 : ℝ) 1, (1 + eps) * mu0 tau ≤ mu1 tau)
    (hMono : ∀ tau₁ ∈ Set.Icc (1 / 2 : ℝ) 1, ∀ tau₂ ∈ Set.Icc (1 / 2 : ℝ) 1,
      tau₁ ≤ tau₂ → mu0 tau₂ ≤ mu0 tau₁)
    (hBase : ((1 + eps / 2) / (1 + eps)) ^ (T / 2) * mu0 (1 / 2) ≤ mu0 1) :
    ∃ j : ℕ, 1 ≤ j ∧ 2 * j ≤ T ∧
      (1 + eps / 2) * mu0 (1 / 2 + ((j : ℝ) - 1) / (T : ℝ)) ≤
        mu1 (1 / 2 + (j : ℝ) / (T : ℝ)) := by
  let m : ℕ := T / 2
  let tau : ℕ → ℝ := fun j => 1 / 2 + (j : ℝ) / (T : ℝ)
  let c : ℝ := (1 + eps / 2) / (1 + eps)
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith) (by linarith)
  have hmem : ∀ j, j ≤ m → tau j ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    intro j hj
    have hj2 : 2 * j ≤ T := by omega
    have hjle : (j : ℝ) ≤ (T : ℝ) / 2 := by
      have h2 : ((2 * j : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hj2
      have h2' : (2 : ℝ) * (j : ℝ) ≤ (T : ℝ) := by simpa using h2
      linarith
    have hjdiv : (j : ℝ) / (T : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hTpos]
      linarith
    constructor
    · dsimp [tau]
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have hdiv0 : 0 ≤ (j : ℝ) / (T : ℝ) := div_nonneg hj0 hTpos.le
      linarith
    · dsimp [tau]
      linarith
  by_cases hzero : mu0 (1 / 2) = 0
  · -- Degenerate base value: monotonicity and nonnegativity force `mu0 = 0`
    -- on the grid, and the gap holds at `j = 1` because `hRatio` then forces
    -- `mu1 ≥ 0`.
    have hm1 : 1 ≤ m := by omega
    have hmem1 : tau 1 ∈ Set.Icc (1 / 2 : ℝ) 1 := hmem 1 hm1
    have hle_half : (1 / 2 : ℝ) ≤ tau 1 := hmem1.1
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
      constructor <;> norm_num
    have hmu_tau1_le : mu0 (tau 1) ≤ mu0 (1 / 2) :=
      hMono (1 / 2) hhalf_mem (tau 1) hmem1 hle_half
    have hmu_tau1_nonneg : 0 ≤ mu0 (tau 1) := hmu0_nonneg _
    have htau1_zero : mu0 (tau 1) = 0 := by linarith
    have hr := hRatio (tau 1) hmem1
    rw [htau1_zero] at hr
    simp only [mul_zero] at hr
    refine ⟨1, by norm_num, by omega, ?_⟩
    have hr' : (1 + eps / 2) * mu0 (1 / 2) ≤
        mu1 (1 / 2 + (1 : ℝ) / (T : ℝ)) := by
      rw [hzero]
      simp only [mul_zero]
      simpa [tau] using hr
    simpa using hr'
  · -- Main case: `mu0 (1/2) > 0`.
    have hu0pos : 0 < mu0 (1 / 2) := lt_of_le_of_ne (hmu0_nonneg _) (Ne.symm hzero)
    by_contra hno
    have hstep : ∀ j, 1 ≤ j → j ≤ m → mu0 (tau j) < c * mu0 (tau (j - 1)) := by
      intro j hj1 hjm
      have hj2 : 2 * j ≤ T := by omega
      have hmemj : tau j ∈ Set.Icc (1 / 2 : ℝ) 1 := hmem j hjm
      have hnot : ¬ ((1 + eps / 2) * mu0 (tau (j - 1)) ≤ mu1 (tau j)) := by
        intro h
        have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub hj1]
          norm_num
        exact hno ⟨j, hj1, hj2, by simpa [tau, hcast] using h⟩
      have hlt : mu1 (tau j) < (1 + eps / 2) * mu0 (tau (j - 1)) :=
        lt_of_not_ge hnot
      have hr := hRatio (tau j) hmemj
      have hcomb : (1 + eps) * mu0 (tau j) < (1 + eps / 2) * mu0 (tau (j - 1)) :=
        lt_of_le_of_lt hr hlt
      have hpos : (0 : ℝ) < 1 + eps := by linarith
      have heq : ((1 + eps / 2) / (1 + eps)) * mu0 (tau (j - 1)) =
          ((1 + eps / 2) * mu0 (tau (j - 1))) / (1 + eps) := by ring
      rw [heq, lt_div_iff₀ hpos]
      nlinarith [hcomb]
    have hchain : ∀ j, 1 ≤ j → j ≤ m → mu0 (tau j) < c ^ j * mu0 (tau 0) := by
      intro j hj1
      refine Nat.le_induction ?base ?step j hj1
      · intro h1m
        simpa using hstep 1 (le_refl 1) h1m
      · intro k hk1 ih hk1m
        have hkm : k ≤ m := by omega
        have hsk := hstep (k + 1) (by omega) hk1m
        have hik := ih hkm
        have hmul : c * mu0 (tau k) < c * (c ^ k * mu0 (tau 0)) :=
          mul_lt_mul_of_pos_left hik hc
        calc mu0 (tau (k + 1)) < c * mu0 (tau k) := hsk
          _ < c * (c ^ k * mu0 (tau 0)) := hmul
          _ = c ^ (k + 1) * mu0 (tau 0) := by rw [pow_succ]; ring
    have hm1 : 1 ≤ m := by omega
    have hZm := hchain m hm1 le_rfl
    have hmemm : tau m ∈ Set.Icc (1 / 2 : ℝ) 1 := hmem m le_rfl
    have hone_mem : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by
      constructor <;> norm_num
    have hmono1 : mu0 1 ≤ mu0 (tau m) :=
      hMono (tau m) hmemm 1 hone_mem hmemm.2
    have hbase : c ^ m * mu0 (tau 0) ≤ mu0 1 := by
      simpa [c, m, tau] using hBase
    linarith

end Qatlib.Papers.RandCertLiu25.MainResults.ThresholdGapExistence
