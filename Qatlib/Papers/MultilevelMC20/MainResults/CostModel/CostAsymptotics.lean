/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Cost asymptotics for MultilevelMC20

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

This file fixes the vocabulary in which every cost claim of the paper is stated:

* `epsZero` is the filter `ε → 0⁺` along which all `O(·)` statements are read;
* `CostClass p q s c` says that the cost profile `c ε` is
  `O(ε ^ (-p) * (log (1/ε)) ^ q * (log log (1/ε)) ^ s)`, the paper's `O(·)` with the
  displayed poly-logarithmic factors (e.g. Theorem 2 display (3.8), Theorem 3 (4.14));
* `CostTildeClass p c` is the paper's `Õ(ε^{-p})`: some fixed polynomial in `log (1/ε)`
  and `log log (1/ε)` is hidden (used in Theorem 1, Corollaries 3--5, Propositions 4--5,
  Theorem 4).

The monotonicity and product lemmas below are fully proved. They are the only things
the exponent bookkeeping in the paper ("a straightforward result from Lemma 3 and
Proposition 2", Section 4.2) needs.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- The one-sided neighbourhood filter `ε → 0⁺`. All cost statements of the paper are
asymptotic as the target accuracy `ε` tends to zero from above. -/
def epsZero : Filter ℝ := 𝓝[>] (0 : ℝ)

/-- The distinguished bound function
`ε ↦ ε^{-p} (log 1/ε)^q (log log 1/ε)^s`. -/
def costBound (p q s : ℝ) (ε : ℝ) : ℝ :=
  ε ^ (-p) * (Real.log ε⁻¹) ^ q * (Real.log (Real.log ε⁻¹)) ^ s

/-- The paper's cost class `O(ε^{-p} (log 1/ε)^q (log log 1/ε)^s)` at `ε → 0⁺`. -/
def CostClass (p q s : ℝ) (c : ℝ → ℝ) : Prop :=
  c =O[epsZero] costBound p q s

/-- The paper's `Õ(ε^{-p})`: a cost `O(ε^{-p})` up to some fixed poly-logarithmic
factor `(log 1/ε)^q (log log 1/ε)^s`. -/
def CostTildeClass (p : ℝ) (c : ℝ → ℝ) : Prop :=
  ∃ q s : ℝ, CostClass p q s c

/-- `ε` is eventually positive along `epsZero`. -/
theorem eventually_pos_epsZero : ∀ᶠ ε : ℝ in epsZero, 0 < ε :=
  self_mem_nhdsWithin

/-- `ε` is eventually below any fixed positive threshold along `epsZero`. -/
theorem eventually_lt_epsZero {a : ℝ} (ha : 0 < a) : ∀ᶠ ε : ℝ in epsZero, ε < a :=
  nhdsWithin_le_nhds (Iio_mem_nhds ha)

/-- Eventually `0 < ε < exp (-exp 1)`. -/
theorem eventually_small : ∀ᶠ ε : ℝ in epsZero,
    0 < ε ∧ ε < Real.exp (-(Real.exp 1)) :=
  (eventually_pos_epsZero.and (eventually_lt_epsZero (Real.exp_pos _)))

/-- For `0 < ε < exp (-exp 1)` we have `1 < log (1/ε)`. -/
theorem one_lt_log_inv {ε : ℝ} (hε0 : 0 < ε) (hε : ε < Real.exp (-(Real.exp 1))) :
    1 < Real.log ε⁻¹ := by
  have hinv : Real.exp (Real.exp 1) < ε⁻¹ := by
    have := (inv_lt_inv₀ (Real.exp_pos _) hε0).2 hε
    rw [Real.exp_neg, inv_inv] at this
    exact this
  have h1 : Real.exp 1 < ε⁻¹ :=
    lt_trans (Real.exp_lt_exp.mpr (by linarith [Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)]))
      hinv
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log ε⁻¹ := Real.log_lt_log (Real.exp_pos 1) h1

/-- For `0 < ε < exp (-exp 1)` we have `1 < log log (1/ε)`. -/
theorem one_lt_loglog_inv {ε : ℝ} (hε0 : 0 < ε) (hε : ε < Real.exp (-(Real.exp 1))) :
    1 < Real.log (Real.log ε⁻¹) := by
  have hinv : Real.exp (Real.exp 1) < ε⁻¹ := by
    have := (inv_lt_inv₀ (Real.exp_pos _) hε0).2 hε
    rw [Real.exp_neg, inv_inv] at this
    exact this
  have hlog : Real.exp 1 < Real.log ε⁻¹ := by
    calc (Real.exp 1) = Real.log (Real.exp (Real.exp 1)) := (Real.log_exp _).symm
      _ < Real.log ε⁻¹ := Real.log_lt_log (Real.exp_pos _) hinv
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log (Real.log ε⁻¹) := Real.log_lt_log (Real.exp_pos 1) hlog

/-- Eventually `1 < log (1/ε)`. -/
theorem eventually_log_gt_one : ∀ᶠ ε : ℝ in epsZero, 1 < Real.log ε⁻¹ := by
  filter_upwards [eventually_small] with ε h
  exact one_lt_log_inv h.1 h.2

/-- Eventually `1 < log log (1/ε)`. -/
theorem eventually_loglog_gt_one : ∀ᶠ ε : ℝ in epsZero,
    1 < Real.log (Real.log ε⁻¹) := by
  filter_upwards [eventually_small] with ε h
  exact one_lt_loglog_inv h.1 h.2

/-- Pointwise domination of the bound functions on `(0, exp (-exp 1))`. -/
theorem costBound_mono_of_small {p p' q q' s s' ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < Real.exp (-(Real.exp 1)))
    (hpp : p ≤ p') (hqq : q ≤ q') (hss : s ≤ s') :
    ‖costBound p q s ε‖ ≤ ‖costBound p' q' s' ε‖ := by
  have hε1 : ε ≤ 1 := le_of_lt (lt_trans hε (Real.exp_lt_one_iff.mpr (by nlinarith [Real.exp_pos 1])))
  have hL1 : 1 ≤ Real.log ε⁻¹ := le_of_lt (one_lt_log_inv hε0 hε)
  have hlogpos : 0 < Real.log ε⁻¹ := lt_of_lt_of_le zero_lt_one hL1
  have hM1 : 1 ≤ Real.log (Real.log ε⁻¹) := le_of_lt (one_lt_loglog_inv hε0 hε)
  have hloglogpos : 0 < Real.log (Real.log ε⁻¹) := lt_of_lt_of_le zero_lt_one hM1
  have e1 : ε ^ (-p) ≤ ε ^ (-p') :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have e2 : (Real.log ε⁻¹) ^ q ≤ (Real.log ε⁻¹) ^ q' :=
    Real.rpow_le_rpow_of_exponent_le hL1 hqq
  have e3 : (Real.log (Real.log ε⁻¹)) ^ s ≤ (Real.log (Real.log ε⁻¹)) ^ s' :=
    Real.rpow_le_rpow_of_exponent_le hM1 hss
  have h1 : 0 ≤ ε ^ (-p) := Real.rpow_nonneg hε0.le _
  have h2 : 0 ≤ ε ^ (-p') := Real.rpow_nonneg hε0.le _
  have h3 : 0 ≤ (Real.log ε⁻¹) ^ q := Real.rpow_nonneg hlogpos.le _
  have h4 : 0 ≤ (Real.log ε⁻¹) ^ q' := Real.rpow_nonneg hlogpos.le _
  have h5 : 0 ≤ (Real.log (Real.log ε⁻¹)) ^ s := Real.rpow_nonneg hloglogpos.le _
  have h6 : 0 ≤ (Real.log (Real.log ε⁻¹)) ^ s' := Real.rpow_nonneg hloglogpos.le _
  rw [costBound, costBound, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg h1 h3) h5),
    abs_of_nonneg (mul_nonneg (mul_nonneg h2 h4) h6)]
  calc ε ^ (-p) * (Real.log ε⁻¹) ^ q * (Real.log (Real.log ε⁻¹)) ^ s
      ≤ ε ^ (-p') * (Real.log ε⁻¹) ^ q * (Real.log (Real.log ε⁻¹)) ^ s := by
        gcongr
    _ ≤ ε ^ (-p') * (Real.log ε⁻¹) ^ q' * (Real.log (Real.log ε⁻¹)) ^ s := by
        gcongr
    _ ≤ ε ^ (-p') * (Real.log ε⁻¹) ^ q' * (Real.log (Real.log ε⁻¹)) ^ s' := by
        gcongr

/-- Monotonicity of the cost class in all three parameters. -/
theorem costClass_mono {p p' q q' s s' : ℝ} {c : ℝ → ℝ}
    (hpp : p ≤ p') (hqq : q ≤ q') (hss : s ≤ s') (h : CostClass p q s c) :
    CostClass p' q' s' c := by
  unfold CostClass at h ⊢
  refine h.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_small] with ε hε
  rw [one_mul]
  exact costBound_mono_of_small hε.1 hε.2 hpp hqq hss

/-- `CostClass` is closed under addition (two cost contributions). -/
theorem costClass_add {p q s : ℝ} {c₁ c₂ : ℝ → ℝ}
    (h₁ : CostClass p q s c₁) (h₂ : CostClass p q s c₂) : CostClass p q s (c₁ + c₂) :=
  IsBigO.add h₁ h₂

/-- A constant multiple of a cost class stays in the same class. -/
theorem costClass_const_mul {p q s : ℝ} {c : ℝ → ℝ} (k : ℝ) (h : CostClass p q s c) :
    CostClass p q s (fun ε => k * c ε) :=
  IsBigO.const_mul_left h k

/-- Product of two cost classes: exponents add (poly-log factors multiply). -/
theorem costClass_mul {p₁ q₁ s₁ p₂ q₂ s₂ : ℝ} {c₁ c₂ : ℝ → ℝ}
    (h₁ : CostClass p₁ q₁ s₁ c₁) (h₂ : CostClass p₂ q₂ s₂ c₂) :
    CostClass (p₁ + p₂) (q₁ + q₂) (s₁ + s₂) (c₁ * c₂) := by
  unfold CostClass at h₁ h₂ ⊢
  refine (IsBigO.mul h₁ h₂).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_small] with ε hε
  rw [one_mul]
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := le_of_lt (lt_trans hε.2 (Real.exp_lt_one_iff.mpr (by nlinarith [Real.exp_pos 1])))
  have hL1 : 1 ≤ Real.log ε⁻¹ := le_of_lt (one_lt_log_inv hε0 hε.2)
  have hM1 : 1 ≤ Real.log (Real.log ε⁻¹) := le_of_lt (one_lt_loglog_inv hε0 hε.2)
  have hLpos : 0 < Real.log ε⁻¹ := lt_of_lt_of_le zero_lt_one hL1
  have hMpos : 0 < Real.log (Real.log ε⁻¹) := lt_of_lt_of_le zero_lt_one hM1
  have hX : ε ^ (-p₁) * ε ^ (-p₂) = ε ^ (-(p₁ + p₂)) := by
    rw [← Real.rpow_add hε0, neg_add]
  have hY : (Real.log ε⁻¹) ^ q₁ * (Real.log ε⁻¹) ^ q₂ = (Real.log ε⁻¹) ^ (q₁ + q₂) := by
    rw [← Real.rpow_add hLpos]
  have hZ : (Real.log (Real.log ε⁻¹)) ^ s₁ * (Real.log (Real.log ε⁻¹)) ^ s₂ =
      (Real.log (Real.log ε⁻¹)) ^ (s₁ + s₂) := by
    rw [← Real.rpow_add hMpos]
  have key : costBound p₁ q₁ s₁ ε * costBound p₂ q₂ s₂ ε =
      costBound (p₁ + p₂) (q₁ + q₂) (s₁ + s₂) ε := by
    unfold costBound
    calc ε ^ (-p₁) * (Real.log ε⁻¹) ^ q₁ * (Real.log (Real.log ε⁻¹)) ^ s₁ *
          (ε ^ (-p₂) * (Real.log ε⁻¹) ^ q₂ * (Real.log (Real.log ε⁻¹)) ^ s₂)
        = (ε ^ (-p₁) * ε ^ (-p₂)) *
            ((Real.log ε⁻¹) ^ q₁ * (Real.log ε⁻¹) ^ q₂) *
            ((Real.log (Real.log ε⁻¹)) ^ s₁ * (Real.log (Real.log ε⁻¹)) ^ s₂) := by
          ring
      _ = ε ^ (-(p₁ + p₂)) * (Real.log ε⁻¹) ^ (q₁ + q₂) *
            (Real.log (Real.log ε⁻¹)) ^ (s₁ + s₂) := by rw [hX, hY, hZ]
  rw [key]

/-- `CostClass` from an eventual bound by a constant times the model bound. -/
theorem costClass_of_bound {p q s M : ℝ} {c : ℝ → ℝ}
    (h : ∀ᶠ ε : ℝ in epsZero, ‖c ε‖ ≤ M * ‖costBound p q s ε‖) :
    CostClass p q s c :=
  IsBigO.of_bound M h

/-- The pure power `c * ε^{-p}` is in the cost class with no poly-logarithmic
factors. -/
theorem costClass_const_rpow (p c : ℝ) :
    CostClass p 0 0 (fun ε => c * ε ^ (-p)) := by
  have h : (fun ε : ℝ => ε ^ (-p)) =O[epsZero] costBound p 0 0 := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with ε
    simp [costBound, Real.rpow_zero]
  exact IsBigO.const_mul_left h c

/-- Sum of two costs already bounded separately: if `c₁` is in a class and `c₂` is
dominated by a constant multiple of the same bound, so is `c₁ + c₂`. -/
theorem costClass_add_of_bound {p q s M : ℝ} {c₁ c₂ : ℝ → ℝ}
    (h₁ : CostClass p q s c₁)
    (h₂ : ∀ᶠ ε : ℝ in epsZero, ‖c₂ ε‖ ≤ M * ‖costBound p q s ε‖) :
    CostClass p q s (c₁ + c₂) :=
  IsBigO.add h₁ (costClass_of_bound h₂)

/-- `CostClass` embeds into the tilde class. -/
theorem costClass_toTilde {p q s : ℝ} {c : ℝ → ℝ} (h : CostClass p q s c) :
    CostTildeClass p c :=
  ⟨q, s, h⟩

/-- Exponent monotonicity of the tilde class. -/
theorem costTildeClass_mono_exp {p p' : ℝ} {c : ℝ → ℝ} (hpp : p ≤ p')
    (h : CostTildeClass p c) : CostTildeClass p' c := by
  obtain ⟨q, s, hq⟩ := h
  exact ⟨q, s, costClass_mono hpp le_rfl le_rfl hq⟩

/-- Product of tilde-class costs. -/
theorem costTildeClass_mul {p₁ p₂ : ℝ} {c₁ c₂ : ℝ → ℝ}
    (h₁ : CostTildeClass p₁ c₁) (h₂ : CostTildeClass p₂ c₂) :
    CostTildeClass (p₁ + p₂) (c₁ * c₂) := by
  obtain ⟨q₁, s₁, hq₁⟩ := h₁
  obtain ⟨q₂, s₂, hq₂⟩ := h₂
  exact ⟨q₁ + q₂, s₁ + s₂, costClass_mul hq₁ hq₂⟩

end Qatlib.Papers.MultilevelMC20.MainResults
