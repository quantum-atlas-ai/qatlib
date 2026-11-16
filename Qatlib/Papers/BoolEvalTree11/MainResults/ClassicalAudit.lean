/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolEvalTree11.MainResults.Models

@[expose] public section


/-! # The old classical carrier does not bind cost to computation

A success probability and an unrelated expected-cost field cannot state a
query lower bound for algorithms computing the promised tree problem. The
entire original target is refuted with a positive legal depth and k=1. This
does not refute the paper's actual decision-tree lower bound.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolEvalTree11.MainResults.ClassicalAudit
open Models

/-- A legal old record whose success field is one and cost field is zero. -/
def freeRecord : ClassicalTreeAlgorithm where
  successProb := 1
  expectedQueriesOnHard := 0
  successProb_nonneg := by norm_num
  successProb_le_one := le_refl _

/-- A fixed positive depth with a provably nonzero logarithm. -/
def sampleDepth : ℕ := 2^20

/-- This depth satisfies the entire old polylog promise at k=1. -/
theorem logRange : 10≤Real.log (sampleDepth:ℝ) ∧
    Real.log (sampleDepth:ℝ)/10<2 := by
  have he : Real.log (sampleDepth:ℝ)=20*Real.log 2 := by
    have hn : (sampleDepth:ℝ)=(2:ℝ)^20 := by norm_num [sampleDepth]
    rw [hn,Real.log_pow]
    norm_num
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hu := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    (by norm_num : (2:ℝ)≠1)
  norm_num at hl hu
  rw [he]
  constructor <;> linarith

/-- The complete literal old classical lower-bound target is false. -/
theorem lowerFalse :
    ¬(∀ {_c n k : ℕ} (_hk : 1≤k) (_hn : 1≤n)
      (_hpolylog : (k:ℝ)<(Real.log (n:ℝ))^2)
      (B : ClassicalTreeAlgorithm) (_hcorrect : (2:ℝ)/3≤B.successProb),
      ∃ C : ℝ, 0<C ∧ C*(Real.log ((n:ℝ)/(k:ℝ)))^k≤B.expectedQueriesOnHard) := by
  intro h
  obtain ⟨C,hC,hb⟩ := h (_c:=1) (n:=sampleDepth) (k:=1)
    (by norm_num) (by norm_num [sampleDepth])
    (by simp only [Nat.cast_one]
        nlinarith [logRange.1,sq_nonneg (Real.log (sampleDepth:ℝ)-1)])
    freeRecord (by norm_num [freeRecord])
  have hl : 0<Real.log (sampleDepth:ℝ) := by linarith [logRange.1]
  have hh : C*Real.log (sampleDepth:ℝ)≤0 := by simpa [freeRecord] using hb
  exact (not_le_of_gt (mul_pos hC hl)) hh

/-- The complete old bias contract is false even for normalized binary marginals. -/
theorem biasFalse :
    ¬(∀ (β : ℕ) (_hβ : 1≤β) (q₀ q₁ q₀' q₁' pb₀ pb₁ : ℝ)
      (_hq₀ : 0<q₀) (_hqb : 0<q₀*pb₀+q₁*pb₁) (_hpb : 0<pb₀+pb₁)
      (_hnotIII : 2*(β:ℝ)^(-(3:ℝ))≤
        biasRatio (pb₀*q₀'+pb₁*q₁') ((pb₀+pb₁)/2)),
      1/(4*(β:ℝ)^3)≤q₀'*((q₀*pb₀+q₁*pb₁)/(q₀*pb₀))) := by
  intro h
  have hh := h 2 (by norm_num) (1/2) (1/2) 0 1 (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [biasRatio,Real.rpow_neg,Real.rpow_natCast])
  norm_num at hh

end Qatlib.Papers.BoolEvalTree11.MainResults.ClassicalAudit
