/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.SourceCorollary1
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.SourceLemma8
public import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.TailBudget
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Euclidean branch-state assembly for Corollary 1

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Corollary 1 is printed on p.11.

The source divides the Lemma 7 average running time by the square root of the
Lemma 8 success probability.  This module puts the common weighted stage sum
inside a normalized branch state in the genuine Euclidean norm.  Thus the
weights are the squared magnitudes of a normalized state in a finite
eigenbasis. Under the finite truncation of the Lemma 7 stopping-moment identity and
the exact branch-decomposition of the success probability used by Lemma 8, the
two frozen results assemble to the printed ratio with the uniform constant
outside all quantifiers.

This is still a conditional source-level bridge.  It does not construct the
adaptive Algorithm 4 program, and it does not claim that its stopping-law and
success-probability hypotheses have yet been transported from that program.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

/-- The Euclidean state whose branch coefficients are `x i` scaled by the
source's stage scale `2 ^ j i`. -/
def stageVector {branchCount : ℕ} (x : EuclideanSpace ℂ (Fin branchCount))
    (j : Fin branchCount → ℕ) : EuclideanSpace ℂ (Fin branchCount) :=
  WithLp.toLp 2 (fun i => x i * ((2 : ℝ) ^ (j i) : ℂ))

/-- The Euclidean norm of `stageVector` is exactly the weighted `ℓ²` stage sum
used by source Lemma 7 and Corollary 1. -/
theorem stageVector_norm_sq {branchCount : ℕ}
    (x : EuclideanSpace ℂ (Fin branchCount)) (j : Fin branchCount → ℕ) :
    ‖stageVector x j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 * (2 : ℝ) ^ (2 * j i) := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hnonneg : 0 ≤ (2 : ℝ) ^ (j i) := by positivity
  show ‖x i * ((2 : ℝ) ^ (j i) : ℂ)‖ ^ 2
    = ‖x i‖ ^ 2 * (2 : ℝ) ^ (2 * j i)
  have hcast : ‖((2 : ℝ) ^ (j i) : ℂ)‖ = (2 : ℝ) ^ (j i) := by
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnonneg]
  rw [norm_mul, hcast, mul_pow]
  congr 1
  rw [← pow_mul]
  ring

/-- Fixed arXiv:1010.4458v2, Corollary 1, Euclidean branch-state form.

For a normalized state on a nonempty finite branch space and a positive
repetition factor `kuniq`, if `Tav` has the finite truncated stopping-moment
form of Lemma 7 and `psucc` is the exact
branch-decomposed success probability from Lemma 8, then

  `Tav / √psucc ≤ 4 · k_uniq · (κ/ε)`.

The constant is the product of the explicit constant `2` from the frozen
truncated Lemma 7 budget and the factor `2` contributed by the `1/4` success
constant in Lemma 8. -/
theorem source_corollary1_euclidean {branchCount : ℕ}
    (_hbranches : 0 < branchCount)
    (x : EuclideanSpace ℂ (Fin branchCount))
    (j nstage : Fin branchCount → ℕ)
    (pstop : Fin branchCount → ℕ → ℝ)
    (q : Fin branchCount → ℝ) (Tav psucc kuniq ε κ : ℝ)
    (hε : 0 < ε) (hκ : 0 < κ) (hk : 0 < kuniq)
    (hx : ‖x‖ = 1)
    (hp0 : ∀ i s, 0 ≤ pstop i s)
    (hp1 : ∀ i, ∑ s ∈ Finset.range (nstage i + 2), pstop i s ≤ 1)
    (hnj : ∀ i, nstage i ≤ j i)
    (hTav : Tav ^ 2 =
      (∑ i, ‖x i‖ ^ 2 *
        (∑ s ∈ Finset.range (nstage i + 2),
          pstop i s * ((2 : ℝ) ^ s) ^ 2)) * kuniq ^ 2)
    (hpsucc : psucc = ∑ i, ‖x i‖ ^ 2 * q i)
    (hq : ∀ i, (1 / 4) * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2 ≤ q i) :
    Tav / Real.sqrt psucc ≤ 4 * kuniq * (κ / ε) := by
  have hlem7 :=
    Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.TailBudget.uniformBudget
      (fun i => ‖x i‖) nstage pstop
    Tav kuniq hp0 hk.le hp1 hTav
  have hlem8 := Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.source_lemma8
    (fun i => ‖x i‖) q j ε κ hε hκ hq
  rw [← hpsucc] at hlem8
  have hbase : (1 : ℝ) ≤ ‖stageVector x j‖ ^ 2 := by
    rw [stageVector_norm_sq]
    have hsum : (1 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 :=
      by
        rw [← EuclideanSpace.norm_sq_eq, hx]
        norm_num
    calc (1 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 := hsum
      _ ≤ ∑ i, ‖x i‖ ^ 2 * (2 : ℝ) ^ (2 * j i) :=
          Finset.sum_le_sum fun i _ =>
            by
              refine le_mul_of_one_le_right (sq_nonneg _) ?_
              have hone : (1 : ℝ) = (2 : ℝ) ^ (0 : ℕ) := by norm_num
              rw [hone]
              exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
                (Nat.zero_le _)
  have hsumle : ∑ i, ‖x i‖ ^ 2 * (2 : ℝ) ^ (2 * nstage i) ≤ ‖stageVector x j‖ ^ 2 := by
    rw [stageVector_norm_sq]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.mul_le_mul_left 2 (hnj i))) (sq_nonneg _)
  have hTj : Tav ≤ 2 * kuniq * Real.sqrt (‖stageVector x j‖ ^ 2) :=
    hlem7.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumle)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hk.le))
  rw [stageVector_norm_sq] at hbase hTj
  have hcombined := Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.source_corollary1
    (fun i => ‖x i‖) j Tav psucc 2 kuniq ε κ hε hκ (by norm_num) hk.le
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hbase) hTj hlem8
  calc Tav / Real.sqrt psucc
      ≤ 2 * 2 * kuniq * (κ / ε) := hcombined
    _ = 4 * kuniq * (κ / ε) := by ring

/-- Corollary 1 with the uniform constant chosen before the branch space,
state, stopping law, and all source parameters. -/
theorem source_corollary1_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∀ (branchCount : ℕ) (_hbranches : 0 < branchCount)
        (x : EuclideanSpace ℂ (Fin branchCount))
        (j nstage : Fin branchCount → ℕ)
        (pstop : Fin branchCount → ℕ → ℝ)
        (q : Fin branchCount → ℝ) (Tav psucc kuniq ε κ : ℝ),
        0 < ε → 0 < κ → 0 < kuniq → ‖x‖ = 1 →
        (∀ i s, 0 ≤ pstop i s) →
        (∀ i, ∑ s ∈ Finset.range (nstage i + 2), pstop i s ≤ 1) →
        (∀ i, nstage i ≤ j i) →
        Tav ^ 2 =
          (∑ i, ‖x i‖ ^ 2 *
            (∑ s ∈ Finset.range (nstage i + 2),
              pstop i s * ((2 : ℝ) ^ s) ^ 2)) * kuniq ^ 2 →
        psucc = ∑ i, ‖x i‖ ^ 2 * q i →
        (∀ i, (1 / 4) * (ε ^ 2 * (2 : ℝ) ^ (2 * j i)) / κ ^ 2 ≤ q i) →
        Tav / Real.sqrt psucc ≤ C * kuniq * (κ / ε) := by
  refine ⟨4, by norm_num, fun branchCount hbranches x j nstage pstop q
      Tav psucc kuniq ε κ hε hκ hk hx hp0 hp1 hnj hTav hpsucc hq => ?_⟩
  exact source_corollary1_euclidean hbranches x j nstage pstop q
    Tav psucc kuniq ε κ hε hκ hk hx hp0 hp1 hnj hTav hpsucc hq

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem
