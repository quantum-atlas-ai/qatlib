/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.BinaryRisk
import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.GeneralPolicy

/-!
# Binary Adaptive

Fresh Policies constructions for Copy Decision.
Defines `pairPrior`, `guessDecision`, `binaryAdaptive`.
Proves `pairPrior_sum_mul`, `pairPrior_update`, `binaryAdaptive_error`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition

/-- Definition of pair Prior in the Fresh Policies construction. -/
def pairPrior (i j : Fin 3) (p q : ℝ) (k : Fin 3) : ℝ :=
  (if k=i then p else 0)+(if k=j then q else 0)

/-- The stated copy-decision construction satisfies `pairPrior_sum_mul` with the complete displayed premises. -/
lemma pairPrior_sum_mul (i j : Fin 3) (p q : ℝ) (f : Fin 3 → ℝ) :
    (∑ k, pairPrior i j p q k*f k)=p*f i+q*f j := by
  simp [pairPrior, add_mul, ite_mul, Finset.sum_add_distrib]

/-- The stated copy-decision construction satisfies `pairPrior_update` with the complete displayed premises. -/
lemma pairPrior_update (i j : Fin 3) (p q : ℝ) (f : Fin 3 → ℝ) :
    (fun k => pairPrior i j p q k*f k)=pairPrior i j (p*f i) (q*f j) := by
  funext k
  have hi : (if k=i then p else 0)*f k=(if k=i then p*f i else 0) := by
    split_ifs with h
    · subst k
      rfl
    · simp
  have hj : (if k=j then q else 0)*f k=(if k=j then q*f j else 0) := by
    split_ifs with h
    · subst k
      rfl
    · simp
  unfold pairPrior
  rw [add_mul, hi, hj]

/-- Definition of guess Decision in the Fresh Policies construction. -/
def guessDecision (label : Fin 3) : TerminalDecision where
  prob k := if k=label then 1 else 0
  nonneg := by intro k; split_ifs <;> norm_num
  total := by simp

/-- An actual fixed-copy adaptive measurement tree. Known Born weights select
the next projectors; no quantum output or true-label register is passed on. -/
def binaryAdaptive : (n : ℕ) → (i j : Fin 3) → (hij : i≠j) →
    (p q : ℝ) → (hp : 0 ≤ p) → (hq : 0 ≤ q) → FinitePOVMPolicy n
  | 0, i, j, _, p, q, _, _ => .leaf (guessDecision (if q ≤ p then i else j))
  | n+1, i, j, hij, p, q, hp, hq =>
      if hQ : 0 < p+q then
        .step 2 (binaryPOVM i j hij p q hQ) (fun a =>
          binaryAdaptive n i j hij (binaryPosteriorP i j hij p q hQ a)
            (binaryPosteriorQ i j hij p q hQ a)
            (binaryPosterior_nonneg i j hij hp hq hQ a).1
            (binaryPosterior_nonneg i j hij hp hq hQ a).2)
      else ignoredPOVMCopies (n+1)

/-- The same explicitly constructed one-copy-at-a-time program attains the
closed-form risk, for arbitrary nonnegative unnormalized priors including zero. -/
theorem binaryAdaptive_error (n : ℕ) (i j : Fin 3) (hij : i≠j)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    povmPolicyError (binaryAdaptive n i j hij p q hp hq) (pairPrior i j p q)=binaryRisk n p q := by
  induction n generalizing p q with
  | zero =>
    change (∑ k, pairPrior i j p q k*(1-(guessDecision (if q ≤ p then i else j)).prob k))=_
    rw [pairPrior_sum_mul, binaryRisk_depth_zero]
    by_cases h : q ≤ p
    · simp [guessDecision, h, Ne.symm hij]
    · simp [guessDecision, h, hij, min_eq_left (le_of_not_ge h)]
  | succ n ih =>
    by_cases hQ : 0 < p+q
    · rw [binaryAdaptive, dif_pos hQ, povmPolicyError]
      simp_rw [pairPrior_update]
      calc
        _ = ∑ a, binaryRisk n (binaryPosteriorP i j hij p q hQ a)
            (binaryPosteriorQ i j hij p q hQ a) := by
          apply Finset.sum_congr rfl
          intro a _
          exact ih _ _ (binaryPosterior_nonneg i j hij hp hq hQ a).1
            (binaryPosterior_nonneg i j hij hp hq hQ a).2
        _ = binaryRisk (n+1) p q := binaryRisk_sum n p q hQ _ _
          (fun a => (binaryPosterior_nonneg i j hij hp hq hQ a).1)
          (fun a => (binaryPosterior_nonneg i j hij hp hq hQ a).2)
          (binaryPosterior_total i j hij p q hQ) (binaryPosterior_product i j hij p q hQ)
    · have hp0 : p=0 := by linarith
      have hq0 : q=0 := by linarith
      rw [povmPolicyError_linear]
      simp [pairPrior, hp0, hq0, binaryRisk]

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
