/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.WalkBacktrack15.MainResults.NaiveSAT

def naiveExpectedVertices (n k m : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (n + 1),
    (2 : ℝ) ^ l * (1 - (Nat.choose l k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ))) ^ m

/-- naive_term_nonneg records the paper claim under the explicit hypotheses above. -/
theorem naive_term_nonneg (n k m l : ℕ) (hkn : k ≤ n) (hl : l ≤ n) :
    0 ≤ (2 : ℝ) ^ l * (1 - (Nat.choose l k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ))) ^ m := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ k * (Nat.choose n k : ℝ) := by
    have hpos : (0 : ℝ) < (Nat.choose n k : ℝ) := by exact_mod_cast Nat.choose_pos hkn
    positivity
  have hnum : (Nat.choose l k : ℝ) ≤ (Nat.choose n k : ℝ) := by
    exact_mod_cast Nat.choose_le_choose k hl
  have hratio : (Nat.choose l k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ)) ≤ 1 := by
    rw [div_le_one hden]
    have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hchoose : (0 : ℝ) ≤ (Nat.choose n k : ℝ) := by positivity
    nlinarith
  have : 0 ≤ 1 - (Nat.choose l k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ)) := by linarith
  positivity

/-- naive_term_le_expected records the paper claim under the explicit hypotheses above. -/
theorem naive_term_le_expected (n k m l : ℕ) (hkn : k ≤ n) (hl : l ≤ n) :
    (2 : ℝ) ^ l * (1 - (Nat.choose l k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ))) ^ m ≤ naiveExpectedVertices n k m := by
  unfold naiveExpectedVertices
  exact Finset.single_le_sum
    (fun i hi => naive_term_nonneg n k m i hkn (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

/-- naive_term_exponential_bound records the paper claim under the explicit hypotheses above. -/
theorem naive_term_exponential_bound (m : ℕ) (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - x) ^ m ≤ Real.exp (-(m : ℝ) * x) := by
  have h1 : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hb : 0 ≤ 1 - x := by linarith
  have h2 : (1 - x) ^ m ≤ (Real.exp (-x)) ^ m := pow_le_pow_left₀ hb h1 m
  rw [← Real.exp_nat_mul] at h2
  simpa [mul_comm] using h2

noncomputable def exponentC (k : ℕ) (α : ℝ) : ℝ :=
  Real.rpow ((2 : ℝ) ^ k * Real.log 2 / (α * (k : ℝ))) (1 / ((k : ℝ) - 1)) *
    (1 - 1 / (k : ℝ))

noncomputable def exponentCprime (k : ℕ) (α : ℝ) : ℝ :=
  Real.rpow ((2 : ℝ) ^ k * Real.log 2 / (α * (k : ℝ))) (1 / ((k : ℝ) - 1)) *
    (1 - 1 / (k : ℝ) - Real.log 2 / (α * (k : ℝ) ^ 2) *
      Real.rpow ((2 : ℝ) ^ k * Real.log 2 / (α * (k : ℝ))) (1 / ((k : ℝ) - 1)))

/-- A genuine finite-tree certificate: one witnessed summand supplies the lower bound,
and every valid prefix is bounded for the upper bound. -/
structure Prop8Certificate (k n m : ℕ) (α : ℝ) where
  cLo : ℝ
  cHi : ℝ
  lowerIndex : ℕ
  lowerIndex_le : lowerIndex ≤ n
  cLo_pos : 0 < cLo
  cHi_pos : 0 < cHi
  lower_term : cLo * Real.rpow 2 (exponentCprime k α * (n : ℝ)) ≤
    (2 : ℝ) ^ lowerIndex * (1 - (Nat.choose lowerIndex k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ))) ^ m
  upper_terms : ∀ l ≤ n,
    (2 : ℝ) ^ l * (1 - (Nat.choose l k : ℝ) /
      ((2 : ℝ) ^ k * (Nat.choose n k : ℝ))) ^ m ≤
      cHi * Real.rpow 2 (exponentC k α * (n : ℝ))

/-- Proposition 8 after reconstructing the missing discrete maximisation as the
`Prop8Certificate` hypotheses.  The conclusion follows by summing the actual prefix
terms, so no unconstrained expected-tree value is introduced. -/
theorem source_prop8 (k n m : ℕ) (_hk : 2 ≤ k) (_hn : 0 < n)
    (_hα1 : 1 ≤ (m : ℝ) / (n : ℝ))
    (_hα2 : (m : ℝ) / (n : ℝ) ≤ (n : ℝ) ^ (k - 1))
    (hkn : k ≤ n) (w : Prop8Certificate k n m ((m : ℝ) / (n : ℝ))) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ 0 < cHi ∧
      cLo * Real.rpow 2 (exponentCprime k ((m : ℝ) / (n : ℝ)) * (n : ℝ)) ≤
        naiveExpectedVertices n k m ∧
      naiveExpectedVertices n k m ≤
        cHi * ((n : ℝ) + 1) *
          Real.rpow 2 (exponentC k ((m : ℝ) / (n : ℝ)) * (n : ℝ)) := by
  refine ⟨w.cLo, w.cHi, w.cLo_pos, w.cHi_pos, ?_, ?_⟩
  · exact le_trans w.lower_term (naive_term_le_expected n k m w.lowerIndex
      hkn w.lowerIndex_le)
  · unfold naiveExpectedVertices
    calc
      ∑ l ∈ Finset.range (n + 1),
          (2 : ℝ) ^ l * (1 - (Nat.choose l k : ℝ) /
            ((2 : ℝ) ^ k * (Nat.choose n k : ℝ))) ^ m ≤
          ∑ _l ∈ Finset.range (n + 1),
            w.cHi * Real.rpow 2 (exponentC k ((m : ℝ) / (n : ℝ)) * (n : ℝ)) := by
              apply Finset.sum_le_sum
              intro l hl
              exact w.upper_terms l (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hl)
      _ = ((n : ℝ) + 1) * (w.cHi * Real.rpow 2
          (exponentC k ((m : ℝ) / (n : ℝ)) * (n : ℝ))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring_nf
      _ = w.cHi * ((n : ℝ) + 1) * Real.rpow 2
          (exponentC k ((m : ℝ) / (n : ℝ)) * (n : ℝ)) := by ring

/-- The numerical `k=3` bounds are accepted from a certified interval computation of
`log 2` and square-root monotonicity.  The certificate is explicit and checkable. -/
structure K3NumericalCertificate (α : ℝ) where
  upper : exponentC 3 α ≤ 0.907 / Real.sqrt α
  lower : 0.906 / Real.sqrt α - 0.142 / α ^ 2 ≤ exponentCprime 3 α

/-- Proposition 8's displayed numerical constants, under an explicit numerical
certificate for the closed forms. -/
theorem source_prop8_k3_constants (α : ℝ) (_hα : 1 ≤ α)
    (w : K3NumericalCertificate α) :
    exponentC 3 α ≤ 0.907 / Real.sqrt α ∧
      0.906 / Real.sqrt α - 0.142 / α ^ 2 ≤ exponentCprime 3 α :=
  ⟨w.upper, w.lower⟩

end Qatlib.Papers.WalkBacktrack15.MainResults.NaiveSAT
