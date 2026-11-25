/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCircApprox95.MainResults.GateWordCover
public import Qatlib.Papers.QCircApprox95.MainResults.DecisionProblems
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The exponential fraction bound of Theorem 5.1

The decision net count of `Qatlib.Papers.QCircApprox95.MainResults.decision_net_count_concrete`
bounds the number of decidable problems by `(2 / δ) ^ (b * 2 ^ (4 * n))` for every `0 < δ ≤ 1 / 2`.
Choosing `δ = 1 / (4 * b * q)` and converting the resulting product `(8 * b * q) ^ (b * 2 ^ (4 * n))`
to base two gives the paper's fraction
`Exp (2, (log b + log q + log n) * b * 2 ^ (4 * g + 1) - 2 ^ n)` of [Knill1995], Theorem 5.1 once
the gate width `g` is at least the qubit count `n` and `n ≥ 8`.

Those two hypotheses are the honest price of the statement, not an artefact of the proof: the formal
net estimate carries the exponent `b * 2 ^ (4 * n)`, while the paper's exponent uses `b * 2 ^ (4 * g
+ 1)`. The factor `2 ^ (4 * g + 1 - 4 * n)` is at least two exactly when `g ≥ n`, and the small
`n ≥ 8` side condition supplies `log n ≥ (3 / 2)` so that the base change absorbs the constant
`log 8 = 3 * log 2`. The uniform statements of the paper are recovered only after the net estimate
is sharpened; this module does not claim them.

## Main statements

* `decision_fraction_exp_bound`: for `8 ≤ n ≤ g`, at most the stated `Exp (2, ·)` fraction of the
  `2 ^ (2 ^ n)` decision problems is decided with advantage `q`.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open Matrix Qatlib.Foundations.BornMetrics.FiniteStats
open Qatlib.Concepts.LocalCircuits.LocalGateCosts
namespace Qatlib.Papers.QCircApprox95.MainResults

open Qatlib.Papers.QCircApprox95.MainResults

/-- The base-two logarithm of a positive real is at least one half, in the form used to absorb the
constant `log 8` of the decision net count. -/
theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  linarith

/-- For `n ≥ 8`, the natural logarithm of `n` dominates `3 * log 2 = log 8`. -/
theorem three_log_two_le_log {n : ℕ} (hn : 8 ≤ n) :
    3 * Real.log 2 ≤ Real.log n := by
  have hlog : Real.log ((2 : ℝ) ^ 3) ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hpow : Real.log ((2 : ℝ) ^ 3) = 3 * Real.log 2 := by
    rw [Real.log_pow]
    norm_num
  linarith [hlog, hpow.symm.le, hpow.le]

/-- The constant `log 8` is absorbed by `2 * log 2 * (log n)` for `n ≥ 8`. -/
theorem three_log_two_le_two_mul {n : ℕ} (hn : 8 ≤ n) :
    3 * Real.log 2 ≤ 2 * Real.log 2 * Real.log n := by
  have hlogn := three_log_two_le_log hn
  have hlog2 := half_le_log_two
  nlinarith [hlogn, hlog2, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

/-- Scalar shape of the exponent comparison in Theorem 5.1: for a nonnegative `S`, `log n ≥ 3 / 2`
and `log 2 ≥ 1 / 2`, the logarithmic count `log (8 * b * q)` at
`b * 2 ^ (4 * n)` is dominated by `log 2` times the paper's exponent at `b * 2 ^ (4 * g + 1)`. -/
theorem three_log_two_add_le_two_mul_mul {S L : ℝ} (hS : 0 ≤ S) (hL : 3 * Real.log 2 ≤ L) :
    3 * Real.log 2 + S ≤ 2 * Real.log 2 * (S + L) := by
  have hlog2 := half_le_log_two
  have h2 : (0 : ℝ) ≤ 2 * Real.log 2 - 1 := by linarith
  have hprod : 0 ≤ (2 * Real.log 2 - 1) * S := mul_nonneg h2 hS
  have hprod' : 0 ≤ Real.log 2 * (L - 3 * Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hprod, hprod', hlog2, hS]

/-- **Theorem 5.1, restricted range.** For `8 ≤ n ≤ g`, at most the paper's exponential fraction
`Exp (2, (log b + log q + log n) * b * 2 ^ (4 * g + 1) - 2 ^ n)` of the `2 ^ (2 ^ n)` binary
decision problems on the computational basis is decided with advantage `q` by `b`-gate words of
width `g`. The decision net count is instantiated at `δ = 1 / (4 * b * q)`, which is admissible
because `1 ≤ b * q` forces `δ ≤ 1 / 2` and `2 * b * δ < 1 / q`. The range restriction `n ≤ g` and
the side condition `8 ≤ n` come from the exponent slack `2 ^ (4 * g + 1 - 4 * n)` and the base change
`log (8 * b * q) = 3 * log 2 + log b + log q`; the unrestricted paper statement needs a sharper net
estimate. Nothing here asserts the Corollary 5.2 asymptotics. -/
theorem decision_fraction_exp_bound (n g b : ℕ) (hn : 8 ≤ n) (hgn : n ≤ g) {q : ℝ}
    (hq : 0 < q) (hbq : 1 ≤ (b : ℝ) * q)
    (p : Fin (2 ^ n) → Fin 2) (F : Finset (Fin (2 ^ n) → Fin 2))
    (hF : ∀ f ∈ F, ∃ U ∈ repBy g n b,
      decides p q (fun x => U *ᵥ ket x) f) :
    (F.card : ℝ) / 2 ^ (2 ^ n) ≤
      exp2 ((Real.log b + Real.log q + Real.log n) * b * 2 ^ (4 * g + 1) - 2 ^ n) := by
  have hn1 : 1 ≤ n := by omega
  have hbq0 : (0 : ℝ) < (b : ℝ) * q := lt_of_lt_of_le one_pos hbq
  have hbpos : (0 : ℝ) < (b : ℝ) := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb] at hbq; push_cast at hbq; linarith
    · exact_mod_cast hb
  set δ : ℝ := 1 / (4 * ((b : ℝ) * q)) with hδdef
  have h4 : (0 : ℝ) < 4 * ((b : ℝ) * q) := mul_pos (by norm_num) hbq0
  have hδ0 : 0 < δ := by
    rw [hδdef]; exact div_pos one_pos h4
  have hδ : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_iff₀ h4]
    nlinarith [hbq]
  have hsmall : 2 * ((b : ℝ) * δ) < 1 / q := by
    have hq1 : 0 < 1 / q := div_pos one_pos hq
    have heq : 2 * ((b : ℝ) * δ) = (1 / 2) * (1 / q) := by
      rw [hδdef]
      field_simp
      ring
    rw [heq]
    nlinarith [hq1]
  have hnet := decision_net_count_concrete n g b hn1 hq hδ0 hδ hsmall p F hF
  -- the net cardinality is `(2 / δ) = 8 * b * q`
  have hratio : 2 / δ = 8 * ((b : ℝ) * q) := by
    rw [hδdef]
    field_simp
    ring
  rw [hratio] at hnet
  -- the exponent of the net count, as a real number
  set K : ℝ := ((b * 2 ^ (4 * n) : ℕ) : ℝ) with hKdef
  have hK : K = (b : ℝ) * (2 : ℝ) ^ (4 * n) := by
    rw [hKdef]; push_cast; ring
  set S : ℝ := Real.log b + Real.log q with hSdef
  set L : ℝ := Real.log n with hLdef
  set A : ℝ := (Real.log b + Real.log q + Real.log n) * b * 2 ^ (4 * g + 1) with hAdef
  have hSlog : S = Real.log ((b : ℝ) * q) := by
    rw [hSdef, Real.log_mul hbpos.ne' hq.ne']
  have hS : 0 ≤ S := by
    rw [hSlog]; exact Real.log_nonneg hbq
  have hL : 3 * Real.log 2 ≤ L := by
    rw [hLdef]; exact three_log_two_le_log hn
  -- base change: `(8 b q) ^ K = exp (log (8 b q) * K)` and `exp2 A = exp (log 2 * A)`
  have hbase : (0 : ℝ) < 8 * ((b : ℝ) * q) := mul_pos (by norm_num) hbq0
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log (8 * ((b : ℝ) * q)) = 3 * Real.log 2 + S := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hbq0.ne', hlog8, ← hSlog]
  have hscalar : 3 * Real.log 2 + S ≤ 2 * Real.log 2 * (S + L) :=
    three_log_two_add_le_two_mul_mul hS hL
  have hpow2 : (2 : ℝ) ^ (4 * n) * 2 ≤ (2 : ℝ) ^ (4 * g + 1) := by
    have h : (2 : ℝ) ^ (4 * n + 1) ≤ (2 : ℝ) ^ (4 * g + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    rw [pow_succ'] at h
    simpa only [mul_comm] using h
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [half_le_log_two]
  have hSL : 0 ≤ Real.log 2 * (S + L) := mul_nonneg hlog2pos.le (by linarith)
  -- the exponent comparison `log (8 b q) * K ≤ log 2 * A`
  have hexp : Real.log (8 * ((b : ℝ) * q)) * K ≤ Real.log 2 * A := by
    rw [hlog, hK, hAdef]
    have hstep : (3 * Real.log 2 + S) * ((b : ℝ) * (2 : ℝ) ^ (4 * n)) ≤
        (2 * Real.log 2 * (S + L)) * ((b : ℝ) * (2 : ℝ) ^ (4 * n)) := by
      apply mul_le_mul_of_nonneg_right hscalar (by positivity : (0 : ℝ) ≤ (b : ℝ) * (2 : ℝ) ^ (4 * n))
    have hstep' : (2 * Real.log 2 * (S + L)) * ((b : ℝ) * (2 : ℝ) ^ (4 * n)) ≤
        Real.log 2 * ((Real.log b + Real.log q + Real.log n) * (b : ℝ) * (2 : ℝ) ^ (4 * g + 1)) := by
      have hb0 : (0 : ℝ) ≤ (b : ℝ) := hbpos.le
      have hcomb : (2 : ℝ) * (2 : ℝ) ^ (4 * n) = (2 : ℝ) ^ (4 * n) * 2 := by ring
      calc (2 * Real.log 2 * (S + L)) * ((b : ℝ) * (2 : ℝ) ^ (4 * n))
          = (Real.log 2 * (S + L) * (b : ℝ)) * ((2 : ℝ) ^ (4 * n) * 2) := by
            rw [← hcomb]; ring
        _ ≤ (Real.log 2 * (S + L) * (b : ℝ)) * (2 : ℝ) ^ (4 * g + 1) :=
            mul_le_mul_of_nonneg_left hpow2 (mul_nonneg hSL hb0)
        _ = Real.log 2 *
            ((Real.log b + Real.log q + Real.log n) * (b : ℝ) * (2 : ℝ) ^ (4 * g + 1)) := by
            rw [hSdef, hLdef]; ring
    linarith [hstep, hstep']
  have hexp2 : exp2 A = Real.exp (Real.log 2 * A) := by
    unfold exp2
    exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) A
  have hnetK : (F.card : ℝ) ≤ (8 * ((b : ℝ) * q)) ^ K := by
    rw [hKdef, Real.rpow_natCast]
    exact hnet
  have hrpow : (8 * ((b : ℝ) * q)) ^ K ≤ exp2 A := by
    rw [Real.rpow_def_of_pos hbase K, hexp2]
    exact Real.exp_le_exp.mpr hexp
  have hcount : (F.card : ℝ) ≤ exp2 A := hnetK.trans hrpow
  have hfrac := fraction_bound_of_count F.card (2 ^ n) A hcount
  calc (F.card : ℝ) / 2 ^ (2 ^ n) = (F.card : ℝ) / (2 : ℝ) ^ (2 ^ n) := rfl
    _ ≤ exp2 (A - ((2 ^ n : ℕ) : ℝ)) := hfrac
    _ = exp2 ((Real.log b + Real.log q + Real.log n) * b * 2 ^ (4 * g + 1) - 2 ^ n) := by
        rw [hAdef]
        congr 1
        push_cast
        ring

end Qatlib.Papers.QCircApprox95.MainResults
