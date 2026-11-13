/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.QPowerSimon97.StandardModel.Theorem34Separation
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionOracle

/-!
# Joint quantum and classical bounds for Simon oracles

This module expresses quantum success and failure for Simon's labeled oracle distribution and
bounds average failure using `simonQuantumFailBound` [Simon1997]. It combines the amplified
quantum estimates with the classical query-tree bound to obtain `simonJointSeparation` on a
common oracle draw.

## Main statements

* `simonQuantumFail_le`: For positive width and at least two samples, expected quantum failure
  is bounded above by `simonQuantumFailBound`.
* `simonQuantumGuessMass_lower`: For positive width and at least two samples, quantum guessing
  mass is at least one minus `simonQuantumFailBound`.
* `simonJointSeparation`: For `n ≥ 64`, every randomized query tree with query budget at most `2
  ^ ((n : ℝ) / 4)` has strictly smaller success than the specified quantum procedure on some
  supported oracle draw. This gives a common-draw separation in the setting of [Simon1997].

## References

* [Simon, 1997][Simon1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Papers.QPowerSimon97.Recovery.SimonAssembly
open Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstruction
open Qatlib.Papers.QPowerSimon97.StandardDefs

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib
open scoped Classical BigOperators ENNReal

/-- The success probability of the amplified quantum decision procedure on a labeled oracle
draw. -/
noncomputable def simonQuantumSuccess (n k r : ℕ)
    (ob : Bool × (BooleanVec n → BooleanVec n)) : ℝ≥0∞ :=
  if ob.1 then (simonAmplifiedReject ob.2 (n + k) r) true
  else 1 - (simonAmplifiedReject ob.2 (n + k) r) true

/-- The failure probability of the amplified quantum decision procedure on a labeled oracle
draw. -/
noncomputable def simonQuantumFail (n k r : ℕ)
    (ob : Bool × (BooleanVec n → BooleanVec n)) : ℝ≥0∞ :=
  if ob.1 then 1 - (simonAmplifiedReject ob.2 (n + k) r) true
  else (simonAmplifiedReject ob.2 (n + k) r) true

/-- The quantum guessing mass equals the expected pointwise success over Simon's oracle
construction. -/
theorem simonQuantumGuessMass_eq_success (n k r : ℕ) :
    simonQuantumGuessMass (n := n) k r =
      expectation (simonOracleConstruction n) (simonQuantumSuccess n k r) := rfl

/-- Pointwise quantum success and failure probabilities sum to one. -/
lemma simonQuantumSuccess_add_fail (n k r : ℕ)
    (ob : Bool × (BooleanVec n → BooleanVec n)) :
    simonQuantumSuccess n k r ob + simonQuantumFail n k r ob = 1 := by
  obtain ⟨b, g⟩ := ob
  have hle : (simonAmplifiedReject g (n + k) r) true ≤ 1 :=
    PMF.coe_le_one (simonAmplifiedReject g (n + k) r) true
  cases b
  · simp only [simonQuantumSuccess, simonQuantumFail, Bool.false_eq_true, if_false]
    exact tsub_add_cancel_of_le hle
  · simp only [simonQuantumSuccess, simonQuantumFail, if_true]
    rw [add_comm]
    exact tsub_add_cancel_of_le hle

/-- The quantum guessing mass equals one minus the expected quantum failure probability. -/
theorem simonQuantumGuessMass_eq_one_sub_fail (n k r : ℕ) :
    simonQuantumGuessMass (n := n) k r =
      1 - expectation (simonOracleConstruction n) (simonQuantumFail n k r) := by
  have hsum : expectation (simonOracleConstruction n) (simonQuantumSuccess n k r) +
      expectation (simonOracleConstruction n) (simonQuantumFail n k r) = 1 := by
    rw [← expectation_add]
    calc expectation (simonOracleConstruction n)
          (fun ob => simonQuantumSuccess n k r ob + simonQuantumFail n k r ob)
        = expectation (simonOracleConstruction n) (fun _ => 1) :=
          expectation_congr fun ob => simonQuantumSuccess_add_fail n k r ob
      _ = 1 := expectation_const _ 1
  have hfail_le_one : expectation (simonOracleConstruction n) (simonQuantumFail n k r) ≤ 1 := by
    refine (expectation_le_of_forall (p := simonOracleConstruction n)
      (f := simonQuantumFail n k r) (g := fun _ => 1) ?_).trans_eq
      (expectation_const _ 1)
    intro ob
    unfold simonQuantumFail
    split_ifs
    · exact tsub_le_self
    · exact PMF.coe_le_one (simonAmplifiedReject ob.2 (n + k) r) true
  have hne : expectation (simonOracleConstruction n) (simonQuantumFail n k r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hfail_le_one
  rw [simonQuantumGuessMass_eq_success]
  exact ENNReal.eq_sub_of_add_eq hne hsum

/-- The true and false masses of the amplified rejection law sum to one. -/
lemma simonReject_total {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) (m r : ℕ) :
    (simonAmplifiedReject f m r) true + (simonAmplifiedReject f m r) false = 1 := by
  rw [pmf_bool_true, pmf_bool_false]
  have hpart := event_partition (simonAmplifiedReject f m r) (fun b => b = true)
  have heq : event (simonAmplifiedReject f m r) (fun b => ¬ (b = true))
      = event (simonAmplifiedReject f m r) (fun b => b = false) := by
    unfold event
    apply expectation_congr
    intro x
    by_cases hx : x = true <;> simp [hx]
  rw [heq] at hpart
  exact hpart

/-- Expected quantum failure decomposes into an average over masks of the equally weighted
two-to-one and permutation failure terms. -/
theorem simonQuantumFail_decomp (n k r : ℕ) :
    expectation (simonOracleConstruction n) (simonQuantumFail n k r) =
      expectation (PMF.uniformOfFintype' (BooleanVec n)) (fun s =>
        (1 / 2 : ℝ≥0∞) *
          (expectation (simonTwoToOneDist s)
              (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) +
           expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
              (fun (π : Equiv.Perm (BooleanVec n)) =>
                (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true))) := by
  unfold simonQuantumFail
  rw [simonOracleConstruction, expectation_bind]
  apply expectation_congr
  intro s
  rw [expectation_bind, expectation_uniform_bool]
  simp only [Bool.false_eq_true, if_false, if_true, expectation_map]
  rw [mul_add]
  congr 1
  congr 1
  change expectation ((PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n))).map
    (fun (π : Equiv.Perm (BooleanVec n)) => (π : BooleanVec n → BooleanVec n)))
    (fun f => (simonAmplifiedReject f (n + k) r) true) = _
  rw [expectation_map]

/-- A pointwise inequality on the nonzero-mass support of a probability law yields the
corresponding expectation inequality. -/
private lemma expectation_le_of_support {α : Type*} {p : PMF α} {f g : α → ℝ≥0∞}
    (h : ∀ a, p a ≠ 0 → f a ≤ g a) : expectation p f ≤ expectation p g := by
  show ∑' a, p a * f a ≤ ∑' a, p a * g a
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hp : p a = 0
  · simp [hp]
  · exact mul_le_mul_right (h a hp) _

/-- For positive width, a nonzero mask, and at least two samples, the expected false-negative
mass under the Simon oracle law is at most `(3 / 4) ^ r`. -/
lemma simonFail_twoToOne_le (n k r : ℕ) (hn : 1 ≤ n) (h2 : 2 ≤ n + k)
    (s : BooleanVec n) (hs : s ≠ 0) :
    expectation (simonTwoToOneDist s)
      (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) ≤
      ENNReal.ofReal ((3 / 4 : ℝ) ^ r) := by
  refine (expectation_le_of_support ?_).trans_eq (expectation_const _ _)
  intro f hf
  have hpos : simonTwoToOneDist s f ≠ 0 := by
    simpa [PMF.mem_support_iff] using! hf
  have hstr := simonTwoToOneDist_of_pos hn s hpos
  have hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n := by
    have hempty : {x : BooleanVec n | f x ≠ f (x + s)} = ∅ := by
      ext x
      simp [hstr.1 x]
    simp [hempty]
  have hle : (simonAmplifiedReject f (n + k) r) false ≤
      ENNReal.ofReal ((3 / 4 : ℝ) ^ r) :=
    (simonNegligibleErrorAmplification n (BooleanVec n) f k r h2).2.1 s hs hcard
  have htot := simonReject_total f (n + k) r
  have hbne : (simonAmplifiedReject f (n + k) r) true ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.coe_le_one (simonAmplifiedReject f (n + k) r) true)
  have hcomm : (simonAmplifiedReject f (n + k) r) false +
      (simonAmplifiedReject f (n + k) r) true = 1 := by
    rw [add_comm]
    exact htot
  have heq : 1 - (simonAmplifiedReject f (n + k) r) true =
      (simonAmplifiedReject f (n + k) r) false :=
    (ENNReal.eq_sub_of_add_eq hbne hcomm).symm
  rw [heq]
  exact hle

/-- With at least two samples, the expected true-output mass under a uniformly random
permutation is at most `r * (1 / 2) ^ k`. -/
lemma simonFail_perm_le (n k r : ℕ) (h2 : 2 ≤ n + k) :
    expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
      (fun (π : Equiv.Perm (BooleanVec n)) =>
        (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true) ≤
      ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) := by
  refine (expectation_le_of_forall ?_).trans_eq (expectation_const _ _)
  intro π
  exact (simonNegligibleErrorAmplification n (BooleanVec n)
    (π : BooleanVec n → BooleanVec n) k r h2).1 π.injective

/-- A uniformly random Boolean vector is zero with probability the reciprocal of `2 ^ n`. -/
lemma expectation_uniform_zero_indicator (n : ℕ) :
    expectation (PMF.uniformOfFintype' (BooleanVec n))
      (fun s => if s = (0 : BooleanVec n) then (1 : ℝ≥0∞) else 0) =
      (2 ^ n : ℝ≥0∞)⁻¹ := by
  rw [expectation, tsum_fintype]
  rw [Finset.sum_eq_single (0 : BooleanVec n)]
  · rw [if_pos rfl, mul_one, PMF.uniformOfFintype'_apply]
    have hcard : ((Fintype.card (BooleanVec n) : ℕ) : ℝ≥0∞) = (2 ^ n : ℝ≥0∞) := by
      rw [show Fintype.card (BooleanVec n) = 2 ^ n from by simp [BooleanVec, ZMod.card]]
      norm_num
    rw [hcard]
  · intro b _ hb
    rw [if_neg hb, mul_zero]
  · intro h0
    exact absurd (Finset.mem_univ (0 : BooleanVec n)) h0

/-- The half-weighted sum of the two-to-one amplification error, the permutation false-rejection
bound, and the zero-mask probability. -/
noncomputable def simonQuantumFailBound (n k r : ℕ) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) *
    (ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
      ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) + (2 ^ n : ℝ≥0∞)⁻¹)

/-- For positive width and at least two samples, expected quantum failure is bounded above by
`simonQuantumFailBound`. -/
theorem simonQuantumFail_le (n k r : ℕ) (hn : 1 ≤ n) (h2 : 2 ≤ n + k) :
    expectation (simonOracleConstruction n) (simonQuantumFail n k r) ≤
      simonQuantumFailBound n k r := by
  unfold simonQuantumFailBound
  rw [simonQuantumFail_decomp]
  have hA (s : BooleanVec n) (hs : s ≠ 0) :
      expectation (simonTwoToOneDist s)
        (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) ≤
        ENNReal.ofReal ((3 / 4 : ℝ) ^ r) :=
    simonFail_twoToOne_le n k r hn h2 s hs
  have hB : expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
      (fun (π : Equiv.Perm (BooleanVec n)) =>
        (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true) ≤
      ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) :=
    simonFail_perm_le n k r h2
  have hA0 : expectation (simonTwoToOneDist (0 : BooleanVec n))
      (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) ≤ 1 := by
    refine (expectation_le_of_forall (fun f => ?_)).trans_eq (expectation_const _ _)
    exact tsub_le_self
  have hpt : ∀ s : BooleanVec n,
      (1 / 2 : ℝ≥0∞) *
        (expectation (simonTwoToOneDist s)
            (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) +
         expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
            (fun (π : Equiv.Perm (BooleanVec n)) =>
              (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true)) ≤
      (1 / 2 : ℝ≥0∞) *
        (ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
          ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) +
          (if s = (0 : BooleanVec n) then 1 else 0)) := by
    intro s
    have hcore :
        expectation (simonTwoToOneDist s)
            (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) +
          expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
            (fun (π : Equiv.Perm (BooleanVec n)) =>
              (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true) ≤
        ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
          ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) +
          (if s = (0 : BooleanVec n) then 1 else 0) := by
      by_cases hs : s = 0
      · subst hs
        rw [if_pos rfl]
        calc
          expectation (simonTwoToOneDist (0 : BooleanVec n))
                (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) +
              expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
                (fun (π : Equiv.Perm (BooleanVec n)) =>
                  (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true)
              ≤ 1 + ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) :=
                add_le_add hA0 hB
          _ ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
                ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) + 1 := by
                calc
                  1 + ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)
                      ≤ (1 + ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k)) +
                          ENNReal.ofReal ((3 / 4 : ℝ) ^ r) := le_add_right le_rfl
                  _ = ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
                        ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) + 1 := by ac_rfl
      · rw [if_neg hs]
        calc
          expectation (simonTwoToOneDist s)
                (fun f => 1 - (simonAmplifiedReject f (n + k) r) true) +
              expectation (PMF.uniformOfFintype' (Equiv.Perm (BooleanVec n)))
                (fun (π : Equiv.Perm (BooleanVec n)) =>
                  (simonAmplifiedReject (π : BooleanVec n → BooleanVec n) (n + k) r) true)
              ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
                ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) := add_le_add (hA s hs) hB
          _ = ENNReal.ofReal ((3 / 4 : ℝ) ^ r) +
                ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) + 0 := by rw [add_zero]
    simpa only [mul_comm] using! mul_le_mul_right hcore (1 / 2 : ℝ≥0∞)
  refine (expectation_le_of_forall hpt).trans ?_
  rw [expectation_const_mul, expectation_add, expectation_const,
    expectation_uniform_zero_indicator]

/-- For positive width and at least two samples, quantum guessing mass is at least one minus
`simonQuantumFailBound`. -/
theorem simonQuantumGuessMass_lower (n k r : ℕ) (hn : 1 ≤ n) (h2 : 2 ≤ n + k) :
    1 - simonQuantumFailBound n k r ≤ simonQuantumGuessMass (n := n) k r := by
  rw [simonQuantumGuessMass_eq_one_sub_fail]
  exact tsub_le_tsub_left (simonQuantumFail_le n k r hn h2) 1

/-- For `n ≥ 64`, the permutation error expression `n * (1 / 2) ^ (2 * n)` is at most `1 / 8`. -/
lemma simonPaperFalseReject_le_eighth (n : ℕ) (hn : 64 ≤ n) :
    (n : ℝ) * (1 / 2 : ℝ) ^ (2 * n) ≤ 1 / 8 := by
  have hn1 : 1 ≤ n := by omega
  have hfirst : (n : ℝ) * (1 / 2 : ℝ) ^ (2 * n) ≤ (1 / 2 : ℝ) ^ n := by
    have h := simonPaperFalseReject_le n hn1
    simpa [simonPaperFalseReject] using! h
  have hsecond : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : 3 ≤ n)
  have hval : (1 / 2 : ℝ) ^ 3 = 1 / 8 := by norm_num
  linarith

/-- For `n ≥ 64`, the quantum failure bound with parameters `2 * n` and `n` is at most `3 / 16`. -/
theorem simonQuantumFailBound_le (n : ℕ) (hn : 64 ≤ n) :
    simonQuantumFailBound n (2 * n) n ≤ ENNReal.ofReal (3 / 16) := by
  unfold simonQuantumFailBound
  have hfa : ENNReal.ofReal ((3 / 4 : ℝ) ^ n) ≤ ENNReal.ofReal (1 / 8) :=
    ENNReal.ofReal_le_ofReal (simonThreeQuarters_pow_le n hn)
  have hfr : ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) ≤
      ENNReal.ofReal (1 / 8) :=
    ENNReal.ofReal_le_ofReal (simonPaperFalseReject_le_eighth n hn)
  have h8 : ENNReal.ofReal (1 / 8 : ℝ) = (8 : ℝ≥0∞)⁻¹ := by
    rw [show (1 / 8 : ℝ) = (8 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have h8le : (8 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
    have h8n : (8 : ℕ) ≤ 2 ^ n := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ n)
    calc (8 : ℝ≥0∞) = ((8 : ℕ) : ℝ≥0∞) := by norm_num
      _ ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast h8n
      _ = (2 : ℝ≥0∞) ^ n := by push_cast; ring
  have hjun : (2 ^ n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (1 / 8) := by
    rw [h8]
    exact ENNReal.inv_le_inv.mpr h8le
  have hsum : ENNReal.ofReal ((3 / 4 : ℝ) ^ n) +
      ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) + (2 ^ n : ℝ≥0∞)⁻¹ ≤
      ENNReal.ofReal (3 / 8) := by
    calc
      ENNReal.ofReal ((3 / 4 : ℝ) ^ n) +
          ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) + (2 ^ n : ℝ≥0∞)⁻¹
          ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) +
              ENNReal.ofReal (1 / 8) := by gcongr
      _ = ENNReal.ofReal (3 / 8) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  calc
    (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal ((3 / 4 : ℝ) ^ n) +
        ENNReal.ofReal ((n : ℝ) * (1 / 2 : ℝ) ^ (2 * n)) + (2 ^ n : ℝ≥0∞)⁻¹)
        ≤ (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (3 / 8) := by gcongr
    _ = ENNReal.ofReal (3 / 16) := by
        rw [← hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num

/-- For `n ≥ 64`, every randomized query tree with query budget at most `2 ^ ((n : ℝ) / 4)` has
strictly smaller success than the specified quantum procedure on some supported oracle draw.
This gives a common-draw separation in the setting of [Simon1997]. -/
theorem simonJointSeparation (n : ℕ) (hn : 64 ≤ n) (q : ℕ)
    (hq : (q : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4)) (P : PMF (SimonQueryTree n))
    (hP : SimonQueryTree.bounded P q) :
    ∃ ob ∈ (simonOracleConstruction n).support,
      SimonQueryTree.guessMass P ob.2 ob.1 <
        simonQuantumSuccess n (2 * n) n ob := by
  by_contra h
  push Not at h
  have hclassical : simonOracleGuessMass P ≤ ENNReal.ofReal (5 / 8) := by
    have h0 : simonOracleGuessMass P ≤
        ENNReal.ofReal (1 / 2 + (2 : ℝ) ^ (-(n : ℝ) / 2)) :=
      simonTheorem33RealBudget n (by omega) q hq P hP
    have h1 : (1 / 2 : ℝ) + (2 : ℝ) ^ (-(n : ℝ) / 2) ≤ 5 / 8 := by
      have := simonExponentHalf_le n hn
      linarith
    exact h0.trans (ENNReal.ofReal_le_ofReal h1)
  have hquantum : ENNReal.ofReal (13 / 16) ≤
      expectation (simonOracleConstruction n) (simonQuantumSuccess n (2 * n) n) := by
    have hlow := simonQuantumGuessMass_lower n (2 * n) n (by omega) (by omega)
    rw [simonQuantumGuessMass_eq_success] at hlow
    have hb := simonQuantumFailBound_le n hn
    have hsub : ENNReal.ofReal (13 / 16) ≤ 1 - simonQuantumFailBound n (2 * n) n := by
      refine le_trans ?_ (tsub_le_tsub_left hb 1)
      have hrew : (1 : ℝ≥0∞) - ENNReal.ofReal (3 / 16) = ENNReal.ofReal (13 / 16) := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 3 / 16)]
        norm_num
      rw [hrew]
    exact hsub.trans hlow
  have hmono : expectation (simonOracleConstruction n) (simonQuantumSuccess n (2 * n) n) ≤
      simonOracleGuessMass P := by
    have hmem : ∀ ob, simonOracleConstruction n ob ≠ 0 →
        simonQuantumSuccess n (2 * n) n ob ≤ SimonQueryTree.guessMass P ob.2 ob.1 := by
      intro ob hob
      exact h ob (by simpa [PMF.mem_support_iff] using! hob)
    have := expectation_le_of_support (p := simonOracleConstruction n)
      (f := simonQuantumSuccess n (2 * n) n)
      (g := fun ob => SimonQueryTree.guessMass P ob.2 ob.1) hmem
    simpa [simonOracleGuessMass] using! this
  have hchain : ENNReal.ofReal (13 / 16) ≤ ENNReal.ofReal (5 / 8) :=
    hquantum.trans (hmono.trans hclassical)
  have hlt : ENNReal.ofReal (5 / 8) < ENNReal.ofReal (13 / 16) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 13 / 16)]
    norm_num
  exact absurd hchain (not_le.mpr hlt)

end Qatlib.Papers.QPowerSimon97.StandardDefs
