/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamPeriodRecoveryStat
import Qatlib.Concepts.AmpTransform.ErrorStream.ErrorStreamSuccessMass

/-!
# Retry bounds for error-stream period recovery

This module proves `ErrorStreamPeriodRecovery` using the amplified progression recovery window
and the finite retry routine. For independent labels drawn from the actual amplified-state Born
distribution, it identifies the exact timeout mass and bounds the mass of returning the planted
period under the stated noise and size assumptions.

The proof also records a worst-case query bound and an expected query bound obtained from the
one-attempt success lower bound. A successful first attempt supplies the planted-period mass
bound for the retry routine.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `errorStreamPeriodRecovery`: normalization, timeout and recovery masses, and query bounds.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.AmpTransform.SuccessRatio
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.AmpTransform.ErrorStream

open scoped Classical BigOperators

/-- If every attempt including its overhead costs at most `C`, repeating over a list costs at
most `xs.length * C`. -/
private theorem aqRepeat_cost_cap {I Z : Type} (a : I → Option Z × ℕ) (k C : ℕ)
    (hc : ∀ x, k+(a x).2 ≤ C) (xs : List I) :
    (aqRepeat a k xs).2 ≤ xs.length*C := by
  induction xs with
  | nil => simp [aqRepeat]
  | cons x xs ih =>
    cases hn : (a x).1 with
    | none =>
      simp only [aqRepeat, hn, List.length_cons]
      have hi := ih
      have hh := hc x
      calc
        (aqRepeat a k xs).2 + k + (a x).2 = (aqRepeat a k xs).2 + (k + (a x).2) := by ring
        _ ≤ (aqRepeat a k xs).2 + C := Nat.add_le_add_left hh _
        _ ≤ xs.length*C + C := Nat.add_le_add_right hi C
        _ = (xs.length+1)*C := by rw [← Nat.succ_eq_add_one, Nat.succ_mul]
    | some z =>
      simp only [aqRepeat, hn, List.length_cons]
      have hh := hc x
      have h2 : C ≤ (xs.length+1)*C := by
        have hm := Nat.mul_le_mul_right C (show (1:ℕ) ≤ xs.length+1 by omega)
        simpa using! hm
      exact hh.trans h2

/-- A finite product-record mass is nonnegative when every one-trial weight is nonnegative. -/
private theorem aqProductMass_nonneg {I : Type} [Fintype I] (w : I → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) {R : ℕ} (ω : Fin R → I) : 0 ≤ aqProductMass w ω := by
  unfold aqProductMass
  exact Finset.prod_nonneg fun r _ => hw0 (ω r)

/-- If the first recovery attempt returns `some P`, retrying on the whole nonempty label list
also returns `some P`. -/
private theorem aqRetry_first_some {N : ℕ} (f : Fin N → Bool) (s M B k P : ℕ)
    (x : Fin N) (xs : List (Fin N)) (hx : (aqAttempt f s M B x).1 = some P) :
    (aqRetry f s M B k (x :: xs)).1 = some P := by
  rw [aqRetry_as_repeat f s M B k (x :: xs)]
  simp [aqRepeat, hx]

/-- For a nonempty indexed label record, a first attempt returning `some P` forces the retry
output on `List.ofFn ω` to be `some P`. -/
private theorem aq_error_retry_first_record {N : ℕ} (f : Fin N → Bool) (s M B k P R : ℕ)
    [NeZero R] (hR : 0 < R) (ω : Fin R → Fin N)
    (hx : (aqAttempt f s M B (ω 0)).1 = some P) :
    (aqRetry f s M B k (List.ofFn ω)).1 = some P := by
  obtain ⟨R', hR'⟩ : ∃ R', R = R'+1 := ⟨R-1, by omega⟩
  subst hR'
  have hcons : Fin.cons (ω 0) (fun i : Fin R' => ω i.succ) = ω := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
    · simp only [Fin.cons_succ]
  have hsplit : List.ofFn ω = ω 0 :: List.ofFn (fun i : Fin R' => ω i.succ) := by
    rw [← hcons, List.ofFn_succ]
  rw [hsplit]
  exact aqRetry_first_some f s M B k P (ω 0) (List.ofFn (fun i : Fin R' => ω i.succ)) hx

/-- Establish normalization, the exact retry timeout mass, a lower bound on planted-period
recovery mass, and worst-case and expected query bounds under `ErrorStreamPeriodRecovery`'s
assumptions; see [Cornwell, Section 3.1][Cornwell2014]. -/
theorem errorStreamPeriodRecovery : ErrorStreamPeriodRecovery := by
  intro N hN s M L P B R G h hM hP hb hMP hPB hsepB hG hdis h2T hsepR hRpos hmark
  (try dsimp only)
  set C := aqProgressionSet N s M P ∪ G with hC
  set T := M+L with hT
  set w : Fin N → ℝ := fun y => BornProb (aqState N hN T C) y with hw
  set b : ℝ := ∑ y, if (aqAttempt h s M B y).1 = none then w y else 0 with hbdef
  set q := aqErrorSuccessLower N M L P with hq
  set k := aqRounds N T with hk
  set a : Fin N → Option ℕ × ℕ := fun y => ((aqAttempt h s M B y).1, (aqAttempt h s M B y).2.1)
    with ha
  have hw0 : ∀ y, 0 ≤ w y := fun _ => bornProb_nonneg _ _
  have hw1 : (∑ y, w y) = 1 := (aq_error_word_counts N hN T C).2.2.2.2
  have hwin := aq_error_window_mass_lower N hN s M L P G h hM hP hb hMP hG hdis h2T hsepR hmark
  have hgood : ∀ y, y ∈ aqGoodWindow N P → (a y).1 = some P := by
    intro y hy
    exact (aq_error_attempt_sound_and_counts N s M P B G h y hM hP hb hPB hsepB hmark).1 hy
  have hcost : ∀ y, k + (a y).2 ≤ k+3 := by
    intro y
    have hc := (aq_error_attempt_sound_and_counts N s M P B G h y hM hP hb hPB hsepB hmark).2.2.1
    have hcy : (aqAttempt h s M B y).2.1 = (a y).2 := rfl
    omega
  have hpmass : q ≤ ∑ y, if (a y).1 = some P then w y else 0 :=
    aq_error_attempt_mass_lower N hN s M L P B G h P (fun y => (a y).1) hgood
      hM hP hb hMP hPB hsepB hG hdis h2T hsepR hmark
  have hpoint (y : Fin N) :
      ((if (a y).1 = none then w y else 0) + (if (a y).1 = some P then w y else 0)) ≤ w y := by
    by_cases hn : (a y).1 = none
    · have hnot : ¬((a y).1 = some P) := by rw [hn]; simp
      rw [if_pos hn, if_neg hnot]
      simp
    · by_cases hp : (a y).1 = some P
      · rw [if_neg hn, if_pos hp]
        simp
      · rw [if_neg hn, if_neg hp]
        simpa using! (bornProb_nonneg _ _)
  have hle : (∑ y,
      ((if (a y).1 = none then w y else 0) + (if (a y).1 = some P then w y else 0))) ≤ ∑ y, w y :=
      Finset.sum_le_sum fun y _ => hpoint y
  have hsplit : b + (∑ y, if (a y).1 = some P then w y else 0) ≤ 1 := by
    calc
      b + (∑ y, if (a y).1 = some P then w y else 0)
          = (∑ y, if (a y).1 = none then w y else 0)
            + (∑ y, if (a y).1 = some P then w y else 0) := by rw [← hbdef]
      _ = ∑ y, ((if (a y).1 = none then w y else 0) + (if (a y).1 = some P then w y else 0)) := by
        rw [Finset.sum_add_distrib]
      _ ≤ ∑ y, w y := hle
      _ = 1 := hw1
  have hbq : b ≤ 1-q := by linarith [hsplit, hpmass]
  have hnorm : (∑ ω : Fin R → Fin N, ∏ r, w (ω r)) = 1 := aqProductMass_total w hw1 R
  have htimeout : (∑ ω : Fin R → Fin N, if (aqRetry h s M B k (List.ofFn ω)).1 = none
      then ∏ r, w (ω r) else 0) = b^R := by
    calc
      (∑ ω : Fin R → Fin N, if (aqRetry h s M B k (List.ofFn ω)).1 = none
          then ∏ r, w (ω r) else 0)
          = ∑ ω : Fin R → Fin N, if (aqRepeat a k (List.ofFn ω)).1 = none
            then ∏ r, w (ω r) else 0 := by
              apply Finset.sum_congr rfl
              intro ω _
              have he : (aqRetry h s M B k (List.ofFn ω)) = aqRepeat a k (List.ofFn ω) := by
                rw [aqRetry_as_repeat h s M B k]
              rw [he]
      _ = (∑ x, if (a x).1 = none then w x else 0)^R := aqRepeat_timeout w a k R
      _ = b^R := rfl
  have hsucc : q ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin R → Fin N =>
      (aqRetry h s M B k (List.ofFn ω)).1 = some P), ∏ r, w (ω r) := by
    obtain ⟨R', hR'⟩ : ∃ R', R = R'+1 := ⟨R-1, by omega⟩
    subst hR'
    have hfirst : (∑ ω : Fin (R'+1) → Fin N, if (a (ω 0)).1 = some P
        then aqProductMass w ω else 0) = ∑ y, if (a y).1 = some P then w y else 0 := by
      rw [aq_sum_records_succ R' (fun ω : Fin (R'+1) → Fin N =>
        if (a (ω 0)).1 = some P then aqProductMass w ω else 0)]
      simp only [Fin.cons_zero, aqProductMass_cons]
      calc
        (∑ x : Fin N, ∑ τ : Fin R' → Fin N,
              (if (a x).1 = some P then w x*aqProductMass w τ else 0))
            = ∑ x : Fin N, ∑ τ : Fin R' → Fin N,
              (if (a x).1 = some P then w x else 0) * aqProductMass w τ := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro τ _
              by_cases hzx : (a x).1 = some P <;> simp [hzx]
        _ = ∑ x : Fin N, (if (a x).1 = some P then w x else 0) *
                ∑ τ : Fin R' → Fin N, aqProductMass w τ := by
              apply Finset.sum_congr rfl
              intro x _
              exact (Finset.mul_sum (R := ℝ) (s := (Finset.univ : Finset (Fin R' → Fin N)))
                (fun τ => aqProductMass w τ)
                (if (a x).1 = some P then w x else 0)).symm
        _ = _ := by
              rw [aqProductMass_total w hw1 R']
              ring_nf
    have hle : (∑ ω : Fin (R'+1) → Fin N, if (a (ω 0)).1 = some P
          then aqProductMass w ω else 0)
        ≤ ∑ ω : Fin (R'+1) → Fin N, if (aqRetry h s M B k (List.ofFn ω)).1 = some P
          then aqProductMass w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hfirstω : (a (ω 0)).1 = some P
      · have hretry := aq_error_retry_first_record h s M B k P (R'+1) (by omega) ω hfirstω
        rw [if_pos hfirstω, if_pos hretry]
      · rw [if_neg hfirstω]
        by_cases hretry : (aqRetry h s M B k (List.ofFn ω)).1 = some P
        · rw [if_pos hretry]
          exact aqProductMass_nonneg w hw0 ω
        · rw [if_neg hretry]
    calc
      q ≤ ∑ y, if (a y).1 = some P then w y else 0 := hpmass
      _ = ∑ ω : Fin (R'+1) → Fin N, if (a (ω 0)).1 = some P then aqProductMass w ω else 0 :=
        hfirst.symm
      _ ≤ ∑ ω : Fin (R'+1) → Fin N, if (aqRetry h s M B k (List.ofFn ω)).1 = some P
          then aqProductMass w ω else 0 := hle
      _ = ∑ ω ∈ Finset.univ.filter (fun ω : Fin (R'+1) → Fin N =>
          (aqRetry h s M B k (List.ofFn ω)).1 = some P), ∏ r, w (ω r) := by
        rw [Finset.sum_filter]
        rfl
  have hcap : (∀ ω : Fin R → Fin N, (aqRetry h s M B k (List.ofFn ω)).2 ≤ R*(k+3)) := by
    intro ω
    have hc := aqRepeat_cost_cap a k (k+3) hcost (List.ofFn ω)
    have he : (aqRetry h s M B k (List.ofFn ω)) = aqRepeat a k (List.ofFn ω) := by
      rw [aqRetry_as_repeat h s M B k]
    rw [he]
    simpa using! hc
  have hexp : (∑ ω : Fin R → Fin N, (∏ r, w (ω r))*
        ((aqRetry h s M B k (List.ofFn ω)).2:ℝ)) ≤ ((k+3:ℕ):ℝ)/q := by
    calc
      (∑ ω : Fin R → Fin N, aqProductMass w ω*
          ((aqRetry h s M B k (List.ofFn ω)).2:ℝ))
          = ∑ ω : Fin R → Fin N, aqProductMass w ω*((aqRepeat a k (List.ofFn ω)).2:ℝ) := by
              apply Finset.sum_congr rfl
              intro ω _
              have he : (aqRetry h s M B k (List.ofFn ω)) = aqRepeat a k (List.ofFn ω) := by
                rw [aqRetry_as_repeat h s M B k]
              rw [he]
      _ ≤ ((k+3:ℕ):ℝ)/q :=
        aqRepeat_expected w a k (k+3) q hw0 hw1 hwin.1 hbq hcost R
  exact ⟨hnorm, htimeout, hsucc, hcap, hexp⟩

end Qatlib.Concepts.AmpTransform.ErrorStream
