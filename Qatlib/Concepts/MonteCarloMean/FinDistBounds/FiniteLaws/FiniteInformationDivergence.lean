/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open scoped BigOperators Classical
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def kl (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : ℝ :=
  ∑ x, p.prob x * (Real.log (p.prob x)-Real.log (q.prob x))

def tv (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : ℝ :=
    (∑ x, |p.prob x-q.prob x|)/2

def records (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin n → X) :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw (fun _ => p)

omit [DecidableEq X] in

@[simp] theorem kl_self (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : kl p p = 0 := by simp [kl]
omit [DecidableEq X] in

@[simp] theorem tv_self (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : tv p p = 0 := by simp [tv]

omit [DecidableEq X] in

theorem kl_nonneg (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) : 0 ≤ kl p q := by
  have h (x : X) : p.prob x-q.prob x ≤
      p.prob x * (Real.log (p.prob x)-Real.log (q.prob x)) := by
    have hl := Real.log_le_sub_one_of_pos (div_pos (hq x) (hp x))
    rw [Real.log_div (hq x).ne' (hp x).ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl (hp x).le
    have he : p.prob x * (q.prob x/p.prob x-1) = q.prob x-p.prob x := by
      field_simp [(hp x).ne']
    rw [he] at hm
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => h x)
  simpa [kl, Finset.sum_sub_distrib, p.sum_one, q.sum_one] using hs

theorem kl_records (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) (n : ℕ) :
    kl (records p n) (records q n) = (n : ℝ) * kl p q := by
  have hlog (w : Fin n → X) :
      Real.log ((records p n).prob w)-Real.log ((records q n).prob w) =
        ∑ i, (Real.log (p.prob (w i))-Real.log (q.prob (w i))) := by
    rw [show (records p n).prob w = ∏ i, p.prob (w i) from rfl,
      show (records q n).prob w = ∏ i, q.prob (w i) from rfl,
      Real.log_prod (fun i _ => (hp _).ne'), Real.log_prod (fun i _ => (hq _).ne'),
      Finset.sum_sub_distrib]
  calc
    kl (records p n) (records q n) =
        ∑ i : Fin n, ∑ w : Fin n → X, p.probOf w *
          (Real.log (p.prob (w i))-Real.log (q.prob (w i))) := by
      simp only [kl, hlog, Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl
    _ = ∑ _i : Fin n, kl p q := by
      apply Finset.sum_congr rfl
      intro i _
      exact p.expect_coord i (fun x => Real.log (p.prob x)-Real.log (q.prob x))
    _ = (n : ℝ) * kl p q := by simp

def errorSum (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (decideQ : X → Bool) : ℝ :=
  ∑ x, if decideQ x = true then p.prob x else q.prob x

omit [DecidableEq X] in

theorem errorSum_lower (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (f : X → Bool) :
    1-tv p q ≤ errorSum p q f := by
  have h (x : X) : p.prob x+q.prob x-|p.prob x-q.prob x| ≤
      2*(if f x = true then p.prob x else q.prob x) := by
    have h1 := le_abs_self (p.prob x-q.prob x)
    have h2 := neg_le_abs (p.prob x-q.prob x)
    split_ifs <;> linarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => h x)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.sum_one, q.sum_one,
    ← Finset.mul_sum] at hs
  dsimp [tv, errorSum]
  linarith

def hellingerSq (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : ℝ :=
  ∑ x, (Real.sqrt (p.prob x)-Real.sqrt (q.prob x))^2

private theorem sqrt_log_bound (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (Real.sqrt p-Real.sqrt q)^2 ≤ p*(Real.log p-Real.log q)+q-p := by
  have ha := Real.sqrt_pos.mpr hp
  have hb := Real.sqrt_pos.mpr hq
  have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', Real.log_sqrt hq.le, Real.log_sqrt hp.le] at hl
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  have he : p*(Real.sqrt q/Real.sqrt p-1) = Real.sqrt p*Real.sqrt q-p := by
    have hs := Real.sq_sqrt hp.le
    field_simp [ha.ne']
    nlinarith
  rw [he] at hm
  nlinarith [Real.sq_sqrt hp.le, Real.sq_sqrt hq.le]

omit [DecidableEq X] in

theorem hellinger_le_kl (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) : hellingerSq p q ≤ kl p q := by
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) =>
    sqrt_log_bound (p.prob x) (q.prob x) (hp x) (hq x))
  simpa only [hellingerSq, kl, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    p.sum_one, q.sum_one, add_sub_cancel_right] using hs

omit [DecidableEq X] in

theorem tv_sq_le_hellinger (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : tv p q ^ 2 ≤ hellingerSq p q := by
  have hid (x : X) : |p.prob x-q.prob x| =
      |Real.sqrt (p.prob x)-Real.sqrt (q.prob x)| *
        (Real.sqrt (p.prob x)+Real.sqrt (q.prob x)) := by
    calc
      _ = |(Real.sqrt (p.prob x)-Real.sqrt (q.prob x))*
          (Real.sqrt (p.prob x)+Real.sqrt (q.prob x))| := by
        congr 1
        nlinarith [Real.sq_sqrt (p.nonneg x), Real.sq_sqrt (q.nonneg x)]
      _ = _ := by rw [abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |Real.sqrt (p.prob x)-Real.sqrt (q.prob x)|)
    (fun x => Real.sqrt (p.prob x)+Real.sqrt (q.prob x))
  simp only [← hid, sq_abs] at hc
  have hb : (∑ x, (Real.sqrt (p.prob x)+Real.sqrt (q.prob x))^2) ≤ 4 := by
    calc
      _ ≤ ∑ x, 2*(p.prob x+q.prob x) := by
        apply Finset.sum_le_sum
        intro x _
        nlinarith [Real.sq_sqrt (p.nonneg x), Real.sq_sqrt (q.nonneg x),
          sq_nonneg (Real.sqrt (p.prob x)-Real.sqrt (q.prob x))]
      _ = 4 := by rw [← Finset.mul_sum, Finset.sum_add_distrib, p.sum_one, q.sum_one]; norm_num
  have hh : 0 ≤ hellingerSq p q := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hh' := mul_le_mul_of_nonneg_left hb hh
  dsimp [hellingerSq] at hh'
  dsimp [tv, hellingerSq]
  nlinarith [hc, hh']

omit [DecidableEq X] in

theorem tv_sq_le_kl (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) : tv p q ^ 2 ≤ kl p q :=
  (tv_sq_le_hellinger p q).trans (hellinger_le_kl p q hp hq)

theorem records_testing_lower (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (hp : ∀ x, 0 < p.prob x) (hq : ∀ x, 0 < q.prob x)
    (n : ℕ) (f : (Fin n → X) → Bool) :
    1-Real.sqrt ((n : ℝ)*kl p q) ≤ errorSum (records p n) (records q n) f := by
  have hp' : ∀ w, 0 < (records p n).prob w := by
    intro w
    change 0 < ∏ i, p.prob (w i)
    exact Finset.prod_pos fun i _ => hp (w i)
  have hq' : ∀ w, 0 < (records q n).prob w := by
    intro w
    change 0 < ∏ i, q.prob (w i)
    exact Finset.prod_pos fun i _ => hq (w i)
  have ht := tv_sq_le_kl (records p n) (records q n) hp' hq'
  rw [kl_records p q hp hq n] at ht
  have hn : 0 ≤ (n : ℝ)*kl p q := mul_nonneg (Nat.cast_nonneg _) (kl_nonneg p q hp hq)
  have hs := Real.sq_sqrt hn
  have hsn := Real.sqrt_nonneg ((n : ℝ)*kl p q)
  have he := errorSum_lower (records p n) (records q n) f
  have htv : tv (records p n) (records q n) ≤ Real.sqrt ((n : ℝ)*kl p q) := by
    nlinarith
  linarith

theorem records_estimation_lower (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X)
    (hp : ∀ x, 0 < p.prob x) (hq : ∀ x, 0 < q.prob x)
    (n : ℕ) (estimate : (Fin n → X) → ℝ) (theta0 theta1 eps : ℝ)
    (hsep : 2*eps < theta1-theta0) :
    1-Real.sqrt ((n : ℝ)*kl p q) ≤
      p.probEvent (fun w => eps < |estimate w-theta0|) +
      q.probEvent (fun w => eps < |estimate w-theta1|) := by
  let test := fun w => decide ((theta0+theta1)/2 < estimate w)
  have ht := records_testing_lower p q hp hq n test
  apply ht.trans
  unfold errorSum Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have hp0 : 0 ≤ p.probOf w := Finset.prod_nonneg fun i _ => p.nonneg _
  have hq0 : 0 ≤ q.probOf w := Finset.prod_nonneg fun i _ => q.nonneg _
  by_cases h : (theta0+theta1)/2 < estimate w
  · have herror : eps < |estimate w-theta0| := by
      have := le_abs_self (estimate w-theta0)
      linarith
    simp only [test, h, decide_true, if_true, herror]
    change p.probOf w ≤ p.probOf w + (if eps < |estimate w-theta1| then q.probOf w else 0)
    split_ifs <;> linarith
  · have herror : eps < |estimate w-theta1| := by
      have := neg_le_abs (estimate w-theta1)
      linarith
    simp only [test, h, decide_false, Bool.false_eq_true, if_false, herror, if_true]
    change q.probOf w ≤ (if eps < |estimate w-theta0| then p.probOf w else 0)+q.probOf w
    split_ifs <;> linarith

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
