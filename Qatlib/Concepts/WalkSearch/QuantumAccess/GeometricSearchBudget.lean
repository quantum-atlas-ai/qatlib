/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.CappedGeometricSearch

/-!
# Failure and resource bounds for geometric search

This module analyzes the probability law of capped geometric search. It derives multiplicative
failure and additive expected-resource recurrences, obtains a `25 / 32` failure bound for a
sufficiently large attempt window, and sums the resulting geometric resource bounds.

The analysis formalizes the increasing-window search strategy of [BoyerEtAl1998], with explicit
cutoff probabilities, expected counters, endpoint behavior, and deterministic bounds for
supported traces.

## Main statements

* `geometric_search_actual_cutoff_failure_probability`: geometric failure decay after a mature
  window.
* `geometric_search_intrinsic_expected_resource_budget`: five expected-resource bounds
  proportional to `1 / sin (2 * θ)`.
* `geometric_search_zero_one_endpoints_and_path_caps`: endpoint probabilities and bounds on each
  supported trace.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.QuantumAccess

open Matrix
open scoped ENNReal Classical

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The expectation of a constant times an event indicator equals that constant times the event
probability. -/
private theorem expectation_indicator_mul {α : Type} (p : PMF α) (P : α → Prop) (c : ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun a => if P a then c else 0) = c * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq p P,
      ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      (fun a => by by_cases hP : P a <;> simp [hP])

/-- The probabilities of a predicate and its complement sum to one. -/
theorem event_compl {α : Type} (p : PMF α) (P : α → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p P + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun a => ¬P a) = 1 := by
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq p P, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq p (fun a => ¬P a),
    ← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add]
  refine Eq.trans ?_ (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const p 1)
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro a
  by_cases hP : P a <;> simp [hP]

/-- If a nonnegative extended-real function is at most `c` on a probability law's support, its
expectation is at most `c`. -/
theorem expectation_le_of_support {α : Type} (p : PMF α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a ≤ c) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p f ≤ c := by
  show ∑' a, p a * f a ≤ c
  calc ∑' a, p a * f a ≤ ∑' a, p a * c := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : p a = 0
        · simp [ha]
        · exact (ENNReal.mul_le_mul_iff_right ha (fun h =>
            have := PMF.coe_le_one p a
            by rw [h] at this; simp at this)).mpr
            (h a ((PMF.mem_support_iff p a).mpr ha))
    _ = c := by
      rw [show ∑' a, p a * c = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun _ => c) from rfl,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]

/-- The condition that an attempt contains no candidate accepted by the validation predicate. -/
def searchSlotFail {I : Type} (valid : I → Bool) (out : Option (I × ℕ) × ℕ × ℕ) : Prop :=
  ¬ ∃ y g, out.1 = some (y, g) ∧ valid y = true

/-- The continuation law after an attempt, stopping with a valid candidate or prepending the
receipt to a fresh search on the remaining schedule. -/
private noncomputable def searchCont {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (valid : I → Bool) (m : ℕ) (ms : List ℕ) (out : Option (I × ℕ) × ℕ × ℕ) :
    PMF (CappedSearchTrace I) :=
  match out.1 with
  | none => (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out)
  | some (y, _) =>
      if valid y then
        PMF.pure
          (prependSearchReceipt m out {(emptySearchTrace (I := I)) with result := some y})
      else (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out)

/-- A search on a nonempty schedule is the first sampled attempt bound to its continuation law. -/
private theorem searchCons_eq (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ) :
    searchForSchedule A hA j₀ S valid (m :: ms)
      = (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).bind
          (searchCont A hA j₀ S valid m ms) := rfl

/-- An attempt without a candidate continues on the remaining schedule and prepends its receipt. -/
private theorem searchCont_none (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ) (bits q : ℕ) :
    searchCont A hA j₀ S valid m ms (none, bits, q)
      = (searchForSchedule A hA j₀ S valid ms).map
          (prependSearchReceipt m (none, bits, q)) := rfl

/-- An attempt with an invalid candidate continues on the remaining schedule and prepends its
receipt. -/
private theorem searchCont_some_invalid (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ) (y : I) (g bits q : ℕ)
    (hv : ¬ valid y = true) :
    searchCont A hA j₀ S valid m ms (some (y, g), bits, q)
      = (searchForSchedule A hA j₀ S valid ms).map
          (prependSearchReceipt m (some (y, g), bits, q)) := by
  show (if valid y = true then
      PMF.pure (prependSearchReceipt m (some (y, g), bits, q)
        {(emptySearchTrace (I := I)) with result := some y})
      else (searchForSchedule A hA j₀ S valid ms).map
          (prependSearchReceipt m (some (y, g), bits, q))) = _
  rw [ite_eq_right hv]

/-- An attempt with a valid candidate terminates in the pure law of the corresponding successful
trace. -/
private theorem searchCont_some_valid (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ) (y : I) (g bits q : ℕ)
    (hv : valid y = true) :
    searchCont A hA j₀ S valid m ms (some (y, g), bits, q)
      = PMF.pure (prependSearchReceipt m (some (y, g), bits, q)
          {(emptySearchTrace (I := I)) with result := some y}) := by
  show (if valid y = true then
      PMF.pure (prependSearchReceipt m (some (y, g), bits, q)
        {(emptySearchTrace (I := I)) with result := some y})
      else (searchForSchedule A hA j₀ S valid ms).map
          (prependSearchReceipt m (some (y, g), bits, q))) = _
  rw [ite_eq_left hv]

/-- Every failed attempt continues with the remaining search law and prepends its attempt
receipt. -/
private theorem searchCont_fail (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ)
    (out : Option (I × ℕ) × ℕ × ℕ) (hfail : searchSlotFail valid out) :
    searchCont A hA j₀ S valid m ms out
      = (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out) := by
  obtain ⟨o1, bits, q⟩ := out
  cases o1 with
  | none => exact searchCont_none A hA j₀ S valid m ms bits q
  | some pair =>
      obtain ⟨y, g⟩ := pair
      exact searchCont_some_invalid A hA j₀ S valid m ms y g bits q
        (fun hv => hfail ⟨y, g, rfl, hv⟩)

omit [DecidableEq I] in

/-- An attempt does not fail exactly when it contains a candidate accepted by validation. -/
private theorem slotFail_iff (valid : I → Bool) (out : Option (I × ℕ) × ℕ × ℕ) :
    (¬ searchSlotFail valid out) ↔ ∃ y g, out.1 = some (y, g) ∧ valid y = true := by
  constructor
  · intro h
    by_contra hcon
    exact h hcon
  · rintro ⟨y, g, ho, hv⟩ hcon
    exact hcon ⟨y, g, ho, hv⟩

/-- The failure probability on a nonempty schedule equals the first-attempt failure probability
times the remaining search's failure probability. -/
theorem search_event_none_recursion (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (m :: ms)) (fun tr => tr.result = none)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
          (fun out => searchSlotFail valid out)
        * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid ms) (fun tr => tr.result = none) := by
  have houter : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      ((preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).bind (searchCont A hA j₀ S valid m ms))
      (fun tr => tr.result = none)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3) (fun out =>
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchCont A hA j₀ S valid m ms out) (fun tr => tr.result = none)) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
    exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr fun out => (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq _ _).symm
  have hsplit : ∀ out : Option (I × ℕ) × ℕ × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchCont A hA j₀ S valid m ms out) (fun tr => tr.result = none)
        = if searchSlotFail valid out then
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid ms) (fun tr => tr.result = none)
          else 0 := by
    intro out
    obtain ⟨o1, bits, q⟩ := out
    by_cases hfail : searchSlotFail valid (o1, bits, q)
    · rw [ite_eq_left hfail, searchCont_fail A hA j₀ S valid m ms (o1, bits, q) hfail,
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
      exact Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun tr =>
        show (prependSearchReceipt m (o1, bits, q) tr).result = none ↔ tr.result = none from by
        constructor
        · intro h
          have h' : tr.result = (prependSearchReceipt m (o1, bits, q) tr).result := rfl
          rw [h']
          exact h
        · intro h
          have h' : (prependSearchReceipt m (o1, bits, q) tr).result = tr.result := rfl
          rw [h']
          exact h)
    · obtain ⟨y, g, ho, hv⟩ := (slotFail_iff valid (o1, bits, q)).mp hfail
      subst ho
      rw [searchCont_some_valid A hA j₀ S valid m ms y g bits q hv, ite_eq_right hfail,
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      refine ite_eq_right ?_
      show ¬(some y : Option I) = none
      simp
  rw [searchCons_eq, houter, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit, expectation_indicator_mul,
    mul_comm]

/-- For a resource counter with additive receipts and zero terminal charge, expected total cost
is expected first-attempt cost plus failure probability times expected continuation cost. -/
theorem search_ledger_recursion (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (L : CappedSearchTrace I → ℕ)
    (inc : Option (I × ℕ) × ℕ × ℕ → ℕ)
    (hinc : ∀ (m : ℕ) (out : Option (I × ℕ) × ℕ × ℕ) (tr : CappedSearchTrace I),
      L (prependSearchReceipt m out tr) = inc out + L tr)
    (hzero : ∀ (_m : ℕ) (_out : Option (I × ℕ) × ℕ × ℕ) (y : I),
      L {(emptySearchTrace (I := I)) with result := some y} = 0)
    (m : ℕ) (ms : List ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid (m :: ms)) (fun tr => (L tr : ℝ≥0∞))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
          (fun out => (inc out : ℝ≥0∞))
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
            (fun out => searchSlotFail valid out)
          * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid ms)
              (fun tr => (L tr : ℝ≥0∞)) := by
  rw [searchCons_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hsplit : ∀ out : Option (I × ℕ) × ℕ × ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchCont A hA j₀ S valid m ms out) (fun tr => (L tr : ℝ≥0∞))
        = (inc out : ℝ≥0∞) + if searchSlotFail valid out then
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid ms) (fun tr => (L tr : ℝ≥0∞))
          else 0 := by
    intro out
    obtain ⟨o1, bits, q⟩ := out
    by_cases hfail : searchSlotFail valid (o1, bits, q)
    · rw [ite_eq_left hfail, searchCont_fail A hA j₀ S valid m ms (o1, bits, q) hfail,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr (fun tr => by
          show ((L (prependSearchReceipt m (o1, bits, q) tr) : ℕ) : ℝ≥0∞)
            = (((inc (o1, bits, q) : ℕ) : ℝ≥0∞) + ((L tr : ℕ) : ℝ≥0∞))
          rw [hinc m (o1, bits, q) tr, Nat.cast_add]),
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const]
    · obtain ⟨y, g, ho, hv⟩ := (slotFail_iff valid (o1, bits, q)).mp hfail
      subst ho
      rw [searchCont_some_valid A hA j₀ S valid m ms y g bits q hv, ite_eq_right hfail,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure,
        hinc m (some (y, g), bits, q) {(emptySearchTrace (I := I)) with result := some y},
        hzero m (some (y, g), bits, q) y]
      simp
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hsplit, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    expectation_indicator_mul]
  ring

/-- The list of `T` geometric windows starting at offset `off` with cap `M`. -/
def schedFrom (M off T : ℕ) : List ℕ :=
  List.ofFn fun i : Fin T => geometricWindow M (off + i.val)

/-- The offset-zero schedule equals `geometricSearchSchedule M T`. -/
theorem schedFrom_zero (M T : ℕ) : schedFrom M 0 T = geometricSearchSchedule M T := by
  simp only [schedFrom, geometricSearchSchedule, Nat.zero_add]

/-- An offset schedule of length `T + 1` splits into its first window and the length-`T`
schedule at the next offset. -/
theorem schedFrom_succ (M off T : ℕ) :
    schedFrom M off (T + 1) = geometricWindow M off :: schedFrom M (off + 1) T := by
  show List.ofFn (fun i : Fin (T+1) => geometricWindow M (off + i.val)) = _
  rw [List.ofFn_succ,
    show (fun i : Fin T => geometricWindow M (off + (Fin.succ i).val))
      = (fun i : Fin T => geometricWindow M ((off + 1) + i.val)) from by
      funext i
      simp only [Fin.val_succ]
      congr 1
      omega,
    show geometricWindow M (off + (0 : Fin (T+1)).val) = geometricWindow M off from by
      simp]
  rfl

/-- An offset schedule of length zero is empty. -/
theorem schedFrom_nil (M off : ℕ) : schedFrom M off 0 = [] := rfl

/-- Every natural power of the real number `6 / 5` is at least one. -/
private theorem geopow_ge_one (k : ℕ) : (1:ℝ) ≤ ((6/5:ℝ)^k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ ((6/5:ℝ)^k) * (6/5) := mul_le_mul ih (by norm_num) (by norm_num) (by norm_num)
        _ = (6/5:ℝ)^(k+1) := (pow_succ _ _).symm

/-- Every capped geometric window is positive. -/
theorem geometric_window_pos (M k : ℕ) : 0 < geometricWindow M k := by
  show 0 < max 1 (min M _)
  omega

/-- For a fixed cap, the geometric window is nondecreasing in its index. -/
theorem geometric_window_mono (M : ℕ) : ∀ a b : ℕ, a ≤ b →
    geometricWindow M a ≤ geometricWindow M b := by
  intro a b h
  induction h with
  | refl => rfl
  | @step m _ ih =>
      have hstep : geometricWindow M m ≤ geometricWindow M m.succ :=
        (geometric_search_actual_integer_schedule M m m).2.2.2.1
      exact le_trans ih hstep

/-- The rounded window numerator satisfies `6 ^ k ≤ 5 ^ k * ((6 ^ k + 5 ^ k - 1) / 5 ^ k)`. -/
private theorem window_raw_mul (k : ℕ) : (6:ℕ)^k ≤ 5^k * ((6^k + 5^k - 1) / 5^k) := by
  have h5 : (0:ℕ) < 5^k := Nat.pow_pos (by norm_num)
  have hd := Nat.div_add_mod (6^k + 5^k - 1) (5^k)
  have hmod : (6^k + 5^k - 1) % 5^k ≤ 5^k - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ h5)
  omega

/-- The real value of the `k`th capped geometric window is at most `3 * (6 / 5) ^ k`. -/
theorem geometric_window_le (M k : ℕ) :
    (geometricWindow M k : ℝ) ≤ 3 * ((6/5:ℝ)^k) := by
  have h5 : (0:ℕ) < 5^k := Nat.pow_pos (by norm_num)
  have h5R : (0:ℝ) < ((5^k:ℕ):ℝ) := by exact_mod_cast h5
  have hdiv : ((6/5:ℝ)^k) = ((6^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := by
    rw [div_pow]
    push_cast
    rfl
  have hhigh : (((6^k+5^k-1)/5^k : ℕ):ℝ) ≤ ((6/5:ℝ)^k) + 1 := by
    have h1 : (((6^k+5^k-1)/5^k : ℕ):ℝ) ≤ ((6^k+5^k-1:ℕ):ℝ)/((5^k:ℕ):ℝ) := Nat.cast_div_le
    have h2 : ((6^k+5^k-1:ℕ):ℝ) ≤ ((6^k+5^k:ℕ):ℝ) := by exact_mod_cast (Nat.sub_le _ _)
    have h3 : ((6^k+5^k-1:ℕ):ℝ)/((5^k:ℕ):ℝ) ≤ ((6^k+5^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h4 : ((6^k+5^k:ℕ):ℝ) = ((6^k:ℕ):ℝ) + ((5^k:ℕ):ℝ) := Nat.cast_add _ _
    calc (((6^k+5^k-1)/5^k : ℕ):ℝ) ≤ ((6^k+5^k-1:ℕ):ℝ)/((5^k:ℕ):ℝ) := h1
      _ ≤ ((6^k+5^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := h3
      _ = ((6^k:ℕ):ℝ)/((5^k:ℕ):ℝ) + ((5^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := by
          rw [h4, add_div]
      _ = ((6/5:ℝ)^k) + 1 := by rw [← hdiv, div_self (ne_of_gt h5R)]
  have hw : (geometricWindow M k : ℝ) ≤ 1 + (((6^k+5^k-1)/5^k : ℕ):ℝ) := by
    have hnat : geometricWindow M k ≤ 1 + ((6^k+5^k-1)/5^k) := by
      show max 1 (min M ((6^k+5^k-1)/5^k)) ≤ 1 + (6^k+5^k-1)/5^k
      generalize (6^k+5^k-1)/5^k = w
      omega
    exact_mod_cast hnat
  have hge := geopow_ge_one k
  linarith

/-- For `0 < s ≤ 1`, if both the cap and the raw geometric window times `s` are at least one,
the integer window times `s` is at least one. -/
theorem geometric_window_mature {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (M k : ℕ)
    (hMs : 1 ≤ (M:ℝ)*s) (hk : 1 ≤ ((6/5:ℝ)^k)*s) :
    1 ≤ (geometricWindow M k : ℝ)*s := by
  have h5R : (0:ℝ) < ((5^k:ℕ):ℝ) := by
    have : (0:ℕ) < 5^k := Nat.pow_pos (by norm_num)
    exact_mod_cast this
  have hdiv : ((6/5:ℝ)^k) = ((6^k:ℕ):ℝ)/((5^k:ℕ):ℝ) := by
    rw [div_pow]
    push_cast
    rfl
  have hgx : ((6/5:ℝ)^k) ≤ (((6^k+5^k-1)/5^k : ℕ):ℝ) := by
    rw [hdiv, div_le_iff₀ h5R, mul_comm]
    exact_mod_cast window_raw_mul k
  have hinv1 : 1/s ≤ (M:ℝ) := by
    rw [div_le_iff₀ hs0]
    exact hMs
  have hinvg : 1/s ≤ (((6^k+5^k-1)/5^k : ℕ):ℝ) := by
    rw [div_le_iff₀ hs0]
    calc (1:ℝ) ≤ ((6/5:ℝ)^k)*s := hk
      _ ≤ (((6^k+5^k-1)/5^k : ℕ):ℝ)*s := mul_le_mul_of_nonneg_right hgx (by positivity)
  have h1s : (1:ℝ) ≤ 1/s := by
    rw [le_div_iff₀ hs0]
    linarith
  have hwm : geometricWindow M k = min M ((6^k+5^k-1)/5^k) := by
    show max 1 (min M ((6^k+5^k-1)/5^k)) = min M ((6^k+5^k-1)/5^k)
    have hM1 : (1:ℕ) ≤ M := by exact_mod_cast (le_trans h1s hinv1)
    have hg1 : (1:ℕ) ≤ (6^k+5^k-1)/5^k := by exact_mod_cast (le_trans h1s hinvg)
    omega
  have hmin : (1/s) ≤ min ((M:ℕ):ℝ) (((6^k+5^k-1)/5^k : ℕ):ℝ) := by
    rw [min_def]
    by_cases h : ((M:ℕ):ℝ) ≤ (((6^k+5^k-1)/5^k : ℕ):ℝ)
    · rw [ite_eq_left h]
      exact hinv1
    · rw [ite_eq_right h]
      exact hinvg
  rw [hwm, Nat.cast_min]
  have hgoal : min ((M:ℕ):ℝ) (((6^k+5^k-1)/5^k : ℕ):ℝ) * s ≥ (1/s)*s :=
    mul_le_mul hmin (le_refl s) (by positivity) (by positivity)
  rw [div_mul_cancel₀ _ (ne_of_gt hs0)] at hgoal
  linarith

/-- For positive `s`, some natural power of `6 / 5` is at least `1 / s`. -/
private theorem exists_geometric_cross {s : ℝ} (hs : 0 < s) :
    ∃ k : ℕ, 1/s ≤ ((6/5:ℝ)^k) := by
  have hgrowth : ∀ k : ℕ, 1 + (k:ℝ)/5 ≤ ((6/5:ℝ)^k) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        calc (1:ℝ) + (((k+1:ℕ):ℝ))/5 ≤ (6/5:ℝ) * (1 + (k:ℝ)/5) := by
              have heq : (1:ℝ) + ((k+1:ℕ):ℝ)/5 + (k:ℝ)/25
                  = (6/5:ℝ) * (1 + (k:ℝ)/5) := by
                push_cast
                field_simp
                ring
              have hk25 : (0:ℝ) ≤ (k:ℝ)/25 := by positivity
              linarith
          _ ≤ (6/5:ℝ) * ((6/5:ℝ)^k) := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (6/5:ℝ)^(k+1) := (pow_succ' _ _).symm
  refine ⟨Nat.ceil (5/s), ?_⟩
  have hc : (5/s) ≤ ((Nat.ceil (5/s) : ℕ):ℝ) := Nat.le_ceil (5/s)
  have h1 : (1:ℝ) + ((Nat.ceil (5/s) : ℕ):ℝ)/5 ≥ 1 + (5/s)/5 := by
    apply add_le_add (le_refl 1)
    exact div_le_div_of_nonneg_right hc (by positivity)
  have h2 : (1:ℝ) + (5/s)/5 = 1 + 1/s := by
    field_simp
  refine le_trans ?_ (hgrowth _)
  calc (1/s) ≤ 1 + 1/s := by linarith
    _ ≤ 1 + ((Nat.ceil (5/s) : ℕ):ℝ)/5 := le_trans (le_of_eq h2.symm) h1

/-- The extended nonnegative real value `25 / 32` equals `ENNReal.ofReal` of the corresponding
real ratio. -/
private theorem rat_coe_25_32 : ((25/32:ℝ≥0∞)) = ENNReal.ofReal ((25/32:ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 32)]
  norm_num

/-- The extended nonnegative real value `7 / 32` equals `ENNReal.ofReal` of the corresponding
real ratio. -/
private theorem rat_coe_7_32 : ((7/32:ℝ≥0∞)) = ENNReal.ofReal ((7/32:ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 32)]
  norm_num

/-- The extended nonnegative real value `1 / 8` equals `ENNReal.ofReal` of the corresponding
real ratio. -/
private theorem rat_coe_1_8 : ((1/8:ℝ≥0∞)) = ENNReal.ofReal ((1/8:ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
  norm_num

/-- The extended nonnegative real value `7 / 8` equals `ENNReal.ofReal` of the corresponding
real ratio. -/
private theorem rat_coe_7_8 : ((7/8:ℝ≥0∞)) = ENNReal.ofReal ((7/8:ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
  norm_num

/-- The extended nonnegative real value `6 / 5` equals `ENNReal.ofReal` of the corresponding
real ratio. -/
private theorem rat_coe_65 : ((6/5:ℝ≥0∞)) = ENNReal.ofReal ((6/5:ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
  norm_num

/-- The extended nonnegative real cast of a natural equals `ENNReal.ofReal` of its real cast. -/
private theorem nat_coe (n : ℕ) : ((n:ℝ≥0∞)) = ENNReal.ofReal ((n:ℝ)) := by norm_num

/-- The cube of one half in extended nonnegative reals equals `ENNReal.ofReal (1 / 8)`. -/
private theorem half_pow3 : ((1/2:ℝ≥0∞))^3 = ENNReal.ofReal ((1/8:ℝ)) := by
  rw [show ((1/2:ℝ≥0∞)) = ENNReal.ofReal ((1/2:ℝ)) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num,
    ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ (1/2:ℝ)) 3]
  congr 1
  norm_num

/-- When validation exactly recognizes `S`, attempt success has the same probability as
producing a candidate in `S`. -/
theorem slot_success_event_congr (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ)
    (hvalid : ∀ y, valid y = true ↔ y ∈ S) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
        (fun out => ¬ searchSlotFail valid out)
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
          (fun out => ∃ y gates, out.1 = some (y, gates) ∧ y ∈ S) :=
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun out => by
    rw [slotFail_iff]
    exact exists_congr fun y => exists_congr fun g => by
      constructor
      · rintro ⟨hv1, hv2⟩
        exact ⟨hv1, (hvalid y).mp hv2⟩
      · rintro ⟨hv1, hS⟩
        exact ⟨hv1, (hvalid y).mpr hS⟩)

/-- With marked mass `sin θ ^ 2` and a positive window satisfying `m * sin (2 * θ) ≥ 1`, the
attempt's failure probability is at most `25 / 32`. -/
theorem slot_fail_le (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (θ : ℝ) (m : ℕ)
    (hvalid : ∀ y, valid y = true ↔ y ∈ S) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (hm : 0 < m) (hms : 1 ≤ (m:ℝ)*Real.sin (2*θ)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
      (fun out => searchSlotFail valid out) ≤ 25/32 := by
  have hm2 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num : 1 < 2) m
  have hq := (finite_coin_effective_cutoff m 3 hm).2.1
  have hq3 : (coinRejectMass (Nat.clog 2 m) m)^3 ≤ ENNReal.ofReal ((1/8:ℝ)) := by
    refine le_trans (ENNReal.pow_le_pow_left hq) ?_
    rw [half_pow3]
  have h78eq : ((7/8:ℝ≥0∞)) = 1 - ENNReal.ofReal ((1/8:ℝ)) :=
    ENNReal.eq_sub_of_add_eq (ENNReal.ofReal_ne_top) (by
      have hr : (7/8:ℝ) + (1/8:ℝ) = 1 := by norm_num
      rw [rat_coe_7_8, ← ENNReal.ofReal_add (by norm_num) (by norm_num), hr,
        ENNReal.ofReal_one])
  have hstep : ((7/8:ℝ≥0∞)) ≤ 1-(coinRejectMass (Nat.clog 2 m) m)^3 :=
    le_trans (le_of_eq h78eq) (tsub_le_tsub_left hq3 1)
  have h78 : ((7/32:ℝ≥0∞)) ≤ (1-(coinRejectMass (Nat.clog 2 m) m)^3)/4 := by
    have h7 : ((7/32:ℝ≥0∞)) = ((7/8:ℝ≥0∞)) * ((4:ℝ≥0∞))⁻¹ := by
      have hr : ((7/8:ℝ)) * ((1/4:ℝ)) = (7/32:ℝ) := by norm_num
      rw [rat_coe_7_32, rat_coe_7_8,
        show ((4:ℝ≥0∞))⁻¹ = ((1/4:ℝ≥0∞)) from (one_div (a := (4:ℝ≥0∞))).symm,
        show ((1/4:ℝ≥0∞)) = ENNReal.ofReal ((1/4:ℝ)) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
          norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7/8)]
      congr 1
      norm_num
    rw [show (1-(coinRejectMass (Nat.clog 2 m) m)^3)/4
        = (1-(coinRejectMass (Nat.clog 2 m) m)^3) * ((4:ℝ≥0∞))⁻¹ from div_eq_mul_inv _ _,
      h7]
    exact mul_le_mul' hstep (le_refl _)
  have hsuccess := (prepared_aa_sampled_lower_and_endpoints A j₀ S hA θ (Nat.clog 2 m) m 3 hm hm2).1
    hθ0 hθ1 hmass hms
  rw [← slot_success_event_congr A hA j₀ S valid m hvalid] at hsuccess
  have hsuccess' : ((7/32:ℝ≥0∞)) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
        (fun out => ¬ searchSlotFail valid out) := le_trans h78 hsuccess
  have hpart := event_compl (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
    (searchSlotFail valid)
  have hsum : ((25/32:ℝ≥0∞)) + (7/32:ℝ≥0∞) = 1 := by
    have hr : (25/32:ℝ) + (7/32:ℝ) = 1 := by norm_num
    rw [rat_coe_25_32, rat_coe_7_32, ← ENNReal.ofReal_add (by norm_num) (by norm_num), hr,
      ENNReal.ofReal_one]
  have hkey : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
      (fun out => searchSlotFail valid out) + (7/32:ℝ≥0∞)
      ≤ (25/32:ℝ≥0∞) + (7/32:ℝ≥0∞) := by
    calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
          (fun out => searchSlotFail valid out) + (7/32:ℝ≥0∞)
          ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
              (fun out => searchSlotFail valid out) +
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
              (fun out => ¬ searchSlotFail valid out) :=
            add_le_add (le_refl _) hsuccess'
      _ = 1 := hpart
      _ = (25/32:ℝ≥0∞) + (7/32:ℝ≥0∞) := hsum.symm
  exact (ENNReal.add_le_add_iff_right
    (by rw [rat_coe_7_32]; exact ENNReal.ofReal_ne_top)).mp hkey

/-- With exact validation and zero initial marked mass, every positive-window attempt fails with
probability one. -/
theorem slot_fail_eq_one (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ)
    (hvalid : ∀ y, valid y = true ↔ y ∈ S) (hm : 0 < m)
    (hmass : MeasureProb (preparedAAState A j₀) S = 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
      (fun out => searchSlotFail valid out) = 1 := by
  have hm2 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num : 1 < 2) m
  have hzero := (prepared_aa_sampled_lower_and_endpoints A j₀ S hA 0 (Nat.clog 2 m) m 3 hm hm2).2.1
    hmass
  have hpart := event_compl (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3)
    (searchSlotFail valid)
  rw [← slot_success_event_congr A hA j₀ S valid m hvalid] at hzero
  rw [hzero, add_zero] at hpart
  exact hpart

/-- With exact validation and initial marked mass one, the window-one attempt has failure
probability zero. -/
theorem slot_fail_first_zero (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool)
    (hvalid : ∀ y, valid y = true ↔ y ∈ S)
    (hmass : MeasureProb (preparedAAState A j₀) S = 1) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 1) 1 3)
      (fun out => searchSlotFail valid out) = 0 := by
  have hm : (0:ℕ) < 1 := by norm_num
  have hm2 : 1 ≤ 2 ^ Nat.clog 2 1 := Nat.le_pow_clog (by norm_num : 1 < 2) 1
  have hone := (prepared_aa_sampled_lower_and_endpoints A j₀ S hA 0 (Nat.clog 2 1) 1 3 hm hm2).2.2
    hmass
  have hq : (coinRejectMass (Nat.clog 2 1) 1)^3 = 0 := by
    rw [Nat.clog_one_right 2]
    norm_num [coinRejectMass]
  have hone' : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 1) 1 3)
      (fun out => ¬ searchSlotFail valid out) = 1 := by
    rw [slot_success_event_congr A hA j₀ S valid 1 hvalid]
    have h2 : (1:ℝ≥0∞) - (coinRejectMass (Nat.clog 2 1) 1)^3 = 1 := by
      rw [hq]
      simp
    rw [h2] at hone
    exact hone
  have hpart := event_compl (preparedAASampled A hA j₀ S (Nat.clog 2 1) 1 3)
    (searchSlotFail valid)
  rw [hone'] at hpart
  have hgoal : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 1) 1 3)
      (searchSlotFail valid) = 0 :=
    WithTop.add_right_cancel (by norm_num : (1:ℝ≥0∞) ≠ ⊤)
      (show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 1) 1 3)
        (searchSlotFail valid) + 1 = (0:ℝ≥0∞) + 1 from by
        rw [hpart]
        exact (zero_add _).symm)
  exact hgoal

/-- With exact validation and marked mass `sin θ ^ 2`, a mature window at index `j` bounds
cutoff failure probability by `(25 / 32) ^ (T - j)` [BoyerEtAl1998]. -/
theorem geometric_search_actual_cutoff_failure_probability :
    ∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
      (j₀ : I) (S : Finset I) (valid : I → Bool) (M T j : ℕ) (θ : ℝ),
      (∀ y, valid y=true ↔ y∈S) → 0<θ → θ<Real.pi/2 →
      MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
      1≤(geometricWindow M j:ℝ)*Real.sin (2*θ) →
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T))
        (fun tr => tr.result=none)).toReal ≤ (25/32:ℝ)^(T-j) := by
  intro A hA j₀ S valid M T j θ hvalid hθ0 hθ1 hmass hwin
  have hwm : ∀ a b : ℕ, a ≤ b → geometricWindow M a ≤ geometricWindow M b :=
    geometric_window_mono M
  have key : ∀ (T off jj : ℕ), jj ≤ T →
      1 ≤ (geometricWindow M (off + jj) : ℝ)*Real.sin (2*θ) →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (schedFrom M off T))
        (fun tr => tr.result = none) ≤ (25/32:ℝ≥0∞)^(T-jj) := by
    intro T
    induction T with
    | zero =>
        intro off jj hjj _
        have hjj0 : jj = 0 := by omega
        subst hjj0
        have hnil : schedFrom M off 0 = [] := rfl
        rw [hnil]
        have hrun : searchForSchedule A hA j₀ S valid [] = PMF.pure emptySearchTrace := rfl
        rw [hrun, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
            Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
        norm_num [emptySearchTrace]
    | succ T ih =>
        intro off jj hjj hmature
        rw [schedFrom_succ, search_event_none_recursion]
        rcases Nat.eq_zero_or_pos jj with hjj0 | hjj0
        · subst hjj0
          have hf : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S
                (Nat.clog 2 (geometricWindow M (off + 0))) (geometricWindow M (off + 0)) 3)
              (fun out => searchSlotFail valid out) ≤ 25/32 := by
            refine slot_fail_le A hA j₀ S valid θ _ hvalid hθ0 hθ1 hmass
              (geometric_window_pos M off) ?_
            simpa using hmature
          have hshift : 1 ≤ (geometricWindow M (off + 1 + 0) : ℝ)*Real.sin (2*θ) := by
            have hmono := hwm off (off + 1) (Nat.le_succ off)
            have hm := hmature
            rw [Nat.add_zero] at hm
            calc (1:ℝ) ≤ (geometricWindow M off : ℝ)*Real.sin (2*θ) := hm
              _ ≤ (geometricWindow M (off + 1) : ℝ)*Real.sin (2*θ) :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hmono)
                    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : (0:ℝ) ≤ 2*θ)
                      (by linarith : 2*θ ≤ Real.pi))
          have ih' := ih (off + 1) 0 (by omega) hshift
          calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S
                (Nat.clog 2 (geometricWindow M (off + 0))) (geometricWindow M (off + 0)) 3)
                (fun out => searchSlotFail valid out) *
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (schedFrom M (off + 1) T))
                (fun tr => tr.result = none)
              ≤ (25/32:ℝ≥0∞) * (25/32:ℝ≥0∞)^(T-0) :=
                mul_le_mul' hf ih'
            _ = (25/32:ℝ≥0∞)^(T+1-0) := by
                rw [show T - 0 = T from by omega, show T + 1 - 0 = T + 1 from by omega, pow_succ,
                  mul_comm]
        · have hf : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S
                (Nat.clog 2 (geometricWindow M off)) (geometricWindow M off) 3)
              (fun out => searchSlotFail valid out) ≤ 1 := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
          have ih' := ih (off + 1) (jj - 1) (by omega)
              (by simpa only [show off + 1 + (jj - 1) = off + jj from by omega] using hmature)
          calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S
                (Nat.clog 2 (geometricWindow M off)) (geometricWindow M off) 3)
                (fun out => searchSlotFail valid out) *
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (schedFrom M (off + 1) T))
                (fun tr => tr.result = none)
              ≤ 1 * (25/32:ℝ≥0∞)^(T-(jj-1)) := mul_le_mul' hf ih'
            _ = (25/32:ℝ≥0∞)^(T+1-jj) := by
                rw [show T + 1 - jj = T - (jj - 1) from by omega]
                simp
  rcases Nat.lt_or_ge T j with hTj | hjT
  · have hTj0 : T - j = 0 := by omega
    have hle : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T))
        (fun tr => tr.result = none) ≤ 1 := Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
    calc (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T))
        (fun tr => tr.result=none)).toReal ≤ (1:ℝ≥0∞).toReal :=
          ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ⊤) hle
      _ ≤ (25/32:ℝ)^(T-j) := by
          rw [show (T - j : ℕ) = 0 from hTj0]
          norm_num
  · have hkey : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid
          (geometricSearchSchedule M T)) (fun tr => tr.result = none)
        ≤ (25/32:ℝ≥0∞)^(T-j) := by
      rw [← schedFrom_zero]
      exact key T 0 j hjT (by simpa only [Nat.zero_add] using hwin)
    calc (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T))
        (fun tr => tr.result=none)).toReal
        ≤ ((25/32:ℝ≥0∞)^(T-j)).toReal :=
          ENNReal.toReal_mono (by
            refine ENNReal.pow_ne_top ?_
            rw [rat_coe_25_32]
            exact ENNReal.ofReal_ne_top) hkey
      _ = ((25/32:ℝ≥0∞)).toReal^(T-j) := ENNReal.toReal_pow _ _
      _ = (25/32:ℝ)^(T-j) := by
          rw [rat_coe_25_32, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 25/32)]

/-- Natural powers of an extended nonnegative real at least one are nondecreasing in the
exponent. -/
private theorem pow_le_of_ge_one {r : ℝ≥0∞} (hr : 1 ≤ r) : ∀ a b : ℕ, a ≤ b → r ^ a ≤ r ^ b := by
  intro a b h
  induction h with
  | refl => rfl
  | @step m _ ih =>
      exact le_trans ih (by
        show r^m ≤ r^(m+1)
        rw [pow_succ]
        calc r^m = r^m * 1 := (mul_one _).symm
          _ ≤ r^m * r := mul_le_mul' (le_refl _) hr)

/-- Every natural power of an extended nonnegative real at least one is at least one. -/
private theorem one_le_pow' {r : ℝ≥0∞} (hr : 1 ≤ r) (k : ℕ) : 1 ≤ r ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      show (1:ℝ≥0∞) ≤ r^(k+1)
      rw [pow_succ]
      calc (1:ℝ≥0∞) = (1:ℝ≥0∞) * 1 := (one_mul _).symm
        _ ≤ r^k * r := mul_le_mul' ih hr

/-- Bounds a recursive cost by the geometric costs before the mature index and a terminal
envelope, under the stated slot, failure, and stability inequalities. -/
private theorem cap_master {r ρ β C : ℝ≥0∞} {jstar : ℕ}
    (slot fail : ℕ → ℝ≥0∞) (F : ℕ → ℕ → ℝ≥0∞)
    (hF0 : ∀ off : ℕ, F off 0 = 0)
    (hstep : ∀ off T : ℕ, F off (T+1) ≤ slot off + fail off * F (off+1) T)
    (hslot : ∀ off : ℕ, slot off ≤ β * r^off)
    (hfail1 : ∀ off : ℕ, fail off ≤ 1)
    (hfailρ : ∀ off : ℕ, jstar ≤ off → fail off ≤ ρ)
    (hβC : β + ρ * C * r ≤ C) :
    ∀ (T off : ℕ), F off T ≤
      ∑ i ∈ Finset.range (min T (jstar - off)), (β * r^(off+i)) + C * r^(off + min T (jstar - off)) := by
  intro T
  induction T with
  | zero =>
      intro off
      rw [hF0 off, show min (0:ℕ) (jstar - off) = 0 from by omega]
      simp
  | succ T ih =>
      intro off
      rcases Nat.lt_or_ge off jstar with hoff | hoff
      · have hn' : min (T+1) (jstar - off) = min T (jstar - off - 1) + 1 := by omega
        have hn'' : min T (jstar - (off+1)) = min T (jstar - off - 1) := by omega
        rw [hn']
        have hih := ih (off+1)
        rw [hn''] at hih
        have hshift : ∑ i ∈ Finset.range (min T (jstar - off - 1)), (β * r^(off+1+i))
            = ∑ i ∈ Finset.range (min T (jstar - off - 1)), (β * r^(off+(i+1))) :=
          Finset.sum_congr rfl fun i _ => by
            rw [show off + 1 + i = off + (i + 1) from by omega]
        have hexpC : C * r^(off + 1 + min T (jstar - off - 1))
            = C * r^(off + (min T (jstar - off - 1) + 1)) := by
          rw [show off + 1 + min T (jstar - off - 1)
            = off + (min T (jstar - off - 1) + 1) from by omega]
        calc F off (T+1) ≤ slot off + fail off * F (off+1) T := hstep off T
          _ ≤ β * r^off + fail off * F (off+1) T :=
              add_le_add (hslot off) (le_refl _)
          _ ≤ β * r^off + 1 * F (off+1) T :=
              add_le_add (le_refl _) (mul_le_mul' (hfail1 off) (le_refl _))
          _ = β * r^off + F (off+1) T := by rw [one_mul]
          _ ≤ β * r^off + (∑ i ∈ Finset.range (min T (jstar - off - 1)), (β * r^(off+1+i))
              + C * r^(off + 1 + min T (jstar - off - 1))) := add_le_add (le_refl _) hih
          _ = ∑ i ∈ Finset.range (min T (jstar - off - 1) + 1), (β * r^(off+i))
              + C * r^(off + (min T (jstar - off - 1) + 1)) := by
              rw [hshift, Finset.sum_range_succ', hexpC]
              ring
      · have hn0 : min (T+1) (jstar - off) = 0 := by omega
        have hn1 : min T (jstar - (off+1)) = 0 := by omega
        have hih := ih (off+1)
        rw [hn1, Finset.range_zero, Finset.sum_empty, zero_add] at hih
        rw [hn0, Finset.range_zero, Finset.sum_empty, zero_add]
        calc F off (T+1) ≤ slot off + fail off * F (off+1) T := hstep off T
          _ ≤ β * r^off + fail off * F (off+1) T :=
              add_le_add (hslot off) (le_refl _)
          _ ≤ β * r^off + ρ * F (off+1) T :=
              add_le_add (le_refl _) (mul_le_mul' (hfailρ off hoff) (le_refl _))
          _ ≤ β * r^off + ρ * (C * r^(off+1)) :=
              add_le_add (le_refl _) (mul_le_mul' (le_refl ρ) hih)
          _ = r^off * (β + ρ * C * r) := by rw [pow_succ r off]; ring
          _ ≤ r^off * C := mul_le_mul' (le_refl _) hβC
          _ = C * r^(off + 0) := by rw [mul_comm, Nat.add_zero off]

/-- For extended nonnegative real ratio `6 / 5`, the sum of the first `n` powers plus five
equals five times the `n`th power. -/
private theorem geo_five {r : ℝ≥0∞} (hr : r = ENNReal.ofReal ((6/5:ℝ))) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, r^i + 5 = 5 * r^n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have h5r : (5:ℝ≥0∞) * r = 6 := by
        rw [hr, show ((5:ℝ≥0∞)) = ENNReal.ofReal ((5:ℝ)) from by norm_num,
          show ((6:ℝ≥0∞)) = ENNReal.ofReal ((6:ℝ)) from by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
        congr 1
        norm_num
      rw [Finset.sum_range_succ]
      calc (∑ i ∈ Finset.range n, r^i + r^n) + 5 = (∑ i ∈ Finset.range n, r^i + 5) + r^n := by ring
        _ = 5 * r^n + r^n := by rw [ih]
        _ = (5 + 1) * r^n := by ring
        _ = 5 * r * r^n := by rw [show (5:ℝ≥0∞) + 1 = 5 * r from by rw [h5r]; norm_num]
        _ = 5 * r^(n+1) := by rw [pow_succ]; ring

/-- Under the stated geometric recurrence and stability assumptions, `F 0 T ≤ (5 * β + C) * r ^
jstar` for every cutoff `T`. -/
private theorem cap_final {r ρ β C : ℝ≥0∞} {jstar : ℕ} (hr1 : 1 ≤ r)
    (hgeo : ∀ n : ℕ, ∑ i ∈ Finset.range n, r^i ≤ 5 * r^n)
    (slot fail : ℕ → ℝ≥0∞) (F : ℕ → ℕ → ℝ≥0∞)
    (hF0 : ∀ off : ℕ, F off 0 = 0)
    (hstep : ∀ off T : ℕ, F off (T+1) ≤ slot off + fail off * F (off+1) T)
    (hslot : ∀ off : ℕ, slot off ≤ β * r^off)
    (hfail1 : ∀ off : ℕ, fail off ≤ 1)
    (hfailρ : ∀ off : ℕ, jstar ≤ off → fail off ≤ ρ)
    (hβC : β + ρ * C * r ≤ C) (T : ℕ) :
    F 0 T ≤ (5*β + C) * r^jstar := by
  have hmaster := cap_master (r := r) (ρ := ρ) (β := β) (C := C) (jstar := jstar)
    slot fail F hF0 hstep hslot hfail1 hfailρ hβC T 0
  have hn : min T jstar ≤ jstar := Nat.min_le_right _ _
  have hsumcongr : ∑ i ∈ Finset.range (min T jstar), (β * r^(0+i))
      = β * ∑ i ∈ Finset.range (min T jstar), r^i := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [Nat.zero_add]), Finset.mul_sum]
  calc F 0 T ≤ (∑ i ∈ Finset.range (min T jstar), (β * r^(0+i))
        + C * r^(0 + min T jstar)) := hmaster
    _ ≤ β * (5 * r^jstar) + C * r^jstar := by
        apply add_le_add
        · rw [hsumcongr]
          exact mul_le_mul' (le_refl _)
            (le_trans (hgeo _)
              (mul_le_mul' (le_refl _) (pow_le_of_ge_one hr1 _ _ hn)))
        · rw [Nat.zero_add]
          exact mul_le_mul' (le_refl _) (pow_le_of_ge_one hr1 _ _ hn)
    _ = (5*β + C) * r^jstar := by ring

/-- Converts an extended-real geometric bound at `jstar` into `X ≤ ENNReal.ofReal (LIM / s)`
under the crossing and constant assumptions. -/
private theorem sin_bound {X : ℝ≥0∞} {K LIM : ℝ} {jstar : ℕ} {s : ℝ} (hs0 : 0 < s)
    (hK : (0:ℝ) ≤ K) (hLIM : (0:ℝ) ≤ LIM) (hKLIM : K * ((6/5:ℝ)) ≤ LIM)
    (hjbound : ((6/5:ℝ)^jstar)*s ≤ 6/5)
    (h : X ≤ (ENNReal.ofReal K) * (ENNReal.ofReal ((6/5:ℝ)))^jstar) :
    X ≤ ENNReal.ofReal (LIM/s) := by
  have hne0 : ENNReal.ofReal s ≠ (0:ℝ≥0∞) := by
    intro h
    have h8 := ENNReal.ofReal_eq_zero.mp h
    linarith
  apply (ENNReal.mul_le_mul_iff_left hne0 ENNReal.ofReal_ne_top).mp
  calc X * ENNReal.ofReal s
      ≤ (ENNReal.ofReal K) * (ENNReal.ofReal ((6/5:ℝ)))^jstar * ENNReal.ofReal s :=
        mul_le_mul' h (le_refl _)
    _ = ENNReal.ofReal (K * ((6/5:ℝ)^jstar) * s) := by
        rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 6/5),
          ← ENNReal.ofReal_mul hK,
          ← ENNReal.ofReal_mul (mul_nonneg hK (by positivity))]
    _ ≤ ENNReal.ofReal (K * ((6/5:ℝ))) := by
        rw [show K * ((6/5:ℝ)^jstar) * s = K * (((6/5:ℝ)^jstar) * s) from by ring]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hjbound hK)
    _ ≤ ENNReal.ofReal LIM := ENNReal.ofReal_le_ofReal hKLIM
    _ = ENNReal.ofReal (LIM/s) * ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_mul (div_nonneg hLIM hs0.le),
          div_mul_cancel₀ _ (ne_of_gt hs0)]

/-- An additive resource counter satisfying the stated slot and stability bounds has expected
search cost at most `LIM / sin (2 * θ)`. -/
private theorem ledger_cap {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (valid : I → Bool) (hvalid : ∀ y, valid y = true ↔ y ∈ S) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi/2)
    (hmass : MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2)
    (M T : ℕ) (hMs : 1 ≤ (M:ℝ)*Real.sin (2*θ))
    (L : CappedSearchTrace I → ℕ) (inc : Option (I × ℕ) × ℕ × ℕ → ℕ)
    (hinc : ∀ (m : ℕ) (out : Option (I × ℕ) × ℕ × ℕ) (tr : CappedSearchTrace I),
      L (prependSearchReceipt m out tr) = inc out + L tr)
    (hzero : ∀ (_m : ℕ) (_out : Option (I × ℕ) × ℕ × ℕ) (y : I),
      L {(emptySearchTrace (I := I)) with result := some y} = 0)
    (hLempty : L emptySearchTrace = 0)
    (β C K LIM : ℝ) (hβ : (0:ℝ) ≤ β) (hC : (0:ℝ) ≤ C) (hK5C : K = 5*β + C)
    (hK0 : (0:ℝ) ≤ K) (hLIM0 : (0:ℝ) ≤ LIM)
    (hβC : (ENNReal.ofReal β) + (25/32) * (ENNReal.ofReal C) * ((6/5:ℝ≥0∞)) ≤ ENNReal.ofReal C)
    (hKLIM : K * ((6/5:ℝ)) ≤ LIM)
    (hslot : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3) (fun out => (inc out : ℝ≥0∞))
        ≤ (ENNReal.ofReal β) * ((ENNReal.ofReal ((6/5:ℝ)))^off)) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
        (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)) (fun tr => (L tr : ℝ≥0∞))
      ≤ ENNReal.ofReal (LIM/Real.sin (2*θ)) := by
  have hs0 : 0 < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (2*θ) ≤ 1 := by
    exact le_trans (Real.sin_le_one _) le_rfl
  set r := ENNReal.ofReal ((6/5:ℝ)) with hrdef
  have hr1 : 1 ≤ r := by
    rw [hrdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hex : ∃ k : ℕ, 1/Real.sin (2*θ) ≤ ((6/5:ℝ)^k) := exists_geometric_cross hs0
  set jstar := Nat.find hex with hjdef
  have hjle : 1/Real.sin (2*θ) ≤ ((6/5:ℝ)^(jstar:ℕ)) := Nat.find_spec hex
  have hjmin : ∀ j < jstar, ((6/5:ℝ)^j) < 1/Real.sin (2*θ) := by
    intro j hj
    by_contra hc
    have hge : 1/Real.sin (2*θ) ≤ ((6/5:ℝ)^j) := not_lt.mp hc
    have hfind : Nat.find hex ≤ j :=
      Nat.find_le (p := fun k => 1/Real.sin (2*θ) ≤ ((6/5:ℝ)^k)) hge
    have hj' := hj
    rw [hjdef] at hj'
    omega
  have hjbound : ((6/5:ℝ)^(jstar:ℕ))*Real.sin (2*θ) ≤ 6/5 := by
    rcases Nat.eq_zero_or_pos jstar with h0 | h0
    · rw [show ((6/5:ℝ)^((jstar:ℕ):ℕ)) = 1 from by rw [h0]; simp]
      linarith
    · have hlt := hjmin (jstar-1) (by omega)
      have hexp : ((6/5:ℝ)^((jstar:ℕ):ℕ))
          = (6/5)*((6/5:ℝ)^(((jstar:ℕ):ℕ)-1)) := by
        have hjsucc : ((6/5:ℝ)^(((jstar:ℕ):ℕ)-1+1))
            = (6/5)*((6/5:ℝ)^(((jstar:ℕ):ℕ)-1)) := pow_succ' _ _
        rw [show (((jstar:ℕ):ℕ)-1+1) = ((jstar:ℕ):ℕ) from by omega] at hjsucc
        exact hjsucc
      rw [hexp]
      have hlt' : ((6/5:ℝ)^(((jstar:ℕ):ℕ)-1))*Real.sin (2*θ) < 1 :=
        (lt_div_iff₀ hs0).mp hlt
      nlinarith
  have hgeo : ∀ n : ℕ, ∑ i ∈ Finset.range n, r^i ≤ 5 * r^n := by
    intro n
    have hiden := geo_five hrdef n
    calc ∑ i ∈ Finset.range n, r^i ≤ (∑ i ∈ Finset.range n, r^i) + 5 :=
          le_add_of_nonneg_right (by norm_num : (0:ℝ≥0∞) ≤ 5)
      _ = 5 * r^n := hiden
  have hwm : ∀ k : ℕ, jstar ≤ k → 1 ≤ (geometricWindow M k : ℝ)*Real.sin (2*θ) := by
    intro k hk
    refine geometric_window_mature hs0 hs1 M k hMs ?_
    have hmono : ((6/5:ℝ)^jstar) ≤ ((6/5:ℝ)^k) :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 6/5) hk
    calc (1:ℝ) = (1/Real.sin (2*θ)) * Real.sin (2*θ) := by
          rw [div_mul_cancel₀ _ (ne_of_gt hs0)]
      _ ≤ ((6/5:ℝ)^jstar) * Real.sin (2*θ) := mul_le_mul_of_nonneg_right hjle hs0.le
      _ ≤ ((6/5:ℝ)^k) * Real.sin (2*θ) := mul_le_mul_of_nonneg_right hmono hs0.le
  have hfail1 : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
        (geometricWindow M off) 3) (fun out => searchSlotFail valid out) ≤ 1 :=
    fun off => Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _
  have hfailρ : ∀ off : ℕ, jstar ≤ off →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
        (geometricWindow M off) 3) (fun out => searchSlotFail valid out) ≤ 25/32 := by
    intro off hoff
    exact slot_fail_le A hA j₀ S valid θ (geometricWindow M off) hvalid hθ0 hθ1 hmass
      (geometric_window_pos M off) (hwm off hoff)
  have hF0 : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid (schedFrom M off 0))
        (fun tr => (L tr : ℝ≥0∞)) = 0 := by
    intro off
    have hnil : schedFrom M off 0 = [] := rfl
    have hrun : searchForSchedule A hA j₀ S valid [] = PMF.pure emptySearchTrace := rfl
    rw [hnil, hrun, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure, hLempty,
        Nat.cast_zero]
  have hstep : ∀ off T : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid (schedFrom M off (T+1)))
          (fun tr => (L tr : ℝ≥0∞))
        ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
              (geometricWindow M off) 3) (fun out => (inc out : ℝ≥0∞))
          + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
              (geometricWindow M off) 3) (fun out => searchSlotFail valid out)
            * Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid (schedFrom M (off+1) T))
              (fun tr => (L tr : ℝ≥0∞)) := by
    intro off T
    have hEq := search_ledger_recursion A hA j₀ S valid L inc hinc hzero
      (geometricWindow M off) (schedFrom M (off+1) T)
    rw [schedFrom_succ]
    exact hEq.le
  have hfinal := cap_final (r := r) (ρ := (25/32:ℝ≥0∞))
    (β := ENNReal.ofReal β) (C := ENNReal.ofReal C) (jstar := jstar)
    hr1 hgeo
    (fun k => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M k))
      (geometricWindow M k) 3) (fun out => (inc out : ℝ≥0∞)))
    (fun off => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
      (geometricWindow M off) 3) (fun out => searchSlotFail valid out))
    (fun off T => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule A hA j₀ S valid (schedFrom M off T))
      (fun tr => (L tr : ℝ≥0∞)))
    hF0 hstep hslot hfail1 hfailρ
    (by
      have hbc := hβC
      rw [rat_coe_65] at hbc
      exact hbc)
    T
  have hKbound : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
      (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)) (fun tr => (L tr : ℝ≥0∞))
      ≤ (ENNReal.ofReal ((5*β + C))) * r^jstar := by
    rw [← schedFrom_zero]
    refine le_trans hfinal ?_
    have h5eq : ((5:ℝ≥0∞)) * ENNReal.ofReal β + ENNReal.ofReal C
        = ENNReal.ofReal (((5:ℝ))*β + C) := by
      rw [show ((5:ℝ≥0∞)) * ENNReal.ofReal β = ENNReal.ofReal (((5:ℝ))*β) from by
        rw [show ((5:ℝ≥0∞)) = ENNReal.ofReal ((5:ℝ)) from by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)],
        ENNReal.ofReal_add (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) hβ) hC]
    rw [h5eq]
  rw [hrdef, ← hK5C] at hKbound
  exact sin_bound hs0 hK0 hLIM0 hKLIM hjbound hKbound

/-- The extended nonnegative real value of the `k`th geometric window is at most `3 * (6 / 5) ^
k`. -/
private theorem window_coe_bound (M k : ℕ) :
    ((geometricWindow M k : ℕ) : ℝ≥0∞)
      ≤ (ENNReal.ofReal (3:ℝ)) * (ENNReal.ofReal ((6/5:ℝ)))^k := by
  have h1 : ((geometricWindow M k : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (((geometricWindow M k : ℕ)):ℝ) := (ENNReal.ofReal_natCast _).symm
  rw [h1, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 6/5),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
  exact ENNReal.ofReal_le_ofReal (geometric_window_le M k)

/-- The base-two ceiling logarithm `Nat.clog 2 m` is at most `m`. -/
private theorem clog2_le (m : ℕ) : Nat.clog 2 m ≤ m := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0]
    · have hm1 : m = 1 := by omega
      subst hm1
      simp
  · have h1 : 1 < m := by omega
    by_contra hc
    have hlt : m < Nat.clog 2 m := Nat.lt_of_not_le (fun hle => hc hle)
    have h2 : (2:ℕ) ^ (Nat.clog 2 m - 1) < m :=
      Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) h1
    have hkey : m ≤ Nat.clog 2 m - 1 := by omega
    have h3 : m ≤ (2:ℕ) ^ (Nat.clog 2 m - 1) :=
      le_trans hkey (le_of_lt Nat.lt_two_pow_self)
    omega

/-- Transfers the nonnegative real stability inequality `β + (25 / 32) * C * (6 / 5) ≤ C` to
extended nonnegative reals. -/
private theorem beta_C_coe (β C : ℝ) (h : β + (25/32:ℝ)*C*(6/5:ℝ) ≤ C)
    (hβ : (0:ℝ) ≤ β) (hC : (0:ℝ) ≤ C) :
    (ENNReal.ofReal β) + (25/32:ℝ≥0∞) * (ENNReal.ofReal C) * ((6/5:ℝ≥0∞)) ≤ ENNReal.ofReal C := by
  rw [rat_coe_25_32, rat_coe_65,
    show (ENNReal.ofReal ((25/32:ℝ)) * ENNReal.ofReal C * ENNReal.ofReal ((6/5:ℝ)))
      = ENNReal.ofReal (((25/32:ℝ)*C*(6/5:ℝ))) from by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 25/32),
        ← ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0:ℝ) ≤ 25/32) hC)],
    ← ENNReal.ofReal_add hβ
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 25/32) hC)
        (by norm_num : (0:ℝ) ≤ 6/5))]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- Every natural power of `ENNReal.ofReal (6 / 5)` is at least one. -/
private theorem rpow_ge_one (k : ℕ) : (1:ℝ≥0∞) ≤ (ENNReal.ofReal ((6/5:ℝ)))^k := by
  refine one_le_pow' ?_ k
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- Under the marked-mass and cap assumptions, expected phase queries, bits, validation queries,
preparations, and macro gates are bounded by `100`, `300`, `100`, `300`, and `400`,
respectively, divided by `sin (2 * θ)` [BoyerEtAl1998]. -/
theorem geometric_search_intrinsic_expected_resource_budget :
    ∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
      (j₀ : I) (S : Finset I) (valid : I → Bool) (M T : ℕ) (θ : ℝ),
      (∀ y, valid y=true ↔ y∈S) → 0<θ → θ<Real.pi/2 →
      MeasureProb (preparedAAState A j₀) S = (Real.sin θ)^2 →
      1≤(M:ℝ)*Real.sin (2*θ) →
      let p := searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.phaseQueries:ℝ≥0∞)) ≤ ENNReal.ofReal (100/Real.sin (2*θ)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.bits:ℝ≥0∞)) ≤ ENNReal.ofReal (300/Real.sin (2*θ)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.validationQueries:ℝ≥0∞)) ≤ ENNReal.ofReal (100/Real.sin (2*θ)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.prepareCalls:ℝ≥0∞)) ≤ ENNReal.ofReal (300/Real.sin (2*θ)) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.macroGates:ℝ≥0∞)) ≤ ENNReal.ofReal (400/Real.sin (2*θ)) := by
  intro A hA j₀ S valid M T θ hvalid hθ0 hθ1 hmass hMs
  have hrpow3 : ∀ off : ℕ, (1:ℝ≥0∞) ≤ (ENNReal.ofReal (3:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
    intro off
    calc (1:ℝ≥0∞) = 1 * 1 := (mul_one _).symm
      _ ≤ (ENNReal.ofReal (3:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
          refine mul_le_mul' ?_ (rpow_ge_one off)
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hshape : ∀ m : ℕ, ∀ out ∈ (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).support,
      out.2.2 ≤ m ∧ out.2.1 ≤ 3 * Nat.clog 2 m ∧ (out.1 = none → out.2.2 = 0) ∧
        ∀ y g, out.1 = some (y, g) → g = 3 * out.2.2 + 1 :=
    fun m out hout => sampled_attempt_shape A hA j₀ S m out hout
  have hslotP : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3) (fun out => (out.2.2 : ℝ≥0∞))
        ≤ (ENNReal.ofReal (3:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
    intro off
    refine le_trans (expectation_le_of_support _ _ _ ?_) (window_coe_bound M off)
    intro out hout
    exact Nat.cast_le.mpr (hshape (geometricWindow M off) out hout).1
  have hslotB : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ (ENNReal.ofReal (9:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
    intro off
    have hle : ∀ out ∈ (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3).support,
        (out.2.1 : ℝ≥0∞) ≤ ((3 * geometricWindow M off : ℕ) : ℝ≥0∞) := by
      intro out hout
      have h2 := (hshape (geometricWindow M off) out hout).2.1
      have hc := clog2_le (geometricWindow M off)
      have hle3 : out.2.1 ≤ 3 * geometricWindow M off := by omega
      exact_mod_cast hle3
    refine le_trans (expectation_le_of_support _ _ _ hle) ?_
    have hw := geometric_window_le M off
    have hge1 : (1:ℝ) ≤ ((6/5:ℝ)^off) := geopow_ge_one off
    have hstep : (((3 * geometricWindow M off : ℕ) : ℝ)) ≤ 9 * ((6/5:ℝ)^off) := by
      have hsplit : (((3 * geometricWindow M off : ℕ) : ℝ))
          = 3 * ((geometricWindow M off : ℕ):ℝ) := by
        push_cast
        ring
      rw [hsplit]
      nlinarith
    calc ((3 * geometricWindow M off : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((3 * geometricWindow M off : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (9 * ((6/5:ℝ)^off)) := ENNReal.ofReal_le_ofReal hstep
      _ = (ENNReal.ofReal (9:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),
            ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 6/5)]
  have hslotV : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3)
          (fun out => ((if out.1.isSome then 1 else 0 : ℕ) : ℝ≥0∞))
        ≤ (ENNReal.ofReal (3:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
    intro off
    have hle : ∀ out ∈ (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3).support,
        ((if out.1.isSome then 1 else 0 : ℕ) : ℝ≥0∞) ≤ 1 := by
      intro out _
      obtain ⟨o1, bits, q⟩ := out
      cases o1 with
      | none => simp
      | some _ => simp
    exact le_trans (expectation_le_of_support _ _ _ hle) (hrpow3 off)
  have hslotPre : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3)
          (fun out => (((if out.1.isSome then 2*out.2.2+1 else 0 : ℕ) : ℝ≥0∞)))
        ≤ (ENNReal.ofReal (9:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
    intro off
    have hle : ∀ out ∈ (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3).support,
        ((if out.1.isSome then 2*out.2.2+1 else 0 : ℕ) : ℝ≥0∞)
          ≤ ((2 * geometricWindow M off + 1 : ℕ) : ℝ≥0∞) := by
      intro out hout
      obtain ⟨o1, bits, q⟩ := out
      have h2 := (hshape (geometricWindow M off) (o1, bits, q) hout).1
      cases o1 with
      | none => simp
      | some pair =>
          obtain ⟨y, g⟩ := pair
          show ((if (some (y, g) : Option (I × ℕ)).isSome then 2*q+1 else 0 : ℕ) : ℝ≥0∞) ≤ _
          simp only [Option.isSome_some, ite_true]
          exact_mod_cast Nat.succ_le_succ (Nat.mul_le_mul_left 2 h2)
    refine le_trans (expectation_le_of_support _ _ _ hle) ?_
    have hw := geometric_window_le M off
    have hge1 : (1:ℝ) ≤ ((6/5:ℝ)^off) := geopow_ge_one off
    have hstep : (((2 * geometricWindow M off + 1 : ℕ) : ℝ)) ≤ 9 * ((6/5:ℝ)^off) := by
      have hsplit : (((2 * geometricWindow M off + 1 : ℕ) : ℝ))
          = 2 * ((geometricWindow M off : ℕ):ℝ) + 1 := by
        push_cast
        ring
      rw [hsplit]
      nlinarith
    calc ((2 * geometricWindow M off + 1 : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((2 * geometricWindow M off + 1 : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (9 * ((6/5:ℝ)^off)) := ENNReal.ofReal_le_ofReal hstep
      _ = (ENNReal.ofReal (9:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9),
            ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 6/5)]
  have hslotMac : ∀ off : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3)
          (fun out => (((out.1.map (fun p => p.2)).getD 0 : ℕ) : ℝ≥0∞))
        ≤ (ENNReal.ofReal (10:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
    intro off
    have hle : ∀ out ∈ (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M off))
          (geometricWindow M off) 3).support,
        (((out.1.map (fun p => p.2)).getD 0 : ℕ) : ℝ≥0∞)
          ≤ ((3 * geometricWindow M off + 1 : ℕ) : ℝ≥0∞) := by
      intro out hout
      obtain ⟨o1, bits, q⟩ := out
      obtain ⟨-, -, hnone, hsome⟩ := hshape (geometricWindow M off) (o1, bits, q) hout
      have hq := (hshape (geometricWindow M off) (o1, bits, q) hout).1
      cases o1 with
      | none => simp
      | some pair =>
          obtain ⟨y, g⟩ := pair
          have hg := hsome y g rfl
          have hbound : g ≤ 3 * geometricWindow M off + 1 := by omega
          show ((g : ℕ) : ℝ≥0∞) ≤ ((3 * geometricWindow M off + 1 : ℕ) : ℝ≥0∞)
          exact_mod_cast hbound
    refine le_trans (expectation_le_of_support _ _ _ hle) ?_
    have hw := geometric_window_le M off
    have hge1 : (1:ℝ) ≤ ((6/5:ℝ)^off) := geopow_ge_one off
    have hstep : (((3 * geometricWindow M off + 1 : ℕ) : ℝ)) ≤ 10 * ((6/5:ℝ)^off) := by
      have hsplit : (((3 * geometricWindow M off + 1 : ℕ) : ℝ))
          = 3 * ((geometricWindow M off : ℕ):ℝ) + 1 := by
        push_cast
        ring
      rw [hsplit]
      nlinarith
    calc ((3 * geometricWindow M off + 1 : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (((3 * geometricWindow M off + 1 : ℕ):ℝ)) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (10 * ((6/5:ℝ)^off)) := ENNReal.ofReal_le_ofReal hstep
      _ = (ENNReal.ofReal (10:ℝ)) * ((ENNReal.ofReal ((6/5:ℝ)))^off) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10),
            ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 6/5)]
  have hP := ledger_cap A hA j₀ S valid hvalid θ hθ0 hθ1 hmass M T hMs
    (fun tr => tr.phaseQueries) (fun out => out.2.2)
    (fun m out tr => rfl) (fun m out y => rfl) rfl
    3 48 63 100 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (beta_C_coe 3 48 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) hslotP
  have hB := ledger_cap A hA j₀ S valid hvalid θ hθ0 hθ1 hmass M T hMs
    (fun tr => tr.bits) (fun out => out.2.1)
    (fun m out tr => rfl) (fun m out y => rfl) rfl
    9 144 189 300 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (beta_C_coe 9 144 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) hslotB
  have hV := ledger_cap A hA j₀ S valid hvalid θ hθ0 hθ1 hmass M T hMs
    (fun tr => tr.validationQueries) (fun out => if out.1.isSome then 1 else 0)
    (fun m out tr => rfl) (fun m out y => rfl) rfl
    3 48 63 100 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (beta_C_coe 3 48 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) hslotV
  have hPre := ledger_cap A hA j₀ S valid hvalid θ hθ0 hθ1 hmass M T hMs
    (fun tr => tr.prepareCalls) (fun out => if out.1.isSome then 2*out.2.2+1 else 0)
    (fun m out tr => rfl) (fun m out y => rfl) rfl
    9 144 189 300 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (beta_C_coe 9 144 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) hslotPre
  have hMac := ledger_cap A hA j₀ S valid hvalid θ hθ0 hθ1 hmass M T hMs
    (fun tr => tr.macroGates) (fun out => (out.1.map (fun p => p.2)).getD 0)
    (fun m out tr => rfl) (fun m out y => rfl) rfl
    10 160 210 400 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (beta_C_coe 10 160 (by norm_num) (by norm_num) (by norm_num)) (by norm_num) hslotMac
  exact ⟨hP, hB, hV, hPre, hMac⟩

/-- Every supported trace has phase queries at most the window sum, validation queries at most
the schedule length, and bits at most three times the sum of ceiling logarithms. -/
private theorem search_support_path_caps (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (valid : I → Bool) :
    ∀ (ms : List ℕ) (tr : CappedSearchTrace I),
      tr ∈ (searchForSchedule A hA j₀ S valid ms).support →
      tr.phaseQueries ≤ ms.sum ∧ tr.validationQueries ≤ ms.length ∧
        tr.bits ≤ 3 * (ms.map (Nat.clog 2)).sum := by
  intro ms
  induction ms with
  | nil =>
      intro tr htr
      have hrw : searchForSchedule A hA j₀ S valid [] = PMF.pure emptySearchTrace := rfl
      rw [hrw] at htr
      have htr' : tr = emptySearchTrace := by
        simpa [PMF.mem_support_pure_iff] using htr
      subst htr'
      exact ⟨by
          show (emptySearchTrace : CappedSearchTrace I).phaseQueries ≤ (List.sum ([] : List ℕ))
          rfl, by
          show (emptySearchTrace : CappedSearchTrace I).validationQueries ≤ ([] : List ℕ).length
          rfl, by
          show (emptySearchTrace : CappedSearchTrace I).bits
            ≤ 3 * (List.map (Nat.clog 2) ([] : List ℕ)).sum
          rfl⟩
  | cons m ms ih =>
      intro tr htr
      rw [searchCons_eq] at htr
      obtain ⟨out, hout, htr⟩ := (PMF.mem_support_bind_iff _ _ _).mp htr
      obtain ⟨o1, bits, q⟩ := out
      have hshape := sampled_attempt_shape A hA j₀ S m (o1, bits, q) hout
      obtain ⟨hqle, hbitsle, hnone, hsome⟩ := hshape
      cases o1 with
      | none =>
          have hfail : searchSlotFail valid (none, bits, q) := by
            rintro ⟨y, g, ho, -⟩
            exact absurd ho (by simp)
          rw [searchCont_fail A hA j₀ S valid m ms (none, bits, q) hfail] at htr
          obtain ⟨tr', htr', htr''⟩ := (PMF.mem_support_map_iff _ _ _).mp htr
          obtain ⟨h1, h2, h3⟩ := ih tr' htr'
          obtain ⟨rfl⟩ := htr''
          obtain ⟨-, -, -, -, gf_ph, gf_val, -, gf_bits⟩ :=
            geometric_search_receipt_actual_ledger_updates m (none, bits, q) tr'
          show (none, bits, q).2.2 + tr'.phaseQueries ≤ m + ms.sum ∧
            (if (none : Option (I × ℕ)).isSome = true then 1 else 0) + tr'.validationQueries
              ≤ ms.length + 1 ∧
            (none, bits, q).2.1 + tr'.bits
              ≤ 3 * (Nat.clog 2 m + (List.map (Nat.clog 2) ms).sum)
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
          have hq : ((none : Option (I × ℕ)), bits, q).2.2 = q := rfl
          have hbb : ((none : Option (I × ℕ)), bits, q).2.1 = bits := rfl
          exact ⟨by omega, by omega, by omega⟩
      | some pair =>
          obtain ⟨y, g⟩ := pair
          by_cases hv : valid y = true
          · rw [searchCont_some_valid A hA j₀ S valid m ms y g bits q hv] at htr
            have htr' : tr = prependSearchReceipt m (some (y, g), bits, q)
                {(emptySearchTrace (I := I)) with result := some y} := by
              simpa [PMF.mem_support_pure_iff] using htr
            subst htr'
            show (some (y, g), bits, q).2.2 ≤ m + ms.sum ∧
              (if (some (y, g) : Option (I × ℕ)).isSome = true then 1 else 0)
                ≤ ms.length + 1 ∧
              (some (y, g), bits, q).2.1
                ≤ 3 * (Nat.clog 2 m + (List.map (Nat.clog 2) ms).sum)
            simp only [Option.isSome_some, ite_true]
            have hq : (some (y, g), bits, q).2.2 = q := rfl
            have hbb : (some (y, g), bits, q).2.1 = bits := rfl
            exact ⟨le_trans hqle (Nat.le_add_right _ _), by omega, by omega⟩
          · have hfail : searchSlotFail valid (some (y, g), bits, q) := by
              rintro ⟨y', g', ho, hv'⟩
              have hyg : (y, g) = (y', g') := Option.some.inj ho
              refine hv ?_
              rw [show y = y' from congrArg Prod.fst hyg]
              exact hv'
            rw [searchCont_fail A hA j₀ S valid m ms (some (y, g), bits, q) hfail] at htr
            obtain ⟨tr', htr', htr''⟩ := (PMF.mem_support_map_iff _ _ _).mp htr
            obtain ⟨h1, h2, h3⟩ := ih tr' htr'
            obtain ⟨rfl⟩ := htr''
            obtain ⟨-, -, -, -, gf_ph, gf_val, -, gf_bits⟩ :=
              geometric_search_receipt_actual_ledger_updates m (some (y, g), bits, q) tr'
            show (some (y, g), bits, q).2.2 + tr'.phaseQueries ≤ m + ms.sum ∧
              (if (some (y, g) : Option (I × ℕ)).isSome = true then 1 else 0)
                + tr'.validationQueries ≤ ms.length + 1 ∧
              (some (y, g), bits, q).2.1 + tr'.bits
                ≤ 3 * (Nat.clog 2 m + (List.map (Nat.clog 2) ms).sum)
            simp only [Option.isSome_some, ite_true]
            have hq : (some (y, g), bits, q).2.2 = q := rfl
            have hbb : (some (y, g), bits, q).2.1 = bits := rfl
            exact ⟨by omega, by omega, by omega⟩

/-- With exact validation, zero marked mass gives certain failure, unit marked mass gives
certain success for positive cutoff, and every supported trace satisfies the stated query
and bit caps. -/
theorem geometric_search_zero_one_endpoints_and_path_caps :
    ∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
      (j₀ : I) (S : Finset I) (valid : I → Bool) (M T : ℕ), (∀ y, valid y=true ↔ y∈S) →
      (MeasureProb (preparedAAState A j₀) S=0 → Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)) (fun tr => tr.result=none)=1) ∧
      (MeasureProb (preparedAAState A j₀) S=1 → 0<T → Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)) (fun tr => tr.result.isSome)=1) ∧
      (∀ tr ∈ (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)).support,
        tr.phaseQueries ≤ (geometricSearchSchedule M T).sum ∧ tr.validationQueries≤T ∧
        tr.bits ≤ 3*((geometricSearchSchedule M T).map (Nat.clog 2)).sum) := by
  intro A hA j₀ S valid M T hvalid
  refine ⟨?_, ?_, ?_⟩
  · intro hmass
    have key : ∀ (T off : ℕ), Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (searchForSchedule A hA j₀ S valid (schedFrom M off T)) (fun tr => tr.result = none) = 1 := by
      intro T
      induction T with
      | zero =>
          intro off
          have hnil : schedFrom M off 0 = [] := rfl
          have hrun : searchForSchedule A hA j₀ S valid [] = PMF.pure emptySearchTrace := rfl
          rw [hnil, hrun, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,
              Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
          norm_num [emptySearchTrace]
      | succ T ih =>
          intro off
          rw [schedFrom_succ, search_event_none_recursion,
            slot_fail_eq_one A hA j₀ S valid (geometricWindow M off) hvalid
              (geometric_window_pos M off) hmass, ih (off + 1), one_mul]
    rw [← schedFrom_zero]
    exact key T 0
  · intro hmass hT0
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    have hfail0 : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled A hA j₀ S (Nat.clog 2 (geometricWindow M 0))
          (geometricWindow M 0) 3) (fun out => searchSlotFail valid out) = 0 := by
      have hw1 : geometricWindow M 0 = 1 := by
        show max 1 (min M ((6^(0:ℕ)+5^(0:ℕ)-1)/5^(0:ℕ))) = 1
        norm_num
      rw [hw1]
      exact slot_fail_first_zero A hA j₀ S valid hvalid hmass
    have hzero : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid
        (geometricSearchSchedule M (T' + 1))) (fun tr => tr.result = none) = 0 := by
      have hS : geometricSearchSchedule M (T' + 1) = schedFrom M 0 (T' + 1) :=
        (schedFrom_zero M (T' + 1)).symm
      rw [hS, schedFrom_succ, search_event_none_recursion, hfail0, zero_mul]
    have hpart := event_compl (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M (T'+1)))
      (fun tr => tr.result = none)
    have hcongr : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M (T'+1)))
        (fun tr => ¬ tr.result = none)
        = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M (T'+1)))
            (fun tr => tr.result.isSome) :=
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun tr => by
        constructor
        · intro h
          cases hr : tr.result with
          | none => exact absurd hr h
          | some _ => rfl
        · intro h hr
          rw [hr] at h
          simp at h)
    rw [hcongr, hzero, zero_add] at hpart
    exact hpart
  · intro tr htr
    obtain ⟨h1, h2, h3⟩ := search_support_path_caps A hA j₀ S valid
      (geometricSearchSchedule M T) tr htr
    refine ⟨h1, ?_, h3⟩
    rw [geometricSearchSchedule, List.length_ofFn] at h2
    exact h2

end Qatlib.Concepts.WalkSearch.QuantumAccess
