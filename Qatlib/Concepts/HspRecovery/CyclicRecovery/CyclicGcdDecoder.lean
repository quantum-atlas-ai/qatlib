/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicPeriodSampling
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Counted gcd decoding of cyclic periods

Defines a counted Euclidean algorithm, a gcd fold over Fourier records, and the period candidate
`cyclicPeriodDecode`. The verified decoder tests this candidate using two oracle readouts, and
`cyclicCountedRecovery` combines verification with fresh sampling.

For a function whose collisions are exactly congruence modulo a positive divisor `r` of `N`,
proves a failure bound `r / 2 ^ m`, absence of incorrect verified outputs, and explicit query,
gate, and Euclidean-step budgets. This develops cyclic period postprocessing in the setting of
[Shor1997].

## Main statements

* `cyclic_decoder_supported_divisor_and_cost`: gives the candidate divisor, gcd criterion, and
  step bound.
* `cyclic_verified_recovery_probability`: bounds failure and excludes incorrect outputs.
* `cyclic_accessible_budget_and_measurements`: combines success and counted recovery resources.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.CyclicRecovery

open scoped Classical

variable {R : Type} [Fintype R] [DecidableEq R] [AddCommGroup R]

/-- Runs the Euclidean algorithm with bounded fuel and returns its current gcd candidate
together with the number of remainder steps. -/
def euclidFuel : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, _ => (a, 0)
  | _ + 1, a, 0 => (a, 0)
  | fuel + 1, a, b + 1 =>
    let result := euclidFuel fuel (b + 1) (a % (b + 1))
    (result.1, result.2 + 1)

/-- If the second argument is smaller than the available fuel, the Euclidean computation returns
`Nat.gcd a b`. -/
theorem euclidFuel_gcd : ∀ (fuel a b : ℕ), b < fuel →
    (euclidFuel fuel a b).1 = Nat.gcd a b := by
  intro fuel
  induction fuel with
  | zero => intro a b h; omega
  | succ fuel ih =>
    intro a b h
    cases b with
    | zero =>
      show (a, 0).1 = Nat.gcd a 0
      exact (Nat.gcd_zero_right a).symm
    | succ b =>
      have hstep : euclidFuel (fuel + 1) a (b + 1) =
          ((euclidFuel fuel (b + 1) (a % (b + 1))).1,
            (euclidFuel fuel (b + 1) (a % (b + 1))).2 + 1) := rfl
      have h2 : a % (b + 1) < b + 1 := Nat.mod_lt a (by omega)
      have hfuel : a % (b + 1) < fuel := by omega
      rw [hstep]
      show (euclidFuel fuel (b + 1) (a % (b + 1))).1 = Nat.gcd a (b + 1)
      rw [ih (b + 1) (a % (b + 1)) hfuel, Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a,
        Nat.gcd_comm]

/-- With fuel exceeding the second argument, the Euclidean remainder-step count is at most that
argument. -/
theorem euclidFuel_count : ∀ (fuel a b : ℕ), b < fuel →
    (euclidFuel fuel a b).2 ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro a b h; omega
  | succ fuel ih =>
    intro a b h
    cases b with
    | zero => exact Nat.le_refl 0
    | succ b =>
      have hstep : euclidFuel (fuel + 1) a (b + 1) =
          ((euclidFuel fuel (b + 1) (a % (b + 1))).1,
            (euclidFuel fuel (b + 1) (a % (b + 1))).2 + 1) := rfl
      have h2 : a % (b + 1) < b + 1 := Nat.mod_lt a (by omega)
      have hfuel : a % (b + 1) < fuel := by omega
      have hmod : a % (b + 1) ≤ b := Nat.le_of_lt_succ h2
      have hih := ih (b + 1) (a % (b + 1)) hfuel
      rw [hstep]
      show (euclidFuel fuel (b + 1) (a % (b + 1))).2 + 1 ≤ b + 1
      omega

/-- Runs the counted Euclidean algorithm on `a` and `b` with fuel `b + 1`. -/
def euclidCounted (a b : ℕ) : ℕ × ℕ := euclidFuel (b + 1) a b

/-- The value returned by `euclidCounted a b` is `Nat.gcd a b`. -/
theorem euclidCounted_gcd (a b : ℕ) : (euclidCounted a b).1 = Nat.gcd a b :=
  euclidFuel_gcd (b + 1) a b (Nat.lt_succ_self b)

/-- The counted Euclidean algorithm uses at most `b` remainder steps on inputs `a` and `b`. -/
theorem euclidCounted_count (a b : ℕ) : (euclidCounted a b).2 ≤ b :=
  euclidFuel_count (b + 1) a b (Nat.lt_succ_self b)

/-- Folds the counted Euclidean algorithm over a list, starting from `N`, and accumulates the
remainder-step counts. -/
def cyclicGcdCounted (N : ℕ) (xs : List ℕ) : ℕ × ℕ :=
  xs.foldl (fun acc x =>
    let result := euclidCounted acc.1 x
    (result.1, acc.2 + result.2)) (N, 0)

/-- The counted gcd fold returns the ordinary gcd fold, with accumulated count at most the
initial count plus the sum of the list. -/
theorem cyclicGcdCounted_foldl (a c : ℕ) (xs : List ℕ) :
    (xs.foldl (fun acc x =>
        ((euclidCounted acc.1 x).1, acc.2 + (euclidCounted acc.1 x).2)) (a, c)).1
      = xs.foldl Nat.gcd a ∧
    (xs.foldl (fun acc x =>
        ((euclidCounted acc.1 x).1, acc.2 + (euclidCounted acc.1 x).2)) (a, c)).2
      ≤ c + xs.sum := by
  induction xs generalizing a c with
  | nil => exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨ih1, ih2⟩ := ih ((euclidCounted a x).1) (c + (euclidCounted a x).2)
    rw [List.foldl_cons, List.foldl_cons]
    constructor
    · calc (xs.foldl (fun acc x =>
              ((euclidCounted acc.1 x).1, acc.2 + (euclidCounted acc.1 x).2))
              ((euclidCounted a x).1, c + (euclidCounted a x).2)).1
          = xs.foldl Nat.gcd ((euclidCounted a x).1) := ih1
        _ = xs.foldl Nat.gcd (Nat.gcd a x) := by rw [euclidCounted_gcd]
    · rw [List.sum_cons]
      have hx := euclidCounted_count a x
      calc (xs.foldl (fun acc x =>
              ((euclidCounted acc.1 x).1, acc.2 + (euclidCounted acc.1 x).2))
              ((euclidCounted a x).1, c + (euclidCounted a x).2)).2
          ≤ (c + (euclidCounted a x).2) + xs.sum := ih2
        _ ≤ c + (x + xs.sum) := by omega

/-- If every list entry is at most `B`, its sum is at most the list length times `B + 1`. -/
theorem list_sum_le_length_mul {xs : List ℕ} {B : ℕ} (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * (B + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have hx := h x List.mem_cons_self
    have hrest : ∀ y ∈ xs, y ≤ B := fun y hy => h y (List.mem_cons_of_mem x hy)
    have hih := ih hrest
    omega

/-- The counted cyclic gcd equals the ordinary gcd fold; if every entry is at most `N`, its
count is at most the list length times `N + 1`. -/
theorem cyclic_counted_euclidean_gcd (N : ℕ) (xs : List ℕ) :
    (cyclicGcdCounted N xs).1 = xs.foldl Nat.gcd N ∧
    ((∀ x ∈ xs, x ≤ N) → (cyclicGcdCounted N xs).2 ≤ xs.length * (N + 1)) := by
  obtain ⟨h1, h2⟩ := cyclicGcdCounted_foldl N 0 xs
  refine ⟨h1, fun hxs => ?_⟩
  calc (cyclicGcdCounted N xs).2 ≤ 0 + xs.sum := h2
    _ ≤ xs.length * (N + 1) := by
        rw [Nat.zero_add]
        exact list_sum_le_length_mul hxs

/-- Decodes a period candidate by dividing `N` by the gcd of `N` and all sampled residue
representatives. -/
def cyclicPeriodDecode {m : ℕ} (N : ℕ) (ω : Fin m → Fin N) : ℕ :=
  N / (cyclicGcdCounted N (List.ofFn fun i => (ω i).val)).1

/-- A gcd fold starting from a positive natural remains positive. -/
theorem foldl_gcd_pos {a : ℕ} (ha : 0 < a) (xs : List ℕ) : 0 < xs.foldl Nat.gcd a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih (Nat.gcd_pos_of_pos_left x ha)

/-- The result of a gcd fold divides its initial accumulator. -/
theorem foldl_gcd_dvd_left (a : ℕ) (xs : List ℕ) : xs.foldl Nat.gcd a ∣ a := by
  induction xs generalizing a with
  | nil => exact dvd_refl a
  | cons x xs ih => exact (ih (Nat.gcd a x)).trans (Nat.gcd_dvd_left a x)

/-- The result of a gcd fold divides every entry in the folded list. -/
theorem foldl_gcd_dvd_of_mem (a : ℕ) (xs : List ℕ) {x : ℕ} (hx : x ∈ xs) :
    xs.foldl Nat.gcd a ∣ x := by
  induction xs generalizing a with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl hxy =>
      subst hxy
      exact (foldl_gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    | inr hmem => exact ih (Nat.gcd a y) hmem

/-- Scaling every list entry and the initial accumulator by `q` scales the gcd fold by `q`. -/
theorem foldl_gcd_mul (q : ℕ) (xs : List ℕ) (a : ℕ) :
    (xs.map (q * ·)).foldl Nat.gcd (q * a) = q * xs.foldl Nat.gcd a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, Nat.gcd_mul_left]
    exact ih _

/-- For records divisible by `N / r`, the decoded candidate is a positive divisor of `r`, its
Euclidean count is at most `m * (N + 1)`, and it equals `r` exactly when the scaled-record
gcd fold is one. -/
theorem cyclic_decoder_supported_divisor_and_cost (N r m : ℕ) (ω : Fin m → Fin N)
    (hN : 0 < N) (hr : 0 < r) (hrdvd : r ∣ N) (hsupp : ∀ i, (N / r) ∣ (ω i).val) :
    0 < cyclicPeriodDecode N ω ∧ cyclicPeriodDecode N ω ∣ r ∧
    (cyclicGcdCounted N (List.ofFn (fun i => (ω i).val))).2 ≤ m * (N + 1) ∧
    (cyclicPeriodDecode N ω = r ↔
      (List.ofFn (fun i => (ω i).val / (N / r))).foldl Nat.gcd r = 1) := by
  set q := N / r with hqdef
  have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hN hrdvd) hr
  have hrq : r * q = N := Nat.mul_div_cancel' hrdvd
  have hNqr : N = q * r := hrq.symm.trans (Nat.mul_comm r q)
  set ks : List ℕ := List.ofFn (fun i => (ω i).val / q) with hks
  have hL : List.ofFn (fun i => (ω i).val) = ks.map (q * ·) := by
    rw [hks, List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => (Nat.mul_div_cancel' (hsupp i)).symm)
  set g' := ks.foldl Nat.gcd r with hg'
  have hg'pos : 0 < g' := hg' ▸ foldl_gcd_pos hr ks
  have hg'r : g' ∣ r := hg'.symm ▸ foldl_gcd_dvd_left r ks
  have hgcd : (cyclicGcdCounted N (List.ofFn fun i => (ω i).val)).1 = q * g' := by
    have h1 := (cyclic_counted_euclidean_gcd N (List.ofFn fun i => (ω i).val)).1
    rw [hL] at h1
    calc (cyclicGcdCounted N (List.ofFn fun i => (ω i).val)).1
        = (ks.map (q * ·)).foldl Nat.gcd N := by rw [hL]; exact h1
      _ = (ks.map (q * ·)).foldl Nat.gcd (q * r) := by rw [hNqr]
      _ = q * ks.foldl Nat.gcd r := foldl_gcd_mul q ks r
      _ = q * g' := congrArg (q * ·) hg'.symm
  have hp : cyclicPeriodDecode N ω = r / g' := by
    show N / (cyclicGcdCounted N (List.ofFn fun i => (ω i).val)).1 = r / g'
    rw [hgcd]
    conv_lhs => rw [hNqr]
    exact Nat.mul_div_mul_left r g' hqpos
  have hcost : (cyclicGcdCounted N (List.ofFn fun i => (ω i).val)).2 ≤ m * (N + 1) := by
    have h2 := (cyclic_counted_euclidean_gcd N (List.ofFn fun i => (ω i).val)).2
      (fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact le_of_lt (ω i).isLt)
    rwa [List.length_ofFn] at h2
  refine ⟨?_, ?_, hcost, ?_⟩
  · rw [hp]
    exact Nat.div_pos (Nat.le_of_dvd hr hg'r) hg'pos
  · rw [hp]
    exact ⟨g', (Nat.div_mul_cancel hg'r).symm⟩
  · rw [hp]
    constructor
    · intro h
      have h2 : g' * (r / g') = r := Nat.mul_div_cancel' hg'r
      rw [h] at h2
      exact Nat.mul_right_cancel hr (by rw [h2, one_mul])
    · intro h
      rw [h, Nat.div_one]

/-- Returns the gcd-decoded candidate only when querying `f` at zero and at the candidate modulo
`N` gives equal labels. -/
def cyclicVerifiedDecode {R : Type} [Fintype R] [DecidableEq R] {m : ℕ}
    (N : ℕ) (hN : 0 < N) (f : Fin N → R) (ω : Fin m → Fin N) : Option ℕ :=
  if f (⟨0, hN⟩ : Fin N) = f (⟨(cyclicPeriodDecode N ω) % N, Nat.mod_lt _ hN⟩ : Fin N)
    then some (cyclicPeriodDecode N ω) else none

/-- Expands the verified decoder as the comparison of the labels at zero and at the decoded
candidate modulo `N`. -/
theorem cyclicVerifiedDecode_def {R : Type} [Fintype R] [DecidableEq R] {m : ℕ}
    (N : ℕ) (hN : 0 < N) (f : Fin N → R) (ω : Fin m → Fin N) :
    cyclicVerifiedDecode N hN f ω =
      if f (⟨0, hN⟩ : Fin N) = f (⟨(cyclicPeriodDecode N ω) % N, Nat.mod_lt _ hN⟩ : Fin N)
        then some (cyclicPeriodDecode N ω) else none := rfl

/-- The costed output-label distribution obtained by measuring a single additive oracle query on
the basis input `(x, 0)`, charged one query. -/
noncomputable def cyclicCountedQueryReadout {N : ℕ} (f : Fin N → R) (x : Fin N) :
    CostedLaw R :=
  (bornDistribution
    (Run (AddOracle f) ([Step.query] : Circuit (Fin N × R)) (Ket (x, 0)))
    (normalized_run_addOracle_query f (normalized_ket (x, 0)))).map
      (fun q => (q.2, 1))

/-- A counted basis-state oracle readout deterministically returns `f x` with cost one. -/
theorem cyclicCountedQueryReadout_eq {N : ℕ} (f : Fin N → R) (x : Fin N) :
    cyclicCountedQueryReadout f x = PMF.pure (f x, 1) := by
  have hrun : Run (AddOracle f) ([Step.query] : Circuit (Fin N × R)) (Ket (x, 0)) =
      Ket (x, f x) := by
    rw [run_addOracle_query, applyGate_addOracle_ket, zero_add]
  simp only [cyclicCountedQueryReadout, hrun, bornDistribution_ket, PMF.pure_map]

/-- Verifies the decoded period by comparing two fresh counted oracle readouts. -/
noncomputable def cyclicCountedVerification {m : ℕ} (N : ℕ) (hN : 0 < N)
    (f : Fin N → R) (ω : Fin m → Fin N) : CostedLaw (Option ℕ) :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (cyclicCountedQueryReadout f (⟨0, hN⟩ : Fin N)) fun a =>
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (cyclicCountedQueryReadout f
      (⟨cyclicPeriodDecode N ω % N, Nat.mod_lt _ hN⟩ : Fin N)) fun b =>
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (if a = b then some (cyclicPeriodDecode N ω) else none)

/-- Counted verification deterministically returns `cyclicVerifiedDecode` with query cost two. -/
theorem cyclicCountedVerification_eq {m : ℕ} (N : ℕ) (hN : 0 < N)
    (f : Fin N → R) (ω : Fin m → Fin N) :
    cyclicCountedVerification N hN f ω = PMF.pure (cyclicVerifiedDecode N hN f ω, 2) := by
  simp [cyclicCountedVerification, cyclicCountedQueryReadout_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret, PMF.pure_bind, PMF.pure_map, cyclicVerifiedDecode_def]

/-- Samples `m` fresh cyclic Fourier records and verifies the resulting gcd-decoded period in a
costed probability law. -/
noncomputable def cyclicCountedRecovery (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    CostedLaw (Option ℕ) :=
  Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (cyclicCountedFreshSamples N hN f m) (cyclicCountedVerification N hN f)

/-- Counted recovery is the fresh-sample law mapped to the verified decoder output with constant
query cost `m + 2`. -/
theorem cyclicCountedRecovery_eq (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    cyclicCountedRecovery N hN f m =
      (cyclicFreshSamples N hN f m).map (fun ω => (cyclicVerifiedDecode N hN f ω, m + 2)) := by
  simp only [cyclicCountedRecovery, cyclicCountedFreshSamples_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind,
    cyclicCountedVerification_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge, PMF.bind_map, PMF.pure_map,
    Function.comp_def]
  rfl

/-- Discarding costs from counted recovery gives the fresh-sample distribution mapped through
verified decoding. -/
theorem cyclicCountedRecovery_erase (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    (cyclicCountedRecovery N hN f m).map Prod.fst =
      (cyclicFreshSamples N hN f m).map (cyclicVerifiedDecode N hN f) := by
  rw [cyclicCountedRecovery_eq, PMF.map_comp]
  rfl

/-- The query cost of counted cyclic recovery is bounded by `m + 2`. -/
theorem cyclicCountedRecovery_bounded (N : ℕ) (hN : 0 < N) (f : Fin N → R) (m : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.BoundedBy (cyclicCountedRecovery N hN f m) (m + 2) := by
  rw [cyclicCountedRecovery_eq]
  intro out hout
  obtain ⟨ω, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  exact le_refl _

/-- The probability of returning `r` within query budget `m + 2` equals the independent-record
verified success probability, converted to `ENNReal`. -/
theorem cyclicCountedRecovery_within (N r m : ℕ) (hN : 0 < N) (f : Fin N → R) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.within (cyclicCountedRecovery N hN f m) (m + 2) (fun out => out = some r) =
      ENNReal.ofReal ((cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicVerifiedDecode N hN f ω = some r)) := by
  rw [cyclicCountedRecovery_eq]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.within, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, le_refl,
    and_true]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_fintype]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  exact cyclicFreshSamples_event N hN f m _

/-- For the exact collision promise and supported records, verification returns `r` exactly when
the gcd decoder does, and every returned candidate equals `r`. Also identifies each
basis-state query output as `Ket (x, f x)`. -/
theorem cyclic_candidate_actual_two_query_verification (N r m : ℕ) (hN : 0 < N)
    (f : Fin N → R) (ω : Fin m → Fin N)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r)
    (hsupp : ∀ i, (N / r) ∣ (ω i).val) :
    (cyclicVerifiedDecode N hN f ω = some r ↔ cyclicPeriodDecode N ω = r) ∧
    (∀ p, cyclicVerifiedDecode N hN f ω = some p → p = r) ∧
    (∀ x : Fin N, Run (AddOracle f) ([Step.query] : Circuit (Fin N × R)) (Ket (x, 0)) =
      Ket (x, f x)) := by
  obtain ⟨hpos, hpr, -, -⟩ := cyclic_decoder_supported_divisor_and_cost N r m ω hN hr hrdvd hsupp
  have hcond : f (⟨0, hN⟩ : Fin N) =
        f (⟨(cyclicPeriodDecode N ω) % N, Nat.mod_lt _ hN⟩ : Fin N)
      ↔ cyclicPeriodDecode N ω = r := by
    rw [hcol]
    show (0 : ℕ) % r = (cyclicPeriodDecode N ω) % N % r ↔ _
    rw [Nat.zero_mod, Nat.mod_mod_of_dvd _ hrdvd]
    constructor
    · intro h
      have hrp : r ∣ cyclicPeriodDecode N ω := by
        rw [Nat.dvd_iff_mod_eq_zero]
        exact h.symm
      exact Nat.dvd_antisymm hpr hrp
    · intro h
      rw [h, Nat.mod_self]
  refine ⟨?_, ?_, ?_⟩
  · rw [cyclicVerifiedDecode_def]
    by_cases hc : f (⟨0, hN⟩ : Fin N) =
        f (⟨(cyclicPeriodDecode N ω) % N, Nat.mod_lt _ hN⟩ : Fin N)
    · rw [if_pos hc]
      constructor
      · intro h
        exact Option.some.inj h
      · intro h
        rw [h]
    · rw [if_neg hc]
      constructor
      · intro h
        cases h
      · intro h
        exact absurd (hcond.mpr h) hc
  · intro p' h
    rw [cyclicVerifiedDecode_def] at h
    by_cases hc : f (⟨0, hN⟩ : Fin N) =
        f (⟨(cyclicPeriodDecode N ω) % N, Nat.mod_lt _ hN⟩ : Fin N)
    · rw [if_pos hc] at h
      have h1 : cyclicPeriodDecode N ω = p' := Option.some.inj h
      rw [← h1]
      exact hcond.mp hc
    · rw [if_neg hc] at h
      cases h
  · intro x
    show ApplyGate (AddOracle f) (Ket (x, (0 : R))) = Ket (x, f x)
    rw [applyGate_addOracle_ket]
    simp

/-- The product probability assigned to any finite independent sample sequence is nonnegative. -/
theorem FinDist.probOf_nonneg {X : Type} [Fintype X] (p : FinDist X) {L : ℕ}
    (ω : Fin L → X) : 0 ≤ p.probOf ω :=
  Finset.prod_nonneg fun _ _ => p.nonneg _

/-- Under the exact cyclic collision promise, a length-`m` record sequence has probability `(1 /
r) ^ m` if all records are divisible by `N / r`, and zero otherwise. -/
theorem cyclicSampleDist_probOf (N r : ℕ) (hN : 0 < N) (f : Fin N → R)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r)
    (m : ℕ) (ω : Fin m → Fin N) :
    (cyclicSampleDist N hN f).probOf ω =
      if (∀ i, (N / r) ∣ (ω i).val) then (1 / (r : ℝ)) ^ m else 0 := by
  have hprob := cyclic_period_born_uniform_multiples N r hN f hr hrdvd hcol
  show (∏ i, (cyclicSampleDist N hN f).prob (ω i)) = _
  rw [Finset.prod_congr rfl (fun i _ => hprob (ω i))]
  by_cases hs : ∀ i, (N / r) ∣ (ω i).val
  · rw [if_pos hs, Finset.prod_congr rfl (fun i _ => if_pos (hs i)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hs]
    obtain ⟨i, hi⟩ := not_forall.mp hs
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Events that agree on all supported cyclic record sequences have equal probabilities under
the exact collision promise. -/
theorem cyclicSampleDist_probEvent_congr (N r : ℕ) (hN : 0 < N) (f : Fin N → R)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r)
    (m : ℕ) (E₁ E₂ : (Fin m → Fin N) → Prop) [DecidablePred E₁] [DecidablePred E₂]
    (h : ∀ ω : Fin m → Fin N, (∀ i, (N / r) ∣ (ω i).val) → (E₁ ω ↔ E₂ ω)) :
    (cyclicSampleDist N hN f).probEvent E₁ =
      (cyclicSampleDist N hN f).probEvent E₂ := by
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [Finset.sum_congr rfl (fun ω _ => cyclicSampleDist_probOf N r hN f hr hrdvd hcol m ω)]
  symm
  rw [Finset.sum_congr rfl (fun ω _ => cyclicSampleDist_probOf N r hN f hr hrdvd hcol m ω)]
  symm
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun ω _ => rfl)
  rw [Finset.filter_filter, Finset.filter_filter]
  apply Finset.filter_congr
  intro ω _
  constructor
  · rintro ⟨hE, hsupp⟩
    exact ⟨(h ω hsupp).mp hE, hsupp⟩
  · rintro ⟨hE, hsupp⟩
    exact ⟨(h ω hsupp).mpr hE, hsupp⟩

/-- Under the exact cyclic collision promise, the probability that gcd decoding of `m` fresh
records fails to return `r` is at most `r / 2 ^ m`. -/
theorem cyclic_gcd_failure_probability (N r m : ℕ) (hN : 0 < N) (f : Fin N → R)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) :
    (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
      cyclicPeriodDecode N ω ≠ r) ≤ (r : ℝ) / (2 ^ m : ℝ) := by
  have hqpos : 0 < N / r := Nat.div_pos (Nat.le_of_dvd hN hrdvd) hr
  have hrq : r * (N / r) = N := Nat.mul_div_cancel' hrdvd

  set S := Finset.univ.filter (fun ω : Fin m → Fin N =>
    cyclicPeriodDecode N ω ≠ r ∧ (∀ i, (N / r) ∣ (ω i).val)) with hS
  have hmass : (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicPeriodDecode N ω ≠ r) = (S.card : ℝ) * (1 / (r : ℝ)) ^ m := by
    show (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin N => cyclicPeriodDecode N ω ≠ r),
        (cyclicSampleDist N hN f).probOf ω) = _
    rw [Finset.sum_congr rfl (fun ω _ => cyclicSampleDist_probOf N r hN f hr hrdvd hcol m ω)]
    rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]

  set Φ : (Fin m → Fin N) → (Fin m → Fin r) := fun ω i =>
    ⟨((ω i).val / (N / r)) % r, Nat.mod_lt _ hr⟩ with hΦ
  have hΦval : ∀ (ω : Fin m → Fin N), (∀ i, (N / r) ∣ (ω i).val) → ∀ i,
      (Φ ω i).val = (ω i).val / (N / r) := by
    intro ω hω i
    show ((ω i).val / (N / r)) % r = (ω i).val / (N / r)
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul hqpos, hrq]
    exact (ω i).isLt

  have hmap : Set.MapsTo Φ S
      ((Nat.primeFactors r).biUnion (fun ℓ => Finset.univ.filter
        (fun k : Fin m → Fin r => ∀ i, ℓ ∣ (k i).val))) := by
    intro ω hω
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hω
    obtain ⟨-, hne, hsupp⟩ := hω
    have hiff := (cyclic_decoder_supported_divisor_and_cost N r m ω hN hr hrdvd hsupp).2.2.2
    have hg1 : (List.ofFn (fun i => (ω i).val / (N / r))).foldl Nat.gcd r ≠ 1 :=
      fun h => hne (hiff.mpr h)
    obtain ⟨ℓ, hℓp, hℓg⟩ := Nat.exists_prime_and_dvd hg1
    have hℓr : ℓ ∣ r := hℓg.trans (foldl_gcd_dvd_left r _)
    have hℓmem : ℓ ∈ Nat.primeFactors r := by
      rw [Nat.mem_primeFactors]
      exact ⟨hℓp, hℓr, hr.ne'⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨ℓ, hℓmem, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_⟩⟩
    rw [hΦval ω hsupp i]
    exact hℓg.trans (foldl_gcd_dvd_of_mem r _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hinj : Set.InjOn Φ S := by
    intro ω₁ h₁ ω₂ h₂ h
    rw [Finset.mem_coe, hS, Finset.mem_filter] at h₁ h₂
    obtain ⟨-, -, hsupp₁⟩ := h₁
    obtain ⟨-, -, hsupp₂⟩ := h₂
    funext i
    apply Fin.ext
    have hi := congrArg Fin.val (congrFun h i)
    rw [hΦval ω₁ hsupp₁ i, hΦval ω₂ hsupp₂ i] at hi
    have e1 := Nat.div_mul_cancel (hsupp₁ i)
    have e2 := Nat.div_mul_cancel (hsupp₂ i)
    calc (ω₁ i).val = (ω₁ i).val / (N / r) * (N / r) := e1.symm
      _ = (ω₂ i).val / (N / r) * (N / r) := by rw [hi]
      _ = (ω₂ i).val := e2

  have hB : ∀ ℓ ∈ Nat.primeFactors r, (Finset.univ.filter (fun k : Fin m → Fin r =>
      ∀ i, ℓ ∣ (k i).val)).card ≤ (r / ℓ) ^ m := by
    intro ℓ hℓ
    rw [Nat.mem_primeFactors] at hℓ
    obtain ⟨hℓp, hℓr, -⟩ := hℓ
    have hℓpos : 0 < ℓ := hℓp.pos
    have hℓq : ℓ * (r / ℓ) = r := Nat.mul_div_cancel' hℓr
    have hrl : 0 < r / ℓ := Nat.div_pos (Nat.le_of_dvd hr hℓr) hℓpos
    set Ψ : (Fin m → Fin r) → (Fin m → Fin (r / ℓ)) := fun k i =>
      ⟨((k i).val / ℓ) % (r / ℓ), Nat.mod_lt _ hrl⟩ with hΨ
    have hΨval : ∀ (k : Fin m → Fin r), (∀ i, ℓ ∣ (k i).val) → ∀ i,
        (Ψ k i).val = (k i).val / ℓ := by
      intro k hk i
      show ((k i).val / ℓ) % (r / ℓ) = (k i).val / ℓ
      apply Nat.mod_eq_of_lt
      rw [Nat.div_lt_iff_lt_mul hℓpos]
      calc (k i).val < r := (k i).isLt
        _ = ℓ * (r / ℓ) := hℓq.symm
        _ = (r / ℓ) * ℓ := Nat.mul_comm _ _
    calc (Finset.univ.filter (fun k : Fin m → Fin r => ∀ i, ℓ ∣ (k i).val)).card
        ≤ (Finset.univ : Finset (Fin m → Fin (r / ℓ))).card := by
          apply Finset.card_le_card_of_injOn Ψ
          · intro k hk
            exact Finset.mem_univ _
          · intro k₁ h₁ k₂ h₂ h
            rw [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
            funext i
            apply Fin.ext
            have hi := congrArg Fin.val (congrFun h i)
            rw [hΨval k₁ h₁.2 i, hΨval k₂ h₂.2 i] at hi
            have e1 := Nat.div_mul_cancel (h₁.2 i)
            have e2 := Nat.div_mul_cancel (h₂.2 i)
            calc (k₁ i).val = (k₁ i).val / ℓ * ℓ := e1.symm
              _ = (k₂ i).val / ℓ * ℓ := by rw [hi]
              _ = (k₂ i).val := e2
      _ = (r / ℓ) ^ m := by
          rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, Fintype.card_fin]
  have hcardU : S.card ≤ ∑ ℓ ∈ Nat.primeFactors r, (r / ℓ) ^ m :=
    (Finset.card_le_card_of_injOn Φ hmap hinj).trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ hℓ => hB ℓ hℓ))
  have hPF : (Nat.primeFactors r).card ≤ r := by
    have hsub : Nat.primeFactors r ⊆ Finset.Icc 2 r := by
      intro ℓ hℓ
      rw [Nat.mem_primeFactors] at hℓ
      rw [Finset.mem_Icc]
      exact ⟨hℓ.1.two_le, Nat.le_of_dvd hr hℓ.2.1⟩
    calc (Nat.primeFactors r).card ≤ (Finset.Icc 2 r).card := Finset.card_le_card hsub
      _ = r + 1 - 2 := Nat.card_Icc 2 r
      _ ≤ r := by omega
  rw [hmass]
  have hcm : (0 : ℝ) ≤ (1 / (r : ℝ)) ^ m := by positivity
  calc (S.card : ℝ) * (1 / (r : ℝ)) ^ m
      ≤ (∑ ℓ ∈ Nat.primeFactors r, ((r / ℓ : ℕ) : ℝ) ^ m) * (1 / (r : ℝ)) ^ m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcardU) hcm
    _ = ∑ ℓ ∈ Nat.primeFactors r, (1 / (ℓ : ℝ)) ^ m := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Nat.mem_primeFactors] at hℓ
        obtain ⟨hℓp, hℓr, -⟩ := hℓ
        have hℓ0 : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓp.pos.ne'
        have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
        rw [← mul_pow, Nat.cast_div hℓr hℓ0]
        field_simp
    _ ≤ ∑ ℓ ∈ Nat.primeFactors r, (1 / (2 : ℝ)) ^ m := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [Nat.mem_primeFactors] at hℓ
        apply pow_le_pow_left₀ (by positivity)
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        exact_mod_cast hℓ.1.two_le
    _ = (Nat.primeFactors r).card * (1 / (2 : ℝ)) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * (1 / (2 : ℝ)) ^ m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hPF) (by positivity)
    _ = (r : ℝ) / (2 ^ m : ℝ) := by
        rw [div_pow, one_pow, mul_one_div]

/-- Under the exact cyclic collision promise, verified recovery succeeds with probability at
least `1 - r / 2 ^ m` and returns an incorrect period with probability zero. -/
theorem cyclic_verified_recovery_probability (N r m : ℕ) (hN : 0 < N) (f : Fin N → R)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) :
    (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicVerifiedDecode N hN f ω = some r) ≥ 1 - (r : ℝ) / (2 ^ m : ℝ) ∧
    (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        ∃ p, p ≠ r ∧ cyclicVerifiedDecode N hN f ω = some p) = 0 := by
  classical
  have hprobOf := cyclicSampleDist_probOf N r hN f hr hrdvd hcol m
  have hEvEd : (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicVerifiedDecode N hN f ω = some r)
      = (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicPeriodDecode N ω = r) :=
    cyclicSampleDist_probEvent_congr N r hN f hr hrdvd hcol m _ _ fun ω hsupp =>
      (cyclic_candidate_actual_two_query_verification N r m hN f ω hr hrdvd hcol hsupp).1
  have htotal : (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicPeriodDecode N ω = r)
      + (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicPeriodDecode N ω ≠ r) = 1 := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [← (cyclicSampleDist N hN f).sum_probOf m]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hG6 := cyclic_gcd_failure_probability N r m hN f hr hrdvd hcol
  constructor
  · rw [hEvEd]
    linarith [htotal, hG6]
  · show ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin N =>
        ∃ p, p ≠ r ∧ cyclicVerifiedDecode N hN f ω = some p),
        (cyclicSampleDist N hN f).probOf ω = 0
    apply Finset.sum_eq_zero
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨p, hpr, hvp⟩ := hω.2
    rw [hprobOf ω]
    by_cases hsupp : ∀ i, (N / r) ∣ (ω i).val
    · exfalso
      exact hpr ((cyclic_candidate_actual_two_query_verification N r m hN f ω hr hrdvd hcol
        hsupp).2.1 p hvp)
    · rw [if_neg hsupp]

/-- With `m = Nat.log2 N + 1 + k`, verified recovery has success probability at least `1 - 2 ^
(-k)`, uses `m + 2` queries including verification and `2 * m` sampling gate macros, and has
Euclidean count at most `m * (N + 1)`. -/
theorem cyclic_accessible_budget_and_three_costs (N r k : ℕ) (hN : 0 < N) (f : Fin N → R)
    (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) :
    let m := Nat.log2 N + 1 + k
    (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
        cyclicVerifiedDecode N hN f ω = some r) ≥ 1 - (2 : ℝ) ^ (-(k : ℤ)) ∧
    ((List.replicate m (cyclicSamplingCircuit (R := R) N)).map QueryCount).sum + 2 = m + 2 ∧
    ((List.replicate m (cyclicSamplingCircuit (R := R) N)).map GateCount).sum = 2 * m ∧
    (∀ ω : Fin m → Fin N,
      (cyclicGcdCounted N (List.ofFn (fun i => (ω i).val))).2 ≤ m * (N + 1)) := by
  intro m
  have hm : m = Nat.log2 N + 1 + k := rfl
  have hrN : r ≤ N := Nat.le_of_dvd hN hrdvd
  have hNlt : N < 2 ^ (Nat.log2 N + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hreal : (r : ℝ) / (2 ^ m : ℝ) ≤ (2 : ℝ) ^ (-(k : ℤ)) := by
    have h1 : (r : ℝ) ≤ N := by exact_mod_cast hrN
    have h2 : (N : ℝ) < 2 ^ (Nat.log2 N + 1 : ℕ) := by exact_mod_cast hNlt
    have h3 : (2 : ℝ) ^ m = 2 ^ (Nat.log2 N + 1) * 2 ^ k := by rw [hm, pow_add]
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    have h6 : (2 : ℝ) ^ (-(k : ℤ)) * (2 ^ (Nat.log2 N + 1) * 2 ^ k) =
        2 ^ (Nat.log2 N + 1) := by
      rw [show (2 : ℝ) ^ (-(k : ℤ)) = (2 ^ k)⁻¹ from by rw [zpow_neg, zpow_natCast]]
      calc ((2 : ℝ) ^ k)⁻¹ * (2 ^ (Nat.log2 N + 1) * 2 ^ k)
          = 2 ^ (Nat.log2 N + 1) * ((2 : ℝ) ^ k)⁻¹ * 2 ^ k := by ring
        _ = 2 ^ (Nat.log2 N + 1) := by rw [mul_assoc, inv_mul_cancel₀ h2k, mul_one]
    rw [h3, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (Nat.log2 N + 1) * 2 ^ k), h6]
    linarith
  have hG7 := cyclic_verified_recovery_probability N r m hN f hr hrdvd hcol
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (1 : ℝ) - 2 ^ (-(k : ℤ)) ≤ 1 - r / (2 ^ m : ℝ) := by linarith [hreal]
      _ ≤ (cyclicSampleDist N hN f).probEvent (fun ω : Fin m → Fin N =>
          cyclicVerifiedDecode N hN f ω = some r) := hG7.1
  · rw [List.map_replicate, List.sum_replicate]
    show m * QueryCount (cyclicSamplingCircuit (R := R) N) + 2 = m + 2
    rw [show QueryCount (cyclicSamplingCircuit (R := R) N) = 1 from rfl,
      Nat.mul_one]
  · rw [List.map_replicate, List.sum_replicate]
    show m * GateCount (cyclicSamplingCircuit (R := R) N) = 2 * m
    rw [show GateCount (cyclicSamplingCircuit (R := R) N) = 2 from rfl,
      Nat.mul_comm]
  · intro ω
    have h2 := (cyclic_counted_euclidean_gcd N (List.ofFn fun i => (ω i).val)).2
      (fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        exact le_of_lt (ω i).isLt)
    rwa [List.length_ofFn] at h2

/-- For `m = Nat.log2 N + 1 + k`, counted recovery succeeds within query budget `m + 2` with
probability at least `1 - 2 ^ (-k)`. Also gives the sampling gate and Euclidean-step bounds
and identifies its exact costed output law [CheungMosca2001]. -/
theorem cyclic_accessible_budget_and_measurements (N r k : ℕ) (hN : 0 < N)
    (f : Fin N → R) (hr : 0 < r) (hrdvd : r ∣ N)
    (hcol : ∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) :
    let m := Nat.log2 N + 1 + k
    ENNReal.ofReal (1 - (2 : ℝ) ^ (-(k : ℤ))) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.within (cyclicCountedRecovery N hN f m) (m + 2) (fun out => out = some r) ∧
    ((List.replicate m (cyclicSamplingCircuit (R := R) N)).map QueryCount).sum + 2 = m + 2 ∧
    ((List.replicate m (cyclicSamplingCircuit (R := R) N)).map GateCount).sum = 2 * m ∧
    (∀ ω : Fin m → Fin N,
      (cyclicGcdCounted N (List.ofFn (fun i => (ω i).val))).2 ≤ m * (N + 1)) ∧
    cyclicCountedRecovery N hN f m = (cyclicFreshSamples N hN f m).map
      (fun ω => (cyclicVerifiedDecode N hN f ω, m + 2)) := by
  intro m
  obtain ⟨hprob, hquery, hgate, hmod⟩ :=
    cyclic_accessible_budget_and_three_costs N r k hN f hr hrdvd hcol
  refine ⟨?_, hquery, hgate, hmod, cyclicCountedRecovery_eq N hN f m⟩
  rw [cyclicCountedRecovery_within]
  exact ENNReal.ofReal_le_ofReal hprob

end Qatlib.Concepts.HspRecovery.CyclicRecovery
