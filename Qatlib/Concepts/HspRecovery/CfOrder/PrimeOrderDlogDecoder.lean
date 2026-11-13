/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CfOrder.PrimeOrderDlogSampling

/-!
# Verified discrete logarithm decoding at prime order

Defines `primeDlogDecode`, which reads records until their first coordinate is nonzero, and
verifies the resulting quotient by counted repeated group addition. The verified decoder records
the number of records read and additions performed.

For independent records from the cyclic discrete logarithm sampling law, recovery succeeds with
probability `1 - (1 / p) ^ m`. This specializes the discrete logarithm postprocessing of
[Shor1997] to prime order.

## Main statements

* `prime_dlog_executable_first_nonzero_decoder`: proves the first-nonzero decoding rule and read
  bound.
* `prime_dlog_actual_verification_and_read_ledger`: gives verification correctness and operation
  counts.
* `prime_dlog_fresh_actual_verified_success`: computes the exact success probability.

## References

* [Shor, 1997][Shor1997]
-/

set_option autoImplicit false

open Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.CfOrder

open Matrix
open scoped Classical

variable {p : ℕ}

/-- Scans for the first record with nonzero first coordinate, returns the quotient of its second
coordinate by its first, and counts records read. -/
def primeDlogDecode {p : ℕ} [Fact p.Prime] : List (ZMod p × ZMod p) → Option (ZMod p) × ℕ
  | [] => (none, 0)
  | z :: zs =>
      if z.1 = 0 then
        let r := primeDlogDecode zs
        (r.1, r.2 + 1)
      else
        (some (z.2 / z.1), 1)

/-- The number of records read by `primeDlogDecode` is at most the input list length. -/
private theorem primeDlogDecode_reads {p : ℕ} [Fact p.Prime] :
    ∀ (xs : List (ZMod p × ZMod p)), (primeDlogDecode xs).2 ≤ xs.length
  | [] => Nat.le_refl 0
  | z :: zs => by
    by_cases hz : z.1 = 0
    · have h1 : (primeDlogDecode (z :: zs)).2 = (primeDlogDecode zs).2 + 1 := by
        simp [primeDlogDecode, hz]
      have h2 := primeDlogDecode_reads zs
      simp only [List.length_cons]
      omega
    · have h1 : (primeDlogDecode (z :: zs)).2 = 1 := by
        simp [primeDlogDecode, hz]
      simp only [List.length_cons, h1]
      omega

/-- The prime-order decoder returns no result exactly when every record has zero first
coordinate. -/
private theorem primeDlogDecode_eq_none_iff {p : ℕ} [Fact p.Prime] :
    ∀ (xs : List (ZMod p × ZMod p)),
      (primeDlogDecode xs).1 = none ↔ ∀ z ∈ xs, z.1 = 0
  | [] => by simp [primeDlogDecode]
  | z :: zs => by
    by_cases hz : z.1 = 0
    · have h1 : (primeDlogDecode (z :: zs)).1 = (primeDlogDecode zs).1 := by
        simp [primeDlogDecode, hz]
      rw [h1, primeDlogDecode_eq_none_iff zs]
      constructor
      · intro hall2 w2 hw2
        rcases List.mem_cons.mp hw2 with hzz2 | hws2
        · subst w2
          exact hz
        · exact hall2 w2 hws2
      · intro hall w1 hw1
        exact hall w1 (List.mem_cons_of_mem z hw1)
    · have h1 : (primeDlogDecode (z :: zs)).1 = some (z.2 / z.1) := by
        simp [primeDlogDecode, hz]
      rw [h1]
      constructor
      · intro hcon
        simp at hcon
      · intro hall
        exact absurd (hall z (by simp)) hz

/-- Over `ZMod p` for prime `p`, a record on `b = d * a` with `a ≠ 0` satisfies `b / a = d`. -/
private theorem primeDlog_quotient {p : ℕ} [Fact p.Prime] (d a b : ZMod p)
    (ha : a ≠ 0) (h : b = d * a) : b / a = d := by
  rw [h, div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ ha, mul_one]

/-- If every record lies on `b = d * a` and some first coordinate is nonzero, the decoder
returns `d`. -/
private theorem primeDlogDecode_eq_some_of {p : ℕ} [Fact p.Prime] (d : ZMod p) :
    ∀ (xs : List (ZMod p × ZMod p)), (∀ z ∈ xs, z.2 = d * z.1) →
      (∃ z ∈ xs, z.1 ≠ 0) → (primeDlogDecode xs).1 = some d
  | [], _, hex => by
    obtain ⟨w, hw, _⟩ := hex
    simp at hw
  | z :: zs, hon, hex => by
    by_cases hz : z.1 = 0
    · have h1 : (primeDlogDecode (z :: zs)).1 = (primeDlogDecode zs).1 := by
        simp [primeDlogDecode, hz]
      have hex' : ∃ w ∈ zs, w.1 ≠ 0 := by
        rcases hex with ⟨w, hw, hne⟩
        rcases List.mem_cons.mp hw with hzz | hws
        · subst w
          exact absurd hz hne
        · exact ⟨w, hws, hne⟩
      have hon' : ∀ w ∈ zs, w.2 = d * w.1 := by
        intro w hw
        exact hon w (List.mem_cons_of_mem z hw)
      rw [h1]
      exact primeDlogDecode_eq_some_of d zs hon' hex'
    · have h1 : (primeDlogDecode (z :: zs)).1 = some (z.2 / z.1) := by
        simp [primeDlogDecode, hz]
      have hbz : z.2 = d * z.1 := hon z (by simp)
      rw [h1, primeDlog_quotient d z.1 z.2 hz hbz]

/-- Adds `g` to an accumulator a specified number of times and returns the resulting group
element with its addition count. -/
def primeDlogRepeatAdd {C : Type} [AddCommGroup C] (g : C) : ℕ → C → C × ℕ
  | 0, acc => (acc, 0)
  | n + 1, acc =>
      let r := primeDlogRepeatAdd g n (acc + g)
      (r.1, r.2 + 1)

/-- Repeated addition of `g` for `n` steps records exactly `n` additions. -/
private theorem primeDlogRepeatAdd_reads {C : Type} [AddCommGroup C] (g : C) :
    ∀ (n : ℕ) (acc : C), (primeDlogRepeatAdd g n acc).2 = n := by
  intro n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    simp only [primeDlogRepeatAdd, ih]

/-- The value returned after `n` repeated additions is `acc + n • g`. -/
private theorem primeDlogRepeatAdd_value {C : Type} [AddCommGroup C] (g : C) :
    ∀ (n : ℕ) (acc : C), (primeDlogRepeatAdd g n acc).1 = acc + n • g := by
  intro n
  induction n with
  | zero => intro acc; simp [primeDlogRepeatAdd]
  | succ n ih =>
    intro acc
    simp only [primeDlogRepeatAdd, ih]
    rw [add_assoc, succ_nsmul]
    abel

/-- Checks `d.val • g = h` by repeated addition and returns the Boolean result together with the
addition count. -/
def primeDlogVerify {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C] [DecidableEq C]
    (g h : C) (d : ZMod p) : Bool × ℕ :=
  let r := primeDlogRepeatAdd g d.val 0
  (decide (r.1 = h), r.2)

/-- Verifying the candidate `d` uses exactly `d.val` additions. -/
private theorem primeDlogVerify_reads {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    [DecidableEq C] (g h : C) (d : ZMod p) : (primeDlogVerify g h d).2 = d.val := by
  simp only [primeDlogVerify]
  rw [primeDlogRepeatAdd_reads]

/-- The candidate verifier returns true exactly when `d.val • g = h`. -/
private theorem primeDlogVerify_bool {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    [DecidableEq C] (g h : C) (d : ZMod p) :
    (primeDlogVerify g h d).1 = true ↔ d.val • g = h := by
  simp only [primeDlogVerify, primeDlogRepeatAdd_value, decide_eq_true_eq, zero_add]

/-- Decodes the first usable record, verifies its candidate, and returns an optional logarithm
with record-read and group-addition counts. -/
def primeDlogVerified {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    [DecidableEq C] (g h : C) (xs : List (ZMod p × ZMod p)) :
    Option (ZMod p) × (ℕ × ℕ) :=
  let dec := primeDlogDecode xs
  match dec.1 with
  | none => (none, (dec.2, 0))
  | some d =>
      let v := primeDlogVerify g h d
      (if v.1 then some d else none, (dec.2, v.2))

/-- A decoded candidate that passes verification is returned by the verified decoder. -/
private theorem primeDlogVerified_of_ok {p : ℕ} [Fact p.Prime] {C : Type}
    [AddCommGroup C] [DecidableEq C] (g h : C) (xs : List (ZMod p × ZMod p)) (d : ZMod p)
    (hd : (primeDlogDecode xs).1 = some d) (hv : (primeDlogVerify g h d).1 = true) :
    (primeDlogVerified g h xs).1 = some d := by
  simp only [primeDlogVerified, hd]
  rw [hv]
  rfl

/-- The verified decoder reads at most the input list length. -/
private theorem primeDlogVerified_reads {p : ℕ} [Fact p.Prime] {C : Type}
    [AddCommGroup C] [DecidableEq C] (g h : C) (xs : List (ZMod p × ZMod p)) :
    (primeDlogVerified g h xs).2.1 ≤ xs.length := by
  have h := primeDlogDecode_reads xs
  cases hd : (primeDlogDecode xs).1 with
  | none => simp only [primeDlogVerified, hd]; exact h
  | some d => simp only [primeDlogVerified, hd]; exact h

/-- The verified decoder performs fewer than `p` group additions. -/
private theorem primeDlogVerified_adds_lt {p : ℕ} [Fact p.Prime] {C : Type}
    [AddCommGroup C] [DecidableEq C] (g h : C) (xs : List (ZMod p × ZMod p)) :
    (primeDlogVerified g h xs).2.2 < p := by
  have hp : 0 < p := by
    have h : Nat.Prime p := Fact.out
    exact h.pos
  cases hd : (primeDlogDecode xs).1 with
  | none => simp only [primeDlogVerified, hd]; omega
  | some d =>
    simp only [primeDlogVerified, hd]
    rw [primeDlogVerify_reads]
    exact ZMod.val_lt d

/-- The product of indicators that every record is `(0, 0)` is the indicator that the entire
record function is constantly `(0, 0)`. -/
private theorem prod_omega0 (m : ℕ) (ω : Fin m → ZMod p × ZMod p) :
    (∏ i : Fin m, (if ω i = (0, 0) then (1 : ℝ) else 0)) =
      if ω = fun _ => (0, 0) then (1 : ℝ) else (0 : ℝ) := by
  by_cases hall : ∀ i, ω i = (0, 0)
  · have he : ω = (fun _ => (0, 0)) := by
      funext i
      exact hall i
    rw [he]
    simp
  · have hex : ∃ i, ω i ≠ (0, 0) := by
      by_contra hcon
      exact hall (fun i => Classical.byContradiction (fun h => hcon ⟨i, h⟩))
    obtain ⟨j, hj⟩ := hex
    have hzj : (if ω j = (0, 0) then (1 : ℝ) else 0) = 0 := by rw [ite_eq_right hj]
    have hz : (∏ i : Fin m, (if ω i = (0, 0) then (1 : ℝ) else 0)) = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hzj]
    have hne : ¬(ω = (fun _ : Fin m => (0, 0))) :=
      fun he => hall (fun i => by rw [he])
    rw [hz]
    simp [hne]

/-- Weighting the record probabilities by the indicator of `(0, 0)` and summing gives the
probability of `(0, 0)`. -/
private theorem sum_zero_omega0 {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    [Fintype C] [DecidableEq C] (g h : C) :
    (∑ x : ZMod p × ZMod p, (primeDlogRecordDist p g h).prob x * (if x = (0, 0) then 1 else 0))
      = (primeDlogRecordDist p g h).prob (0, 0) := by
  have h2 : (∑ x : ZMod p × ZMod p,
      (if x = (0, 0) then (primeDlogRecordDist p g h).prob (0, 0) else 0))
      = (primeDlogRecordDist p g h).prob (0, 0) := by
    rw [Finset.sum_ite_eq']
    simp
  calc
    (∑ x : ZMod p × ZMod p, (primeDlogRecordDist p g h).prob x * (if x = (0, 0) then 1 else 0))
      = ∑ x : ZMod p × ZMod p,
          (if x = (0, 0) then (primeDlogRecordDist p g h).prob (0, 0) else 0) := by
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x = (0, 0) <;> simp [hx]
    _ = _ := h2

/-- The probabilities of all length-`m` independent prime-order discrete logarithm record
sequences sum to one. -/
private theorem probEvent_total {p : ℕ} [Fact p.Prime] {C : Type} [AddCommGroup C]
    [Fintype C] [DecidableEq C] (g h : C) (m : ℕ) :
    (∑ ω : Fin m → ZMod p × ZMod p, (primeDlogRecordDist p g h).probOf ω) = 1 := by
  calc
    (∑ ω : Fin m → ZMod p × ZMod p, (primeDlogRecordDist p g h).probOf ω)
      = ∑ ω : Fin m → ZMod p × ZMod p,
          (primeDlogRecordDist p g h).probOf ω * (∏ _k : Fin m, (1 : ℝ)) := by
            congr 1
            funext ω
            simp
      _ = ∏ _k : Fin m, ∑ x, (primeDlogRecordDist p g h).prob x * 1 :=
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod (primeDlogRecordDist p g h) (fun _ _ => (1 : ℝ))
      _ = 1 := by
        simp only [Finset.prod_const, mul_one, Finset.card_univ, Fintype.card_fin]
        rw [(primeDlogRecordDist p g h).sum_one, one_pow]

end Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.CfOrder

open Matrix
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open scoped Classical

/-- For records on `b = d * a`, the decoder reads at most the list length, fails exactly when
all first coordinates vanish, and returns `d` whenever a nonzero first coordinate occurs
[Shor1997]. -/
theorem prime_dlog_executable_first_nonzero_decoder (p : ℕ) [Fact p.Prime] (d : ZMod p)
    (xs : List (ZMod p × ZMod p)) (hon : ∀ z ∈ xs, z.2 = d * z.1) :
    (primeDlogDecode xs).2 ≤ xs.length ∧
      ((primeDlogDecode xs).1 = none ↔ ∀ z ∈ xs, z.1 = 0) ∧
      ((∃ z ∈ xs, z.1 ≠ 0) → (primeDlogDecode xs).1 = some d) :=
  ⟨primeDlogDecode_reads xs, primeDlogDecode_eq_none_iff xs,
    primeDlogDecode_eq_some_of d xs hon⟩

/-- Verification tests `d.val • g = h` using exactly `d.val` additions, while verified decoding
reads at most the input length and uses fewer than `p` additions. -/
theorem prime_dlog_actual_verification_and_read_ledger (p : ℕ) [Fact p.Prime] (C : Type)
    [AddCommGroup C] [DecidableEq C] (g h : C) (d : ZMod p)
    (xs : List (ZMod p × ZMod p)) :
    (primeDlogVerify g h d).2 = d.val ∧
      ((primeDlogVerify g h d).1 = true ↔ d.val • g = h) ∧
      (primeDlogVerified g h xs).2.1 ≤ xs.length ∧
        (primeDlogVerified g h xs).2.2 < p :=
  ⟨primeDlogVerify_reads g h d, primeDlogVerify_bool g h d,
    primeDlogVerified_reads g h xs, primeDlogVerified_adds_lt g h xs⟩

/-- Under the cyclic oracle hypotheses, verified decoding of `m` independent records returns the
logarithm with exact probability `1 - (1 / p) ^ m` [Shor1997]. -/
theorem prime_dlog_fresh_actual_verified_success (p : ℕ) [Fact p.Prime] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod p) (m : ℕ)
    (hp : (p : ℕ) • g = 0) (hinj : Function.Injective (fun a : ZMod p => a.val • g))
    (hh : h = d.val • g) :
    (primeDlogRecordDist p g h).probEvent
        (fun ω : Fin m → ZMod p × ZMod p =>
          (primeDlogVerified g h (List.ofFn ω)).1 = some d) = 1 - (1 / (p : ℝ)) ^ m := by
  set P := primeDlogRecordDist p g h with hP
  set E := (fun ω : Fin m → ZMod p × ZMod p => (primeDlogVerified g h (List.ofFn ω)).1 = some d)
    with hE
  have hz : ∀ ω : (Fin m → ZMod p × ZMod p),
      (¬ ((primeDlogVerified g h (List.ofFn ω)).1 = some d)) →
        ω = (fun _ => (0, 0)) ∨ P.probOf ω = 0 := by
    intro ω hnot
    by_cases hne : ω = (fun _ => (0, 0))
    · exact Or.inl hne
    · right
      have hex : ∃ j, ω j ≠ (0, 0) := by
        by_contra hcon
        exact hne (funext fun i => Classical.byContradiction (fun h => hcon ⟨i, h⟩))
      obtain ⟨j, hj⟩ := hex
      by_cases honl : ∀ i, (ω i).2 = d * (ω i).1
      · have hj1 : (ω j).1 ≠ 0 := by
          intro hz0
          have hb : (ω j).2 = 0 := by rw [honl j, hz0, mul_zero]
          have : ω j = (0, 0) := Prod.ext hz0 hb
          exact hj this
        have hon : ∀ z ∈ List.ofFn ω, z.2 = d * z.1 := by
          intro z hz2
          obtain ⟨i, -, rfl⟩ := List.mem_ofFn.mp hz2
          exact honl i
        have hex2 : ∃ z ∈ List.ofFn ω, z.1 ≠ 0 := by
          refine ⟨ω j, List.mem_ofFn.mpr ⟨j, rfl⟩, hj1⟩
        have hdec : (primeDlogDecode (List.ofFn ω)).1 = some d :=
          primeDlogDecode_eq_some_of d _ hon hex2
        have hvb : (primeDlogVerify g h d).1 = true := by
          rw [primeDlogVerify_bool]
          exact hh.symm
        have hout : (primeDlogVerified g h (List.ofFn ω)).1 = some d :=
          primeDlogVerified_of_ok g h _ d hdec hvb
        exact absurd hout hnot
      · have hexl : ∃ i, (ω i).2 ≠ d * (ω i).1 := by
          by_contra hcon
          exact honl (fun i => Classical.byContradiction (fun h => hcon ⟨i, h⟩))
        obtain ⟨i, hi⟩ := hexl
        have hpi : P.prob (ω i) = 0 := by
          have hg := prime_dlog_actual_fourier_line_law p C g h d hp hinj hh (ω i).1 (ω i).2
          rw [← hP] at hg
          by_cases hz3 : (ω i).2 = d * (ω i).1
          · exact absurd hz3 hi
          · rw [hg, ite_eq_right hz3]
        have hz2 : (∏ j : Fin m, P.prob (ω j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hpi
        rwa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
  have hEapp (ω : Fin m → ZMod p × ZMod p) :
      E ω = ((primeDlogVerified g h (List.ofFn ω)).1 = some d) := congrFun hE ω
  have hEnot (ω : Fin m → ZMod p × ZMod p) (hnot : ¬E ω) :
      ¬ ((primeDlogVerified g h (List.ofFn ω)).1 = some d) := by
    intro hc
    exact hnot ((hEapp ω).symm ▸ hc)
  have hEω0 : ¬ E (fun _ : Fin m => (0 : ZMod p × ZMod p)) := by
    have hz2 : (primeDlogDecode
        (List.ofFn (fun _ : Fin m => (0 : ZMod p × ZMod p)))).1 = none := by
      rw [primeDlogDecode_eq_none_iff]
      intro z hz4
      obtain ⟨i, -, rfl⟩ := List.mem_ofFn.mp hz4
      rfl
    have hz3 : (primeDlogVerified g h
        (List.ofFn (fun _ : Fin m => (0 : ZMod p × ZMod p)))).1 = none := by
      rw [primeDlogVerified, hz2]
    exact hEnot (fun _ : Fin m => (0 : ZMod p × ZMod p)) (fun hc => by
      have h4 : (primeDlogVerified g h
          (List.ofFn (fun _ : Fin m => (0 : ZMod p × ZMod p)))).1 = some d :=
        (hEapp _).symm ▸ hc
      rw [hz3] at h4
      cases h4)
  have hsplitω (ω : Fin m → ZMod p × ZMod p) :
      P.probOf ω * (if E ω then 0 else 1) =
        P.probOf ω * if ω = (fun _ : Fin m => (0 : ZMod p × ZMod p)) then 1 else 0 := by
    by_cases hω : E ω
    · have hne0 : ¬(ω = (fun _ : Fin m => (0 : ZMod p × ZMod p))) := by
        intro he
        exact (he ▸ hEω0) hω
      rw [ite_eq_left hω, mul_zero, ite_eq_right hne0, mul_zero]
    · rw [ite_eq_right hω, mul_one]
      rcases hz ω (hEnot ω hω) with hzero | hzero
      · rw [hzero, ite_eq_left, mul_one]
        rfl
      · rw [hzero, zero_mul]
  have hsplit : (∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω * if E ω then 0 else 1) =
      ∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω *
        if ω = fun _ => (0 : ZMod p × ZMod p) then 1 else 0 :=
    Finset.sum_congr rfl (fun ω _ => hsplitω ω)
  have hcompl : (∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω * if E ω then 0 else 1)
      = (1 / (p : ℝ)) ^ m := by
    calc
      (∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω * if E ω then 0 else 1)
        = ∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω *
            (∏ i : Fin m, (if ω i = (0, 0) then (1 : ℝ) else 0)) := by
          rw [hsplit]
          exact Finset.sum_congr rfl
            (fun ω _ => congrArg (fun z => P.probOf ω * z) (prod_omega0 m ω).symm)
      _ = ∏ _k : Fin m, ∑ x, P.prob x * (if x = (0, 0) then 1 else 0) :=
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod P (fun _ x => if x = (0, 0) then 1 else 0)
      _ = ∏ _k : Fin m, P.prob (0, 0) := by
          rw [Finset.prod_congr rfl (fun _ _ => sum_zero_omega0 g h)]
      _ = (1 / (p : ℝ)) ^ m := by
          have hg := prime_dlog_actual_fourier_line_law p C g h d hp hinj hh 0 0
          have : P.prob (0, 0) = 1 / (p : ℝ) := by
            show (primeDlogRecordDist p g h).prob (0, 0) = 1 / (p : ℝ)
            have hz : (0 : ZMod p) = (d : ZMod p) * 0 := by ring
            simp only [hg, ite_eq_left hz]
          rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    P.probEvent E = ∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω * (if E ω then 1 else 0) := by
      rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent]
      have h2 := Finset.sum_filter (s := (Finset.univ : Finset (Fin m → ZMod p × ZMod p)))
        E (fun ω => P.probOf ω)
      rw [h2]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : E ω <;> simp [hω]
    _ = (∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω) -
        (∑ ω : Fin m → ZMod p × ZMod p, P.probOf ω * (if E ω then 0 else 1)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : E ω <;> simp [hω]
    _ = 1 - (1 / (p : ℝ)) ^ m := by rw [probEvent_total g h m, hcompl]

/-- For the logarithm of two to the generator one in `ZMod 3`, two records recover two with
probability `8 / 9`; the list `[(0, 0), (1, 2)]` returns two with counts `(2, 2)`. -/
theorem prime_dlog_mod_three_actual_consumer :
    (primeDlogRecordDist 3 (1 : ZMod 3) 2).probEvent
        (fun ω : Fin 2 → (ZMod 3 × ZMod 3) =>
          (primeDlogVerified (1 : ZMod 3) 2 (List.ofFn ω)).1 = some 2) = 8 / 9 ∧
      (primeDlogVerified (1 : ZMod 3) 2 ([(0, 0), (1, 2)] : List (ZMod 3 × ZMod 3))).1 = some 2 ∧
      (primeDlogVerified (1 : ZMod 3) 2 ([(0, 0), (1, 2)] : List (ZMod 3 × ZMod 3))).2 = (2, 2) := by
  have hgen := prime_dlog_fresh_actual_verified_success 3 (ZMod 3) (1 : ZMod 3) 2 (2 : ZMod 3) 2
    (by
      have h : (3 : ℕ) • (1 : ZMod 3) = 3 := by norm_num
      rw [h]
      decide)
    (by
      intro a b hab
      have hab' : a = b := by
        simpa only [show a.val • (1 : ZMod 3) = a from by norm_num,
          show b.val • (1 : ZMod 3) = b from by norm_num] using! hab
      exact hab')
    rfl
  refine ⟨?_,
      by simp [primeDlogVerified, primeDlogDecode, primeDlogVerify]; decide, by simp [primeDlogVerified, primeDlogDecode, primeDlogVerify]; decide⟩
  rw [hgen]
  norm_num

end Qatlib.Concepts.HspRecovery.CfOrder
