/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.JointDlog.CompositeDlogConsumers
import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicGcdDecoder

/-!
# Joint discrete logarithm recovery by Bezout folding

`jointDlogFold` combines modular sample pairs using extended Euclidean coefficients while
counting sample reads and divisions. `jointDlogVerified` checks the resulting candidate by
counted binary scalar multiplication; the discrete logarithm setting is discussed in
[ProosZalka2003].

The fold preserves the common-line relation between sample coordinates. The verified decoder has
explicit logarithmic arithmetic bounds and, for independent samples from a valid cyclic discrete
logarithm instance, success probability at least `1 - r / 2^m`.

## Main statements

* `joint_dlog_fold_invariant_and_work`: the gcd invariant, line invariant, and work bounds.
* `joint_dlog_actual_verified_correctness_and_work`: output soundness, the gcd criterion for
  success on line samples, and counted work.
* `joint_dlog_fresh_actual_verified_success`: a lower bound for recovery from fresh samples.

## References

* [Proos and Zalka, 2003][ProosZalka2003]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
open scoped Classical BigOperators
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.CyclicRecovery

namespace Qatlib.Concepts.HspRecovery.JointDlog

/-- Folds modular sample pairs by extended Euclidean combination, returning the running gcd and
combined second coordinate together with sample-read and division counts. -/
def jointDlogFold {r : ℕ} [NeZero r] (xs : List (ZMod r × ZMod r)) :
    (ℕ × ZMod r) × (ℕ × ℕ) :=
  xs.foldl (fun acc z =>
    let e := cyclicDlogEuclid z.1.val 1 0 acc.1.1 0 1
    ((e.1.1, (e.1.2.1 : ZMod r)*z.2 + (e.1.2.2 : ZMod r)*acc.1.2),
      (acc.2.1+1,acc.2.2+e.2))) ((r,0),(0,0))

/-- Computes a scalar multiple by binary doubling and addition with a prescribed recursion fuel,
returning the value and the counted group additions. -/
def binaryAddFuel {C : Type} [AddCommGroup C] : C → ℕ → ℕ → C × ℕ
  | _, 0, _ => (0,0)
  | g, k+1, n =>
      if n = 0 then (0,0) else
        let v := binaryAddFuel (g+g) k (n/2)
        (if n%2=0 then v.1 else v.1+g, v.2+1+(if n%2=0 then 0 else 1))

/-- Runs counted binary scalar multiplication with `Nat.log 2 n + 1` units of fuel. -/
def binaryAddCounted {C : Type} [AddCommGroup C] (g : C) (n : ℕ) : C × ℕ :=
  binaryAddFuel g (Nat.log 2 n+1) n

/-- Returns the candidate from `jointDlogFold` only when its gcd is one and counted scalar
multiplication verifies the target, together with read, division, and addition counts. -/
def jointDlogVerified {r : ℕ} [NeZero r] {C : Type} [AddCommGroup C]
    [DecidableEq C] (g h : C) (xs : List (ZMod r × ZMod r)) :
    Option (ZMod r) × (ℕ × ℕ × ℕ) :=
  let dec := jointDlogFold xs
  if dec.1.1 = 1 then
    let v := binaryAddCounted g dec.1.2.val
    (if v.1 = h then some dec.1.2 else none,(dec.2.1,dec.2.2,v.2))
  else (none,(dec.2.1,dec.2.2,0))

end Qatlib.Concepts.HspRecovery.JointDlog
namespace Qatlib.Concepts.HspRecovery.JointDlog
open Qatlib.Concepts.HspRecovery.BackendAudit Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

/-- If `0 < a < n`, then twice the remainder of `n` modulo `a` is strictly less than `n`. -/
private theorem joint_euclid_two_step (n a : ℕ) (_hn : 0 < n) (ha : 0 < a) (han : a < n) :
    2*(n%a) < n := by
  have hmod := Nat.mod_lt n ha
  by_cases hsmall : 2*a ≤ n
  · omega
  · have heq : n%a = n-a := by
      rw [Nat.mod_eq_sub_mod (by omega : a ≤ n), Nat.mod_eq_of_lt (by omega : n-a < a)]
    omega

/-- The counted Euclidean routine performs at most `2 * k` divisions when its first natural
argument is less than `2^k`. -/
private theorem joint_euclid_pow_work (k n m : ℕ) (s t s' t' : ℤ)
    (hn : n < 2^k) : (cyclicDlogEuclid n s t m s' t').2 ≤ 2*k := by
  induction k generalizing n m s t s' t' with
  | zero =>
    have hn0 : n = 0 := by simpa using! hn
    subst n
    rw [cyclicDlogEuclid]
    simp
  | succ k ih =>
    by_cases hn0 : n = 0
    · subst n; rw [cyclicDlogEuclid]; simp
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      rw [cyclicDlogEuclid, dif_neg hn0]
      (try dsimp only)
      by_cases ha : m%n = 0
      · rw [cyclicDlogEuclid, dif_pos ha]
        (try dsimp only)
        omega
      · have hapos := Nat.pos_of_ne_zero ha
        have hlt := joint_euclid_two_step n (m%n) hnpos hapos (Nat.mod_lt m hnpos)
        have hu : n%(m%n) < 2^k := by rw [pow_succ] at hn; omega
        rw [cyclicDlogEuclid, dif_neg ha]
        (try dsimp only)
        have hw := ih (n%(m%n)) (m%n)
          (s - ((n/(m%n) : ℕ) : ℤ)*(s' - ((m/n : ℕ) : ℤ)*s))
          (t - ((n/(m%n) : ℕ) : ℤ)*(t' - ((m/n : ℕ) : ℤ)*t))
          (s' - ((m/n : ℕ) : ℤ)*s) (t' - ((m/n : ℕ) : ℤ)*t) hu
        omega

/-- Bounds the division count of `cyclicDlogEuclid` by `2 * (Nat.log 2 r + 1) + 2` when both
natural inputs are at most the positive bound `r`. -/
theorem joint_dlog_logarithmic_euclid (r n m : ℕ) (s t s' t' : ℤ)
    (_hr : 0 < r) (hn : n ≤ r) (_hm : m ≤ r) :
    (cyclicDlogEuclid n s t m s' t').2 ≤ 2*(Nat.log 2 r+1)+2 := by
  have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r
  have h := joint_euclid_pow_work (Nat.log 2 r+1) n m s t s' t' (by omega)
  omega

/-- With `n < 2^k`, binary scalar multiplication with fuel `k` returns `n • g` and counts at
most `2 * k` group additions. -/
theorem binary_add_value_and_work (C : Type) [AddCommGroup C] (g : C) (n k : ℕ)
    (hn : n < 2^k) : (binaryAddFuel g k n).1 = n • g ∧
      (binaryAddFuel g k n).2 ≤ 2*k := by
  induction k generalizing g n with
  | zero =>
    have hn0 : n = 0 := by simpa using! hn
    subst n
    simp [binaryAddFuel]
  | succ k ih =>
    by_cases hn0 : n = 0
    · subst n; simp [binaryAddFuel]
    · have hhalf : n/2 < 2^k := by rw [pow_succ] at hn; omega
      have hv := ih (g+g) (n/2) hhalf
      rw [binaryAddFuel, if_neg hn0]
      (try dsimp only)
      constructor
      · rw [hv.1, nsmul_add, ← two_nsmul, ← mul_nsmul]
        have hdiv := Nat.mod_add_div n 2
        have hmod := Nat.mod_lt n (by omega : 0 < 2)
        split_ifs with heven
        · have heq : (n/2)*2 = n := by omega
          rw [heq]
        · have heq : n = (n/2)*2+1 := by omega
          calc _ = ((n/2)*2+1) • g := by rw [add_nsmul, one_nsmul]
               _ = n • g := by rw [← heq]
      · have hwork := hv.2
        split_ifs <;> omega

/-- Updates a joint decoder accumulator using the extended Euclidean coefficients of the new
first coordinate and current gcd, incrementing read and division counts. -/
private def jointDlogStep {r : ℕ} [NeZero r]
    (acc : (ℕ × ZMod r) × (ℕ × ℕ)) (z : ZMod r × ZMod r) :
    (ℕ × ZMod r) × (ℕ × ℕ) :=
  let e := cyclicDlogEuclid z.1.val 1 0 acc.1.1 0 1
  ((e.1.1, (e.1.2.1 : ZMod r)*z.2 + (e.1.2.2 : ZMod r)*acc.1.2),
    (acc.2.1+1,acc.2.2+e.2))

/-- The extended Euclidean coefficients for `a.val` and `q` satisfy the Bezout identity after
reduction modulo `r`. -/
private theorem joint_euclid_bezout (r : ℕ) [NeZero r] (a : ZMod r) (q : ℕ) :
    ((cyclicDlogEuclid a.val 1 0 q 0 1).1.2.1 : ZMod r)*a +
      ((cyclicDlogEuclid a.val 1 0 q 0 1).1.2.2 : ZMod r)*(q : ZMod r) =
        (Nat.gcd a.val q : ZMod r) := by
  have hz := Nat.gcd_eq_gcd_ab a.val q
  have hc := congrArg (fun x : ℤ => (x : ZMod r)) hz
  rw [cyclicDlogEuclid_value, Nat.xgcdAux_val, Nat.xgcd_val]
  push_cast at hc
  simpa [mul_comm] using! hc.symm

/-- Starting from `(q, d * q)` with `q ≤ r`, folding samples on the line of slope `d` preserves
the gcd and line invariants, adds one read per sample, and obeys the logarithmic division
bound. -/
private theorem joint_fold_general (r : ℕ) [NeZero r] (d : ZMod r)
    (xs : List (ZMod r × ZMod r)) (q reads divisions : ℕ) (hq : q ≤ r)
    (hon : ∀ z ∈ xs, z.2 = d*z.1) :
    let acc := xs.foldl jointDlogStep ((q,d*(q : ZMod r)),(reads,divisions))
    acc.1.1 = (xs.map (fun z => z.1.val)).foldl Nat.gcd q ∧
    acc.1.2 = d*(acc.1.1 : ZMod r) ∧
    acc.2.1 = reads+xs.length ∧
    acc.2.2 ≤ divisions+xs.length*(2*(Nat.log 2 r+1)+2) := by
  induction xs generalizing q reads divisions with
  | nil => simp
  | cons z xs ih =>
    let e := cyclicDlogEuclid z.1.val 1 0 q 0 1
    have hegcd : e.1.1 = Nat.gcd q z.1.val := by
      rw [cyclicDlogEuclid_value, Nat.xgcdAux_fst, Nat.gcd_comm]
    have hline : (e.1.2.1 : ZMod r)*z.2 + (e.1.2.2 : ZMod r)*(d*(q : ZMod r)) =
        d*(Nat.gcd q z.1.val : ZMod r) := by
      rw [hon z (by simp)]
      calc _ = d*((e.1.2.1 : ZMod r)*z.1 + (e.1.2.2 : ZMod r)*(q : ZMod r)) := by ring
        _ = _ := by rw [joint_euclid_bezout, Nat.gcd_comm]
    have hqnew : Nat.gcd q z.1.val ≤ r := by
      by_cases hz : z.1.val = 0
      · simpa [hz] using! hq
      · have h := Nat.gcd_le_right q (Nat.pos_of_ne_zero hz)
        have hv := ZMod.val_lt z.1
        omega
    have hwork := joint_dlog_logarithmic_euclid r z.1.val q 1 0 0 1
      (Nat.pos_of_ne_zero (NeZero.ne r)) (ZMod.val_lt z.1).le hq
    have ht := ih (Nat.gcd q z.1.val) (reads+1) (divisions+e.2) hqnew
      (fun w hw => hon w (List.mem_cons_of_mem z hw))
    dsimp only [e] at hegcd hline ht
    simp only [List.foldl_cons, List.map_cons, jointDlogStep, hegcd, hline]
    change _ = _ ∧ _ = _ ∧ _ = reads+(z::xs).length ∧
      _ ≤ divisions+(z::xs).length*(2*(Nat.log 2 r+1)+2)
    refine ⟨ht.1, ht.2.1, ?_, ?_⟩
    · have h := ht.2.2.1
      simp only [List.length_cons]
      omega
    · have h := ht.2.2.2
      simp only [List.length_cons]
      nlinarith

/-- For samples on the line of slope `d`, `jointDlogFold` returns the gcd of `r` and the first
coordinates, with second coordinate `d` times that gcd, one read per sample, and the stated
division bound. -/
theorem joint_dlog_fold_invariant_and_work (r : ℕ) [NeZero r] (d : ZMod r)
    (xs : List (ZMod r × ZMod r)) (hon : ∀ z ∈ xs, z.2 = d*z.1) :
    (jointDlogFold xs).1.1 = (xs.map (fun z => z.1.val)).foldl Nat.gcd r ∧
    (jointDlogFold xs).1.2 = d*((jointDlogFold xs).1.1 : ZMod r) ∧
    (jointDlogFold xs).2.1 = xs.length ∧
    (jointDlogFold xs).2.2 ≤ xs.length*(2*(Nat.log 2 r+1)+2) := by
  simpa [jointDlogFold, jointDlogStep] using!
    joint_fold_general r d xs r 0 0 (le_refl _) hon

/-- For an arbitrary initial second coordinate and `q ≤ r`, the fold computes the gcd of the
first coordinates with `q`, adds one read per sample, and satisfies the division bound
including the initial count. -/
private theorem joint_fold_work_general (r : ℕ) [NeZero r]
    (xs : List (ZMod r × ZMod r)) (q : ℕ) (b : ZMod r) (reads divisions : ℕ)
    (hq : q ≤ r) :
    let acc := xs.foldl jointDlogStep ((q,b),(reads,divisions))
    acc.1.1 = (xs.map (fun z => z.1.val)).foldl Nat.gcd q ∧
    acc.2.1 = reads+xs.length ∧
    acc.2.2 ≤ divisions+xs.length*(2*(Nat.log 2 r+1)+2) := by
  induction xs generalizing q b reads divisions with
  | nil => simp
  | cons z xs ih =>
    have hegcd : (cyclicDlogEuclid z.1.val 1 0 q 0 1).1.1 = Nat.gcd q z.1.val := by
      rw [cyclicDlogEuclid_value, Nat.xgcdAux_fst, Nat.gcd_comm]
    have hqnew : Nat.gcd q z.1.val ≤ r := by
      by_cases hz : z.1.val = 0
      · simpa [hz] using! hq
      · have h := Nat.gcd_le_right q (Nat.pos_of_ne_zero hz)
        have hv := ZMod.val_lt z.1
        omega
    have hwork := joint_dlog_logarithmic_euclid r z.1.val q 1 0 0 1
      (Nat.pos_of_ne_zero (NeZero.ne r)) (ZMod.val_lt z.1).le hq
    have ht := ih (Nat.gcd q z.1.val)
      (((cyclicDlogEuclid z.1.val 1 0 q 0 1).1.2.1 : ZMod r)*z.2 +
        ((cyclicDlogEuclid z.1.val 1 0 q 0 1).1.2.2 : ZMod r)*b)
      (reads+1) (divisions+(cyclicDlogEuclid z.1.val 1 0 q 0 1).2) hqnew
    simp only [List.foldl_cons, List.map_cons, jointDlogStep, hegcd]
    refine ⟨ht.1, ?_, ?_⟩
    · have h := ht.2.1
      simp only [List.length_cons]
      omega
    · have h := ht.2.2
      simp only [List.length_cons]
      nlinarith

/-- For arbitrary samples, `jointDlogFold` computes the gcd of their first coordinates with `r`,
reads each sample once, and performs at most `xs.length * (2 * (Nat.log 2 r + 1) + 2)`
divisions. -/
theorem jointDlogFold_work (r : ℕ) [NeZero r] (xs : List (ZMod r × ZMod r)) :
    (jointDlogFold xs).1.1 = (xs.map (fun z => z.1.val)).foldl Nat.gcd r ∧
    (jointDlogFold xs).2.1 = xs.length ∧
    (jointDlogFold xs).2.2 ≤ xs.length*(2*(Nat.log 2 r+1)+2) := by
  simpa [jointDlogFold, jointDlogStep] using!
    joint_fold_work_general r xs r 0 0 0 (le_refl _)

/-- Counted binary scalar multiplication returns `n • g` using at most `2 * (Nat.log 2 n + 1)`
counted group additions. -/
theorem binaryAddCounted_value_and_work {C : Type} [AddCommGroup C] (g : C) (n : ℕ) :
    (binaryAddCounted g n).1 = n • g ∧
    (binaryAddCounted g n).2 ≤ 2*(Nat.log 2 n+1) :=
  binary_add_value_and_work C g n (Nat.log 2 n+1)
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n)

/-- The verified decoder has the stated read, division, and addition bounds, and every returned
candidate produces `h` from `g`. On samples on the line of a valid secret `d`, it returns
`d` exactly when the first-coordinate gcd with `r` is one. -/
theorem joint_dlog_actual_verified_correctness_and_work (r : ℕ) [NeZero r]
    (C : Type) [AddCommGroup C] [DecidableEq C] (g h : C)
    (xs : List (ZMod r × ZMod r)) :
    (jointDlogVerified g h xs).2.1 = xs.length ∧
    (jointDlogVerified g h xs).2.2.1 ≤ xs.length*(2*(Nat.log 2 r+1)+2) ∧
    (jointDlogVerified g h xs).2.2.2 ≤ 2*(Nat.log 2 r+1) ∧
    (∀ e, (jointDlogVerified g h xs).1 = some e → e.val • g = h) ∧
    (∀ d : ZMod r, h = d.val • g → (∀ z ∈ xs, z.2 = d*z.1) →
      ((jointDlogVerified g h xs).1 = some d ↔
        (xs.map (fun z => z.1.val)).foldl Nat.gcd r = 1)) := by
  have hfold := jointDlogFold_work r xs
  have hbin := binaryAddCounted_value_and_work g (jointDlogFold xs).1.2.val
  have hlog := Nat.log_mono_right (ZMod.val_lt (jointDlogFold xs).1.2).le (b := 2)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [jointDlogVerified]
    split <;> (try dsimp only) <;> exact hfold.2.1
  · simp only [jointDlogVerified]
    split <;> (try dsimp only) <;> exact hfold.2.2
  · simp only [jointDlogVerified]
    split
    · (try dsimp only)
      have h := hbin.2
      omega
    · (try dsimp only); omega
  · intro e he
    simp only [jointDlogVerified] at he
    split at he
    · split at he
      · rename_i hv
        have heq : (jointDlogFold xs).1.2 = e := Option.some.inj he
        rw [hbin.1] at hv
        simpa only [heq] using! hv
      · cases he
    · cases he
  · intro d hh hon
    have hgood := joint_dlog_fold_invariant_and_work r d xs hon
    have heq := hgood.1
    by_cases hg : (jointDlogFold xs).1.1 = 1
    · have hsecret : (jointDlogFold xs).1.2 = d := by simpa only [hg, Nat.cast_one, mul_one] using! hgood.2.1
      simp only [jointDlogVerified, hg, if_true, hsecret,
        (binaryAddCounted_value_and_work g d.val).1, hh]
      simp [← heq, hg]
    · simp [jointDlogVerified, hg, ← heq]

/-- Lifts a record of residues represented in `Fin r` to modular pairs on the line of slope `d`. -/
private def jointLineRecord (r : ℕ) [NeZero r] (d : ZMod r) (m : ℕ)
    (a : Fin m → Fin r) : Fin m → ZMod r × ZMod r :=
  fun i => ((a i).val, d*((a i).val : ZMod r))

/-- Extracts the canonical `Fin r` representatives of the first coordinates of a modular pair
record. -/
private def jointFirstRecord (r : ℕ) [NeZero r] (m : ℕ)
    (ω : Fin m → ZMod r × ZMod r) : Fin m → Fin r :=
  fun i => ⟨(ω i).1.val, ZMod.val_lt _⟩

/-- Extracting first coordinates after forming a line record recovers the original residue
record. -/
private theorem joint_record_forward (r : ℕ) [NeZero r] (d : ZMod r) (m : ℕ)
    (a : Fin m → Fin r) : jointFirstRecord r m (jointLineRecord r d m a) = a := by
  funext i
  apply Fin.ext
  simp only [jointFirstRecord, jointLineRecord, ZMod.val_natCast,
    Nat.mod_eq_of_lt (a i).isLt]

/-- A record on the line of slope `d` is recovered by extracting its first coordinates and
forming the associated line record. -/
private theorem joint_record_backward (r : ℕ) [NeZero r] (d : ZMod r) (m : ℕ)
    (ω : Fin m → ZMod r × ZMod r) (hon : ∀ i, (ω i).2 = d*(ω i).1) :
    jointLineRecord r d m (jointFirstRecord r m ω) = ω := by
  funext i
  apply Prod.ext
  · simp [jointLineRecord, jointFirstRecord]
  · simp [jointLineRecord, jointFirstRecord, hon i]

/-- For a valid cyclic discrete logarithm instance, the probability of a record event is the sum
of uniform masses `(1 / r)^m` over the first-coordinate records whose line lifts satisfy the
event. -/
private theorem joint_line_event_mass (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod r) (m : ℕ)
    (hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g)
    (E : (Fin m → ZMod r × ZMod r) → Prop) [DecidablePred E] :
    (cyclicDlogRecordDist r g h).probEvent E =
      ∑ _a ∈ Finset.univ.filter (fun a : Fin m → Fin r => E (jointLineRecord r d m a)),
        (1/(r : ℝ))^m := by
  classical
  have hprob (ω : Fin m → ZMod r × ZMod r) :
      (cyclicDlogRecordDist r g h).probOf ω =
        if ∀ i, (ω i).2 = d*(ω i).1 then (1/(r : ℝ))^m else 0 := by
    by_cases hon : ∀ i, (ω i).2 = d*(ω i).1
    · unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf
      simp_rw [show ∀ i, (cyclicDlogRecordDist r g h).prob (ω i) = 1/(r : ℝ) from
        fun i => by
          rw [show ω i = ((ω i).1,(ω i).2) from rfl,
            composite_dlog_actual_line_law r C g h d _ _ hr hp hinj hh, if_pos (hon i)]]
      simp [hon]
    · rw [if_neg hon]
      obtain ⟨i, hi⟩ := not_forall.mp hon
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [show ω i = ((ω i).1,(ω i).2) from rfl,
        composite_dlog_actual_line_law r C g h d _ _ hr hp hinj hh, if_neg hi]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
  rw [Finset.sum_congr rfl (fun ω _ => hprob ω), ← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_bij (fun ω _ => jointFirstRecord r m ω)
  · intro ω hω
    obtain ⟨_, hE, hon⟩ := Finset.mem_filter.mp hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [joint_record_backward r d m ω hon]
      exact hE⟩
  · intro ω₁ h₁ ω₂ h₂ heq
    have h₁on := (Finset.mem_filter.mp h₁).2.2
    have h₂on := (Finset.mem_filter.mp h₂).2.2
    calc ω₁ = jointLineRecord r d m (jointFirstRecord r m ω₁) :=
          (joint_record_backward r d m ω₁ h₁on).symm
      _ = jointLineRecord r d m (jointFirstRecord r m ω₂) := by rw [heq]
      _ = ω₂ := joint_record_backward r d m ω₂ h₂on
  · intro a ha
    refine ⟨jointLineRecord r d m a, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ha).2, fun _ => rfl⟩, joint_record_forward r d m a⟩
  · intro ω hω
    rfl

/-- For a valid cyclic discrete logarithm instance with secret `d`, the probability that the
verified decoder returns `d` equals the uniform mass of first-coordinate records whose gcd
with `r` is one. -/
theorem joint_dlog_uniform_success_mass (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod r) (m : ℕ)
    (hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g) :
    (cyclicDlogRecordDist r g h).probEvent
      (fun ω : Fin m → ZMod r × ZMod r =>
        (jointDlogVerified g h (List.ofFn ω)).1 = some d) =
      ∑ _a ∈ Finset.univ.filter (fun a : Fin m → Fin r =>
        (List.ofFn (fun i => (a i).val)).foldl Nat.gcd r = 1), (1/(r : ℝ))^m := by
  rw [joint_line_event_mass r C g h d m hr hp hinj hh]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro a _
  have hon : ∀ z ∈ List.ofFn (jointLineRecord r d m a), z.2 = d*z.1 := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    rfl
  have h := (joint_dlog_actual_verified_correctness_and_work r C g h
    (List.ofFn (jointLineRecord r d m a))).2.2.2.2 d hh hon
  have hvals : (List.ofFn (jointLineRecord r d m a)).map (fun z => z.1.val) =
      List.ofFn (fun i => (a i).val) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply, jointLineRecord, ZMod.val_natCast,
      Nat.mod_eq_of_lt (a i).isLt]
  simpa only [hvals] using! h

/-- For a valid cyclic discrete logarithm instance, the verified joint decoder recovers the
secret from `m` independent samples with probability at least `1 - r / 2^m`. -/
theorem joint_dlog_fresh_actual_verified_success (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod r) (m : ℕ)
    (hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g) :
    1-(r : ℝ)/(2^m : ℝ) ≤ (cyclicDlogRecordDist r g h).probEvent
      (fun ω : Fin m → ZMod r × ZMod r =>
        (jointDlogVerified g h (List.ofFn ω)).1 = some d) := by
  have hrpos : 0 < r := by omega
  let f : Fin r → ZMod r := fun x => x.val
  have hcol : ∀ x y : Fin r, f x = f y ↔ x.val%r = y.val%r := by
    intro x y
    rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
    constructor
    · intro hxy
      have hv := congrArg ZMod.val hxy
      simpa only [f, ZMod.val_natCast, Nat.mod_eq_of_lt x.isLt,
        Nat.mod_eq_of_lt y.isLt] using! hv
    · intro hxy
      dsimp only [f]
      rw [hxy]
  have hbound := (cyclic_verified_recovery_probability r r m hrpos f hrpos
    (dvd_refl _) hcol).1
  have hprob (a : Fin m → Fin r) : (cyclicSampleDist r hrpos f).probOf a = (1/(r : ℝ))^m := by
    simpa only [Nat.div_self hrpos, one_dvd, implies_true, if_true] using!
      cyclicSampleDist_probOf r r hrpos f hrpos (dvd_refl _) hcol m a
  have hevent (a : Fin m → Fin r) : cyclicVerifiedDecode r hrpos f a = some r ↔
      (List.ofFn (fun i => (a i).val)).foldl Nat.gcd r = 1 := by
    have hsupp : ∀ i, (r/r) ∣ (a i).val := by rw [Nat.div_self hrpos]; simp
    have hverify := (cyclic_candidate_actual_two_query_verification r r m hrpos f a
      hrpos (dvd_refl _) hcol hsupp).1
    have hgcd := (cyclic_decoder_supported_divisor_and_cost r r m a hrpos hrpos
      (dvd_refl _) hsupp).2.2.2
    simpa only [Nat.div_self hrpos, Nat.div_one] using! hverify.trans hgcd
  rw [joint_dlog_uniform_success_mass r C g h d m hr hp hinj hh]
  simpa only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, hprob, hevent] using!
      hbound

end Qatlib.Concepts.HspRecovery.JointDlog
