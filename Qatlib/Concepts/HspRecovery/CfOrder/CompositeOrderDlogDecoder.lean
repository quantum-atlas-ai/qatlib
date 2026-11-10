/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CfOrder.CompositeOrderDlogSampling
import Qatlib.Concepts.HspRecovery.CfOrder.PrimeOrderDlogDecoder
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Totient
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.CfOrder

def cyclicDlogEuclid (n : ℕ) (s t : ℤ) (m : ℕ) (s' t' : ℤ) :
    (ℕ × ℤ × ℤ) × ℕ :=
  if hn : n = 0 then ((m,s',t'),0)
  else
    let q := m / n
    let step :=  cyclicDlogEuclid (m % n) (s' - q*s) (t' - q*t) n s t
    (step.1, step.2+1)
termination_by n
 decreasing_by all_goals apply Nat.mod_lt; omega

theorem cyclicDlogEuclid_value (n : ℕ) (s t : ℤ) (m : ℕ) (s' t' : ℤ) :
    (cyclicDlogEuclid n s t m s' t').1 = Nat.xgcdAux n s t m s' t' := by
  rw [cyclicDlogEuclid]
  split
  · rename_i hn; subst n; simp
  · rename_i hn
    rw [Nat.xgcdAux_rec (Nat.pos_of_ne_zero hn)]
    exact cyclicDlogEuclid_value _ _ _ _ _ _
termination_by n
 decreasing_by all_goals apply Nat.mod_lt; omega

theorem cyclicDlogEuclid_work (n : ℕ) (s t : ℤ) (m : ℕ) (s' t' : ℤ) :
    (cyclicDlogEuclid n s t m s' t').2 ≤ n := by
  rw [cyclicDlogEuclid]
  split
  · rename_i hn; subst n; simp
  · rename_i hn
    have ih := cyclicDlogEuclid_work (m % n) (s' - ((m/n : ℕ) : ℤ)*s) (t' - ((m/n : ℕ) : ℤ)*t) n s t
    have hlt := Nat.mod_lt m (Nat.pos_of_ne_zero hn)
    (try dsimp only)
    omega
termination_by n
 decreasing_by all_goals apply Nat.mod_lt; omega

def cyclicDlogDecode {r : ℕ} [NeZero r] :
    List (ZMod r × ZMod r) → Option (ZMod r) × (ℕ × ℕ)
  | [] => (none,(0,0))
  | z :: zs =>
    let e := cyclicDlogEuclid z.1.val 1 0 r 0 1
    if e.1.1 = 1 then (some ((e.1.2.1 : ZMod r)*z.2), (1,e.2))
    else
      let dec := cyclicDlogDecode zs
      (dec.1,(dec.2.1+1,dec.2.2+e.2))

def cyclicDlogVerified {r : ℕ} [NeZero r] {C : Type} [AddCommGroup C]
    [DecidableEq C] (g h : C) (xs : List (ZMod r × ZMod r)) :
    Option (ZMod r) × (ℕ × ℕ × ℕ) :=
  let dec := cyclicDlogDecode xs
  match dec.1 with
  | none => (none,(dec.2.1,dec.2.2,0))
  | some d =>
    let v := primeDlogRepeatAdd g d.val 0
    (if v.1 = h then some d else none,(dec.2.1,dec.2.2,v.2))

private theorem euclid_gcd (r : ℕ) (a : ZMod r) :
    (cyclicDlogEuclid a.val 1 0 r 0 1).1.1 = Nat.gcd a.val r := by
  rw [cyclicDlogEuclid_value, Nat.xgcdAux_fst]

private theorem euclid_inverse (r : ℕ) [NeZero r] (a : ZMod r)
    (ha : Nat.Coprime a.val r) :
    ((cyclicDlogEuclid a.val 1 0 r 0 1).1.2.1 : ZMod r) * a = 1 := by
  have hz := Nat.gcd_eq_gcd_ab a.val r
  rw [ha.gcd_eq_one] at hz
  have hcast := congrArg (fun x : ℤ => (x : ZMod r)) hz
  rw [cyclicDlogEuclid_value, Nat.xgcdAux_val, Nat.xgcd_val]
  push_cast at hcast
  simpa [mul_comm] using! hcast.symm

theorem cyclicDlogDecode_work {r : ℕ} [NeZero r] (xs : List (ZMod r × ZMod r)) :
    (cyclicDlogDecode xs).2.1 ≤ xs.length ∧
    (cyclicDlogDecode xs).2.2 ≤ xs.length*(2*r+1) := by
  induction xs with
  | nil => simp [cyclicDlogDecode]
  | cons z zs ih =>
    have he := cyclicDlogEuclid_work z.1.val 1 0 r 0 1
    have hv := ZMod.val_lt z.1
    simp only [cyclicDlogDecode, List.length_cons]
    split
    · (try dsimp only); constructor <;> nlinarith
    · (try dsimp only); constructor <;> nlinarith [ih.1,ih.2]

theorem cyclicDlogDecode_none {r : ℕ} [NeZero r] (xs : List (ZMod r × ZMod r)) :
    (cyclicDlogDecode xs).1 = none ↔ ∀ z ∈ xs, ¬Nat.Coprime z.1.val r := by
  induction xs with
  | nil => simp [cyclicDlogDecode]
  | cons z zs ih =>
    simp only [cyclicDlogDecode, euclid_gcd]
    by_cases hz : Nat.Coprime z.1.val r
    · simp [hz.gcd_eq_one]
    · have hg : Nat.gcd z.1.val r ≠ 1 := hz
      simp [hg, ih]

theorem cyclicDlogDecode_some {r : ℕ} [NeZero r] (d : ZMod r)
    (xs : List (ZMod r × ZMod r)) (hon : ∀ z ∈ xs, z.2 = d*z.1)
    (hex : ∃ z ∈ xs, Nat.Coprime z.1.val r) : (cyclicDlogDecode xs).1 = some d := by
  induction xs with
  | nil => simp at hex
  | cons z zs ih =>
    by_cases hz : Nat.Coprime z.1.val r
    · simp only [cyclicDlogDecode, euclid_gcd, hz.gcd_eq_one, ↓reduceIte]
      congr 1
      rw [hon z (by simp)]
      calc
        _ = d * (((cyclicDlogEuclid z.1.val 1 0 r 0 1).1.2.1 : ZMod r)*z.1) := by ring
        _ = d := by rw [euclid_inverse r z.1 hz, mul_one]
    · have hg : Nat.gcd z.1.val r ≠ 1 := hz
      simp only [cyclicDlogDecode, euclid_gcd, if_neg hg]
      apply ih
      · intro w hw; exact hon w (List.mem_cons_of_mem z hw)
      · obtain ⟨w,hw,hunit⟩ := hex
        rcases List.mem_cons.mp hw with he | he
        · subst w; exact (hz hunit).elim
        · exact ⟨w,he,hunit⟩

private theorem repeatAdd_count {C : Type} [AddCommGroup C] (g : C) (n : ℕ) (acc : C) :
    (primeDlogRepeatAdd g n acc).2 = n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp [primeDlogRepeatAdd, ih]

private theorem repeatAdd_value {C : Type} [AddCommGroup C] (g : C) (n : ℕ) (acc : C) :
    (primeDlogRepeatAdd g n acc).1 = acc + n • g := by
  induction n generalizing acc with
  | zero => simp [primeDlogRepeatAdd]
  | succ n ih => simp only [primeDlogRepeatAdd, ih]; rw [succ_nsmul]; abel

theorem cyclicDlogVerified_ok {r : ℕ} [NeZero r] {C : Type} [AddCommGroup C]
    [DecidableEq C] (g h : C) (xs : List (ZMod r × ZMod r)) (d : ZMod r)
    (hd : (cyclicDlogDecode xs).1 = some d) (hh : h = d.val • g) :
    (cyclicDlogVerified g h xs).1 = some d := by
  simp [cyclicDlogVerified, hd, repeatAdd_value, hh]

open scoped Classical BigOperators

private theorem coprime_card (r : ℕ) [NeZero r] :
    (Finset.univ.filter (fun a : ZMod r => Nat.Coprime a.val r)).card = Nat.totient r := by
  rw [← Fintype.card_subtype]
  rw [← Fintype.card_congr (ZMod.unitsEquivCoprime (n := r)), ZMod.card_units_eq_totient]

private theorem cyclicDlog_unit_mass (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod r)
    (hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g) :
    (∑ x : ZMod r × ZMod r, (cyclicDlogRecordDist r g h).prob x *
      (if Nat.Coprime x.1.val r then 1 else 0)) = (Nat.totient r : ℝ)/(r : ℝ) := by
  rw [Fintype.sum_prod_type]
  have hinner (a : ZMod r) :
      (∑ b : ZMod r, (cyclicDlogRecordDist r g h).prob (a,b) *
        (if Nat.Coprime a.val r then 1 else 0)) =
      if Nat.Coprime a.val r then 1/(r : ℝ) else 0 := by
    simp_rw [composite_dlog_actual_line_law r C g h d a _ hr hp hinj hh]
    simp
  simp_rw [hinner]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, coprime_card]
  ring

private theorem cyclicDlog_nonunit_mass (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod r)
    (hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g) :
    (∑ x : ZMod r × ZMod r, (cyclicDlogRecordDist r g h).prob x *
      (if ¬Nat.Coprime x.1.val r then 1 else 0)) = 1-(Nat.totient r : ℝ)/(r : ℝ) := by
  have hw := cyclicDlog_unit_mass r C g h d hr hp hinj hh
  have hs :
      (∑ x : ZMod r × ZMod r, (cyclicDlogRecordDist r g h).prob x *
        (if ¬Nat.Coprime x.1.val r then 1 else 0)) =
      (∑ x : ZMod r × ZMod r, (cyclicDlogRecordDist r g h).prob x) -
      (∑ x : ZMod r × ZMod r, (cyclicDlogRecordDist r g h).prob x *
        (if Nat.Coprime x.1.val r then 1 else 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : Nat.Coprime x.1.val r
    · rw [if_neg (not_not.mpr hx), if_pos hx]; ring
    · rw [if_pos hx, if_neg hx]; ring
  rw [hs, (cyclicDlogRecordDist r g h).sum_one, hw]

private theorem prod_nonunit {r m : ℕ} [NeZero r] (ω : Fin m → ZMod r × ZMod r) :
    (∏ i, (if ¬Nat.Coprime (ω i).1.val r then (1 : ℝ) else 0)) =
    if ∀ i, ¬Nat.Coprime (ω i).1.val r then 1 else 0 := by
  by_cases hall : ∀ i, ¬Nat.Coprime (ω i).1.val r
  · simp [hall]
  · obtain ⟨i,hi⟩ := not_forall.mp hall
    rw [if_neg hall]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

private theorem queryCount_append {I : Type} (C D : Circuit I) :
    QueryCount (C ++ D) = QueryCount C + QueryCount D := by
  induction C with
  | nil => simp [QueryCount]
  | cons s C ih => cases s <;> simp [QueryCount, ih, Nat.add_assoc, Nat.add_comm 1]

private theorem gateCount_append {I : Type} (C D : Circuit I) :
    GateCount (C ++ D) = GateCount C + GateCount D := by
  induction C with
  | nil => simp [GateCount]
  | cons s C ih => cases s <;> simp [GateCount, ih, Nat.add_assoc, Nat.add_comm 1]

end Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.CfOrder
open Matrix Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher

theorem composite_dlog_counted_bezout_decoder (r : ℕ) [NeZero r] (d : ZMod r)
    (xs : List (ZMod r × ZMod r)) (_hr : 2 ≤ r) (hon : ∀ z ∈ xs, z.2 = d*z.1) :
    (cyclicDlogDecode xs).2.1 ≤ xs.length ∧
    (cyclicDlogDecode xs).2.2 ≤ xs.length*(2*r+1) ∧
    ((cyclicDlogDecode xs).1 = none ↔ ∀ z ∈ xs, ¬Nat.Coprime z.1.val r) ∧
    ((∃ z ∈ xs, Nat.Coprime z.1.val r) → (cyclicDlogDecode xs).1 = some d) :=
  ⟨(cyclicDlogDecode_work xs).1, (cyclicDlogDecode_work xs).2,
    cyclicDlogDecode_none xs, cyclicDlogDecode_some d xs hon⟩

theorem composite_dlog_actual_verification_work (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [DecidableEq C] (g h : C) (xs : List (ZMod r × ZMod r)) :
    (cyclicDlogVerified g h xs).2.1 ≤ xs.length ∧
    (cyclicDlogVerified g h xs).2.2.1 ≤ xs.length*(2*r+1) ∧
    (cyclicDlogVerified g h xs).2.2.2 < r ∧
    ∀ d, (cyclicDlogVerified g h xs).1 = some d → d.val • g = h := by
  have hw := cyclicDlogDecode_work xs
  have hr := Nat.pos_of_ne_zero (NeZero.ne r)
  cases hd : (cyclicDlogDecode xs).1 with
  | none =>
    simp only [cyclicDlogVerified, hd]
    refine ⟨hw.1,hw.2,hr,?_⟩
    intro d hfalse; cases hfalse
  | some d =>
    simp only [cyclicDlogVerified, hd, repeatAdd_count, repeatAdd_value, zero_add]
    refine ⟨hw.1,hw.2,ZMod.val_lt d,?_⟩
    intro e he
    split at he
    · rename_i hv
      have heq : d = e := Option.some.inj he
      simpa [← heq] using! hv
    · cases he
open scoped Classical BigOperators
set_option warningAsError false

theorem composite_dlog_fresh_verified_success (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (g h : C) (d : ZMod r) (m : ℕ)
    (hr : 2 ≤ r) (hp : r • g = 0)
    (hinj : Function.Injective (fun x : ZMod r => x.val • g)) (hh : h = d.val • g) :
    (cyclicDlogRecordDist r g h).probEvent
      (fun ω : Fin m → ZMod r × ZMod r =>
        (cyclicDlogVerified g h (List.ofFn ω)).1 = some d) =
    1-(1-(Nat.totient r : ℝ)/(r : ℝ))^m := by
  let P := cyclicDlogRecordDist r g h
  let E := fun ω : Fin m → ZMod r × ZMod r =>
    (cyclicDlogVerified g h (List.ofFn ω)).1 = some d
  have hs (ω : Fin m → ZMod r × ZMod r) :
      P.probOf ω * (if E ω then 1 else 0) =
      P.probOf ω * (1-∏ i, (if ¬Nat.Coprime (ω i).1.val r then 1 else 0)) := by
    by_cases hon : ∀ i, (ω i).2 = d*(ω i).1
    · rw [prod_nonunit]
      by_cases hall : ∀ i, ¬Nat.Coprime (ω i).1.val r
      · have hd : (cyclicDlogDecode (List.ofFn ω)).1 = none := by
          rw [cyclicDlogDecode_none]
          intro z hz
          obtain ⟨i, -, rfl⟩ := List.mem_ofFn.mp hz
          exact hall i
        have hn : ¬E ω := by simp [E,cyclicDlogVerified,hd]
        simp [hn,hall]
      · have hex : ∃ z ∈ List.ofFn ω, Nat.Coprime z.1.val r := by
          obtain ⟨i,hi⟩ := not_forall.mp hall
          exact ⟨ω i,List.mem_ofFn.mpr ⟨i,rfl⟩,not_not.mp hi⟩
        have hline : ∀ z ∈ List.ofFn ω, z.2 = d*z.1 := by
          intro z hz
          obtain ⟨i,-,rfl⟩ := List.mem_ofFn.mp hz
          exact hon i
        have he : E ω := cyclicDlogVerified_ok g h _ d
          (cyclicDlogDecode_some d _ hline hex) hh
        simp [he,hall]
    · obtain ⟨i,hi⟩ := not_forall.mp hon
      have hz : P.prob (ω i) = 0 := by
        change (cyclicDlogRecordDist r g h).prob (ω i) = 0
        change (cyclicDlogRecordDist r g h).prob ((ω i).1,(ω i).2) = 0
        rw [composite_dlog_actual_line_law r C g h d _ _ hr hp hinj hh,
          if_neg hi]
      have hpz : P.probOf ω = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
      simp [hpz]
  change P.probEvent E = _
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter]
  have heq : (∑ ω, if E ω then P.probOf ω else 0) =
      ∑ ω, P.probOf ω * (if E ω then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro ω _; by_cases he : E ω <;> simp [he]
  rw [heq, Finset.sum_congr rfl (fun ω _ => hs ω)]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, P.sum_probOf m,
      P.expect_prod
      (fun (_ : Fin m) (x : ZMod r × ZMod r) => if ¬Nat.Coprime x.1.val r then 1 else 0)]
  have hm := cyclicDlog_nonunit_mass r C g h d hr hp hinj hh
  simp only [P] at *
  simp_rw [hm]
  simp

theorem composite_dlog_same_sampling_resource_ledger (r : ℕ) [NeZero r] (C : Type)
    [AddCommGroup C] [Fintype C] [DecidableEq C] (m : ℕ) :
    let cs := tableSamplingCircuit (R := C) (cyclicDlogCharacters r) (cyclicDlogSamplingPrepare r)
    QueryCount cs = 1 ∧ GateCount cs = 2 ∧
    QueryCount (List.replicate m cs).flatten = m ∧
    GateCount (List.replicate m cs).flatten = 2*m := by
  (try dsimp only)
  let cs := tableSamplingCircuit (R := C) (cyclicDlogCharacters r) (cyclicDlogSamplingPrepare r)
  have hc := tableSamplingCircuit_resources (R := C) (cyclicDlogCharacters r)
    (cyclicDlogSamplingPrepare r)
  refine ⟨hc.1,hc.2,?_,?_⟩
  · induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, queryCount_append, ih, hc.1]
      omega
  · induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, gateCount_append, ih, hc.2]
      omega
end Qatlib.Concepts.HspRecovery.CfOrder
