/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCoinReceiptProgram
import Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.ClassicalTape.FairCoinTape

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.CoinTmLaw

open Qatlib

inductive RaceOut
  | left | right | timeout
  deriving DecidableEq, Fintype, Inhabited

def outBit : RaceOut → Option Bool
  | .left => some false
  | .right => some true
  | .timeout => none

def raceOut (N a : ℕ) (w : List Bool) : RaceOut :=
  if raceWalk N a w = 0 then .left
  else if raceWalk N a w = N then .right
  else .timeout

def wordsOf : ℕ → List (List Bool)
  | 0 => [[]]
  | t + 1 => (wordsOf t).flatMap fun w => [false :: w, true :: w]

theorem wordsOf_length (t : ℕ) : (wordsOf t).length = 2 ^ t := by
  induction t with
  | zero => simp [wordsOf]
  | succ t ih =>
      have h : (wordsOf (t + 1)).length = 2 * (wordsOf t).length := by
        rw [wordsOf, List.length_flatMap]
        simp
        omega
      rw [h, ih, Nat.pow_succ]
      ring

theorem wordsOf_mem : ∀ (t : ℕ) (w : List Bool), w ∈ wordsOf t ↔ w.length = t := by
  intro t
  induction t with
  | zero =>
      intro w
      simp only [wordsOf, List.mem_singleton]
      constructor
      · intro h
        cases w with
        | nil => rfl
        | cons c w => simp at h
      · intro h
        cases w with
        | nil => rfl
        | cons c w => simp at h
  | succ t ih =>
      intro w
      rw [wordsOf, List.mem_flatMap]
      constructor
      · intro h
        obtain ⟨u, hu, hmem⟩ := h
        rcases List.mem_cons.1 hmem with rfl | hmem
        · have hlen := (ih u).1 hu
          simp only [List.length_cons]
          omega
        · have hw : w = true :: u := List.mem_singleton.1 hmem
          rw [hw, List.length_cons]
          have hlen := (ih u).1 hu
          omega
      · intro h
        cases w with
        | nil => simp at h
        | cons c w =>
            have hmem := (ih w).2 (by simp at h; omega)
            refine ⟨w, hmem, ?_⟩
            cases c with
            | false => exact List.Mem.head _
            | true => exact List.Mem.tail _ (List.Mem.head _)

theorem countP_ge_one_mem {α : Type*} (l : List α) (Q : α → Bool) {x : α}
    (hx : x ∈ l) (hQx : Q x = true) : 1 ≤ l.countP Q := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
      by_cases hzx : x = z
      · subst hzx
        rw [List.countP_cons_of_pos hQx]
        omega
      · rw [List.countP_cons]
        have hx' : x ∈ zs := (List.mem_cons.1 hx).resolve_left hzx
        have h := ih hx'
        omega

theorem countP_ge_two_mem {α : Type*} (l : List α) (P : α → Bool) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) (hPx : P x = true) (hPy : P y = true) :
    2 ≤ l.countP P := by
  induction l with
  | nil => cases hx
  | cons z zs ih =>
      by_cases hz : P z = true
      · rw [List.countP_cons_of_pos hz]
        have h1 : 1 ≤ zs.countP P := by
          by_cases hxz : x ∈ zs
          · exact countP_ge_one_mem zs P hxz hPx
          · have hxz' : x = z := by
              rcases List.mem_cons.1 hx with h | h
              · exact h
              · exact absurd h hxz
            have hyz : y ∈ zs := by
              rcases List.mem_cons.1 hy with h | h
              · exact absurd (hxz'.trans h.symm) hne
              · exact h
            exact countP_ge_one_mem zs P hyz hPy
        have h2 := countP_ge_one_mem (z :: zs) P hx hPx
        omega
      · rw [List.countP_cons_of_neg (by simpa using! hz)]
        have hxz : x ∈ zs := (List.mem_cons.1 hx).resolve_left (by
          intro he
          rw [← he] at hz
          rw [hPx] at hz
          simp at hz)
        have hyz : y ∈ zs := (List.mem_cons.1 hy).resolve_left (by
          intro he
          rw [← he] at hz
          rw [hPy] at hz
          simp at hz)
        have h := ih hxz hyz
        omega

theorem countP_le_length_sub_two {α : Type*} (l : List α) (Q : α → Bool) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) (hQx : Q x = false) (hQy : Q y = false) :
    l.countP Q + 2 ≤ l.length := by
  have hsplit : ∀ (m : List α), m.countP Q + m.countP (fun z => !Q z) = m.length := by
    intro m
    induction m with
    | nil => rfl
    | cons z zs ih =>
        rw [List.countP_cons, List.countP_cons]
        cases hz : Q z <;> simp_all <;> omega
  have h2 : 2 ≤ l.countP (fun z => !Q z) :=
    countP_ge_two_mem l (fun z => !Q z) hx hy hne (by simp [hQx]) (by simp [hQy])
  have h := hsplit l
  omega

theorem countP_partition_three {α : Type*} (l : List α) (f : α → RaceOut) :
    l.countP (fun x => f x = .left) + l.countP (fun x => f x = .right)
      + l.countP (fun x => f x = .timeout) = l.length := by
  induction l with
  | nil => rfl
  | cons x ls ih =>
      rw [List.countP_cons, List.countP_cons, List.countP_cons]
      cases hfx : f x <;> simp_all <;> omega

theorem countP_mul_le_sum {α : Type*} (l : List α) (f : α → ℕ) (k : ℕ) :
    k * l.countP (fun x => f x = k) ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x ls ih =>
      by_cases h : f x = k
      · rw [List.countP_cons_of_pos (by simpa using! h), List.map_cons, List.sum_cons,
          Nat.mul_add, Nat.mul_one]
        omega
      · rw [List.countP_cons_of_neg (by simpa using! h), List.map_cons, List.sum_cons]
        have hsum := ih
        omega

theorem sum_le_mul_countP {α : Type*} (l : List α) (g : α → ℕ) (k : ℕ) (P : α → Bool)
    (h0 : ∀ x ∈ l, P x = false → g x = 0)
    (hk : ∀ x ∈ l, P x = true → g x ≤ k) :
    (l.map g).sum ≤ k * l.countP P := by
  induction l with
  | nil => simp
  | cons x ls ih =>
      by_cases hP : P x = true
      · rw [List.countP_cons_of_pos hP, List.map_cons, List.sum_cons,
          Nat.mul_add, Nat.mul_one]
        have hx := hk x (by simp) hP
        have hls := ih (fun y hy => h0 y (by simp [hy]))
          (fun y hy => hk y (by simp [hy]))
        omega
      · rw [List.countP_cons_of_neg (by simpa using! hP), List.map_cons, List.sum_cons]
        have hx := h0 x (by simp) (by simpa using! hP)
        have hls := ih (fun y hy => h0 y (by simp [hy]))
          (fun y hy => hk y (by simp [hy]))
        omega

theorem countP_flatMap {α β : Type*} (P : β → Bool) (l : List α) (f : α → List β) :
    (l.flatMap f).countP P = (l.map fun x => (f x).countP P).sum := by
  induction l with
  | nil => rfl
  | cons x ls ih => rw [List.flatMap_cons, List.countP_append, List.map_cons,
      List.sum_cons, ih]

theorem sum_flatMap {α β : Type*} (g : β → ℕ) (l : List α) (f : α → List β) :
    ((l.flatMap f).map g).sum = ((l.map fun x => ((f x).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x ls ih => rw [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

theorem sum_map_sub (N : ℕ) (f : List Bool → ℕ) (l : List (List Bool))
    (hle : ∀ w ∈ l, f w ≤ N) :
    (l.map fun w => N - f w).sum + (l.map f).sum = N * l.length := by
  induction l with
  | nil => simp
  | cons w ls ih =>
      have h1 : f w ≤ N := hle w (by simp)
      have h2 : ∀ x ∈ ls, f x ≤ N := fun x hx => hle x (by simp [hx])
      have h3 := ih h2
      have hN : N * (ls.length + 1) = N * ls.length + N := by
        ring
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

def machineCountOf (N a t : ℕ) (o : RaceOut) : ℕ :=
  (wordsOf t).countP fun w =>
    (coinTapeRunAux (raceMachine N a) (raceAccept N a) w
      (Turing.TM0.init ([] : List (Option Bool)))).1 = outBit o

def fiberCountOf (N a t : ℕ) (o : RaceOut) : ℕ :=
  (wordsOf t).countP fun w => raceOut N a w = o

theorem race_outBit (N a : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) (w : List Bool) :
    (coinTapeRunAux (raceMachine N a) (raceAccept N a) w
        (Turing.TM0.init ([] : List (Option Bool)))).1
      = outBit (raceOut N a w) := by
  rw [race_coinTapeRunAux_init N a ha w]
  cases hh : raceWalk N a w with
  | zero =>
      have hne' : (0 : ℕ) ≠ N := by omega
      simp [raceOut, outBit, hh, hne']
  | succ n =>
      by_cases eN : (n : ℕ) + 1 = N
      · have hout : raceOut N a w = RaceOut.right := by
          unfold raceOut
          rw [hh, if_neg (by omega : ¬((n : ℕ) + 1 = 0)), if_pos eN]
        rw [hout, if_pos (Or.inr eN), eN]
        show some (decide (N = N)) = outBit RaceOut.right
        simp [outBit]
      · have hout : raceOut N a w = RaceOut.timeout := by
          unfold raceOut
          rw [hh, if_neg (by omega : ¬((n : ℕ) + 1 = 0)), if_neg eN]
        rw [hout, if_neg (fun h => by rcases h with h | h <;> omega)]
        rfl

theorem machineCountOf_eq (N a t : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) (o : RaceOut) :
    machineCountOf N a t o = fiberCountOf N a t o := by
  simp only [machineCountOf, fiberCountOf]
  refine List.countP_congr (fun w _ => ?_)
  rw [race_outBit N a ha hne w]
  cases raceOut N a w <;> cases o <;> simp [outBit]

def walkSumOf (N a t : ℕ) : ℕ := ((wordsOf t).map (fun w => raceWalk N a w)).sum

theorem sum_flatMap_words (g : List Bool → ℕ) (t : ℕ) :
    ((wordsOf (t + 1)).map g).sum
      = ((wordsOf t).map (fun w => g (false :: w))).sum
        + ((wordsOf t).map (fun w => g (true :: w))).sum := by
  rw [wordsOf]
  induction (wordsOf t) with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_nil, List.sum_nil]
      rw [ih]
      omega

theorem walkSumOf_eq (N a : ℕ) (ha : a ≤ N) : ∀ t, walkSumOf N a t = a * 2 ^ t := by
  intro t
  induction t generalizing a with
  | zero => simp [walkSumOf, wordsOf, raceWalk]
  | succ t ih =>
      have hsplit := sum_flatMap_words (fun w => raceWalk N a w) t
      simp only [walkSumOf] at hsplit ⊢
      rw [hsplit]
      have h1 : ((wordsOf t).map (fun w => raceWalk N a (false :: w))).sum
          = walkSumOf N (raceStep N a false) t := rfl
      have h2 : ((wordsOf t).map (fun w => raceWalk N a (true :: w))).sum
          = walkSumOf N (raceStep N a true) t := rfl
      rw [h1, h2]
      by_cases hab : a = 0 ∨ a = N
      · rw [raceStep_absorb N false hab, raceStep_absorb N true hab, ih a ha, Nat.pow_succ]
        ring
      · have hfa : raceStep N a false = a - 1 := by
          rw [raceStep, if_neg hab, if_neg (by simp : ¬(false = true))]
        have hft : raceStep N a true = a + 1 := by
          rw [raceStep, if_neg hab, if_pos rfl]
        have h2 : a - 1 + 1 = a := by omega
        have hsub : (a - 1) * 2 ^ t + 2 ^ t = a * 2 ^ t := by
          have e : ((a - 1) + 1) * 2 ^ t = (a - 1) * 2 ^ t + 1 * 2 ^ t :=
            Nat.add_mul _ _ _
          rw [h2, Nat.one_mul] at e
          exact e.symm
        rw [hfa, hft, ih (a - 1) (by omega), ih (a + 1) (by omega),
          Nat.add_mul, Nat.one_mul, Nat.pow_succ]
        have hfin : a * (2 ^ t * 2) = 2 * (a * 2 ^ t) := by ring
        rw [hfin]
        omega

theorem walkCompSumOf_eq (N a : ℕ) (ha : a ≤ N) (t : ℕ) :
    ((wordsOf t).map (fun w => N - raceWalk N a w)).sum = (N - a) * 2 ^ t := by
  have hle : ∀ w ∈ wordsOf t, raceWalk N a w ≤ N := fun w hw => raceWalk_le N w ha
  have h := sum_map_sub N (fun w => raceWalk N a w) (wordsOf t) hle
  have hsum : ((wordsOf t).map (fun w => raceWalk N a w)).sum = a * 2 ^ t :=
    walkSumOf_eq N a ha t
  have h2 : ((wordsOf t).map (fun w => N - raceWalk N a w)).sum
      + ((wordsOf t).map (fun w => raceWalk N a w)).sum = N * (wordsOf t).length := h
  rw [wordsOf_length, hsum] at h2
  have hsumna : (N - a) + a = N := by omega
  have hdistr : (N - a) * 2 ^ t + a * 2 ^ t = N * 2 ^ t := by
    calc (N - a) * 2 ^ t + a * 2 ^ t
        = ((N - a) + a) * 2 ^ t := (Nat.add_mul _ _ _).symm
      _ = N * 2 ^ t := by rw [hsumna]
  omega

theorem fiberRight_le (N a t : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) :
    N * fiberCountOf N a t .right ≤ a * 2 ^ t := by
  have hN0 : N ≠ 0 := by omega
  have h := countP_mul_le_sum (wordsOf t) (fun w => raceWalk N a w) N
  have hsum : ((wordsOf t).map (fun w => raceWalk N a w)).sum = a * 2 ^ t :=
    walkSumOf_eq N a ha t
  rw [hsum] at h
  have hcongr : (wordsOf t).countP (fun w => raceWalk N a w = N)
      = fiberCountOf N a t .right := by
    refine List.countP_congr (fun w _ => ?_)
    simp only [raceOut]
    by_cases hw : raceWalk N a w = N
    · simp [hw, hN0]
    · by_cases h0 : raceWalk N a w = 0
      · simp [h0]
        omega
      · simp [hw, h0]
  rw [hcongr] at h
  exact h

theorem fiberLeft_le (N a t : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) :
    N * fiberCountOf N a t .left ≤ (N - a) * 2 ^ t := by
  have hN0 : N ≠ 0 := by omega
  have hle : ∀ w ∈ wordsOf t, raceWalk N a w ≤ N := fun w hw => raceWalk_le N w ha
  have h := countP_mul_le_sum (wordsOf t) (fun w => N - raceWalk N a w) N
  rw [walkCompSumOf_eq N a ha t] at h
  have hcongr : (wordsOf t).countP (fun w => N - raceWalk N a w = N)
      = fiberCountOf N a t .left := by
    refine List.countP_congr (fun w _ => ?_)
    simp only [raceOut]
    have hw := raceWalk_le N w ha
    by_cases h0 : raceWalk N a w = 0
    · simp [h0]
    · by_cases hwN : raceWalk N a w = N
      · simp [hwN, hN0]
        omega
      · have hsub : N - raceWalk N a w ≠ N := by omega
        simp [h0, hwN, hsub]
  rw [hcongr] at h
  exact h

theorem fiber_partition (N a t : ℕ) : fiberCountOf N a t .left + fiberCountOf N a t .right
    + fiberCountOf N a t .timeout = 2 ^ t := by
  have h := countP_partition_three (wordsOf t) (raceOut N a)
  simpa only [fiberCountOf, wordsOf_length] using! h

def raceMass (N a t : ℕ) (o : RaceOut) : ℚ :=
  (fiberCountOf N a t o : ℚ) / (2 : ℚ) ^ t

def raceTarget (N a : ℕ) : RaceOut → ℚ
  | .right => (a : ℚ) / (N : ℚ)
  | .left => ((N - a : ℕ) : ℚ) / (N : ℚ)
  | .timeout => 0

theorem raceMass_partition (N a t : ℕ) :
    raceMass N a t .left + raceMass N a t .right + raceMass N a t .timeout = 1 := by
  have hp := fiber_partition N a t
  have h2 : ((2 : ℚ) ^ t) ≠ 0 := by positivity
  have hcast := congrArg (fun x : ℕ => (x : ℚ)) hp
  push_cast at hcast
  unfold raceMass
  field_simp
  linarith

theorem raceMass_right_le (N a t : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) :
    raceMass N a t .right ≤ raceTarget N a .right := by
  have hint := fiberRight_le N a t ha hne
  have hN : ((N : ℚ)) ≠ 0 := by positivity
  have h2 : ((2 : ℚ) ^ t) ≠ 0 := by positivity
  have hcast : ((N * fiberCountOf N a t RaceOut.right : ℕ) : ℚ)
      ≤ ((a * 2 ^ t : ℕ) : ℚ) :=
    Nat.cast_le.mpr hint
  push_cast at hcast
  unfold raceMass raceTarget
  field_simp
  linarith

theorem raceMass_left_le (N a t : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) :
    raceMass N a t .left ≤ raceTarget N a .left := by
  have hint := fiberLeft_le N a t ha hne
  have hN : ((N : ℚ)) ≠ 0 := by positivity
  have h2 : ((2 : ℚ) ^ t) ≠ 0 := by positivity
  have hcast : ((N * fiberCountOf N a t RaceOut.left : ℕ) : ℚ)
      ≤ (((N - a) * 2 ^ t : ℕ) : ℚ) :=
    Nat.cast_le.mpr hint
  push_cast at hcast
  have key : ((fiberCountOf N a t RaceOut.left : ℕ) : ℚ) * ((N : ℚ))
      ≤ ((N - a : ℕ) : ℚ) * ((2 : ℚ) ^ t) := by
    rw [mul_comm ((fiberCountOf N a t RaceOut.left : ℕ) : ℚ) ((N : ℚ))]
    exact hcast
  unfold raceMass raceTarget
  rw [le_div_iff₀ (show (0 : ℚ) < (N : ℚ) by positivity)]
  rw [div_mul_eq_mul_div, div_le_iff₀ (show (0 : ℚ) < (2 : ℚ) ^ t by positivity)]
  exact key

def raceTV (N a t : ℕ) : ℚ :=
  (|raceMass N a t .left - raceTarget N a .left|
    + |raceMass N a t .right - raceTarget N a .right|
    + raceMass N a t .timeout) / 2

theorem raceTV_eq_timeout (N a t : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) :
    raceTV N a t = raceMass N a t .timeout := by
  have hleft : raceMass N a t .left ≤ raceTarget N a .left :=
    raceMass_left_le N a t ha hne
  have hright : raceMass N a t .right ≤ raceTarget N a .right :=
    raceMass_right_le N a t ha hne
  have hpart := raceMass_partition N a t
  have htarget : raceTarget N a .left + raceTarget N a .right
      + raceTarget N a .timeout = 1 := by
    have hN : ((N : ℚ)) ≠ 0 := by positivity
    have hsub : ((N - a : ℕ) : ℚ) = ((N : ℚ)) - ((a : ℚ)) := by
      rw [Nat.cast_sub ha]
    unfold raceTarget
    rw [hsub]
    field_simp
    linarith
  have hT0 : raceTarget N a .timeout = 0 := by unfold raceTarget; simp
  have h1 : raceTarget N a .left - raceMass N a t .left
      + (raceTarget N a .right - raceMass N a t .right)
      = raceMass N a t .timeout := by
    have hz : (raceTarget N a .left + raceTarget N a .right + raceTarget N a .timeout)
        - (raceMass N a t .left + raceMass N a t .right + raceMass N a t .timeout) = 0 := by
      rw [htarget, hpart, sub_self]
    linarith
  unfold raceTV
  rw [abs_of_nonpos (by linarith : raceMass N a t .left - raceTarget N a .left ≤ 0),
    neg_sub, abs_of_nonpos (by linarith : raceMass N a t .right - raceTarget N a .right ≤ 0),
    neg_sub]
  linarith

theorem raceWalk_replicate_true (N : ℕ) : ∀ (k p : ℕ), 1 ≤ p → p ≤ N →
    raceWalk N p (List.replicate k true) = min (p + k) N := by
  intro k
  induction k with
  | zero =>
      intro p _ hp
      rw [List.replicate_zero, Nat.add_zero, min_eq_left hp]
      rfl
  | succ k ih =>
      intro p hp1 hpN
      rw [List.replicate_succ, raceWalk]
      by_cases hN : p = N
      · have hab : raceStep N p true = p := raceStep_absorb N true (Or.inr hN)
        rw [hab, hN, ih N (by omega) (by omega),
          min_eq_right (by omega : N ≤ N + k), min_eq_right (by omega : N ≤ N + (k + 1))]
      · have hstep : raceStep N p true = p + 1 := by
          rw [raceStep, if_neg (by intro h; rcases h with h | h <;> omega),
            if_pos rfl]
        rw [hstep, ih (p + 1) (by omega) (by omega)]
        congr 1
        omega

theorem raceWalk_replicate_false (N : ℕ) : ∀ (k p : ℕ), p ≤ N - 1 →
    raceWalk N p (List.replicate k false) = p - k := by
  intro k
  induction k with
  | zero => intro p _; rfl
  | succ k ih =>
      intro p hpN
      rw [List.replicate_succ, raceWalk]
      by_cases h0 : p = 0
      · subst h0
        rw [raceStep_absorb N false (Or.inl rfl), ih 0 (by omega : (0 : ℕ) ≤ N - 1)]
        omega
      · have hstep : raceStep N p false = p - 1 := by
          rw [raceStep, if_neg (by intro h; rcases h with h | h <;> omega),
            if_neg (by simp : ¬(false = true))]
        rw [hstep, ih (p - 1) (by omega)]
        omega

theorem countP_map' {α β : Type*} (P : β → Bool) (f : α → β) (l : List α) :
    (l.map f).countP P = l.countP (fun x => P (f x)) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [List.map_cons, List.countP_cons, List.countP_cons, ih]

def timeoutW (N a : ℕ) (w : List Bool) : ℕ :=
  if raceOut N a w = RaceOut.timeout then 1 else 0

theorem countP_timeoutW_sum (N a : ℕ) (l : List (List Bool)) :
    l.countP (fun w => raceOut N a w = RaceOut.timeout)
      = (l.map (timeoutW N a)).sum := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ih]
      cases h : raceOut N a w <;> simp [timeoutW, h]
      omega

theorem countP_compose_timeoutW (N a : ℕ) (u : List Bool) (l : List (List Bool)) :
    l.countP (fun s => raceOut N a (u ++ s) = RaceOut.timeout)
      = (l.map (fun x => timeoutW N a (u ++ x))).sum := by
  have e := countP_timeoutW_sum N a (l.map (fun x => u ++ x))
  rw [countP_map', List.map_map] at e
  exact e

theorem sum_wordsOf_add (G : List Bool → ℕ) (r : ℕ) : ∀ t : ℕ,
    ((wordsOf (t + r)).map G).sum
      = ((wordsOf t).map fun u => ((wordsOf r).map fun x => G (u ++ x)).sum).sum := by
  intro t
  induction t generalizing G with
  | zero =>
      rw [Nat.zero_add, wordsOf]
      simp only [List.sum_cons, List.sum_nil, List.map_singleton, List.nil_append]
      exact (Nat.add_zero _).symm
  | succ t ih =>
      have hgg : ∀ u ∈ (wordsOf (t + r)),
          (([false :: u, true :: u]).map G).sum = G (false :: u) + G (true :: u) :=
        fun _ _ => rfl
      have hff : ∀ u ∈ (wordsOf t),
          (([false :: u, true :: u]).map
              (fun w => ((wordsOf r).map fun x => G (w ++ x)).sum)).sum
            = (((wordsOf r).map fun x => G (false :: (u ++ x))).sum
                + ((wordsOf r).map fun x => G (true :: (u ++ x))).sum) := by
        intro u _
        have e1 : ((wordsOf r).map fun x => G ((false :: u) ++ x)).sum
            = ((wordsOf r).map fun x => G (false :: (u ++ x))).sum := rfl
        have e2 : ((wordsOf r).map fun x => G ((true :: u) ++ x)).sum
            = ((wordsOf r).map fun x => G (true :: (u ++ x))).sum := rfl
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [e1, e2]
        omega
      have eF := ih (fun v => G (false :: v))
      have eT := ih (fun v => G (true :: v))
      have hconF : ∀ u ∈ (wordsOf t),
          ((wordsOf r).map (fun x => (fun v => G (false :: v)) (u ++ x))).sum
            = ((wordsOf r).map (fun x => G (false :: (u ++ x)))).sum :=
        fun _ _ => rfl
      have hconT : ∀ u ∈ (wordsOf t),
          ((wordsOf r).map (fun x => (fun v => G (true :: v)) (u ++ x))).sum
            = ((wordsOf r).map (fun x => G (true :: (u ++ x)))).sum :=
        fun _ _ => rfl
      rw [show t + 1 + r = t + r + 1 from by omega]
      simp only [wordsOf, sum_flatMap]
      rw [List.map_congr_left hgg, List.sum_map_add, eF, eT,
        List.map_congr_left hff, List.sum_map_add,
        List.map_congr_left hconF, List.map_congr_left hconT]

theorem fiber_timeout_stride (N a : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) (t : ℕ) :
    fiberCountOf N a (t + N) .timeout ≤ (2 ^ N - 2) * fiberCountOf N a t .timeout := by
  have hN0 : N ≠ 0 := by omega
  have hkey : ∀ u : List Bool,
      (wordsOf N).countP (fun s => raceOut N a (u ++ s) = .timeout) ≤ 2 ^ N - 2 := by
    intro u
    by_cases hu : raceWalk N a u = 0 ∨ raceWalk N a u = N
    · have hz : (wordsOf N).countP (fun s => raceOut N a (u ++ s) = .timeout) = 0 := by
        refine List.countP_eq_zero.2 fun s _ => ?_
        have habs : raceWalk N a (u ++ s) = raceWalk N a u := by
          rw [raceWalk_append, raceWalk_absorb_stay N _ s hu]
        unfold raceOut
        rw [habs]
        rcases hu with hu | hu
        · rw [hu]; simp
        · rw [hu]; simp [hN0]
      omega
    · have hint1 : 1 ≤ raceWalk N a u := by omega
      have hint2 : raceWalk N a u ≤ N - 1 := by
        have hle := raceWalk_le N u ha
        omega
      have htrue : raceOut N a (u ++ List.replicate N true) ≠ .timeout := by
        have hwalk : raceWalk N a (u ++ List.replicate N true) = N := by
          rw [raceWalk_append, raceWalk_replicate_true N N _ hint1 (by omega),
            min_eq_right (by omega)]
        unfold raceOut
        rw [hwalk]
        simp [hN0]
      have hfalse : raceOut N a (u ++ List.replicate N false) ≠ .timeout := by
        have hwalk : raceWalk N a (u ++ List.replicate N false) = 0 := by
          rw [raceWalk_append, raceWalk_replicate_false N N _ hint2]
          omega
        unfold raceOut
        rw [hwalk]
        simp
      have hmemT : List.replicate N true ∈ wordsOf N := by
        rw [wordsOf_mem]; simp
      have hmemF : List.replicate N false ∈ wordsOf N := by
        rw [wordsOf_mem]; simp
      have hne2 : List.replicate N true ≠ List.replicate N false := by
        intro h
        cases N with
        | zero => omega
        | succ m =>
            simp only [List.replicate_succ, List.cons.injEq] at h
            exact Bool.noConfusion h.1
      have hcount := countP_le_length_sub_two (wordsOf N)
        (fun s => raceOut N a (u ++ s) = .timeout)
        (List.replicate N true) (List.replicate N false) hmemT hmemF hne2
        (by simp [htrue]) (by simp [hfalse])
      have hlen := wordsOf_length N
      omega
  have hmain : (wordsOf (t + N)).countP (fun w => raceOut N a w = RaceOut.timeout)
      = ((wordsOf t).map (fun u =>
          (wordsOf N).countP (fun s => raceOut N a (u ++ s) = .timeout))).sum := by
    rw [countP_timeoutW_sum, sum_wordsOf_add (timeoutW N a) N t,
      List.map_congr_left (fun u (_ : u ∈ wordsOf t) =>
        (countP_compose_timeoutW N a u (wordsOf N)).symm)]
  unfold fiberCountOf
  rw [hmain]
  refine sum_le_mul_countP (wordsOf t)
    (fun u => (wordsOf N).countP (fun s => raceOut N a (u ++ s) = .timeout))
    (2 ^ N - 2) (fun w => raceOut N a w = .timeout) ?_ (fun u _ _ => hkey u)
  intro u _
  by_cases hu : raceWalk N a u = 0 ∨ raceWalk N a u = N
  · intro _
    refine List.countP_eq_zero.2 fun s _ => ?_
    have habs : raceWalk N a (u ++ s) = raceWalk N a u := by
      rw [raceWalk_append, raceWalk_absorb_stay N _ s hu]
    unfold raceOut
    rw [habs]
    rcases hu with hu | hu
    · rw [hu]; simp
    · rw [hu]; simp [hN0]
  · intro hP
    have ht : raceOut N a u = RaceOut.timeout := by
      unfold raceOut
      rw [if_neg (fun h => hu (Or.inl h)), if_neg (fun h => hu (Or.inr h))]
    have hP' : decide (raceOut N a u = RaceOut.timeout) = false := hP
    rw [ht] at hP'
    simp at hP'

theorem fiber_timeout_iter (N a : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) : ∀ (k r : ℕ),
    fiberCountOf N a (k * N + r) .timeout
      ≤ (2 ^ N - 2) ^ k * fiberCountOf N a r .timeout := by
  intro k
  induction k with
  | zero => intro r; simp
  | succ k ih =>
      intro r
      have hstride := fiber_timeout_stride N a ha hne (k * N + r)
      have hrew : k * N + r + N = (k + 1) * N + r := by ring
      rw [hrew] at hstride
      have hih := ih r
      calc fiberCountOf N a ((k + 1) * N + r) .timeout
          ≤ (2 ^ N - 2) * fiberCountOf N a (k * N + r) .timeout := hstride
        _ ≤ (2 ^ N - 2) * ((2 ^ N - 2) ^ k * fiberCountOf N a r .timeout) :=
            Nat.mul_le_mul_left _ hih
        _ = (2 ^ N - 2) ^ (k + 1) * fiberCountOf N a r .timeout := by ring

theorem raceMass_timeout_decay_aux (N a : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) (k r : ℕ) :
    raceMass N a (k * N + r) .timeout ≤ ((2 ^ N - 2 : ℚ) / (2 : ℚ) ^ N) ^ k := by
  have h2N : 2 ≤ 2 ^ N := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hne
    simpa using! this
  have hposcast : ((2 ^ N - 2 : ℕ) : ℚ) = ((2 : ℚ) ^ N - 2) := by
    rw [Nat.cast_sub h2N]
    push_cast
    ring
  have hint := fiber_timeout_iter N a ha hne k r
  have hbase : fiberCountOf N a r .timeout ≤ 2 ^ r := by
    have hle : fiberCountOf N a r .timeout ≤ (wordsOf r).length :=
      List.countP_le_length
    rwa [wordsOf_length] at hle
  have hcount : fiberCountOf N a (k * N + r) .timeout ≤ (2 ^ N - 2) ^ k * 2 ^ r :=
    le_trans hint (Nat.mul_le_mul_left _ hbase)
  have hcast : ((fiberCountOf N a (k * N + r) .timeout : ℕ) : ℚ)
      ≤ ((2 ^ N - 2 : ℕ) ^ k * 2 ^ r : ℕ) :=
    Nat.cast_le.mpr hcount
  push_cast at hcast
  rw [hposcast] at hcast
  have hApow : ((2 : ℚ) ^ (k * N + r)) = ((2 : ℚ) ^ N) ^ k * (2 : ℚ) ^ r := by
    rw [pow_add, Nat.mul_comm k N, pow_mul]
  unfold raceMass
  rw [hApow, div_pow]
  rw [div_le_iff₀ (by positivity :
    (0 : ℚ) < ((2 : ℚ) ^ N) ^ k * (2 : ℚ) ^ r)]
  have hcomb : (((2 : ℚ) ^ N - 2) ^ k / ((2 : ℚ) ^ N) ^ k)
      * (((2 : ℚ) ^ N) ^ k * (2 : ℚ) ^ r)
      = ((2 : ℚ) ^ N - 2) ^ k * (2 : ℚ) ^ r := by
    field_simp
  rw [hcomb]
  exact hcast

theorem raceMass_timeout_decay (N a : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) (t : ℕ) :
    raceMass N a t .timeout ≤ ((2 ^ N - 2 : ℚ) / (2 : ℚ) ^ N) ^ (t / N) := by
  obtain ⟨k, r, hkr, hrlt⟩ : ∃ k r, t = k * N + r ∧ r < N :=
    ⟨t / N, t % N, by rw [Nat.mul_comm]; exact (Nat.div_add_mod t N).symm,
      Nat.mod_lt _ (by omega)⟩
  have hk : t / N = k := by
    have e1 := Nat.add_mul_div_left r k (show 0 < N by omega)
    have e2 : r / N = 0 := Nat.div_eq_of_lt hrlt
    have e3 : r + N * k = k * N + r := by ring
    rw [hkr, ← e3, e1, e2]
    try omega
  rw [hk, hkr]
  exact raceMass_timeout_decay_aux N a ha hne k r

theorem output2.frontier1 (N a : ℕ) (ha : a ≤ N) (hne : 1 ≤ N) (t : ℕ) :
    (∀ o, machineCountOf N a t o = fiberCountOf N a t o)
    ∧ raceMass N a t .left + raceMass N a t .right + raceMass N a t .timeout = 1
    ∧ raceMass N a t .right ≤ raceTarget N a .right
    ∧ raceMass N a t .left ≤ raceTarget N a .left
    ∧ raceTV N a t = raceMass N a t .timeout
    ∧ raceMass N a t .timeout ≤ ((2 ^ N - 2 : ℚ) / (2 : ℚ) ^ N) ^ (t / N) :=
  ⟨fun o => machineCountOf_eq N a t ha hne o, raceMass_partition N a t,
    raceMass_right_le N a t ha hne, raceMass_left_le N a t ha hne,
    raceTV_eq_timeout N a t ha hne, raceMass_timeout_decay N a ha hne t⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod.CoinTmLaw
