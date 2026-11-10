/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClockedTapeDecision
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib

namespace Qatlib.Concepts.ClassicalTape.FairCoinTape

open scoped BigOperators Classical

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def TM0StmtApply (T : Turing.Tape Γ) : Turing.TM0.Stmt Γ → Turing.Tape Γ
  | Turing.TM0.Stmt.move d => T.move d
  | Turing.TM0.Stmt.write a => T.write a

theorem TM0_step_apply (M : Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    Turing.TM0.step M cfg =
      (M cfg.q cfg.Tape.head).map fun p => ⟨p.1, TM0StmtApply cfg.Tape p.2⟩ := by
  obtain ⟨q, T⟩ := cfg
  rfl

theorem TM0_step_eq_none (M : Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    (Turing.TM0.step M cfg = none) ↔ (M cfg.q cfg.Tape.head = none) := by
  rw [TM0_step_apply, Option.map_eq_none_iff]

theorem TM0_step_eq_some (M : Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (q' : Λ) (stmt : Turing.TM0.Stmt Γ) (h : M cfg.q cfg.Tape.head = some (q', stmt)) :
    Turing.TM0.step M cfg = some ⟨q', TM0StmtApply cfg.Tape stmt⟩ := by
  rw [TM0_step_apply, h]
  rfl

def coinHalt (M : Bool → Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) : Bool :=
  (M false cfg.q cfg.Tape.head).isNone && (M true cfg.q cfg.Tape.head).isNone

def coinTapeRunAux (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    List Bool → Turing.TM0.Cfg Γ Λ → Option Bool × ℕ
  | [], cfg =>
      if coinHalt M cfg then (some (accept cfg.q), 0) else (none, 0)
  | c :: cs, cfg =>
      if coinHalt M cfg then (some (accept cfg.q), 0)
      else
        match Turing.TM0.step (M c) cfg with
        | none => (some (accept cfg.q), 1)
        | some cfg' => Prod.map id (· + 1) (coinTapeRunAux M accept cs cfg')

def coinTapeRun (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (input : List Γ) (coins : List Bool) : Option Bool × ℕ :=
  coinTapeRunAux M accept coins (Turing.TM0.init input)

def coinTapeTransitionCountAux (M : Bool → Turing.TM0.Machine Γ Λ) :
    List Bool → Turing.TM0.Cfg Γ Λ → ℕ
  | [], _ => 0
  | c :: cs, cfg =>
      if coinHalt M cfg then 0 else
        match Turing.TM0.step (M c) cfg with
        | none => 0
        | some cfg' => coinTapeTransitionCountAux M cs cfg' + 1

def coinTapeTransitionCount (M : Bool → Turing.TM0.Machine Γ Λ)
    (input : List Γ) (coins : List Bool) : ℕ :=
  coinTapeTransitionCountAux M coins (Turing.TM0.init input)

theorem coinTapeTransitionCountAux_le_reads (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) : ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
    coinTapeTransitionCountAux M coins cfg ≤ (coinTapeRunAux M accept coins cfg).2 := by
  intro coins
  induction coins with
  | nil =>
    intro cfg
    simp only [coinTapeTransitionCountAux, coinTapeRunAux]
    split <;> exact Nat.zero_le _
  | cons c cs ih =>
    intro cfg
    by_cases hc : coinHalt M cfg = true
    · simp [coinTapeTransitionCountAux, coinTapeRunAux, hc]
    · cases hs : Turing.TM0.step (M c) cfg with
      | none => simp [coinTapeTransitionCountAux, coinTapeRunAux, hc, hs]
      | some cfg' =>
        simpa [coinTapeTransitionCountAux, coinTapeRunAux, hc, hs, Prod.map] using
          Nat.succ_le_succ (ih cfg')

theorem coinTapeTransitionCount_le_reads (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (input : List Γ) (coins : List Bool) :
    coinTapeTransitionCount M input coins ≤ (coinTapeRun M accept input coins).2 :=
  coinTapeTransitionCountAux_le_reads M accept coins _

theorem coinTapeRunAux_of_coinHalt (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : coinHalt M cfg = true) :
    coinTapeRunAux M accept coins cfg = (some (accept cfg.q), 0) := by
  cases coins with
  | nil => simp only [coinTapeRunAux]; rw [if_pos h]
  | cons c cs => simp only [coinTapeRunAux]; rw [if_pos h]

theorem coinTapeRunAux_nil_of_not_coinHalt (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (cfg : Turing.TM0.Cfg Γ Λ) (h : coinHalt M cfg = false) :
    coinTapeRunAux M accept [] cfg = (none, 0) := by
  simp only [coinTapeRunAux]
  rw [if_neg (by simp [h])]

theorem coinTapeRunAux_cons_of_step_none (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (c : Bool) (cs : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (h : coinHalt M cfg = false) (hs : Turing.TM0.step (M c) cfg = none) :
    coinTapeRunAux M accept (c :: cs) cfg = (some (accept cfg.q), 1) := by
  simp only [coinTapeRunAux]
  rw [if_neg (by simp [h])]
  rw [hs]

theorem coinTapeRunAux_cons_of_step_some (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (c : Bool) (cs : List Bool) (cfg cfg' : Turing.TM0.Cfg Γ Λ)
    (h : coinHalt M cfg = false) (hs : Turing.TM0.step (M c) cfg = some cfg') :
    coinTapeRunAux M accept (c :: cs) cfg =
      Prod.map id (· + 1) (coinTapeRunAux M accept cs cfg') := by
  simp only [coinTapeRunAux]
  rw [if_neg (by simp [h])]
  rw [hs]

theorem coinTapeRunAux_snd_le (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      (coinTapeRunAux M accept coins cfg).2 ≤ coins.length := by
  intro coins
  induction coins with
  | nil =>
      intro cfg
      by_cases h : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt M accept [] cfg h]
        exact Nat.zero_le _
      · have h' : coinHalt M cfg = false := by simpa using h
        rw [coinTapeRunAux_nil_of_not_coinHalt M accept cfg h']
        exact Nat.zero_le _
  | cons c cs ih =>
      intro cfg
      by_cases h : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt M accept _ cfg h]
        exact Nat.zero_le _
      · have h' : coinHalt M cfg = false := by simpa using h
        cases hs : Turing.TM0.step (M c) cfg with
        | none =>
            rw [coinTapeRunAux_cons_of_step_none M accept c cs cfg h' hs]
            exact Nat.succ_le_succ (Nat.zero_le _)
        | some cfg' =>
            rw [coinTapeRunAux_cons_of_step_some M accept c cs cfg cfg' h' hs]
            have hle := ih cfg'
            simp only [Prod.map, id, List.length_cons]
            omega

theorem coinTapeRunAux_append (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) (b : Bool) (k : ℕ),
      coinTapeRunAux M accept coins cfg = (some b, k) →
      ∀ extra : List Bool, coinTapeRunAux M accept (coins ++ extra) cfg = (some b, k) := by
  intro coins
  induction coins with
  | nil =>
      intro cfg b k h extra
      by_cases hc : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt M accept [] cfg hc] at h
        obtain ⟨rfl, rfl⟩ := h
        exact coinTapeRunAux_of_coinHalt M accept _ cfg hc
      · have hc' : coinHalt M cfg = false := by simpa using hc
        rw [coinTapeRunAux_nil_of_not_coinHalt M accept cfg hc'] at h
        nomatch h
  | cons c cs ih =>
      intro cfg b k h extra
      by_cases hc : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt M accept (c :: cs) cfg hc] at h
        obtain ⟨rfl, rfl⟩ := h
        exact coinTapeRunAux_of_coinHalt M accept _ cfg hc
      · have hc' : coinHalt M cfg = false := by simpa using hc
        cases hs : Turing.TM0.step (M c) cfg with
        | none =>
            rw [coinTapeRunAux_cons_of_step_none M accept c cs cfg hc' hs] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [List.cons_append]
            exact coinTapeRunAux_cons_of_step_none M accept c (cs ++ extra) cfg hc' hs
        | some cfg' =>
            rw [coinTapeRunAux_cons_of_step_some M accept c cs cfg cfg' hc' hs] at h
            rcases hr : coinTapeRunAux M accept cs cfg' with ⟨r, m⟩
            rw [hr] at h
            simp only [Prod.map, id, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [List.cons_append,
              coinTapeRunAux_cons_of_step_some M accept c (cs ++ extra) cfg cfg' hc' hs,
              ih cfg' b m hr extra]
            rfl

theorem coinTapeRunAux_take (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) (b : Bool) (k : ℕ),
      coinTapeRunAux M accept coins cfg = (some b, k) →
      k ≤ coins.length → coinTapeRunAux M accept (coins.take k) cfg = (some b, k) := by
  intro coins
  induction coins with
  | nil =>
      intro cfg b k h hk
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      rw [List.take_zero]
      by_cases hc : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt M accept [] cfg hc] at h
        obtain ⟨rfl, rfl⟩ := h
        exact coinTapeRunAux_of_coinHalt M accept [] cfg hc
      · have hc' : coinHalt M cfg = false := by simpa using hc
        rw [coinTapeRunAux_nil_of_not_coinHalt M accept cfg hc'] at h
        nomatch h
  | cons c cs ih =>
      intro cfg b k h hk
      by_cases hc : coinHalt M cfg = true
      · rw [coinTapeRunAux_of_coinHalt M accept (c :: cs) cfg hc] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [List.take_zero]
        exact coinTapeRunAux_of_coinHalt M accept [] cfg hc
      · have hc' : coinHalt M cfg = false := by simpa using hc
        cases hs : Turing.TM0.step (M c) cfg with
        | none =>
            rw [coinTapeRunAux_cons_of_step_none M accept c cs cfg hc' hs] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [show (c :: cs).take 1 = [c] from rfl]
            exact coinTapeRunAux_cons_of_step_none M accept c [] cfg hc' hs
        | some cfg' =>
            rw [coinTapeRunAux_cons_of_step_some M accept c cs cfg cfg' hc' hs] at h
            rcases hr : coinTapeRunAux M accept cs cfg' with ⟨r, m⟩
            rw [hr] at h
            simp only [Prod.map, id, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hm : m ≤ cs.length := by
              simp only [List.length_cons] at hk
              omega
            rw [List.take_succ_cons,
              coinTapeRunAux_cons_of_step_some M accept c (cs.take m) cfg cfg' hc' hs,
              ih cfg' b m hr hm]
            rfl

noncomputable def fairTapeSuccess (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (input : List Γ) (t : ℕ) (target : Bool) : ℝ :=
  (∑ ω : Fin t → Bool,
    if (coinTapeRun M accept input (List.ofFn ω)).1 = some target then (1 : ℝ) else 0) / 2 ^ t

theorem fairTapeSuccess_nonneg (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (input : List Γ) (t : ℕ) (target : Bool) :
    0 ≤ fairTapeSuccess M accept input t target := by
  unfold fairTapeSuccess
  exact div_nonneg (Finset.sum_nonneg fun ω _ => by split_ifs <;> norm_num)
    (pow_nonneg (by norm_num) t)

theorem fairTapeSuccess_add_le_one (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (input : List Γ) (t : ℕ) :
    fairTapeSuccess M accept input t true + fairTapeSuccess M accept input t false ≤ 1 := by
  unfold fairTapeSuccess
  rw [← add_div, ← Finset.sum_add_distrib]
  have hpoint : ∀ ω : Fin t → Bool,
      ((if (coinTapeRun M accept input (List.ofFn ω)).1 = some true then (1 : ℝ) else 0) +
        (if (coinTapeRun M accept input (List.ofFn ω)).1 = some false then (1 : ℝ) else 0)) ≤ 1 := by
    intro ω
    rcases h : (coinTapeRun M accept input (List.ofFn ω)).1 with _ | b
    · simp
    · cases b <;> simp
  have hsum : (∑ _ω : Fin t → Bool, (1 : ℝ)) = 2 ^ t := by
    simp [Finset.sum_const]
  have hle : (∑ ω : Fin t → Bool,
        ((if (coinTapeRun M accept input (List.ofFn ω)).1 = some true then (1 : ℝ) else 0) +
          (if (coinTapeRun M accept input (List.ofFn ω)).1 = some false then (1 : ℝ) else 0)))
      ≤ 2 ^ t := by
    rw [← hsum]
    exact Finset.sum_le_sum fun ω _ => hpoint ω
  calc (∑ ω : Fin t → Bool,
          ((if (coinTapeRun M accept input (List.ofFn ω)).1 = some true then (1 : ℝ) else 0) +
            (if (coinTapeRun M accept input (List.ofFn ω)).1 = some false then (1 : ℝ) else 0)))
        / 2 ^ t
        ≤ (2 ^ t : ℝ) / 2 ^ t := (div_le_div_iff_of_pos_right (pow_pos (by norm_num) t)).mpr hle
    _ = 1 := div_self (pow_ne_zero t (by norm_num))

theorem fair_coin_tape_actual_consumption_and_mass :
    ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (M : Bool → Turing.TM0.Machine Γ Λ)
      (a : Λ → Bool) (input : List Γ) (coins : List Bool),
      (coinTapeRun M a input coins).2 ≤ coins.length ∧
        ∀ t : ℕ, 0 ≤ fairTapeSuccess M a input t true ∧
          0 ≤ fairTapeSuccess M a input t false ∧
            fairTapeSuccess M a input t true + fairTapeSuccess M a input t false ≤ 1 := by
  intro Γ Λ _ _ M a input coins
  exact ⟨coinTapeRunAux_snd_le M a coins _, fun t =>
    ⟨fairTapeSuccess_nonneg M a input t true, fairTapeSuccess_nonneg M a input t false,
      fairTapeSuccess_add_le_one M a input t⟩⟩

theorem coinTapeRunAux_const_fst (M : Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ),
      (coinTapeRunAux (fun _ => M) accept coins cfg).1 =
        tapeDecisionRun M accept coins.length cfg := by
  intro coins
  induction coins with
  | nil =>
      intro cfg
      by_cases h : M cfg.q cfg.Tape.head = none
      · rw [coinTapeRunAux_of_coinHalt _ _ [] cfg (by simp [coinHalt, h])]
        simp only [List.length_nil, tapeDecisionRun]
        rw [if_pos ((TM0_step_eq_none M cfg).mpr h)]
      · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp h
        have h' : coinHalt (fun _ => M) cfg = false := by simp [coinHalt, ← hp]
        rw [coinTapeRunAux_nil_of_not_coinHalt _ _ cfg h']
        simp only [List.length_nil, tapeDecisionRun]
        rw [if_neg (mt (TM0_step_eq_none M cfg).mp h)]
  | cons c cs ih =>
      intro cfg
      by_cases h : M cfg.q cfg.Tape.head = none
      · rw [coinTapeRunAux_of_coinHalt _ _ (c :: cs) cfg (by simp [coinHalt, h])]
        simp only [List.length_cons, tapeDecisionRun]
        rw [(TM0_step_eq_none M cfg).mpr h]
      · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp h
        have h' : coinHalt (fun _ => M) cfg = false := by simp [coinHalt, ← hp]
        have hs := TM0_step_eq_some M cfg p.1 p.2 hp.symm
        rw [coinTapeRunAux_cons_of_step_some _ _ c cs cfg _ h' hs]
        simp only [Prod.map, id, List.length_cons]
        rw [ih]
        simp only [tapeDecisionRun]
        rw [hs]

theorem fair_coin_tape_deterministic_embedding :
    ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] (M : Turing.TM0.Machine Γ Λ)
      (a : Λ → Bool) (input : List Γ) (t : ℕ) (ω : Fin t → Bool),
      (coinTapeRun (fun _ => M) a input (List.ofFn ω)).1 = tapeDecision M a input t := by
  intro Γ Λ _ _ M a input t ω
  show (coinTapeRunAux (fun _ => M) a (List.ofFn ω) (Turing.TM0.init input)).1 =
    tapeDecisionRun M a t (Turing.TM0.init input)
  have h := coinTapeRunAux_const_fst M a (List.ofFn ω) (Turing.TM0.init input)
  rwa [List.length_ofFn] at h

def finBoolSnocEquiv (t : ℕ) : (Fin t → Bool) × Bool ≃ (Fin (t + 1) → Bool) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (w ∘ Fin.castSucc, w (Fin.last t))
  left_inv p := by
    obtain ⟨v, b⟩ := p
    ext1
    · funext i
      simp [Fin.snoc_castSucc]
    · simp [Fin.snoc_last]
  right_inv w := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j
      simp

theorem fairTapeSuccess_succ_of_forall_isSome (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (input : List Γ) (t : ℕ) (target : Bool)
    (h : ∀ ω : Fin t → Bool, ((coinTapeRun M accept input (List.ofFn ω)).1).isSome) :
    fairTapeSuccess M accept input (t + 1) target =
      fairTapeSuccess M accept input t target := by
  unfold fairTapeSuccess
  have key : ∀ p : (Fin t → Bool) × Bool,
      (if (coinTapeRun M accept input
            (List.ofFn (finBoolSnocEquiv t p))).1 = some target then (1 : ℝ) else 0) =
        if (coinTapeRun M accept input (List.ofFn p.1)).1 = some target then (1 : ℝ) else 0 := by
    intro ⟨v, b⟩
    (try dsimp only)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h v)
    have hrun : coinTapeRun M accept input (List.ofFn v) =
        (some x, (coinTapeRun M accept input (List.ofFn v)).2) := Prod.ext hx rfl
    have happ : coinTapeRun M accept input (List.ofFn v ++ [b]) =
        (some x, (coinTapeRun M accept input (List.ofFn v)).2) :=
      coinTapeRunAux_append M accept (List.ofFn v) (Turing.TM0.init input) x _ hrun [b]
    have hof : List.ofFn (finBoolSnocEquiv t (v, b)) = List.ofFn v ++ [b] := by
      show List.ofFn (Fin.snoc v b) = List.ofFn v ++ [b]
      rw [List.ofFn_succ', List.concat_eq_append]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hof, happ, hrun]
  rw [← Equiv.sum_comp (finBoolSnocEquiv t)
    (fun w => if (coinTapeRun M accept input (List.ofFn w)).1 = some target then (1 : ℝ) else 0)]
  rw [Finset.sum_congr rfl (fun p _ => key p)]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_congr rfl (fun v _ => show
      (∑ _b : Bool,
          if (coinTapeRun M accept input (List.ofFn v)).1 = some target then (1 : ℝ) else 0) =
        2 * (if (coinTapeRun M accept input (List.ofFn v)).1 = some target then (1 : ℝ) else 0) by
      simp [Finset.sum_const, nsmul_eq_mul])]
  rw [← Finset.mul_sum]
  rw [pow_succ, mul_comm (2 : ℝ) _, mul_div_mul_right _ _ (two_ne_zero (α := ℝ))]

theorem fairTapeSuccess_eq_of_forall_isSome (M : Bool → Turing.TM0.Machine Γ Λ)
    (accept : Λ → Bool) (input : List Γ) (m : ℕ) (target : Bool)
    (h : ∀ t ≥ m, ∀ ω : Fin t → Bool, ((coinTapeRun M accept input (List.ofFn ω)).1).isSome) :
    ∀ t ≥ m, fairTapeSuccess M accept input t target =
      fairTapeSuccess M accept input m target := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      rw [fairTapeSuccess_succ_of_forall_isSome M accept input n target (h n hn), ih]

def TapeInP (L : List Bool → Prop) : Prop :=
  ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (accept : Fin (q + 1) → Bool) (c k : ℕ),
    ∀ input : List Bool, ∃ t : ℕ, t ≤ c * input.length ^ k + c ∧
      tapeDecision M accept (input.map some) t = some (decide (L input))

def TapeInBPP (L : List Bool → Prop) : Prop :=
  ∃ (q : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    (accept : Fin (q + 1) → Bool) (c k : ℕ),
    (∀ ql γ, (M false ql γ = none) ↔ (M true ql γ = none)) ∧
      ∀ input : List Bool,
        (∀ ω : Fin (c * input.length ^ k + c) → Bool,
            (coinTapeRun M accept (input.map some) (List.ofFn ω)).1 ≠ none) ∧
          fairTapeSuccess M accept (input.map some) (c * input.length ^ k + c)
            (if L input then true else false) ≥ 2 / 3

theorem tape_polynomial_classes_deterministic_inclusion :
    ∀ L : List Bool → Prop, TapeInP L → TapeInBPP L := by
  intro L hP
  obtain ⟨q, M, accept, c, k, hbound⟩ := hP
  refine ⟨q, fun _ => M, accept, c, k, fun _ _ => Iff.rfl, fun input => ?_⟩
  obtain ⟨t, ht, hdec⟩ := hbound input
  have hT : tapeDecision M accept (input.map some) (c * input.length ^ k + c) =
      some (decide (L input)) :=
    (clocked_tape_decision_monotone_and_in_time _ _ M accept (input.map some) t _
      (decide (L input)) ht hdec).1
  refine ⟨fun ω => ?_, ?_⟩
  · rw [fair_coin_tape_deterministic_embedding _ _ M accept (input.map some) _ ω, hT]
    exact Option.some_ne_none _
  · have htarget : (if L input then true else false) = decide (L input) := by
      by_cases h : L input <;> simp [h]
    rw [htarget]
    unfold fairTapeSuccess
    have h1 : ∀ ω : Fin (c * input.length ^ k + c) → Bool,
        (if (coinTapeRun (fun _ => M) accept (input.map some) (List.ofFn ω)).1 =
            some (decide (L input)) then (1 : ℝ) else 0) = 1 := by
      intro ω
      rw [fair_coin_tape_deterministic_embedding _ _ M accept (input.map some) _ ω, hT]
      simp
    have hsum : (∑ ω : Fin (c * input.length ^ k + c) → Bool,
          (if (coinTapeRun (fun _ => M) accept (input.map some) (List.ofFn ω)).1 =
              some (decide (L input)) then (1 : ℝ) else 0)) =
        ∑ _ω : Fin (c * input.length ^ k + c) → Bool, (1 : ℝ) :=
      Finset.sum_congr rfl fun ω _ => h1 ω
    rw [hsum]
    have hcard : (∑ _ω : Fin (c * input.length ^ k + c) → Bool, (1 : ℝ)) =
        2 ^ (c * input.length ^ k + c) := by
      simp [Finset.sum_const]
    rw [hcard, div_self (pow_ne_zero _ (by norm_num))]
    norm_num

end Qatlib.Concepts.ClassicalTape.FairCoinTape
