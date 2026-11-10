/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler
import Qatlib.Concepts.ClassicalTape.TapeCompilation.FiniteTapeMajority
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.ClassicalTape.TapeCompilation

open Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler (phaseCopyResult phaseWorkMap
  phaseInput phaseBusy PhaseHomeAt PhaseInputSame PhaseMarkAbs CellCore SweepPhase
  phase1Table phase1EmbedCfg phase1Readout tmCopyRunResetCompile tmCopyRunResetCompile_run
  pairCoins coinTapeRunAux_cons_live)

structure CoinReceipt where
  output : Option Bool
  reads : ℕ
  clock : ℕ
  peak : ℕ

def CoinReceipt.bump (r : CoinReceipt) : CoinReceipt :=
  ⟨r.output, r.reads + 1, r.clock + 1, r.peak⟩

theorem CoinReceipt.bump_peak_clock (r : CoinReceipt) :
    (CoinReceipt.bump r).peak = r.peak ∧ (CoinReceipt.bump r).clock = r.clock + 1 :=
  ⟨rfl, rfl⟩

def stmtExtent {Γ : Type*} (stmt : Turing.TM0.Stmt Γ) (lo hi d : ℤ) : ℤ × ℤ × ℤ :=
  match stmt with
  | .write _ => (lo, hi, d)
  | .move Turing.Dir.left => (min lo (d - 1), hi, d - 1)
  | .move Turing.Dir.right => (lo, max hi (d + 1), d + 1)

theorem stmtExtent_inv {Γ : Type*} (stmt : Turing.TM0.Stmt Γ) {lo hi d : ℤ}
    (hlo : lo ≤ d) (hhi : d ≤ hi) :
    (stmtExtent stmt lo hi d).1 ≤ (stmtExtent stmt lo hi d).2.2
      ∧ (stmtExtent stmt lo hi d).2.2 ≤ (stmtExtent stmt lo hi d).2.1 := by
  cases stmt with
  | write _ => simp only [stmtExtent]; omega
  | move dir =>
      cases dir <;> simp only [stmtExtent] <;> omega

theorem stmtExtent_range {Γ : Type*} (stmt : Turing.TM0.Stmt Γ) {lo hi d : ℤ}
    (hlo : lo ≤ d) (hhi : d ≤ hi) :
    (stmtExtent stmt lo hi d).2.1 - (stmtExtent stmt lo hi d).1 ≤ hi - lo + 1 := by
  cases stmt with
  | write _ => simp only [stmtExtent]; omega
  | move dir =>
      cases dir <;> simp only [stmtExtent] <;> omega

def coinReceiptAux {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    List Bool → Turing.TM0.Cfg Γ Λ → ℤ → ℤ → ℤ → CoinReceipt
  | [], cfg, lo, hi, _ =>
      ⟨if coinHalt M cfg then some (accept cfg.q) else none, 0, 0, (hi - lo + 1).toNat⟩
  | c :: cs, cfg, lo, hi, d =>
      if coinHalt M cfg then ⟨some (accept cfg.q), 0, 0, (hi - lo + 1).toNat⟩
      else
        match M c cfg.q cfg.Tape.head with
        | none => ⟨some (accept cfg.q), 1, 0, (hi - lo + 1).toNat⟩
        | some (q', stmt) =>
            CoinReceipt.bump
              (coinReceiptAux M accept cs ⟨q', TM0StmtApply cfg.Tape stmt⟩
                (stmtExtent stmt lo hi d).1 (stmtExtent stmt lo hi d).2.1
                (stmtExtent stmt lo hi d).2.2)

def coinReceiptRun {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool)
    (input : List Γ) (coins : List Bool) : CoinReceipt :=
  coinReceiptAux M accept coins (Turing.TM0.init input) 0 0 0

theorem one_le_toNat_of_one_le {x : ℤ} (h : (1 : ℤ) ≤ x) : 1 ≤ x.toNat := by
  have hx := Int.self_le_toNat x
  omega

theorem coinReceiptAux_cons_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) (c : Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) (cs : List Bool) (lo hi d : ℤ)
    (hc : coinHalt M cfg = true) :
    coinReceiptAux M accept (c :: cs) cfg lo hi d
      = ⟨some (accept cfg.q), 0, 0, (hi - lo + 1).toNat⟩ := by
  simp only [coinReceiptAux, hc, if_true]

theorem coinReceiptAux_cons_none {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) (c : Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) (cs : List Bool) (lo hi d : ℤ)
    (hc : coinHalt M cfg = false)
    (hentry : M c cfg.q cfg.Tape.head = none) :
    coinReceiptAux M accept (c :: cs) cfg lo hi d
      = ⟨some (accept cfg.q), 1, 0, (hi - lo + 1).toNat⟩ := by
  have hne : ¬(coinHalt M cfg = true) := by simp [hc]
  simp only [coinReceiptAux, if_neg hne, hentry]

theorem coinReceiptAux_cons_some {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) (c : Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) (cs : List Bool) (lo hi d : ℤ) (q' : Λ)
    (stmt : Turing.TM0.Stmt Γ)
    (hc : coinHalt M cfg = false)
    (hentry : M c cfg.q cfg.Tape.head = some (q', stmt)) :
    coinReceiptAux M accept (c :: cs) cfg lo hi d
      = CoinReceipt.bump
          (coinReceiptAux M accept cs ⟨q', TM0StmtApply cfg.Tape stmt⟩
            (stmtExtent stmt lo hi d).1 (stmtExtent stmt lo hi d).2.1
            (stmtExtent stmt lo hi d).2.2) := by
  have hne : ¬(coinHalt M cfg = true) := by simp [hc]
  simp only [coinReceiptAux, if_neg hne, hentry]

theorem coinReceiptAux_agree {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) (lo hi d : ℤ) (_hlo : lo ≤ d)
      (_hhi : d ≤ hi),
      (coinReceiptAux M accept coins cfg lo hi d).output
          = (coinTapeRunAux M accept coins cfg).1
        ∧ (coinReceiptAux M accept coins cfg lo hi d).reads
          = (coinTapeRunAux M accept coins cfg).2
        ∧ (coinReceiptAux M accept coins cfg lo hi d).clock
          = coinTapeTransitionCountAux M coins cfg
        ∧ 1 ≤ (coinReceiptAux M accept coins cfg lo hi d).peak := by
  intro coins
  induction coins with
  | nil =>
      intro cfg lo hi d hlo hhi
      simp only [coinReceiptAux, coinTapeRunAux, coinTapeTransitionCountAux]
      split
      · exact ⟨by trivial, by trivial, by trivial, one_le_toNat_of_one_le (by omega)⟩
      · exact ⟨by trivial, by trivial, by trivial, one_le_toNat_of_one_le (by omega)⟩
  | cons c cs ih =>
      intro cfg lo hi d hlo hhi
      by_cases hcf : coinHalt M cfg = false
      · have hne : ¬(coinHalt M cfg = true) := by simp [hcf]
        match hentry : M c cfg.q cfg.Tape.head with
        | none =>
            have hs : Turing.TM0.step (M c) cfg = none := by
              rw [TM0_step_apply, hentry]; rfl
            have hrun : coinTapeRunAux M accept (c :: cs) cfg = (some (accept cfg.q), 1) := by
              rw [coinTapeRunAux, if_neg hne, hs]
            have hcount : coinTapeTransitionCountAux M (c :: cs) cfg = 0 := by
              rw [coinTapeTransitionCountAux, if_neg hne, hs]
            rw [coinReceiptAux_cons_none M accept c cfg cs lo hi d hcf hentry,
              hrun, hcount]
            exact ⟨rfl, rfl, rfl, one_le_toNat_of_one_le (by omega)⟩
        | some (q', stmt) =>
            have hstep : Turing.TM0.step (M c) cfg
                = some ⟨q', TM0StmtApply cfg.Tape stmt⟩ :=
              TM0_step_eq_some (M c) cfg q' stmt hentry
            have hinv := stmtExtent_inv stmt hlo hhi
            obtain ⟨h1, h2, h3, h4⟩ :=
              ih ⟨q', TM0StmtApply cfg.Tape stmt⟩ (stmtExtent stmt lo hi d).1
                (stmtExtent stmt lo hi d).2.1 (stmtExtent stmt lo hi d).2.2 hinv.1 hinv.2
            have hrun := coinTapeRunAux_cons_live (M := M) (accept := accept) (cs := cs)
              hcf (q' := q') (T' := TM0StmtApply cfg.Tape stmt) hstep
            have hcount : coinTapeTransitionCountAux M (c :: cs) cfg
                = coinTapeTransitionCountAux M cs ⟨q', TM0StmtApply cfg.Tape stmt⟩ + 1 := by
              rw [coinTapeTransitionCountAux, if_neg hne, hstep]
            rw [coinReceiptAux_cons_some M accept c cfg cs lo hi d q' stmt hcf hentry,
              CoinReceipt.bump, h1, h2, h3, hrun, hcount]
            rw [Prod.map_fst, Prod.map_snd]
            exact ⟨rfl, rfl, rfl, h4⟩
      · have hc : coinHalt M cfg = true := by
          cases hh : coinHalt M cfg with
          | true => rfl
          | false => exact absurd hh hcf
        rw [coinReceiptAux_cons_halt M accept c cfg cs lo hi d hc]
        have hrun : coinTapeRunAux M accept (c :: cs) cfg = (some (accept cfg.q), 0) := by
          rw [coinTapeRunAux, hc, if_pos (rfl : (true : Bool) = true)]
        have hcount : coinTapeTransitionCountAux M (c :: cs) cfg = 0 := by
          rw [coinTapeTransitionCountAux, hc, if_pos (rfl : (true : Bool) = true)]
        rw [hrun, hcount]
        exact ⟨rfl, rfl, rfl, one_le_toNat_of_one_le (by omega)⟩

theorem coinReceiptAux_peak_le {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) :
    ∀ (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) (lo hi d : ℤ) (_hlo : lo ≤ d)
      (_hhi : d ≤ hi),
      (coinReceiptAux M accept coins cfg lo hi d).peak
        ≤ (hi - lo + 1).toNat + (coinReceiptAux M accept coins cfg lo hi d).clock := by
  intro coins
  induction coins with
  | nil => intro cfg lo hi d _hlo _hhi; simp only [coinReceiptAux]; omega
  | cons c cs ih =>
      intro cfg lo hi d hlo hhi
      by_cases hcf : coinHalt M cfg = false
      · have hne : ¬(coinHalt M cfg = true) := by simp [hcf]
        match hentry : M c cfg.q cfg.Tape.head with
        | none =>
            rw [coinReceiptAux_cons_none M accept c cfg cs lo hi d hcf hentry]
            have hp : (⟨some (accept cfg.q), 1, 0, (hi - lo + 1).toNat⟩ :
                CoinReceipt).peak = (hi - lo + 1).toNat := rfl
            have hck : (⟨some (accept cfg.q), 1, 0, (hi - lo + 1).toNat⟩ :
                CoinReceipt).clock = 0 := rfl
            rw [hp, hck]
            omega
        | some (q', stmt) =>
            have hinv := stmtExtent_inv stmt hlo hhi
            have hrange := stmtExtent_range stmt hlo hhi
            have h := ih ⟨q', TM0StmtApply cfg.Tape stmt⟩ (stmtExtent stmt lo hi d).1
              (stmtExtent stmt lo hi d).2.1 (stmtExtent stmt lo hi d).2.2 hinv.1 hinv.2
            rw [coinReceiptAux_cons_some M accept c cfg cs lo hi d q' stmt hcf hentry]
            obtain ⟨hp, hck⟩ := CoinReceipt.bump_peak_clock (coinReceiptAux M accept cs
              ⟨q', TM0StmtApply cfg.Tape stmt⟩ (stmtExtent stmt lo hi d).1
              (stmtExtent stmt lo hi d).2.1 (stmtExtent stmt lo hi d).2.2)
            rw [hp, hck]
            omega
      · have hc : coinHalt M cfg = true := by
          cases hh : coinHalt M cfg with
          | true => rfl
          | false => exact absurd hh hcf
        rw [coinReceiptAux_cons_halt M accept c cfg cs lo hi d hc]
        have hp : (⟨some (accept cfg.q), 0, 0, (hi - lo + 1).toNat⟩ :
            CoinReceipt).peak = (hi - lo + 1).toNat := rfl
        have hck : (⟨some (accept cfg.q), 0, 0, (hi - lo + 1).toNat⟩ :
            CoinReceipt).clock = 0 := rfl
        rw [hp, hck]
        omega

theorem coinReceiptRun_agree {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (accept : Λ → Bool) (input : List Γ)
    (coins : List Bool) :
    (coinReceiptRun M accept input coins).output = (coinTapeRun M accept input coins).1
      ∧ (coinReceiptRun M accept input coins).reads = (coinTapeRun M accept input coins).2
      ∧ (coinReceiptRun M accept input coins).clock = coinTapeTransitionCount M input coins
      ∧ 1 ≤ (coinReceiptRun M accept input coins).peak := by
  have h := coinReceiptAux_agree M accept coins (Turing.TM0.init input) 0 0 0
    (by omega) (by omega)
  simpa only [coinReceiptRun, coinTapeRun, coinTapeTransitionCount] using! h

def raceStep (N : ℕ) (p : ℕ) (c : Bool) : ℕ :=
  if p = 0 ∨ p = N then p else if c = true then p + 1 else p - 1

def raceWalk (N : ℕ) (p : ℕ) : List Bool → ℕ
  | [] => p
  | c :: w => raceWalk N (raceStep N p c) w

def raceTime (N : ℕ) (p : ℕ) : List Bool → ℕ
  | [] => 0
  | c :: w => if p = 0 ∨ p = N then 0 else raceTime N (raceStep N p c) w + 1

theorem raceStep_absorb (N : ℕ) {p : ℕ} (c : Bool) (hp : p = 0 ∨ p = N) :
    raceStep N p c = p := by
  rw [raceStep, if_pos hp]

theorem raceWalk_le (N : ℕ) : ∀ (w : List Bool) {p : ℕ}, p ≤ N → raceWalk N p w ≤ N := by
  intro w
  induction w with
  | nil => intro p h; exact h
  | cons c w ih =>
      intro p h
      rw [raceWalk]
      refine ih ?_
      by_cases hp : p = 0 ∨ p = N
      · rw [raceStep_absorb N c hp]; exact h
      · have h1 : p ≠ 0 := fun e => hp (Or.inl e)
        have h2 : p ≠ N := fun e => hp (Or.inr e)
        by_cases hc : c = true
        · rw [raceStep, if_neg hp, if_pos hc]; omega
        · rw [raceStep, if_neg hp, if_neg hc]; omega

theorem raceWalk_absorb_stay (N : ℕ) (p : ℕ) (w : List Bool) (hp : p = 0 ∨ p = N) :
    raceWalk N p w = p := by
  induction w generalizing p with
  | nil => rfl
  | cons c w ih => rw [raceWalk, raceStep_absorb N c hp]; exact ih _ hp

theorem raceTime_absorb_zero (N : ℕ) (p : ℕ) (w : List Bool) (hp : p = 0 ∨ p = N) :
    raceTime N p w = 0 := by
  induction w generalizing p with
  | nil => rfl
  | cons c w ih => rw [raceTime, if_pos hp]

theorem raceWalk_append (N : ℕ) (p : ℕ) (u v : List Bool) :
    raceWalk N p (u ++ v) = raceWalk N (raceWalk N p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons c u ih =>
      rw [List.cons_append, raceWalk, ih]
      rfl

def raceLabelL (N a : ℕ) : ℕ := (N + 1 - a) % (N + 1)

def raceLabelR (N a : ℕ) : ℕ := (N - a) % (N + 1)

def raceWall (N a : ℕ) (ℓ : ℕ) : Bool := decide (ℓ = raceLabelL N a ∨ ℓ = raceLabelR N a)

def racePosOf (N a : ℕ) (ℓ : ℕ) : ℕ := (ℓ + a) % (N + 1)

def raceRotStep (N : ℕ) (ℓ : ℕ) (c : Bool) : ℕ := (ℓ + (if c then 1 else N)) % (N + 1)

def raceNext (N : ℕ) (ℓ : ℕ) (c : Bool) : Fin (N + 1) :=
  ⟨raceRotStep N ℓ c, Nat.mod_lt _ (Nat.succ_pos N)⟩

theorem raceLabelL_lt (N a : ℕ) : raceLabelL N a < N + 1 :=
  Nat.mod_lt _ (Nat.succ_pos N)

theorem raceLabelR_lt (N a : ℕ) : raceLabelR N a < N + 1 :=
  Nat.mod_lt _ (Nat.succ_pos N)

theorem racePosOf_lt (N a : ℕ) (ℓ : ℕ) : racePosOf N a ℓ < N + 1 :=
  Nat.mod_lt _ (Nat.succ_pos N)

theorem racePosOf_wallL (N a : ℕ) (ha : a ≤ N) : racePosOf N a (raceLabelL N a) = 0 := by
  rcases Nat.eq_zero_or_pos a with h0 | h1
  · subst h0
    simp [racePosOf, raceLabelL]
  · have hlt : N + 1 - a < N + 1 := by omega
    simp only [racePosOf, raceLabelL, Nat.mod_eq_of_lt hlt]
    have h : N + 1 - a + a = N + 1 := by omega
    rw [h, Nat.mod_self]

theorem racePosOf_wallR (N a : ℕ) (ha : a ≤ N) : racePosOf N a (raceLabelR N a) = N := by
  rcases Nat.eq_zero_or_pos a with h0 | h1
  · subst h0
    simp [racePosOf, raceLabelR]
  · have hlt : N - a < N + 1 := by omega
    simp only [racePosOf, raceLabelR, Nat.mod_eq_of_lt hlt]
    have h : N - a + a = N := by omega
    rw [h]
    exact Nat.mod_eq_of_lt (by omega)

theorem racePosOf_zero (N a : ℕ) (ha : a ≤ N) : racePosOf N a 0 = a := by
  show (0 + a) % (N + 1) = a
  rw [Nat.zero_add]
  exact Nat.mod_eq_of_lt (by omega)

theorem racePosOf_inj (N a : ℕ) {ℓ₁ ℓ₂ : ℕ} (h₁ : ℓ₁ < N + 1) (h₂ : ℓ₂ < N + 1)
    (h : racePosOf N a ℓ₁ = racePosOf N a ℓ₂) : ℓ₁ = ℓ₂ := by
  have hmod : (ℓ₁ + a) ≡ (ℓ₂ + a) [MOD N + 1] := h
  have hEq : ℓ₁ % (N + 1) = ℓ₂ % (N + 1) :=
    Nat.ModEq.add_right_cancel' a hmod
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hEq

theorem racePosOf_eq_zero_iff (N a : ℕ) (ha : a ≤ N) {ℓ : ℕ} (hℓ : ℓ < N + 1) :
    racePosOf N a ℓ = 0 ↔ ℓ = raceLabelL N a :=
  ⟨fun h => racePosOf_inj N a hℓ (raceLabelL_lt N a)
    (by rw [h, racePosOf_wallL N a ha]),
   fun h => by rw [h, racePosOf_wallL N a ha]⟩

theorem racePosOf_eq_N_iff (N a : ℕ) (ha : a ≤ N) {ℓ : ℕ} (hℓ : ℓ < N + 1) :
    racePosOf N a ℓ = N ↔ ℓ = raceLabelR N a :=
  ⟨fun h => racePosOf_inj N a hℓ (raceLabelR_lt N a)
    (by rw [h, racePosOf_wallR N a ha]),
   fun h => by rw [h, racePosOf_wallR N a ha]⟩

theorem raceWall_iff (N a : ℕ) (ha : a ≤ N) {ℓ : ℕ} (hℓ : ℓ < N + 1) :
    raceWall N a ℓ = true ↔ racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := by
  constructor
  · intro h
    simp only [raceWall, decide_eq_true_eq] at h
    rcases h with h | h
    · exact Or.inl (by rw [h, racePosOf_wallL N a ha])
    · exact Or.inr (by rw [h, racePosOf_wallR N a ha])
  · intro h
    simp only [raceWall, decide_eq_true_eq]
    rcases h with h | h
    · exact Or.inl ((racePosOf_eq_zero_iff N a ha hℓ).mp h)
    · exact Or.inr ((racePosOf_eq_N_iff N a ha hℓ).mp h)

theorem racePosOf_add (N a k : ℕ) (ℓ : ℕ) :
    racePosOf N a ((ℓ + k) % (N + 1)) = (racePosOf N a ℓ + k) % (N + 1) := by
  simp only [racePosOf]
  rw [Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem racePosOf_rotStep (N a : ℕ) (ha : a ≤ N) {ℓ : ℕ} (hℓ : ℓ < N + 1)
    (hwall : raceWall N a ℓ = false) (c : Bool) :
    racePosOf N a (raceRotStep N ℓ c) = raceStep N (racePosOf N a ℓ) c := by
  have hiff := raceWall_iff N a ha hℓ
  have hni : ¬(racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N) := by
    intro h
    rw [hiff.mpr h] at hwall
    simp at hwall
  have hp1 : 1 ≤ racePosOf N a ℓ := by
    rcases Nat.eq_zero_or_pos (racePosOf N a ℓ) with h0 | hpos
    · exact absurd (Or.inl h0) hni
    · omega
  have hlt : racePosOf N a ℓ + 1 ≤ N := by
    have h9 := racePosOf_lt N a ℓ
    have hN : racePosOf N a ℓ ≠ N := fun h => hni (Or.inr h)
    omega
  cases c with
  | true =>
      have hm : raceRotStep N ℓ true = (ℓ + 1) % (N + 1) := rfl
      rw [hm, racePosOf_add, Nat.mod_eq_of_lt (show racePosOf N a ℓ + 1 < N + 1 by omega),
        raceStep, if_neg hni]
      rfl
  | false =>
      have hstep : raceStep N (racePosOf N a ℓ) false = racePosOf N a ℓ - 1 := by
        rw [raceStep, if_neg hni]
        rfl
      have hm : raceRotStep N ℓ false = (ℓ + N) % (N + 1) := rfl
      rw [hm, racePosOf_add, hstep]
      have hsplit : racePosOf N a ℓ + N = racePosOf N a ℓ - 1 + (N + 1) := by omega
      rw [hsplit, Nat.add_comm, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (show racePosOf N a ℓ - 1 < N + 1 by omega)

def raceMachine (N a : ℕ) : Bool → Turing.TM0.Machine (Option Bool) (Fin (N + 1)) :=
  fun c q _ =>
    if _h : q.val = raceLabelL N a ∨ q.val = raceLabelR N a then none
    else some (raceNext N q.val c,
      Turing.TM0.Stmt.move (if c then Turing.Dir.right else Turing.Dir.left))

def raceAccept (N a : ℕ) (q : Fin (N + 1)) : Bool := decide (q.val = raceLabelR N a)

def raceCode (N a : ℕ) : Code := encodeMachine N (raceMachine N a) (raceAccept N a)

theorem race_coinHalt (N a : ℕ) (q : Fin (N + 1)) (T : Turing.Tape (Option Bool)) :
    coinHalt (raceMachine N a) ⟨q, T⟩ = raceWall N a q.val := by
  unfold coinHalt raceMachine raceWall
  by_cases h : q.val = raceLabelL N a ∨ q.val = raceLabelR N a
  · rw [dif_pos h, dif_pos h]; simp [h]
  · rw [dif_neg h, dif_neg h]; simp [h]

theorem race_entry_some (N a : ℕ) (c : Bool) (q : Fin (N + 1))
    (T : Turing.Tape (Option Bool))
    (hni : ¬ (q.val = raceLabelL N a ∨ q.val = raceLabelR N a)) :
    raceMachine N a c q T.head = some (raceNext N q.val c,
      Turing.TM0.Stmt.move (if c then Turing.Dir.right else Turing.Dir.left)) := by
  simp only [raceMachine]
  rw [dif_neg hni]

theorem race_step_some (N a : ℕ) (c : Bool) (q : Fin (N + 1))
    (T : Turing.Tape (Option Bool))
    (hni : ¬ (q.val = raceLabelL N a ∨ q.val = raceLabelR N a)) :
    Turing.TM0.step (raceMachine N a c) ⟨q, T⟩
      = some ⟨raceNext N q.val c,
          TM0StmtApply T (Turing.TM0.Stmt.move
            (if c then Turing.Dir.right else Turing.Dir.left))⟩ :=
  TM0_step_eq_some _ _ _ _ (race_entry_some N a c q T hni)

def raceLabelFold (N a : ℕ) (ℓ : ℕ) : List Bool → ℕ
  | [] => ℓ
  | c :: w => raceLabelFold N a (if raceWall N a ℓ then ℓ else raceRotStep N ℓ c) w

def raceCfgStep (N a : ℕ) (c : Bool) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (N + 1))) :
    Turing.TM0.Cfg (Option Bool) (Fin (N + 1)) :=
  if raceWall N a cfg.q.val then cfg
  else
    match raceMachine N a c cfg.q cfg.Tape.head with
    | some (q', stmt) => ⟨q', TM0StmtApply cfg.Tape stmt⟩
    | none => cfg

def raceCfgFold (N a : ℕ) : List Bool → Turing.TM0.Cfg (Option Bool) (Fin (N + 1)) →
    Turing.TM0.Cfg (Option Bool) (Fin (N + 1))
  | [], cfg => cfg
  | c :: w, cfg => raceCfgFold N a w (raceCfgStep N a c cfg)

theorem raceCfgStep_wall (N a : ℕ) (c : Bool)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin (N + 1)))
    (hw : raceWall N a cfg.q.val = true) :
    raceCfgStep N a c cfg = cfg := by
  simp only [raceCfgStep]
  rw [if_pos (show raceWall N a cfg.q.val = true by exact hw)]

theorem raceCfgStep_live (N a : ℕ) (c : Bool)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin (N + 1)))
    (hni : ¬(cfg.q.val = raceLabelL N a ∨ cfg.q.val = raceLabelR N a)) :
    raceCfgStep N a c cfg
      = ⟨raceNext N cfg.q.val c,
          TM0StmtApply cfg.Tape (Turing.TM0.Stmt.move
            (if c then Turing.Dir.right else Turing.Dir.left))⟩ := by
  have hw : ¬(raceWall N a cfg.q.val = true) := fun h => hni (by
    simp only [raceWall, decide_eq_true_eq] at h
    exact h)
  simp only [raceCfgStep]
  rw [if_neg hw, race_entry_some N a c cfg.q cfg.Tape hni]

theorem raceCfgFold_nil (N a : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (N + 1))) :
    raceCfgFold N a [] cfg = cfg := rfl

theorem raceCfgFold_cons (N a : ℕ) (c : Bool) (w : List Bool)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin (N + 1))) :
    raceCfgFold N a (c :: w) cfg = raceCfgFold N a w (raceCfgStep N a c cfg) := rfl

theorem raceLabelFold_lt (N a : ℕ) : ∀ (w : List Bool) {ℓ : ℕ}, ℓ < N + 1 →
    raceLabelFold N a ℓ w < N + 1 := by
  intro w
  induction w with
  | nil => intro ℓ h; exact h
  | cons c w ih =>
      intro ℓ h
      simp only [raceLabelFold]
      split
      · exact ih h
      · exact ih (Nat.mod_lt _ (Nat.succ_pos N))

theorem raceCfgFold_val (N a : ℕ) : ∀ (w : List Bool)
    (cfg : Turing.TM0.Cfg (Option Bool) (Fin (N + 1))),
    (raceCfgFold N a w cfg).q.val = raceLabelFold N a cfg.q.val w := by
  intro w
  induction w with
  | nil => intro cfg; rfl
  | cons c w ih =>
      intro cfg
      by_cases hw : raceWall N a cfg.q.val = true
      · rw [raceCfgFold_cons, raceCfgStep_wall N a c cfg hw, raceLabelFold, if_pos hw]
        exact ih cfg
      · have hni : ¬(cfg.q.val = raceLabelL N a ∨ cfg.q.val = raceLabelR N a) := by
          intro h
          apply hw
          simp only [raceWall, decide_eq_true_eq]
          exact h
        rw [raceCfgFold_cons, raceCfgStep_live N a c cfg hni, raceLabelFold, if_neg hw]
        exact ih _

theorem racePosOf_raceLabelFold (N a : ℕ) (ha : a ≤ N) : ∀ (w : List Bool) {ℓ : ℕ},
    ℓ < N + 1 →
    racePosOf N a (raceLabelFold N a ℓ w) = raceWalk N (racePosOf N a ℓ) w := by
  intro w
  induction w with
  | nil => intro ℓ _; rfl
  | cons c w ih =>
      intro ℓ hℓ
      have hiff := raceWall_iff N a ha hℓ
      by_cases hwall : raceWall N a ℓ = true
      · have habs : racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := hiff.mp hwall
        rw [raceWalk, raceStep_absorb N c habs, raceLabelFold, if_pos hwall, ih hℓ,
          raceWalk_absorb_stay N (racePosOf N a ℓ) w habs]
      · rw [raceWalk, raceLabelFold, if_neg hwall]
        have hwf : raceWall N a ℓ = false := by
          cases hh : raceWall N a ℓ with
          | false => rfl
          | true => exact absurd hh hwall
        have ih2 := ih (ℓ := raceRotStep N ℓ c) (Nat.mod_lt _ (Nat.succ_pos N))
        rw [ih2, racePosOf_rotStep N a ha hℓ hwf c]

theorem raceCfgFold_absorb_stay (N a : ℕ) (T : Turing.Tape (Option Bool)) {ℓ : ℕ}
    (hℓ : ℓ < N + 1) (hw : raceWall N a ℓ = true) (w : List Bool) :
    raceCfgFold N a w ⟨⟨ℓ, hℓ⟩, T⟩ = ⟨⟨ℓ, hℓ⟩, T⟩ := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      rw [raceCfgFold_cons, raceCfgStep_wall N a c ⟨⟨ℓ, hℓ⟩, T⟩ hw]
      exact ih

theorem race_coinTapeRunAux (N a : ℕ) (ha : a ≤ N) : ∀ (w : List Bool)
    (T : Turing.Tape (Option Bool)) (ℓ : ℕ) (hℓ : ℓ < N + 1),
    coinTapeRunAux (raceMachine N a) (raceAccept N a) w ⟨⟨ℓ, hℓ⟩, T⟩
      = (if raceWalk N (racePosOf N a ℓ) w = 0 ∨ raceWalk N (racePosOf N a ℓ) w = N
           then some (decide (raceWalk N (racePosOf N a ℓ) w = N))
           else none,
         raceTime N (racePosOf N a ℓ) w) := by
  intro w
  induction w with
  | nil =>
      intro T ℓ hℓ
      have hiff := raceWall_iff N a ha hℓ
      have hacc : raceAccept N a ⟨ℓ, hℓ⟩ = decide (racePosOf N a ℓ = N) := by
        show decide (ℓ = raceLabelR N a) = decide (racePosOf N a ℓ = N)
        by_cases h : racePosOf N a ℓ = N
        · rw [(racePosOf_eq_N_iff N a ha hℓ).mp h, racePosOf_wallR N a ha]
          simp
        · have h' : ℓ ≠ raceLabelR N a := fun hl => h (by rw [hl, racePosOf_wallR N a ha])
          simp [h, h']
      rw [coinTapeRunAux, race_coinHalt N a ⟨ℓ, hℓ⟩ T]
      by_cases hwall : raceWall N a ℓ = true
      · have habs : racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := hiff.mp hwall
        rw [if_pos hwall, raceWalk, raceTime, if_pos habs, hacc]
      · have hni : ¬(racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N) :=
          fun h => hwall (hiff.mpr h)
        rw [if_neg hwall, raceWalk, raceTime, if_neg hni]
  | cons c w ih =>
      intro T ℓ hℓ
      have hiff := raceWall_iff N a ha hℓ
      have hacc : raceAccept N a ⟨ℓ, hℓ⟩ = decide (racePosOf N a ℓ = N) := by
        show decide (ℓ = raceLabelR N a) = decide (racePosOf N a ℓ = N)
        by_cases h : racePosOf N a ℓ = N
        · rw [(racePosOf_eq_N_iff N a ha hℓ).mp h, racePosOf_wallR N a ha]
          simp
        · have h' : ℓ ≠ raceLabelR N a := fun hl => h (by rw [hl, racePosOf_wallR N a ha])
          simp [h, h']
      rw [coinTapeRunAux, race_coinHalt N a ⟨ℓ, hℓ⟩ T]
      by_cases hwall : raceWall N a ℓ = true
      · have habs : racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := hiff.mp hwall
        rw [if_pos hwall, raceWalk, raceStep_absorb N c habs, raceTime, if_pos habs,
            raceWalk_absorb_stay N (racePosOf N a ℓ) w habs, if_pos habs, hacc]
      · have hni : ¬(racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N) :=
          fun h => hwall (hiff.mpr h)
        have hni' : ¬(ℓ = raceLabelL N a ∨ ℓ = raceLabelR N a) := by
          intro h
          rcases h with h | h
          · rw [h] at hwall; simp [raceWall] at hwall
          · rw [h] at hwall; simp [raceWall] at hwall
        rw [if_neg hwall]
        have hs := race_step_some N a c ⟨ℓ, hℓ⟩ T hni'
        simp only [hs, raceNext]
        have hwf : raceWall N a ℓ = false := by
          cases hh : raceWall N a ℓ with
          | false => rfl
          | true => exact absurd hh hwall
        have ih2 := ih (TM0StmtApply T (Turing.TM0.Stmt.move
            (if c then Turing.Dir.right else Turing.Dir.left)))
          (raceRotStep N ℓ c) (Nat.mod_lt _ (Nat.succ_pos N))
        rw [ih2, racePosOf_rotStep N a ha hℓ hwf c]
        simp only [Prod.map, id_eq]
        rw [raceWalk, raceTime, if_neg hni]

theorem race_coinTapeTransitionCountAux (N a : ℕ) (ha : a ≤ N) : ∀ (w : List Bool)
    (T : Turing.Tape (Option Bool)) (ℓ : ℕ) (hℓ : ℓ < N + 1),
    coinTapeTransitionCountAux (raceMachine N a) w ⟨⟨ℓ, hℓ⟩, T⟩
      = raceTime N (racePosOf N a ℓ) w := by
  intro w
  induction w with
  | nil => intro T ℓ hℓ; rfl
  | cons c w ih =>
      intro T ℓ hℓ
      have hiff := raceWall_iff N a ha hℓ
      rw [coinTapeTransitionCountAux, race_coinHalt N a ⟨ℓ, hℓ⟩ T]
      by_cases hwall : raceWall N a ℓ = true
      · have habs : racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := hiff.mp hwall
        rw [if_pos hwall, raceTime, if_pos habs]
      · have hni : ¬(racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N) :=
          fun h => hwall (hiff.mpr h)
        have hni' : ¬(ℓ = raceLabelL N a ∨ ℓ = raceLabelR N a) := by
          intro h
          rcases h with h | h
          · rw [h] at hwall; simp [raceWall] at hwall
          · rw [h] at hwall; simp [raceWall] at hwall
        rw [if_neg hwall]
        have hs := race_step_some N a c ⟨ℓ, hℓ⟩ T hni'
        simp only [hs, raceNext]
        have hwf : raceWall N a ℓ = false := by
          cases hh : raceWall N a ℓ with
          | false => rfl
          | true => exact absurd hh hwall
        have ih2 := ih (TM0StmtApply T (Turing.TM0.Stmt.move
            (if c then Turing.Dir.right else Turing.Dir.left)))
          (raceRotStep N ℓ c) (Nat.mod_lt _ (Nat.succ_pos N))
        rw [ih2, racePosOf_rotStep N a ha hℓ hwf c, raceTime, if_neg hni]

theorem race_coinConfigRunAux (N a : ℕ) (ha : a ≤ N) : ∀ (w : List Bool)
    (T : Turing.Tape (Option Bool)) (ℓ : ℕ) (hℓ : ℓ < N + 1),
    (coinConfigRunAux (raceMachine N a) w ⟨⟨ℓ, hℓ⟩, T⟩).reads
      = raceTime N (racePosOf N a ℓ) w ∧
    (coinConfigRunAux (raceMachine N a) w ⟨⟨ℓ, hℓ⟩, T⟩).stopped
      = if raceWalk N (racePosOf N a ℓ) w = 0 ∨ raceWalk N (racePosOf N a ℓ) w = N
        then some (raceCfgFold N a w ⟨⟨ℓ, hℓ⟩, T⟩) else none := by
  intro w
  induction w with
  | nil =>
      intro T ℓ hℓ
      have hiff := raceWall_iff N a ha hℓ
      rw [coinConfigRunAux, race_coinHalt N a ⟨ℓ, hℓ⟩ T]
      by_cases hwall : raceWall N a ℓ = true
      · have habs : racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := hiff.mp hwall
        rw [if_pos hwall, raceWalk, raceTime, if_pos habs]
        exact ⟨rfl, rfl⟩
      · have hni : ¬(racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N) :=
          fun h => hwall (hiff.mpr h)
        rw [if_neg hwall, raceWalk, raceTime, if_neg hni]
        exact ⟨rfl, rfl⟩
  | cons c w ih =>
      intro T ℓ hℓ
      have hiff := raceWall_iff N a ha hℓ
      rw [coinConfigRunAux, race_coinHalt N a ⟨ℓ, hℓ⟩ T]
      by_cases hwall : raceWall N a ℓ = true
      · have habs : racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N := hiff.mp hwall
        rw [if_pos hwall]
        rw [raceWalk, raceStep_absorb N c habs,
            raceWalk_absorb_stay N (racePosOf N a ℓ) w habs]
        rw [raceCfgFold_cons, raceCfgStep_wall N a c ⟨⟨ℓ, hℓ⟩, T⟩ hwall,
          raceCfgFold_absorb_stay N a T hℓ hwall w, if_pos habs]
        rw [raceTime, if_pos habs]
        exact ⟨rfl, rfl⟩
      · have hni : ¬(racePosOf N a ℓ = 0 ∨ racePosOf N a ℓ = N) :=
          fun h => hwall (hiff.mpr h)
        have hni' : ¬(ℓ = raceLabelL N a ∨ ℓ = raceLabelR N a) := by
          intro h
          rcases h with h | h
          · rw [h] at hwall; simp [raceWall] at hwall
          · rw [h] at hwall; simp [raceWall] at hwall
        rw [if_neg hwall]
        have hs := race_step_some N a c ⟨ℓ, hℓ⟩ T hni'
        simp only [hs, raceNext]
        have hwf : raceWall N a ℓ = false := by
          cases hh : raceWall N a ℓ with
          | false => rfl
          | true => exact absurd hh hwall
        have ih2 := ih (TM0StmtApply T (Turing.TM0.Stmt.move
            (if c then Turing.Dir.right else Turing.Dir.left)))
          (raceRotStep N ℓ c) (Nat.mod_lt _ (Nat.succ_pos N))
        obtain ⟨hr1, hs1⟩ := ih2
        have hcf : raceCfgFold N a (c :: w) ⟨⟨ℓ, hℓ⟩, T⟩
            = raceCfgFold N a w ⟨⟨raceRotStep N ℓ c, Nat.mod_lt _ (Nat.succ_pos N)⟩,
                TM0StmtApply T (Turing.TM0.Stmt.move
                  (if c then Turing.Dir.right else Turing.Dir.left))⟩ := by
          rw [raceCfgFold_cons, raceCfgStep_live N a c ⟨⟨ℓ, hℓ⟩, T⟩ hni']
          rfl
        rw [hr1, hs1, hcf, racePosOf_rotStep N a ha hℓ hwf c]
        rw [raceWalk, raceTime, if_neg hni]
        exact ⟨rfl, rfl⟩

theorem race_commonHalt (N a : ℕ) : commonHalt (raceCode N a) := by
  intro q sym
  have htable : table (raceCode N a) = raceMachine N a := table_encode N _ _
  rw [htable]
  simp only [raceMachine]
  by_cases h : q.val = raceLabelL N a ∨ q.val = raceLabelR N a
  · simp [h]
  · simp [h]

def raceSourceInit (N : ℕ) : Turing.TM0.Cfg (Option Bool) (Fin (N + 1)) :=
  ⟨default, (phaseCopyResult []).map phaseWorkMap⟩

theorem raceSourceInit_label (N : ℕ) : (raceSourceInit N).q.val = 0 := rfl

theorem race_readout_final (N a : ℕ) (ha : a ≤ N) (w : List Bool) :
    readout (raceCode N a) (raceCfgFold N a w (raceSourceInit N)).q
      = decide (raceWalk N a w = N) := by
  show readout (encodeMachine N (raceMachine N a) (raceAccept N a))
      (raceCfgFold N a w (raceSourceInit N)).q = decide (raceWalk N a w = N)
  rw [readout_encode_eq]
  simp only [raceAccept, raceCfgFold_val]
  have hlt : (raceSourceInit N).q.val < N + 1 := by
    rw [raceSourceInit_label]; omega
  have hfl := raceLabelFold_lt N a w hlt
  have hpos : racePosOf N a (raceLabelFold N a (raceSourceInit N).q.val w)
      = raceWalk N a w := by
    have h := racePosOf_raceLabelFold N a ha w hlt
    rw [raceSourceInit_label, racePosOf_zero N a ha] at h
    exact h
  by_cases h : raceWalk N a w = N
  · have hN : racePosOf N a (raceLabelFold N a (raceSourceInit N).q.val w) = N :=
      hpos.trans h
    rw [(racePosOf_eq_N_iff N a ha hfl).mp hN, h]
    simp
  · have hR : raceLabelFold N a (raceSourceInit N).q.val w ≠ raceLabelR N a := by
      intro hl
      apply h
      rw [← hpos, hl, racePosOf_wallR N a ha]
    simp [h, hR]

theorem race_coinTapeRunAux_init (N a : ℕ) (ha : a ≤ N) (w : List Bool) :
    coinTapeRunAux (raceMachine N a) (raceAccept N a) w
        (Turing.TM0.init ([] : List (Option Bool)))
      = (if raceWalk N a w = 0 ∨ raceWalk N a w = N
           then some (decide (raceWalk N a w = N)) else none,
         raceTime N a w) := by
  have h := race_coinTapeRunAux N a ha w (Turing.Tape.mk₁ []) 0 (by omega)
  rw [racePosOf_zero N a ha] at h
  exact h

theorem race_coinTapeTransitionCountAux_init (N a : ℕ) (ha : a ≤ N) (w : List Bool) :
    coinTapeTransitionCountAux (raceMachine N a) w
        (Turing.TM0.init ([] : List (Option Bool)))
      = raceTime N a w := by
  have h := race_coinTapeTransitionCountAux N a ha w (Turing.Tape.mk₁ []) 0 (by omega)
  rw [racePosOf_zero N a ha] at h
  exact h

theorem race_receipt_run (N a : ℕ) (ha : a ≤ N) (w : List Bool) :
    (coinReceiptRun (raceMachine N a) (raceAccept N a) [] w).output
      = (if raceWalk N a w = 0 ∨ raceWalk N a w = N
           then some (decide (raceWalk N a w = N)) else none)
      ∧ (coinReceiptRun (raceMachine N a) (raceAccept N a) [] w).reads
        = raceTime N a w
      ∧ (coinReceiptRun (raceMachine N a) (raceAccept N a) [] w).clock
        = raceTime N a w
      ∧ (coinReceiptRun (raceMachine N a) (raceAccept N a) [] w).peak
        ≤ raceTime N a w + 1
      ∧ 1 ≤ (coinReceiptRun (raceMachine N a) (raceAccept N a) [] w).peak := by
  obtain ⟨h1, h2, h3, h4⟩ := coinReceiptRun_agree (raceMachine N a) (raceAccept N a) [] w
  simp only [coinTapeRun, coinTapeTransitionCount] at h1 h2 h3
  rw [h1, h2, h3, race_coinTapeRunAux_init N a ha w,
    race_coinTapeTransitionCountAux_init N a ha w]
  refine ⟨rfl, rfl, rfl, ?_, h4⟩
  have hagree := coinReceiptAux_agree (raceMachine N a) (raceAccept N a) w
    (Turing.TM0.init ([] : List (Option Bool))) 0 0 0 (by omega) (by omega)
  have hck := hagree.2.2.1
  rw [race_coinTapeTransitionCountAux_init N a ha w] at hck
  have hpeak := coinReceiptAux_peak_le (raceMachine N a) (raceAccept N a) w
    (Turing.TM0.init ([] : List (Option Bool))) 0 0 0 (by omega) (by omega)
  have hone : (((0 : ℤ) - (0 : ℤ) + 1).toNat) = 1 := rfl
  rw [hone] at hpeak
  calc (coinReceiptRun (raceMachine N a) (raceAccept N a) [] w).peak
      = (coinReceiptAux (raceMachine N a) (raceAccept N a) w
          (Turing.TM0.init ([] : List (Option Bool))) 0 0 0).peak := rfl
    _ ≤ 1 + (coinReceiptAux (raceMachine N a) (raceAccept N a) w
        (Turing.TM0.init ([] : List (Option Bool))) 0 0 0).clock := hpeak
    _ = raceTime N a w + 1 := by rw [hck]; omega

theorem output1.frontier1 (N a : ℕ) (ha : a ≤ N) (w fs : List Bool)
    (habs : raceWalk N a w = 0 ∨ raceWalk N a w = N)
    (hend : raceTime N a w = w.length)
    (hfs : w.length ≤ fs.length) :
    ∃ (sf : Bool) (Tf T'' : Turing.Tape CellCore) (off' lo' hi' : ℤ),
      (PhaseHomeAt T'' 0 ∧ PhaseInputSame (phaseCopyResult []) T'' 0 ∧
        (∀ i : ℤ, phaseBusy (T''.nth i) = false) ∧
        Turing.Tape.map phaseWorkMap Tf = (raceCfgFold N a w (raceSourceInit N)).Tape ∧
        PhaseMarkAbs Tf off' lo' hi' ∧
        -(w.length : ℤ) ≤ off' ∧ off' ≤ (w.length : ℤ) ∧
        lo' ≤ 1 ∧ 0 ≤ hi' ∧ hi' ≤ 2 * w.length + 1 ∧ 1 - lo' ≤ 2 * w.length + 1) ∧
      ∀ (jcopy jhome jreset tail : List Bool) (c₁ c₂ c₃ x : Bool),
        jcopy.length = 3 →
        jhome.length = (if sf then (-off').toNat else off'.toNat) →
        jreset.length = 3 * hi'.toNat + 3 * (-lo').toNat + 5 →
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile (raceCode N a)))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput []))).stopped
          = some (phase1EmbedCfg (controlSize (raceCode N a))
              ⟨Sum.inr (Sum.inr (Sum.inr (SweepPhase.backHomeR,
                readout (raceCode N a) (raceCfgFold N a w (raceSourceInit N)).q))), T''⟩) ∧
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile (raceCode N a)))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput []))).reads
          = 3 + 1 + (2 * w.length + 1) + 1
              + (if sf then (-off').toNat else off'.toNat) + 1
              + (3 * hi'.toNat + 3 * (-lo').toNat + 5) ∧
        (coinConfigRunAux (phase1Table (tmCopyRunResetCompile (raceCode N a)))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput []))).transitions
          = 3 + 1 + (2 * w.length + 1) + 1
              + (if sf then (-off').toNat else off'.toNat) + 1
              + (3 * hi'.toNat + 3 * (-lo').toNat + 5) ∧
        (coinTapeRunAux (phase1Table (tmCopyRunResetCompile (raceCode N a)))
            (phase1Readout (tmCopyRunResetCompile (raceCode N a)))
            ((jcopy ++ c₁ :: ((pairCoins w fs ++ [x]) ++ c₂ :: (jhome ++ c₃ :: jreset)))
              ++ tail)
            (Turing.TM0.init (phaseInput [])))
          = (some (readout (raceCode N a) (raceCfgFold N a w (raceSourceInit N)).q),
              3 + 1 + (2 * w.length + 1) + 1
                + (if sf then (-off').toNat else off'.toNat) + 1
                + (3 * hi'.toNat + 3 * (-lo').toNat + 5)) := by
  have htable : table (raceCode N a) = raceMachine N a := table_encode N _ _
  have hsim := race_coinConfigRunAux N a ha w ((phaseCopyResult []).map phaseWorkMap) 0
    (by omega)
  rw [racePosOf_zero N a ha] at hsim
  have hread : (coinConfigRunAux (table (raceCode N a)) w (raceSourceInit N)).reads
      = w.length := by
    rw [htable]
    exact hsim.1.trans hend
  have hstop : (coinConfigRunAux (table (raceCode N a)) w (raceSourceInit N)).stopped
      = some (raceCfgFold N a w (raceSourceInit N)) := by
    rw [htable]
    have h2 := hsim.2
    simp only [habs, if_true] at h2
    exact h2
  obtain ⟨sf, Tf, T'', off', lo', hi', hbound, hrun⟩ :=
    tmCopyRunResetCompile_run (raceCode N a) (race_commonHalt N a) [] w fs
      (raceCfgFold N a w (raceSourceInit N)) hstop hread hfs
  refine ⟨sf, Tf, T'', off', lo', hi', hbound, ?_⟩
  intro jcopy jhome jreset tail c₁ c₂ c₃ x hjcopy hjhome hjreset
  rcases hbound with ⟨-, -, -, -, -, -, -, -, h0hi, -, -⟩
  have hlen : (3 * ([] : List Bool).length + 3) = 3 := by simp
  have hmaxr : (3 * (max hi' ((([] : List Bool).length : ℤ) - 1)).toNat
      + 3 * (-lo').toNat + 5) = 3 * hi'.toNat + 3 * (-lo').toNat + 5 := by
    have hn1 : ((([] : List Bool).length : ℤ)) - 1 = -1 := by
      simp only [List.length_nil]
      norm_num
    rw [hn1, max_eq_left (by omega)]
  obtain ⟨hc1, hc2, hc3, hc4⟩ :=
    hrun jcopy jhome jreset tail c₁ c₂ c₃ x (hjcopy.trans hlen.symm) hjhome
      (hjreset.trans hmaxr.symm)
  rw [hlen, hmaxr] at hc2 hc3 hc4
  exact ⟨hc1, hc2, hc3, hc4⟩

end Qatlib.Concepts.AdversaryBounds.AdvDuality
