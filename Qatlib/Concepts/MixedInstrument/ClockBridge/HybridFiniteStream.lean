/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridFiniteStreamDefs

/-!
# Hybrid execution on a shared finite bit stream

This module relates path records and hybrid stream execution, showing that the consumed coin
lists are prefixes of the supplied stream. It proves that resuming native execution or supplying
more bits agrees with executing the combined input, and identifies the associated resource
ledgers and terminal joint law. See [NielsenChuang2010] for the quantum computation framework.

## Main statements

* `execStream_coins_prefix`: identifies the consumed coin prefix.
* `schedule_resume_eq_whole`: combines native fuel budgets.
* `scheduleTerminalLaw_eq_jointLaw`: identifies terminal and joint laws.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridCallReturn
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridFiniteStream
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

namespace HybridFiniteStream

open scoped ENNReal

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable {D : ℕ} {A V : Type}

/-- Recording a gate or query step applies the corresponding operator to the path record and
adds its gate or query count. -/
theorem record_step_eq {D : ℕ} {A : Type} (O : Operator D) {p : HybridProgram D A}
    (s : Step (Fin D)) (h : HybridProgram.Path p) :
    ((HybridProgram.Path.step s h).record O) = match s with
      | .gate U => (h.record O).quantum U 0 1 0 []
      | .query => (h.record O).quantum O 1 0 0 [] := by
  cases s <;> rfl

/-- Adding a gate or query step to a path leaves its recorded coin list unchanged. -/
theorem record_step_coins {D : ℕ} {A : Type} (O : Operator D) {p : HybridProgram D A}
    (s : Step (Fin D)) (h : HybridProgram.Path p) :
    ((HybridProgram.Path.step s h).record O).coins = (h.record O).coins := by
  cases s <;> rfl

/-- Recording the false branch of a random-bit choice prepends a false coin to the continuation
record. -/
theorem record_bitFalse_eq {D : ℕ} {A : Type} (O : Operator D) {p q : HybridProgram D A}
    (h : HybridProgram.Path p) :
    ((HybridProgram.Path.bitFalse (p := p) (q := q) h).record O) = (h.record O).coin false := rfl

/-- The coin list of a false-branch path is `false` followed by the continuation's coin list. -/
theorem record_bitFalse_coins {D : ℕ} {A : Type} (O : Operator D) {p q : HybridProgram D A}
    (h : HybridProgram.Path p) :
    ((HybridProgram.Path.bitFalse (p := p) (q := q) h).record O).coins
      = false :: (h.record O).coins := rfl

/-- Recording the true branch of a random-bit choice prepends a true coin to the continuation
record. -/
theorem record_bitTrue_eq {D : ℕ} {A : Type} (O : Operator D) {p q : HybridProgram D A}
    (h : HybridProgram.Path q) :
    ((HybridProgram.Path.bitTrue (p := p) (q := q) h).record O) = (h.record O).coin true := rfl

/-- The coin list of a true-branch path is `true` followed by the continuation's coin list. -/
theorem record_bitTrue_coins {D : ℕ} {A : Type} (O : Operator D) {p q : HybridProgram D A}
    (h : HybridProgram.Path q) :
    ((HybridProgram.Path.bitTrue (p := p) (q := q) h).record O).coins
      = true :: (h.record O).coins := rfl

/-- Mapping an option successively by `f` and `g` equals mapping it by their composition. -/
theorem map_map_option {α β γ : Type} (f : α → β) (g : β → γ) (o : Option α) :
    (o.map f).map g = o.map (fun x => g (f x)) := by
  cases o <;> rfl

/-- If `streamPath` returns a path, the coins in its record form a prefix of the supplied bit
stream. -/
theorem streamPath_coins_prefix {D : ℕ} {A : Type} (O : Operator D) :
    ∀ (p : HybridProgram D A) (bs : List Bool) (h : HybridProgram.Path p),
      streamPath p bs = some h → ∃ rest, bs = (h.record O).coins ++ rest := by
  intro p
  induction p with
  | ret a =>
      intro bs h hh
      have hrec : (h.record O).coins = [] := by
        cases h
        rfl
      refine ⟨bs, ?_⟩
      rw [hrec]
      rfl
  | step s p ih =>
      intro bs h hh
      have hh' : (streamPath p bs).map (fun x => (HybridProgram.Path.step s x)) = some h := by
        simpa only [streamPath] using hh
      obtain ⟨h0, hh0, hhe⟩ := Option.map_eq_some_iff.mp hh'
      have hcoin : (h.record O).coins = (h0.record O).coins := by
        rw [← hhe]
        exact record_step_coins O s h0
      obtain ⟨rest, hrest⟩ := ih bs h0 hh0
      refine ⟨rest, ?_⟩
      rw [hcoin]
      exact hrest
  | bit p q ihp ihq =>
      intro bs h hh
      cases bs with
      | nil =>
          have : streamPath (.bit p q) [] = none := rfl
          rw [this] at hh
          cases hh
      | cons b bs =>
          cases hb : b with
          | false =>
              have hht : streamPath (.bit p q) (false :: bs) = some h := by
                simpa only [hb] using hh
              have hh' : (streamPath p bs).map (fun x => (HybridProgram.Path.bitFalse x))
                  = some h := by
                have hthis : streamPath (.bit p q) (false :: bs)
                    = (streamPath p bs).map (fun x => (HybridProgram.Path.bitFalse x)) := by
                  simp [streamPath]
                rw [hthis] at hht
                exact hht
              obtain ⟨h0, hh0, hhe⟩ := Option.map_eq_some_iff.mp hh'
              have hcoin : (h.record O).coins = false :: (h0.record O).coins := by
                rw [← hhe]
                exact record_bitFalse_coins O h0
              obtain ⟨rest, hrest⟩ := ihp bs h0 hh0
              refine ⟨rest, ?_⟩
              rw [hcoin]
              simp [hrest]
          | true =>
              have hht : streamPath (.bit p q) (true :: bs) = some h := by
                simpa only [hb] using hh
              have hh' : (streamPath q bs).map (fun x => (HybridProgram.Path.bitTrue x))
                  = some h := by
                have hthis : streamPath (.bit p q) (true :: bs)
                    = (streamPath q bs).map (fun x => (HybridProgram.Path.bitTrue x)) := by
                  simp [streamPath]
                rw [hthis] at hht
                exact hht
              obtain ⟨h0, hh0, hhe⟩ := Option.map_eq_some_iff.mp hh'
              have hcoin : (h.record O).coins = true :: (h0.record O).coins := by
                rw [← hhe]
                exact record_bitTrue_coins O h0
              obtain ⟨rest, hrest⟩ := ihq bs h0 hh0
              refine ⟨rest, ?_⟩
              rw [hcoin]
              simp [hrest]
  | measure n label next ih =>
      intro bs h hh
      have : streamPath (.measure n label next) bs = none := rfl
      rw [this] at hh
      cases hh
  | project P p q ihp ihq =>
      intro bs h hh
      have : streamPath (.project P p q) bs = none := rfl
      rw [this] at hh
      cases hh

/-- If stream execution returns a leaf, its recorded coins form a prefix of the supplied bit
stream. -/
theorem execStream_coins_prefix {D : ℕ} {A : Type} (O : Operator D) :
    ∀ (p : HybridProgram D A) (bs : List Bool) (t : HybridLeaf D A),
      execStream O p bs = some t → ∃ rest, bs = t.coins ++ rest := by
  intro p
  induction p with
  | ret a =>
      intro bs t h
      have ht : t = ⟨a, 1, 0, 0, 0, [], [], []⟩ := by
        have h' : execStream O (.ret a) bs = some ⟨a, 1, 0, 0, 0, [], [], []⟩ := rfl
        rw [h'] at h
        exact (Option.some.inj h).symm
      refine ⟨bs, ?_⟩
      simp [ht]
  | step s p ih =>
      intro bs t h
      cases s with
      | gate U =>
          have h' : (execStream O p bs).map (fun x => x.quantum U 0 1 0 []) = some t := by
            simpa only [execStream] using h
          obtain ⟨u, hu, htu⟩ := Option.map_eq_some_iff.mp h'
          have hcoin : t.coins = u.coins := by
            rw [← htu]
            simp only [HybridLeaf.quantum]
          obtain ⟨rest, hrest⟩ := ih bs u hu
          refine ⟨rest, ?_⟩
          rw [hcoin]
          exact hrest
      | query =>
          have h' : (execStream O p bs).map (fun x => x.quantum O 1 0 0 []) = some t := by
            simpa only [execStream] using h
          obtain ⟨u, hu, htu⟩ := Option.map_eq_some_iff.mp h'
          have hcoin : t.coins = u.coins := by
            rw [← htu]
            simp only [HybridLeaf.quantum]
          obtain ⟨rest, hrest⟩ := ih bs u hu
          refine ⟨rest, ?_⟩
          rw [hcoin]
          exact hrest
  | bit p q ihp ihq =>
      intro bs t h
      cases bs with
      | nil =>
          simp [execStream] at h
      | cons b bs =>
          cases hb : b with
          | false =>
              have h' : (execStream O p bs).map (fun x => x.coin false) = some t := by
                simpa only [execStream, hb] using h
              obtain ⟨u, hu, htu⟩ := Option.map_eq_some_iff.mp h'
              have hcoin : t.coins = false :: u.coins := by
                rw [← htu]
                simp only [HybridLeaf.coin]
              obtain ⟨rest, hrest⟩ := ihp bs u hu
              refine ⟨rest, ?_⟩
              rw [hcoin]
              simp [hrest]
          | true =>
              have h' : (execStream O q bs).map (fun x => x.coin true) = some t := by
                simpa only [execStream, hb] using h
              obtain ⟨u, hu, htu⟩ := Option.map_eq_some_iff.mp h'
              have hcoin : t.coins = true :: u.coins := by
                rw [← htu]
                simp only [HybridLeaf.coin]
              obtain ⟨rest, hrest⟩ := ihq bs u hu
              refine ⟨rest, ?_⟩
              rw [hcoin]
              simp [hrest]
  | measure n label next ih =>
      intro bs t h
      simp [execStream] at h
  | project P p q ihp ihq =>
      intro bs t h
      simp [execStream] at h

/-- For a coin-only hybrid program, executing a leaf's own coin list returns that leaf. -/
theorem execStream_of_leaf {D : ℕ} {A : Type} (O : Operator D) :
    ∀ (p : HybridProgram D A) (t : HybridLeaf D A),
      CoinOnly p → t ∈ p.leaves O → execStream O p t.coins = some t := by
  intro p
  induction p with
  | ret a =>
      intro t _ ht
      have hte : t = ⟨a, 1, 0, 0, 0, [], [], []⟩ := by
        simpa [HybridProgram.leaves] using ht
      subst hte
      show execStream O (.ret a) [] = some ⟨a, 1, 0, 0, 0, [], [], []⟩
      rfl
  | step s p ih =>
      intro t hc ht
      cases s with
      | gate U =>
          have ht' : t ∈ (p.leaves O).map (HybridLeaf.quantum U 0 1 0 []) := by
            simpa [HybridProgram.leaves] using ht
          obtain ⟨u, hu, htu⟩ := List.mem_map.mp ht'
          have hcoins : t.coins = u.coins := by
            rw [← htu]
            simp only [HybridLeaf.quantum]
          have hrec : execStream O p u.coins = some u := ih u hc hu
          have h' : (execStream O p u.coins).map (fun x => x.quantum U 0 1 0 []) = some t := by
            rw [hrec]
            simp only [Option.map_some]
            rw [← htu]
          show execStream O (.step (.gate U) p) t.coins = some t
          rw [hcoins]
          simpa only [execStream] using h'
      | query =>
          have ht' : t ∈ (p.leaves O).map (HybridLeaf.quantum O 1 0 0 []) := by
            simpa [HybridProgram.leaves] using ht
          obtain ⟨u, hu, htu⟩ := List.mem_map.mp ht'
          have hcoins : t.coins = u.coins := by
            rw [← htu]
            simp only [HybridLeaf.quantum]
          have hrec : execStream O p u.coins = some u := ih u hc hu
          have h' : (execStream O p u.coins).map (fun x => x.quantum O 1 0 0 []) = some t := by
            rw [hrec]
            simp only [Option.map_some]
            rw [← htu]
          show execStream O (.step .query p) t.coins = some t
          rw [hcoins]
          simpa only [execStream] using h'
  | bit p q ihp ihq =>
      intro t hc ht
      obtain ⟨hcp, hcq⟩ := hc
      have ht' : t ∈ (p.leaves O).map (HybridLeaf.coin false)
          ++ (q.leaves O).map (HybridLeaf.coin true) := by
        simpa [HybridProgram.leaves] using ht
      rcases List.mem_append.mp ht' with ht | ht
      · obtain ⟨u, hu, htu⟩ := List.mem_map.mp ht
        have hcoins : t.coins = false :: u.coins := by
          rw [← htu]
          simp only [HybridLeaf.coin]
        have hrec : execStream O p u.coins = some u := ihp u hcp hu
        have h' : (execStream O p u.coins).map (fun x => x.coin false) = some t := by
          rw [hrec]
          simp only [Option.map_some]
          rw [← htu]
        show execStream O (.bit p q) t.coins = some t
        rw [hcoins]
        simpa only [execStream] using h'
      · obtain ⟨u, hu, htu⟩ := List.mem_map.mp ht
        have hcoins : t.coins = true :: u.coins := by
          rw [← htu]
          simp only [HybridLeaf.coin]
        have hrec : execStream O q u.coins = some u := ihq u hcq hu
        have h' : (execStream O q u.coins).map (fun x => x.coin true) = some t := by
          rw [hrec]
          simp only [Option.map_some]
          rw [← htu]
        show execStream O (.bit p q) t.coins = some t
        rw [hcoins]
        simpa only [execStream] using h'
  | measure n label next ih =>
      intro t hc ht
      simp [CoinOnly] at hc
  | project P p q ihp ihq =>
      intro t hc ht
      simp [CoinOnly] at hc

/-- If `streamPath` returns a path, stream execution returns that path's record. -/
theorem execStream_of_streamPath {D : ℕ} {A : Type} (O : Operator D) :
    ∀ (p : HybridProgram D A) (bs : List Bool) (h : HybridProgram.Path p),
      streamPath p bs = some h → execStream O p bs = some (h.record O) := by
  intro p
  induction p with
  | ret a =>
      intro bs h hh
      cases h
      rfl
  | step s p ih =>
      intro bs h hh
      have hh' : (streamPath p bs).map (fun x => (HybridProgram.Path.step s x)) = some h := by
        simpa only [streamPath] using hh
      obtain ⟨h0, hh0, hhe⟩ := Option.map_eq_some_iff.mp hh'
      have hrec : execStream O p bs = some (h0.record O) := ih bs h0 hh0
      cases s with
      | gate U =>
          show execStream O (.step (.gate U) p) bs = some (h.record O)
          rw [execStream, hrec]
          simp only [Option.map_some]
          rw [← hhe]
          congr 1
      | query =>
          show execStream O (.step .query p) bs = some (h.record O)
          rw [execStream, hrec]
          simp only [Option.map_some]
          rw [← hhe]
          congr 1
  | bit p q ihp ihq =>
      intro bs h hh
      cases bs with
      | nil =>
          have hthis : streamPath (.bit p q) [] = none := rfl
          rw [hthis] at hh
          cases hh
      | cons b bs =>
          cases hb : b with
          | false =>
              have hht : streamPath (.bit p q) (false :: bs) = some h := by
                simpa only [hb] using hh
              have hh' : (streamPath p bs).map
                  (fun x => (HybridProgram.Path.bitFalse (p := p) (q := q) x)) = some h := by
                have hthis : streamPath (.bit p q) (false :: bs)
                    = (streamPath p bs).map
                        (fun x => (HybridProgram.Path.bitFalse (p := p) (q := q) x)) := by
                  simp [streamPath]
                rw [hthis] at hht
                exact hht
              obtain ⟨h0, hh0, hhe⟩ := Option.map_eq_some_iff.mp hh'
              have hrec : execStream O p bs = some (h0.record O) := ihp bs h0 hh0
              show execStream O (.bit p q) (false :: bs) = some (h.record O)
              rw [execStream, hrec]
              simp only [Option.map_some]
              rw [← hhe]
              congr 1
          | true =>
              have hht : streamPath (.bit p q) (true :: bs) = some h := by
                simpa only [hb] using hh
              have hh' : (streamPath q bs).map
                  (fun x => (HybridProgram.Path.bitTrue (p := p) (q := q) x)) = some h := by
                have hthis : streamPath (.bit p q) (true :: bs)
                    = (streamPath q bs).map
                        (fun x => (HybridProgram.Path.bitTrue (p := p) (q := q) x)) := by
                  simp [streamPath]
                rw [hthis] at hht
                exact hht
              obtain ⟨h0, hh0, hhe⟩ := Option.map_eq_some_iff.mp hh'
              have hrec : execStream O q bs = some (h0.record O) := ihq bs h0 hh0
              show execStream O (.bit p q) (true :: bs) = some (h.record O)
              rw [execStream, hrec]
              simp only [Option.map_some]
              rw [← hhe]
              congr 1
  | measure n label next ih =>
      intro bs h hh
      have hthis : streamPath (.measure n label next) bs = none := rfl
      rw [hthis] at hh
      cases hh
  | project P p q ihp ihq =>
      intro bs h hh
      have hthis : streamPath (.project P p q) bs = none := rfl
      rw [hthis] at hh
      cases hh

/-- Equal native execution results produce equal schedules. -/
theorem scheduleOf_congr {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) {r r' : NativeTape.Result Γ Λ}
    (h : r = r') : scheduleOf c O r = scheduleOf c O r' := by
  cases h
  rfl

/-- Resuming a schedule with extra native fuel equals scheduling from the start with the
combined fuel budget. -/
theorem schedule_resume_eq_whole {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (extra : ℕ) :
    scheduleResume c O extra = schedule { c with budget := c.budget + extra } O := by
  apply scheduleOf_congr c O
  have h := NativeTape.run_add c.program c.budget extra c.bits c.config
  simp only [ReturnCall.native] at h ⊢
  exact h.symm

/-- Supplying more bits to a schedule equals scheduling from the start with those bits appended. -/
theorem schedule_supply_eq_whole {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (more : List Bool) :
    scheduleSupply c O more = schedule { c with bits := c.bits ++ more } O := by
  apply scheduleOf_congr c O
  have h := NativeTape.run_append c.program c.budget c.bits more c.config
  simp only [ReturnCall.native] at h ⊢
  exact h.symm

/-- The original bit stream splits into the native execution's consumed bits followed by its
unread bits. -/
theorem schedule_stream_account {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) :
    c.bits = c.native.bits ++ c.native.unread := by
  simpa [ReturnCall.native] using
    (NativeTape.run_account c.program c.budget c.bits c.config)

/-- Two returned values and leaves for the same scheduled native result agree. -/
theorem scheduleOf_returned_unique {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (r : NativeTape.Result Γ Λ) {v v' : V}
    {t t' : HybridLeaf D A} (h1 : scheduleOf c O r = .returned r v t)
    (h2 : scheduleOf c O r = .returned r v' t') : v = v' ∧ t = t' := by
  rw [h1] at h2
  cases h2
  exact ⟨rfl, rfl⟩

/-- A returned schedule decodes the native result to `v` and executes the continuation on the
unread bits to obtain `t`. -/
theorem scheduleOf_returned_exec {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (r : NativeTape.Result Γ Λ) (v : V)
    (t : HybridLeaf D A) (h : scheduleOf c O r = .returned r v t) :
    c.decoded r = some v ∧ execStream O (c.next v) r.unread = some t := by
  cases hdec : c.decoded r with
  | none =>
      by_cases hs : r.stop = NativeTape.Stop.halted
      · simp [scheduleOf, hdec, hs] at h
      · simp [scheduleOf, hdec, hs] at h
  | some v' =>
      cases he : execStream O (c.next v') r.unread with
      | none =>
          simp [scheduleOf, hdec, he] at h
      | some t' =>
          have hv : v' = v := by
            have hcongr := congrArg (fun z => match z with
              | .returned _ w _ => w
              | _ => v') h
            simpa [scheduleOf, hdec, he] using hcongr
          have ht : t' = t := by
            have hcongr := congrArg (fun z => match z with
              | .returned _ _ tt => tt
              | _ => t') h
            simpa [scheduleOf, hdec, he] using hcongr
          refine ⟨congrArg some hv, ?_⟩
          rw [← congrArg c.next hv, ← congrArg some ht]
          exact he

/-- A returned schedule splits its input stream into the native consumed bits, the
continuation's recorded coins, and a remaining suffix. -/
theorem schedule_returned_one_stream {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (v : V) (t : HybridLeaf D A)
    (h : schedule c O = .returned c.native v t) :
    ∃ rest, c.bits = c.native.bits ++ t.coins ++ rest := by
  obtain ⟨hdec, hexec⟩ := scheduleOf_returned_exec c O c.native v t h
  obtain ⟨rest, hrest⟩ := execStream_coins_prefix O (c.next v) c.native.unread t hexec
  refine ⟨rest, ?_⟩
  rw [schedule_stream_account c, hrest]
  exact (List.append_assoc _ _ _).symm

/-- A pending native schedule records its native steps, bits, CPU time, and peak space, has
quantum space `D`, and has zero quantum counts and communication. -/
theorem scheduleLedger_pending {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (h : schedule c O = .pendingNative c.native) :
    (scheduleLedger c O).nativeSteps = c.native.steps ∧
    (scheduleLedger c O).nativeBits = c.native.bits.length ∧
    (scheduleLedger c O).nativeCpu = nativeCpuTime c.program c.native ∧
    (scheduleLedger c O).nativeSpace = nativePeakSpace c.program c.native ∧
    (scheduleLedger c O).quantumSpace = D ∧
    (scheduleLedger c O).quantum = HybridCounts.zero ∧
    (scheduleLedger c O).communication = 0 := by
  have h' : scheduleOf c O c.native = .pendingNative c.native := by
    simpa only [schedule] using h
  have hledger : scheduleLedger c O
      = runClocks (D := D) (A := A) c.program c.native none 0 := by
    simp only [scheduleLedger]
    rw [h']
  rw [hledger]
  simp [runClocks, HybridCounts.zero]

/-- A returned schedule records the leaf's quantum counts, the decoded value's communication
width, the native resource ledger, and quantum space `D`. -/
theorem scheduleLedger_returned {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D) (v : V) (t : HybridLeaf D A)
    (h : schedule c O = .returned c.native v t) :
    (scheduleLedger c O).quantum = t.counts ∧
    (scheduleLedger c O).communication = c.decodeWidth v ∧
    (scheduleLedger c O).nativeSteps = c.native.steps ∧
    (scheduleLedger c O).nativeBits = c.native.bits.length ∧
    (scheduleLedger c O).nativeCpu = nativeCpuTime c.program c.native ∧
    (scheduleLedger c O).nativeSpace = nativePeakSpace c.program c.native ∧
    (scheduleLedger c O).quantumSpace = D := by
  have h' : scheduleOf c O c.native = .returned c.native v t := by
    simpa only [schedule] using h
  have hledger : scheduleLedger c O
      = runClocks (D := D) (A := A) c.program c.native (some t) (c.decodeWidth v) := by
    simp only [scheduleLedger]
    rw [h']
  rw [hledger]
  simp [runClocks]

/-- Adding extra fuel in `scheduleLawFuel` gives the schedule law at the sum of the two fuel
budgets. -/
theorem scheduleLawFuel_eq {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (n extra : ℕ) :
    scheduleLawFuel c O hO hp ρ hρ n extra = scheduleLaw c O hO hp ρ hρ (n + extra) := by
  have key : ∀ r : NativeTape.Result Γ Λ,
      (scheduleConditional c O hO hp ρ hρ r).bind (scheduleContinueFuel c O hO hp ρ hρ extra)
        = (NativeTape.continueLaw c.program extra r).bind
            (scheduleConditional c O hO hp ρ hρ) := by
    intro r
    cases hs : r.stop with
    | halted =>
        have hcont : NativeTape.continueLaw c.program extra r = PMF.pure r := by
          simp [NativeTape.continueLaw, hs]
        cases hd : c.decode r.cfg with
        | none =>
            have hcond : scheduleConditional c O hO hp ρ hρ r = PMF.pure (.undecoded r) := by
              simp [scheduleConditional, hs, hd]
            rw [hcond, hcont]
            simp only [PMF.pure_bind]
            rw [hcond]
            simp [scheduleContinueFuel]
        | some v =>
            have hcond : scheduleConditional c O hO hp ρ hρ r
                = (leafLaw (c.next v) O hO (hp v) ρ hρ).map (fun t => .returned r v t) := by
              simp [scheduleConditional, hs, hd]
            rw [hcond, hcont]
            simp only [PMF.pure_bind]
            rw [hcond]
            rw [PMF.bind_map]
            have hcont' : scheduleContinueFuel c O hO hp ρ hρ extra ∘ (fun t => .returned r v t)
                = PMF.pure ∘ (fun t => .returned r v t) := by
              funext t
              simp [scheduleContinueFuel]
            rw [hcont', PMF.bind_pure_comp]
    | fuel =>
        have hcond : scheduleConditional c O hO hp ρ hρ r = PMF.pure (.pendingNative r) := by
          simp [scheduleConditional, hs]
        rw [hcond]
        simp only [PMF.pure_bind]
        rfl
    | needBits =>
        have hcond : scheduleConditional c O hO hp ρ hρ r = PMF.pure (.pendingNative r) := by
          simp [scheduleConditional, hs]
        rw [hcond]
        simp only [PMF.pure_bind]
        rfl
  unfold scheduleLawFuel scheduleLaw
  rw [PMF.bind_bind, NativeTape.law_add, PMF.bind_bind]
  apply congrArg (fun p : NativeTape.Result Γ Λ → PMF (ScheduleOutcome Γ Λ D A V) =>
    (NativeTape.law c.program n c.config).bind p)
  funext r
  exact key r

/-- The terminal schedule law equals the corresponding joint law. -/
theorem scheduleTerminalLaw_eq_jointLaw {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {D : ℕ} {A V : Type} (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    scheduleTerminalLaw c O hO hp ρ hρ = jointLaw c O hO hp ρ hρ := by
  apply PMF.ext
  intro z
  simp only [scheduleTerminalLaw, jointLaw, PMF.bind_apply]
  apply tsum_congr
  intro z'
  cases z' with
  | none =>
      simp [scheduleTerminalConditional, conditionalLaw]
  | some r =>
      by_cases hs : r.stop = NativeTape.Stop.halted
      · have hdec : c.decoded r = c.decode r.cfg := by
          simp [ReturnCall.decoded, hs]
        simp [scheduleTerminalConditional, conditionalLaw, hdec]
        rfl
      · have hz : NativeTape.terminalLaw c.program c.config (some r) = 0 := by
          simp [NativeTape.haltedMass, NativeTape.finishedMass, hs]
        rw [hz]
        simp

end HybridFiniteStream

end Qatlib.Concepts.MixedInstrument.ClockBridge
