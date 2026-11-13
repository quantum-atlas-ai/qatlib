/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridCallReturnDefs

/-!
# Native call-return execution laws

This module proves the execution and probability laws for `ReturnCall` and `JointRecord`. The
results describe suspended calls, decoded returns, resumed execution, and the separation of
native, quantum, and communication costs; the quantum instrument interpretation follows the
standard framework in [Watrous2018].

The `jointLaw` results retain nontermination and failed decoding as explicit outcomes, factor
returned outcomes into native and quantum probabilities, and identify the fair-bit weights of
supported native traces.

## Main statements

* `law_weight` and `haltedMass_weight` compute native trace probabilities from consumed fair
  bits.
* `run_branch_eq_instrument` and `run_bornMass_eq_instrumentProb` identify returned quantum
  branches and their probabilities.
* `jointLaw_returned`, `jointLaw_total`, and `jointLaw_fiber` give factorization, normalization,
  and native marginals.
* `fair_source_split` and `clause16_complete` collect fair-source, execution, and resource
  guarantees.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeHybridCallReturn

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

namespace NativeHybridCallReturn

open Qatlib
open scoped ENNReal

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
variable {D : ℕ} {A V : Type}

omit [Inhabited Λ] in

/-- Prepending the same native tick to two results preserves enough information to recover
equality of the original results. -/
private theorem prepend_injective {r s : NativeTape.Result Γ Λ} (e : NativeTape.Tick Γ Λ)
    (h : NativeTape.Result.prepend e r = NativeTape.Result.prepend e s) : r = s := by
  cases r with
  | mk cfg unread stop trace =>
    cases s with
    | mk cfg' unread' stop' trace' =>
      simp only [NativeTape.Result.prepend] at h
      have hcfg : cfg = cfg' := congrArg (fun x => x.cfg) h
      have hunread : unread = unread' := congrArg (fun x => x.unread) h
      have hstop : stop = stop' := congrArg (fun x => x.stop) h
      have htrace : e :: trace = e :: trace' := congrArg (fun x => x.trace) h
      have hts : trace = trace' := (List.cons.inj htrace).2
      subst hts; subst hcfg; subst hunread; subst hstop; rfl

omit [Inhabited Λ] in

/-- Equal results obtained by prepending coin ticks at the same configuration have equal
prepended coin bits. -/
private theorem prepend_some_eq {b b' : Bool} (cfg : Turing.TM0.Cfg Γ Λ)
    (t t' : NativeTape.Result Γ Λ)
    (h : NativeTape.Result.prepend (cfg, some b) t = NativeTape.Result.prepend (cfg, some b') t') :
    b = b' := by
  have htr := congrArg NativeTape.Result.trace h
  simp only [NativeTape.Result.prepend] at htr
  have hbb : (cfg, some b) = (cfg, some b') := (List.cons.inj htr).1
  have hbs : some b = some b' := congrArg Prod.snd hbb
  exact Option.some.inj hbs

omit [Inhabited Λ] in

/-- Mapping a native-result distribution by prepending a fixed tick preserves the mass of each
result at its image. -/
private theorem map_prepend_apply {p : PMF (NativeTape.Result Γ Λ)} (e : NativeTape.Tick Γ Λ)
    (r s : NativeTape.Result Γ Λ) (h : r = NativeTape.Result.prepend e s) :
    p.map (NativeTape.Result.prepend e) r = p s := by
  classical
  rw [PMF.map_apply]
  show (∑' (a : NativeTape.Result Γ Λ),
      (if r = NativeTape.Result.prepend e a then p a else 0)) = p s
  calc
    (∑' (a : NativeTape.Result Γ Λ),
        (if r = NativeTape.Result.prepend e a then p a else 0))
        = (if r = NativeTape.Result.prepend e s then p s else 0) := by
          refine tsum_eq_single (L := SummationFilter.unconditional (NativeTape.Result Γ Λ))
            (α := ℝ≥0∞) (β := NativeTape.Result Γ Λ)
            (f := fun a => if r = NativeTape.Result.prepend e a then p a else 0) s ?_
          intro t ht
          have hne : r ≠ NativeTape.Result.prepend e t := by
            intro heq
            exact ht (prepend_injective e (heq.symm.trans h))
          simp [hne]
    _ = p s := if_pos h

omit [Inhabited Λ] in

/-- The distribution obtained by prepending a fixed tick assigns zero mass to any result outside
the image of that operation. -/
private theorem map_prepend_apply_ne {p : PMF (NativeTape.Result Γ Λ)} (e : NativeTape.Tick Γ Λ)
    (r : NativeTape.Result Γ Λ) (hne : ∀ t, NativeTape.Result.prepend e t ≠ r) :
    p.map (NativeTape.Result.prepend e) r = 0 := by
  classical
  rw [PMF.map_apply]
  show (∑' (a : NativeTape.Result Γ Λ),
      (if r = NativeTape.Result.prepend e a then p a else 0)) = 0
  rw [ENNReal.tsum_eq_zero]
  intro a
  have hne' : r ≠ NativeTape.Result.prepend e a := fun heq => hne a heq.symm
  simp [hne']

/-- If only one input can assign nonzero conditional mass to an output, the bound distribution's
mass there is the product of that input's mass and its conditional mass. -/
private theorem bind_apply_eq {α β : Type} {p : PMF α} {f : α → PMF β} {b : β} {a : α}
    (hzero : ∀ x, x ≠ a → f x b = 0) :
    (p.bind f) b = p a * f a b := by
  classical
  rw [PMF.bind_apply]
  show (∑' (x : α), p x * f x b) = p a * f a b
  calc
    (∑' (x : α), p x * f x b) = p a * f a b := by
      refine tsum_eq_single (L := SummationFilter.unconditional α) (α := ℝ≥0∞) (β := α)
        (f := fun x => p x * f x b) a ?_
      intro x hx
      simp only [hzero x hx, mul_zero]
    _ = p a * f a b := rfl

omit [Inhabited Λ] in

/-- Every supported result of a bounded native execution has probability one half raised to the
number of fair bits it consumed. -/
theorem law_weight (M : NativeTape.Program Γ Λ) :
    ∀ (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (r : NativeTape.Result Γ Λ),
      r ∈ (NativeTape.law M n cfg).support →
      (NativeTape.law M n cfg) r = (1 / 2 : ℝ≥0∞)^r.bits.length := by
  intro n
  induction n with
  | zero =>
    intro cfg r hr
    cases hc : M cfg.q cfg.Tape.head <;>
      simp only [NativeTape.law, hc, PMF.mem_support_pure_iff] at hr
    all_goals subst r
    all_goals simp [NativeTape.law, hc, NativeTape.Result.bits]
  | succ n ih =>
    intro cfg r hr
    cases hc : M cfg.q cfg.Tape.head with
    | halt =>
      simp only [NativeTape.law, hc, PMF.mem_support_pure_iff] at hr
      subst r
      simp [NativeTape.law, hc, NativeTape.Result.bits]
    | det q' s =>
      simp only [NativeTape.law, hc] at hr
      obtain ⟨t, ht, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
      have hmass : (NativeTape.law M (n+1) cfg) r
          = (NativeTape.law M n (NativeTape.advance cfg (q', s))) t := by
        simp only [NativeTape.law, hc]
        exact map_prepend_apply (cfg, none) r t heq.symm
      have hbits : r.bits = t.bits := by
        rw [← heq]
        exact (NativeTape.Result.bits_prepend_none t cfg).symm
      rw [hmass, ih (NativeTape.advance cfg (q', s)) t ht, hbits]
    | coin k =>
      simp only [NativeTape.law, hc] at hr
      obtain ⟨b, _, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hr
      obtain ⟨t, ht', heq⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      have hmass : (NativeTape.law M (n+1) cfg) r
          = (1 / 2 : ℝ≥0∞) * (NativeTape.law M n (NativeTape.advance cfg (k b))) t := by
        simp only [NativeTape.law, hc, PMF.bind_apply]
        have hsum : (∑' (b' : Bool), (PMF.uniformOfFintype' Bool) b' *
              (NativeTape.law M n (NativeTape.advance cfg (k b'))).map
                (NativeTape.Result.prepend (cfg, some b')) r)
            = (PMF.uniformOfFintype' Bool) b *
              (NativeTape.law M n (NativeTape.advance cfg (k b))).map
                (NativeTape.Result.prepend (cfg, some b)) r := by
          refine tsum_eq_single (L := SummationFilter.unconditional Bool) (α := ℝ≥0∞)
              (β := Bool) b ?_
          intro b' hb'
          have hz : (NativeTape.law M n (NativeTape.advance cfg (k b'))).map
                (NativeTape.Result.prepend (cfg, some b')) r = 0 := by
            refine map_prepend_apply_ne (cfg, some b') r ?_
            intro t' heq2
            exact hb' (prepend_some_eq cfg t t' (heq.trans heq2.symm)).symm
          have hunif : (PMF.uniformOfFintype' Bool) b' = (1 / 2 : ℝ≥0∞) := by
            simp [PMF.uniformOfFintype'_apply]
          rw [hunif, hz, mul_zero]
        rw [hsum, map_prepend_apply (cfg, some b) r t heq.symm]
        simp [PMF.uniformOfFintype'_apply]
      have hbits : r.bits = b :: t.bits := by
        rw [← heq]
        exact (NativeTape.Result.bits_prepend_some t cfg b).symm
      rw [hmass, ih (NativeTape.advance cfg (k b)) t ht']
      rw [hbits]
      simp only [List.length_cons]
      rw [pow_succ, mul_comm]

/-- A result supported by the native terminal law has halted mass one half raised to its
consumed-bit count. -/
theorem haltedMass_weight (M : NativeTape.Program Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (r : NativeTape.Result Γ Λ) (hr : some r ∈ (NativeTape.terminalLaw M cfg).support) :
    NativeTape.haltedMass M cfg r = (1 / 2 : ℝ≥0∞)^r.bits.length := by
  classical
  obtain ⟨hrun, hunread, hstop, hpath, hfuel⟩ :=
    NativeTape.terminalLaw_first_stop M cfg r hr
  have hsup : r ∈ (NativeTape.law M r.steps cfg).support :=
    (NativeTape.mem_support_law_iff M r.steps cfg r).mpr ⟨hrun, hunread, by simp [hstop]⟩
  have hlow : (1 / 2 : ℝ≥0∞)^r.bits.length ≤ NativeTape.haltedMass M cfg r := by
    have hfin : NativeTape.finishedMass M r.steps cfg r = (1 / 2 : ℝ≥0∞)^r.bits.length := by
      simp only [NativeTape.finishedMass, hstop, ↓reduceIte]
      exact law_weight M r.steps cfg r hsup
    have hle : NativeTape.finishedMass M r.steps cfg r ≤ ⨆ n, NativeTape.finishedMass M n cfg r :=
      le_iSup (fun n => NativeTape.finishedMass M n cfg r) r.steps
    rw [NativeTape.haltedMass]
    exact hfin.symm ▸ hle
  have hupp : NativeTape.haltedMass M cfg r ≤ (1 / 2 : ℝ≥0∞)^r.bits.length := by
    rw [NativeTape.haltedMass]
    refine iSup_le ?_
    intro n
    by_cases hn : r ∈ (NativeTape.law M n cfg).support
    · by_cases hstop' : r.stop = NativeTape.Stop.halted
      · simp only [NativeTape.finishedMass, hstop', ↓reduceIte]
        rw [law_weight M n cfg r hn]
      · simp [NativeTape.finishedMass, hstop']
    · have hz : NativeTape.law M n cfg r = 0 :=
        (PMF.apply_eq_zero_iff (NativeTape.law M n cfg) r).mpr hn
      simp only [NativeTape.finishedMass, hstop, ↓reduceIte]
      rw [hz]
      exact bot_le
  exact le_antisymm hupp hlow

/-- A native result that has not halted yields neither a decoded value nor a selected quantum
continuation. -/
theorem decoded_of_suspended {c : ReturnCall Γ Λ D A V} {r : NativeTape.Result Γ Λ}
    (h : r.stop ≠ NativeTape.Stop.halted) :
    c.decoded r = none ∧ c.selected r = none := by
  simp [ReturnCall.decoded, h, ReturnCall.selected]

/-- For a halted native result, decoding uses its final configuration and continuation selection
maps the decoder's value through the continuation function. -/
theorem decoded_of_halted {c : ReturnCall Γ Λ D A V} {r : NativeTape.Result Γ Λ}
    (h : r.stop = NativeTape.Stop.halted) :
    c.decoded r = c.decode r.cfg ∧ c.selected r = (c.decode r.cfg).map c.next := by
  simp [ReturnCall.decoded, h, ReturnCall.selected]

/-- A suspended call retains its native result, has no decoded value or quantum leaf, and has
zero branch and action. Its ledger records native costs and quantum space with zero quantum
counts and communication. -/
theorem run_suspended {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop ≠ NativeTape.Stop.halted) (ρ : Operator D) :
    (c.run O paths).value = none ∧
    (c.run O paths).leaf = none ∧
    (c.run O paths).native = c.native ∧
    (c.run O paths).branch ρ = 0 ∧
    (c.run O paths).action ρ = 0 ∧
    (c.run O paths).clocks.nativeSteps = c.native.steps ∧
    (c.run O paths).clocks.nativeBits = c.native.bits.length ∧
    (c.run O paths).clocks.quantum = HybridCounts.zero ∧
    (c.run O paths).clocks.nativeCpu = nativeCpuTime c.program c.native ∧
    (c.run O paths).clocks.nativeSpace = nativePeakSpace c.program c.native ∧
    (c.run O paths).clocks.quantumSpace = D ∧
    (c.run O paths).clocks.communication = 0 := by
  have hdec : c.decoded c.native = none := (decoded_of_suspended h).1
  simp [ReturnCall.run, hdec, JointRecord.branch, JointRecord.action, runClocks,
    HybridCounts.zero]

/-- When the native run halts and decodes to a value, the joint record stores that value, the
chosen continuation leaf, and the original native result. -/
theorem run_returned {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v) :
    (c.run O paths).value = some v ∧
    (c.run O paths).leaf = some ((paths v).record O) ∧
    (c.run O paths).native = c.native := by
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  simp [ReturnCall.run, hdec]

/-- After a halted call decodes successfully, its action is left multiplication by the operator
of the chosen continuation leaf. -/
theorem run_action_of_returned {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v)
    (ρ : Operator D) :
    (c.run O paths).action ρ = ((paths v).record O).operator * ρ := by
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  simp [ReturnCall.run, hdec, JointRecord.action, nativeAction]

/-- For a unitary oracle and legal continuations, a successfully returned call has the same
branch as an instrument index representing its chosen quantum leaf. -/
theorem run_branch_eq_instrument {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v)
    (ρ : Operator D) :
    ∃ i : Fin (c.next v).leafCount,
      (c.next v).leaf O i = (paths v).record O ∧
      (c.run O paths).branch ρ = ((c.next v).instrument O hO (hp v)).branch i ρ := by
  obtain ⟨i, hi⟩ := (paths v).record_index O
  refine ⟨i, hi, ?_⟩
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  simp only [JointRecord.branch]
  have hrun : (c.run O paths).leaf = some ((paths v).record O) := by
    simp [ReturnCall.run, hdec]
  rw [hrun]
  simp only []
  rw [HybridProgram.branch_law _ O hO (hp v) ρ i, hi]

/-- For a unitary oracle and legal continuations, the Born mass of a successfully returned call
equals the instrument probability at an index representing its chosen leaf. -/
theorem run_bornMass_eq_instrumentProb {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v)
    (ρ : Operator D) :
    ∃ i : Fin (c.next v).leafCount,
      (c.next v).leaf O i = (paths v).record O ∧
      (c.run O paths).bornMass ρ =
        instrumentProb ((c.next v).instrument O hO (hp v)) ρ i := by
  obtain ⟨i, hi⟩ := (paths v).record_index O
  refine ⟨i, hi, ?_⟩
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  simp only [JointRecord.bornMass, JointRecord.branch]
  have hrun : (c.run O paths).leaf = some ((paths v).record O) := by
    simp [ReturnCall.run, hdec]
  rw [hrun]
  simp only []
  rw [HybridProgram.probability_law _ O hO (hp v) ρ i, hi]
  simp [Matrix.trace_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

/-- Summing pointwise sums of two natural-valued functions over a list equals the sum of their
separate list sums. -/
private theorem sum_map_add {α : Type} (f g : α → ℕ) :
    ∀ l : List α, (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_add f g l]
    omega

/-- Summing a list after replacing every entry by one gives the list's length. -/
private theorem sum_map_one {α : Type} (l : List α) :
    (l.map (fun _ => (1 : ℕ))).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]
    omega

/-- The duplicate-free native cursor trace starting at zero always contains its starting
position. -/
private theorem mem_cursorTrace_origin {M : NativeTape.Program Γ Λ} :
    ∀ (es : List (NativeTape.Tick Γ Λ)), 0 ∈ (NativeTape.cursorTrace M 0 es).eraseDups := by
  intro es
  rw [List.mem_eraseDups]
  induction es with
  | nil =>
    simp [NativeTape.cursorTrace, List.scanl]
  | cons e es ih =>
    simp [NativeTape.cursorTrace, List.scanl]

/-- Native CPU time equals the step count plus the sum of the absolute cursor displacements of
the recorded ticks. -/
theorem nativeCpuTime_eq (M : NativeTape.Program Γ Λ) (r : NativeTape.Result Γ Λ) :
    nativeCpuTime M r =
      r.steps + (r.trace.map (fun e => (NativeTape.tickDisplacement M e).natAbs)).sum := by
  have h := sum_map_add (fun _ => (1 : ℕ))
    (fun e => (NativeTape.tickDisplacement M e).natAbs) r.trace
  have h1 : (r.trace.map (fun _ => (1 : ℕ))).sum = r.trace.length := sum_map_one r.trace
  have h2 : r.trace.length = r.steps := rfl
  unfold nativeCpuTime nativeInstructionCost
  rw [h, h1, h2]

/-- The native CPU cost of a result is at least its recorded step count. -/
theorem nativeCpuTime_ge_steps (M : NativeTape.Program Γ Λ) (r : NativeTape.Result Γ Λ) :
    r.steps ≤ nativeCpuTime M r := by
  rw [nativeCpuTime_eq]
  exact Nat.le_add_right _ _

/-- Native peak space is positive because the cursor trace includes its initial position. -/
theorem nativePeakSpace_pos (M : NativeTape.Program Γ Λ) (r : NativeTape.Result Γ Λ) :
    0 < nativePeakSpace M r := by
  have h : 0 ∈ (NativeTape.cursorTrace M 0 r.trace).eraseDups :=
    mem_cursorTrace_origin (M := M) r.trace
  have hlen : (0 : ℕ) < (NativeTape.cursorTrace M 0 r.trace).eraseDups.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hz' : (NativeTape.cursorTrace M 0 r.trace).eraseDups = [] :=
      List.length_eq_zero_iff.mp hz
    rw [hz'] at h
    simp at h
  unfold nativePeakSpace
  exact hlen

/-- A successfully returned call records its native steps, consumed bits, CPU time, and visited
cursor positions together with the selected quantum counts. Quantum space is the operator
dimension, and communication is the decoded value's declared width. -/
theorem run_ledger_of_returned {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v) :
    (c.run O paths).clocks.nativeSteps = c.native.steps ∧
    (c.run O paths).clocks.nativeBits = c.native.bits.length ∧
    (c.run O paths).clocks.quantum = ((paths v).record O).counts ∧
    (c.run O paths).clocks.nativeCpu = nativeCpuTime c.program c.native ∧
    (c.run O paths).clocks.nativeSpace = nativePeakSpace c.program c.native ∧
    (c.run O paths).clocks.quantumSpace = D ∧
    (c.run O paths).clocks.communication = c.decodeWidth v := by
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  simp [ReturnCall.run, hdec, runClocks, HybridLeaf.counts]

/-- For a successfully returned call, native CPU time bounds native steps and peak space is the
sum of native and quantum space. Query counts come from the selected quantum leaf, and
communication equals the decoded value's width. -/
theorem run_ledger_separated {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v) :
    c.native.steps ≤ (c.run O paths).clocks.nativeCpu ∧
    (c.run O paths).clocks.peakSpace =
      (c.run O paths).clocks.nativeSpace + (c.run O paths).clocks.quantumSpace ∧
    (c.run O paths).clocks.queries = ((paths v).record O).counts.queries ∧
    (c.run O paths).clocks.communication = c.decodeWidth v := by
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  have hcpu : (c.run O paths).clocks.nativeCpu = nativeCpuTime c.program c.native := by
    simp [ReturnCall.run, hdec, runClocks]
  have hq : (c.run O paths).clocks.queries = ((paths v).record O).counts.queries := by
    simp [ReturnCall.run, hdec, runClocks, HybridLeaf.counts, Ledger.queries]
  obtain ⟨_, _, _, _, _, _, hcomm⟩ := run_ledger_of_returned (O := O) paths h hv
  refine ⟨?_, ?_, hq, hcomm⟩
  · rw [hcpu]
    exact nativeCpuTime_ge_steps c.program c.native
  · simp only [Ledger.peakSpace]

/-- The native execution attached to a return call uses at most the call's step budget. -/
theorem run_native_steps_le {c : ReturnCall Γ Λ D A V} :
    c.native.steps ≤ c.budget := by
  exact NativeTape.run_steps_le_budget c.program c.budget c.bits c.config

/-- Resuming a return call stopped for lack of fuel preserves the partition of the original
supplied bits into consumed and unread bits. -/
theorem resume_bits_partition {c : ReturnCall Γ Λ D A V} (extra : ℕ)
    (h : c.native.stop = NativeTape.Stop.fuel) :
    (NativeTape.resume c.program extra c.native).bits ++
      (NativeTape.resume c.program extra c.native).unread = c.bits := by
  rw [NativeTape.resume_bits_partition c.program extra c.native h]
  have hr := NativeTape.run_bits_partition c.program c.budget c.bits c.config
  simpa [ReturnCall.native] using hr

/-- The resumed joint record stores the resumed native result, its halted-only decoded value,
and the corresponding optional continuation leaf. -/
theorem run_resume {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v)) (extra : ℕ) :
    (c.resume O extra paths).native = NativeTape.resume c.program extra c.native ∧
    (c.resume O extra paths).value = c.decoded (NativeTape.resume c.program extra c.native) ∧
    (c.resume O extra paths).leaf =
      (c.decoded (NativeTape.resume c.program extra c.native)).map
        (fun v => (paths v).record O) := by
  cases hd : c.decoded (NativeTape.resume c.program extra c.native) with
  | none => simp [ReturnCall.resume, hd]
  | some v => simp [ReturnCall.resume, hd]

/-- If resumed native execution halts and decodes successfully, its joint branch equals an
instrument branch representing the chosen continuation leaf, assuming a unitary oracle and
legal continuations. -/
theorem resume_branch_eq_instrument {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (paths : ∀ v : V, HybridProgram.Path (c.next v)) (extra : ℕ)
    (hstop : (NativeTape.resume c.program extra c.native).stop = NativeTape.Stop.halted)
    {v : V} (hv : c.decode (NativeTape.resume c.program extra c.native).cfg = some v)
    (ρ : Operator D) :
    ∃ i : Fin (c.next v).leafCount,
      (c.next v).leaf O i = (paths v).record O ∧
      (c.resume O extra paths).branch ρ = ((c.next v).instrument O hO (hp v)).branch i ρ := by
  obtain ⟨i, hi⟩ := (paths v).record_index O
  refine ⟨i, hi, ?_⟩
  have hdec : c.decoded (NativeTape.resume c.program extra c.native) = some v := by
    simp [ReturnCall.decoded, hstop, hv]
  simp only [JointRecord.branch]
  have hrun : (c.resume O extra paths).leaf = some ((paths v).record O) := by
    simp [ReturnCall.resume, hdec]
  rw [hrun]
  simp only []
  rw [HybridProgram.branch_law _ O hO (hp v) ρ i, hi]

/-- Supplying more bits stores the resulting native execution and the value obtained by decoding
that result only if it has halted. -/
theorem run_supply {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v)) (more : List Bool) :
    (c.supply O more paths).native = NativeTape.supply c.program c.budget more c.native ∧
    (c.supply O more paths).value = c.decoded (NativeTape.supply c.program c.budget more c.native) := by
  cases hd : c.decoded (NativeTape.supply c.program c.budget more c.native) with
  | none => simp [ReturnCall.supply, hd]
  | some v => simp [ReturnCall.supply, hd]

/-- The action of a successfully returned call is left multiplication by a single operator that
does not depend on the input operator. -/
theorem run_action_state_independent {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (h : c.native.stop = NativeTape.Stop.halted) {v : V} (hv : c.decode c.native.cfg = some v) :
    ∃ A : Operator D, ∀ ρ : Operator D, (c.run O paths).action ρ = A * ρ := by
  have hdec : c.decoded c.native = some v := by
    simp [ReturnCall.decoded, h, hv]
  refine ⟨((paths v).record O).operator, ?_⟩
  intro ρ
  simp [ReturnCall.run, hdec, JointRecord.action, nativeAction]

/-- If the decoder always returns one fixed value, every halted native result selects that
value's continuation. -/
theorem selected_of_constant_decode {c : ReturnCall Γ Λ D A V} {r : NativeTape.Result Γ Λ}
    {v : V} (hv : ∀ cfg : Turing.TM0.Cfg Γ Λ, c.decode cfg = some v)
    (h : r.stop = NativeTape.Stop.halted) :
    c.selected r = some (c.next v) := by
  simp [ReturnCall.selected, ReturnCall.decoded, h, hv]

/-- Mapping a probability mass function through an injective function preserves each input's
mass at its image. -/
private theorem map_inj_apply {α β : Type} {p : PMF α} {f : α → β} (hf : Function.Injective f)
    (y : α) : p.map f (f y) = p y := by
  classical
  rw [PMF.map_apply]
  show (∑' (a : α), (if f y = f a then p a else 0)) = p y
  calc
    (∑' (a : α), (if f y = f a then p a else 0)) = (if f y = f y then p y else 0) := by
      refine tsum_eq_single (L := SummationFilter.unconditional α) (α := ℝ≥0∞) (β := α)
        (f := fun a => if f y = f a then p a else 0) y ?_
      intro a ha
      have hne : f y ≠ f a := fun h => ha (hf h.symm)
      simp [hne]
    _ = p y := if_pos rfl

/-- The joint law's nontermination outcome has exactly the mass of the native terminal law's
nontermination outcome. -/
theorem jointLaw_never {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (jointLaw c O hO hp ρ hρ) .never = (NativeTape.terminalLaw c.program c.config) none := by
  classical
  have hz : ∀ z, z ≠ none → (conditionalLaw c O hO hp ρ hρ z) .never = 0 := by
    intro z hz
    cases z with
    | none => exact absurd rfl hz
    | some r =>
      cases hd : c.decode r.cfg with
      | none => simp [conditionalLaw, hd, PMF.pure_apply]
      | some v => simp [conditionalLaw, hd, PMF.map_apply]
  rw [jointLaw]
  calc
    (jointLaw c O hO hp ρ hρ) .never
        = (NativeTape.terminalLaw c.program c.config) none *
            (conditionalLaw c O hO hp ρ hρ none) .never :=
          bind_apply_eq (p := NativeTape.terminalLaw c.program c.config)
            (f := conditionalLaw c O hO hp ρ hρ) (b := .never) (a := none) hz
    _ = (NativeTape.terminalLaw c.program c.config) none := by
          simp [conditionalLaw, PMF.pure_apply]

/-- If a native result's final configuration fails to decode, its undecoded joint outcome has
the same mass as that native terminal result. -/
theorem jointLaw_undecoded {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {r : NativeTape.Result Γ Λ} (hv : c.decode r.cfg = none) :
    (jointLaw c O hO hp ρ hρ) (.undecoded r) =
      (NativeTape.terminalLaw c.program c.config) (some r) := by
  classical
  have hz : ∀ z, z ≠ some r → (conditionalLaw c O hO hp ρ hρ z) (.undecoded r) = 0 := by
    intro z hz
    cases z with
    | none => simp [conditionalLaw, PMF.pure_apply]
    | some r' =>
      have hr' : r' ≠ r := by
        intro h
        exact hz (by simp [h])
      cases hd : c.decode r'.cfg with
      | none => simp [conditionalLaw, hd, PMF.pure_apply, Ne.symm hr']
      | some v => simp [conditionalLaw, hd, PMF.map_apply]
  rw [jointLaw]
  calc
    (jointLaw c O hO hp ρ hρ) (.undecoded r)
        = (NativeTape.terminalLaw c.program c.config) (some r) *
            (conditionalLaw c O hO hp ρ hρ (some r)) (.undecoded r) :=
          bind_apply_eq (p := NativeTape.terminalLaw c.program c.config)
            (f := conditionalLaw c O hO hp ρ hρ) (b := .undecoded r) (a := some r) hz
    _ = (NativeTape.terminalLaw c.program c.config) (some r) := by
          simp [conditionalLaw, hv, PMF.pure_apply]

/-- For a successfully decoded native result, the mass of a returned joint outcome factors as
its native terminal mass times the selected quantum leaf's probability. -/
theorem jointLaw_returned {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {r : NativeTape.Result Γ Λ} {v : V} {t : HybridLeaf D A} (hv : c.decode r.cfg = some v) :
    (jointLaw c O hO hp ρ hρ) (.returned r v t) =
      (NativeTape.terminalLaw c.program c.config) (some r) *
        (leafLaw (c.next v) O hO (hp v) ρ hρ) t := by
  classical
  have hz : ∀ z, z ≠ some r → (conditionalLaw c O hO hp ρ hρ z) (.returned r v t) = 0 := by
    intro z hz
    cases z with
    | none => simp [conditionalLaw, PMF.pure_apply]
    | some r' =>
      have hr' : r' ≠ r := by
        intro h
        exact hz (by simp [h])
      cases hd : c.decode r'.cfg with
      | none => simp [conditionalLaw, hd, PMF.pure_apply]
      | some v' => simp [conditionalLaw, hd, PMF.map_apply, Ne.symm hr']
  rw [jointLaw]
  calc
    (jointLaw c O hO hp ρ hρ) (.returned r v t)
        = (NativeTape.terminalLaw c.program c.config) (some r) *
            (conditionalLaw c O hO hp ρ hρ (some r)) (.returned r v t) :=
          bind_apply_eq (p := NativeTape.terminalLaw c.program c.config)
            (f := conditionalLaw c O hO hp ρ hρ) (b := .returned r v t) (a := some r) hz
    _ = (NativeTape.terminalLaw c.program c.config) (some r) *
        (leafLaw (c.next v) O hO (hp v) ρ hρ) t := by
          simp only [conditionalLaw, hv]
          rw [map_inj_apply (f := fun t' => JointOutcome.returned r v t')
            (by intro a b hab; exact (JointOutcome.returned.inj hab).2.2) t]

/-- A native result whose final configuration fails to decode assigns zero joint mass to every
returned outcome carrying that result. -/
theorem jointLaw_returned_of_undecoded {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {r : NativeTape.Result Γ Λ} {v : V} {t : HybridLeaf D A} (hv : c.decode r.cfg = none) :
    (jointLaw c O hO hp ρ hρ) (.returned r v t) = 0 := by
  classical
  have hz : ∀ z, z ≠ some r → (conditionalLaw c O hO hp ρ hρ z) (.returned r v t) = 0 := by
    intro z hz
    cases z with
    | none => simp [conditionalLaw, PMF.pure_apply]
    | some r' =>
      by_cases hrr : r' = r
      · subst hrr
        simp [conditionalLaw, hv, PMF.pure_apply]
      · cases hd : c.decode r'.cfg with
        | none => simp [conditionalLaw, hd, PMF.pure_apply]
        | some v' => simp [conditionalLaw, hd, PMF.map_apply, Ne.symm hrr]
  rw [jointLaw]
  calc
    (jointLaw c O hO hp ρ hρ) (.returned r v t)
        = (NativeTape.terminalLaw c.program c.config) (some r) *
            (conditionalLaw c O hO hp ρ hρ (some r)) (.returned r v t) :=
          bind_apply_eq (p := NativeTape.terminalLaw c.program c.config)
            (f := conditionalLaw c O hO hp ρ hρ) (b := .returned r v t) (a := some r) hz
    _ = 0 := by simp [conditionalLaw, hv, PMF.pure_apply]

/-- The joint law sums to one across nontermination, undecoded, and returned outcomes. -/
theorem jointLaw_total {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (∑' z : JointOutcome Γ Λ D A V, (jointLaw c O hO hp ρ hρ) z) = 1 :=
  PMF.tsum_coe (jointLaw c O hO hp ρ hρ)

/-- Summing returned joint outcomes over all quantum leaves for a fixed decoded native result
recovers that result's native terminal mass. -/
theorem jointLaw_fiber {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {r : NativeTape.Result Γ Λ} {v : V} (hv : c.decode r.cfg = some v) :
    (∑' t : HybridLeaf D A, (jointLaw c O hO hp ρ hρ) (.returned r v t)) =
      (NativeTape.terminalLaw c.program c.config) (some r) := by
  classical
  rw [tsum_congr (fun t => jointLaw_returned hO hp ρ hρ hv)]
  rw [ENNReal.tsum_mul_left]
  rw [PMF.tsum_coe]
  simp

/-- For a supported native terminal result that decodes successfully, native mass and returned
joint mass expose the fair-bit weight of its consumed word. Each selected-continuation
instrument probability similarly factors into its leaf's fair-coin weight and
conjugated-operator trace mass. -/
theorem fair_source_split {c : ReturnCall Γ Λ D A V} {O : Operator D}
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {r : NativeTape.Result Γ Λ} {v : V} {t : HybridLeaf D A}
    (hr : some r ∈ (NativeTape.terminalLaw c.program c.config).support)
    (hv : c.decode r.cfg = some v) (i : Fin (c.next v).leafCount) :
    (NativeTape.terminalLaw c.program c.config) (some r) = (1 / 2 : ℝ≥0∞)^r.bits.length ∧
    (jointLaw c O hO hp ρ hρ) (.returned r v t) =
      (1 / 2 : ℝ≥0∞)^r.bits.length * (leafLaw (c.next v) O hO (hp v) ρ hρ) t ∧
    instrumentProb ((c.next v).instrument O hO (hp v)) ρ i =
      ((1 / 2 : ℝ)^((c.next v).leaf O i).coins.length) *
        (Matrix.trace (conjBranch ((c.next v).leaf O i).operator ρ)).re := by
  refine ⟨?_, ?_, ?_⟩
  · rw [NativeTape.terminalLaw_some]
    exact haltedMass_weight c.program c.config r hr
  · rw [jointLaw_returned hO hp ρ hρ hv, NativeTape.terminalLaw_some]
    rw [haltedMass_weight c.program c.config r hr]
  · rw [HybridProgram.probability_law _ O hO (hp v) ρ i]
    simp [CoinCode.wordWeight]

/-- The combined fair word has length equal to the native consumed-bit count plus the quantum
leaf's coin count. -/
theorem fairWord_length {Γ Λ : Type} [Inhabited Γ] {D : ℕ} {A : Type}
    (r : NativeTape.Result Γ Λ) (t : HybridLeaf D A) :
    (fairWord r t).length = r.bits.length + t.coins.length := by
  simp [fairWord]

/-- For a halted call with a decoded return, collect native budget and bit conservation,
joint-law normalization, continuation selection, and instrument-branch compatibility. The
conclusion also identifies the action and the separate native, quantum, and communication
ledger entries. -/
theorem clause16_complete {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] {D : ℕ} {A V : Type}
    (c : ReturnCall Γ Λ D A V) (O : Operator D)
    (hO : O ∈ Matrix.unitaryGroup (Fin D) ℂ) (hp : ∀ v : V, (c.next v).Legal)
    (paths : ∀ v : V, HybridProgram.Path (c.next v))
    (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {v : V} (hv : c.decode c.native.cfg = some v)
    (hstop : c.native.stop = NativeTape.Stop.halted) :
    c.native.steps ≤ c.budget ∧
    c.native.bits.length ≤ c.bits.length ∧
    c.native.bits ++ c.native.unread = c.bits ∧
    (∑' z : JointOutcome Γ Λ D A V, (jointLaw c O hO hp ρ hρ) z) = 1 ∧
    (c.run O paths).value = some v ∧
    (c.run O paths).leaf = some ((paths v).record O) ∧
    (c.run O paths).native = c.native ∧
    (∃ i : Fin (c.next v).leafCount,
      (c.next v).leaf O i = (paths v).record O ∧
      (c.run O paths).branch ρ = ((c.next v).instrument O hO (hp v)).branch i ρ) ∧
    (c.run O paths).action ρ = ((paths v).record O).operator * ρ ∧
    (c.run O paths).clocks.nativeSteps = c.native.steps ∧
    (c.run O paths).clocks.nativeBits = c.native.bits.length ∧
    (c.run O paths).clocks.quantum = ((paths v).record O).counts ∧
    c.native.steps ≤ (c.run O paths).clocks.nativeCpu ∧
    (c.run O paths).clocks.nativeCpu = nativeCpuTime c.program c.native ∧
    (c.run O paths).clocks.nativeSpace = nativePeakSpace c.program c.native ∧
    (c.run O paths).clocks.quantumSpace = D ∧
    (c.run O paths).clocks.communication = c.decodeWidth v := by
  have hpart : c.native.bits ++ c.native.unread = c.bits := by
    exact NativeTape.run_bits_partition c.program c.budget c.bits c.config
  have hsteps : c.native.steps ≤ c.budget :=
    NativeTape.run_steps_le_budget c.program c.budget c.bits c.config
  have hlen : c.native.bits.length ≤ c.bits.length := by
    have h2 : c.bits.length = c.native.bits.length + c.native.unread.length := by
      rw [← hpart, List.length_append]
    rw [h2]
    exact Nat.le_add_right _ _
  have hled := run_ledger_of_returned (O := O) paths hstop hv
  refine ⟨hsteps, hlen, hpart, jointLaw_total hO hp ρ hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (run_returned paths hstop hv).1
  · exact (run_returned paths hstop hv).2.1
  · exact (run_returned paths hstop hv).2.2
  · obtain ⟨i, hi, hbr⟩ := run_branch_eq_instrument hO hp paths hstop hv ρ
    exact ⟨i, hi, hbr⟩
  · exact run_action_of_returned paths hstop hv ρ
  · exact hled.1
  · exact hled.2.1
  · exact hled.2.2.1
  · rw [hled.2.2.2.1]
    exact nativeCpuTime_ge_steps c.program c.native
  · exact hled.2.2.2.1
  · exact hled.2.2.2.2.1
  · exact hled.2.2.2.2.2.1
  · exact hled.2.2.2.2.2.2

end NativeHybridCallReturn

end Qatlib.Concepts.AdversaryBounds.AdvDuality
