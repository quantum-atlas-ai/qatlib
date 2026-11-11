/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs

/-!
# Dynamic live-wire resource accounting

This module computes live-wire and workspace peaks from execution trails and proves composition
and exchange identities. Work totals are invariant under exchanging two words; the corresponding
peak and final-live identities require both words to restore the initial live-wire list. These
resource distinctions complement the circuit model in [NielsenChuang2010].

Concrete examples distinguish reset and uncomputation from release, show that peak space is not
an allocation or word-length count, and compute the resources of `lcuDynamicWord`. The module
also proves additive composition of reference-error bounds and records stopping-cost ledgers.

## Main statements

* `account_livePeak_formula`: The live peak is the maximum of the initial size and the live-wire
  trail.
* `account_livePeak_exchange`: Exchanging balanced words preserves live peak.
* `ref_error_combination`: Reference errors add under the stated nonexpansiveness assumptions.
* `lcu_dynamic_word`: The LCU word has its synthesis gate count and peak workspace one.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib
open Qatlib
open scoped ENNReal

open Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsDefs
open Qatlib.Concepts.StoppingCore.InterruptBridge
open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
noncomputable section

/-- The intrinsic account of a dynamic step has live peak zero before execution-dependent
live-wire accounting. -/
theorem stepAccount_livePeak_zero (s : DynStep) : s.stepAccount.livePeak = 0 := by
  cases s with
  | oracle b ws => cases b <;> rfl
  | _ g => rfl
end
noncomputable section

/-- The intrinsic account of a dynamic step has workspace peak zero before execution-dependent
live-wire accounting. -/
theorem stepAccount_peakWorkspace_zero (s : DynStep) : s.stepAccount.peakWorkspace = 0 := by
  cases s with
  | oracle b ws => cases b <;> rfl
  | _ g => rfl
end
noncomputable section

/-- Executing one dynamic step updates the live peak to the maximum of its previous value and
the new live-list length. -/
theorem step_acc_livePeak (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.livePeak = max st.acc.livePeak (applyLive st.live s).length := by
  simp only [step, Account.seq, stepAccount_livePeak_zero]
  omega
end
noncomputable section

/-- Executing one dynamic step updates the workspace peak using the new live-list length minus
the base size. -/
theorem step_acc_peakWorkspace (base : ℕ) (st : RunState) (s : DynStep) :
    (step base st s).acc.peakWorkspace =
      max st.acc.peakWorkspace ((applyLive st.live s).length - base) := by
  simp only [step, Account.seq, stepAccount_peakWorkspace_zero]
  omega
end
noncomputable section

/-- The maximum of a nonempty trail is the maximum of its head and the maximum of its tail. -/
theorem maxTrail_cons (x : ℕ) (xs : List ℕ) : maxTrail (x :: xs) = max x (maxTrail xs) := rfl
end
noncomputable section

/-- Taking the maximum of three natural numbers satisfies the associative law. -/
theorem max_assoc_comm (a b c : ℕ) : max (max a b) c = max a (max b c) := by
  calc max (max a b) c = max (max b a) c := by rw [Nat.max_comm a b]
    _ = max b (max a c) := Nat.max_assoc _ _ _
    _ = max b (max c a) := by rw [Nat.max_comm a c]
    _ = max (max b c) a := (Nat.max_assoc _ _ _).symm
    _ = max a (max b c) := by rw [Nat.max_comm a (max b c)]
end
noncomputable section

/-- The maximum of concatenated trails is the maximum of their separate maxima. -/
theorem maxTrail_append (a b : List ℕ) : maxTrail (a ++ b) = max (maxTrail a) (maxTrail b) := by
  induction a with
  | nil => simp [maxTrail]
  | cons x a ih =>
      simp only [List.cons_append, maxTrail, ih]
      calc max x (max (maxTrail a) (maxTrail b))
          = max (max (maxTrail a) (maxTrail b)) x := Nat.max_comm _ _
        _ = max (maxTrail a) (max (maxTrail b) x) := Nat.max_assoc _ _ _
        _ = max (maxTrail a) (max x (maxTrail b)) := by rw [Nat.max_comm (maxTrail b) x]
        _ = max (max (maxTrail a) x) (maxTrail b) := (Nat.max_assoc _ _ _).symm
        _ = max (max x (maxTrail a)) (maxTrail b) := by rw [Nat.max_comm (maxTrail a) x]
end
noncomputable section

/-- The live-wire trail of a concatenated word is the first trail followed by the second trail
starting from the first word's final live list. -/
theorem liveTrail_append (live : List ℕ) (a b : List DynStep) :
    liveTrail live (a ++ b) = liveTrail live a ++ liveTrail (liveAfter live a) b := by
  induction a generalizing live with
  | nil => rfl
  | cons s a ih =>
      simp only [List.cons_append, liveTrail, liveAfter, List.foldl_cons, ih]
end
noncomputable section

/-- The workspace trail of a concatenated word is the first trail followed by the second trail
starting from the first word's final live list. -/
theorem wsTrail_append (base : ℕ) (live : List ℕ) (a b : List DynStep) :
    wsTrail base live (a ++ b) = wsTrail base live a ++ wsTrail base (liveAfter live a) b := by
  induction a generalizing live with
  | nil => rfl
  | cons s a ih =>
      simp only [List.cons_append, wsTrail, liveAfter, List.foldl_cons, ih]
end
noncomputable section

/-- The final live peak is the maximum of the initial account peak and the maximum live-wire
trail value. -/
theorem runFrom_livePeak (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.livePeak = max st.acc.livePeak (maxTrail (liveTrail st.live ops)) := by
  induction ops generalizing st with
  | nil =>
      rw [runFrom_nil]
      simp [maxTrail, liveTrail]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_live]
      rw [step_acc_livePeak]
      simp only [liveTrail, maxTrail]
      exact max_assoc_comm _ _ _
end
noncomputable section

/-- The final workspace peak is the maximum of the initial account peak and the maximum
workspace-trail value. -/
theorem runFrom_peakWorkspace (base : ℕ) (st : RunState) (ops : List DynStep) :
    (runFrom base st ops).acc.peakWorkspace =
      max st.acc.peakWorkspace (maxTrail (wsTrail base st.live ops)) := by
  induction ops generalizing st with
  | nil =>
      rw [runFrom_nil]
      simp [maxTrail, wsTrail]
  | cons s ops ih =>
      rw [runFrom_cons, ih, step_live]
      rw [step_acc_peakWorkspace]
      simp only [wsTrail, maxTrail]
      exact max_assoc_comm _ _ _
end
noncomputable section

/-- A word's live peak is the maximum of the base size and the maximum live-wire trail starting
from `List.range base`. -/
theorem account_livePeak_formula (base : ℕ) (ops : List DynStep) :
    (account base ops).livePeak = max base (maxTrail (liveTrail (List.range base) ops)) := by
  rw [account, runTrace_eq, runFrom_livePeak]
  simp [initState, Account.initAccount, Account.zero]
end
noncomputable section

/-- A word's workspace peak is the maximum of zero and the workspace trail starting from
`List.range base`. -/
theorem account_peakWorkspace_formula (base : ℕ) (ops : List DynStep) :
    (account base ops).peakWorkspace = max 0 (maxTrail (wsTrail base (List.range base) ops)) := by
  rw [account, runTrace_eq, runFrom_peakWorkspace]
  simp [initState, Account.initAccount, Account.zero]
end
noncomputable section

/-- Applying the live-list updates from the base live list yields `finalLive base ops`. -/
theorem liveAfter_range_base (base : ℕ) (ops : List DynStep) :
    liveAfter (List.range base) ops = finalLive base ops := by
  unfold finalLive
  rw [runTrace_eq, runFrom_live]
  rfl
end
noncomputable section

/-- The final live list of a concatenated word is obtained by applying the second word's updates
to the first word's final live list. -/
theorem finalLive_append (base : ℕ) (a b : List DynStep) :
    finalLive base (a ++ b) = liveAfter (finalLive base a) b := by
  have h1 : finalLive base (a ++ b) = (runTrace base (a ++ b)).live := rfl
  have h2 : finalLive base a = (runTrace base a).live := rfl
  rw [h1, runTrace_append, runFrom_live, h2]
end
noncomputable section

/-- The empty dynamic word is balanced for every base size. -/
theorem balanced_nil (base : ℕ) : balanced base [] := by
  rfl
end
noncomputable section

/-- Exchanging two dynamic words preserves forward and adjoint queries, Hamiltonian calls and
ticks, macro and basic gates, depth, and classical-bit totals. -/
theorem account_work_exchange_conj (base : ℕ) (a b : List DynStep) :
    (account base (a ++ b)).queries = (account base (b ++ a)).queries ∧
    (account base (a ++ b)).adjointQueries = (account base (b ++ a)).adjointQueries ∧
    (account base (a ++ b)).hamiltonianCount = (account base (b ++ a)).hamiltonianCount ∧
    (account base (a ++ b)).macroGates = (account base (b ++ a)).macroGates ∧
    (account base (a ++ b)).basicGates = (account base (b ++ a)).basicGates ∧
    (account base (a ++ b)).depth = (account base (b ++ a)).depth ∧
    (account base (a ++ b)).classicalBits = (account base (b ++ a)).classicalBits ∧
    (account base (a ++ b)).hamiltonianTicks = (account base (b ++ a)).hamiltonianTicks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [account_queries, counters_append, seq_queries]; omega
  · simp only [account_adjointQueries, counters_append, seq_adjointQueries]; omega
  · simp only [account_hamiltonianCount, counters_append, seq_hamiltonianCount]; omega
  · simp only [account_macroGates, counters_append, seq_macroGates]; omega
  · simp only [account_basicGates, counters_append, seq_basicGates]; omega
  · simp only [account_depth, counters_append, seq_depth]; omega
  · simp only [account_classicalBits, counters_append, seq_classicalBits]; omega
  · simp only [account_hamiltonianTicks, counters_append, seq_hamiltonianTicks]; omega
end
noncomputable section

/-- Exchanging two dynamic words preserves their full work ledger. -/
theorem account_work_exchange (base : ℕ) (a b : List DynStep) :
    workOf (account base (a ++ b)) = workOf (account base (b ++ a)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := account_work_exchange_conj base a b
  unfold workOf
  simp only [WorkLedger.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
end
noncomputable section

/-- Exchanging two words that are each balanced at the same base preserves the live peak. -/
theorem account_livePeak_exchange (base : ℕ) (a b : List DynStep)
    (ha : balanced base a) (hb : balanced base b) :
    (account base (a ++ b)).livePeak = (account base (b ++ a)).livePeak := by
  have ha' : finalLive base a = List.range base := ha
  have hb' : finalLive base b = List.range base := hb
  rw [account_livePeak_formula, account_livePeak_formula]
  rw [liveTrail_append, liveTrail_append]
  rw [liveAfter_range_base, liveAfter_range_base]
  rw [ha', hb']
  rw [maxTrail_append, maxTrail_append]
  omega
end
noncomputable section

/-- Exchanging two words that are each balanced at the same base preserves the workspace peak. -/
theorem account_peakWorkspace_exchange (base : ℕ) (a b : List DynStep)
    (ha : balanced base a) (hb : balanced base b) :
    (account base (a ++ b)).peakWorkspace = (account base (b ++ a)).peakWorkspace := by
  have ha' : finalLive base a = List.range base := ha
  have hb' : finalLive base b = List.range base := hb
  rw [account_peakWorkspace_formula, account_peakWorkspace_formula]
  rw [wsTrail_append, wsTrail_append]
  rw [liveAfter_range_base, liveAfter_range_base]
  rw [ha', hb']
  rw [maxTrail_append, maxTrail_append]
  omega
end
noncomputable section

/-- Exchanging two words that are each balanced at the same base preserves the final live list. -/
theorem finalLive_exchange (base : ℕ) (a b : List DynStep)
    (ha : balanced base a) (hb : balanced base b) :
    finalLive base (a ++ b) = finalLive base (b ++ a) := by
  have ha' : finalLive base a = List.range base := ha
  have hb' : finalLive base b = List.range base := hb
  rw [finalLive_append, finalLive_append]
  rw [ha', hb']
  rw [liveAfter_range_base, liveAfter_range_base]
  rw [ha', hb']
end
noncomputable section

/-- The coordinate-sum vector norm `vnorm` satisfies the triangle inequality. -/
theorem vnorm_add_le {n : ℕ} (x y : Fin n → ℂ) : vnorm (x + y) ≤ vnorm x + vnorm y := by
  unfold vnorm
  calc (∑ i : Fin n, ‖(x + y) i‖) ≤ ∑ i : Fin n, (‖x i‖ + ‖y i‖) := by
        exact Finset.sum_le_sum fun i _ => norm_add_le (x i) (y i)
    _ = (∑ i : Fin n, ‖x i‖) + ∑ i : Fin n, ‖y i‖ := Finset.sum_add_distrib
end
noncomputable section

/-- Reference-error bounds for two matrix factors add under multiplication when `A` and `B'` are
nonexpansive and the stated error parameters are nonnegative. -/
theorem ref_error_combination (d r : ℕ) (A A' B B' : Matrix (Fin (d * r)) (Fin (d * r)) ℂ)
    (εA εB : ℝ) (hεA : 0 ≤ εA) (_hεB : 0 ≤ εB)
    (hA : Nonexpansive A) (hB' : Nonexpansive B')
    (hRA : RefBounded A A' εA) (hRB : RefBounded B B' εB) :
    RefBounded (A * B) (A' * B') (εA + εB) := by
  intro v
  have hsplit : (A * B - A' * B').mulVec v
      = A.mulVec ((B - B').mulVec v) + (A - A').mulVec (B'.mulVec v) := by
    have h1 : A.mulVec (B.mulVec v) - A.mulVec (B'.mulVec v) = A.mulVec ((B - B').mulVec v) := by
      rw [← Matrix.mulVec_sub]
      exact congrArg (fun w => A.mulVec w) (Matrix.sub_mulVec B B' v).symm
    have h2 : A.mulVec (B'.mulVec v) - A'.mulVec (B'.mulVec v)
        = (A - A').mulVec (B'.mulVec v) := (Matrix.sub_mulVec A A' (B'.mulVec v)).symm
    calc (A * B - A' * B').mulVec v
        = (A * B).mulVec v - (A' * B').mulVec v := Matrix.sub_mulVec _ _ _
      _ = A.mulVec (B.mulVec v) - A'.mulVec (B'.mulVec v) := by
          rw [← Matrix.mulVec_mulVec v A B]
          rw [← Matrix.mulVec_mulVec v A' B']
      _ = (A.mulVec (B.mulVec v) - A.mulVec (B'.mulVec v))
            + (A.mulVec (B'.mulVec v) - A'.mulVec (B'.mulVec v)) := by ring
      _ = A.mulVec ((B - B').mulVec v) + (A - A').mulVec (B'.mulVec v) := by rw [h1, h2]
  rw [hsplit]
  calc vnorm (A.mulVec ((B - B').mulVec v) + (A - A').mulVec (B'.mulVec v))
      ≤ vnorm (A.mulVec ((B - B').mulVec v)) + vnorm ((A - A').mulVec (B'.mulVec v)) :=
        vnorm_add_le _ _
    _ ≤ vnorm ((B - B').mulVec v) + εA * vnorm (B'.mulVec v) :=
      add_le_add (hA _) (hRA _)
    _ ≤ εB * vnorm v + εA * vnorm v :=
      add_le_add (hRB v) (mul_le_mul_of_nonneg_left (hB' v) hεA)
    _ = (εA + εB) * vnorm v := by ring
end
noncomputable section

/-- The LCU/QSVT account has basic-gate count equal to the synthesis and truncation counts added
together, with zero forward queries, adjoint queries, Hamiltonian calls, and live peak. -/
theorem lqAccount_ledgers (n q : ℕ) :
    (lqAccount n q).basicGates = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n + Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqJaTruncOpCount q ∧
    (lqAccount n q).queries = 0 ∧ (lqAccount n q).adjointQueries = 0 ∧
    (lqAccount n q).hamiltonianCount = 0 ∧ (lqAccount n q).livePeak = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩
end
noncomputable section

/-- The stopping account's classical-bit total is the sum of the preparation and trial costs. -/
theorem stoppingAccount_ledgers (prep trial : ℕ) :
    (stoppingAccount prep trial).classicalBits = prep + trial := rfl
end
noncomputable section

/-- The stopping account charges preparation plus trial bits; two accounts with costs two and
three charge ten bits, matching the stated alternating-retry expected cost. -/
theorem stopping_consumer_same_execution (prep trial : ℕ) :
    (stoppingAccount prep trial).classicalBits = prep + trial ∧
    (Account.seq (stoppingAccount 2 3) (stoppingAccount 2 3)).classicalBits = 10 ∧
    weightedExpectedCost alternatingRetryKernel alternatingRetryCost (.inr false) = 10 := by
  refine ⟨rfl, rfl, alternatingRetry_expectedCost⟩
end
noncomputable section

/-- There exist dynamic words for which the shorter word has strictly larger live peak. -/
theorem peak_space_is_dynamic :
    ∃ (a b : List DynStep),
      b.length < a.length ∧ (account 0 a).livePeak < (account 0 b).livePeak := by
  have h1 : liveTrail (List.range 0)
      [DynStep.alloc 0, DynStep.releaseClean 0, DynStep.alloc 1, DynStep.releaseClean 1]
      = [1, 0, 1, 0] := by rfl
  have h2 : liveTrail (List.range 0) [DynStep.alloc 0, DynStep.alloc 1] = [1, 2] := by rfl
  refine ⟨[DynStep.alloc 0, DynStep.releaseClean 0, DynStep.alloc 1, DynStep.releaseClean 1],
    [DynStep.alloc 0, DynStep.alloc 1], ?_⟩
  constructor
  · simp
  · rw [account_livePeak_formula, account_livePeak_formula, h1, h2]
    simp [maxTrail]
end
noncomputable section

/-- Resetting a wire leaves the live-wire list unchanged. -/
theorem applyLive_reset (live : List ℕ) (w : ℕ) :
    applyLive live (DynStep.reset w) = live := rfl
end
noncomputable section

/-- Uncomputing a wire leaves the live-wire list unchanged. -/
theorem applyLive_uncompute (live : List ℕ) (w : ℕ) :
    applyLive live (DynStep.uncompute w) = live := rfl
end
noncomputable section

/-- Releasing a dirty wire erases it from the live-wire list. -/
theorem applyLive_releaseDirty (live : List ℕ) (w : ℕ) :
    applyLive live (DynStep.releaseDirty w) = live.erase w := rfl
end
noncomputable section

/-- Allocation, clean release, dirty release, reset, and uncomputation carry classical-bit
charges one, two, four, three, and three, respectively. -/
theorem dynStep_release_bitCharges (w : ℕ) :
    (DynStep.alloc w).stepAccount.classicalBits = 1 ∧
    (DynStep.releaseClean w).stepAccount.classicalBits = 2 ∧
    (DynStep.releaseDirty w).stepAccount.classicalBits = 4 ∧
    (DynStep.reset w).stepAccount.classicalBits = 3 ∧
    (DynStep.uncompute w).stepAccount.classicalBits = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [DynStep.stepAccount, DynStep.bitCharge]
end
noncomputable section

/-- Allocating and then releasing a dirty wire has live and workspace peaks one, classical-bit
cost five, depth two, and an empty final live list. -/
theorem discard_charges_peak :
    (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).livePeak = 1 ∧
      (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).peakWorkspace = 1 ∧
      (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).classicalBits = 5 ∧
      (account 0 [DynStep.alloc 0, DynStep.releaseDirty 0]).depth = 2 ∧
      finalLive 0 [DynStep.alloc 0, DynStep.releaseDirty 0] = [] := by
  decide
end
noncomputable section

/-- Allocation followed by reset leaves the wire live and the word unbalanced; adding a clean
release makes the word balanced. -/
theorem reset_keeps_wire_live :
    finalLive 0 [DynStep.alloc 0, DynStep.reset 0] = [0] ∧
      ¬ balanced 0 [DynStep.alloc 0, DynStep.reset 0] ∧
      balanced 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0] := by
  have h1 : finalLive 0 [DynStep.alloc 0, DynStep.reset 0] = [0] := by decide
  refine ⟨h1, ?_, ?_⟩
  · intro h
    have h2 : finalLive 0 [DynStep.alloc 0, DynStep.reset 0] = List.range 0 := h
    have h3 : [0] ≠ List.range 0 := by decide
    exact h3 (h1.symm.trans h2)
  · have h4 : finalLive 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0] = [] := by
      decide
    have h5 : [] = List.range 0 := by decide
    exact h4.trans h5
end
noncomputable section

/-- Allocation followed by uncomputation leaves the wire live and the word unbalanced; adding a
clean release makes the word balanced. -/
theorem uncompute_keeps_wire_live :
    finalLive 0 [DynStep.alloc 0, DynStep.uncompute 0] = [0] ∧
      ¬ balanced 0 [DynStep.alloc 0, DynStep.uncompute 0] ∧
      balanced 0 [DynStep.alloc 0, DynStep.uncompute 0, DynStep.releaseClean 0] := by
  have h1 : finalLive 0 [DynStep.alloc 0, DynStep.uncompute 0] = [0] := by decide
  refine ⟨h1, ?_, ?_⟩
  · intro h
    have h2 : finalLive 0 [DynStep.alloc 0, DynStep.uncompute 0] = List.range 0 := h
    have h3 : [0] ≠ List.range 0 := by decide
    exact h3 (h1.symm.trans h2)
  · have h4 : finalLive 0 [DynStep.alloc 0, DynStep.uncompute 0, DynStep.releaseClean 0] = [] := by
      decide
    have h5 : [] = List.range 0 := by decide
    exact h4.trans h5
end
noncomputable section

/-- Allocation, reset, and clean release have classical-bit cost six, depth three, and live and
workspace peaks one. -/
theorem reset_discharge_ledger :
    (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).classicalBits = 6 ∧
      (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).depth = 3 ∧
      (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).livePeak = 1 ∧
      (account 0 [DynStep.alloc 0, DynStep.reset 0, DynStep.releaseClean 0]).peakWorkspace = 1 := by
  decide
end
noncomputable section

/-- Repeating allocation and clean release three times has live and workspace peaks one,
classical-bit cost nine, and depth six. -/
theorem peak_not_allocation_count :
    (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).livePeak = 1 ∧
      (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).peakWorkspace = 1 ∧
      (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).classicalBits = 9 ∧
      (account 0 (repeatWord [DynStep.alloc 0, DynStep.releaseClean 0] 3)).depth = 6 := by
  decide
end
noncomputable section

/-- Repeating a macro step `k` times gives a constant live-wire trail of length `k` at the
initial live-list length. -/
theorem liveTrail_replicate_macro (live : List ℕ) (k : ℕ) (g : FiniteGateCode) :
    liveTrail live (List.replicate k (DynStep.macro g)) = List.replicate k live.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, liveTrail]
      have happ : applyLive live (DynStep.macro g) = live := rfl
      rw [happ]
      rw [ih]
      rfl
end
noncomputable section

/-- Repeating a macro step `k` times gives a constant workspace trail at the initial live-list
length minus the base. -/
theorem wsTrail_replicate_macro (base : ℕ) (live : List ℕ) (k : ℕ) (g : FiniteGateCode) :
    wsTrail base live (List.replicate k (DynStep.macro g)) =
      List.replicate k (live.length - base) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, wsTrail]
      have happ : applyLive live (DynStep.macro g) = live := rfl
      rw [happ]
      rw [ih]
      rfl
end
noncomputable section

/-- A list of repeated macro steps preserves the live-wire list. -/
theorem liveAfter_replicate_macro (live : List ℕ) (k : ℕ) (g : FiniteGateCode) :
    liveAfter live (List.replicate k (DynStep.macro g)) = live := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, liveAfter, List.foldl_cons]
      have happ : applyLive live (DynStep.macro g) = live := rfl
      rw [happ]
      exact ih
end
noncomputable section

/-- The maximum of `k` copies of `x` is zero when `k` is zero and `x` otherwise. -/
theorem maxTrail_replicate (x : ℕ) (k : ℕ) :
    maxTrail (List.replicate k x) = if k = 0 then 0 else x := by
  induction k with
  | zero => simp [maxTrail]
  | succ k ih =>
      rw [List.replicate_succ, maxTrail_cons, ih]
      by_cases hk : k = 0
      · subst hk
        simp
      · rw [if_neg hk, if_neg (by omega : (k + 1) ≠ 0)]
        exact Nat.max_eq_left (le_refl x)
end
noncomputable section

/-- A word of `k` macro steps has basic-gate count `k`. -/
theorem counters_replicate_macro (k : ℕ) (g : FiniteGateCode) :
    (counters (List.replicate k (DynStep.macro g))).basicGates = k := by
  induction k with
  | zero => simp [counters_nil, Account.zero]
  | succ k ih =>
      rw [List.replicate_succ, counters_cons, seq_basicGates]
      have h1 : (DynStep.macro g).stepAccount.basicGates = 1 := rfl
      rw [h1]
      omega
end
noncomputable section

/-- The basic-gate count of the LCU dynamic word is `n * (8 * n + 28)`. -/
theorem counters_lcuDynamicWord (n : ℕ) :
    (counters (lcuDynamicWord n)).basicGates = n * (8 * n + 28) := by
  have h2 : (counters [DynStep.alloc 0, DynStep.uncompute 0]).basicGates = 0 := by
    rw [counters_cons, seq_basicGates]
    have h1 : (DynStep.alloc 0).stepAccount.basicGates = 0 := rfl
    rw [h1]
    rw [counters_cons, seq_basicGates]
    have h3 : (DynStep.uncompute 0).stepAccount.basicGates = 0 := rfl
    rw [h3]
    simp [counters_nil, Account.zero]
  have h4 : (counters (List.replicate (n * (8 * n + 28)) (DynStep.macro (.h 0)))).basicGates
      = n * (8 * n + 28) := counters_replicate_macro _ _
  unfold lcuDynamicWord
  rw [counters_append, seq_basicGates, h4, h2]
  rfl
end
noncomputable section

/-- The LCU word's live-wire trail stays at the initial size for `n * (8 * n + 28)` steps and
then records two steps at that size plus one. -/
theorem liveTrail_lcuDynamicWord (live : List ℕ) (n : ℕ) :
    liveTrail live (lcuDynamicWord n) =
      List.replicate (n * (8 * n + 28)) live.length ++ [live.length + 1, live.length + 1] := by
  rw [lcuDynamicWord, liveTrail_append, liveTrail_replicate_macro,
    liveAfter_replicate_macro]
  have h3 : liveTrail live [DynStep.alloc 0, DynStep.uncompute 0]
      = [live.length + 1, live.length + 1] := by rfl
  rw [h3]
end
noncomputable section

/-- The LCU word's workspace trail is obtained by subtracting the base from its initial live
size and from the size after one additional wire becomes live. -/
theorem wsTrail_lcuDynamicWord (base : ℕ) (live : List ℕ) (n : ℕ) :
    wsTrail base live (lcuDynamicWord n) =
      List.replicate (n * (8 * n + 28)) (live.length - base) ++
        [live.length + 1 - base, live.length + 1 - base] := by
  rw [lcuDynamicWord, wsTrail_append, wsTrail_replicate_macro,
    liveAfter_replicate_macro]
  have h3 : wsTrail base live [DynStep.alloc 0, DynStep.uncompute 0]
      = [live.length + 1 - base, live.length + 1 - base] := by rfl
  rw [h3]
end
noncomputable section

/-- The LCU dynamic word has basic-gate count `lqSynthOpCount n` and both live peak and
workspace peak equal to one. -/
theorem lcu_dynamic_word (n : ℕ) :
    (account 0 (lcuDynamicWord n)).basicGates = Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.lqSynthOpCount n ∧
    (account 0 (lcuDynamicWord n)).livePeak = 1 ∧
    (account 0 (lcuDynamicWord n)).peakWorkspace = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [account_basicGates, counters_lcuDynamicWord]
    rfl
  · rw [account_livePeak_formula, liveTrail_lcuDynamicWord, maxTrail_append,
      maxTrail_replicate]
    simp [maxTrail, List.range_zero]
  · rw [account_peakWorkspace_formula, wsTrail_lcuDynamicWord, maxTrail_append,
      maxTrail_replicate]
    simp [maxTrail, List.range_zero]
end
end Qatlib.Concepts.AdversaryBounds.AdvDuality.ResourceBoundsTransportLiveWire
