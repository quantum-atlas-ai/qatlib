/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.SketchArith.TransposeAccess.FinDistTransport
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
set_option warningAsError false

set_option autoImplicit false
open scoped Classical BigOperators ENNReal
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.TransposeAccess
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.StoppingCore.BranchCostCore

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.SqEstimation.HierarchicalSQ

structure ClosureNativeRandom where
  uniform : (n : ℕ) → FinDist (Option (Fin n))
  uniform_some : ∀ n (j : Fin n), (uniform n).prob (some j)=1/(n:ℝ)
  uniform_none : ∀ n, (uniform n).prob none=if n=0 then 1 else 0
  coin : ℝ → FinDist Bool
  coin_true : ∀ r, (coin r).prob true=max 0 (min 1 r)

noncomputable def closurePMF {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) : PMF X :=
  Classical.choose (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pmf p)
noncomputable def closureNormSq {X : Type} [Fintype X] (v : X → ℂ) : ℝ := ∑ i, Complex.normSq (v i)
noncomputable def closureMax {τ : ℕ} (q : Fin τ → ℝ) : ℝ := (List.ofFn q).foldl max 0
noncomputable def closureSum {τ : ℕ} (q : Fin τ → ℝ) : ℝ := ∑ t, q t
noncomputable def closureAccept {τ : ℕ} (q : Fin τ → ℝ) (t : Fin τ) : ℝ :=
  if closureMax q=0 then 0 else q t/closureMax q
noncomputable def closureRate {τ : ℕ} (q : Fin τ → ℝ) : ℝ := closureSum q/((τ:ℝ)*closureMax q)
noncomputable def closureSuccess {τ : ℕ} (q : Fin τ → ℝ) (T : ℕ) : ℝ :=
  if closureMax q=0 then 0 else 1-(1-closureRate q)^T

noncomputable def closureChoiceNext {τ : ℕ} (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (C : ℝ) :
    Unit → PMF (RandomizedExecution.Configuration Unit (Fin τ)) := fun _ =>
  (closurePMF (rand.uniform τ)).bind (fun o => match o with
    | none => PMF.pure (.inr ())
    | some t => (closurePMF (rand.coin (if C=0 then 0 else q t/C))).map (fun b => if b then .inl t else .inr ()))

noncomputable def closureChoiceRun {τ : ℕ} (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ) :
    CostedLaw (RandomizedExecution.Configuration Unit (Fin τ)) :=
  if closureMax q=0 then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inr ()) else
    RandomizedExecution.runFor (closureChoiceNext rand q (closureMax q)) T (.inr ())

inductive ClosureChoiceStatus (τ : ℕ) where
  | emptyWeights | timeout | chosen (t : Fin τ)
  deriving DecidableEq
noncomputable def closureChoiceStatus {τ : ℕ} (q : Fin τ → ℝ)
    (cfg : RandomizedExecution.Configuration Unit (Fin τ)) : ClosureChoiceStatus τ :=
  if closureMax q=0 then .emptyWeights else match cfg with
    | .inr _ => .timeout
    | .inl t => .chosen t

abbrev ClosureDrawResult (X : Type) := Option X × ℕ × ℕ × ℕ
def closureDrawRandomCalls {X : Type} (z : ClosureDrawResult X) : ℕ := 2*z.2.1
noncomputable def closureDraw {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ) (native : Fin τ → FinDist X) :
    PMF (ClosureDrawResult X) :=
  PMF.bind (closureChoiceRun rand q T) (fun z => match z.1 with
    | .inr _ => PMF.pure (none,z.2,0,0)
    | .inl t => (closurePMF (native t)).map (fun x => (some x,z.2,1,0)))
noncomputable def closureChoiceUnbounded {τ : ℕ} (rand : ClosureNativeRandom) (q : Fin τ → ℝ) :
    PMF (Option (Fin τ × ℕ)) :=
  generalUnboundedLaw (closureChoiceNext rand q (closureMax q)) (.inr ())
noncomputable def closureUnboundedDraw {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X) :
    PMF (ClosureDrawResult X) :=
  PMF.bind (closureChoiceUnbounded rand q) (fun z => match z with
    | none => PMF.pure (none,0,0,0)
    | some (t,k) => (closurePMF (native t)).map (fun x => (some x,k,1,0)))

noncomputable def closureDrawMass {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ) (native : Fin τ → FinDist X) (x : X) : ℝ :=
  (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureDraw rand q T native) (fun z => z.1=some x)).toReal

theorem closurePMF_apply {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (x : X) :
    closurePMF p x = ENNReal.ofReal (p.prob x) := Classical.choose_spec (Qatlib.Concepts.SketchArith.TransposeAccess.FinDist.exists_pmf p) x

theorem closurePMF_toReal {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (x : X) :
    (closurePMF p x).toReal = p.prob x := by
  rw [closurePMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

private theorem closure_max_fold_bounds (xs : List ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hnn : ∀ x ∈ xs, 0 ≤ x) :
    c ≤ xs.foldl max c ∧ (∀ x ∈ xs, x ≤ xs.foldl max c) ∧
      xs.foldl max c ≤ c+xs.sum := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    have hx := hnn x (by simp)
    have ht := ih (max c x) (le_trans hc (le_max_left _ _))
      (fun y hy => hnn y (List.mem_cons_of_mem x hy))
    simp only [List.foldl_cons]
    refine ⟨le_trans (le_max_left _ _) ht.1, ?_, ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact le_trans (le_max_right _ _) ht.1
      · exact ht.2.1 y hy
    · have hm : max c x ≤ c+x := max_le (by linarith) (by linarith)
      have h := ht.2.2
      simp only [List.sum_cons]
      linarith

theorem closureMax_bounds {τ : ℕ} (q : Fin τ → ℝ) (hnn : ∀ t, 0 ≤ q t) :
    0 ≤ closureMax q ∧ (∀ t, q t ≤ closureMax q) ∧
    closureMax q ≤ closureSum q ∧ closureSum q ≤ (τ : ℝ)*closureMax q := by
  have h := closure_max_fold_bounds (List.ofFn q) 0 (le_refl _)
    (fun x hx => by obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hnn i)
  have hpoint : ∀ t, q t ≤ closureMax q :=
    fun t => h.2.1 _ (List.mem_ofFn.mpr ⟨t, rfl⟩)
  refine ⟨h.1, hpoint, ?_, ?_⟩
  · simpa only [zero_add, List.sum_ofFn] using! h.2.2
  · exact (Finset.sum_le_sum (fun t _ => hpoint t)).trans_eq (by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin])

theorem closure_positive_rate {τ : ℕ} (q : Fin τ → ℝ) (hnn : ∀ t, 0 ≤ q t)
    (hs : 0 < closureSum q) :
    0 < closureMax q ∧ 0 < τ ∧
    (1/(τ : ℝ) ≤ closureRate q ∧ closureRate q ≤ 1) ∧
    (∀ t, 0 ≤ closureAccept q t ∧ closureAccept q t ≤ 1) := by
  have hb := closureMax_bounds q hnn
  have hC : 0 < closureMax q := by
    have hτ : (0 : ℝ) ≤ τ := Nat.cast_nonneg _
    have hu := hb.2.2.2
    nlinarith
  have hτ : 0 < τ := by
    by_contra hn
    have ht : τ = 0 := by omega
    subst τ
    simp [closureSum] at hs
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hden : 0 < (τ : ℝ)*closureMax q := mul_pos hτr hC
  refine ⟨hC, hτ, ⟨?_, ?_⟩, ?_⟩
  · unfold closureRate
    apply (div_le_div_iff₀ hτr hden).mpr
    have h := mul_le_mul_of_nonneg_right hb.2.2.1 hτr.le
    nlinarith
  · exact (div_le_one hden).mpr hb.2.2.2
  · intro t
    simp only [closureAccept, if_neg hC.ne']
    exact ⟨div_nonneg (hnn t) hC.le, (div_le_one hC).mpr (hb.2.1 t)⟩

private theorem closureChoiceNext_inl {τ : ℕ} (rand : ClosureNativeRandom)
    (q : Fin τ → ℝ) (C : ℝ) (hC : C ≠ 0) (t : Fin τ) :
    closureChoiceNext rand q C () (.inl t) =
      closurePMF (rand.uniform τ) (some t)*closurePMF (rand.coin (q t/C)) true := by
  simp [closureChoiceNext, if_neg hC, PMF.bind_apply, PMF.map_apply,
    tsum_fintype, Fintype.sum_option, eq_comm]

private theorem closure_pmf_sum_real {X : Type} [Fintype X] (p : PMF X) :
    ∑ x, (p x).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => p.apply_ne_top x)] at h
  simpa only [ENNReal.toReal_one] using h

theorem native_coefficient_choice_actual_step (τ : ℕ) (rand : ClosureNativeRandom)
    (q : Fin τ → ℝ) (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) :
    0 < closureMax q ∧ (1/(τ : ℝ) ≤ closureRate q ∧ closureRate q ≤ 1) ∧
    (∀ t, 0 ≤ closureAccept q t ∧ closureAccept q t ≤ 1) ∧
    (∀ t, (closureChoiceNext rand q (closureMax q) () (.inl t)).toReal =
      q t/((τ : ℝ)*closureMax q)) ∧
    (closureChoiceNext rand q (closureMax q) () (.inr ())).toReal = 1-closureRate q := by
  have hb := closure_positive_rate q hnn hs
  have hC := hb.1
  have hpoint (t : Fin τ) : (closureChoiceNext rand q (closureMax q) () (.inl t)).toReal =
      q t/((τ : ℝ)*closureMax q) := by
    have hn : 0 ≤ q t/closureMax q := div_nonneg (hnn t) hC.le
    have hu : q t/closureMax q ≤ 1 := (div_le_one hC).mpr ((closureMax_bounds q hnn).2.1 t)
    rw [closureChoiceNext_inl rand q _ hC.ne', ENNReal.toReal_mul,
      closurePMF_toReal, closurePMF_toReal, rand.uniform_some, rand.coin_true,
      min_eq_right hu, max_eq_right hn]
    have hτ : (τ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb.2.1)
    field_simp
  refine ⟨hC, hb.2.2.1, hb.2.2.2, hpoint, ?_⟩
  have htotal := closure_pmf_sum_real (closureChoiceNext rand q (closureMax q) ())
  rw [Fintype.sum_sum_type] at htotal
  simp only [Fintype.sum_unique] at htotal
  simp_rw [hpoint] at htotal
  rw [← Finset.sum_div] at htotal
  change closureRate q + _ = 1 at htotal
  linarith

theorem native_coefficient_choice_empty_weight_diagnostic (τ : ℕ) (rand : ClosureNativeRandom)
    (q : Fin τ → ℝ) (T : ℕ) (hz : ∀ t, q t = 0) :
    closureChoiceRun rand q T = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inr ()) ∧
    (∀ z ∈ (closureChoiceRun rand q T).support,
      closureChoiceStatus q z.1 = .emptyWeights ∧ z.2 = 0) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (closureChoiceRun rand q T) = 0 := by
  have hb := closureMax_bounds q (fun t => by rw [hz t])
  have hsum : closureSum q = 0 := by simp [closureSum, hz]
  have hmax : closureMax q = 0 := le_antisymm (hsum ▸ hb.2.2.1) hb.1
  have hret : closureChoiceRun rand q T = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inr ()) := by
    simp [closureChoiceRun, hmax]
  refine ⟨hret, ?_, by rw [hret]; simp⟩
  intro z hz'
  rw [hret] at hz'
  have heq : z = (.inr (),0) := (PMF.mem_support_pure_iff _ _).mp hz'
  simp [heq, closureChoiceStatus, hmax]

private theorem closure_next_expectation {O : Type} [Fintype O]
    (next : Unit → PMF (O ⊕ Unit)) (W : O ⊕ Unit → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (next ()) W =
      (∑ o, next () (.inl o)*W (.inl o)) + next () (.inr ())*W (.inr ()) := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [tsum_sum_type']
  simp only [tsum_fintype, Fintype.sum_unique]

private theorem closure_run_event_step {O : Type} [Fintype O]
    (next : Unit → PMF (O ⊕ Unit)) (T : ℕ) (E : O ⊕ Unit → Prop) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (RandomizedExecution.runFor next (T+1) (.inr ())) (fun z => E z.1) =
      (∑ o, next () (.inl o)*(if E (.inl o) then 1 else 0)) +
      next () (.inr ())*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (RandomizedExecution.runFor next T (.inr ())) (fun z => E z.1) := by
  have hhalt (o : O) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (RandomizedExecution.runFor next T (.inl o)))
      (fun z => E z.1) = if E (.inl o) then 1 else 0 := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general,
        RandomizedExecution.runFor_halted, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret]
  have hrun : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (RandomizedExecution.runFor next T (.inr ()))) (fun z => E z.1) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (RandomizedExecution.runFor next T (.inr ())) (fun z => E z.1) := by
    rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_charge_general]
  rw [show RandomizedExecution.runFor next (T+1) (.inr ()) =
      PMF.bind (RandomizedExecution.tick next (.inr ()))
        (fun x => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge x.2 (RandomizedExecution.runFor next T x.1)) from rfl,
    Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_bind_general]
  rw [show RandomizedExecution.tick next (.inr ()) = (next ()).map (fun c => (c,1)) from rfl,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, closure_next_expectation]
  (try dsimp only)
  simp_rw [hhalt, hrun]

private theorem closure_run_pending {O : Type} [Fintype O]
    (next : Unit → PMF (O ⊕ Unit)) (T : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (RandomizedExecution.runFor next T (.inr ()))
      (fun z => z.1 = .inr ()) = (next () (.inr ()))^T := by
  induction T with
  | zero => simp [RandomizedExecution.runFor_zero, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret]
  | succ T ih =>
    rw [closure_run_event_step next T (fun c => c = .inr ())]
    simp only [Sum.inl_ne_inr, if_false, mul_zero, Finset.sum_const_zero, zero_add, ih]
    rw [pow_succ']

private theorem closure_run_halt {O : Type} [Fintype O] [DecidableEq O]
    (next : Unit → PMF (O ⊕ Unit)) (T : ℕ) (o : O) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (RandomizedExecution.runFor next T (.inr ()))
      (fun z => z.1 = .inl o) = next () (.inl o)*
        ∑ k ∈ Finset.range T, (next () (.inr ()))^k := by
  induction T with
  | zero => simp [RandomizedExecution.runFor_zero, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_ret]
  | succ T ih =>
    rw [closure_run_event_step next T (fun c => c = .inl o), ih, geom_sum_succ]
    simp only [Sum.inl.injEq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

private theorem closure_general_pending {O : Type} [Fintype O]
    (next : Unit → PMF (O ⊕ Unit)) (T : ℕ) :
    generalPendingMass next (.inr ()) T = (next () (.inr ()))^T := by
  unfold generalPendingMass
  have hiff : ∀ z : (O ⊕ Unit) × ℕ, (∃ s, z.1 = .inr s) ↔ z.1 = .inr () := by
    intro z
    constructor
    · rintro ⟨s, hs⟩; cases s; exact hs
    · intro h; exact ⟨(), h⟩
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr hiff]
  exact closure_run_pending next T

private theorem closure_haltJoint_zero {O : Type} (next : Unit → PMF (O ⊕ Unit)) (o : O) :
    haltJoint next (.inr ()) o 0 = 0 := by
  exact GeneralExecution.runFor_point_halt_zero next 0 () o

private theorem closure_haltJoint_succ {O : Type} [Fintype O] [DecidableEq O]
    (next : Unit → PMF (O ⊕ Unit)) (T : ℕ) (o : O) :
    haltJoint next (.inr ()) o (T+1) = next () (.inl o)*(next () (.inr ()))^T := by
  have h0 := general_finite_output_mass next (.inr ()) T o
  have h1 := general_finite_output_mass next (.inr ()) (T+1) o
  have hfin : (∑ k ∈ Finset.range (T+1), haltJoint next (.inr ()) o k) ≠ ⊤ := by
    rw [← h0]
    exact ne_of_lt
        (lt_of_le_of_lt (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _) (by simp))
  have heq : (∑ k ∈ Finset.range (T+1), haltJoint next (.inr ()) o k) +
      haltJoint next (.inr ()) o (T+1) =
      (∑ k ∈ Finset.range (T+1), haltJoint next (.inr ()) o k) +
        next () (.inl o)*(next () (.inr ()))^T := by
    calc _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (RandomizedExecution.runFor next (T+1) (.inr ())) (fun z => z.1 = .inl o) := by
          rw [h1]
          exact (Finset.sum_range_succ (fun k => haltJoint next (.inr ()) o k) (T+1)).symm
      _ = next () (.inl o)*∑ k ∈ Finset.range (T+1), (next () (.inr ()))^k :=
        closure_run_halt next (T+1) o
      _ = next () (.inl o)*(∑ k ∈ Finset.range T, (next () (.inr ()))^k) +
          next () (.inl o)*(next () (.inr ()))^T := by rw [Finset.sum_range_succ, mul_add]
      _ = _ := by rw [← closure_run_halt next T o, h0]
  exact (WithTop.add_left_inj hfin).mp heq

private theorem closure_halt_marginal {O : Type} [Fintype O] [DecidableEq O]
    (next : Unit → PMF (O ⊕ Unit)) (o : O) :
    (∑' k, haltJoint next (.inr ()) o k) =
      next () (.inl o)*(1-next () (.inr ()))⁻¹ := by
  rw [tsum_eq_zero_add' ENNReal.summable, closure_haltJoint_zero, zero_add]
  simp_rw [closure_haltJoint_succ]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

private def closureOptionEquiv (α : Type) : Option α ≃ Unit ⊕ α where
  toFun
    | none => Sum.inl ()
    | some a => Sum.inr a
  invFun
    | Sum.inl () => none
    | Sum.inr a => some a
  left_inv
    | none => rfl
    | some _ => rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr _ => rfl

private theorem closure_tsum_option_split {α : Type} (F : Option α → ℝ≥0∞) :
    ∑' z : Option α, F z = F none + ∑' a : α, F (some a) := by
  have hsum := (ENNReal.summable
    (f := fun x : Unit ⊕ α => F ((closureOptionEquiv α).symm x))).hasSum
  rw [tsum_sum_type'] at hsum
  have hunit : (∑' x : Unit, F ((closureOptionEquiv α).symm (Sum.inl x))) = F none := by
    rw [tsum_fintype (L := SummationFilter.unconditional Unit)]
    simp [closureOptionEquiv]
  rw [hunit, tsum_congr (fun a : α => rfl)] at hsum
  exact ((Equiv.hasSum_iff (closureOptionEquiv α).symm).mp hsum).tsum_eq

private theorem closure_unbounded_event {O : Type} [Fintype O] [DecidableEq O]
    (next : Unit → PMF (O ⊕ Unit)) (o : O) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (generalUnboundedLaw next (.inr ()))
      (fun z => ∃ k, z = some (o,k)) = ∑' k, haltJoint next (.inr ()) o k := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [closure_tsum_option_split]
  have hnone : ¬∃ k : ℕ, (none : Option (O × ℕ)) = some (o,k) := by simp
  simp only [if_neg hnone, mul_zero, zero_add]
  rw [tsum_prod_type']
  have hsome (j : O) (k : ℕ) : (∃ k', some (j,k) = some (o,k')) ↔ j = o := by simp
  apply (tsum_eq_single o (fun j hj => ?_)).trans
  · apply tsum_congr
    intro k
    rw [if_pos (by exact ⟨k,rfl⟩), mul_one]
    rfl
  · apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [if_neg (fun h => hj ((hsome j k).mp h)), mul_zero]

private theorem closure_unbounded_cost {O : Type}
    (next : Unit → PMF (O ⊕ Unit)) (hne : generalNeverMass next (.inr ()) = 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (generalUnboundedLaw next (.inr ()))
      (fun z => match z with | none => 0 | some (_,k) => (k : ℝ≥0∞)) =
        generalUnboundedTime next (.inr ()) := by
  have h := (general_unbounded_actual_expected_time Unit O next (.inr ())).1
  rw [hne, mul_zero, add_zero] at h
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [closure_tsum_option_split]
  simp only [mul_zero, zero_add]
  rw [tsum_prod_type']
  rw [h]
  apply tsum_congr
  intro o
  apply tsum_congr
  intro k
  simp only [generalUnboundedLaw_apply, generalUnboundedMass_some]
  exact mul_comm _ _

theorem closure_choice_unbounded_time {τ : ℕ} (rand : ClosureNativeRandom)
    (q : Fin τ → ℝ) (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) :
    generalUnboundedTime (closureChoiceNext rand q (closureMax q)) (.inr ()) =
      ENNReal.ofReal (1/closureRate q) ∧
    closureChoiceUnbounded rand q none = 0 ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q)
      (fun z => match z with | none => 0 | some (_,k) => (k : ℝ≥0∞)) =
        ENNReal.ofReal (1/closureRate q) := by
  let next := closureChoiceNext rand q (closureMax q)
  have hstep := native_coefficient_choice_actual_step τ rand q hnn hs
  have hb := closure_positive_rate q hnn hs
  have hτ : (0 : ℝ) < τ := by exact_mod_cast hb.2.1
  have ha : 0 < closureRate q := div_pos hs (mul_pos hτ hb.1)
  have hu := hstep.2.1.2
  have hr : next () (.inr ()) = ENNReal.ofReal (1-closureRate q) := by
    rw [← ENNReal.ofReal_toReal ((next ()).apply_ne_top (.inr ())), hstep.2.2.2.2]
  have hsub : 1-next () (.inr ()) = ENNReal.ofReal (closureRate q) := by
    rw [hr, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1-closureRate q)]
    congr 1
    ring
  have htime : generalUnboundedTime next (.inr ()) = ENNReal.ofReal (1/closureRate q) := by
    unfold generalUnboundedTime
    simp_rw [closure_general_pending]
    rw [ENNReal.tsum_geometric, hsub, ← ENNReal.ofReal_inv_of_pos ha]
    simp only [one_div]
  have hnever : generalNeverMass next (.inr ()) = 0 :=
    (general_unbounded_actual_expected_time Unit (Fin τ) next (.inr ())).2.1
      (by rw [htime]; exact ENNReal.ofReal_lt_top)
  refine ⟨htime, hnever, ?_⟩
  unfold closureChoiceUnbounded
  convert (closure_unbounded_cost next hnever).trans htime using 1
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  rintro (_ | ⟨t,k⟩) <;> rfl

theorem native_coefficient_choice_joint_halt_and_cost (τ : ℕ) (rand : ClosureNativeRandom)
    (q : Fin τ → ℝ) (T : ℕ) (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceRun rand q T) (fun z => z.1 = .inr ())).toReal =
      (1-closureRate q)^T ∧
    (∀ t, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceRun rand q T) (fun z => z.1 = .inl t)).toReal =
      closureSuccess q T*q t/closureSum q) ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (closureChoiceRun rand q T)).toReal ≤ (τ : ℝ) ∧
    (1-closureRate q)^T ≤ Real.exp (-(T : ℝ)/(τ : ℝ)) ∧
    (∀ z ∈ (closureChoiceRun rand q T).support, z.2 ≤ T) ∧
    closureChoiceUnbounded rand q none = 0 ∧
    (∀ t, (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceUnbounded rand q)
      (fun z => ∃ k, z = some (t,k))).toReal = q t/closureSum q) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q)
      (fun z => match z with | none => 0 | some (_,k) => (k : ℝ≥0∞)) ≤ (τ : ℝ≥0∞) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q)
      (fun z => match z with | none => 0 | some (_,k) => (2*k : ℕ)) ≤ (2*τ : ℕ) := by
  let next := closureChoiceNext rand q (closureMax q)
  have hstep := native_coefficient_choice_actual_step τ rand q hnn hs
  have hb := closure_positive_rate q hnn hs
  have hC := hb.1
  have hτ : (0 : ℝ) < τ := by exact_mod_cast hb.2.1
  have ha : 0 < closureRate q := div_pos hs (mul_pos hτ hC)
  have hu := hstep.2.1.2
  have hr := hstep.2.2.2.2
  have ht := closure_choice_unbounded_time rand q hnn hs
  have hinv : 1/closureRate q ≤ (τ : ℝ) := by
    apply (div_le_iff₀ ha).mpr
    have hl := hstep.2.1.1
    have hmul := (div_le_iff₀ hτ).mp hl
    nlinarith
  have htimebound : generalUnboundedTime next (.inr ()) ≤ (τ : ℝ≥0∞) := by
    rw [ht.1]
    exact (ENNReal.ofReal_le_ofReal hinv).trans_eq (by simp)
  have hfinite : (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (closureChoiceRun rand q T)) ≤ (τ : ℝ≥0∞) := by
    rw [closureChoiceRun, if_neg hC.ne',
      (general_unbounded_actual_expected_time Unit (Fin τ) next (.inr ())).2.2]
    exact (ENNReal.sum_le_tsum _).trans htimebound
  refine ⟨?_, ?_, ?_, ?_, ?_, ht.2.1, ?_, ?_, ?_⟩
  · rw [closureChoiceRun, if_neg hC.ne', closure_run_pending, ENNReal.toReal_pow, hr]
  · intro t
    rw [closureChoiceRun, if_neg hC.ne', closure_run_halt, ENNReal.toReal_mul,
      hstep.2.2.2.1 t]
    rw [ENNReal.toReal_sum (fun k _ => ne_of_lt (lt_of_le_of_lt
      (pow_le_one' ((next ()).coe_le_one (.inr ())) k) ENNReal.one_lt_top))]
    simp only [ENNReal.toReal_pow]
    change (q t/((τ : ℝ)*closureMax q))*∑ k ∈ Finset.range T,
      (next () (.inr ())).toReal^k = _
    have hrnext : (next () (.inr ())).toReal = 1-closureRate q := hr
    simp_rw [hrnext]
    rw [geom_sum_eq (by linarith : 1-closureRate q ≠ 1) T]
    rw [closureSuccess, if_neg hC.ne']
    unfold closureRate
    field_simp [hs.ne', hC.ne', hτ.ne']
    ring
  · simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top τ) hfinite
  · have hbase : 1-closureRate q ≤ Real.exp (-closureRate q) := by
      have h := Real.add_one_le_exp (-closureRate q)
      linarith
    calc (1-closureRate q)^T ≤ (Real.exp (-closureRate q))^T :=
        pow_le_pow_left₀ (by linarith) hbase T
      _ = Real.exp ((T : ℝ)*(-closureRate q)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hstep.2.1.1 (Nat.cast_nonneg T)
        simp only [div_eq_mul_inv, one_mul] at hmul ⊢
        nlinarith
  · rw [closureChoiceRun, if_neg hC.ne']
    exact RandomizedExecution.runFor_bounded next T (.inr ())
  · intro t
    unfold closureChoiceUnbounded
    rw [closure_unbounded_event, closure_halt_marginal, ENNReal.toReal_mul,
      hstep.2.2.2.1 t, ENNReal.toReal_inv]
    have hsub : (1-next () (.inr ())).toReal = closureRate q := by
      rw [ENNReal.toReal_sub_of_le ((next ()).coe_le_one (.inr ())) ENNReal.one_ne_top,
        ENNReal.toReal_one, hr]
      ring
    rw [hsub]
    unfold closureRate
    field_simp
  · rw [ht.2.2]
    exact (ENNReal.ofReal_le_ofReal hinv).trans_eq (by simp)
  · have hdouble : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q)
        (fun z => match z with | none => 0 | some (_,k) => (2*k : ℕ)) =
        2*Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q)
          (fun z => match z with | none => 0 | some (_,k) => (k : ℝ≥0∞)) := by
      rw [← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
      apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
      intro z
      cases z with
      | none => simp
      | some p => simp [Nat.cast_mul]
    rw [hdouble, ht.2.2]
    exact (mul_le_mul' (le_refl 2) (ENNReal.ofReal_le_ofReal hinv)).trans_eq (by simp)

theorem closure_record_mixture_event {Ω Y : Type} {τ : ℕ}
    (p : PMF Ω) (index : Ω → Option (Fin τ)) (after : Ω → PMF Y) (E : Y → Prop)
    (mass : Fin τ → ℝ≥0∞)
    (hafter : ∀ ω, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (after ω) E =
      ∑ t, if index ω = some t then mass t else 0) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (p.bind after) E =
      ∑ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun ω => index ω = some t)*mass t := by
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p
      (fun ω => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (after ω) E) = _
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr hafter,
      Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_sum]
  apply Finset.sum_congr rfl
  intro t _
  have hfun : (fun ω => if index ω = some t then mass t else 0) =
      (fun ω => mass t*(if index ω = some t then 1 else 0)) := by
    funext ω
    split_ifs <;> simp
  rw [hfun, Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_const_mul]
  rw [mul_comm (mass t)]
  congr 1
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro ω
  by_cases h : index ω = some t <;> simp [h]

theorem closureDraw_event {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ)
    (native : Fin τ → FinDist X) (x : X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureDraw rand q T native) (fun z => z.1 = some x) =
      ∑ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceRun rand q T) (fun z => z.1 = .inl t)*
        closurePMF (native t) x := by
  unfold closureDraw
  let index := fun z : (Fin τ ⊕ Unit) × ℕ => match z.1 with
    | .inl t => some t | .inr _ => none
  have h := closure_record_mixture_event (closureChoiceRun rand q T) index
    (fun z => match z.1 with
      | .inr _ => PMF.pure (none,z.2,0,0)
      | .inl t => (closurePMF (native t)).map (fun y => (some y,z.2,1,0)))
    (fun z : ClosureDrawResult X => z.1 = some x) (fun t => closurePMF (native t) x) ?_
  · simpa only [index, show ∀ z : (Fin τ ⊕ Unit) × ℕ, ∀ t,
        (match z.1 with | .inl j => some j | .inr _ => none) = some t ↔ z.1 = .inl t by
          intro z t; cases z.1 <;> simp] using h
  · rintro ⟨cfg,k⟩
    cases cfg with
    | inr u => simp [index, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    | inl t =>
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
      simp only [Option.some.injEq]
      rw [GeneralExecution.event_point_mass]
      simp [index]

theorem closureUnboundedDraw_event {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X) (x : X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureUnboundedDraw rand q native) (fun z => z.1 = some x) =
      ∑ t, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceUnbounded rand q)
        (fun z => ∃ k, z = some (t,k))*closurePMF (native t) x := by
  unfold closureUnboundedDraw
  let index := fun z : Option (Fin τ × ℕ) => z.map Prod.fst
  have h := closure_record_mixture_event (closureChoiceUnbounded rand q) index
    (fun z => match z with
      | none => PMF.pure (none,0,0,0)
      | some (t,k) => (closurePMF (native t)).map (fun y => (some y,k,1,0)))
    (fun z : ClosureDrawResult X => z.1 = some x) (fun t => closurePMF (native t) x) ?_
  · have hiff : ∀ z : Option (Fin τ × ℕ), ∀ t, index z = some t ↔ ∃ k, z = some (t,k) := by
      intro z t
      cases z with
      | none => simp [index]
      | some p =>
        rcases p with ⟨j,k⟩
        simp [index]
    simpa only [hiff] using h
  · intro z
    cases z with
    | none => simp [index, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
    | some p =>
      rcases p with ⟨t,k⟩
      rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
      simp only [Option.some.injEq]
      rw [GeneralExecution.event_point_mass]
      simp [index]

theorem closureUnboundedDraw_attempts {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureUnboundedDraw rand q native) (fun z => (z.2.1 : ℝ≥0∞)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q)
        (fun z => match z with | none => 0 | some (_,k) => (k : ℝ≥0∞)) := by
  rw [closureUnboundedDraw, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  intro z
  cases z with
  | none => simp
  | some p => rcases p with ⟨t,k⟩; simp

theorem closureUnboundedDraw_native_calls {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X)
    (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureUnboundedDraw rand q native) (fun z => (z.2.2.1 : ℝ≥0∞)) = 1 := by
  have hnone := (closure_choice_unbounded_time rand q hnn hs).2.1
  have hsum := (closureChoiceUnbounded rand q).tsum_coe
  rw [closure_tsum_option_split, hnone, zero_add] at hsum
  rw [closureUnboundedDraw, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have hfun : (fun z => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (match z with
      | none => PMF.pure (none,0,0,0)
      | some (t,k) => (closurePMF (native t)).map (fun x => (some x,k,1,0)))
        (fun z : ClosureDrawResult X => (z.2.2.1 : ℝ≥0∞))) =
      (fun z : Option (Fin τ × ℕ) => if z = none then 0 else 1) := by
    funext z
    cases z with
    | none => simp
    | some p => rcases p with ⟨t,k⟩; simp
  rw [hfun]
  unfold Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation
  rw [closure_tsum_option_split]
  simp only [if_true, mul_zero, Option.some_ne_none, if_false, mul_one, zero_add]
  exact hsum

private theorem closure_event_product_ne_top {Ω X : Type} [Fintype X] [DecidableEq X]
    (p : PMF Ω) (E : Ω → Prop) (q : FinDist X) (x : X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p E*closurePMF q x ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt
    ((mul_le_mul' (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one p E) ((closurePMF q).coe_le_one x)).trans_eq (one_mul _))
    ENNReal.one_lt_top)

theorem closureDrawMass_formula {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ) (native : Fin τ → FinDist X)
    (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) (x : X) :
    closureDrawMass rand q T native x =
      closureSuccess q T/closureSum q * ∑ t, q t*(native t).prob x := by
  have h := native_coefficient_choice_joint_halt_and_cost τ rand q T hnn hs
  rw [closureDrawMass, closureDraw_event, ENNReal.toReal_sum (fun t _ =>
    closure_event_product_ne_top (closureChoiceRun rand q T) (fun z => z.1 = .inl t) (native t) x)]
  simp_rw [ENNReal.toReal_mul, h.2.1, closurePMF_toReal]
  simp_rw [show ∀ t, (closureSuccess q T*q t/closureSum q)*(native t).prob x =
      (closureSuccess q T/closureSum q)*(q t*(native t).prob x) by intro t; ring]
  rw [← Finset.mul_sum]

theorem closureUnboundedDrawMass_formula {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X)
    (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) (x : X) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureUnboundedDraw rand q native) (fun z => z.1 = some x)).toReal =
      (1/closureSum q)*∑ t, q t*(native t).prob x := by
  have h := native_coefficient_choice_joint_halt_and_cost τ rand q 0 hnn hs
  rw [closureUnboundedDraw_event, ENNReal.toReal_sum (fun t _ =>
    closure_event_product_ne_top (closureChoiceUnbounded rand q)
      (fun z => ∃ k, z = some (t,k)) (native t) x)]
  simp_rw [ENNReal.toReal_mul, h.2.2.2.2.2.2.1, closurePMF_toReal]
  simp_rw [show ∀ t, q t/closureSum q*(native t).prob x =
      (1/closureSum q)*(q t*(native t).prob x) by intro t; ring]
  rw [← Finset.mul_sum]

theorem closureDraw_zero {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ) (native : Fin τ → FinDist X)
    (hz : ∀ t, q t = 0) : closureDraw rand q T native = PMF.pure (none,0,0,0) := by
  rw [closureDraw, (native_coefficient_choice_empty_weight_diagnostic τ rand q T hz).1]
  simp [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret]

theorem closureUnboundedDraw_none {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X)
    (hnn : ∀ t, 0 ≤ q t) (hs : 0 < closureSum q) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureUnboundedDraw rand q native) (fun z => z.1 = none) = 0 := by
  have hnone := (closure_choice_unbounded_time rand q hnn hs).2.1
  unfold closureUnboundedDraw Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  calc _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceUnbounded rand q) (fun z => z = none) := by
        apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
        intro z
        cases z with
        | none => simp
        | some p => rcases p with ⟨t,k⟩; simp
    _ = 0 := by rw [GeneralExecution.event_point_mass, hnone]

theorem closureUnboundedDraw_norm_queries {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (native : Fin τ → FinDist X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureUnboundedDraw rand q native) (fun z => (z.2.2.2 : ℝ≥0∞)) = 0 := by
  rw [closureUnboundedDraw, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  calc _ = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (closureChoiceUnbounded rand q) (fun _ => 0) := by
        apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
        intro z
        cases z with
        | none => simp
        | some p => rcases p with ⟨t,k⟩; simp
    _ = 0 := by simp

theorem closureDraw_none {τ : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (rand : ClosureNativeRandom) (q : Fin τ → ℝ) (T : ℕ) (native : Fin τ → FinDist X) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureDraw rand q T native) (fun z => z.1 = none) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (closureChoiceRun rand q T) (fun z => z.1 = .inr ()) := by
  unfold closureDraw Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.expectation_congr
  rintro ⟨cfg,k⟩
  cases cfg with
  | inl t => simp
  | inr u => cases u; simp

end Qatlib.Concepts.SqEstimation.HierarchicalSQ
