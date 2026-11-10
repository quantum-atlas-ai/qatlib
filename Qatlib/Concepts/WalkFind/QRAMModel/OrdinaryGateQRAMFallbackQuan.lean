/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.QRAMModel.OrdinaryGateQRAMFallbackStat
import Mathlib.Tactic.Linarith
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Concepts.BlockEncoding.LinearCombination
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.QRAMModel
open Matrix
open scoped Classical BigOperators

theorem addressValue_lt_capacity {b : ℕ} (ψ : Reg b) (a w : ℕ) :
    addressValue ψ a w < 2^w := by
  induction w with
  | zero => simp [addressValue]
  | succ w ih =>
    simp only [addressValue, Finset.sum_range_succ, pow_succ] at *
    split_ifs <;> omega

theorem legal_qram_target_bounds {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b) :
    t < b ∧ m+addressValue ψ a aw < b ∧ t ≠ m+addressValue ψ a aw := by
  have h : a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧ 0 < ml ∧ 2^aw ≤ ml ∧
      (t < m ∨ m+ml ≤ t) ∧ (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a) := by
    simpa only [sourceCodeLegal, decide_eq_true_eq] using! hg
  have hv := addressValue_lt_capacity ψ a aw
  omega

theorem legal_qram_preserves_address {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b) :
    addressValue (qramAction b a aw t m ψ) a aw = addressValue ψ a aw := by
  have h : a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧ 0 < ml ∧ 2^aw ≤ ml ∧
      (t < m ∨ m+ml ≤ t) ∧ (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a) := by
    simpa only [sourceCodeLegal, decide_eq_true_eq] using! hg
  have hv := addressValue_lt_capacity ψ a aw
  unfold addressValue
  apply Finset.sum_congr rfl
  intro i hi
  have hiw : i < aw := Finset.mem_range.mp hi
  have hib : a+i < b := by omega
  have hit : a+i ≠ t := by omega
  have him : a+i ≠ m+addressValue ψ a aw := by omega
  simp [readBit, hib, qramAction, hit, him]

theorem legal_qram_involutive {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    Function.Involutive (qramAction b a aw t m) := by
  intro ψ
  obtain ⟨ht, hj, htj⟩ := legal_qram_target_bounds hg ψ
  have ha := legal_qram_preserves_address hg ψ
  have hreadt : readBit (qramAction b a aw t m ψ) t =
      readBit ψ (m+addressValue ψ a aw) := by
    simp [readBit, ht, qramAction]
  have hreadj : readBit (qramAction b a aw t m ψ) (m+addressValue ψ a aw) =
      readBit ψ t := by
    simp [readBit, hj, qramAction, htj.symm]
  funext i
  change (if i.val = t then readBit (qramAction b a aw t m ψ)
      (m+addressValue (qramAction b a aw t m ψ) a aw)
    else if i.val = m+addressValue (qramAction b a aw t m ψ) a aw then
      readBit (qramAction b a aw t m ψ) t else qramAction b a aw t m ψ i) = ψ i
  rw [ha, hreadj, hreadt]
  by_cases hit : i.val = t
  · simp only [hit, if_pos, readBit, dif_pos ht]
    congr 1
    exact Fin.ext hit.symm
  · rw [if_neg hit]
    by_cases hij : i.val = m+addressValue ψ a aw
    · simp only [hij, if_pos, readBit, dif_pos hj]
      exact congrArg ψ (Fin.ext hij.symm)
    · simp [qramAction, hit, hij]

theorem legal_qram_unitary {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    sourceCodeMatrix b (.qram a aw t m ml) ∈ Matrix.unitaryGroup (Reg b) ℂ := by
  exact permMatrix_unitary_of_injective (legal_qram_involutive hg).injective

theorem sourceWord_unitary (b : ℕ) (cs : List SourceCode) (hcs : sourceWordLegal b cs) :
    IsUnitaryCircuit (sourceCircuit b cs) := by
  intro U hU
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hU
  have hlegal := hcs c hc
  cases c with
  | query => simp at he
  | «local» g =>
    injection he with he
    subst U
    exact finiteCodeMatrix_unitary b g hlegal
  | qram a aw t m ml =>
    injection he with he
    subst U
    exact legal_qram_unitary hlegal

theorem ordinary_local_fallback (b : ℕ) (g : FiniteGateCode)
    (hg : sourceCodeLegal b (.local g) = true) :
    ∃ (a : ℕ) (word : List FiniteGateCode),
      a ≤ 2*b ∧ finiteWordLegal (b+a) word = true ∧
      word.length ≤ (b+1)^3 ∧
      ∀ ψ : QState (Reg b),
        Run 1 (finiteCodeCircuit (b+a) word)
          (fun z => TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr a)) ((regAppendEquiv b a) z)) =
        (fun z => TensorState (sourceCodeMatrix b (.local g) *ᵥ ψ)
          (Qatlib.Foundations.PureStateMath.Ket (ZeroStr a)) ((regAppendEquiv b a) z)) := by
  have hpad (ψ : QState (Reg b)) :
      (fun z => TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 0)) ((regAppendEquiv b 0) z)) = ψ := by
    funext z
    have hfst : (regAppendEquiv b 0 z).1 = z := by
      funext i
      rfl
    have hsnd : (regAppendEquiv b 0 z).2 = ZeroStr 0 := Subsingleton.elim _ _
    simp [TensorState, Qatlib.Foundations.PureStateMath.Ket, hfst, hsnd]
  refine ⟨0, [g], by omega, ?_, ?_, ?_⟩
  · simpa [finiteWordLegal, sourceCodeLegal] using! hg
  · simp only [List.length_singleton, Nat.one_le_iff_ne_zero]
    positivity
  · intro ψ
    rw [hpad, hpad]
    rfl

def finiteReflectionKind {n : ℕ} (g : ReflectionGate n) : Prop :=
  match g with
  | .inl (_, U) => U = Hadamard ∨ U = PauliX ∨ U = tGate ∨ U = tGateAdj
  | .inr _ => True

private theorem finiteReflection_code {n : ℕ} (g : ReflectionGate n)
    (hk : finiteReflectionKind g) (hl : reflectionGateLegal g) :
    ∃ code : FiniteGateCode, finiteCodeLegal n code = true ∧
      finiteCodeMatrix n code = reflectionGateMatrix g := by
  rcases g with ⟨w, U⟩ | ⟨c, t⟩
  · rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨.h w.val, by simp [finiteCodeLegal], by simp [finiteCodeMatrix, reflectionGateMatrix]⟩
    · exact ⟨.x w.val, by simp [finiteCodeLegal], by simp [finiteCodeMatrix, reflectionGateMatrix]⟩
    · exact ⟨.t w.val, by simp [finiteCodeLegal], by simp [finiteCodeMatrix, reflectionGateMatrix]⟩
    · exact ⟨.tdg w.val,
        by simp [finiteCodeLegal], by simp [finiteCodeMatrix, reflectionGateMatrix]⟩
  · have hct : c.val ≠ t.val := fun h => hl (Fin.ext h)
    exact ⟨.cx c.val t.val, by simp [finiteCodeLegal, hct],
      by simp [finiteCodeMatrix, reflectionGateMatrix, hct]⟩

theorem finiteReflection_compile {n : ℕ} (gs : List (ReflectionGate n))
    (hk : ∀ g ∈ gs, finiteReflectionKind g) (hl : reflectionLegal gs) :
    ∃ word : List FiniteGateCode, finiteWordLegal n word = true ∧
      word.length = gs.length ∧ finiteCodeCircuit n word = reflectionCompile gs := by
  induction gs with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨code, hc, he⟩ :=
        finiteReflection_code g (hk g List.mem_cons_self) (hl g List.mem_cons_self)
    obtain ⟨word, hw, hlen, hcirc⟩ := ih
      (fun g hg => hk g (List.mem_cons_of_mem _ hg))
      (fun g hg => hl g (List.mem_cons_of_mem _ hg))
    refine ⟨code::word, ?_, by simp [hlen], ?_⟩
    · simp only [finiteWordLegal, List.all_cons, hc, Bool.true_and]
      exact hw
    · simp only [finiteCodeCircuit, reflectionCompile, List.map_cons] at hcirc ⊢
      rw [he, hcirc]

private theorem toffoli_finite_kind {n : ℕ} (a b t : Fin n) :
    ∀ g ∈ toffoliLocalSteps a b t, finiteReflectionKind g := by
  simp [toffoliLocalSteps, finiteReflectionKind]

private theorem dirtyPrefix_finite_kind {n : ℕ} (c w : ℕ → Fin n) (r : ℕ) :
    ∀ g ∈ noWorkDirtyPrefixSteps c w r, finiteReflectionKind g := by
  induction r using Nat.twoStepInduction with
  | zero => simp [noWorkDirtyPrefixSteps]
  | one => exact toffoli_finite_kind _ _ _
  | more r _ ih =>
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact toffoli_finite_kind _ _ _ g hg
      · exact ih g hg
    · exact toffoli_finite_kind _ _ _ g hg

private theorem borrowedAnd_finite_kind {n : ℕ} (c w : ℕ → Fin n) (t : Fin n) (r : ℕ) :
    ∀ g ∈ noWorkBorrowedAndSteps c w t r, finiteReflectionKind g := by
  intro g hg
  simp only [noWorkBorrowedAndSteps, List.mem_append] at hg
  rcases hg with ((hg | hg) | hg) | hg
  · exact toffoli_finite_kind _ _ _ g hg
  · exact dirtyPrefix_finite_kind _ _ _ g hg
  · exact toffoli_finite_kind _ _ _ g hg
  · exact dirtyPrefix_finite_kind _ _ _ g hg

theorem finite_kind_borrowed_and_table {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (m : ℕ)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-2)))
    (hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j)
    (hct : ∀ i < m, c i ≠ t) (hwt : ∀ j < m-2, w j ≠ t) :
    ∃ gs : List (ReflectionGate N), (∀ g ∈ gs, finiteReflectionKind g) ∧ reflectionLegal gs ∧ gs.length ≤ 60*m+1 ∧
      ∀ x : Reg N, Run 1 (reflectionCompile gs) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
  rcases m with _ | m
  · refine ⟨knownFlipSteps [t], by simp [knownFlipSteps, finiteReflectionKind], knownFlipSteps_legal _,by simp [knownFlipSteps],?_⟩
    intro x
    rw [knownFlipSteps_action [t] (by simp)]
    congr 1
    funext k
    by_cases hk : k = t
    · subst k
      simp [noWorkPrefixAnd]
    · simp [hk,noWorkPrefixAnd]
  rcases m with _ | m
  · refine ⟨[.inr (c 0,t)], by simp [finiteReflectionKind], ?_,by simp,?_⟩
    · intro g hg
      obtain rfl := List.mem_singleton.mp hg
      exact hct 0 (by omega)
    · intro x
      simp only [reflectionCompile,List.map_cons,List.map_nil,run_gate,run_nil,reflectionGateMatrix]
      simpa [noWorkPrefixAnd,List.range_succ] using!
          applyGate_cnotGate_ket N (c 0) t (hct 0 (by omega)) x
  rcases m with _ | m
  · have h01 : c 0 ≠ c 1 := fun he => by
      have hh : 0 = 1 := hc (by simp) (by simp) he
      omega
    refine ⟨toffoliLocalSteps (c 0) (c 1) t, toffoli_finite_kind _ _ _,
      toffoliLocalSteps_legal _ _ _ h01 (hct 0 (by omega)) (hct 1 (by omega)),?_,?_⟩
    · rw [toffoliLocalSteps_length]
      norm_num
    · intro x
      simpa [noWorkPrefixAnd,List.range_succ] using!
        (local_toffoli_fifteen_exact N _ _ _ h01 (hct 0 (by omega)) (hct 1 (by omega))).2.2 x
  · have hm : m+1+1+1 = (m+1)+2 := by omega
    have hsub : m+1+1+1-2 = m+1 := by omega
    have hprefix : noWorkDirtyPrefixLayout c w (m+1) := by
      refine ⟨?_,?_,?_⟩
      · intro i hi j hj he
        exact hc (show i < m+1+1+1 from by change i < m+1+1 at hi; omega)
          (show j < m+1+1+1 from by change j < m+1+1 at hj; omega) he
      · simpa only [hsub] using! hw
      · intro i hi j hj
        exact hcw i (by omega) j (by omega)
    have hlast : ∀ j < m+1, c (m+1+1) ≠ w j := fun j hj => hcw _ (by omega) j (by omega)
    have htarget : ∀ i < m+1+2, c i ≠ t := fun i hi => hct i (by omega)
    have hwork : ∀ j < m+1, w j ≠ t := fun j hj => hwt j (by omega)
    refine ⟨noWorkBorrowedAndSteps c w t (m+1), borrowedAnd_finite_kind _ _ _ _,
      noWorkBorrowedAndSteps_legal c w t (m+1) (by omega) hprefix hlast htarget hwork,?_,?_⟩
    · rw [noWorkBorrowedAndSteps_length _ _ _ _ (by omega)]
      omega
    · intro x
      simpa only [hm] using!
        noWorkBorrowedAndSteps_ket c w t (m+1) (by omega) hprefix hlast htarget hwork x

theorem finiteMultiX_word {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (m : ℕ)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-2)))
    (hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j)
    (hct : ∀ i < m, c i ≠ t) (hwt : ∀ j < m-2, w j ≠ t) :
    ∃ word : List FiniteGateCode, finiteWordLegal N word = true ∧ word.length ≤ 60*m+1 ∧
      ∀ x : Reg N, Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ noWorkPrefixAnd (fun i => x (c i)) m)) := by
  obtain ⟨gs, hk, hl, hlen, hrun⟩ := finite_kind_borrowed_and_table c w t m hc hw hcw hct hwt
  obtain ⟨word, hword, hlength, hcompile⟩ := finiteReflection_compile gs hk hl
  exact ⟨word, hword, hlength.trans_le hlen, by simpa only [hcompile] using! hrun⟩

theorem finitePatternX_word {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (m : ℕ) (pattern : Reg m)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-2)))
    (hcw : ∀ i < m, ∀ j < m-2, c i ≠ w j)
    (hct : ∀ i < m, c i ≠ t) (hwt : ∀ j < m-2, w j ≠ t) :
    ∃ word : List FiniteGateCode, finiteWordLegal N word = true ∧ word.length ≤ 62*m+1 ∧
      ∀ x : Reg N, Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (Function.update x t (x t ^^ decide (∀ i : Fin m, x (c i.val) = pattern i))) := by
  classical
  let mask : Finset (Fin N) := (Finset.univ.filter (fun i : Fin m => pattern i = false)).image
    (fun i => c i.val)
  have hmask (i : Fin m) : c i.val ∈ mask ↔ pattern i = false := by
    simp only [mask, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, heq⟩
      have hij : j = i := Fin.ext (hc j.isLt i.isLt heq)
      simpa [hij] using! hj
    · intro h; exact ⟨i, h, rfl⟩
  have htmask : t ∉ mask := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact hct i.val i.isLt hi
  let flip : Reg N → Reg N := fun x k => if k ∈ mask then !(x k) else x k
  have hflip : Function.Involutive flip := by
    intro x
    funext k
    simp only [flip]
    split_ifs <;> simp
  have htarget (x : Reg N) : flip x t = x t := by simp [flip, htmask]
  have hupdate (x : Reg N) (v : Bool) : flip (Function.update x t v) =
      Function.update (flip x) t v := by
    funext k
    by_cases hk : k = t
    · subst k; simp [flip, htmask]
    · simp [flip, hk]
  have htest (x : Reg N) : noWorkPrefixAnd (fun i => flip x (c i)) m =
      decide (∀ i : Fin m, x (c i.val) = pattern i) := by
    apply Bool.eq_iff_iff.mpr
    simp only [noWorkPrefixAnd, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    constructor
    · intro h i
      have hi := h i.val i.isLt
      change (if c i.val ∈ mask then !(x (c i.val)) else x (c i.val)) = true at hi
      simp only [hmask i] at hi
      cases hp : pattern i <;> cases hx : x (c i.val) <;> simp_all
    · intro h i hi
      have hp := h ⟨i, hi⟩
      change (if c i ∈ mask then !(x (c i)) else x (c i)) = true
      simp only [hmask ⟨i, hi⟩, hp]
      cases pattern ⟨i, hi⟩ <;> rfl
  have hkind : ∀ g ∈ knownFlipSteps mask.toList, finiteReflectionKind g := by
    simp [knownFlipSteps, finiteReflectionKind]
  obtain ⟨xs, hxs, hxslen, hxscomp⟩ := finiteReflection_compile (knownFlipSteps mask.toList)
    hkind (knownFlipSteps_legal _)
  have hxlen : xs.length ≤ m := by
    rw [hxslen]
    simp only [knownFlipSteps, List.length_map, Finset.length_toList]
    exact (Finset.card_image_le).trans (Finset.card_filter_le _ _ |>.trans (by simp))
  have hxrun (x : Reg N) : Run 1 (finiteCodeCircuit N xs) (Qatlib.Foundations.PureStateMath.Ket x) = Qatlib.Foundations.PureStateMath.Ket (flip x) := by
    rw [hxscomp, knownFlipSteps_action _ (Finset.nodup_toList _)]
    simp [flip]
  obtain ⟨word, hword, hlen, hrun⟩ := finiteMultiX_word c w t m hc hw hcw hct hwt
  refine ⟨xs++word++xs, ?_, ?_, ?_⟩
  · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨⟨hxs, hword⟩, hxs⟩
  · simp only [List.length_append]
    omega
  · intro x
    simp only [finiteCodeCircuit, List.map_append, run_append]
    change Run 1 (finiteCodeCircuit N xs)
      (Run 1 (finiteCodeCircuit N word) (Run 1 (finiteCodeCircuit N xs) (Qatlib.Foundations.PureStateMath.Ket x))) = _
    rw [hxrun, hrun, hxrun, hupdate, hflip, htarget, htest]

private def finiteToggle {N : ℕ} (x : Reg N) (s t : Fin N) (flag : Bool) : Reg N :=
  Function.update x t (x t ^^ (flag && x s))

private theorem finiteToggle_swap {N : ℕ} (x : Reg N) (s t : Fin N)
    (flag : Bool) (hst : s ≠ t) :
    finiteToggle (finiteToggle (finiteToggle x s t flag) t s flag) s t flag =
      if flag then Function.update (Function.update x t (x s)) s (x t) else x := by
  cases flag with
  | false => simp [finiteToggle]
  | true =>
    funext k
    by_cases hkt : k = t
    · subst k
      cases ht : x t <;> cases hs : x s <;> simp_all [finiteToggle, Function.update]
    · by_cases hks : k = s
      · subst k
        cases ht : x t <;> cases hs : x s <;> simp_all [finiteToggle, Function.update]
      · simp [finiteToggle, Function.update, hkt, hks]

theorem finitePatternSwap_word {N : ℕ} (c w : ℕ → Fin N) (s t : Fin N)
    (m : ℕ) (pattern : Reg m)
    (hc : Set.InjOn c (Set.Iio m)) (hw : Set.InjOn w (Set.Iio (m-1)))
    (hcw : ∀ i < m, ∀ j < m-1, c i ≠ w j)
    (hcs : ∀ i < m, c i ≠ s) (hct : ∀ i < m, c i ≠ t)
    (hws : ∀ j < m-1, w j ≠ s) (hwt : ∀ j < m-1, w j ≠ t) (hst : s ≠ t) :
    ∃ word : List FiniteGateCode, finiteWordLegal N word = true ∧
      word.length ≤ 186*(m+1)+3 ∧
      ∀ x : Reg N, Run 1 (finiteCodeCircuit N word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (if (∀ i : Fin m, x (c i.val) = pattern i) then
          Function.update (Function.update x t (x s)) s (x t) else x) := by
  classical
  let extc (q : Fin N) (i : ℕ) := if i < m then c i else q
  let extp : Reg (m+1) := fun i => if h : i.val < m then pattern ⟨i.val,h⟩ else true
  have hext (q : Fin N) (hcq : ∀ i < m, c i ≠ q) :
      Set.InjOn (extc q) (Set.Iio (m+1)) := by
    intro i hi j hj hij
    by_cases him : i < m <;> by_cases hjm : j < m
    · exact hc him hjm (by simpa [extc, him, hjm] using! hij)
    · exact False.elim (hcq i him (by simpa [extc, him, hjm] using! hij))
    · exact False.elim (hcq j hjm (by simpa [extc, him, hjm] using! hij.symm))
    · have : i = j := by change i < m+1 at hi; change j < m+1 at hj; omega
      exact this
  have hextw (q : Fin N) (hwq : ∀ j < m-1, w j ≠ q) :
      ∀ i < m+1, ∀ j < m+1-2, extc q i ≠ w j := by
    intro i hi j hj
    dsimp [extc]
    split_ifs with h
    · exact hcw i h j (by omega)
    · exact (hwq j (by omega)).symm
  have hextt (q u : Fin N) (hcq : ∀ i < m, c i ≠ u) (hqu : q ≠ u) :
      ∀ i < m+1, extc q i ≠ u := by
    intro i _
    dsimp [extc]
    split_ifs with hi
    · exact hcq i hi
    · exact hqu
  obtain ⟨ts, hts, hlts, hrts⟩ := finitePatternX_word (extc s) w t (m+1) extp
    (hext s hcs) (by simpa using! hw) (hextw s hws) (hextt s t hct hst)
    (by simpa using! hwt)
  obtain ⟨st, hstword, hlst, hrst⟩ := finitePatternX_word (extc t) w s (m+1) extp
    (hext t hct) (by simpa using! hw) (hextw t hwt) (hextt t s hcs hst.symm)
    (by simpa using! hws)
  let test (x : Reg N) := decide (∀ i : Fin m, x (c i.val) = pattern i)
  have htest (q : Fin N) (x : Reg N) :
      decide (∀ i : Fin (m+1), x (extc q i.val) = extp i) = (test x && x q) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, test, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro i
        simpa [extc, extp, i.isLt] using! h i.castSucc
      · simpa [extc, extp] using! h (Fin.last m)
    · rintro ⟨h, hq⟩ i
      by_cases hi : i.val < m
      · simpa [extc, extp, hi] using! h ⟨i.val,hi⟩
      · simp [extc, extp, hi, hq]
  have htest_update (q : Fin N) (hq : ∀ i < m, c i ≠ q) (x : Reg N) (v : Bool) :
      test (Function.update x q v) = test x := by
    apply Bool.eq_iff_iff.mpr
    simp only [test, decide_eq_true_eq]
    constructor
    · intro h i
      simpa only [Function.update_of_ne (hq i.val i.isLt)] using! h i
    · intro h i
      simpa only [Function.update_of_ne (hq i.val i.isLt)] using! h i
  refine ⟨ts++st++ts, ?_, ?_, ?_⟩
  · simp only [finiteWordLegal, List.all_append, Bool.and_eq_true]
    exact ⟨⟨hts, hstword⟩, hts⟩
  · simp only [List.length_append]
    omega
  · intro x
    simp only [finiteCodeCircuit, List.map_append, run_append]
    change Run 1 (finiteCodeCircuit N ts)
      (Run 1 (finiteCodeCircuit N st) (Run 1 (finiteCodeCircuit N ts) (Qatlib.Foundations.PureStateMath.Ket x))) = _
    rw [hrts, hrst, hrts]
    simp only [htest, htest_update t hct, htest_update s hcs]
    apply congrArg Qatlib.Foundations.PureStateMath.Ket
    simpa only [finiteToggle, test, decide_eq_true_eq] using! finiteToggle_swap x s t (test x) hst

theorem legal_qram_preserves_address_bit {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (ψ : Reg b)
    (i : ℕ) (hi : i < aw) :
    readBit (qramAction b a aw t m ψ) (a+i) = readBit ψ (a+i) := by
  have h : a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧ 0 < ml ∧ 2^aw ≤ ml ∧
      (t < m ∨ m+ml ≤ t) ∧ (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a) := by
    simpa only [sourceCodeLegal, decide_eq_true_eq] using! hg
  have hv := addressValue_lt_capacity ψ a aw
  have hib : a+i < b := by omega
  have hit : a+i ≠ t := by omega
  have him : a+i ≠ m+addressValue ψ a aw := by omega
  simp [readBit, hib, qramAction, hit, him]

theorem finiteQRAM_basis_word {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    ∃ word : List FiniteGateCode, finiteWordLegal (b+b) word = true ∧
      word.length ≤ 200*(b+1)^3 ∧
      ∀ x : Reg (b+b), Run 1 (finiteCodeCircuit (b+b) word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (qramAction (b+b) a aw t m x) := by
  classical
  have h : a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧ 0 < ml ∧ 2^aw ≤ ml ∧
      (t < m ∨ m+ml ≤ t) ∧ (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a) := by
    simpa only [sourceCodeLegal, decide_eq_true_eq] using! hg
  have hb : 0 < b := by omega
  have hg' : sourceCodeLegal (b+b) (.qram a aw t m ml) = true := by
    simp only [sourceCodeLegal, decide_eq_true_eq]
    omega
  let target : Fin (b+b) := ⟨t, by omega⟩
  let c : ℕ → Fin (b+b) := fun i => if h : a+i < b+b then ⟨a+i,h⟩ else target
  let w : ℕ → Fin (b+b) := fun i => if h : b+i < b+b then ⟨b+i,h⟩ else target
  let read : Reg (b+b) → Reg aw := fun x i => x (c i.val)
  have hcval (i : ℕ) (hi : i < aw) : (c i).val = a+i := by
    simp [c, show a+i < b+b by omega]
  have hwval (i : ℕ) (hi : i < aw-1) : (w i).val = b+i := by
    simp [w, show i < b by omega]
  have hc : Set.InjOn c (Set.Iio aw) := by
    intro i hi j hj hij
    have heq := congrArg Fin.val hij
    rw [hcval i hi, hcval j hj] at heq
    omega
  have hw : Set.InjOn w (Set.Iio (aw-1)) := by
    intro i hi j hj hij
    have heq := congrArg Fin.val hij
    rw [hwval i hi, hwval j hj] at heq
    omega
  have hcw : ∀ i < aw, ∀ j < aw-1, c i ≠ w j := by
    intro i hi j hj heq
    have hv := congrArg Fin.val heq
    rw [hcval i hi, hwval j hj] at hv
    omega
  have hct : ∀ i < aw, c i ≠ target := by
    intro i hi heq
    have hv := congrArg Fin.val heq
    rw [hcval i hi] at hv
    change a+i = t at hv
    omega
  have hwt : ∀ j < aw-1, w j ≠ target := by
    intro j hj heq
    have hv := congrArg Fin.val heq
    rw [hwval j hj] at hv
    change b+j = t at hv
    omega
  have haddress (x : Reg (b+b)) : addressValue x a aw = addressValue (read x) 0 aw := by
    unfold addressValue
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < aw := Finset.mem_range.mp hi
    simp [readBit, hi', read, c, show a+i < b+b by omega]
  have hread (x : Reg (b+b)) : read (qramAction (b+b) a aw t m x) = read x := by
    funext i
    have hv := legal_qram_preserves_address_bit hg' x i.val i.isLt
    simpa [read, c, readBit, show a+i.val < b+b by omega] using! hv
  have hwords (p : Reg aw) : ∃ word : List FiniteGateCode,
      finiteWordLegal (b+b) word = true ∧ word.length ≤ 186*(aw+1)+3 ∧
      ∀ x : Reg (b+b), Run 1 (finiteCodeCircuit (b+b) word) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (if read x = p then qramAction (b+b) a aw t m x else x) := by
    have hp := addressValue_lt_capacity p 0 aw
    let j : Fin (b+b) := ⟨m+addressValue p 0 aw, by omega⟩
    have hjb : j.val < b := by dsimp [j]; omega
    have hcs : ∀ i < aw, c i ≠ j := by
      intro i hi heq
      have hv := congrArg Fin.val heq
      rw [hcval i hi] at hv
      change a+i = m+addressValue p 0 aw at hv
      omega
    have hws : ∀ i < aw-1, w i ≠ j := by
      intro i hi heq
      have hv := congrArg Fin.val heq
      rw [hwval i hi] at hv
      omega
    have hjt : j ≠ target := by
      intro heq
      have hv := congrArg Fin.val heq
      change m+addressValue p 0 aw = t at hv
      omega
    obtain ⟨word, hlegal, hlen, hrun⟩ := finitePatternSwap_word c w j target aw p
      hc hw hcw hcs hct hws hwt hjt
    refine ⟨word, hlegal, hlen, ?_⟩
    intro x
    rw [hrun]
    have htest : (∀ i : Fin aw, x (c i.val) = p i) ↔ read x = p :=
      ⟨fun h => funext h, fun h i => congrFun h i⟩
    simp only [htest]
    apply congrArg Qatlib.Foundations.PureStateMath.Ket
    by_cases hx : read x = p
    · simp only [hx, if_pos]
      have haeq : addressValue x a aw = addressValue p 0 aw := by rw [haddress, hx]
      funext i
      have ht : t < b+b := by omega
      have hj : m+addressValue p 0 aw < b+b := j.isLt
      have htj : t ≠ m+addressValue p 0 aw := by omega
      by_cases hit : i.val = t
      · simp [Function.update, Fin.ext_iff, hit, target, j, qramAction, haeq, readBit, hj, htj]
      · by_cases hij : i.val = j.val
        · simp [Function.update, Fin.ext_iff, hij, target, j, qramAction, haeq, readBit, ht,
            htj.symm]
        · simp [Function.update, Fin.ext_iff, hit, hij, target, j, qramAction, haeq]
    · simp [hx]
  choose words hlegal hlen hrun using hwords
  have hloop (ps : List (Reg aw)) (hn : ps.Nodup) (x : Reg (b+b)) :
      Run 1 (finiteCodeCircuit (b+b) (ps.flatMap words)) (Qatlib.Foundations.PureStateMath.Ket x) =
        Qatlib.Foundations.PureStateMath.Ket (if read x ∈ ps then qramAction (b+b) a aw t m x else x) := by
    induction ps generalizing x with
    | nil => simp [finiteCodeCircuit]
    | cons p ps ih =>
      simp only [List.flatMap_cons, finiteCodeCircuit, List.map_append, run_append]
      change Run 1 (finiteCodeCircuit (b+b) (ps.flatMap words))
        (Run 1 (finiteCodeCircuit (b+b) (words p)) (Qatlib.Foundations.PureStateMath.Ket x)) = _
      rw [hrun]
      by_cases hx : read x = p
      · rw [if_pos hx, ih (List.nodup_cons.mp hn).2]
        simp [hread, hx, (List.nodup_cons.mp hn).1]
      · rw [if_neg hx, ih (List.nodup_cons.mp hn).2]
        simp [hx]
  have hlength (ps : List (Reg aw)) : (ps.flatMap words).length ≤
      ps.length*(186*(aw+1)+3) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hp := hlen p
      nlinarith
  let ps := (Finset.univ : Finset (Reg aw)).toList
  refine ⟨ps.flatMap words, ?_, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro code hcode
    obtain ⟨p, _, hcode⟩ := List.mem_flatMap.mp hcode
    exact List.all_eq_true.mp (hlegal p) code hcode
  · have hl := hlength ps
    have hcard : ps.length = 2^aw := by simp [ps, Reg]
    rw [hcard] at hl
    have haw : aw ≤ b := by omega
    have hpow : 2^aw ≤ b := by omega
    nlinarith [Nat.mul_le_mul hpow (show 186*(aw+1)+3 ≤ 186*(b+1)+3 by omega)]
  · intro x
    rw [hloop ps (Finset.nodup_toList _) x]
    simp [ps]

private def finiteExecutionMatrix (n : ℕ) : List FiniteGateCode → Matrix (Reg n) (Reg n) ℂ
  | [] => 1
  | g::gs => finiteExecutionMatrix n gs * finiteCodeMatrix n g

private theorem finiteExecutionMatrix_spec (n : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg n)) :
    Run 1 (finiteCodeCircuit n gs) ψ = finiteExecutionMatrix n gs *ᵥ ψ := by
  induction gs generalizing ψ with
  | nil => simp [finiteCodeCircuit, finiteExecutionMatrix]
  | cons g gs ih =>
    simp only [finiteCodeCircuit, List.map_cons, run_gate]
    change Run 1 (finiteCodeCircuit n gs) (finiteCodeMatrix n g *ᵥ ψ) = _
    rw [ih, Matrix.mulVec_mulVec]
    rfl

private theorem permutation_involution_apply {H : Type} [Fintype H] [DecidableEq H]
    (f : H → H) (hf : Function.Involutive f) (ψ : QState H) (y : H) :
    (permMatrix f *ᵥ ψ) y = ψ (f y) := by
  simp only [permMatrix, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (f y)]
  · simp [hf y]
  · intro x _ hx
    have hne : y ≠ f x := by
      intro h
      have heq := congrArg f h
      rw [hf x] at heq
      exact hx heq.symm
    simp [hne]
  · simp

theorem qramAction_split {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) (x : Reg (b+b)) :
    regAppendEquiv b b (qramAction (b+b) a aw t m x) =
      (qramAction b a aw t m (regAppendEquiv b b x).1, (regAppendEquiv b b x).2) := by
  have h : a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧ 0 < ml ∧ 2^aw ≤ ml ∧
      (t < m ∨ m+ml ≤ t) ∧ (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a) := by
    simpa only [sourceCodeLegal, decide_eq_true_eq] using! hg
  have hbit (i : ℕ) (hi : i < b) : readBit x i = readBit (regAppendEquiv b b x).1 i := by
    simp [readBit, hi, show i < b+b by omega, regAppendEquiv]
  have haddr : addressValue x a aw = addressValue (regAppendEquiv b b x).1 a aw := by
    unfold addressValue
    apply Finset.sum_congr rfl
    intro i hi
    rw [hbit (a+i) (by have := Finset.mem_range.mp hi; omega)]
  have hv := addressValue_lt_capacity (regAppendEquiv b b x).1 a aw
  have hj : m+addressValue (regAppendEquiv b b x).1 a aw < b := by omega
  have hbq : readBit x t = readBit (regAppendEquiv b b x).1 t := hbit t h.2.1
  have hbj := hbit _ hj
  apply Prod.ext
  · funext i
    change (if i.val = t then readBit x (m+addressValue x a aw)
        else if i.val = m+addressValue x a aw then readBit x t else x (Fin.castAdd b i)) = _
    rw [haddr, hbj, hbq]
    rfl
  · funext i
    have ht : i.val+b ≠ t := by omega
    have hmem : i.val+b ≠ m+addressValue x a aw := by rw [haddr]; omega
    simp [regAppendEquiv, qramAction, ht, hmem]

theorem ordinary_qram_fallback {b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    ∃ word : List FiniteGateCode, finiteWordLegal (b+b) word = true ∧
      word.length ≤ 200*(b+1)^3 ∧
      ∀ ψ : QState (Reg b),
        Run 1 (finiteCodeCircuit (b+b) word)
          (fun z => TensorState ψ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr b)) ((regAppendEquiv b b) z)) =
        (fun z => TensorState (sourceCodeMatrix b (.qram a aw t m ml) *ᵥ ψ)
          (Qatlib.Foundations.PureStateMath.Ket (ZeroStr b)) ((regAppendEquiv b b) z)) := by
  obtain ⟨word, hlegal, hlen, hket⟩ := finiteQRAM_basis_word hg
  have hmatrix : finiteExecutionMatrix (b+b) word =
      sourceCodeMatrix (b+b) (.qram a aw t m ml) := by
    ext y x
    have h := congrFun (hket x) y
    rw [finiteExecutionMatrix_spec, mulVec_ket_apply] at h
    exact h
  have hg' : sourceCodeLegal (b+b) (.qram a aw t m ml) = true := by
    have h : a+aw ≤ b ∧ t < b ∧ m+ml ≤ b ∧ 0 < ml ∧ 2^aw ≤ ml ∧
      (t < m ∨ m+ml ≤ t) ∧ (t < a ∨ a+aw ≤ t) ∧ (a+aw ≤ m ∨ m+ml ≤ a) := by
      simpa only [sourceCodeLegal, decide_eq_true_eq] using! hg
    simp only [sourceCodeLegal, decide_eq_true_eq]
    omega
  refine ⟨word, hlegal, hlen, ?_⟩
  intro ψ
  rw [finiteExecutionMatrix_spec, hmatrix]
  ext z
  change (permMatrix (qramAction (b+b) a aw t m) *ᵥ _) z = _
  rw [permutation_involution_apply _ (legal_qram_involutive hg')]
  rw [qramAction_split hg z]
  unfold TensorState
  rw [show sourceCodeMatrix b (.qram a aw t m ml) = permMatrix (qramAction b a aw t m) by rfl,
    permutation_involution_apply _ (legal_qram_involutive hg)]

theorem ordinaryGateQRAMFallback_answer : OrdinaryGateQRAMFallback := by
  refine ⟨200, by decide, ?_⟩
  intro b g hg hnq
  cases g with
  | query => exact False.elim (hnq rfl)
  | «local» code =>
    obtain ⟨a, word, ha, hw, hlen, hsem⟩ := ordinary_local_fallback b code hg
    exact ⟨a, word, ha, hw, by omega, hsem⟩
  | qram a aw t m ml =>
    obtain ⟨word, hw, hlen, hsem⟩ := ordinary_qram_fallback hg
    exact ⟨b, word, by omega, hw, hlen, hsem⟩

end Qatlib.Concepts.WalkFind.QRAMModel
