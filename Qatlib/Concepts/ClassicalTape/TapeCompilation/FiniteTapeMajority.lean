/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.FiniteTapeMajorityVocabulary
import Mathlib.Computability.Partrec
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.Amplification
open Qatlib.Foundations.BornMetrics.EventProbability

set_option autoImplicit false

namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

open scoped BigOperators Classical

set_option maxHeartbeats 2000000 in

theorem symbolIndex_lt (a : Option Bool) : symbolIndex a < 3 := by
  cases a with
  | none => decide
  | some b => cases b <;> decide

theorem decodeSymbol_symbolIndex (a : Option Bool) : decodeSymbol (symbolIndex a) = a := by
  cases a with
  | none => rfl
  | some b => cases b <;> rfl

theorem actionIndex_lt (stmt : Turing.TM0.Stmt (Option Bool)) : actionIndex stmt < 5 := by
  cases stmt with
  | move d => cases d <;> decide
  | write a => cases a with
    | none => decide
    | some b => cases b <;> decide

theorem decodeTransition_encode {Q : ℕ}
    (p : Option (Fin (Q + 1) × Turing.TM0.Stmt (Option Bool))) :
    decodeTransition Q (encodeTransition p) = p := by
  cases p with
  | none => rfl
  | some p =>
    obtain ⟨q, stmt⟩ := p
    have ha := actionIndex_lt stmt
    have hd : (5 * q.val + actionIndex stmt) / 5 = q.val := by omega
    have hm : (5 * q.val + actionIndex stmt) % 5 = actionIndex stmt := by omega
    simp only [encodeTransition, decodeTransition, hd, Nat.mod_eq_of_lt q.isLt]
    congr 2
    unfold decodeAction
    rw [hm]
    cases stmt with
    | move d => cases d <;> rfl
    | write a => cases a with
      | none => rfl
      | some b => cases b <;> rfl

@[simp] theorem controlSize_encode (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) : controlSize (encodeMachine Q M a) = Q := rfl

theorem encodeMachine_length (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) : (encodeMachine Q M a).length = 1 + 7 * (Q + 1) := by
  simp [encodeMachine]
  omega

theorem rowIndex_lt (Q : ℕ) (c : Bool) (q : Fin (Q + 1)) (a : Option Bool) :
    rowIndex Q c q a < 6 * (Q + 1) := by
  have hs := symbolIndex_lt a
  cases c <;> simp only [rowIndex, Bool.toNat, cond_false, cond_true] <;> omega

theorem rowIndex_coordinates (Q : ℕ) (c : Bool) (q : Fin (Q + 1)) (a : Option Bool) :
    decide (3 * (Q + 1) ≤ rowIndex Q c q a) = c ∧
    (rowIndex Q c q a / 3) % (Q + 1) = q.val ∧
    decodeSymbol (rowIndex Q c q a % 3) = a := by
  have hs := symbolIndex_lt a
  have hd : rowIndex Q c q a / 3 = c.toNat * (Q + 1) + q.val := by
    unfold rowIndex
    omega
  have hm : rowIndex Q c q a % 3 = symbolIndex a := by
    unfold rowIndex
    omega
  refine ⟨?_, ?_, ?_⟩
  · cases c <;> simp only [rowIndex, Bool.toNat, cond_false, cond_true,
      decide_eq_false_iff_not, decide_eq_true_eq] <;> omega
  · rw [hd]
    cases c <;> simp [Nat.mod_eq_of_lt q.isLt]
  · rw [hm, decodeSymbol_symbolIndex]

theorem readout_encode (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (q : Fin (Q + 1)) :
    readout (encodeMachine Q M a) q = a q := by
  simp only [readout]
  rw [show 1 + q.val = q.val + 1 by omega]
  change ((List.ofFn (fun q : Fin (Q + 1) => (a q).toNat) ++ _).getD q.val 0 % 2 == 1) = _
  rw [List.getD_append _ _ _ _ (by simpa using! q.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using! q.isLt)]
  simp only [List.getElem_ofFn]
  cases a q <;> rfl

theorem table_encode (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) : table (encodeMachine Q M a) = M := by
  funext c q sym
  unfold table
  simp only [controlSize_encode]
  rw [show 1 + (Q + 1) + rowIndex Q c q sym = (Q + 1 + rowIndex Q c q sym) + 1 by omega]
  change decodeTransition Q ((List.ofFn (fun q : Fin (Q + 1) => (a q).toNat) ++
    List.ofFn (fun i : Fin (6 * (Q + 1)) =>
      encodeTransition (M (decide (3 * (Q + 1) ≤ i.val))
        ⟨i.val / 3 % (Q + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (i.val % 3))))).getD
      (Q + 1 + rowIndex Q c q sym) 0) = M c q sym
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by have h := rowIndex_lt Q c q sym; simp only [List.length_ofFn]; omega)]
  simp only [List.getElem_ofFn]
  obtain ⟨hc, hq, hs⟩ := rowIndex_coordinates Q c q sym
  have hfin : (⟨rowIndex Q c q sym / 3 % (Q + 1), Nat.mod_lt _ (by omega)⟩ :
      Fin (Q + 1)) = q := Fin.ext hq
  rw [hc, hfin, hs, decodeTransition_encode]

theorem readout_encode_eq (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) : readout (encodeMachine Q M a) = a :=
  funext (readout_encode Q M a)

theorem relabel_coinHalt {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']
    (e : Λ ≃ Λ') (M : Bool → Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ) :
    coinHalt (relabelTable e M) (relabelCfg e cfg) = coinHalt M cfg := by
  simp [coinHalt, relabelTable, relabelCfg]

theorem relabel_step {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']
    (e : Λ ≃ Λ') (M : Bool → Turing.TM0.Machine Γ Λ) (c : Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) :
    Turing.TM0.step (relabelTable e M c) (relabelCfg e cfg) =
      (Turing.TM0.step (M c) cfg).map (relabelCfg e) := by
  simp only [TM0_step_apply, relabelCfg, relabelTable, Equiv.symm_apply_apply,
    Option.map_map, Function.comp_def]

theorem relabel_runAux {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']
    (e : Λ ≃ Λ') (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool)
    (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    coinTapeRunAux (relabelTable e M) (fun q => a (e.symm q)) coins (relabelCfg e cfg) =
      coinTapeRunAux M a coins cfg := by
  induction coins generalizing cfg with
  | nil =>
    simp only [coinTapeRunAux, relabel_coinHalt]
    simp [relabelCfg]
  | cons c cs ih =>
    simp only [coinTapeRunAux, relabel_coinHalt]
    split
    · simp [relabelCfg]
    · rw [relabel_step]
      cases hs : Turing.TM0.step (M c) cfg with
      | none => simp [relabelCfg]
      | some cfg' => simp only [Option.map_some, ih]

theorem relabel_transitionsAux {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']
    (e : Λ ≃ Λ') (M : Bool → Turing.TM0.Machine Γ Λ)
    (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    coinTapeTransitionCountAux (relabelTable e M) coins (relabelCfg e cfg) =
      coinTapeTransitionCountAux M coins cfg := by
  induction coins generalizing cfg with
  | nil => rfl
  | cons c cs ih =>
    simp only [coinTapeTransitionCountAux, relabel_coinHalt]
    split
    · rfl
    · rw [relabel_step]
      cases hs : Turing.TM0.step (M c) cfg with
      | none => rfl
      | some cfg' => simp only [Option.map_some, ih]

theorem relabel_run {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']
    (e : Λ ≃ Λ') (he : e default = default)
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool)
    (coins : List Bool) (input : List Γ) :
    coinTapeRun (relabelTable e M) (fun q => a (e.symm q)) input coins =
      coinTapeRun M a input coins ∧
    coinTapeTransitionCount (relabelTable e M) input coins =
      coinTapeTransitionCount M input coins := by
  have hi : relabelCfg e (Turing.TM0.init input) = Turing.TM0.init input := by
    simp [relabelCfg, Turing.TM0.init, he]
  constructor
  · simpa only [coinTapeRun, hi] using! relabel_runAux e M a coins (Turing.TM0.init input)
  · simpa only [coinTapeTransitionCount, hi] using!
      relabel_transitionsAux e M coins (Turing.TM0.init input)

theorem trueCount_le_length (coins : List Bool) : trueCount coins ≤ coins.length := by
  induction coins with
  | nil => simp
  | cons c cs ih => cases c <;> simp_all [Bool.toNat] <;> omega

theorem tallyTable_commonHalt (N : ℕ) (q : TallyState N) (a : Option Bool) :
    (tallyTable N false q a = none) ↔ (tallyTable N true q a = none) := by
  simp only [tallyTable]
  split <;> simp

theorem tally_coinHalt (N : ℕ) (q : TallyState N) (T : Turing.Tape (Option Bool)) :
    coinHalt (tallyTable N) ⟨q, T⟩ = decide (N ≤ q.1.val) := by
  by_cases h : q.1.val < N <;> simp [coinHalt, tallyTable, h, Nat.not_le.mpr, Nat.le_of_not_gt]

theorem tally_step (N : ℕ) (q : TallyState N) (T : Turing.Tape (Option Bool))
    (c : Bool) (h : q.1.val < N) :
    Turing.TM0.step (tallyTable N c) ⟨q, T⟩ =
      some ⟨(⟨q.1.val + 1, by omega⟩,
        ⟨min N (q.2.val + c.toNat), by omega⟩), T⟩ := by
  rw [TM0_step_apply]
  simp [tallyTable, h, TM0StmtApply, Turing.Tape.write_self]

theorem tally_run_prefix (N : ℕ) (coins extra : List Bool)
    (q : TallyState N) (T : Turing.Tape (Option Bool))
    (hfinish : q.1.val + coins.length = N) (hcount : q.2.val ≤ q.1.val) :
    coinTapeRunAux (tallyTable N) (tallyAccept N) (coins ++ extra) ⟨q, T⟩ =
      (some (decide (N / 2 < q.2.val + trueCount coins)), coins.length) ∧
    coinTapeTransitionCountAux (tallyTable N) (coins ++ extra) ⟨q, T⟩ = coins.length := by
  induction coins generalizing q with
  | nil =>
    have hc : coinHalt (tallyTable N) ⟨q, T⟩ = true := by
      rw [tally_coinHalt]; simp_all
    constructor
    · simpa [tallyAccept] using! coinTapeRunAux_of_coinHalt (tallyTable N) (tallyAccept N)
        extra ⟨q, T⟩ hc
    · cases extra <;> simp [coinTapeTransitionCountAux, hc]
  | cons c cs ih =>
    have hi : q.1.val < N := by simp only [List.length_cons] at hfinish; omega
    have hb : c.toNat ≤ 1 := by cases c <;> decide
    have hv : q.2.val + c.toNat ≤ N := by omega
    let q' : TallyState N := (⟨q.1.val + 1, by omega⟩,
      ⟨min N (q.2.val + c.toNat), by omega⟩)
    have hq' : q'.2.val = q.2.val + c.toNat := Nat.min_eq_right hv
    have hc : coinHalt (tallyTable N) ⟨q, T⟩ = false := by
      rw [tally_coinHalt]; simp [Nat.not_le.mpr hi]
    have hs := tally_step N q T c hi
    have hnext : q'.1.val + cs.length = N := by
      simp only [List.length_cons] at hfinish
      dsimp [q']; omega
    have hnextCount : q'.2.val ≤ q'.1.val := by dsimp [q']; omega
    obtain ⟨hr, hl⟩ := ih q' hnext hnextCount
    constructor
    · rw [List.cons_append, coinTapeRunAux_cons_of_step_some _ _ c (cs ++ extra) _ _ hc hs]
      change Prod.map id (· + 1)
        (coinTapeRunAux (tallyTable N) (tallyAccept N) (cs ++ extra) ⟨q', T⟩) = _
      rw [hr]
      simp [Prod.map, hq', Nat.add_assoc]
    · simp only [List.cons_append, coinTapeTransitionCountAux, hc, Bool.false_eq_true,
        ↓reduceIte, hs]
      change coinTapeTransitionCountAux (tallyTable N) (cs ++ extra) ⟨q', T⟩ + 1 = _
      rw [hl, List.length_cons]

theorem tally_run (coins extra : List Bool) (input : List (Option Bool)) :
    coinTapeRun (tallyTable coins.length) (tallyAccept coins.length) input (coins ++ extra) =
      (some (decide (coins.length / 2 < trueCount coins)), coins.length) ∧
    coinTapeTransitionCount (tallyTable coins.length) input (coins ++ extra) = coins.length := by
  simpa [coinTapeRun, coinTapeTransitionCount, Turing.TM0.init] using!
    tally_run_prefix coins.length coins extra ((0, 0) : TallyState coins.length)
      (Turing.Tape.mk₁ input) (by simp) (by simp)

theorem tally_run_pending (N : ℕ) (coins : List Bool) (q : TallyState N)
    (T : Turing.Tape (Option Bool)) (hshort : q.1.val + coins.length < N) :
    coinTapeRunAux (tallyTable N) (tallyAccept N) coins ⟨q, T⟩ = (none, coins.length) ∧
    coinTapeTransitionCountAux (tallyTable N) coins ⟨q, T⟩ = coins.length := by
  induction coins generalizing q with
  | nil =>
    have hc : coinHalt (tallyTable N) ⟨q, T⟩ = false := by
      rw [tally_coinHalt]; simp only [List.length_nil, Nat.add_zero] at hshort
      simp [Nat.not_le.mpr hshort]
    simp [coinTapeRunAux, coinTapeTransitionCountAux, hc]
  | cons c cs ih =>
    have hi : q.1.val < N := by simp only [List.length_cons] at hshort; omega
    let q' : TallyState N := (⟨q.1.val + 1, by omega⟩,
      ⟨min N (q.2.val + c.toNat), by omega⟩)
    have hc : coinHalt (tallyTable N) ⟨q, T⟩ = false := by
      rw [tally_coinHalt]; simp [Nat.not_le.mpr hi]
    have hs := tally_step N q T c hi
    have hnext : q'.1.val + cs.length < N := by
      simp only [List.length_cons] at hshort
      dsimp [q']; omega
    obtain ⟨hr, hl⟩ := ih q' hnext
    constructor
    · rw [coinTapeRunAux_cons_of_step_some _ _ c cs _ _ hc hs]
      change Prod.map id (· + 1)
        (coinTapeRunAux (tallyTable N) (tallyAccept N) cs ⟨q', T⟩) = _
      rw [hr]; rfl
    · simp only [coinTapeTransitionCountAux, hc, Bool.false_eq_true, ↓reduceIte, hs]
      change coinTapeTransitionCountAux (tallyTable N) cs ⟨q', T⟩ + 1 = _
      rw [hl, List.length_cons]

theorem tally_run_sufficient (N : ℕ) (coins : List Bool) (input : List (Option Bool))
    (hlen : N ≤ coins.length) :
    coinTapeRun (tallyTable N) (tallyAccept N) input coins =
      (some (decide (N / 2 < trueCount (coins.take N))), N) ∧
    coinTapeTransitionCount (tallyTable N) input coins = N := by
  have h := tally_run (coins.take N) (coins.drop N) input
  rw [List.length_take, Nat.min_eq_left hlen, List.take_append_drop] at h
  exact h

theorem tally_state_card (N : ℕ) : Fintype.card (TallyState N) = (N + 1) ^ 2 := by
  simp [TallyState, pow_two]

theorem trueCount_ofFn {N : ℕ} (w : Fin N → Bool) :
    trueCount (List.ofFn w) = MajorityCount w := by
  simp only [trueCount, List.map_ofFn, List.sum_ofFn, MajorityCount]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  change (w j).toNat = _
  cases w j <;> rfl

theorem tally_run_ofFn {N : ℕ} (w : Fin N → Bool) (extra : List Bool)
    (input : List (Option Bool)) :
    coinTapeRun (tallyTable N) (tallyAccept N) input (List.ofFn w ++ extra) =
      (some (MajorityBit w), N) ∧
    coinTapeTransitionCount (tallyTable N) input (List.ofFn w ++ extra) = N := by
  have h := tally_run (List.ofFn w) extra input
  rw [List.length_ofFn] at h
  simpa only [trueCount_ofFn, MajorityBit] using! h

theorem tally_fair_mass (N : ℕ) (input : List (Option Bool)) (target : Bool) :
    fairTapeSuccess (tallyTable N) (tallyAccept N) input N target =
      (∑ w : Fin N → Bool, if MajorityBit w = target then (1 : ℝ) else 0) / 2 ^ N := by
  unfold fairTapeSuccess
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  have h := (tally_run_ofFn w [] input).1
  simp only [List.append_nil] at h
  rw [h]
  simp

theorem majorityBit_eq_target_iff (r : ℕ) (w : Fin (2 * r + 1) → Bool) (target : Bool) :
    MajorityBit w = target ↔ r < (Finset.univ.filter fun j => w j = target).card := by
  cases target with
  | true => exact majorityBit_eq_true_iff r w
  | false =>
    rw [majorityBit_eq_false_iff]
    have h := Finset.card_filter_add_card_filter_not (fun j => w j = true)
      (s := (Finset.univ : Finset (Fin (2 * r + 1))))
    have heq : (Finset.univ.filter fun j => ¬w j = true) =
        (Finset.univ.filter fun j => w j = false) := by
      ext j
      cases w j <;> simp
    rw [heq, Finset.card_univ, Fintype.card_fin] at h
    unfold MajorityCount
    omega

theorem uniform_product_event {I : Type*} [Fintype I] [DecidableEq I]
    (N : ℕ) (E : Finset (Fin N → I)) :
    MeasureProb (PiTensorState fun _ : Fin N => Uniform I) E =
      (∑ ω : Fin N → I, if ω ∈ E then (1 : ℝ) else 0) / (Fintype.card I : ℝ) ^ N := by
  simp only [MeasureProb, bornProb_piTensorState, bornProb_uniform,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem uniform_majority_bound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (r : ℕ) (vote : I → Bool) (target : Bool)
    (hgood : (2 / 3 : ℝ) ≤
      (∑ i : I, if vote i = target then (1 : ℝ) else 0) / Fintype.card I) :
    1 - (8 / 9 : ℝ) ^ r ≤
      (∑ ω : Fin (2 * r + 1) → I,
        if (MajorityBit fun j => vote (ω j)) = target then (1 : ℝ) else 0) /
        (Fintype.card I : ℝ) ^ (2 * r + 1) := by
  let S : Finset I := Finset.univ.filter fun i => vote i = target
  have hφ : Normalized (Uniform I) := normalized_uniform Fintype.card_pos
  have hS : MeasureProb (Uniform I) S =
      (∑ i : I, if vote i = target then (1 : ℝ) else 0) / Fintype.card I := by
    rw [measureProb_uniform]
    simp [S]
  have htotal : MeasureProb (Uniform I) S + MeasureProb (Uniform I) Sᶜ = 1 := by
    rw [← measureProb_union _ (disjoint_compl_right), Finset.union_compl]
    exact hφ
  have hq : MeasureProb (Uniform I) Sᶜ ≤ 1 / 3 := by rw [hS] at htotal; linarith
  have htail := majority_copies_fail_mass r (Uniform I) hφ S hq
  let E : Finset (Fin (2 * r + 1) → I) :=
    Finset.univ.filter fun ω => (MajorityBit fun j => vote (ω j)) = target
  have hEc : Eᶜ = (Finset.univ.filter fun ω =>
      (Finset.univ.filter fun j => ω j ∈ S).card ≤ r) := by
    ext ω
    simp [E, S, majorityBit_eq_target_iff]
  have hprod : Normalized (PiTensorState fun _ : Fin (2 * r + 1) => Uniform I) :=
    normalized_piTensorState fun _ => hφ
  have hsum : MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => Uniform I) E +
      MeasureProb (PiTensorState fun _ : Fin (2 * r + 1) => Uniform I) Eᶜ = 1 := by
    rw [← measureProb_union _ (disjoint_compl_right), Finset.union_compl]
    exact hprod
  rw [← hEc] at htail
  have hE := uniform_product_event (2 * r + 1) E
  simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hE
  rw [hE] at hsum
  linarith

theorem source_vote_eq_target {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (coins : List Bool) (target : Bool)
    (ht : (coinTapeRun M a input coins).1 ≠ none) :
    ((coinTapeRun M a input coins).1 == some true) = target ↔
      (coinTapeRun M a input coins).1 = some target := by
  cases h : (coinTapeRun M a input coins).1 with
  | none => exact (ht h).elim
  | some b => cases b <;> cases target <;> simp

theorem tallyLabels_zero (N : ℕ) : tallyLabels N (0, 0) = 0 := by
  apply Fin.ext
  simp [tallyLabels, finProdFinEquiv]

theorem native_tally_run {N : ℕ} (w : Fin N → Bool) (extra : List Bool)
    (input : List (Option Bool)) :
    coinTapeRun (nativeTallyTable N) (nativeTallyAccept N) input (List.ofFn w ++ extra) =
      (some (MajorityBit w), N) ∧
    coinTapeTransitionCount (nativeTallyTable N) input (List.ofFn w ++ extra) = N := by
  have h := relabel_run (tallyLabels N) (tallyLabels_zero N) (tallyTable N)
    (tallyAccept N) (List.ofFn w ++ extra) input
  exact ⟨h.1.trans (tally_run_ofFn w extra input).1,
    h.2.trans (tally_run_ofFn w extra input).2⟩

theorem tallyCode_run {N : ℕ} (w : Fin N → Bool) (extra : List Bool)
    (input : List (Option Bool)) :
    coinTapeRun (table (tallyCode N)) (readout (tallyCode N)) input
        (List.ofFn w ++ extra) = (some (MajorityBit w), N) ∧
    coinTapeTransitionCount (table (tallyCode N)) input (List.ofFn w ++ extra) = N := by
  simpa only [tallyCode, table_encode, readout_encode_eq] using! native_tally_run w extra input

theorem encodeMachine_run (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (input : List (Option Bool)) (coins : List Bool) :
    coinTapeRun (table (encodeMachine Q M a)) (readout (encodeMachine Q M a)) input coins =
      coinTapeRun M a input coins ∧
    coinTapeTransitionCount (table (encodeMachine Q M a)) input coins =
      coinTapeTransitionCount M input coins := by
  simp only [table_encode, readout_encode_eq]
  exact ⟨trivial, trivial⟩

theorem tallyCode_length (N : ℕ) : (tallyCode N).length = 1 + 7 * (N + 1) ^ 2 := by
  rw [tallyCode, encodeMachine_length]
  ring

theorem tallyCode_run_sufficient (N : ℕ) (coins : List Bool) (input : List (Option Bool))
    (hlen : N ≤ coins.length) :
    coinTapeRun (table (tallyCode N)) (readout (tallyCode N)) input coins =
      (some (decide (N / 2 < trueCount (coins.take N))), N) ∧
    coinTapeTransitionCount (table (tallyCode N)) input coins = N := by
  simp only [tallyCode, table_encode, readout_encode_eq]
  have h := relabel_run (tallyLabels N) (tallyLabels_zero N) (tallyTable N)
    (tallyAccept N) coins input
  have hr := tally_run_sufficient N coins input hlen
  exact ⟨h.1.trans hr.1, h.2.trans hr.2⟩

theorem tallyCode_totalAt (N t : ℕ) (input : List Bool) (hNt : N ≤ t) :
    totalAt (tallyCode N) input t := by
  intro ω
  have h := (tallyCode_run_sufficient N (List.ofFn ω) (input.map some)
    (by simpa only [List.length_ofFn] using! hNt)).1
  rw [h]
  simp

theorem tallyCode_commonHalt (N : ℕ) : commonHalt (tallyCode N) := by
  unfold commonHalt
  simp only [tallyCode, table_encode, nativeTallyTable, relabelTable]
  intro q a
  exact Option.map_eq_none_iff.trans
    ((tallyTable_commonHalt N ((tallyLabels N).symm q) a).trans Option.map_eq_none_iff.symm)

theorem runFrom_coin_constant {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (t : ℕ)
    (cfg final : Turing.TM0.Cfg Γ Λ) (coins : List Bool)
    (hr : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M t cfg = some final)
    (hh : Turing.TM0.step M final = none) (hlen : t ≤ coins.length) :
    coinTapeRunAux (fun _ => M) a coins cfg = (some (a final.q), t) ∧
    coinTapeTransitionCountAux (fun _ => M) coins cfg = t := by
  induction t generalizing cfg coins with
  | zero =>
    have heq : cfg = final := Option.some.inj hr
    subst cfg
    have hc : coinHalt (fun _ => M) final = true := by
      have htab := (TM0_step_eq_none M final).mp hh
      simp [coinHalt, htab]
    constructor
    · exact coinTapeRunAux_of_coinHalt _ _ coins final hc
    · cases coins <;> simp [coinTapeTransitionCountAux, hc]
  | succ t ih =>
    rw [show t + 1 = 1 + t by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one] at hr
    cases hs : Turing.TM0.step M cfg with
    | none => simp [hs] at hr
    | some next =>
      rw [hs] at hr
      simp only [Option.bind_some] at hr
      have hc : coinHalt (fun _ => M) cfg = false := by
        cases ht : M cfg.q cfg.Tape.head with
        | none => simp [TM0_step_apply, ht] at hs
        | some p => simp [coinHalt, ht]
      obtain ⟨c, cs, rfl⟩ : ∃ c cs, coins = c :: cs :=
        List.exists_cons_of_ne_nil (fun h => by simp [h] at hlen)
      have hlen' : t ≤ cs.length := by simp only [List.length_cons] at hlen; omega
      obtain ⟨hout, htrans⟩ := ih next cs hr hlen'
      constructor
      · rw [coinTapeRunAux_cons_of_step_some _ _ c cs _ _ hc hs, hout]
        rfl
      · simp only [coinTapeTransitionCountAux, hc, Bool.false_eq_true, ↓reduceIte, hs]
        rw [htrans]

@[simp] theorem markerCell_default : (default : MarkerCell) = (none, none, false) := rfl

theorem markerCopy_pair (left rest : List MarkerCell) (s : MarkerCell)
    (hs : s.1.isSome = true) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyTable 2
        ⟨1, Turing.Tape.mk₂ left (s :: rest)⟩ =
      some ⟨1, Turing.Tape.mk₂ (fillCell s :: left) rest⟩ := by
  simp [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom, TM0_step_apply, markerCopyTable, hs,
    TM0StmtApply, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write, Turing.Tape.move,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk]

theorem markerCopy_sweep (cells left : List MarkerCell)
    (hs : ∀ s ∈ cells, s.1.isSome = true) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyTable (2 * cells.length)
        ⟨1, Turing.Tape.mk₂ left cells⟩ =
      some ⟨1, Turing.Tape.mk₂ ((cells.map fillCell).reverse ++ left) []⟩ := by
  induction cells generalizing left with
  | nil => rfl
  | cons s rest ih =>
    have hs' : s.1.isSome = true := hs s (by simp)
    have hrest : ∀ s ∈ rest, s.1.isSome = true := fun s h => hs s (by simp [h])
    rw [List.length_cons, show 2 * (rest.length + 1) = 2 + 2 * rest.length by omega,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, markerCopy_pair left rest s hs']
    simp only [Option.bind_some]
    rw [ih (fillCell s :: left) hrest]
    simp [List.reverse_cons, List.append_assoc]

private theorem blank_head_tail {Γ : Type*} [Inhabited Γ] (right : List Γ) :
    Turing.ListBlank.mk (right.headI :: right.tail) = Turing.ListBlank.mk right := by
  simpa only [Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk,
    Turing.ListBlank.cons_mk] using! Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk right)

theorem markerCopy_return (cells right : List MarkerCell) (home : MarkerCell)
    (hhead : right.headI.2.2 = false)
    (hcells : ∀ s ∈ cells, s.2.2 = false) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyTable (cells.length + 1)
        ⟨3, Turing.Tape.mk₂ (cells ++ [home]) right⟩ =
      some ⟨3, Turing.Tape.mk₂ [] (home :: cells.reverse ++ right)⟩ := by
  induction cells generalizing right with
  | nil =>
    simp [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom, TM0_step_apply, markerCopyTable,
      TM0StmtApply, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.move,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, hhead]
    exact blank_head_tail right
  | cons s rest ih =>
    have hs : s.2.2 = false := hcells s (by simp)
    have hrest : ∀ s ∈ rest, s.2.2 = false := fun s h => hcells s (by simp [h])
    have hstep : Turing.TM0.step markerCopyTable
        (⟨3, Turing.Tape.mk₂ ((s :: rest) ++ [home]) right⟩) =
        some ⟨3, Turing.Tape.mk₂ (rest ++ [home]) (s :: right)⟩ := by
      simp [TM0_step_apply, markerCopyTable, TM0StmtApply, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.move, Turing.ListBlank.head_mk,
        Turing.ListBlank.tail_mk, hhead]
      exact blank_head_tail right
    rw [List.length_cons, show rest.length + 1 + 1 = 1 + (rest.length + 1) by omega,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep]
    simp only [Option.bind_some]
    rw [ih (s :: right) (by simpa using! hs) hrest]
    simp [List.reverse_cons, List.append_assoc]

theorem markerCopy_run (input : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyTable (3 * input.length + 3)
        (Turing.TM0.init (markerInput input)) = some ⟨4, markerCopyResult input⟩ ∧
    Turing.TM0.step markerCopyTable ⟨4, markerCopyResult input⟩ = none := by
  constructor
  · cases input with
    | nil =>
      simp [markerCopyResult, markerInput, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom,
        Turing.TM0.init, TM0_step_apply, markerCopyTable, TM0StmtApply,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
    | cons b bs =>
      let cells : List MarkerCell := (some b, none, true) :: markerInput bs
      let home : MarkerCell := (some b, some b, true)
      let copied : List MarkerCell := (markerInput bs).map fillCell
      have hmark : Turing.TM0.step markerCopyTable (Turing.TM0.init (markerInput (b :: bs))) =
          some ⟨1, Turing.Tape.mk₂ [] cells⟩ := by
        simp [cells, markerInput, Turing.TM0.init, TM0_step_apply, markerCopyTable,
          TM0StmtApply, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
      have hsweep : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyTable (2 * (bs.length + 1))
          ⟨1, Turing.Tape.mk₂ [] cells⟩ =
          some ⟨1, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ := by
        have hn : ∀ s ∈ cells, s.1.isSome = true := by
          intro s hs
          change s ∈ (some b, none, true) :: markerInput bs at hs
          rcases List.mem_cons.mp hs with rfl | hs
          · rfl
          · obtain ⟨b', _, rfl⟩ := List.mem_map.mp hs
            rfl
        have h := markerCopy_sweep cells [] hn
        simpa [cells, home, copied, markerInput, fillCell] using! h
      have hblank : Turing.TM0.step markerCopyTable
          ⟨1, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ =
          some ⟨3, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ := by
        simp [TM0_step_apply, markerCopyTable, TM0StmtApply, Turing.Tape.mk₂,
          Turing.Tape.mk', Turing.Tape.write]
      have hreturn : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyTable (bs.length + 1)
          ⟨3, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ =
          some ⟨3, Turing.Tape.mk₂ [] (home :: copied)⟩ := by
        have h := markerCopy_return copied.reverse [] home rfl (by
          simp [copied, markerInput, fillCell])
        simpa [copied, markerInput] using! h
      have hfinal : Turing.TM0.step markerCopyTable ⟨3, Turing.Tape.mk₂ [] (home :: copied)⟩ =
          some ⟨4, Turing.Tape.mk₂ [] (home :: copied)⟩ := by
        simp [TM0_step_apply, markerCopyTable, home, TM0StmtApply, Turing.Tape.mk₂,
          Turing.Tape.mk', Turing.Tape.write]
      have hout : Turing.Tape.mk₂ [] (home :: copied) = markerCopyResult (b :: bs) := by
        simp [markerCopyResult, home, copied, markerInput, fillCell, Function.comp_def, Turing.Tape.mk₁,
          Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
      simp only [List.length_cons]
      rw [show 3 * (bs.length + 1) + 3 =
        1 + (2 * (bs.length + 1) + (1 + ((bs.length + 1) + 1))) by omega,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hmark]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hsweep]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hblank]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hreturn]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hfinal, hout]
  · simp [TM0_step_apply, markerCopyTable]

theorem markerCopy_coin_run (input : List Bool) (coins : List Bool)
    (hlen : 3 * input.length + 3 ≤ coins.length) :
    coinTapeRun (fun _ => markerCopyTable) markerCopyAccept (markerInput input) coins =
      (some true, 3 * input.length + 3) ∧
    coinTapeTransitionCount (fun _ => markerCopyTable) (markerInput input) coins =
      3 * input.length + 3 := by
  have h := markerCopy_run input
  exact runFrom_coin_constant markerCopyTable markerCopyAccept (3 * input.length + 3)
    (Turing.TM0.init (markerInput input)) ⟨4, markerCopyResult input⟩ coins h.1 h.2 hlen

theorem markerReset_pair (left rest : List MarkerCell) (s : MarkerCell)
    (hs : s.1.isSome = true) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable 2
        ⟨1, Turing.Tape.mk₂ left (s :: rest)⟩ =
      some ⟨1, Turing.Tape.mk₂ (eraseCell s :: left) rest⟩ := by
  simp [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom, TM0_step_apply, markerResetTable, hs,
    TM0StmtApply, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write, Turing.Tape.move,
    Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk]

theorem markerReset_sweep (cells left : List MarkerCell)
    (hs : ∀ s ∈ cells, s.1.isSome = true) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable (2 * cells.length)
        ⟨1, Turing.Tape.mk₂ left cells⟩ =
      some ⟨1, Turing.Tape.mk₂ ((cells.map eraseCell).reverse ++ left) []⟩ := by
  induction cells generalizing left with
  | nil => rfl
  | cons s rest ih =>
    have hs' : s.1.isSome = true := hs s (by simp)
    have hrest : ∀ s ∈ rest, s.1.isSome = true := fun s h => hs s (by simp [h])
    rw [List.length_cons, show 2 * (rest.length + 1) = 2 + 2 * rest.length by omega,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, markerReset_pair left rest s hs']
    simp only [Option.bind_some]
    rw [ih (eraseCell s :: left) hrest]
    simp [List.reverse_cons, List.append_assoc]

theorem markerReset_return (cells right : List MarkerCell) (home : MarkerCell)
    (hhead : right.headI.2.2 = false)
    (hcells : ∀ s ∈ cells, s.2.2 = false) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable (cells.length + 1)
        ⟨3, Turing.Tape.mk₂ (cells ++ [home]) right⟩ =
      some ⟨3, Turing.Tape.mk₂ [] (home :: cells.reverse ++ right)⟩ := by
  induction cells generalizing right with
  | nil =>
    simp [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom, TM0_step_apply, markerResetTable,
      TM0StmtApply, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.move,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, hhead]
    exact blank_head_tail right
  | cons s rest ih =>
    have hs : s.2.2 = false := hcells s (by simp)
    have hrest : ∀ s ∈ rest, s.2.2 = false := fun s h => hcells s (by simp [h])
    have hstep : Turing.TM0.step markerResetTable
        (⟨3, Turing.Tape.mk₂ ((s :: rest) ++ [home]) right⟩) =
        some ⟨3, Turing.Tape.mk₂ (rest ++ [home]) (s :: right)⟩ := by
      simp [TM0_step_apply, markerResetTable, TM0StmtApply, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.move, Turing.ListBlank.head_mk,
        Turing.ListBlank.tail_mk, hhead]
      exact blank_head_tail right
    rw [List.length_cons, show rest.length + 1 + 1 = 1 + (rest.length + 1) by omega,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hstep]
    simp only [Option.bind_some]
    rw [ih (s :: right) (by simpa using! hs) hrest]
    simp [List.reverse_cons, List.append_assoc]

theorem markerReset_run (input : List (Bool × Option Bool)) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable (3 * input.length + 3)
        (Turing.TM0.init (markerResetInput input)) = some ⟨4, markerResetResult input⟩ ∧
    Turing.TM0.step markerResetTable ⟨4, markerResetResult input⟩ = none := by
  constructor
  · cases input with
    | nil =>
      simp [markerResetResult, markerResetInput, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom,
        Turing.TM0.init, TM0_step_apply, markerResetTable, TM0StmtApply,
        Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
    | cons b bs =>
      let cells : List MarkerCell := (some b.1, b.2, true) :: markerResetInput bs
      let home : MarkerCell := (some b.1, none, true)
      let copied : List MarkerCell := (markerResetInput bs).map eraseCell
      have hmark : Turing.TM0.step markerResetTable (Turing.TM0.init (markerResetInput (b :: bs))) =
          some ⟨1, Turing.Tape.mk₂ [] cells⟩ := by
        simp [cells, markerResetInput, Turing.TM0.init, TM0_step_apply, markerResetTable,
          TM0StmtApply, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
      have hsweep : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable (2 * (bs.length + 1))
          ⟨1, Turing.Tape.mk₂ [] cells⟩ =
          some ⟨1, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ := by
        have hn : ∀ s ∈ cells, s.1.isSome = true := by
          intro s hs
          change s ∈ (some b.1, b.2, true) :: markerResetInput bs at hs
          rcases List.mem_cons.mp hs with rfl | hs
          · rfl
          · obtain ⟨b', _, rfl⟩ := List.mem_map.mp hs
            rfl
        have h := markerReset_sweep cells [] hn
        simpa [cells, home, copied, markerResetInput, eraseCell] using! h
      have hblank : Turing.TM0.step markerResetTable
          ⟨1, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ =
          some ⟨3, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ := by
        simp [TM0_step_apply, markerResetTable, TM0StmtApply, Turing.Tape.mk₂,
          Turing.Tape.mk', Turing.Tape.write]
      have hreturn : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable (bs.length + 1)
          ⟨3, Turing.Tape.mk₂ (copied.reverse ++ [home]) []⟩ =
          some ⟨3, Turing.Tape.mk₂ [] (home :: copied)⟩ := by
        have h := markerReset_return copied.reverse [] home rfl (by
          simp [copied, markerResetInput, eraseCell])
        simpa [copied, markerResetInput] using! h
      have hfinal : Turing.TM0.step markerResetTable ⟨3, Turing.Tape.mk₂ [] (home :: copied)⟩ =
          some ⟨4, Turing.Tape.mk₂ [] (home :: copied)⟩ := by
        simp [TM0_step_apply, markerResetTable, home, TM0StmtApply, Turing.Tape.mk₂,
          Turing.Tape.mk', Turing.Tape.write]
      have hout : Turing.Tape.mk₂ [] (home :: copied) = markerResetResult (b :: bs) := by
        simp [markerResetResult, home, copied, markerResetInput, eraseCell, Function.comp_def, Turing.Tape.mk₁,
          Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
      simp only [List.length_cons]
      rw [show 3 * (bs.length + 1) + 3 =
        1 + (2 * (bs.length + 1) + (1 + ((bs.length + 1) + 1))) by omega,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hmark]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hsweep]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hblank]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hreturn]
      simp only [Option.bind_some]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hfinal, hout]
  · simp [TM0_step_apply, markerResetTable]

theorem markerReset_coin_run (input : List (Bool × Option Bool)) (coins : List Bool)
    (hlen : 3 * input.length + 3 ≤ coins.length) :
    coinTapeRun (fun _ => markerResetTable) markerResetAccept (markerResetInput input) coins =
      (some true, 3 * input.length + 3) ∧
    coinTapeTransitionCount (fun _ => markerResetTable) (markerResetInput input) coins =
      3 * input.length + 3 := by
  have h := markerReset_run input
  exact runFrom_coin_constant markerResetTable markerResetAccept (3 * input.length + 3)
    (Turing.TM0.init (markerResetInput input)) ⟨4, markerResetResult input⟩ coins h.1 h.2 hlen

theorem runFrom_map_success {Γ Λ Μ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M : Turing.TM0.Machine Γ Λ) (M' : Turing.TM0.Machine Γ Μ) (f : Λ → Μ)
    (hstep : ∀ cfg cfg', Turing.TM0.step M cfg = some cfg' →
      Turing.TM0.step M' (mapCfg f cfg) = some (mapCfg f cfg'))
    (t : ℕ) (cfg final : Turing.TM0.Cfg Γ Λ)
    (hr : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M t cfg = some final) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M' t (mapCfg f cfg) = some (mapCfg f final) := by
  induction t generalizing cfg with
  | zero =>
    have heq : cfg = final := Option.some.inj hr
    subst cfg
    rfl
  | succ t ih =>
    rw [show t + 1 = 1 + t by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one] at hr ⊢
    cases hs : Turing.TM0.step M cfg with
    | none => simp [hs] at hr
    | some next =>
      rw [hs] at hr
      simp only [Option.bind_some] at hr
      rw [hstep cfg next hs]
      simp only [Option.bind_some]
      exact ih next hr

theorem sequence_left_step {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (M₂ : Turing.TM0.Machine Γ Μ)
    (cfg next : Turing.TM0.Cfg Γ Λ) (hs : Turing.TM0.step M₁ cfg = some next) :
    Turing.TM0.step (sequenceTable M₁ M₂) (mapCfg Sum.inl cfg) =
      some (mapCfg Sum.inl next) := by
  cases ht : M₁ cfg.q cfg.Tape.head with
  | none => simp [TM0_step_apply, ht] at hs
  | some p =>
    rw [TM0_step_apply, ht] at hs
    cases hs
    simp [TM0_step_apply, sequenceTable, mapCfg, ht]

theorem sequence_right_step {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (M₂ : Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Μ) :
    Turing.TM0.step (sequenceTable M₁ M₂) (mapCfg Sum.inr cfg) =
      (Turing.TM0.step M₂ cfg).map (mapCfg Sum.inr) := by
  simp only [TM0_step_apply, sequenceTable, mapCfg, Option.map_map, Function.comp_def]

theorem sequence_dispatch {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (M₂ : Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Λ) (hh : Turing.TM0.step M₁ cfg = none) :
    Turing.TM0.step (sequenceTable M₁ M₂) (mapCfg Sum.inl cfg) =
      some ⟨Sum.inr default, cfg.Tape⟩ := by
  have ht := (TM0_step_eq_none M₁ cfg).mp hh
  simp [TM0_step_apply, sequenceTable, mapCfg, ht, TM0StmtApply]

theorem sequence_run {Γ Λ Μ : Type} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (M₂ : Turing.TM0.Machine Γ Μ)
    (t₁ t₂ : ℕ) (cfg final₁ : Turing.TM0.Cfg Γ Λ) (final₂ : Turing.TM0.Cfg Γ Μ)
    (hr₁ : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M₁ t₁ cfg = some final₁)
    (hh₁ : Turing.TM0.step M₁ final₁ = none)
    (hr₂ : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M₂ t₂ ⟨default, final₁.Tape⟩ = some final₂)
    (hh₂ : Turing.TM0.step M₂ final₂ = none) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (sequenceTable M₁ M₂) (t₁ + 1 + t₂)
        (mapCfg Sum.inl cfg) = some (mapCfg Sum.inr final₂) ∧
    Turing.TM0.step (sequenceTable M₁ M₂) (mapCfg Sum.inr final₂) = none := by
  have hleft := runFrom_map_success M₁ (sequenceTable M₁ M₂) Sum.inl
    (sequence_left_step M₁ M₂) t₁ cfg final₁ hr₁
  have hright := runFrom_map_success M₂ (sequenceTable M₁ M₂) Sum.inr
    (fun cfg cfg' hs => by rw [sequence_right_step, hs]; rfl)
    t₂ ⟨default, final₁.Tape⟩ final₂ hr₂
  constructor
  · rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      hleft]
    simp only [Option.bind_some]
    rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one,
        sequence_dispatch M₁ M₂ final₁ hh₁]
    exact hright
  · rw [sequence_right_step, hh₂]
    rfl

theorem runFrom_eq_of_step_eq {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (t : ℕ) (cfg₁ cfg₂ : Turing.TM0.Cfg Γ Λ)
    (hs : Turing.TM0.step M cfg₁ = Turing.TM0.step M cfg₂) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M (t + 1) cfg₁ =
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M (t + 1) cfg₂ := by
  rw [show t + 1 = 1 + t by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one,
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]

theorem markerReset_after_copy (input : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerResetTable (3 * input.length + 3)
        ⟨0, markerCopyResult input⟩ = some ⟨4, markerErasedResult input⟩ ∧
    Turing.TM0.step markerResetTable ⟨4, markerErasedResult input⟩ = none := by
  have hs : Turing.TM0.step markerResetTable ⟨0, markerCopyResult input⟩ =
      Turing.TM0.step markerResetTable
        (Turing.TM0.init (markerResetInput (input.map fun b => (b, some b)))) := by
    cases input with
    | nil =>
      simp [TM0_step_apply, markerCopyResult, markerResetInput, markerResetTable,
        Turing.TM0.init, TM0StmtApply, Turing.Tape.mk₁, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.write]
    | cons b bs =>
      simp [TM0_step_apply, markerCopyResult, markerResetInput, markerResetTable,
        Function.comp_def, Turing.TM0.init, TM0StmtApply, Turing.Tape.mk₁,
        Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.write]
  have heq := runFrom_eq_of_step_eq markerResetTable (3 * input.length + 2)
    ⟨0, markerCopyResult input⟩
    (Turing.TM0.init (markerResetInput (input.map fun b => (b, some b)))) hs
  constructor
  · rw [show 3 * input.length + 3 = (3 * input.length + 2) + 1 by omega, heq]
    simpa [markerErasedResult, markerResetResult, Function.comp_def] using!
      (markerReset_run (input.map fun b => (b, some b))).1
  · simp [TM0_step_apply, markerResetTable]

theorem markerCopyReset_run (input : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyResetTable (6 * input.length + 7)
        (Turing.TM0.init (markerInput input)) = some ⟨9, markerErasedResult input⟩ ∧
    Turing.TM0.step markerCopyResetTable ⟨9, markerErasedResult input⟩ = none := by
  have hc := markerCopy_run input
  have hr := markerReset_after_copy input
  have h := sequence_run markerCopyTable markerResetTable
    (3 * input.length + 3) (3 * input.length + 3)
    (Turing.TM0.init (markerInput input)) ⟨4, markerCopyResult input⟩
    ⟨4, markerErasedResult input⟩ hc.1 hc.2 hr.1 hr.2
  rw [show (3 * input.length + 3) + 1 + (3 * input.length + 3) =
    6 * input.length + 7 by omega] at h
  have hlift := runFrom_map_success (sequenceTable markerCopyTable markerResetTable)
    markerCopyResetTable markerCopyResetLabels (fun cfg cfg' hs => by
      change Turing.TM0.step (relabelTable markerCopyResetLabels
        (fun _ => sequenceTable markerCopyTable markerResetTable) false)
        (relabelCfg markerCopyResetLabels cfg) = some (relabelCfg markerCopyResetLabels cfg')
      rw [relabel_step, hs]
      rfl) (6 * input.length + 7)
    (mapCfg Sum.inl (Turing.TM0.init (markerInput input)))
    (mapCfg Sum.inr ⟨4, markerErasedResult input⟩) h.1
  have hzero : markerCopyResetLabels (.inl 0) = 0 := by decide
  have hlast : markerCopyResetLabels (.inr 4) = 9 := by decide
  constructor
  · change Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerCopyResetTable (6 * input.length + 7)
      ⟨markerCopyResetLabels (.inl 0), Turing.Tape.mk₁ (markerInput input)⟩ =
      some ⟨markerCopyResetLabels (.inr 4), markerErasedResult input⟩ at hlift
    rw [hzero, hlast] at hlift
    exact hlift
  · have hs := relabel_step markerCopyResetLabels
      (fun _ => sequenceTable markerCopyTable markerResetTable) false
      (mapCfg Sum.inr ⟨4, markerErasedResult input⟩)
    rw [h.2] at hs
    change Turing.TM0.step markerCopyResetTable
      ⟨markerCopyResetLabels (.inr 4), markerErasedResult input⟩ = none at hs
    rw [hlast] at hs
    exact hs

theorem markerCopyReset_coin_run (input : List Bool) (coins : List Bool)
    (hlen : 6 * input.length + 7 ≤ coins.length) :
    coinTapeRun (fun _ => markerCopyResetTable) markerCopyResetAccept (markerInput input) coins =
      (some true, 6 * input.length + 7) ∧
    coinTapeTransitionCount (fun _ => markerCopyResetTable) (markerInput input) coins =
      6 * input.length + 7 := by
  have h := markerCopyReset_run input
  exact runFrom_coin_constant markerCopyResetTable markerCopyResetAccept (6 * input.length + 7)
    (Turing.TM0.init (markerInput input)) ⟨9, markerErasedResult input⟩ coins h.1 h.2 hlen

theorem run_exact_prefix_iff {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) (front suffix : List Bool) (b : Bool) :
    coinTapeRunAux M a (front ++ suffix) cfg = (some b, front.length) ↔
      coinTapeRunAux M a front cfg = (some b, front.length) := by
  constructor
  · intro h
    have ht := coinTapeRunAux_take M a (front ++ suffix) cfg b front.length h (by simp)
    simpa using! ht
  · intro h
    exact coinTapeRunAux_append M a front cfg b front.length h suffix

theorem stopped_prefix_suffix_mass {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) (k m : ℕ) (b : Bool)
    (P : (Fin m → Bool) → Prop) [DecidablePred P] :
    (∑ tapes : (Fin k → Bool) × (Fin m → Bool),
      if coinTapeRunAux M a (List.ofFn tapes.1 ++ List.ofFn tapes.2) cfg = (some b, k) ∧ P tapes.2
        then (1 : ℝ) else 0) / 2 ^ (k + m) =
      ((∑ front : Fin k → Bool,
        if coinTapeRunAux M a (List.ofFn front) cfg = (some b, k) then (1 : ℝ) else 0) / 2 ^ k) *
      ((∑ suffix : Fin m → Bool, if P suffix then (1 : ℝ) else 0) / 2 ^ m) := by
  have hp (u : Fin k → Bool) (v : Fin m → Bool) :
      coinTapeRunAux M a (List.ofFn u ++ List.ofFn v) cfg = (some b, k) ↔
        coinTapeRunAux M a (List.ofFn u) cfg = (some b, k) := by
    simpa only [List.length_ofFn] using! run_exact_prefix_iff M a cfg (List.ofFn u) (List.ofFn v) b
  have hs : (∑ tapes : (Fin k → Bool) × (Fin m → Bool),
      if coinTapeRunAux M a (List.ofFn tapes.1 ++ List.ofFn tapes.2) cfg = (some b, k) ∧ P tapes.2
        then (1 : ℝ) else 0) =
      (∑ front : Fin k → Bool,
        if coinTapeRunAux M a (List.ofFn front) cfg = (some b, k) then (1 : ℝ) else 0) *
      (∑ suffix : Fin m → Bool, if P suffix then (1 : ℝ) else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    simp only [hp]
    by_cases hu : coinTapeRunAux M a (List.ofFn u) cfg = (some b, k) <;>
      by_cases hv : P v <;> simp [hu, hv]
  rw [hs, pow_add, mul_div_mul_comm]

theorem coinConfigRunAux_readout {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool)
    (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    ((coinConfigRunAux M coins cfg).stopped.map fun final => a final.q,
      (coinConfigRunAux M coins cfg).reads) = coinTapeRunAux M a coins cfg ∧
    (coinConfigRunAux M coins cfg).transitions = coinTapeTransitionCountAux M coins cfg := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M cfg = true <;>
      simp [coinConfigRunAux, coinTapeRunAux, coinTapeTransitionCountAux, hc]
  | cons c cs ih =>
    by_cases hc : coinHalt M cfg = true
    · simp [coinConfigRunAux, coinTapeRunAux, coinTapeTransitionCountAux, hc]
    · cases hs : Turing.TM0.step (M c) cfg with
      | none => simp [coinConfigRunAux, coinTapeRunAux, coinTapeTransitionCountAux, hc, hs]
      | some next =>
        obtain ⟨ho, ht⟩ := ih next
        simp only [coinConfigRunAux, coinTapeRunAux, coinTapeTransitionCountAux, hc,
          hs]
        rw [← ho, ht]
        exact ⟨rfl, rfl⟩

theorem coinConfigRunAux_append {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (coins extra : List Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) (hstop : (coinConfigRunAux M coins cfg).stopped ≠ none) :
    coinConfigRunAux M (coins ++ extra) cfg = coinConfigRunAux M coins cfg := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M cfg = true
    · cases extra <;> simp [coinConfigRunAux, hc]
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt M cfg = true
    · simp [coinConfigRunAux, hc]
    · cases hs : Turing.TM0.step (M c) cfg with
      | none => simp [coinConfigRunAux, hc, hs]
      | some next =>
        have hn : (coinConfigRunAux M cs next).stopped ≠ none := by
          simpa only [coinConfigRunAux, hc, hs] using! hstop
        simp only [List.cons_append, coinConfigRunAux, hc, hs, ih next hn]

theorem step_none_common_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ)
    (hcommon : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (c : Bool) (cfg : Turing.TM0.Cfg Γ Λ) (hs : Turing.TM0.step (M c) cfg = none) :
    coinHalt M cfg = true := by
  have ht := (TM0_step_eq_none (M c) cfg).mp hs
  cases c with
  | false =>
    have ht' := (hcommon cfg.q cfg.Tape.head).mp ht
    simp [coinHalt, ht, ht']
  | true =>
    have ht' := (hcommon cfg.q cfg.Tape.head).mpr ht
    simp [coinHalt, ht, ht']

theorem coinConfigRunAux_commonHalt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ)
    (hcommon : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    (coinConfigRunAux M coins cfg).transitions = (coinConfigRunAux M coins cfg).reads ∧
    ∀ final, (coinConfigRunAux M coins cfg).stopped = some final → coinHalt M final = true := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M cfg = true
    · simp only [coinConfigRunAux, hc, ↓reduceIte]
      constructor
      · trivial
      · intro final heq
        have hcfg : cfg = final := Option.some.inj heq
        subst final
        exact hc
    · simp [coinConfigRunAux, hc]
  | cons c cs ih =>
    by_cases hc : coinHalt M cfg = true
    · simp only [coinConfigRunAux, hc, ↓reduceIte]
      constructor
      · trivial
      · intro final heq
        have hcfg : cfg = final := Option.some.inj heq
        subst final
        exact hc
    · cases hs : Turing.TM0.step (M c) cfg with
      | none => exact (hc (step_none_common_halt M hcommon c cfg hs)).elim
      | some next =>
        obtain ⟨hl, hf⟩ := ih next
        simp only [coinConfigRunAux, hc, hs]
        exact ⟨congrArg Nat.succ hl, hf⟩

theorem coinConfigRunAux_reads_le {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    (coinConfigRunAux M coins cfg).reads ≤ coins.length := by
  have h := congrArg Prod.snd (coinConfigRunAux_readout M (fun _ => false) coins cfg).1
  change (coinConfigRunAux M coins cfg).reads = (coinTapeRunAux M (fun _ => false) coins cfg).2 at h
  rw [h]
  exact coinTapeRunAux_snd_le M (fun _ => false) coins cfg

theorem coinConfigRunAux_take {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (hstop : (coinConfigRunAux M coins cfg).stopped ≠ none) :
    coinConfigRunAux M (coins.take (coinConfigRunAux M coins cfg).reads) cfg =
      coinConfigRunAux M coins cfg := by
  induction coins generalizing cfg with
  | nil => simp
  | cons c cs ih =>
    by_cases hc : coinHalt M cfg = true
    · simp [coinConfigRunAux, hc]
    · cases hs : Turing.TM0.step (M c) cfg with
      | none => simp [coinConfigRunAux, hc, hs]
      | some next =>
        have hn : (coinConfigRunAux M cs next).stopped ≠ none := by
          simpa only [coinConfigRunAux, hc, hs] using! hstop
        simp [coinConfigRunAux, hc, hs, ih next hn]

theorem sequence_coinHalt_right {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Μ) :
    coinHalt (sequenceCoinTable M₁ M₂) (mapCfg Sum.inr cfg) = coinHalt M₂ cfg := by
  simp [coinHalt, sequenceCoinTable, sequenceTable, mapCfg]

theorem sequence_coinHalt_left {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Λ) :
    coinHalt (sequenceCoinTable M₁ M₂) (mapCfg Sum.inl cfg) = false := by
  cases hf : M₁ false cfg.q cfg.Tape.head <;>
    cases ht : M₁ true cfg.q cfg.Tape.head <;>
      simp [coinHalt, sequenceCoinTable, sequenceTable, mapCfg, hf, ht]

theorem sequence_coinConfig_right {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Μ) :
    coinConfigRunAux (sequenceCoinTable M₁ M₂) coins (mapCfg Sum.inr cfg) =
      let r := coinConfigRunAux M₂ coins cfg
      ⟨r.stopped.map (mapCfg Sum.inr), r.reads, r.transitions⟩ := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M₂ cfg = true <;>
      simp [coinConfigRunAux, sequence_coinHalt_right, hc]
  | cons c cs ih =>
    by_cases hc : coinHalt M₂ cfg = true
    · simp [coinConfigRunAux, sequence_coinHalt_right, hc]
    · have hs := sequence_right_step (M₁ c) (M₂ c) cfg
      change Turing.TM0.step (sequenceCoinTable M₁ M₂ c) (mapCfg Sum.inr cfg) = _ at hs
      simp only [coinConfigRunAux, sequence_coinHalt_right, hc, Bool.false_eq_true, ↓reduceIte, hs]
      cases ht : Turing.TM0.step (M₂ c) cfg with
      | none => rfl
      | some next => simp [ih]

theorem coinHalt_step_none {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (cfg : Turing.TM0.Cfg Γ Λ)
    (hc : coinHalt M cfg = true) (c : Bool) : Turing.TM0.step (M c) cfg = none := by
  have ht : M false cfg.q cfg.Tape.head = none ∧ M true cfg.q cfg.Tape.head = none := by
    simpa [coinHalt] using! hc
  cases c with
  | false => exact (TM0_step_eq_none _ _).mpr ht.1
  | true => exact (TM0_step_eq_none _ _).mpr ht.2

theorem sequenceCoinTable_commonHalt {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (hc : ∀ q s, (M₂ false q s = none) ↔ (M₂ true q s = none)) :
    ∀ q s, (sequenceCoinTable M₁ M₂ false q s = none) ↔
      (sequenceCoinTable M₁ M₂ true q s = none) := by
  intro q s
  cases q with
  | inl q =>
    cases hf : M₁ false q s <;> cases ht : M₁ true q s <;>
      simp [sequenceCoinTable, sequenceTable, hf, ht]
  | inr q =>
    exact Option.map_eq_none_iff.trans ((hc q s).trans Option.map_eq_none_iff.symm)

theorem sequence_coinConfig_left {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (hcommon : ∀ q s, (M₁ false q s = none) ↔ (M₁ true q s = none))
    (front tail : List Bool) (switch : Bool) (cfg final : Turing.TM0.Cfg Γ Λ)
    (hstop : (coinConfigRunAux M₁ front cfg).stopped = some final)
    (hread : (coinConfigRunAux M₁ front cfg).reads = front.length) :
    let r := coinConfigRunAux M₂ tail ⟨default, final.Tape⟩
    let total := coinConfigRunAux (sequenceCoinTable M₁ M₂)
      (front ++ switch :: tail) (mapCfg Sum.inl cfg)
    total.stopped = r.stopped.map (mapCfg Sum.inr) ∧
      total.reads = r.reads + front.length + 1 ∧
      total.transitions = r.transitions + front.length + 1 := by
  induction front generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M₁ cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      have hd := sequence_dispatch (M₁ switch) (M₂ switch) cfg
        (coinHalt_step_none M₁ cfg hc switch)
      change Turing.TM0.step (sequenceCoinTable M₁ M₂ switch) (mapCfg Sum.inl cfg) = _ at hd
      have hr := sequence_coinConfig_right M₁ M₂ tail
        (⟨default, cfg.Tape⟩ : Turing.TM0.Cfg Γ Μ)
      change coinConfigRunAux (sequenceCoinTable M₁ M₂) tail
        ⟨Sum.inr default, cfg.Tape⟩ = _ at hr
      (try dsimp only)
      simp only [List.nil_append, List.length_nil, coinConfigRunAux, sequence_coinHalt_left,
        Bool.false_eq_true, ↓reduceIte, hd]
      rw [hr]
      simp
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt M₁ cfg = true
    · simp [coinConfigRunAux, hc] at hread
    · cases hs : Turing.TM0.step (M₁ c) cfg with
      | none => exact (hc (step_none_common_halt M₁ hcommon c cfg hs)).elim
      | some next =>
        have hstop' : (coinConfigRunAux M₁ cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, hs] using! hstop
        have hread' : (coinConfigRunAux M₁ cs next).reads = cs.length := by
          have h := hread
          simp only [coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, hs,
              List.length_cons] at h
          exact Nat.succ.inj h
        have hp := sequence_left_step (M₁ c) (M₂ c) cfg next hs
        change Turing.TM0.step (sequenceCoinTable M₁ M₂ c) (mapCfg Sum.inl cfg) = _ at hp
        obtain ⟨ho, hr, ht⟩ := ih next hstop' hread'
        (try dsimp only)
        simp only [List.cons_append, List.length_cons, coinConfigRunAux, sequence_coinHalt_left,
          Bool.false_eq_true, ↓reduceIte, hp]
        constructor
        · exact ho
        · constructor
          · rw [hr]
            omega
          · rw [ht]
            omega

theorem coinConfigRunAux_const_trace {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (coins : List Bool) (cfg final : Turing.TM0.Cfg Γ Λ)
    (hstop : (coinConfigRunAux (fun _ => M) coins cfg).stopped = some final) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M (coinConfigRunAux (fun _ => M) coins cfg).transitions cfg =
      some final := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt (fun _ => M) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      simp [coinConfigRunAux, hc, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom]
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt (fun _ => M) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      simp [coinConfigRunAux, hc, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom]
    · cases hs : Turing.TM0.step M cfg with
      | none =>
        exact (hc (step_none_common_halt (fun _ => M) (fun _ _ => Iff.rfl) c cfg hs)).elim
      | some next =>
        have hn : (coinConfigRunAux (fun _ => M) cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, hs] using! hstop
        have ht := ih next hn
        simp only [coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, hs]
        rw [show (coinConfigRunAux (fun _ => M) cs next).transitions + 1 =
          1 + (coinConfigRunAux (fun _ => M) cs next).transitions by omega,
          Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
        exact ht

theorem coinConfigRunAux_const {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    (M : Turing.TM0.Machine Γ Λ) (t : ℕ) (cfg final : Turing.TM0.Cfg Γ Λ)
    (coins : List Bool) (hr : Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom M t cfg = some final)
    (hh : Turing.TM0.step M final = none) (hlen : t ≤ coins.length) :
    (coinConfigRunAux (fun _ => M) coins cfg).stopped = some final ∧
    (coinConfigRunAux (fun _ => M) coins cfg).reads = t ∧
    (coinConfigRunAux (fun _ => M) coins cfg).transitions = t := by
  have hp := coinConfigRunAux_readout (fun _ => M) (fun _ => true) coins cfg
  have hf := runFrom_coin_constant M (fun _ => true) t cfg final coins hr hh hlen
  have hread : (coinConfigRunAux (fun _ => M) coins cfg).reads = t := by
    have h := congrArg Prod.snd hp.1
    change (coinConfigRunAux (fun _ => M) coins cfg).reads =
      (coinTapeRunAux (fun _ => M) (fun _ => true) coins cfg).2 at h
    rw [hf.1] at h
    exact h
  have htrans : (coinConfigRunAux (fun _ => M) coins cfg).transitions = t := hp.2.trans hf.2
  have hbit : (coinConfigRunAux (fun _ => M) coins cfg).stopped.map (fun _ => true) = some true := by
    have h := congrArg Prod.fst hp.1
    change (coinConfigRunAux (fun _ => M) coins cfg).stopped.map (fun _ => true) =
      (coinTapeRunAux (fun _ => M) (fun _ => true) coins cfg).1 at h
    rw [hf.1] at h
    exact h
  cases hs : (coinConfigRunAux (fun _ => M) coins cfg).stopped with
  | none => simp [hs] at hbit
  | some actual =>
    have ht := coinConfigRunAux_const_trace M coins cfg actual hs
    rw [htrans, hr] at ht
    have heq : final = actual := Option.some.inj ht
    subst actual
    exact ⟨rfl, hread, htrans⟩

theorem markerCopy_then_coin_source {Μ : Type*} [Inhabited Μ]
    (M : Bool → Turing.TM0.Machine MarkerCell Μ) (input : List Bool)
    (front : Fin (3 * input.length + 3) → Bool) (switch : Bool) (tail : List Bool) :
    let r := coinConfigRunAux M tail ⟨default, markerCopyResult input⟩
    let total := coinConfigRunAux (sequenceCoinTable (fun _ => markerCopyTable) M)
      (List.ofFn front ++ switch :: tail)
      (mapCfg Sum.inl (Turing.TM0.init (markerInput input)))
    total.stopped = r.stopped.map (mapCfg Sum.inr) ∧
      total.reads = r.reads + (3 * input.length + 4) ∧
      total.transitions = r.transitions + (3 * input.length + 4) := by
  have hc := markerCopy_run input
  have hp := coinConfigRunAux_const markerCopyTable (3 * input.length + 3)
    (Turing.TM0.init (markerInput input)) ⟨4, markerCopyResult input⟩ (List.ofFn front)
    hc.1 hc.2 (by simp)
  have h := sequence_coinConfig_left (fun _ => markerCopyTable) M (fun _ _ => Iff.rfl)
    (List.ofFn front) tail switch (Turing.TM0.init (markerInput input))
    ⟨4, markerCopyResult input⟩ hp.1 (by simpa only [List.length_ofFn] using! hp.2.1)
  simpa only [List.length_ofFn, Nat.add_assoc, Nat.reduceAdd] using! h

theorem liftWork_step {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    (Turing.TM0.step (liftWorkTable M c) cfg).map workCfg =
      Turing.TM0.step (M c) (workCfg cfg) := by
  simp only [TM0_step_apply, liftWorkTable, workCfg, Turing.Tape.map_fst]
  change (Option.map (fun p => ⟨p.1, TM0StmtApply cfg.Tape p.2⟩)
    (Option.map (fun p => match p.2 with
      | .move d => (p.1, Turing.TM0.Stmt.move d)
      | .write b => (p.1, Turing.TM0.Stmt.write (cfg.Tape.head.1, b, cfg.Tape.head.2.2)))
      (M c cfg.q cfg.Tape.head.2.1))).map workCfg =
      Option.map (fun p => ⟨p.1, TM0StmtApply (cfg.Tape.map workMap) p.2⟩)
        (M c cfg.q cfg.Tape.head.2.1)
  cases ht : M c cfg.q cfg.Tape.head.2.1 with
  | none => rfl
  | some p =>
    obtain ⟨q, stmt⟩ := p
    cases stmt with
    | move d => simp [workCfg, TM0StmtApply, Turing.Tape.map_move]
    | write b => simp [workCfg, TM0StmtApply, workMap]

theorem liftWork_coinHalt {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    coinHalt (liftWorkTable M) cfg = coinHalt M (workCfg cfg) := by
  simp [coinHalt, liftWorkTable, workCfg, workMap]

theorem liftWork_coin_run {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (coins : List Bool) (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    coinTapeRunAux (liftWorkTable M) a coins cfg = coinTapeRunAux M a coins (workCfg cfg) ∧
    coinTapeTransitionCountAux (liftWorkTable M) coins cfg =
      coinTapeTransitionCountAux M coins (workCfg cfg) := by
  induction coins generalizing cfg with
  | nil =>
    simp only [coinTapeRunAux, coinTapeTransitionCountAux, liftWork_coinHalt]
    exact ⟨rfl, True.intro⟩
  | cons c cs ih =>
    by_cases hc : coinHalt (liftWorkTable M) cfg = true
    · have hc' : coinHalt M (workCfg cfg) = true := by rw [← liftWork_coinHalt]; exact hc
      simp only [coinTapeRunAux, coinTapeTransitionCountAux, hc, hc', ↓reduceIte]
      exact ⟨rfl, True.intro⟩
    · have hc' : coinHalt M (workCfg cfg) ≠ true := by rw [← liftWork_coinHalt]; exact hc
      have hstep := liftWork_step M c cfg
      cases hs : Turing.TM0.step (liftWorkTable M c) cfg with
      | none =>
        have hsource : Turing.TM0.step (M c) (workCfg cfg) = none := by rw [← hstep, hs]; rfl
        simp only [coinTapeRunAux, coinTapeTransitionCountAux, hc, hc', hs, hsource]
        exact ⟨rfl, True.intro⟩
      | some next =>
        have hsource : Turing.TM0.step (M c) (workCfg cfg) = some (workCfg next) := by
          rw [← hstep, hs]; rfl
        obtain ⟨ho, ht⟩ := ih next
        simp only [coinTapeRunAux, coinTapeTransitionCountAux, hc, hc', hs, hsource]
        rw [ho, ht]
        exact ⟨rfl, rfl⟩

theorem markerCopyResult_work (input : List Bool) :
    (markerCopyResult input).map workMap = Turing.Tape.mk₁ (input.map some) := by
  unfold markerCopyResult
  rw [Turing.Tape.map_write]
  change ((Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).map workMap).write
    ((Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).map workMap).head = _
  rw [Turing.Tape.write_self, Turing.Tape.map_mk₁]
  simp [workMap, Function.comp_def]

theorem liftWork_commonHalt {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ q s, (liftWorkTable M false q s = none) ↔ (liftWorkTable M true q s = none) := by
  intro q s
  exact Option.map_eq_none_iff.trans ((hc q s.2.1).trans Option.map_eq_none_iff.symm)

theorem prepareLabels_zero (Q : ℕ) : prepareLabels Q (.inl 0) = 0 := by
  apply Fin.ext
  simp [prepareLabels, finSumFinEquiv]

theorem prepare_initial (Q : ℕ) (input : List Bool) :
    relabelCfg (prepareLabels Q) (mapCfg Sum.inl (Turing.TM0.init (markerInput input))) =
      Turing.TM0.init (markerInput input) := by
  change (⟨prepareLabels Q (.inl 0), Turing.Tape.mk₁ (markerInput input)⟩ :
    Turing.TM0.Cfg MarkerCell (Fin (Q + 6))) = _
  rw [prepareLabels_zero]
  rfl

theorem prepare_coin_run (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (input : List Bool)
    (front : Fin (3 * input.length + 3) → Bool) (switch : Bool) (tail : List Bool) :
    coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
        (List.ofFn front ++ switch :: tail) =
      Prod.map id (fun n => n + (3 * input.length + 4)) (coinTapeRun M a (input.map some) tail) ∧
    coinTapeTransitionCount (prepareCoinTable Q M) (markerInput input)
        (List.ofFn front ++ switch :: tail) =
      coinTapeTransitionCount M (input.map some) tail + (3 * input.length + 4) := by
  let cfg : Turing.TM0.Cfg MarkerCell (Fin 5) := Turing.TM0.init (markerInput input)
  let cfg₂ : Turing.TM0.Cfg MarkerCell (Fin (Q + 1)) := ⟨default, markerCopyResult input⟩
  let seq := sequenceCoinTable (fun _ => markerCopyTable) (liftWorkTable M)
  let coins := List.ofFn front ++ switch :: tail
  have hp := markerCopy_then_coin_source (liftWorkTable M) input front switch tail
  have ho := coinConfigRunAux_readout seq (sourcePhaseAccept a) coins (mapCfg Sum.inl cfg)
  have hs := coinConfigRunAux_readout (liftWorkTable M) a tail cfg₂
  have hcfg : workCfg cfg₂ = Turing.TM0.init (input.map some) := by
    simp [cfg₂, workCfg, markerCopyResult_work, Turing.TM0.init]
  have hw := liftWork_coin_run M a tail cfg₂
  rw [hcfg] at hw
  have hseq : coinTapeRunAux seq (sourcePhaseAccept a) coins (mapCfg Sum.inl cfg) =
      Prod.map id (fun n => n + (3 * input.length + 4))
        (coinTapeRunAux (liftWorkTable M) a tail cfg₂) := by
    rw [← ho.1]
    rw [hp.1, hp.2.1]
    simp only [Option.map_map, mapCfg, sourcePhaseAccept, Function.comp_def]
    rw [← hs.1]
    rfl
  have hseqCount : coinTapeTransitionCountAux seq coins (mapCfg Sum.inl cfg) =
      coinTapeTransitionCountAux (liftWorkTable M) tail cfg₂ + (3 * input.length + 4) := by
    rw [← ho.2, hp.2.2, hs.2]
  have hlabel := relabel_runAux (prepareLabels Q) seq (sourcePhaseAccept a) coins
    (mapCfg Sum.inl cfg)
  have hlabelCount := relabel_transitionsAux (prepareLabels Q) seq coins (mapCfg Sum.inl cfg)
  rw [prepare_initial] at hlabel hlabelCount
  change coinTapeRunAux (prepareCoinTable Q M) (prepareAccept Q a) coins
      (Turing.TM0.init (markerInput input)) =
    coinTapeRunAux seq (sourcePhaseAccept a) coins (mapCfg Sum.inl cfg) at hlabel
  change coinTapeTransitionCountAux (prepareCoinTable Q M) coins
      (Turing.TM0.init (markerInput input)) =
    coinTapeTransitionCountAux seq coins (mapCfg Sum.inl cfg) at hlabelCount
  constructor
  · change coinTapeRunAux (prepareCoinTable Q M) (prepareAccept Q a) coins
      (Turing.TM0.init (markerInput input)) = _
    rw [hlabel, hseq, hw.1]
    rfl
  · change coinTapeTransitionCountAux (prepareCoinTable Q M) coins
      (Turing.TM0.init (markerInput input)) = _
    rw [hlabelCount, hseqCount, hw.2]
    rfl

theorem prepare_commonHalt (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ q s, (prepareCoinTable Q M false q s = none) ↔ (prepareCoinTable Q M true q s = none) := by
  intro q s
  have h := sequenceCoinTable_commonHalt (fun _ => markerCopyTable) (liftWorkTable M)
    (liftWork_commonHalt M hc) ((prepareLabels Q).symm q) s
  exact Option.map_eq_none_iff.trans (h.trans Option.map_eq_none_iff.symm)

theorem prepareCoinWords_ofFn (input : List Bool) (t : ℕ)
    (p : (Fin (3 * input.length + 3) → Bool) × Bool × (Fin t → Bool)) :
    List.ofFn (prepareCoinWords input t p) =
      List.ofFn p.1 ++ p.2.1 :: List.ofFn p.2.2 := by
  change List.ofFn (Fin.append p.1 (Fin.cons p.2.1 p.2.2)) = _
  rw [List.ofFn_fin_append, List.ofFn_succ (f := Fin.cons p.2.1 p.2.2)]
  rfl

theorem prepare_fair_mass (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (input : List Bool) (t : ℕ) (target : Bool) :
    fairTapeSuccess (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
        ((3 * input.length + 3) + (t + 1)) target =
      fairTapeSuccess M a (input.map some) t target := by
  have hp (p : (Fin (3 * input.length + 3) → Bool) × Bool × (Fin t → Bool)) :
      (coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
        (List.ofFn (prepareCoinWords input t p))).1 =
        (coinTapeRun M a (input.map some) (List.ofFn p.2.2)).1 := by
    rw [prepareCoinWords_ofFn,
      (prepare_coin_run Q M a input p.1 p.2.1 (List.ofFn p.2.2)).1]
    rfl
  have hs : (∑ w : Fin ((3 * input.length + 3) + (t + 1)) → Bool,
      if (coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
        (List.ofFn w)).1 = some target then (1 : ℝ) else 0) =
      (2 : ℝ) ^ (3 * input.length + 3) * 2 *
      (∑ w : Fin t → Bool,
        if (coinTapeRun M a (input.map some) (List.ofFn w)).1 = some target then (1 : ℝ) else 0) := by
    rw [← (prepareCoinWords input t).sum_comp]
    simp_rw [hp]
    simp only [Fintype.sum_prod_type]
    simp [mul_assoc]
  unfold fairTapeSuccess
  rw [hs, pow_add (2 : ℝ) (3 * input.length + 3) (t + 1), pow_succ (2 : ℝ) t]
  have hk : (2 : ℝ) ^ (3 * input.length + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : (2 : ℝ) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hk, ht]

theorem prepare_word_output (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (input : List Bool) (t : ℕ)
    (p : (Fin (3 * input.length + 3) → Bool) × Bool × (Fin t → Bool)) :
    (coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
      (List.ofFn (prepareCoinWords input t p))).1 =
      (coinTapeRun M a (input.map some) (List.ofFn p.2.2)).1 := by
  rw [prepareCoinWords_ofFn, (prepare_coin_run Q M a input p.1 p.2.1 (List.ofFn p.2.2)).1]
  rfl

theorem prepare_totality_iff (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (input : List Bool) (t : ℕ) :
    (∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) ↔
    (∀ w : Fin ((3 * input.length + 3) + (t + 1)) → Bool,
      (coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
        (List.ofFn w)).1 ≠ none) := by
  constructor
  · intro ht w
    have h := prepare_word_output Q M a input t ((prepareCoinWords input t).symm w)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    exact ht _
  · intro ht w
    have h := ht (prepareCoinWords input t ((fun _ => false), false, w))
    rw [prepare_word_output] at h
    exact h

theorem coinTape_totality_monotone {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ) (N : ℕ)
    (hN : ∀ w : Fin N → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hNB : N ≤ B) :
    ∀ w : Fin B → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hNB
  intro w
  let p := (appendCoinWords N extra).symm w
  have hw : w = appendCoinWords N extra p := (Equiv.apply_symm_apply _ w).symm
  have hword : List.ofFn w = List.ofFn p.1 ++ List.ofFn p.2 := by
    rw [hw]
    exact List.ofFn_fin_append p.1 p.2
  have hn := hN p.1
  cases ho : (coinTapeRun M a input (List.ofFn p.1)).1 with
  | none => exact (hn ho).elim
  | some b =>
    let reads := (coinTapeRun M a input (List.ofFn p.1)).2
    have hr : coinTapeRunAux M a (List.ofFn p.1) (Turing.TM0.init input) = (some b, reads) := by
      exact Prod.ext ho rfl
    have ha :=
        coinTapeRunAux_append M a (List.ofFn p.1) (Turing.TM0.init input) b reads hr (List.ofFn p.2)
    change (coinTapeRunAux M a (List.ofFn w) (Turing.TM0.init input)).1 ≠ none
    rw [hword, ha]
    simp

theorem fairTapeSuccess_of_total {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ) (N : ℕ)
    (hN : ∀ w : Fin N → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hNB : N ≤ B) (target : Bool) :
    fairTapeSuccess M a input B target = fairTapeSuccess M a input N target := by
  apply fairTapeSuccess_eq_of_forall_isSome M a input N target ?_ B hNB
  intro t ht w
  exact Option.isSome_iff_ne_none.mpr (coinTape_totality_monotone M a input N hN t ht w)

theorem prepare_poly_bound (c k n : ℕ) :
    (3 * n + 3) + (c * n ^ k + c + 1) ≤
      (2 * c + 7) * n ^ (2 * (k + 1)) + (2 * c + 7) := by
  by_cases hn : n = 0
  · subst n
    cases k <;> simp <;> omega
  · have hn1 : 1 ≤ n := by omega
    have hp : n ^ k ≤ n ^ (2 * (k + 1)) :=
      Nat.pow_le_pow_right hn1 (by omega)
    have hl : n ≤ n ^ (2 * (k + 1)) := by
      have h := Nat.pow_le_pow_right hn1 (show 1 ≤ 2 * (k + 1) by omega)
      simpa using! h
    have hm := Nat.mul_le_mul_right (n ^ (2 * (k + 1))) (show c + 3 ≤ 2 * c + 7 by omega)
    nlinarith [Nat.mul_le_mul_left c hp, Nat.mul_le_mul_left 3 hl]

theorem prepare_polynomial (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (c k : ℕ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (htotal : ∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
      (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q s, (prepareCoinTable Q M false q s = none) ↔ (prepareCoinTable Q M true q s = none)) ∧
      ∀ input : List Bool,
        let T := c * input.length ^ k + c
        let B := d * input.length ^ (2 * (k + 1)) + d
        (∀ w : Fin B → Bool,
          (coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
            (List.ofFn w)).1 ≠ none) ∧
        (∀ w : Fin B → Bool,
          coinTapeTransitionCount (prepareCoinTable Q M) (markerInput input) (List.ofFn w) ≤ B) ∧
        (∀ target : Bool,
          fairTapeSuccess (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input) B target =
            fairTapeSuccess M a (input.map some) T target) := by
  refine ⟨2 * c + 7, by omega, prepare_commonHalt Q M hc, ?_⟩
  intro input
  let T := c * input.length ^ k + c
  let N := (3 * input.length + 3) + (T + 1)
  let B := (2 * c + 7) * input.length ^ (2 * (k + 1)) + (2 * c + 7)
  have hn : ∀ w : Fin N → Bool,
      (coinTapeRun (prepareCoinTable Q M) (prepareAccept Q a) (markerInput input)
        (List.ofFn w)).1 ≠ none := (prepare_totality_iff Q M a input T).mp (htotal input)
  have hnb : N ≤ B := prepare_poly_bound c k input.length
  refine ⟨coinTape_totality_monotone (prepareCoinTable Q M) (prepareAccept Q a)
    (markerInput input) N hn B hnb, ?_, ?_⟩
  · intro w
    have hr := coinTapeRunAux_snd_le (prepareCoinTable Q M) (prepareAccept Q a)
      (List.ofFn w) (Turing.TM0.init (markerInput input))
    have ht := coinTapeTransitionCount_le_reads (prepareCoinTable Q M) (prepareAccept Q a)
      (markerInput input) (List.ofFn w)
    exact ht.trans (by simpa only [coinTapeRun, List.length_ofFn] using! hr)
  · intro target
    exact (fairTapeSuccess_of_total (prepareCoinTable Q M) (prepareAccept Q a)
      (markerInput input) N hn B hnb target).trans (prepare_fair_mass Q M a input T target)

theorem majorityBit_one (w : Fin 1 → Bool) : MajorityBit w = w 0 := by
  cases h : w 0 <;> simp [MajorityBit, MajorityCount, Finset.filter_singleton, h]

theorem independentMajorityMass_zero {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t : ℕ) (target : Bool)
    (ht : ∀ ω : Fin t → Bool, (coinTapeRun M a input (List.ofFn ω)).1 ≠ none) :
    independentMajorityMass M a input t 0 target = fairTapeSuccess M a input t target := by
  unfold independentMajorityMass fairTapeSuccess
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  congr 1
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin t → Bool))
  intro ω
  rw [majorityBit_one]
  have h := source_vote_eq_target M a input (List.ofFn (ω 0)) target (ht (ω 0))
  simp only [Equiv.funUnique_apply, Fin.default_eq_zero, h]
  (try rfl)

@[simp] theorem freshBlocks_apply (N t : ℕ) (coins : Fin (N * t) → Bool)
    (j : Fin N) (i : Fin t) :
    freshBlocks N t coins j i = coins (finProdFinEquiv (j, i)) := rfl

theorem freshBlocks_disjoint {N t : ℕ} {j k : Fin N} (hjk : j ≠ k) (i l : Fin t) :
    finProdFinEquiv (j, i) ≠ finProdFinEquiv (k, l) := by
  intro h
  exact hjk (congrArg Prod.fst (finProdFinEquiv.injective h))

theorem independentMajorityMass_flat {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t r : ℕ) (target : Bool) :
    independentMajorityMass M a input t r target =
      (∑ coins : Fin ((2 * r + 1) * t) → Bool,
        if (MajorityBit fun j => (coinTapeRun M a input
            (List.ofFn (freshBlocks (2 * r + 1) t coins j))).1 == some true) = target
          then (1 : ℝ) else 0) / 2 ^ ((2 * r + 1) * t) := by
  let f : (Fin (2 * r + 1) → Fin t → Bool) → ℝ := fun ω =>
    if (MajorityBit fun j => (coinTapeRun M a input
      (List.ofFn (ω j))).1 == some true) = target then 1 else 0
  change (∑ ω, f ω) / 2 ^ (t * (2 * r + 1)) =
    (∑ coins, f (freshBlocks (2 * r + 1) t coins)) / 2 ^ ((2 * r + 1) * t)
  rw [(freshBlocks (2 * r + 1) t).sum_comp, Nat.mul_comm t (2 * r + 1)]

theorem independentMajorityMass_ge {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t r : ℕ) (target : Bool)
    (ht : ∀ ω : Fin t → Bool, (coinTapeRun M a input (List.ofFn ω)).1 ≠ none)
    (hgood : (2 / 3 : ℝ) ≤ fairTapeSuccess M a input t target) :
    1 - (8 / 9 : ℝ) ^ r ≤ independentMajorityMass M a input t r target := by
  let vote : (Fin t → Bool) → Bool := fun ω =>
    (coinTapeRun M a input (List.ofFn ω)).1 == some true
  have hm : (∑ ω : Fin t → Bool, if vote ω = target then (1 : ℝ) else 0) /
      Fintype.card (Fin t → Bool) = fairTapeSuccess M a input t target := by
    unfold fairTapeSuccess
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    simp only [show (vote ω = target) ↔ (coinTapeRun M a input (List.ofFn ω)).1 = some target
      from source_vote_eq_target M a input (List.ofFn ω) target (ht ω)]
  have h := uniform_majority_bound r vote target (by rw [hm]; exact hgood)
  simpa only [independentMajorityMass, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] using! h

theorem homeAt_move_left (T : Turing.Tape MarkerCell) (off : ℤ) (h : HomeAt T off) :
    HomeAt (T.move .left) (off - 1) := by
  intro i
  rw [Turing.Tape.move_left_nth, h]
  rw [show i - 1 + off = i + (off - 1) by omega]

theorem homeAt_move_right (T : Turing.Tape MarkerCell) (off : ℤ) (h : HomeAt T off) :
    HomeAt (T.move .right) (off + 1) := by
  intro i
  rw [Turing.Tape.move_right_nth, h]
  rw [show i + 1 + off = i + (off + 1) by omega]

theorem markerHome_step_home (q : HomeState) (T : Turing.Tape MarkerCell)
    (h : T.head.2.2 = true) : Turing.TM0.step markerHomeTable ⟨q, T⟩ = none := by
  simp [TM0_step_apply, markerHomeTable, h]

theorem markerHome_step_away (left bit : Bool) (T : Turing.Tape MarkerCell)
    (h : T.head.2.2 = false) :
    Turing.TM0.step markerHomeTable ⟨(left, bit), T⟩ =
      some ⟨(left, bit), T.move (homeDirection left)⟩ := by
  simp [TM0_step_apply, markerHomeTable, h, TM0StmtApply]

theorem markerHome_run (left bit : Bool) (n : ℕ) (T : Turing.Tape MarkerCell)
    (h : HomeAt T (homeDistance left n)) :
    ∃ final : Turing.Tape MarkerCell,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerHomeTable n ⟨(left, bit), T⟩ =
        some ⟨(left, bit), final⟩ ∧
      HomeAt final 0 ∧ Turing.TM0.step markerHomeTable ⟨(left, bit), final⟩ = none ∧
      ∀ i : ℤ, final.nth i = T.nth (i - homeDistance left n) := by
  induction n generalizing T with
  | zero =>
    have hh : HomeAt T 0 := by simpa [homeDistance] using! h
    have hhead : T.head.2.2 = true := by simpa using! hh 0
    exact ⟨T, rfl, hh, markerHome_step_home (left, bit) T hhead, by simp [homeDistance]⟩
  | succ n ih =>
    have hhead : T.head.2.2 = false := by
      have hz : homeDistance left (n + 1) ≠ 0 := by
        cases left <;> dsimp [homeDistance] <;> omega
      simpa [hz] using! h 0
    have hnext : HomeAt (T.move (homeDirection left)) (homeDistance left n) := by
      cases left with
      | false =>
        have hm := homeAt_move_left T (homeDistance false (n + 1)) h
        convert! hm using 1; (try simp [homeDistance])
      | true =>
        have hm := homeAt_move_right T (homeDistance true (n + 1)) h
        convert! hm using 1; (try simp [homeDistance])
    obtain ⟨final, hr, hh, halt, data⟩ := ih (T.move (homeDirection left)) hnext
    refine ⟨final, ?_, hh, halt, ?_⟩
    · rw [show n + 1 = 1 + n by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, markerHome_step_away left bit T hhead]
      exact hr
    · intro i
      rw [data]
      cases left with
      | false =>
        change (T.move .left).nth (i - (n : ℤ)) = T.nth (i - (↑(n + 1)))
        rw [Turing.Tape.move_left_nth]
        congr 1
        omega
      | true =>
        change (T.move .right).nth (i - (-(n : ℤ))) = T.nth (i - (-(↑(n + 1))))
        rw [Turing.Tape.move_right_nth]
        congr 1
        omega

theorem markerHome_coin_run (left bit : Bool) (n : ℕ) (T : Turing.Tape MarkerCell)
    (h : HomeAt T (homeDistance left n)) (coins : List Bool) (hlen : n ≤ coins.length) :
    ∃ final : Turing.Tape MarkerCell, HomeAt final 0 ∧
      (∀ i : ℤ, final.nth i = T.nth (i - homeDistance left n)) ∧
      coinTapeRunAux (fun _ => markerHomeTable) markerHomeAccept coins ⟨(left, bit), T⟩ =
        (some bit, n) ∧
      coinTapeTransitionCountAux (fun _ => markerHomeTable) coins ⟨(left, bit), T⟩ = n := by
  obtain ⟨final, hr, hh, halt, data⟩ := markerHome_run left bit n T h
  have hc := runFrom_coin_constant markerHomeTable markerHomeAccept n ⟨(left, bit), T⟩
    ⟨(left, bit), final⟩ coins hr halt hlen
  exact ⟨final, hh, data, hc⟩

theorem homeAt_head (T : Turing.Tape MarkerCell) (off : ℤ) (h : HomeAt T off) :
    T.head.2.2 = decide (off = 0) := by simpa using! h 0

theorem homeAt_write_work (T : Turing.Tape MarkerCell) (off : ℤ) (b : Option Bool)
    (h : HomeAt T off) : HomeAt (T.write (T.head.1, b, T.head.2.2)) off := by
  intro i
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · subst i
    simpa using! h 0
  · rw [if_neg hi]
    exact h i

theorem sideAt_move_left (left : Bool) (off : ℤ) (h : SideAt left off) :
    SideAt (sideAfterMove left (decide (off = 0)) .left) (off - 1) := by
  by_cases hz : off = 0
  · subst off
    simp [SideAt, sideAfterMove]
  · have hf : sideAfterMove left (decide (off = 0)) .left = left := by simp [sideAfterMove, hz]
    rw [hf]
    exact ⟨fun hl => h.1 (by omega), fun hr => h.2 (by omega)⟩

theorem sideAt_move_right (left : Bool) (off : ℤ) (h : SideAt left off) :
    SideAt (sideAfterMove left (decide (off = 0)) .right) (off + 1) := by
  by_cases hz : off = 0
  · subst off
    simp [SideAt, sideAfterMove]
  · have hf : sideAfterMove left (decide (off = 0)) .right = left := by simp [sideAfterMove, hz]
    rw [hf]
    exact ⟨fun hl => h.1 (by omega), fun hr => h.2 (by omega)⟩

theorem markerCopyResult_home (input : List Bool) : HomeAt (markerCopyResult input) 0 := by
  intro i
  unfold markerCopyResult
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · simp [hi]
  · rw [if_neg hi]
    have hm : ((Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).nth i).2.2 = false := by
      change ((Turing.TM0.init (input.map fun b => (some b, some b, false)) :
        Turing.TM0.Cfg MarkerCell (Fin 1)).Tape.nth i).2.2 = false
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.init_nth]
      split_ifs
      · rfl
      · rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.getI_map]
        split_ifs <;> rfl
    rw [hm]
    simp [hi]

theorem sideWork_step_invariant {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (cfg next : Turing.TM0.Cfg MarkerCell (Λ × Bool)) (off : ℤ)
    (hh : HomeAt cfg.Tape off) (hs : SideAt cfg.q.2 off)
    (hstep : Turing.TM0.step (sideWorkTable M c) cfg = some next) :
    ∃ off' : ℤ, HomeAt next.Tape off' ∧ SideAt next.q.2 off' ∧ off'.natAbs ≤ off.natAbs + 1 := by
  cases ht : M c cfg.q.1 cfg.Tape.head.2.1 with
  | none => simp [TM0_step_apply, sideWorkTable, ht] at hstep
  | some p =>
    obtain ⟨q, stmt⟩ := p
    cases stmt with
    | write b =>
      have he : Turing.TM0.step (sideWorkTable M c) cfg =
          some ⟨(q, cfg.q.2), cfg.Tape.write (cfg.Tape.head.1, b, cfg.Tape.head.2.2)⟩ := by
        simp [TM0_step_apply, sideWorkTable, ht, TM0StmtApply]
      rw [he] at hstep
      have hn := Option.some.inj hstep
      subst next
      exact ⟨off, homeAt_write_work cfg.Tape off b hh, hs, by omega⟩
    | move d =>
      have he : Turing.TM0.step (sideWorkTable M c) cfg =
          some ⟨(q, sideAfterMove cfg.q.2 cfg.Tape.head.2.2 d), cfg.Tape.move d⟩ := by
        simp [TM0_step_apply, sideWorkTable, ht, TM0StmtApply]
      rw [he] at hstep
      have hn := Option.some.inj hstep
      subst next
      have hhead := homeAt_head cfg.Tape off hh
      cases d with
      | left =>
        refine ⟨off - 1, homeAt_move_left cfg.Tape off hh, ?_, ?_⟩
        · rw [hhead]
          exact sideAt_move_left cfg.q.2 off hs
        · simpa [sub_eq_add_neg] using! Int.natAbs_add_le off (-1)
      | right =>
        refine ⟨off + 1, homeAt_move_right cfg.Tape off hh, ?_, ?_⟩
        · rw [hhead]
          exact sideAt_move_right cfg.q.2 off hs
        · simpa using! Int.natAbs_add_le off 1

theorem sideWork_coin_invariant {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (coins : List Bool)
    (cfg final : Turing.TM0.Cfg MarkerCell (Λ × Bool)) (off : ℤ)
    (hh : HomeAt cfg.Tape off) (hs : SideAt cfg.q.2 off)
    (hstop : (coinConfigRunAux (sideWorkTable M) coins cfg).stopped = some final) :
    ∃ off' : ℤ, HomeAt final.Tape off' ∧ SideAt final.q.2 off' ∧
      off'.natAbs ≤ off.natAbs + (coinConfigRunAux (sideWorkTable M) coins cfg).transitions := by
  induction coins generalizing cfg off with
  | nil =>
    by_cases hc : coinHalt (sideWorkTable M) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      exact ⟨off, hh, hs, by simp [coinConfigRunAux, hc]⟩
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt (sideWorkTable M) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      exact ⟨off, hh, hs, by simp [coinConfigRunAux, hc]⟩
    · cases ht : Turing.TM0.step (sideWorkTable M c) cfg with
      | none =>
        have heq : cfg = final := Option.some.inj (by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, ht] using! hstop)
        subst final
        exact ⟨off, hh, hs, by simp [coinConfigRunAux, hc, ht]⟩
      | some next =>
        have hn : (coinConfigRunAux (sideWorkTable M) cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, ht] using! hstop
        obtain ⟨off₁, hm₁, hs₁, hd₁⟩ := sideWork_step_invariant M c cfg next off hh hs ht
        obtain ⟨off₂, hm₂, hs₂, hd₂⟩ := ih next off₁ hm₁ hs₁ hn
        refine ⟨off₂, hm₂, hs₂, ?_⟩
        simp only [coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, ht]
        omega

theorem sideAt_distance (left : Bool) (off : ℤ) (h : SideAt left off) :
    off = homeDistance left off.natAbs := by
  cases left with
  | false =>
    have hn : 0 ≤ off := by
      by_contra hn
      have hf := h.1 (by omega)
      cases hf
    simp [homeDistance, abs_of_nonneg hn]
  | true =>
    have hn : off ≤ 0 := by
      by_contra hn
      have hf := h.2 (by omega)
      cases hf
    simp [homeDistance, abs_of_nonpos hn]

theorem sideWork_homing_run {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (input : List Bool)
    (coins : List Bool) (final : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    (hstop : (coinConfigRunAux (sideWorkTable M) coins
      ⟨(default, false), markerCopyResult input⟩).stopped = some final) :
    ∃ (n : ℕ) (home : Turing.Tape MarkerCell),
      n ≤ (coinConfigRunAux (sideWorkTable M) coins
        ⟨(default, false), markerCopyResult input⟩).transitions ∧
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerHomeTable n
        ⟨(final.q.2, a final.q.1), final.Tape⟩ = some ⟨(final.q.2, a final.q.1), home⟩ ∧
      HomeAt home 0 ∧ Turing.TM0.step markerHomeTable ⟨(final.q.2, a final.q.1), home⟩ = none ∧
      ∀ i : ℤ, home.nth i = final.Tape.nth (i - homeDistance final.q.2 n) := by
  obtain ⟨off, hh, hs, hd⟩ := sideWork_coin_invariant M coins
    ⟨(default, false), markerCopyResult input⟩ final 0
    (markerCopyResult_home input) (by simp [SideAt]) hstop
  have heq := sideAt_distance final.q.2 off hs
  rw [heq] at hh
  obtain ⟨home, hr, hm, halt, data⟩ :=
      markerHome_run final.q.2 (a final.q.1) off.natAbs final.Tape hh
  exact ⟨off.natAbs, home, by simpa using! hd, hr, hm, halt, data⟩

theorem sideWork_step {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (cfg : Turing.TM0.Cfg MarkerCell (Λ × Bool)) :
    (Turing.TM0.step (sideWorkTable M c) cfg).map sideWorkCfg =
      Turing.TM0.step (M c) (sideWorkCfg cfg) := by
  simp only [TM0_step_apply, sideWorkTable, sideWorkCfg, Turing.Tape.map_fst]
  change (Option.map (fun p => ⟨p.1, TM0StmtApply cfg.Tape p.2⟩)
    (Option.map (fun p => match p.2 with
      | .move d => ((p.1, sideAfterMove cfg.q.2 cfg.Tape.head.2.2 d), Turing.TM0.Stmt.move d)
      | .write b => ((p.1, cfg.q.2), Turing.TM0.Stmt.write (cfg.Tape.head.1, b, cfg.Tape.head.2.2)))
      (M c cfg.q.1 cfg.Tape.head.2.1))).map sideWorkCfg =
      Option.map (fun p => ⟨p.1, TM0StmtApply (cfg.Tape.map workMap) p.2⟩)
        (M c cfg.q.1 cfg.Tape.head.2.1)
  cases ht : M c cfg.q.1 cfg.Tape.head.2.1 with
  | none => rfl
  | some p =>
    obtain ⟨q, stmt⟩ := p
    cases stmt with
    | move d => simp [sideWorkCfg, TM0StmtApply, Turing.Tape.map_move]
    | write b => simp [sideWorkCfg, TM0StmtApply, workMap]

theorem sideWork_coinHalt {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (cfg : Turing.TM0.Cfg MarkerCell (Λ × Bool)) :
    coinHalt (sideWorkTable M) cfg = coinHalt M (sideWorkCfg cfg) := by
  simp [coinHalt, sideWorkTable, sideWorkCfg, workMap]

theorem sideWork_coin_run {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (coins : List Bool) (cfg : Turing.TM0.Cfg MarkerCell (Λ × Bool)) :
    coinTapeRunAux (sideWorkTable M) (fun q => a q.1) coins cfg = coinTapeRunAux M a coins (sideWorkCfg cfg) ∧
    coinTapeTransitionCountAux (sideWorkTable M) coins cfg =
      coinTapeTransitionCountAux M coins (sideWorkCfg cfg) := by
  induction coins generalizing cfg with
  | nil =>
    simp only [coinTapeRunAux, coinTapeTransitionCountAux, sideWork_coinHalt]
    exact ⟨rfl, True.intro⟩
  | cons c cs ih =>
    by_cases hc : coinHalt (sideWorkTable M) cfg = true
    · have hc' : coinHalt M (sideWorkCfg cfg) = true := by rw [← sideWork_coinHalt]; exact hc
      simp only [coinTapeRunAux, coinTapeTransitionCountAux, hc, hc', ↓reduceIte]
      exact ⟨rfl, True.intro⟩
    · have hc' : coinHalt M (sideWorkCfg cfg) ≠ true := by rw [← sideWork_coinHalt]; exact hc
      have hstep := sideWork_step M c cfg
      cases hs : Turing.TM0.step (sideWorkTable M c) cfg with
      | none =>
        have hsource : Turing.TM0.step (M c) (sideWorkCfg cfg) = none := by rw [← hstep, hs]; rfl
        simp only [coinTapeRunAux, coinTapeTransitionCountAux, hc, hc', hs, hsource]
        exact ⟨rfl, True.intro⟩
      | some next =>
        have hsource : Turing.TM0.step (M c) (sideWorkCfg cfg) = some (sideWorkCfg next) := by
          rw [← hstep, hs]; rfl
        obtain ⟨ho, ht⟩ := ih next
        simp only [coinTapeRunAux, coinTapeTransitionCountAux, hc, hc', hs, hsource]
        rw [ho, ht]
        exact ⟨rfl, rfl⟩

theorem sideWork_commonHalt {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ q s, (sideWorkTable M false q s = none) ↔ (sideWorkTable M true q s = none) := by
  intro q s
  exact Option.map_eq_none_iff.trans ((hc q.1 s.2.1).trans Option.map_eq_none_iff.symm)

theorem sideWork_prepared_run {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (input : List Bool) (coins : List Bool) :
    coinTapeRunAux (sideWorkTable M) (fun q => a q.1) coins
      ⟨(default, false), markerCopyResult input⟩ = coinTapeRun M a (input.map some) coins ∧
    coinTapeTransitionCountAux (sideWorkTable M) coins
      ⟨(default, false), markerCopyResult input⟩ = coinTapeTransitionCount M (input.map some) coins := by
  have h := sideWork_coin_run M a coins ⟨(default, false), markerCopyResult input⟩
  have hc : sideWorkCfg (⟨(default, false), markerCopyResult input⟩ :
      Turing.TM0.Cfg MarkerCell (Λ × Bool)) = Turing.TM0.init (input.map some) := by
    simp [sideWorkCfg, markerCopyResult_work, Turing.TM0.init]
  rw [hc] at h
  exact h

theorem dispatch_left_step {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Turing.TM0.Machine Γ Μ)
    (cfg next : Turing.TM0.Cfg Γ Λ) (hs : Turing.TM0.step M₁ cfg = some next) :
    Turing.TM0.step (dispatchTable M₁ nextLabel M₂) (mapCfg Sum.inl cfg) =
      some (mapCfg Sum.inl next) := by
  cases ht : M₁ cfg.q cfg.Tape.head with
  | none => simp [TM0_step_apply, ht] at hs
  | some p =>
    rw [TM0_step_apply, ht] at hs
    cases hs
    simp [TM0_step_apply, dispatchTable, mapCfg, ht]

theorem dispatch_right_step {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Μ) :
    Turing.TM0.step (dispatchTable M₁ nextLabel M₂) (mapCfg Sum.inr cfg) =
      (Turing.TM0.step M₂ cfg).map (mapCfg Sum.inr) := by
  simp only [TM0_step_apply, dispatchTable, mapCfg, Option.map_map, Function.comp_def]

theorem dispatch_step {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Λ) (hh : Turing.TM0.step M₁ cfg = none) :
    Turing.TM0.step (dispatchTable M₁ nextLabel M₂) (mapCfg Sum.inl cfg) =
      some ⟨Sum.inr (nextLabel cfg.q), cfg.Tape⟩ := by
  have ht := (TM0_step_eq_none M₁ cfg).mp hh
  simp [TM0_step_apply, dispatchTable, mapCfg, ht, TM0StmtApply]

theorem dispatch_coinHalt_right {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Μ) :
    coinHalt (dispatchCoinTable M₁ nextLabel M₂) (mapCfg Sum.inr cfg) = coinHalt M₂ cfg := by
  simp [coinHalt, dispatchCoinTable, dispatchTable, mapCfg]

theorem dispatch_coinHalt_left {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (cfg : Turing.TM0.Cfg Γ Λ) :
    coinHalt (dispatchCoinTable M₁ nextLabel M₂) (mapCfg Sum.inl cfg) = false := by
  cases hf : M₁ false cfg.q cfg.Tape.head <;>
    cases ht : M₁ true cfg.q cfg.Tape.head <;>
      simp [coinHalt, dispatchCoinTable, dispatchTable, mapCfg, hf, ht]

theorem dispatch_coinConfig_right {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Μ) :
    coinConfigRunAux (dispatchCoinTable M₁ nextLabel M₂) coins (mapCfg Sum.inr cfg) =
      let r := coinConfigRunAux M₂ coins cfg
      ⟨r.stopped.map (mapCfg Sum.inr), r.reads, r.transitions⟩ := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M₂ cfg = true <;>
      simp [coinConfigRunAux, dispatch_coinHalt_right, hc]
  | cons c cs ih =>
    by_cases hc : coinHalt M₂ cfg = true
    · simp [coinConfigRunAux, dispatch_coinHalt_right, hc]
    · have hs := dispatch_right_step (M₁ c) nextLabel (M₂ c) cfg
      change Turing.TM0.step (dispatchCoinTable M₁ nextLabel M₂ c) (mapCfg Sum.inr cfg) = _ at hs
      simp only [coinConfigRunAux, dispatch_coinHalt_right, hc, Bool.false_eq_true, ↓reduceIte, hs]
      cases ht : Turing.TM0.step (M₂ c) cfg with
      | none => rfl
      | some next => simp [ih]

theorem dispatchCoinTable_commonHalt {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (hc : ∀ q s, (M₂ false q s = none) ↔ (M₂ true q s = none)) :
    ∀ q s, (dispatchCoinTable M₁ nextLabel M₂ false q s = none) ↔
      (dispatchCoinTable M₁ nextLabel M₂ true q s = none) := by
  intro q s
  cases q with
  | inl q =>
    cases hf : M₁ false q s <;> cases ht : M₁ true q s <;>
      simp [dispatchCoinTable, dispatchTable, hf, ht]
  | inr q =>
    exact Option.map_eq_none_iff.trans ((hc q s).trans Option.map_eq_none_iff.symm)

theorem dispatch_coinConfig_left {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (nextLabel : Λ → Μ) (M₂ : Bool → Turing.TM0.Machine Γ Μ)
    (hcommon : ∀ q s, (M₁ false q s = none) ↔ (M₁ true q s = none))
    (front tail : List Bool) (switch : Bool) (cfg final : Turing.TM0.Cfg Γ Λ)
    (hstop : (coinConfigRunAux M₁ front cfg).stopped = some final)
    (hread : (coinConfigRunAux M₁ front cfg).reads = front.length) :
    let r := coinConfigRunAux M₂ tail ⟨nextLabel final.q, final.Tape⟩
    let total := coinConfigRunAux (dispatchCoinTable M₁ nextLabel M₂)
      (front ++ switch :: tail) (mapCfg Sum.inl cfg)
    total.stopped = r.stopped.map (mapCfg Sum.inr) ∧
      total.reads = r.reads + front.length + 1 ∧
      total.transitions = r.transitions + front.length + 1 := by
  induction front generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M₁ cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      have hd := dispatch_step (M₁ switch) nextLabel (M₂ switch) cfg
        (coinHalt_step_none M₁ cfg hc switch)
      change Turing.TM0.step (dispatchCoinTable M₁ nextLabel M₂ switch)
          (mapCfg Sum.inl cfg) = _ at hd
      have hr := dispatch_coinConfig_right M₁ nextLabel M₂ tail
        (⟨nextLabel cfg.q, cfg.Tape⟩ : Turing.TM0.Cfg Γ Μ)
      change coinConfigRunAux (dispatchCoinTable M₁ nextLabel M₂) tail
        ⟨Sum.inr (nextLabel cfg.q), cfg.Tape⟩ = _ at hr
      (try dsimp only)
      simp only [List.nil_append, List.length_nil, coinConfigRunAux, dispatch_coinHalt_left,
        Bool.false_eq_true, ↓reduceIte, hd]
      rw [hr]
      simp
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt M₁ cfg = true
    · simp [coinConfigRunAux, hc] at hread
    · cases hs : Turing.TM0.step (M₁ c) cfg with
      | none => exact (hc (step_none_common_halt M₁ hcommon c cfg hs)).elim
      | some next =>
        have hstop' : (coinConfigRunAux M₁ cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, hs] using! hstop
        have hread' : (coinConfigRunAux M₁ cs next).reads = cs.length := by
          have h := hread
          simp only [coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, hs,
              List.length_cons] at h
          exact Nat.succ.inj h
        have hp := dispatch_left_step (M₁ c) nextLabel (M₂ c) cfg next hs
        change Turing.TM0.step (dispatchCoinTable M₁ nextLabel M₂ c) (mapCfg Sum.inl cfg) = _ at hp
        obtain ⟨ho, hr, ht⟩ := ih next hstop' hread'
        (try dsimp only)
        simp only [List.cons_append, List.length_cons, coinConfigRunAux, dispatch_coinHalt_left,
          Bool.false_eq_true, ↓reduceIte, hp]
        constructor
        · exact ho
        · constructor
          · rw [hr]
            omega
          · rw [ht]
            omega

theorem homingCoinTable_commonHalt {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) :
    ∀ q s, (homingCoinTable M a false q s = none) ↔
      (homingCoinTable M a true q s = none) :=
  dispatchCoinTable_commonHalt _ _ _ (fun _ _ => Iff.rfl)

theorem homing_coinConfig_run {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (front : List Bool) (switch : Bool)
    (final : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    (hstop : (coinConfigRunAux (sideWorkTable M) front
      ⟨(default, false), markerCopyResult input⟩).stopped = some final)
    (hread : (coinConfigRunAux (sideWorkTable M) front
      ⟨(default, false), markerCopyResult input⟩).reads = front.length) :
    ∃ (n : ℕ) (home : Turing.Tape MarkerCell), n ≤ front.length ∧ HomeAt home 0 ∧
      ∀ tail : List Bool, n ≤ tail.length →
        let total := coinConfigRunAux (homingCoinTable M a) (front ++ switch :: tail)
          ⟨Sum.inl (default, false), markerCopyResult input⟩
        total.stopped = some ⟨Sum.inr (final.q.2, a final.q.1), home⟩ ∧
        total.reads = front.length + 1 + n ∧
        total.transitions = front.length + 1 + n ∧
        total.stopped.map (fun cfg => homingAccept cfg.q) = some (a final.q.1) := by
  obtain ⟨n, home, hn, hr, hm, hh, _⟩ := sideWork_homing_run M a input front final hstop
  have hledger := (coinConfigRunAux_commonHalt (sideWorkTable M) (sideWork_commonHalt M hc)
    front (⟨(default, false), markerCopyResult input⟩ : Turing.TM0.Cfg MarkerCell (Λ × Bool))).1
  rw [hledger, hread] at hn
  refine ⟨n, home, hn, hm, ?_⟩
  intro tail hlen
  have hhome := coinConfigRunAux_const markerHomeTable n
    ⟨(final.q.2, a final.q.1), final.Tape⟩ ⟨(final.q.2, a final.q.1), home⟩ tail hr hh hlen
  have h := dispatch_coinConfig_left (sideWorkTable M) (fun q => (q.2, a q.1))
    (fun _ => markerHomeTable) (sideWork_commonHalt M hc) front tail switch
    ⟨(default, false), markerCopyResult input⟩ final hstop hread
  dsimp only at h
  change (coinConfigRunAux (homingCoinTable M a) (front ++ switch :: tail)
    ⟨Sum.inl (default, false), markerCopyResult input⟩).stopped = _ ∧ _ at h
  obtain ⟨hs, hrd, htr⟩ := h
  rw [hhome.1] at hs
  rw [hhome.2.1] at hrd
  rw [hhome.2.2] at htr
  change (coinConfigRunAux (homingCoinTable M a) (front ++ switch :: tail)
    ⟨Sum.inl (default, false), markerCopyResult input⟩).reads = n + front.length + 1 at hrd
  change (coinConfigRunAux (homingCoinTable M a) (front ++ switch :: tail)
    ⟨Sum.inl (default, false), markerCopyResult input⟩).transitions = n + front.length + 1 at htr
  (try dsimp only)
  refine ⟨hs, by omega, by omega, ?_⟩
  rw [hs]
  rfl

theorem homing_coinConfig_budget {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (coins : List Bool) (t : ℕ) (hlen : 2 * t + 1 ≤ coins.length)
    (final : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    (hstop : (coinConfigRunAux (sideWorkTable M) (coins.take t)
      ⟨(default, false), markerCopyResult input⟩).stopped = some final) :
    ∃ home : Turing.Tape MarkerCell, HomeAt home 0 ∧
      let total := coinConfigRunAux (homingCoinTable M a) coins
        ⟨Sum.inl (default, false), markerCopyResult input⟩
      total.stopped = some ⟨Sum.inr (final.q.2, a final.q.1), home⟩ ∧
      total.reads ≤ 2 * t + 1 ∧ total.transitions = total.reads ∧
      total.stopped.map (fun cfg => homingAccept cfg.q) = some (a final.q.1) := by
  let cfg : Turing.TM0.Cfg MarkerCell (Λ × Bool) :=
    ⟨(default, false), markerCopyResult input⟩
  let k := (coinConfigRunAux (sideWorkTable M) (coins.take t) cfg).reads
  have hkt : k ≤ t := (coinConfigRunAux_reads_le (sideWorkTable M) (coins.take t) cfg).trans
    (List.length_take_le t coins)
  have hklen : k ≤ coins.length := by omega
  have htake := coinConfigRunAux_take (sideWorkTable M) (coins.take t) cfg
    (by rw [hstop]; exact Option.some_ne_none final)
  change coinConfigRunAux (sideWorkTable M) ((coins.take t).take k) cfg = _ at htake
  rw [List.take_take, min_eq_left hkt] at htake
  have hpstop : (coinConfigRunAux (sideWorkTable M) (coins.take k) cfg).stopped = some final := by
    rw [htake]; exact hstop
  have hpread : (coinConfigRunAux (sideWorkTable M) (coins.take k) cfg).reads =
      (coins.take k).length := by
    rw [htake, List.length_take, min_eq_left hklen]
  have hdropLen : (coins.drop k).length = coins.length - k := List.length_drop
  cases hd : coins.drop k with
  | nil => simp only [hd, List.length_nil] at hdropLen; omega
  | cons switch tail =>
    have hsplit : coins = coins.take k ++ switch :: tail := by
      rw [← hd, List.take_append_drop]
    have htail : k ≤ tail.length := by
      simp only [hd, List.length_cons] at hdropLen
      omega
    obtain ⟨n, home, hn, hm, hrun⟩ := homing_coinConfig_run M a hc input (coins.take k)
      switch final hpstop hpread
    have hn' : n ≤ k := by simpa [List.length_take, min_eq_left hklen] using! hn
    have h := hrun tail (by omega)
    rw [← hsplit] at h
    obtain ⟨hs, hr, ht, ho⟩ := h
    refine ⟨home, hm, hs, ?_, ?_, ho⟩
    · (try dsimp only)
      rw [hr, List.length_take, min_eq_left hklen]
      omega
    · (try dsimp only)
      rw [hr, ht]

theorem relabel_coinConfig {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ']
    (e : Λ ≃ Λ') (M : Bool → Turing.TM0.Machine Γ Λ) (coins : List Bool)
    (cfg : Turing.TM0.Cfg Γ Λ) :
    coinConfigRunAux (relabelTable e M) coins (relabelCfg e cfg) =
      let r := coinConfigRunAux M coins cfg
      ⟨r.stopped.map (relabelCfg e), r.reads, r.transitions⟩ := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M cfg = true <;>
      simp [coinConfigRunAux, relabel_coinHalt, hc]
  | cons c cs ih =>
    by_cases hc : coinHalt M cfg = true
    · simp [coinConfigRunAux, relabel_coinHalt, hc]
    · simp only [coinConfigRunAux, relabel_coinHalt, hc, Bool.false_eq_true,
        ↓reduceIte, relabel_step]
      cases ht : Turing.TM0.step (M c) cfg with
      | none => rfl
      | some next => simp [ih]

theorem homingLabels_zero (Q : ℕ) : homingLabels Q (.inl (0, false)) = 0 := by
  apply Fin.ext
  simp [homingLabels, Equiv.prodCongr, finTwoEquiv, finProdFinEquiv, finSumFinEquiv]

theorem nativeHoming_initial (Q : ℕ) (T : Turing.Tape MarkerCell) :
    relabelCfg (homingLabels Q)
      (⟨Sum.inl (0, false), T⟩ : Turing.TM0.Cfg MarkerCell
        (Sum (Fin (Q + 1) × Bool) HomeState)) = ⟨0, T⟩ := by
  simp [relabelCfg, homingLabels_zero]

theorem nativeHoming_coinConfig_budget (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (coins : List Bool) (t : ℕ) (hlen : 2 * t + 1 ≤ coins.length)
    (final : Turing.TM0.Cfg MarkerCell (Fin (Q + 1) × Bool))
    (hstop : (coinConfigRunAux (sideWorkTable M) (coins.take t)
      ⟨(0, false), markerCopyResult input⟩).stopped = some final) :
    ∃ home : Turing.Tape MarkerCell, HomeAt home 0 ∧
      let total := coinConfigRunAux (nativeHomingCoinTable Q M a) coins
        ⟨0, markerCopyResult input⟩
      total.stopped = some ⟨homingLabels Q (.inr (final.q.2, a final.q.1)), home⟩ ∧
      total.reads ≤ 2 * t + 1 ∧ total.transitions = total.reads ∧
      total.stopped.map (fun cfg => nativeHomingAccept Q cfg.q) = some (a final.q.1) := by
  obtain ⟨home, hm, hs, hr, ht, ho⟩ :=
      homing_coinConfig_budget M a hc input coins t hlen final hstop
  simp only [Fin.default_eq_zero] at hs hr ht ho
  have he := relabel_coinConfig (homingLabels Q) (homingCoinTable M a) coins
    (⟨Sum.inl (0, false), markerCopyResult input⟩ : Turing.TM0.Cfg MarkerCell
      (Sum (Fin (Q + 1) × Bool) HomeState))
  rw [nativeHoming_initial] at he
  change coinConfigRunAux (nativeHomingCoinTable Q M a) coins
    ⟨0, markerCopyResult input⟩ = _ at he
  refine ⟨home, hm, ?_⟩
  (try dsimp only)
  rw [he]
  (try dsimp only)
  refine ⟨?_, hr, ht, ?_⟩
  · rw [hs]
    rfl
  · rw [hs]
    simp [relabelCfg, nativeHomingAccept, homingAccept]

theorem nativeHoming_commonHalt (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    ∀ q s, (nativeHomingCoinTable Q M a false q s = none) ↔
      (nativeHomingCoinTable Q M a true q s = none) := by
  intro q s
  have h := homingCoinTable_commonHalt M a ((homingLabels Q).symm q) s
  exact Option.map_eq_none_iff.trans (h.trans Option.map_eq_none_iff.symm)

theorem nativeHoming_source_output (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (coins : List Bool) (t : ℕ) (hlen : 2 * t + 1 ≤ coins.length)
    (htotal : (coinTapeRun M a (input.map some) (coins.take t)).1 ≠ none) :
    (coinTapeRunAux (nativeHomingCoinTable Q M a) (nativeHomingAccept Q) coins
        ⟨0, markerCopyResult input⟩).1 =
      (coinTapeRun M a (input.map some) (coins.take t)).1 ∧
    ∃ (q : Fin (2 * Q + 6)) (home : Turing.Tape MarkerCell), HomeAt home 0 ∧
      let total := coinConfigRunAux (nativeHomingCoinTable Q M a) coins
        ⟨0, markerCopyResult input⟩
      total.stopped = some ⟨q, home⟩ ∧ total.reads ≤ 2 * t + 1 ∧
      total.transitions = total.reads := by
  let cfg : Turing.TM0.Cfg MarkerCell (Fin (Q + 1) × Bool) :=
    ⟨(0, false), markerCopyResult input⟩
  have hreadout := congrArg Prod.fst
    (coinConfigRunAux_readout (sideWorkTable M) (fun q => a q.1) (coins.take t) cfg).1
  change (coinConfigRunAux (sideWorkTable M) (coins.take t) cfg).stopped.map (fun q => a q.q.1) = _
    at hreadout
  have hsource := congrArg Prod.fst (sideWork_prepared_run M a input (coins.take t)).1
  simp only [Fin.default_eq_zero] at hsource
  change (coinTapeRunAux (sideWorkTable M) (fun q => a q.1) (coins.take t) cfg).1 = _ at hsource
  rw [hsource] at hreadout
  cases hs : (coinConfigRunAux (sideWorkTable M) (coins.take t) cfg).stopped with
  | none =>
    rw [hs] at hreadout
    exact (htotal hreadout.symm).elim
  | some final =>
    have hout : some (a final.q.1) = (coinTapeRun M a (input.map some) (coins.take t)).1 := by
      simpa only [hs, Option.map_some] using! hreadout
    obtain ⟨home, hm, hstop, hr, ht, ho⟩ := nativeHoming_coinConfig_budget Q M a hc input coins t
      hlen final hs
    have hn := congrArg Prod.fst (coinConfigRunAux_readout (nativeHomingCoinTable Q M a)
      (nativeHomingAccept Q) coins ⟨0, markerCopyResult input⟩).1
    change (coinConfigRunAux (nativeHomingCoinTable Q M a) coins
      ⟨0, markerCopyResult input⟩).stopped.map (fun q => nativeHomingAccept Q q.q) = _ at hn
    constructor
    · exact hn.symm.trans (ho.trans hout)
    · exact ⟨homingLabels Q (.inr (final.q.2, a final.q.1)), home, hm, hstop, hr, ht⟩

theorem prepareHomingLabels_zero (Q : ℕ) : prepareHomingLabels Q (.inl 0) = 0 := by
  apply Fin.ext
  simp [prepareHomingLabels, finSumFinEquiv]

theorem prepareHoming_initial (Q : ℕ) (input : List Bool) :
    relabelCfg (prepareHomingLabels Q)
      (mapCfg Sum.inl (Turing.TM0.init (markerInput input))) =
        Turing.TM0.init (markerInput input) := by
  change (⟨prepareHomingLabels Q (.inl 0), Turing.Tape.mk₁ (markerInput input)⟩ :
    Turing.TM0.Cfg MarkerCell (Fin (2 * Q + 11))) = _
  rw [prepareHomingLabels_zero]
  rfl

theorem prepareHoming_commonHalt (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    ∀ q s, (prepareHomingCoinTable Q M a false q s = none) ↔
      (prepareHomingCoinTable Q M a true q s = none) := by
  intro q s
  have h := sequenceCoinTable_commonHalt (fun _ => markerCopyTable) (nativeHomingCoinTable Q M a)
    (nativeHoming_commonHalt Q M a) ((prepareHomingLabels Q).symm q) s
  exact Option.map_eq_none_iff.trans (h.trans Option.map_eq_none_iff.symm)

theorem prepareHoming_source_output (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (front : Fin (3 * input.length + 3) → Bool) (switch : Bool)
    (tail : List Bool) (t : ℕ) (hlen : 2 * t + 1 ≤ tail.length)
    (htotal : (coinTapeRun M a (input.map some) (tail.take t)).1 ≠ none) :
    (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input)
      (List.ofFn front ++ switch :: tail)).1 =
      (coinTapeRun M a (input.map some) (tail.take t)).1 ∧
    ∃ (q : Fin (2 * Q + 11)) (home : Turing.Tape MarkerCell), HomeAt home 0 ∧
      let total := coinConfigRunAux (prepareHomingCoinTable Q M a)
        (List.ofFn front ++ switch :: tail) (Turing.TM0.init (markerInput input))
      total.stopped = some ⟨q, home⟩ ∧ total.reads ≤ 3 * input.length + 2 * t + 5 ∧
      total.transitions = total.reads := by
  obtain ⟨ho, q, home, hm, hs, hr, ht⟩ :=
      nativeHoming_source_output Q M a hc input tail t hlen htotal
  let seq := sequenceCoinTable (fun _ => markerCopyTable) (nativeHomingCoinTable Q M a)
  let coins := List.ofFn front ++ switch :: tail
  let cfg : Turing.TM0.Cfg MarkerCell (Fin 5) := Turing.TM0.init (markerInput input)
  have hp := markerCopy_then_coin_source (nativeHomingCoinTable Q M a) input front switch tail
  simp only [Fin.default_eq_zero] at hp
  have he := relabel_coinConfig (prepareHomingLabels Q) seq coins (mapCfg Sum.inl cfg)
  rw [prepareHoming_initial] at he
  change coinConfigRunAux (prepareHomingCoinTable Q M a) coins
    (Turing.TM0.init (markerInput input)) = _ at he
  have hpstop := hp.1
  rw [hs] at hpstop
  have hfinal : (coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))).stopped =
      some ⟨prepareHomingLabels Q (.inr q), home⟩ := by
    rw [he]
    change (coinConfigRunAux seq coins (mapCfg Sum.inl cfg)).stopped.map _ = _
    change (coinConfigRunAux seq coins (mapCfg Sum.inl cfg)).stopped = _ at hpstop
    rw [hpstop]
    rfl
  have hread : (coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))).reads =
      (coinConfigRunAux (nativeHomingCoinTable Q M a) tail ⟨0, markerCopyResult input⟩).reads +
        (3 * input.length + 4) := by
    rw [he]
    exact hp.2.1
  have htrans : (coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))).transitions =
      (coinConfigRunAux (nativeHomingCoinTable Q M a) tail ⟨0, markerCopyResult input⟩).transitions +
        (3 * input.length + 4) := by
    rw [he]
    exact hp.2.2
  constructor
  · have hn := congrArg Prod.fst (coinConfigRunAux_readout (nativeHomingCoinTable Q M a)
      (nativeHomingAccept Q) tail ⟨0, markerCopyResult input⟩).1
    change (coinConfigRunAux (nativeHomingCoinTable Q M a) tail
      ⟨0, markerCopyResult input⟩).stopped.map (fun cfg => nativeHomingAccept Q cfg.q) = _ at hn
    rw [hs] at hn
    have hreadout := congrArg Prod.fst (coinConfigRunAux_readout (prepareHomingCoinTable Q M a)
      (prepareHomingAccept Q) coins (Turing.TM0.init (markerInput input))).1
    change (coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))).stopped.map (fun cfg => prepareHomingAccept Q cfg.q) = _
      at hreadout
    rw [hfinal] at hreadout
    have hbit : some (nativeHomingAccept Q q) =
        (coinTapeRun M a (input.map some) (tail.take t)).1 := hn.trans ho
    exact hreadout.symm.trans (by
      simpa [prepareHomingAccept, sourcePhaseAccept] using! hbit)
  · refine ⟨prepareHomingLabels Q (.inr q), home, hm, hfinal, ?_, ?_⟩
    · (try dsimp only)
      rw [hread]
      omega
    · (try dsimp only)
      rw [htrans, hread, ht]

theorem homingCoinWords_ofFn (input : List Bool) (t : ℕ)
    (p : (Fin (3 * input.length + 3) → Bool) × Bool ×
      ((Fin t → Bool) × (Fin (t + 1) → Bool))) :
    List.ofFn (homingCoinWords input t p) =
      List.ofFn p.1 ++ p.2.1 :: (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2) := by
  change List.ofFn (prepareCoinWords input (t + (t + 1))
    (p.1, p.2.1, appendCoinWords t (t + 1) p.2.2)) = _
  rw [prepareCoinWords_ofFn]
  rw [show List.ofFn (appendCoinWords t (t + 1) p.2.2) =
    List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2 from List.ofFn_fin_append _ _]

theorem prepareHoming_word_output (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (p : (Fin (3 * input.length + 3) → Bool) × Bool ×
      ((Fin t → Bool) × (Fin (t + 1) → Bool))) :
      (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input)
        (List.ofFn (homingCoinWords input t p))).1 =
        (coinTapeRun M a (input.map some) (List.ofFn p.2.2.1)).1 := by
  rw [homingCoinWords_ofFn]
  have htake : (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2).take t = List.ofFn p.2.2.1 := by simp
  have h := (prepareHoming_source_output Q M a hc input p.1 p.2.1
    (List.ofFn p.2.2.1 ++ List.ofFn p.2.2.2) t (by simp; omega)
    (by rw [htake]; exact ht _)).1
  rw [htake] at h
  exact h

theorem prepareHoming_fair_mass (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ) (target : Bool)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) :
    fairTapeSuccess (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input)
        ((3 * input.length + 3) + ((t + (t + 1)) + 1)) target =
      fairTapeSuccess M a (input.map some) t target := by
  have hp := prepareHoming_word_output Q M a hc input t ht
  have hj (w : Fin t → Bool) :
      (∑ _junk : Fin (t + 1) → Bool,
        if (coinTapeRun M a (input.map some) (List.ofFn w)).1 = some target then (1 : ℝ) else 0) =
      2 ^ (t + 1) *
        (if (coinTapeRun M a (input.map some) (List.ofFn w)).1 = some target then (1 : ℝ) else 0) := by
    by_cases h : (coinTapeRun M a (input.map some) (List.ofFn w)).1 = some target <;> simp [h]
  have hs : (∑ w : Fin ((3 * input.length + 3) + ((t + (t + 1)) + 1)) → Bool,
      if (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input)
        (List.ofFn w)).1 = some target then (1 : ℝ) else 0) =
      (2 : ℝ) ^ (3 * input.length + 3) * 2 * 2 ^ (t + 1) *
      (∑ w : Fin t → Bool,
        if (coinTapeRun M a (input.map some) (List.ofFn w)).1 = some target then (1 : ℝ) else 0) := by
    rw [← (homingCoinWords input t).sum_comp]
    simp_rw [hp]
    simp only [Fintype.sum_prod_type]
    simp_rw [hj]
    rw [← Finset.mul_sum]
    simp [mul_assoc]
  unfold fairTapeSuccess
  rw [hs, pow_add (2 : ℝ) (3 * input.length + 3) ((t + (t + 1)) + 1),
    pow_succ (2 : ℝ) (t + (t + 1)), pow_add (2 : ℝ) t (t + 1)]
  have hk : (2 : ℝ) ^ (3 * input.length + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht' : (2 : ℝ) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (2 : ℝ) ^ (t + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hk, ht', he]

theorem prepareHoming_total (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) :
    ∀ w : Fin ((3 * input.length + 3) + ((t + (t + 1)) + 1)) → Bool,
      (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input)
        (List.ofFn w)).1 ≠ none := by
  intro w
  have h := prepareHoming_word_output Q M a hc input t ht ((homingCoinWords input t).symm w)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact ht _

theorem prepareHoming_poly_bound (c k n : ℕ) :
    (3 * n + 3) + (((c * n ^ k + c) + ((c * n ^ k + c) + 1)) + 1) ≤
      (4 * c + 9) * n ^ (2 * (k + 1)) + (4 * c + 9) := by
  have h := prepare_poly_bound (2 * c) k n
  nlinarith [Nat.zero_le (n ^ (2 * (k + 1)))]

theorem prepareHoming_polynomial (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (c k : ℕ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (htotal : ∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
      (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q s, (prepareHomingCoinTable Q M a false q s = none) ↔
        (prepareHomingCoinTable Q M a true q s = none)) ∧
      ∀ input : List Bool,
        let T := c * input.length ^ k + c
        let B := d * input.length ^ (2 * (k + 1)) + d
        (∀ w : Fin B → Bool,
          (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input)
            (List.ofFn w)).1 ≠ none) ∧
        (∀ w : Fin B → Bool,
          coinTapeTransitionCount (prepareHomingCoinTable Q M a) (markerInput input) (List.ofFn w) ≤ B) ∧
        (∀ target : Bool,
          fairTapeSuccess (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input) B target =
            fairTapeSuccess M a (input.map some) T target) := by
  refine ⟨4 * c + 9, by omega, prepareHoming_commonHalt Q M a, ?_⟩
  intro input
  let T := c * input.length ^ k + c
  let N := (3 * input.length + 3) + ((T + (T + 1)) + 1)
  let B := (4 * c + 9) * input.length ^ (2 * (k + 1)) + (4 * c + 9)
  have hn := prepareHoming_total Q M a hc input T (htotal input)
  have hnb : N ≤ B := prepareHoming_poly_bound c k input.length
  refine ⟨coinTape_totality_monotone (prepareHomingCoinTable Q M a) (prepareHomingAccept Q)
    (markerInput input) N hn B hnb, ?_, ?_⟩
  · intro w
    have hr := coinTapeRunAux_snd_le (prepareHomingCoinTable Q M a) (prepareHomingAccept Q)
      (List.ofFn w) (Turing.TM0.init (markerInput input))
    have ht := coinTapeTransitionCount_le_reads (prepareHomingCoinTable Q M a) (prepareHomingAccept Q)
      (markerInput input) (List.ofFn w)
    exact ht.trans (by simpa only [coinTapeRun, List.length_ofFn] using! hr)
  · intro target
    exact (fairTapeSuccess_of_total (prepareHomingCoinTable Q M a) (prepareHomingAccept Q)
      (markerInput input) N hn B hnb target).trans
        (prepareHoming_fair_mass Q M a hc input T target (htotal input))

theorem protectedAt_move_left (initial T : Turing.Tape MarkerCell) (off : ℤ)
    (h : ProtectedAt initial T off) : ProtectedAt initial (T.move .left) (off - 1) := by
  refine ⟨homeAt_move_left T off h.1, ?_⟩
  intro i
  rw [Turing.Tape.move_left_nth, h.2]
  congr 2
  omega

theorem protectedAt_move_right (initial T : Turing.Tape MarkerCell) (off : ℤ)
    (h : ProtectedAt initial T off) : ProtectedAt initial (T.move .right) (off + 1) := by
  refine ⟨homeAt_move_right T off h.1, ?_⟩
  intro i
  rw [Turing.Tape.move_right_nth, h.2]
  congr 2
  omega

theorem protectedAt_write_work (initial T : Turing.Tape MarkerCell) (off : ℤ)
    (b : Option Bool) (h : ProtectedAt initial T off) :
    ProtectedAt initial (T.write (T.head.1, b, T.head.2.2)) off := by
  refine ⟨homeAt_write_work T off b h.1, ?_⟩
  intro i
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · subst i
    simp only [↓reduceIte, Int.zero_add]
    simpa using! h.2 0
  · simpa only [hi, ↓reduceIte] using! h.2 i

theorem sideWork_step_protected {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool)
    (cfg next : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    (initial : Turing.Tape MarkerCell) (off : ℤ)
    (h : ProtectedAt initial cfg.Tape off)
    (hs : Turing.TM0.step (sideWorkTable M c) cfg = some next) :
    ∃ off' : ℤ, ProtectedAt initial next.Tape off' := by
  cases ht : M c cfg.q.1 cfg.Tape.head.2.1 with
  | none => simp [TM0_step_apply, sideWorkTable, ht] at hs
  | some p =>
    obtain ⟨q, stmt⟩ := p
    cases stmt with
    | write b =>
      have he : Turing.TM0.step (sideWorkTable M c) cfg =
          some ⟨(q, cfg.q.2), cfg.Tape.write (cfg.Tape.head.1, b, cfg.Tape.head.2.2)⟩ := by
        simp [TM0_step_apply, sideWorkTable, ht, TM0StmtApply]
      rw [he] at hs
      cases hs
      exact ⟨off, protectedAt_write_work initial cfg.Tape off b h⟩
    | move d =>
      have he : Turing.TM0.step (sideWorkTable M c) cfg =
          some ⟨(q, sideAfterMove cfg.q.2 cfg.Tape.head.2.2 d), cfg.Tape.move d⟩ := by
        simp [TM0_step_apply, sideWorkTable, ht, TM0StmtApply]
      rw [he] at hs
      cases hs
      cases d with
      | left => exact ⟨off - 1, protectedAt_move_left initial cfg.Tape off h⟩
      | right => exact ⟨off + 1, protectedAt_move_right initial cfg.Tape off h⟩

theorem sideWork_coin_protected {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (coins : List Bool)
    (cfg final : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    (initial : Turing.Tape MarkerCell) (off : ℤ)
    (h : ProtectedAt initial cfg.Tape off)
    (hstop : (coinConfigRunAux (sideWorkTable M) coins cfg).stopped = some final) :
    ∃ off' : ℤ, ProtectedAt initial final.Tape off' := by
  induction coins generalizing cfg off with
  | nil =>
    by_cases hc : coinHalt (sideWorkTable M) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      exact ⟨off, h⟩
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt (sideWorkTable M) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      exact ⟨off, h⟩
    · cases ht : Turing.TM0.step (sideWorkTable M c) cfg with
      | none =>
        have heq : cfg = final := Option.some.inj (by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, ht] using! hstop)
        subst final
        exact ⟨off, h⟩
      | some next =>
        have hn : (coinConfigRunAux (sideWorkTable M) cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, ht] using! hstop
        obtain ⟨off', h'⟩ := sideWork_step_protected M c cfg next initial off h ht
        exact ih next off' h' hn

theorem homeAt_offset_unique (T : Turing.Tape MarkerCell) (off off' : ℤ)
    (h : HomeAt T off) (h' : HomeAt T off') : off = off' := by
  have hh := h (-off)
  have hh' := h' (-off)
  rw [hh] at hh'
  have he : -off + off' = 0 := by simpa using! hh'.symm
  omega

theorem sideWork_homing_protected_run {Λ : Type} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (input : List Bool)
    (coins : List Bool) (final : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    (hstop : (coinConfigRunAux (sideWorkTable M) coins
      ⟨(default, false), markerCopyResult input⟩).stopped = some final) :
    ∃ (n : ℕ) (home : Turing.Tape MarkerCell),
      n ≤ (coinConfigRunAux (sideWorkTable M) coins
        ⟨(default, false), markerCopyResult input⟩).transitions ∧
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom markerHomeTable n
        ⟨(final.q.2, a final.q.1), final.Tape⟩ = some ⟨(final.q.2, a final.q.1), home⟩ ∧
      ProtectedAt (markerCopyResult input) home 0 ∧
      Turing.TM0.step markerHomeTable ⟨(final.q.2, a final.q.1), home⟩ = none ∧
      ∀ i : ℤ, home.nth i = final.Tape.nth (i - homeDistance final.q.2 n) := by
  obtain ⟨off, hh, hs, hd⟩ := sideWork_coin_invariant M coins
    ⟨(default, false), markerCopyResult input⟩ final 0
    (markerCopyResult_home input) (by simp [SideAt]) hstop
  obtain ⟨off', hp⟩ := sideWork_coin_protected M coins
    ⟨(default, false), markerCopyResult input⟩ final (markerCopyResult input) 0
    ⟨markerCopyResult_home input, by intro i; simp⟩ hstop
  have heq : off' = off := homeAt_offset_unique final.Tape off' off hp.1 hh
  subst off'
  have hdist := sideAt_distance final.q.2 off hs
  rw [hdist] at hh
  obtain ⟨home, hr, hm, halt, data⟩ :=
      markerHome_run final.q.2 (a final.q.1) off.natAbs final.Tape hh
  refine ⟨off.natAbs, home, by simpa using! hd, hr, ⟨hm, ?_⟩, halt, data⟩
  intro i
  rw [data, hp.2]
  simp only [Int.add_zero]
  congr 2
  omega

theorem focusTrack_writeTrack {N : ℕ} (j : Fin N) (s : TrackCell N) (b : MarkerCell) :
    focusTrack j (writeTrack j s b) = b := by
  obtain ⟨b₁, b₂, b₃⟩ := b
  simp [focusTrack, writeTrack]

theorem writeTrack_other {N : ℕ} (j k : Fin N) (h : k ≠ j)
    (s : TrackCell N) (b : MarkerCell) : (writeTrack j s b).2.1 k = s.2.1 k := by
  simp [writeTrack, h]

theorem track_step {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (c : Bool)
    (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    (Turing.TM0.step (trackTable j M c) cfg).map (focusTrackCfg j) =
      Turing.TM0.step (M c) (focusTrackCfg j cfg) := by
  simp only [TM0_step_apply, trackTable, focusTrackCfg, Turing.Tape.map_fst]
  change (Option.map (fun p => ⟨p.1, TM0StmtApply cfg.Tape p.2⟩)
    (Option.map (fun p => match p.2 with
      | .move d => (p.1, Turing.TM0.Stmt.move d)
      | .write b => (p.1, Turing.TM0.Stmt.write (writeTrack j cfg.Tape.head b)))
      (M c cfg.q (focusTrack j cfg.Tape.head)))).map (focusTrackCfg j) =
      Option.map (fun p => ⟨p.1, TM0StmtApply (cfg.Tape.map (focusTrack j)) p.2⟩)
        (M c cfg.q (focusTrack j cfg.Tape.head))
  cases ht : M c cfg.q (focusTrack j cfg.Tape.head) with
  | none => rfl
  | some p =>
    obtain ⟨q, stmt⟩ := p
    cases stmt with
    | move d => simp [focusTrackCfg, TM0StmtApply, Turing.Tape.map_move]
    | write b => simp [focusTrackCfg, TM0StmtApply, Turing.Tape.map_write, focusTrack_writeTrack]

theorem track_coinHalt {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ)
    (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    coinHalt (trackTable j M) cfg = coinHalt M (focusTrackCfg j cfg) := by
  simp [coinHalt, trackTable, focusTrackCfg]

theorem track_coinConfig {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (coins : List Bool)
    (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    let wide := coinConfigRunAux (trackTable j M) coins cfg
    let focused := coinConfigRunAux M coins (focusTrackCfg j cfg)
    wide.stopped.map (focusTrackCfg j) = focused.stopped ∧
      wide.reads = focused.reads ∧ wide.transitions = focused.transitions := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M (focusTrackCfg j cfg) = true <;>
      simp [coinConfigRunAux, track_coinHalt, hc]
  | cons c cs ih =>
    by_cases hc : coinHalt M (focusTrackCfg j cfg) = true
    · simp [coinConfigRunAux, track_coinHalt, hc]
    · have hstep := track_step j M c cfg
      cases hs : Turing.TM0.step (trackTable j M c) cfg with
      | none =>
        have hsource : Turing.TM0.step (M c) (focusTrackCfg j cfg) = none := by
          rw [← hstep, hs]; rfl
        simp [coinConfigRunAux, track_coinHalt, hc, hs, hsource]
      | some next =>
        have hsource : Turing.TM0.step (M c) (focusTrackCfg j cfg) = some (focusTrackCfg j next) := by
          rw [← hstep, hs]; rfl
        obtain ⟨ho, hr, ht⟩ := ih next
        simp only [coinConfigRunAux, track_coinHalt, hc, Bool.false_eq_true, ↓reduceIte, hs,
            hsource]
        exact ⟨ho, by omega, by omega⟩

theorem tracksInput_focus {N : ℕ} (j : Fin N) (input : List Bool) :
    (Turing.Tape.mk₁ (tracksInput N input)).map (focusTrack j) =
      Turing.Tape.mk₁ (markerInput input) := by
  simp [tracksInput, markerInput, Turing.Tape.map_mk₁, List.map_map, focusTrack, Function.comp_def]

theorem coinConfigRunAux_invariant {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (P : Turing.TM0.Cfg Γ Λ → Prop)
    (hstep : ∀ c cfg next, P cfg → Turing.TM0.step (M c) cfg = some next → P next)
    (coins : List Bool) (cfg final : Turing.TM0.Cfg Γ Λ) (hp : P cfg)
    (hstop : (coinConfigRunAux M coins cfg).stopped = some final) : P final := by
  induction coins generalizing cfg with
  | nil =>
    by_cases hc : coinHalt M cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      exact hp
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt M cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      exact hp
    · cases ht : Turing.TM0.step (M c) cfg with
      | none =>
        have heq : cfg = final := Option.some.inj (by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, ht] using! hstop)
        subst final
        exact hp
      | some next =>
        have hn : (coinConfigRunAux M cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, ht] using! hstop
        exact ih next (hstep c cfg next hp ht) hn

theorem blankTrack_move {N : ℕ} (k : Fin N) (T : Turing.Tape (TrackCell N))
    (d : Turing.Dir) (h : BlankTrack k T) : BlankTrack k (T.move d) := by
  intro i
  cases d with
  | left => rw [Turing.Tape.move_left_nth]; exact h _
  | right => rw [Turing.Tape.move_right_nth]; exact h _

theorem blankTrack_write_other {N : ℕ} (j k : Fin N) (hkj : k ≠ j)
    (T : Turing.Tape (TrackCell N)) (b : MarkerCell) (h : BlankTrack k T) :
    BlankTrack k (T.write (writeTrack j T.head b)) := by
  intro i
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · subst i
    simpa [writeTrack, hkj] using! h 0
  · simpa only [hi, ↓reduceIte] using! h i

theorem track_step_blank_other {N : ℕ} {Λ : Type*} [Inhabited Λ] (j k : Fin N)
    (hkj : k ≠ j) (M : Bool → Turing.TM0.Machine MarkerCell Λ) (c : Bool)
    (cfg next : Turing.TM0.Cfg (TrackCell N) Λ) (h : BlankTrack k cfg.Tape)
    (hs : Turing.TM0.step (trackTable j M c) cfg = some next) : BlankTrack k next.Tape := by
  cases ht : M c cfg.q (focusTrack j cfg.Tape.head) with
  | none => simp [TM0_step_apply, trackTable, ht] at hs
  | some p =>
    obtain ⟨q, stmt⟩ := p
    cases stmt with
    | write b =>
      have he : Turing.TM0.step (trackTable j M c) cfg =
          some ⟨q, cfg.Tape.write (writeTrack j cfg.Tape.head b)⟩ := by
        simp [TM0_step_apply, trackTable, ht, TM0StmtApply]
      rw [he] at hs
      cases hs
      exact blankTrack_write_other j k hkj cfg.Tape b h
    | move d =>
      have he : Turing.TM0.step (trackTable j M c) cfg = some ⟨q, cfg.Tape.move d⟩ := by
        simp [TM0_step_apply, trackTable, ht, TM0StmtApply]
      rw [he] at hs
      cases hs
      exact blankTrack_move k cfg.Tape d h

theorem track_coin_blank_other {N : ℕ} {Λ : Type*} [Inhabited Λ] (j k : Fin N)
    (hkj : k ≠ j) (M : Bool → Turing.TM0.Machine MarkerCell Λ) (coins : List Bool)
    (cfg final : Turing.TM0.Cfg (TrackCell N) Λ) (h : BlankTrack k cfg.Tape)
    (hstop : (coinConfigRunAux (trackTable j M) coins cfg).stopped = some final) :
    BlankTrack k final.Tape :=
  coinConfigRunAux_invariant (trackTable j M) (fun cfg => BlankTrack k cfg.Tape)
    (track_step_blank_other j k hkj M) coins cfg final h hstop

theorem tracksInput_blank {N : ℕ} (j : Fin N) (input : List Bool) :
    BlankTrack j (Turing.Tape.mk₁ (tracksInput N input)) := by
  intro i
  change ((Turing.TM0.init (tracksInput N input) :
    Turing.TM0.Cfg (TrackCell N) (Fin 1)).Tape.nth i).2.1 j = none
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.init_nth]
  by_cases hi : i < 0
  · simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceIte, tracksInput]
    rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.getI_map]
    split_ifs <;> rfl

theorem track_coin_run {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (a : Λ → Bool)
    (coins : List Bool) (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    coinTapeRunAux (trackTable j M) a coins cfg = coinTapeRunAux M a coins (focusTrackCfg j cfg) ∧
    coinTapeTransitionCountAux (trackTable j M) coins cfg =
      coinTapeTransitionCountAux M coins (focusTrackCfg j cfg) := by
  have h := track_coinConfig j M coins cfg
  have hw := coinConfigRunAux_readout (trackTable j M) a coins cfg
  have hs := coinConfigRunAux_readout M a coins (focusTrackCfg j cfg)
  constructor
  · rw [← hw.1, ← hs.1, ← h.1, h.2.1]
    simp [Option.map_map, focusTrackCfg, Function.comp_def]
  · rw [← hw.2, ← hs.2]
    exact h.2.2

theorem track_commonHalt {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ q s, (trackTable j M false q s = none) ↔ (trackTable j M true q s = none) := by
  intro q s
  exact Option.map_eq_none_iff.trans ((hc q (focusTrack j s)).trans Option.map_eq_none_iff.symm)

theorem tracksInput_initial {N : ℕ} {Λ : Type*} [Inhabited Λ]
    (j : Fin N) (input : List Bool) :
    focusTrackCfg j (Turing.TM0.init (tracksInput N input) : Turing.TM0.Cfg (TrackCell N) Λ) =
      Turing.TM0.init (markerInput input) := by
  simp [focusTrackCfg, Turing.TM0.init, tracksInput_focus]

theorem trackCell_card (N : ℕ) : Fintype.card (TrackCell N) = 6 * 3 ^ N := by
  simp only [TrackCell, Fintype.card_prod, Fintype.card_option, Fintype.card_bool,
    Fintype.card_fun, Fintype.card_fin]
  ring

theorem trackRound_run {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (coins : List Bool) :
    coinTapeRun (trackRoundTable j Q M a) (prepareHomingAccept Q) (tracksInput N input) coins =
      coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input) coins ∧
    coinTapeTransitionCount (trackRoundTable j Q M a) (tracksInput N input) coins =
      coinTapeTransitionCount (prepareHomingCoinTable Q M a) (markerInput input) coins := by
  have h := track_coin_run j (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) coins
    (Turing.TM0.init (tracksInput N input))
  rw [tracksInput_initial] at h
  exact h

theorem trackRound_source_output {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (front : Fin (3 * input.length + 3) → Bool) (switch : Bool)
    (tail : List Bool) (t : ℕ) (hlen : 2 * t + 1 ≤ tail.length)
    (htotal : (coinTapeRun M a (input.map some) (tail.take t)).1 ≠ none) :
    (coinTapeRun (trackRoundTable j Q M a) (prepareHomingAccept Q) (tracksInput N input)
      (List.ofFn front ++ switch :: tail)).1 =
      (coinTapeRun M a (input.map some) (tail.take t)).1 ∧
    ∃ final : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)),
      let total := coinConfigRunAux (trackRoundTable j Q M a)
        (List.ofFn front ++ switch :: tail) (Turing.TM0.init (tracksInput N input))
      total.stopped = some final ∧ HomeAt (final.Tape.map (focusTrack j)) 0 ∧
      (∀ k : Fin N, k ≠ j → BlankTrack k final.Tape) ∧
      total.reads ≤ 3 * input.length + 2 * t + 5 ∧ total.transitions = total.reads := by
  obtain ⟨ho, q, home, hm, hs, hr, ht⟩ :=
      prepareHoming_source_output Q M a hc input front switch tail t hlen htotal
  have hw := trackRound_run j Q M a input (List.ofFn front ++ switch :: tail)
  constructor
  · exact (congrArg Prod.fst hw.1).trans ho
  · have hp := track_coinConfig j (prepareHomingCoinTable Q M a)
      (List.ofFn front ++ switch :: tail) (Turing.TM0.init (tracksInput N input))
    rw [tracksInput_initial] at hp
    obtain ⟨hproj, hread, htrans⟩ := hp
    change (coinConfigRunAux (trackRoundTable j Q M a) _ _).reads = _ at hread
    change (coinConfigRunAux (trackRoundTable j Q M a) _ _).transitions = _ at htrans
    change (coinConfigRunAux (trackRoundTable j Q M a) (List.ofFn front ++ switch :: tail)
      (Turing.TM0.init (tracksInput N input))).stopped.map (focusTrackCfg j) = _ at hproj
    rw [hs] at hproj
    cases hwstop : (coinConfigRunAux (trackRoundTable j Q M a) (List.ofFn front ++ switch :: tail)
      (Turing.TM0.init (tracksInput N input))).stopped with
    | none => rw [hwstop] at hproj; cases hproj
    | some final =>
      have hcfg : focusTrackCfg j final = ⟨q, home⟩ := Option.some.inj (by
        simpa only [hwstop, Option.map_some] using! hproj)
      have htape : final.Tape.map (focusTrack j) = home := congrArg Turing.TM0.Cfg.Tape hcfg
      refine ⟨final, hwstop, ?_, ?_, ?_, ?_⟩
      · rw [htape]
        exact hm
      · intro k hkj
        exact track_coin_blank_other j k hkj (prepareHomingCoinTable Q M a)
          (List.ofFn front ++ switch :: tail) _ final (tracksInput_blank k input) hwstop
      · (try dsimp only)
        rw [hread]
        exact hr
      · (try dsimp only)
        rw [htrans, hread]
        exact ht

theorem markerCopy_marked_first (input : List Bool) :
    Turing.TM0.step markerCopyTable ⟨0, markedInputTape input⟩ =
      Turing.TM0.step markerCopyTable (Turing.TM0.init (markerInput input)) := by
  simp [TM0_step_apply, markerCopyTable, markedInputTape, Turing.TM0.init, TM0StmtApply]
  rfl

theorem copySequence_marked_start {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (input : List Bool) (coins : List Bool) :
    coinConfigRunAux (sequenceCoinTable (fun _ => markerCopyTable) M) coins
        (mapCfg Sum.inl ⟨0, markedInputTape input⟩) =
      coinConfigRunAux (sequenceCoinTable (fun _ => markerCopyTable) M) coins
        (mapCfg Sum.inl (Turing.TM0.init (markerInput input))) := by
  cases coins with
  | nil => simp [coinConfigRunAux, sequence_coinHalt_left]
  | cons c cs =>
    have h := markerCopy_marked_first input
    have hu : Turing.TM0.step markerCopyTable (Turing.TM0.init (markerInput input)) =
        some ⟨1, markedInputTape input⟩ := by
      simp [TM0_step_apply, markerCopyTable, markedInputTape, Turing.TM0.init, TM0StmtApply]
    rw [hu] at h
    have hl := sequence_left_step markerCopyTable (M c) ⟨0, markedInputTape input⟩
      ⟨1, markedInputTape input⟩ h
    have hr := sequence_left_step markerCopyTable (M c) (Turing.TM0.init (markerInput input))
      ⟨1, markedInputTape input⟩ hu
    change Turing.TM0.step (sequenceCoinTable (fun _ => markerCopyTable) M c) _ = _ at hl hr
    simp only [coinConfigRunAux, sequence_coinHalt_left, Bool.false_eq_true, ↓reduceIte]
    rw [hl, hr]

theorem prepareHoming_marked_start (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (coins : List Bool) :
    coinConfigRunAux (prepareHomingCoinTable Q M a) coins ⟨0, markedInputTape input⟩ =
      coinConfigRunAux (prepareHomingCoinTable Q M a) coins
        (Turing.TM0.init (markerInput input)) := by
  let seq := sequenceCoinTable (fun _ => markerCopyTable) (nativeHomingCoinTable Q M a)
  have hm := relabel_coinConfig (prepareHomingLabels Q) seq coins
    (mapCfg Sum.inl (⟨0, markedInputTape input⟩ : Turing.TM0.Cfg MarkerCell (Fin 5)))
  have hu := relabel_coinConfig (prepareHomingLabels Q) seq coins
    (mapCfg Sum.inl (Turing.TM0.init (markerInput input)))
  rw [prepareHoming_initial] at hu
  have he : relabelCfg (prepareHomingLabels Q)
      (mapCfg Sum.inl (⟨0, markedInputTape input⟩ : Turing.TM0.Cfg MarkerCell (Fin 5))) =
      ⟨0, markedInputTape input⟩ := by simp [relabelCfg, mapCfg, prepareHomingLabels_zero]
  rw [he] at hm
  have hs := copySequence_marked_start (nativeHomingCoinTable Q M a) input coins
  change coinConfigRunAux seq coins _ = coinConfigRunAux seq coins _ at hs
  rw [hs] at hm
  exact hm.trans hu.symm

theorem homing_step_protected {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (c : Bool)
    (cfg next : Turing.TM0.Cfg MarkerCell (Sum (Λ × Bool) HomeState))
    (initial : Turing.Tape MarkerCell) (off : ℤ) (hp : ProtectedAt initial cfg.Tape off)
    (hs : Turing.TM0.step (homingCoinTable M a c) cfg = some next) :
    ∃ off' : ℤ, ProtectedAt initial next.Tape off' := by
  obtain ⟨q, T⟩ := cfg
  cases q with
  | inl q =>
    cases ht : Turing.TM0.step (sideWorkTable M c) ⟨q, T⟩ with
    | none =>
      have he := dispatch_step (sideWorkTable M c) (fun q => (q.2, a q.1)) markerHomeTable ⟨q, T⟩ ht
      change Turing.TM0.step (homingCoinTable M a c) ⟨Sum.inl q, T⟩ = _ at he
      rw [he] at hs
      cases hs
      exact ⟨off, hp⟩
    | some srcNext =>
      have he := dispatch_left_step (sideWorkTable M c) (fun q => (q.2, a q.1)) markerHomeTable
        ⟨q, T⟩ srcNext ht
      change Turing.TM0.step (homingCoinTable M a c) ⟨Sum.inl q, T⟩ = _ at he
      rw [he] at hs
      cases hs
      exact sideWork_step_protected M c ⟨q, T⟩ srcNext initial off hp ht
  | inr q =>
    by_cases hh : T.head.2.2 = true
    · simp [TM0_step_apply, homingCoinTable, dispatchCoinTable, dispatchTable, markerHomeTable,
        hh] at hs
    · have he : Turing.TM0.step (homingCoinTable M a c) ⟨Sum.inr q, T⟩ =
          some ⟨Sum.inr q, T.move (homeDirection q.1)⟩ := by
        simp [TM0_step_apply, homingCoinTable, dispatchCoinTable, dispatchTable, markerHomeTable,
          hh, TM0StmtApply]
      rw [he] at hs
      cases hs
      cases hdir : homeDirection q.1 with
      | left => exact ⟨off - 1, by simpa only [hdir] using! protectedAt_move_left initial T off hp⟩
      | right => exact ⟨off + 1, by simpa only [hdir] using! protectedAt_move_right initial T off hp⟩

theorem homing_halt_at_home {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool)
    (cfg : Turing.TM0.Cfg MarkerCell (Sum (Λ × Bool) HomeState))
    (hh : coinHalt (homingCoinTable M a) cfg = true) : cfg.Tape.head.2.2 = true := by
  obtain ⟨q, T⟩ := cfg
  cases q with
  | inl q =>
    have hn := dispatch_coinHalt_left (sideWorkTable M) (fun q => (q.2, a q.1))
      (fun _ => markerHomeTable) (⟨q, T⟩ : Turing.TM0.Cfg MarkerCell (Λ × Bool))
    change coinHalt (homingCoinTable M a) ⟨Sum.inl q, T⟩ = false at hn
    rw [hn] at hh
    cases hh
  | inr q =>
    by_contra hn
    simp [coinHalt, homingCoinTable, dispatchCoinTable, dispatchTable, markerHomeTable, hn] at hh

theorem homing_coin_protected {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) (input : List Bool)
    (coins : List Bool) (final : Turing.TM0.Cfg MarkerCell (Sum (Λ × Bool) HomeState))
    (hstop : (coinConfigRunAux (homingCoinTable M a) coins
      ⟨Sum.inl (default, false), markerCopyResult input⟩).stopped = some final) :
    ProtectedAt (markerCopyResult input) final.Tape 0 := by
  have hi : ∃ off : ℤ, ProtectedAt (markerCopyResult input) (markerCopyResult input) off :=
    ⟨0, markerCopyResult_home input, by intro i; simp⟩
  obtain ⟨off, hp⟩ := coinConfigRunAux_invariant (homingCoinTable M a)
    (fun cfg => ∃ off : ℤ, ProtectedAt (markerCopyResult input) cfg.Tape off)
    (by
      intro c cfg next h hs
      obtain ⟨off, hp⟩ := h
      exact homing_step_protected M a c cfg next (markerCopyResult input) off hp hs)
    coins ⟨Sum.inl (default, false), markerCopyResult input⟩ final hi hstop
  have hc := (coinConfigRunAux_commonHalt (homingCoinTable M a) (homingCoinTable_commonHalt M a)
    coins ⟨Sum.inl (default, false), markerCopyResult input⟩).2 final hstop
  have hh := homing_halt_at_home M a final hc
  have hm := homeAt_head final.Tape off hp.1
  rw [hh] at hm
  have hz : off = 0 := by simpa using! hm.symm
  simpa only [hz] using! hp

theorem nativeHoming_coin_protected (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (coins : List Bool)
    (final : Turing.TM0.Cfg MarkerCell (Fin (2 * Q + 6)))
    (hstop : (coinConfigRunAux (nativeHomingCoinTable Q M a) coins
      ⟨0, markerCopyResult input⟩).stopped = some final) :
    ProtectedAt (markerCopyResult input) final.Tape 0 := by
  have he := relabel_coinConfig (homingLabels Q) (homingCoinTable M a) coins
    (⟨Sum.inl (0, false), markerCopyResult input⟩ : Turing.TM0.Cfg MarkerCell
      (Sum (Fin (Q + 1) × Bool) HomeState))
  rw [nativeHoming_initial] at he
  have hs := congrArg CoinRunResult.stopped he
  change (coinConfigRunAux (nativeHomingCoinTable Q M a) coins
    ⟨0, markerCopyResult input⟩).stopped = _ at hs
  rw [hstop] at hs
  dsimp only at hs
  cases hc : (coinConfigRunAux (homingCoinTable M a) coins
    ⟨Sum.inl (0, false), markerCopyResult input⟩).stopped with
  | none => rw [hc] at hs; cases hs
  | some src =>
    rw [hc] at hs
    have hcfg := Option.some.inj hs
    have hp := homing_coin_protected M a input coins src
      (by simpa only [Fin.default_eq_zero] using! hc)
    have htape : final.Tape = src.Tape := congrArg Turing.TM0.Cfg.Tape hcfg
    rw [htape]
    exact hp

theorem prepareHoming_coin_protected (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (front : Fin (3 * input.length + 3) → Bool) (switch : Bool)
    (tail : List Bool) (final : Turing.TM0.Cfg MarkerCell (Fin (2 * Q + 11)))
    (hstop : (coinConfigRunAux (prepareHomingCoinTable Q M a) (List.ofFn front ++ switch :: tail)
      (Turing.TM0.init (markerInput input))).stopped = some final) :
    ProtectedAt (markerCopyResult input) final.Tape 0 := by
  let seq := sequenceCoinTable (fun _ => markerCopyTable) (nativeHomingCoinTable Q M a)
  have he := relabel_coinConfig (prepareHomingLabels Q) seq (List.ofFn front ++ switch :: tail)
    (mapCfg Sum.inl (Turing.TM0.init (markerInput input)))
  rw [prepareHoming_initial] at he
  have hs := congrArg CoinRunResult.stopped he
  change (coinConfigRunAux (prepareHomingCoinTable Q M a) (List.ofFn front ++ switch :: tail)
    (Turing.TM0.init (markerInput input))).stopped = _ at hs
  rw [hstop] at hs
  dsimp only at hs
  have hp := markerCopy_then_coin_source (nativeHomingCoinTable Q M a) input front switch tail
  simp only [Fin.default_eq_zero] at hp
  have hps := hp.1
  change (coinConfigRunAux seq (List.ofFn front ++ switch :: tail)
    (mapCfg Sum.inl (Turing.TM0.init (markerInput input)))).stopped = _ at hps
  rw [hps] at hs
  cases hc : (coinConfigRunAux (nativeHomingCoinTable Q M a) tail
    ⟨0, markerCopyResult input⟩).stopped with
  | none => rw [hc] at hs; cases hs
  | some src =>
    rw [hc] at hs
    have hcfg := Option.some.inj hs
    have htape : final.Tape = src.Tape := congrArg Turing.TM0.Cfg.Tape hcfg
    rw [htape]
    exact nativeHoming_coin_protected Q M a input tail src hc

theorem mapTape_nth {Γ Γ' : Type*} [Inhabited Γ] [Inhabited Γ']
    (f : Turing.PointedMap Γ Γ') (T : Turing.Tape Γ) (i : ℤ) :
    (T.map f).nth i = f (T.nth i) := by
  cases i with
  | ofNat n => cases n <;> simp [Turing.Tape.nth, Turing.Tape.map, Turing.ListBlank.nth_map]
  | negSucc n => simp [Turing.Tape.nth, Turing.Tape.map, Turing.ListBlank.nth_map]

theorem markedInputTape_home (input : List Bool) : HomeAt (markedInputTape input) 0 := by
  intro i
  unfold markedInputTape
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · simp [hi]
  · rw [if_neg hi]
    have hm : ((Turing.Tape.mk₁ (markerInput input)).nth i).2.2 = false := by
      change ((Turing.TM0.init (markerInput input) : Turing.TM0.Cfg MarkerCell (Fin 1)).Tape.nth i).2.2 = false
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.init_nth]
      split_ifs
      · rfl
      · rw [markerInput, Qatlib.Concepts.ClassicalTape.TapeCompilation.getI_map]
        split_ifs <;> rfl
    rw [hm]
    simp [hi]

theorem markerInput_work_blank (input : List Bool) (i : ℤ) :
    ((Turing.Tape.mk₁ (markerInput input)).nth i).2.1 = none := by
  change ((Turing.TM0.init (markerInput input) : Turing.TM0.Cfg MarkerCell (Fin 1)).Tape.nth i).2.1 = none
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.init_nth]
  split_ifs
  · rfl
  · rw [markerInput, Qatlib.Concepts.ClassicalTape.TapeCompilation.getI_map]
    split_ifs <;> rfl

theorem markedInput_work_blank (input : List Bool) (i : ℤ) :
    ((markedInputTape input).nth i).2.1 = none := by
  unfold markedInputTape
  rw [Turing.Tape.write_nth]
  by_cases hi : i = 0
  · subst i
    simpa using! markerInput_work_blank input 0
  · simpa only [hi, ↓reduceIte] using! markerInput_work_blank input i

theorem markedInput_copy_input (input : List Bool) (i : ℤ) :
    ((markedInputTape input).nth i).1 = ((markerCopyResult input).nth i).1 := by
  let f : Turing.PointedMap MarkerCell (Option Bool) := ⟨Prod.fst, rfl⟩
  have hm : (markedInputTape input).map f = Turing.Tape.mk₁ (input.map some) := by
    unfold markedInputTape
    rw [Turing.Tape.map_write]
    have h : (Turing.Tape.mk₁ (markerInput input)).map f = Turing.Tape.mk₁ (input.map some) := by
      simp [Turing.Tape.map_mk₁, markerInput, List.map_map, f, Function.comp_def]
    have hh := congrArg Turing.Tape.head h
    change f (Turing.Tape.mk₁ (markerInput input)).head = _ at hh
    change ((Turing.Tape.mk₁ (markerInput input)).map f).write
      (f (Turing.Tape.mk₁ (markerInput input)).head) = _
    rw [h, hh, Turing.Tape.write_self]
  have hc : (markerCopyResult input).map f = Turing.Tape.mk₁ (input.map some) := by
    unfold markerCopyResult
    rw [Turing.Tape.map_write]
    have h : (Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).map f =
        Turing.Tape.mk₁ (input.map some) := by
      simp [Turing.Tape.map_mk₁, List.map_map, f, Function.comp_def]
    have hh := congrArg Turing.Tape.head h
    change f (Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).head = _ at hh
    change ((Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).map f).write
      (f (Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))).head) = _
    rw [h, hh, Turing.Tape.write_self]
  have hn := congrArg (fun T : Turing.Tape (Option Bool) => T.nth i) (hm.trans hc.symm)
  simpa only [mapTape_nth, f] using! hn

theorem blankTrack_fresh_view {N : ℕ} (j k : Fin N) (input : List Bool)
    (T : Turing.Tape (TrackCell N))
    (hp : ProtectedAt (markerCopyResult input) (T.map (focusTrack j)) 0)
    (hb : BlankTrack k T) : T.map (focusTrack k) = markedInputTape input := by
  apply Qatlib.Concepts.ClassicalTape.TapeCompilation.tape_ext
  intro i
  have hi := hp.2 i
  have hh := hp.1 i
  simp only [mapTape_nth, focusTrack, Int.add_zero] at hi
  simp only [mapTape_nth, focusTrack, Int.add_zero] at hh
  rw [mapTape_nth]
  apply Prod.ext
  · exact hi.trans (markedInput_copy_input input i).symm
  · apply Prod.ext
    · exact (hb i).trans (markedInput_work_blank input i).symm
    · have hm := markedInputTape_home input i
      simp only [Int.add_zero] at hm
      exact hh.trans hm.symm

theorem trackRound_fresh_project {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (T : Turing.Tape (TrackCell N)) (coins : List Bool)
    (hf : T.map (focusTrack j) = Turing.Tape.mk₁ (markerInput input) ∨
      T.map (focusTrack j) = markedInputTape input) :
    let wide := coinConfigRunAux (trackRoundTable j Q M a) coins ⟨0, T⟩
    let single := coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))
    wide.stopped.map (focusTrackCfg j) = single.stopped ∧
      wide.reads = single.reads ∧ wide.transitions = single.transitions := by
  have h := track_coinConfig j (prepareHomingCoinTable Q M a) coins ⟨0, T⟩
  change (coinConfigRunAux (trackRoundTable j Q M a) coins ⟨0, T⟩).stopped.map (focusTrackCfg j) =
      (coinConfigRunAux (prepareHomingCoinTable Q M a) coins ⟨0, T.map (focusTrack j)⟩).stopped ∧
    _ = (coinConfigRunAux (prepareHomingCoinTable Q M a) coins ⟨0, T.map (focusTrack j)⟩).reads ∧
    _ = (coinConfigRunAux (prepareHomingCoinTable Q M a) coins ⟨0, T.map (focusTrack j)⟩).transitions at h
  rcases hf with hf | hf
  · rw [hf] at h
    exact h
  · rw [hf, prepareHoming_marked_start] at h
    exact h

theorem trackRound_fresh_execution {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (T : Turing.Tape (TrackCell N))
    (hf : T.map (focusTrack j) = Turing.Tape.mk₁ (markerInput input) ∨
      T.map (focusTrack j) = markedInputTape input)
    (front : Fin (3 * input.length + 3) → Bool) (switch : Bool)
    (tail : List Bool) (t : ℕ) (hlen : 2 * t + 1 ≤ tail.length)
    (htotal : (coinTapeRun M a (input.map some) (tail.take t)).1 ≠ none) :
    ∃ final : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)),
      let total := coinConfigRunAux (trackRoundTable j Q M a)
        (List.ofFn front ++ switch :: tail) ⟨0, T⟩
      total.stopped = some final ∧
      some (prepareHomingAccept Q final.q) = (coinTapeRun M a (input.map some) (tail.take t)).1 ∧
      ProtectedAt (markerCopyResult input) (final.Tape.map (focusTrack j)) 0 ∧
      (∀ k : Fin N, k ≠ j → BlankTrack k T →
        BlankTrack k final.Tape ∧ final.Tape.map (focusTrack k) = markedInputTape input) ∧
      total.reads ≤ 3 * input.length + 2 * t + 5 ∧ total.transitions = total.reads := by
  obtain ⟨ho, q, home, hm, hs, hr, ht⟩ :=
      prepareHoming_source_output Q M a hc input front switch tail t hlen htotal
  have hp := trackRound_fresh_project j Q M a input T (List.ofFn front ++ switch :: tail) hf
  dsimp only at hp
  obtain ⟨hproj, hread, htrans⟩ := hp
  rw [hs] at hproj
  cases hstop : (coinConfigRunAux (trackRoundTable j Q M a)
    (List.ofFn front ++ switch :: tail) ⟨0, T⟩).stopped with
  | none => rw [hstop] at hproj; cases hproj
  | some final =>
    have hcfg : focusTrackCfg j final = ⟨q, home⟩ := Option.some.inj (by
      simpa only [hstop, Option.map_some] using! hproj)
    have htape : final.Tape.map (focusTrack j) = home := congrArg Turing.TM0.Cfg.Tape hcfg
    have hq : final.q = q := congrArg Turing.TM0.Cfg.q hcfg
    have hprot := prepareHoming_coin_protected Q M a input front switch tail ⟨q, home⟩ hs
    have hprotected : ProtectedAt (markerCopyResult input) (final.Tape.map (focusTrack j)) 0 := by
      rw [htape]
      exact hprot
    have hro := congrArg Prod.fst (coinConfigRunAux_readout (prepareHomingCoinTable Q M a)
      (prepareHomingAccept Q) (List.ofFn front ++ switch :: tail)
      (Turing.TM0.init (markerInput input))).1
    change (coinConfigRunAux (prepareHomingCoinTable Q M a) (List.ofFn front ++ switch :: tail)
      (Turing.TM0.init (markerInput input))).stopped.map (fun cfg => prepareHomingAccept Q cfg.q) = _ at hro
    rw [hs] at hro
    refine ⟨final, hstop, ?_, hprotected, ?_, ?_, ?_⟩
    · rw [hq]
      exact hro.trans ho
    · intro k hkj hb
      have hblank := track_coin_blank_other j k hkj (prepareHomingCoinTable Q M a)
        (List.ofFn front ++ switch :: tail) ⟨0, T⟩ final hb hstop
      exact ⟨hblank, blankTrack_fresh_view j k input final.Tape hprotected hblank⟩
    · (try dsimp only)
      rw [hread]
      exact hr
    · (try dsimp only)
      rw [htrans, hread]
      exact ht

theorem boundedSucc_val (N : ℕ) (q : Fin (N + 1)) (h : q.val < N) :
    (boundedSucc N q).val = q.val + 1 := by
  simp [boundedSucc, min_eq_left (by omega : q.val + 1 ≤ N)]

theorem roundsNext_values (N Q : ℕ) (q : RoundsState N Q)
    (hj : q.1.val < N) (hc : q.2.1.val ≤ q.1.val) :
    (roundsNext N Q q).1.val = q.1.val + 1 ∧
    (roundsNext N Q q).2.1.val = q.2.1.val + (prepareHomingAccept Q q.2.2).toNat ∧
    (roundsNext N Q q).2.1.val ≤ (roundsNext N Q q).1.val := by
  have hcount : q.2.1.val < N := by omega
  simp only [roundsNext, boundedSucc_val N q.1 hj]
  cases hv : prepareHomingAccept Q q.2.2 <;>
    simp [boundedSucc_val N q.2.1 hcount] <;> omega

theorem roundsTable_halt_iff (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (c : Bool) (q : RoundsState N Q) (s : TrackCell N) :
    roundsTable N Q M a c q s = none ↔ q.1.val = N := by
  by_cases hj : q.1.val < N
  · cases ht : trackRoundTable ⟨q.1.val, hj⟩ Q M a c q.2.2 s <;>
      simp [roundsTable, hj, ht, show q.1.val ≠ N by omega]
  · have he : q.1.val = N := by have h := q.1.isLt; omega
    simp [roundsTable, he]

theorem roundsTable_commonHalt (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    ∀ q s, (roundsTable N Q M a false q s = none) ↔ (roundsTable N Q M a true q s = none) := by
  intro q s
  exact (roundsTable_halt_iff N Q M a false q s).trans (roundsTable_halt_iff N Q M a true q s).symm

set_option backward.isDefEq.respectTransparency true in

theorem roundsLabels_zero (N Q : ℕ) : roundsLabels N Q (0, 0, 0) = 0 := by
  apply Fin.ext
  simp [roundsLabels, finProdFinEquiv, Equiv.prodCongr]

theorem rounds_initial (N Q : ℕ) (input : List Bool) :
    relabelCfg (roundsLabels N Q) (Turing.TM0.init (tracksInput N input)) =
      Turing.TM0.init (tracksInput N input) := by
  change (⟨roundsLabels N Q (0, 0, 0), Turing.Tape.mk₁ (tracksInput N input)⟩ :
    Turing.TM0.Cfg (TrackCell N) (Fin (roundsControlMax N Q + 1))) = _
  rw [roundsLabels_zero]
  rfl

theorem nativeRounds_run (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (coins : List Bool) :
    coinTapeRun (nativeRoundsTable N Q M a) (nativeRoundsAccept N Q) (tracksInput N input) coins =
      coinTapeRun (roundsTable N Q M a) (roundsAccept N Q) (tracksInput N input) coins ∧
    coinTapeTransitionCount (nativeRoundsTable N Q M a) (tracksInput N input) coins =
      coinTapeTransitionCount (roundsTable N Q M a) (tracksInput N input) coins := by
  have hr := relabel_runAux (roundsLabels N Q) (roundsTable N Q M a) (roundsAccept N Q) coins
    (Turing.TM0.init (tracksInput N input))
  have ht := relabel_transitionsAux (roundsLabels N Q) (roundsTable N Q M a) coins
    (Turing.TM0.init (tracksInput N input))
  rw [rounds_initial] at hr ht
  exact ⟨hr, ht⟩

theorem trackRound_commonHalt {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    ∀ q s, (trackRoundTable j Q M a false q s = none) ↔
      (trackRoundTable j Q M a true q s = none) :=
  track_commonHalt j _ (prepareHoming_commonHalt Q M a)

theorem rounds_coinHalt_active (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (j count : Fin (N + 1)) (hj : j.val < N)
    (cfg : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11))) :
    coinHalt (roundsTable N Q M a) (roundsCfg j count cfg) = false := by
  have hf :=
      (roundsTable_halt_iff N Q M a false (j, count, cfg.q) cfg.Tape.head).not.mpr
      (by change j.val ≠ N; omega)
  simp only [coinHalt, roundsCfg]
  cases ht : roundsTable N Q M a false (j, count, cfg.q) cfg.Tape.head with
  | none => exact (hf ht).elim
  | some p => rfl

theorem rounds_step_success (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (j count : Fin (N + 1)) (hj : j.val < N) (c : Bool)
    (cfg next : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)))
    (hs : Turing.TM0.step (trackRoundTable ⟨j.val, hj⟩ Q M a c) cfg = some next) :
    Turing.TM0.step (roundsTable N Q M a c) (roundsCfg j count cfg) =
      some (roundsCfg j count next) := by
  cases ht : trackRoundTable ⟨j.val, hj⟩ Q M a c cfg.q cfg.Tape.head with
  | none => simp [TM0_step_apply, ht] at hs
  | some p =>
    rw [TM0_step_apply, ht] at hs
    cases hs
    simp [TM0_step_apply, roundsTable, roundsCfg, hj, ht]

theorem rounds_step_dispatch (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (j count : Fin (N + 1)) (hj : j.val < N) (c : Bool)
    (cfg : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)))
    (hh : Turing.TM0.step (trackRoundTable ⟨j.val, hj⟩ Q M a c) cfg = none) :
    Turing.TM0.step (roundsTable N Q M a c) (roundsCfg j count cfg) =
      some ⟨roundsNext N Q (j, count, cfg.q), cfg.Tape⟩ := by
  have ht := (TM0_step_eq_none _ cfg).mp hh
  simp [TM0_step_apply, roundsTable, roundsCfg, hj, ht, TM0StmtApply]

theorem rounds_coinConfig_stage (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (j count : Fin (N + 1)) (hj : j.val < N)
    (front tail : List Bool) (switch : Bool)
    (cfg final : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)))
    (hstop : (coinConfigRunAux (trackRoundTable ⟨j.val, hj⟩ Q M a) front cfg).stopped = some final)
    (hread : (coinConfigRunAux (trackRoundTable ⟨j.val, hj⟩ Q M a) front cfg).reads = front.length) :
    let total :=
        coinConfigRunAux (roundsTable N Q M a) (front ++ switch :: tail) (roundsCfg j count cfg)
    let r := coinConfigRunAux (roundsTable N Q M a) tail
      ⟨roundsNext N Q (j, count, final.q), final.Tape⟩
    total.stopped = r.stopped ∧ total.reads = r.reads + front.length + 1 ∧
      total.transitions = r.transitions + front.length + 1 := by
  induction front generalizing cfg with
  | nil =>
    by_cases hc : coinHalt (trackRoundTable ⟨j.val, hj⟩ Q M a) cfg = true
    · have heq : cfg = final := Option.some.inj (by
        simpa only [coinConfigRunAux, hc, ↓reduceIte] using! hstop)
      subst final
      have hd := rounds_step_dispatch N Q M a j count hj switch cfg
        (coinHalt_step_none _ cfg hc switch)
      (try dsimp only)
      simp only [List.nil_append, List.length_nil, coinConfigRunAux, rounds_coinHalt_active _ _ _ _ _ _ hj,
        Bool.false_eq_true, ↓reduceIte, hd]
      simp
    · simp [coinConfigRunAux, hc] at hstop
  | cons c cs ih =>
    by_cases hc : coinHalt (trackRoundTable ⟨j.val, hj⟩ Q M a) cfg = true
    · simp [coinConfigRunAux, hc] at hread
    · cases hs : Turing.TM0.step (trackRoundTable ⟨j.val, hj⟩ Q M a c) cfg with
      | none => exact (hc (step_none_common_halt _ (trackRound_commonHalt _ Q M a) c cfg hs)).elim
      | some next =>
        have hstop' : (coinConfigRunAux (trackRoundTable ⟨j.val, hj⟩ Q M a) cs next).stopped = some final := by
          simpa only [coinConfigRunAux, hc, ↓reduceIte, hs] using! hstop
        have hread' : (coinConfigRunAux (trackRoundTable ⟨j.val, hj⟩ Q M a) cs next).reads = cs.length := by
          have h := hread
          simp only [coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, hs,
              List.length_cons] at h
          exact Nat.succ.inj h
        have hp := rounds_step_success N Q M a j count hj c cfg next hs
        obtain ⟨ho, hr, ht⟩ := ih next hstop' hread'
        (try dsimp only)
        simp only [List.cons_append, List.length_cons, coinConfigRunAux,
          rounds_coinHalt_active _ _ _ _ _ _ hj, Bool.false_eq_true, ↓reduceIte, hp]
        refine ⟨ho, ?_, ?_⟩
        · rw [hr]
          omega
        · rw [ht]
          omega

theorem boolWord_of_length (l : List Bool) (n : ℕ) (h : l.length = n) :
    ∃ w : Fin n → Bool, List.ofFn w = l := by
  subst n
  exact ⟨l.get, List.ofFn_get l⟩

theorem trackRound_fresh_budget {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (T : Turing.Tape (TrackCell N))
    (hf : T.map (focusTrack j) = Turing.Tape.mk₁ (markerInput input) ∨
      T.map (focusTrack j) = markedInputTape input)
    (t : ℕ) (ht : ∀ w : Fin t → Bool,
      (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (coins : List Bool) (hlen : 3 * input.length + 2 * t + 5 ≤ coins.length) :
    ∃ final : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)),
      let r := coinConfigRunAux (trackRoundTable j Q M a) coins ⟨0, T⟩
      r.stopped = some final ∧ ProtectedAt (markerCopyResult input) (final.Tape.map (focusTrack j)) 0 ∧
      (∀ k : Fin N, k ≠ j → BlankTrack k T →
        BlankTrack k final.Tape ∧ final.Tape.map (focusTrack k) = markedInputTape input) ∧
      r.reads ≤ 3 * input.length + 2 * t + 5 ∧ r.transitions = r.reads := by
  let L := 3 * input.length + 3
  have hl : L < coins.length := by dsimp [L]; omega
  obtain ⟨front, hfront⟩ :=
      boolWord_of_length (coins.take L) L (by simp [List.length_take, Nat.le_of_lt hl])
  have hdlen : (coins.drop L).length = coins.length - L := List.length_drop
  cases hd : coins.drop L with
  | nil => simp only [hd, List.length_nil] at hdlen; omega
  | cons switch tail =>
    have hsplit : coins = List.ofFn front ++ switch :: tail := by
      rw [hfront, ← hd, List.take_append_drop]
    have htail : 2 * t + 1 ≤ tail.length := by
      simp only [hd, List.length_cons] at hdlen
      dsimp [L] at hdlen
      omega
    have htake : (tail.take t).length = t := by simp [List.length_take]; omega
    obtain ⟨w, hw⟩ := boolWord_of_length (tail.take t) t htake
    have h := trackRound_fresh_execution j Q M a hc input T hf front switch tail t htail
      (by rw [← hw]; exact ht w)
    rw [← hsplit] at h
    obtain ⟨final, hs, _, hp, hfresh, hr, ht'⟩ := h
    exact ⟨final, hs, hp, hfresh, hr, ht'⟩

theorem fresh_view_blank {N : ℕ} (j : Fin N) (input : List Bool) (T : Turing.Tape (TrackCell N))
    (hf : T.map (focusTrack j) = Turing.Tape.mk₁ (markerInput input) ∨
      T.map (focusTrack j) = markedInputTape input) : BlankTrack j T := by
  intro i
  rcases hf with hf | hf
  · have h := congrArg (fun t : Turing.Tape MarkerCell => (t.nth i).2.1) hf
    simp only [mapTape_nth, focusTrack] at h
    exact h.trans (markerInput_work_blank input i)
  · have h := congrArg (fun t : Turing.Tape MarkerCell => (t.nth i).2.1) hf
    simp only [mapTape_nth, focusTrack] at h
    exact h.trans (markedInput_work_blank input i)

theorem rounds_total_from (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (fuel : ℕ) (j count : Fin (N + 1)) (hcount : count.val ≤ j.val) (hrem : j.val + fuel = N)
    (T : Turing.Tape (TrackCell N))
    (hfresh : ∀ k : Fin N, j.val ≤ k.val →
      T.map (focusTrack k) = Turing.Tape.mk₁ (markerInput input) ∨
        T.map (focusTrack k) = markedInputTape input)
    (coins : List Bool) (hlen : fuel * (3 * input.length + 2 * t + 6) ≤ coins.length) :
    ∃ final : Turing.TM0.Cfg (TrackCell N) (RoundsState N Q),
      let r := coinConfigRunAux (roundsTable N Q M a) coins (roundsCfg j count ⟨0, T⟩)
      r.stopped = some final ∧ final.q.1.val = N ∧
      r.reads ≤ fuel * (3 * input.length + 2 * t + 6) ∧ r.transitions = r.reads := by
  induction fuel generalizing j count T coins with
  | zero =>
    have hj : j.val = N := by omega
    have hf := (roundsTable_halt_iff N Q M a false (j, count, 0) T.head).mpr hj
    have ht' := (roundsTable_halt_iff N Q M a true (j, count, 0) T.head).mpr hj
    have hh : coinHalt (roundsTable N Q M a) (roundsCfg j count ⟨0, T⟩) = true := by
      simp [coinHalt, roundsCfg, hf, ht']
    refine ⟨roundsCfg j count ⟨0, T⟩, ?_⟩
    cases coins <;> simp only [coinConfigRunAux, hh, ↓reduceIte] <;> simp [roundsCfg, hj]
  | succ fuel ih =>
    have hj : j.val < N := by omega
    let selected : Fin N := ⟨j.val, hj⟩
    have hbudget : fuel * (3 * input.length + 2 * t + 6) +
        (3 * input.length + 2 * t + 6) ≤ coins.length := by
      simpa only [Nat.add_mul, Nat.one_mul] using! hlen
    have hC : 3 * input.length + 2 * t + 5 ≤ coins.length := by omega
    obtain ⟨roundFinal, hstop, hprot, hothers, hreads, _⟩ :=
      trackRound_fresh_budget selected Q M a hc input T (hfresh selected (by rfl)) t ht coins hC
    let k := (coinConfigRunAux (trackRoundTable selected Q M a) coins ⟨0, T⟩).reads
    have hk : k ≤ 3 * input.length + 2 * t + 5 := hreads
    have hklen : k ≤ coins.length := by omega
    have he := coinConfigRunAux_take (trackRoundTable selected Q M a) coins ⟨0, T⟩
      (by rw [hstop]; exact Option.some_ne_none roundFinal)
    change coinConfigRunAux (trackRoundTable selected Q M a) (coins.take k) ⟨0, T⟩ = _ at he
    have hstop' : (coinConfigRunAux (trackRoundTable selected Q M a) (coins.take k) ⟨0, T⟩).stopped =
        some roundFinal := by rw [he]; exact hstop
    have hread' : (coinConfigRunAux (trackRoundTable selected Q M a) (coins.take k) ⟨0, T⟩).reads =
        (coins.take k).length := by rw [he, List.length_take, min_eq_left hklen]
    have hdlen : (coins.drop k).length = coins.length - k := List.length_drop
    cases hd : coins.drop k with
    | nil => simp only [hd, List.length_nil] at hdlen; omega
    | cons switch tail =>
      have hsplit : coins = coins.take k ++ switch :: tail := by rw [← hd, List.take_append_drop]
      have htail : fuel * (3 * input.length + 2 * t + 6) ≤ tail.length := by
        simp only [hd, List.length_cons] at hdlen
        omega
      let next := roundsNext N Q (j, count, roundFinal.q)
      have hv := roundsNext_values N Q (j, count, roundFinal.q) hj hcount
      dsimp only at hv
      have hnextval : next.1.val = j.val + 1 := hv.1
      have hnextcount : next.2.1.val ≤ next.1.val := hv.2.2
      have hnextrem : next.1.val + fuel = N := by omega
      have hnextfresh : ∀ l : Fin N, next.1.val ≤ l.val →
          roundFinal.Tape.map (focusTrack l) = Turing.Tape.mk₁ (markerInput input) ∨
            roundFinal.Tape.map (focusTrack l) = markedInputTape input := by
        intro l hl
        have hl' : j.val < l.val := by omega
        have hne : l ≠ selected := by
          intro heq; have hv' := congrArg Fin.val heq; dsimp [selected] at hv'; omega
        have hb := fresh_view_blank l input T (hfresh l (by omega))
        exact Or.inr (hothers l hne hb).2
      obtain ⟨final, hs, hfinal, hr, htr⟩ := ih next.1 next.2.1 hnextcount hnextrem
        roundFinal.Tape hnextfresh tail htail
      have hentry : roundsCfg next.1 next.2.1 ⟨0, roundFinal.Tape⟩ = ⟨next, roundFinal.Tape⟩ := by
        rfl
      rw [hentry] at hs hr htr
      have hstage := rounds_coinConfig_stage N Q M a j count hj (coins.take k) tail switch
        ⟨0, T⟩ roundFinal hstop' hread'
      dsimp only at hstage
      rw [← hsplit] at hstage
      obtain ⟨hstageStop, hstageReads, hstageTransitions⟩ := hstage
      refine ⟨final, hstageStop.trans hs, hfinal, ?_, ?_⟩
      · (try dsimp only)
        rw [hstageReads, List.length_take, min_eq_left hklen]
        change (coinConfigRunAux (roundsTable N Q M a) tail ⟨next, roundFinal.Tape⟩).reads ≤ _ at hr
        nlinarith
      · (try dsimp only)
        rw [hstageTransitions, hstageReads, htr]

theorem rounds_total (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (coins : List Bool) (hlen : N * (3 * input.length + 2 * t + 6) ≤ coins.length) :
    ∃ final : Turing.TM0.Cfg (TrackCell N) (RoundsState N Q),
      let r := coinConfigRunAux (roundsTable N Q M a) coins (Turing.TM0.init (tracksInput N input))
      r.stopped = some final ∧ final.q.1.val = N ∧
      r.reads ≤ N * (3 * input.length + 2 * t + 6) ∧ r.transitions = r.reads := by
  have h := rounds_total_from N Q M a hc input t ht N 0 0 (by simp) (by simp)
    (Turing.Tape.mk₁ (tracksInput N input)) (by intro k _; exact Or.inl (tracksInput_focus k input)) coins hlen
  simpa only [roundsCfg, Turing.TM0.init, Fin.default_eq_zero] using! h

theorem nativeRounds_commonHalt (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    ∀ q s, (nativeRoundsTable N Q M a false q s = none) ↔
      (nativeRoundsTable N Q M a true q s = none) := by
  intro q s
  have h := roundsTable_commonHalt N Q M a ((roundsLabels N Q).symm q) s
  exact Option.map_eq_none_iff.trans (h.trans Option.map_eq_none_iff.symm)

theorem nativeRounds_total (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (coins : List Bool) (hlen : N * (3 * input.length + 2 * t + 6) ≤ coins.length) :
    (coinTapeRun (nativeRoundsTable N Q M a) (nativeRoundsAccept N Q) (tracksInput N input) coins).1 ≠ none ∧
    (coinTapeRun (nativeRoundsTable N Q M a) (nativeRoundsAccept N Q) (tracksInput N input) coins).2 ≤
      N * (3 * input.length + 2 * t + 6) ∧
    coinTapeTransitionCount (nativeRoundsTable N Q M a) (tracksInput N input) coins =
      (coinTapeRun (nativeRoundsTable N Q M a) (nativeRoundsAccept N Q) (tracksInput N input) coins).2 := by
  obtain ⟨final, hs, _, hr, ht'⟩ := rounds_total N Q M a hc input t ht coins hlen
  have h := coinConfigRunAux_readout (roundsTable N Q M a) (roundsAccept N Q) coins
    (Turing.TM0.init (tracksInput N input))
  have hn := nativeRounds_run N Q M a input coins
  rw [hn.1, hn.2]
  obtain ⟨hreadout, hledger⟩ := h
  change _ = coinTapeRun (roundsTable N Q M a) (roundsAccept N Q)
      (tracksInput N input) coins at hreadout
  change _ = coinTapeTransitionCount (roundsTable N Q M a) (tracksInput N input) coins at hledger
  rw [← hreadout, ← hledger, hs]
  exact ⟨Option.some_ne_none _, hr, ht'⟩

theorem rounds_poly_bound (N c k n : ℕ) :
    N * (3 * n + 2 * (c * n ^ k + c) + 6) ≤
      (N * (4 * c + 10) + 1) * n ^ (2 * (k + 1)) + (N * (4 * c + 10) + 1) := by
  have h := prepareHoming_poly_bound c k n
  have hs : 3 * n + 2 * (c * n ^ k + c) + 6 ≤
      (4 * c + 10) * n ^ (2 * (k + 1)) + (4 * c + 10) := by
    nlinarith [Nat.zero_le (n ^ (2 * (k + 1)))]
  calc
    _ ≤ N * ((4 * c + 10) * n ^ (2 * (k + 1)) + (4 * c + 10)) := Nat.mul_le_mul_left N hs
    _ = (N * (4 * c + 10)) * n ^ (2 * (k + 1)) + N * (4 * c + 10) := by ring
    _ ≤ _ := by nlinarith [Nat.zero_le (n ^ (2 * (k + 1)))]

theorem nativeRounds_polynomial (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (c k : ℕ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (htotal : ∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
      (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q s, (nativeRoundsTable N Q M a false q s = none) ↔
        (nativeRoundsTable N Q M a true q s = none)) ∧
      ∀ input : List Bool,
        let B := d * input.length ^ (2 * (k + 1)) + d
        (∀ w : Fin B → Bool,
          (coinTapeRun (nativeRoundsTable N Q M a) (nativeRoundsAccept N Q) (tracksInput N input)
            (List.ofFn w)).1 ≠ none) ∧
        (∀ w : Fin B → Bool,
          coinTapeTransitionCount (nativeRoundsTable N Q M a) (tracksInput N input) (List.ofFn w) ≤ B) := by
  refine ⟨N * (4 * c + 10) + 1, by omega, nativeRounds_commonHalt N Q M a, ?_⟩
  intro input
  let T := c * input.length ^ k + c
  let B := (N * (4 * c + 10) + 1) * input.length ^ (2 * (k + 1)) + (N * (4 * c + 10) + 1)
  have hb : N * (3 * input.length + 2 * T + 6) ≤ B := rounds_poly_bound N c k input.length
  have hrun (w : Fin B → Bool) := nativeRounds_total N Q M a hc input T (htotal input)
    (List.ofFn w) (by simpa using! hb)
  constructor
  · intro w
    exact (hrun w).1
  · intro w
    have hw := hrun w
    exact hw.2.2.le.trans (hw.2.1.trans hb)

theorem fairCfgValue_zero {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (g : Turing.TM0.Cfg Γ Λ → ℝ)
    (cfg : Turing.TM0.Cfg Γ Λ) :
    fairCfgValue M g 0 cfg = if coinHalt M cfg then g cfg else 0 := by
  by_cases hc : coinHalt M cfg = true <;> simp [fairCfgValue, stoppedValue, coinConfigRunAux, hc]

theorem fairCfgValue_halt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (g : Turing.TM0.Cfg Γ Λ → ℝ)
    (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (hc : coinHalt M cfg = true) :
    fairCfgValue M g n cfg = g cfg := by
  have hr (coins : List Bool) : stoppedValue g (coinConfigRunAux M coins cfg) = g cfg := by
    cases coins <;> simp [stoppedValue, coinConfigRunAux, hc]
  simp [fairCfgValue, hr]

theorem fairCfgValue_succ_live {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (g : Turing.TM0.Cfg Γ Λ → ℝ)
    (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (hc : coinHalt M cfg ≠ true) :
    fairCfgValue M g (n + 1) cfg =
      ((Turing.TM0.step (M false) cfg).elim (g cfg) (fairCfgValue M g n) +
        (Turing.TM0.step (M true) cfg).elim (g cfg) (fairCfgValue M g n)) / 2 := by
  have hp (b : Bool) (w : Fin n → Bool) :
      stoppedValue g (coinConfigRunAux M (List.ofFn (consCoinWords n (b, w))) cfg) =
      (Turing.TM0.step (M b) cfg).elim (g cfg)
        (fun next => stoppedValue g (coinConfigRunAux M (List.ofFn w) next)) := by
    have hw : List.ofFn (consCoinWords n (b, w)) = b :: List.ofFn w := by
      rw [List.ofFn_succ]; rfl
    rw [hw]
    cases hs : Turing.TM0.step (M b) cfg <;> simp [stoppedValue, coinConfigRunAux, hc, hs]
  unfold fairCfgValue
  rw [← (consCoinWords n).sum_comp]
  simp_rw [hp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases hf : Turing.TM0.step (M false) cfg <;> cases ht : Turing.TM0.step (M true) cfg <;>
    simp only [Option.elim_none, Option.elim_some] <;>
    simp [pow_succ] <;> field_simp <;> ring

theorem coinConfig_total_next {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (n : ℕ)
    (cfg next : Turing.TM0.Cfg Γ Λ) (c : Bool) (hs : Turing.TM0.step (M c) cfg = some next)
    (ht : ∀ w : Fin (n + 1) → Bool, (coinConfigRunAux M (List.ofFn w) cfg).stopped ≠ none) :
    ∀ w : Fin n → Bool, (coinConfigRunAux M (List.ofFn w) next).stopped ≠ none := by
  have hc : coinHalt M cfg ≠ true := by
    intro hc
    rw [coinHalt_step_none M cfg hc c] at hs
    cases hs
  intro w
  have h := ht (consCoinWords n (c, w))
  have hw : List.ofFn (consCoinWords n (c, w)) = c :: List.ofFn w := by
    rw [List.ofFn_succ]; rfl
  simpa only [hw, coinConfigRunAux, hc, ↓reduceIte, hs] using! h

theorem fairCfgValue_dispatch {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (K : Bool → Turing.TM0.Machine Γ Λ) (h : Turing.TM0.Cfg Γ Λ → ℝ)
    (cfg next : Turing.TM0.Cfg Γ Λ) (D : ℕ) (value : ℝ)
    (hlive : coinHalt K cfg = false)
    (hstep : ∀ c, Turing.TM0.step (K c) cfg = some next)
    (hcont : ∀ u : ℕ, fairCfgValue K h (D + u) next = value) (t : ℕ) :
    fairCfgValue K h (t + 1 + D) cfg = value := by
  rw [show t + 1 + D = (D + t) + 1 by omega,
    fairCfgValue_succ_live K h (D + t) cfg (by rw [hlive]; decide)]
  rw [hstep false, hstep true]
  simp only [Option.elim_some]
  rw [hcont t]
  ring

theorem fairCfgValue_bind
    {Γ Λ Δ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Δ] [Inhabited Μ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (K : Bool → Turing.TM0.Machine Δ Μ)
    (embed dispatch : Turing.TM0.Cfg Γ Λ → Turing.TM0.Cfg Δ Μ)
    (P : Turing.TM0.Cfg Γ Λ → Prop)
    (hclosed : ∀ c cfg next, P cfg → Turing.TM0.step (M c) cfg = some next → P next)
    (hcommon : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (hlive : ∀ cfg, P cfg → coinHalt K (embed cfg) = false)
    (hstep : ∀ c cfg next, P cfg → Turing.TM0.step (M c) cfg = some next →
      Turing.TM0.step (K c) (embed cfg) = some (embed next))
    (hdispatch : ∀ c cfg, P cfg → coinHalt M cfg = true →
      Turing.TM0.step (K c) (embed cfg) = some (dispatch cfg))
    (g : Turing.TM0.Cfg Γ Λ → ℝ) (h : Turing.TM0.Cfg Δ Μ → ℝ) (D : ℕ)
    (hcont : ∀ cfg, P cfg → coinHalt M cfg = true → ∀ u : ℕ,
      fairCfgValue K h (D + u) (dispatch cfg) = g cfg)
    (t : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) (hp : P cfg)
    (htotal : ∀ w : Fin t → Bool, (coinConfigRunAux M (List.ofFn w) cfg).stopped ≠ none) :
    fairCfgValue K h (t + 1 + D) (embed cfg) = fairCfgValue M g t cfg := by
  induction t generalizing cfg with
  | zero =>
    have hc : coinHalt M cfg = true := by
      by_contra hc
      have hn := htotal (fun i => Fin.elim0 i)
      simp [coinConfigRunAux, hc] at hn
    exact (fairCfgValue_dispatch K h (embed cfg) (dispatch cfg) D (g cfg)
      (hlive cfg hp) (fun c => hdispatch c cfg hp hc) (hcont cfg hp hc) 0).trans
      (fairCfgValue_halt M g 0 cfg hc).symm
  | succ n ih =>
    by_cases hc : coinHalt M cfg = true
    · exact (fairCfgValue_dispatch K h (embed cfg) (dispatch cfg) D (g cfg)
        (hlive cfg hp) (fun c => hdispatch c cfg hp hc) (hcont cfg hp hc) (n + 1)).trans
        (fairCfgValue_halt M g (n + 1) cfg hc).symm
    · cases hf : Turing.TM0.step (M false) cfg with
      | none => exact (hc (step_none_common_halt M hcommon false cfg hf)).elim
      | some fnext =>
        cases ht : Turing.TM0.step (M true) cfg with
        | none => exact (hc (step_none_common_halt M hcommon true cfg ht)).elim
        | some tnext =>
          have hf' := ih fnext (hclosed false cfg fnext hp hf)
            (coinConfig_total_next M n cfg fnext false hf htotal)
          have ht' := ih tnext (hclosed true cfg tnext hp ht)
            (coinConfig_total_next M n cfg tnext true ht htotal)
          rw [show (n + 1) + 1 + D = (n + 1 + D) + 1 by omega,
            fairCfgValue_succ_live K h (n + 1 + D) (embed cfg) (by rw [hlive cfg hp]; decide),
            fairCfgValue_succ_live M g n cfg hc]
          rw [hstep false cfg fnext hp hf, hstep true cfg tnext hp ht, hf, ht]
          simp only [Option.elim_some]
          rw [hf', ht']

theorem coinStepsAux_append {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (front tail : List Bool) (cfg : Turing.TM0.Cfg Γ Λ) :
    coinStepsAux M (front ++ tail) cfg = (coinStepsAux M front cfg).bind (coinStepsAux M tail) := by
  induction front generalizing cfg with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, coinStepsAux]
    cases hs : Turing.TM0.step (M c) cfg with
    | none => rfl
    | some next => exact ih next

theorem coinStepsAux_stopped {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (coins : List Bool)
    (cfg final : Turing.TM0.Cfg Γ Λ) (hr : coinStepsAux M coins cfg = some final)
    (hh : coinHalt M final = true) :
    (coinConfigRunAux M coins cfg).stopped = some final ∧
      (coinConfigRunAux M coins cfg).reads = coins.length ∧
      (coinConfigRunAux M coins cfg).transitions = coins.length := by
  induction coins generalizing cfg with
  | nil =>
    have heq : cfg = final := Option.some.inj hr
    subst final
    simp [coinConfigRunAux, hh]
  | cons c cs ih =>
    cases hs : Turing.TM0.step (M c) cfg with
    | none => simp [coinStepsAux, hs] at hr
    | some next =>
      have hn : coinStepsAux M cs next = some final := by
        simpa only [coinStepsAux, hs, Option.bind_some] using! hr
      have hc : coinHalt M cfg ≠ true := by
        intro hc
        rw [coinHalt_step_none M cfg hc c] at hs
        cases hs
      obtain ⟨ho, hread, htrans⟩ := ih next hn
      simp only [coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, hs, List.length_cons]
      exact ⟨ho, congrArg Nat.succ hread, congrArg Nat.succ htrans⟩

theorem prepareHoming_any_protected (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (coins : List Bool) (final : Turing.TM0.Cfg MarkerCell (Fin (2 * Q + 11)))
    (hstop : (coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))).stopped = some final) :
    ProtectedAt (markerCopyResult input) final.Tape 0 := by
  let L := 3 * input.length + 3
  let extra := coins ++ List.replicate (L + 1) false
  have he := coinConfigRunAux_append (prepareHomingCoinTable Q M a) coins (List.replicate (L + 1) false)
    (Turing.TM0.init (markerInput input)) (by rw [hstop]; exact Option.some_ne_none final)
  have hs : (coinConfigRunAux (prepareHomingCoinTable Q M a) extra
      (Turing.TM0.init (markerInput input))).stopped = some final := by rw [he]; exact hstop
  have hl : L < extra.length := by simp [extra]; omega
  obtain ⟨front, hfront⟩ :=
      boolWord_of_length (extra.take L) L (by simp [List.length_take, Nat.le_of_lt hl])
  have hdlen : (extra.drop L).length = extra.length - L := List.length_drop
  cases hd : extra.drop L with
  | nil => simp only [hd, List.length_nil] at hdlen; omega
  | cons switch tail =>
    have hsplit : extra = List.ofFn front ++ switch :: tail := by
      rw [hfront, ← hd, List.take_append_drop]
    rw [hsplit] at hs
    exact prepareHoming_coin_protected Q M a input front switch tail final hs

theorem trackRound_fresh_stopped {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List Bool) (T : Turing.Tape (TrackCell N))
    (hf : T.map (focusTrack j) = Turing.Tape.mk₁ (markerInput input) ∨
      T.map (focusTrack j) = markedInputTape input)
    (coins : List Bool) (final : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)))
    (hstop : (coinConfigRunAux (trackRoundTable j Q M a) coins ⟨0, T⟩).stopped = some final) :
    ProtectedAt (markerCopyResult input) (final.Tape.map (focusTrack j)) 0 ∧
      ∀ k : Fin N, k ≠ j → BlankTrack k T →
        BlankTrack k final.Tape ∧ final.Tape.map (focusTrack k) = markedInputTape input := by
  have hp := trackRound_fresh_project j Q M a input T coins hf
  have hs : (coinConfigRunAux (prepareHomingCoinTable Q M a) coins
      (Turing.TM0.init (markerInput input))).stopped = some (focusTrackCfg j final) := by
    rw [← hp.1, hstop]
    rfl
  have hprotected := prepareHoming_any_protected Q M a input coins (focusTrackCfg j final) hs
  refine ⟨hprotected, ?_⟩
  intro k hkj hb
  have hk :=
      track_coin_blank_other j k hkj (prepareHomingCoinTable Q M a) coins ⟨0, T⟩ final hb hstop
  exact ⟨hk, blankTrack_fresh_view j k input final.Tape hprotected hk⟩

theorem fairCfgValue_bool {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (f : Bool → ℝ)
    (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    fairCfgValue M (fun c => f (a c.q)) n cfg =
      f false * fairCfgValue M (fun c => if a c.q = false then 1 else 0) n cfg +
      f true * fairCfgValue M (fun c => if a c.q = true then 1 else 0) n cfg := by
  have hp (w : Fin n → Bool) :
      stoppedValue (fun c => f (a c.q)) (coinConfigRunAux M (List.ofFn w) cfg) =
      f false * stoppedValue (fun c => if a c.q = false then 1 else 0) (coinConfigRunAux M (List.ofFn w) cfg) +
      f true * stoppedValue (fun c => if a c.q = true then 1 else 0) (coinConfigRunAux M (List.ofFn w) cfg) := by
    cases hs : (coinConfigRunAux M (List.ofFn w) cfg).stopped with
    | none => simp [stoppedValue, hs]
    | some final => cases hb : a final.q <;> simp [stoppedValue, hs, hb]
  unfold fairCfgValue
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem fairCfgValue_success {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (target : Bool)
    (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) :
    fairCfgValue M (fun c => if a c.q = target then 1 else 0) n cfg =
      (∑ w : Fin n → Bool,
        if (coinTapeRunAux M a (List.ofFn w) cfg).1 = some target then (1 : ℝ) else 0) / 2 ^ n := by
  unfold fairCfgValue
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  have hp := congrArg Prod.fst (coinConfigRunAux_readout M a (List.ofFn w) cfg).1
  change (coinConfigRunAux M (List.ofFn w) cfg).stopped.map (fun c => a c.q) = _ at hp
  rw [← hp]
  cases hs : (coinConfigRunAux M (List.ofFn w) cfg).stopped <;> simp [stoppedValue, hs]

theorem fairCfgValue_initial {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (target : Bool)
    (n : ℕ) (input : List Γ) :
    fairCfgValue M (fun c => if a c.q = target then 1 else 0) n (Turing.TM0.init input) =
      fairTapeSuccess M a input n target := fairCfgValue_success M a target n _

theorem trackRound_fresh_mass {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (T : Turing.Tape (TrackCell N))
    (hf : T.map (focusTrack j) = Turing.Tape.mk₁ (markerInput input) ∨
      T.map (focusTrack j) = markedInputTape input)
    (t : ℕ) (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (target : Bool) :
    fairCfgValue (trackRoundTable j Q M a) (fun c => if prepareHomingAccept Q c.q = target then 1 else 0)
        (3 * input.length + 2 * t + 5) ⟨0, T⟩ =
      fairTapeSuccess M a (input.map some) t target := by
  let C := 3 * input.length + 2 * t + 5
  have hpoint (w : Fin C → Bool) :
      (coinTapeRunAux (trackRoundTable j Q M a) (prepareHomingAccept Q) (List.ofFn w) ⟨0, T⟩).1 =
      (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q) (markerInput input) (List.ofFn w)).1 := by
    have hp := trackRound_fresh_project j Q M a input T (List.ofFn w) hf
    have hw := congrArg Prod.fst (coinConfigRunAux_readout (trackRoundTable j Q M a)
      (prepareHomingAccept Q) (List.ofFn w) ⟨0, T⟩).1
    have hs := congrArg Prod.fst (coinConfigRunAux_readout (prepareHomingCoinTable Q M a)
      (prepareHomingAccept Q) (List.ofFn w) (Turing.TM0.init (markerInput input))).1
    change (coinConfigRunAux (trackRoundTable j Q M a) (List.ofFn w) ⟨0, T⟩).stopped.map
      (fun c => prepareHomingAccept Q c.q) = _ at hw
    change (coinConfigRunAux (prepareHomingCoinTable Q M a) (List.ofFn w)
      (Turing.TM0.init (markerInput input))).stopped.map (fun c => prepareHomingAccept Q c.q) = _ at hs
    change _ = (coinTapeRun (prepareHomingCoinTable Q M a) (prepareHomingAccept Q)
      (markerInput input) (List.ofFn w)).1 at hs
    rw [← hw, ← hs, ← hp.1]
    simp [Option.map_map, focusTrackCfg, Function.comp_def]
  rw [fairCfgValue_success]
  simp_rw [hpoint]
  change fairTapeSuccess (prepareHomingCoinTable Q M a) (prepareHomingAccept Q)
      (markerInput input) C target = _
  have hclock : C = (3 * input.length + 3) + ((t + (t + 1)) + 1) := by dsimp [C]; omega
  rw [hclock]
  exact prepareHoming_fair_mass Q M a hc input t target ht

theorem rounds_mass_from (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (target : Bool) (fuel : ℕ) (j count : Fin (N + 1))
    (hcount : count.val ≤ j.val) (hrem : j.val + fuel = N)
    (T : Turing.Tape (TrackCell N))
    (hfresh : ∀ k : Fin N, j.val ≤ k.val →
      T.map (focusTrack k) = Turing.Tape.mk₁ (markerInput input) ∨
        T.map (focusTrack k) = markedInputTape input)
    (B : ℕ) (hB : fuel * (3 * input.length + 2 * t + 6) ≤ B) :
    fairCfgValue (roundsTable N Q M a) (fun cfg => if roundsAccept N Q cfg.q = target then 1 else 0)
      B (roundsCfg j count ⟨0, T⟩) =
      remainingVoteMass N (fairTapeSuccess M a (input.map some) t false)
        (fairTapeSuccess M a (input.map some) t true) target fuel count.val := by
  induction fuel generalizing j count T B with
  | zero =>
    have hj : j.val = N := by omega
    have hf := (roundsTable_halt_iff N Q M a false (j, count, 0) T.head).mpr hj
    have ht' := (roundsTable_halt_iff N Q M a true (j, count, 0) T.head).mpr hj
    have hh : coinHalt (roundsTable N Q M a) (roundsCfg j count ⟨0, T⟩) = true := by
      simp [coinHalt, roundsCfg, hf, ht']
    rw [fairCfgValue_halt _ _ B _ hh]
    rfl
  | succ fuel ih =>
    have hj : j.val < N := by omega
    let selected : Fin N := ⟨j.val, hj⟩
    let C := 3 * input.length + 2 * t + 5
    let D := B - (C + 1)
    have hbudget : fuel * (C + 1) + (C + 1) ≤ B := by
      simpa only [Nat.add_mul, Nat.one_mul] using! hB
    have hBD : B = C + 1 + D := by dsimp [D]; omega
    have hD : fuel * (C + 1) ≤ D := by dsimp [D]; omega
    let S := trackRoundTable selected Q M a
    let K := roundsTable N Q M a
    let start : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)) := ⟨0, T⟩
    let P := fun cfg => ∃ front : List Bool, coinStepsAux S front start = some cfg
    let payoff := fun cfg : Turing.TM0.Cfg (TrackCell N) (RoundsState N Q) =>
      if roundsAccept N Q cfg.q = target then (1 : ℝ) else 0
    let f := fun b : Bool => remainingVoteMass N (fairTapeSuccess M a (input.map some) t false)
      (fairTapeSuccess M a (input.map some) t true) target fuel (count.val + b.toNat)
    let g :=
        fun cfg : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)) => f (prepareHomingAccept Q cfg.q)
    let dispatch := fun cfg : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11)) =>
      (⟨roundsNext N Q (j, count, cfg.q), cfg.Tape⟩ : Turing.TM0.Cfg (TrackCell N) (RoundsState N Q))
    have hclosed : ∀ c cfg next, P cfg → Turing.TM0.step (S c) cfg = some next → P next := by
      intro c cfg next hp hs
      obtain ⟨front, hr⟩ := hp
      refine ⟨front ++ [c], ?_⟩
      rw [coinStepsAux_append, hr]
      simp [coinStepsAux, hs]
    have hcont : ∀ cfg, P cfg → coinHalt S cfg = true → ∀ u : ℕ,
        fairCfgValue K payoff (D + u) (dispatch cfg) = g cfg := by
      intro cfg hp hh u
      obtain ⟨front, hr⟩ := hp
      have hstop := (coinStepsAux_stopped S front start cfg hr hh).1
      have hframes :=
          trackRound_fresh_stopped selected Q M a input T (hfresh selected (by rfl)) front cfg hstop
      let next := roundsNext N Q (j, count, cfg.q)
      have hv := roundsNext_values N Q (j, count, cfg.q) hj hcount
      dsimp only at hv
      have hnextval : next.1.val = j.val + 1 := hv.1
      have hnextcount : next.2.1.val ≤ next.1.val := hv.2.2
      have hnextrem : next.1.val + fuel = N := by omega
      have hnextfresh : ∀ l : Fin N, next.1.val ≤ l.val →
          cfg.Tape.map (focusTrack l) = Turing.Tape.mk₁ (markerInput input) ∨
            cfg.Tape.map (focusTrack l) = markedInputTape input := by
        intro l hl
        have hl' : j.val < l.val := by omega
        have hne : l ≠ selected := by
          intro heq
          have hv' := congrArg Fin.val heq
          dsimp [selected] at hv'
          omega
        have hb := fresh_view_blank l input T (hfresh l (by omega))
        exact Or.inr (hframes.2 l hne hb).2
      have h :=
          ih next.1 next.2.1 hnextcount hnextrem cfg.Tape hnextfresh (D + u)
          (by change fuel * (C + 1) ≤ D + u; omega)
      change fairCfgValue K payoff (D + u) (roundsCfg next.1 next.2.1 ⟨0, cfg.Tape⟩) = _ at h
      change fairCfgValue K payoff (D + u) (roundsCfg next.1 next.2.1 ⟨0, cfg.Tape⟩) = _
      rw [h]
      rw [hv.2.1]
    have htotal : ∀ w : Fin C → Bool, (coinConfigRunAux S (List.ofFn w) start).stopped ≠ none := by
      intro w
      obtain ⟨final, hs, _⟩ := trackRound_fresh_budget selected Q M a hc input T
        (hfresh selected (by rfl)) t ht (List.ofFn w) (by simp [C])
      rw [hs]
      exact Option.some_ne_none final
    have hbind := fairCfgValue_bind S K (roundsCfg j count) dispatch P hclosed
      (trackRound_commonHalt selected Q M a)
      (fun cfg _ => rounds_coinHalt_active N Q M a j count hj cfg)
      (fun c cfg next _ hs => rounds_step_success N Q M a j count hj c cfg next hs)
      (fun c cfg _ hh => rounds_step_dispatch N Q M a j count hj c cfg (coinHalt_step_none S cfg hh c))
      g payoff D hcont C start ⟨[], rfl⟩ htotal
    change fairCfgValue K payoff B (roundsCfg j count start) = _
    rw [hBD, hbind]
    change fairCfgValue S (fun cfg => f (prepareHomingAccept Q cfg.q)) C start = _
    rw [fairCfgValue_bool]
    rw [trackRound_fresh_mass selected Q M a hc input T (hfresh selected (by rfl)) t ht false,
      trackRound_fresh_mass selected Q M a hc input T (hfresh selected (by rfl)) t ht true]
    simp only [remainingVoteMass, f, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
    ring

theorem uniformVotesMass_zero {I : Type*} [Fintype I] (N : ℕ) (vote : I → Bool)
    (target : Bool) (count : ℕ) : uniformVotesMass N vote target 0 count =
      if decide (N / 2 < count) = target then 1 else 0 := by
  simp [uniformVotesMass]

theorem uniformVotesMass_succ {I : Type*} [Fintype I] [Nonempty I]
    (N : ℕ) (vote : I → Bool) (target : Bool) (fuel count : ℕ) :
    uniformVotesMass N vote target (fuel + 1) count =
      ((∑ x : I, if vote x = false then (1 : ℝ) else 0) / Fintype.card I) *
        uniformVotesMass N vote target fuel count +
      ((∑ x : I, if vote x = true then (1 : ℝ) else 0) / Fintype.card I) *
        uniformVotesMass N vote target fuel (count + 1) := by
  have hp (x : I) (w : Fin fuel → I) :
      (if decide (N / 2 < count + trueCount (List.ofFn fun j => vote (consTrials I fuel (x, w) j))) = target
        then (1 : ℝ) else 0) =
      (if vote x = false then (1 : ℝ) else 0) *
        (if decide (N / 2 < count + trueCount (List.ofFn fun j => vote (w j))) = target then 1 else 0) +
      (if vote x = true then (1 : ℝ) else 0) *
        (if decide (N / 2 < (count + 1) + trueCount (List.ofFn fun j => vote (w j))) = target then 1 else 0) := by
    have hw : List.ofFn (fun j => vote (consTrials I fuel (x, w) j)) =
        vote x :: List.ofFn (fun j => vote (w j)) := by rw [List.ofFn_succ]; rfl
    rw [hw, trueCount_cons]
    cases hv : vote x <;> simp [Nat.add_assoc]
  unfold uniformVotesMass
  rw [← (consTrials I fuel).sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [hp]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [pow_succ]
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem uniformVotesMass_eq_remaining {I : Type*} [Fintype I] [Nonempty I]
    (N : ℕ) (vote : I → Bool) (target : Bool) (fuel count : ℕ) :
    uniformVotesMass N vote target fuel count =
      remainingVoteMass N ((∑ x : I, if vote x = false then (1 : ℝ) else 0) / Fintype.card I)
        ((∑ x : I, if vote x = true then (1 : ℝ) else 0) / Fintype.card I) target fuel count := by
  induction fuel generalizing count with
  | zero => exact uniformVotesMass_zero N vote target count
  | succ fuel ih => rw [uniformVotesMass_succ, ih count, ih (count + 1)]; rfl

theorem independentMajorityMass_uniform {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t r : ℕ) (target : Bool) :
    independentMajorityMass M a input t r target =
      uniformVotesMass (2 * r + 1)
        (fun w : Fin t → Bool => (coinTapeRun M a input (List.ofFn w)).1 == some true)
        target (2 * r + 1) 0 := by
  unfold independentMajorityMass uniformVotesMass
  simp only [Nat.zero_add, trueCount_ofFn, MajorityBit, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]

theorem independentMajorityMass_recurrence {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t r : ℕ) (target : Bool)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none) :
    independentMajorityMass M a input t r target =
      remainingVoteMass (2 * r + 1) (fairTapeSuccess M a input t false)
        (fairTapeSuccess M a input t true) target (2 * r + 1) 0 := by
  rw [independentMajorityMass_uniform, uniformVotesMass_eq_remaining]
  have hp (b : Bool) :
      ((∑ w : Fin t → Bool,
        if ((coinTapeRun M a input (List.ofFn w)).1 == some true) = b then (1 : ℝ) else 0) /
          Fintype.card (Fin t → Bool)) = fairTapeSuccess M a input t b := by
    unfold fairTapeSuccess
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    simp only [source_vote_eq_target M a input (List.ofFn w) b (ht w)]
  rw [hp false, hp true]

theorem nativeRounds_fair_mass (r Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hB : (2 * r + 1) * (3 * input.length + 2 * t + 6) ≤ B) (target : Bool) :
    fairTapeSuccess (nativeRoundsTable (2 * r + 1) Q M a) (nativeRoundsAccept (2 * r + 1) Q)
      (tracksInput (2 * r + 1) input) B target = independentMajorityMass M a (input.map some) t r target := by
  let N := 2 * r + 1
  have hm := rounds_mass_from N Q M a hc input t ht target N 0 0 (by simp) (by simp)
    (Turing.Tape.mk₁ (tracksInput N input))
    (by intro k _; exact Or.inl (tracksInput_focus k input)) B hB
  have hi : fairCfgValue (roundsTable N Q M a) (fun cfg => if roundsAccept N Q cfg.q = target then 1 else 0)
      B (Turing.TM0.init (tracksInput N input)) =
      remainingVoteMass N (fairTapeSuccess M a (input.map some) t false)
        (fairTapeSuccess M a (input.map some) t true) target N 0 := by
    simpa only [roundsCfg, Turing.TM0.init, Fin.default_eq_zero] using! hm
  rw [fairCfgValue_initial] at hi
  have hn : fairTapeSuccess (nativeRoundsTable N Q M a) (nativeRoundsAccept N Q) (tracksInput N input) B target =
      fairTapeSuccess (roundsTable N Q M a) (roundsAccept N Q) (tracksInput N input) B target := by
    unfold fairTapeSuccess
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [(nativeRounds_run N Q M a input (List.ofFn w)).1]
  exact hn.trans
      (hi.trans (independentMajorityMass_recurrence M a (input.map some) t r target ht).symm)

theorem nativeRounds_amplification (r Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hB : (2 * r + 1) * (3 * input.length + 2 * t + 6) ≤ B) (target : Bool)
    (hp : (2 / 3 : ℝ) ≤ fairTapeSuccess M a (input.map some) t target) :
    1 - (8 / 9 : ℝ) ^ r ≤
      fairTapeSuccess (nativeRoundsTable (2 * r + 1) Q M a) (nativeRoundsAccept (2 * r + 1) Q)
        (tracksInput (2 * r + 1) input) B target := by
  rw [nativeRounds_fair_mass r Q M a hc input t ht B hB target]
  exact independentMajorityMass_ge M a (input.map some) t r target ht hp

theorem nativeRounds_majority_polynomial (r Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) (c k : ℕ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (htotal : ∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
      (coinTapeRun M a (input.map some) (List.ofFn w)).1 ≠ none) :
    ∃ d : ℕ, 0 < d ∧
      (∀ q s, (nativeRoundsTable (2 * r + 1) Q M a false q s = none) ↔
        (nativeRoundsTable (2 * r + 1) Q M a true q s = none)) ∧
      ∀ input : List Bool,
        let T := c * input.length ^ k + c
        let B := d * input.length ^ (2 * (k + 1)) + d
        (∀ w : Fin B → Bool,
          (coinTapeRun (nativeRoundsTable (2 * r + 1) Q M a) (nativeRoundsAccept (2 * r + 1) Q)
            (tracksInput (2 * r + 1) input) (List.ofFn w)).1 ≠ none) ∧
        (∀ w : Fin B → Bool,
          coinTapeTransitionCount (nativeRoundsTable (2 * r + 1) Q M a)
            (tracksInput (2 * r + 1) input) (List.ofFn w) ≤ B) ∧
        (∀ target : Bool,
          fairTapeSuccess (nativeRoundsTable (2 * r + 1) Q M a) (nativeRoundsAccept (2 * r + 1) Q)
            (tracksInput (2 * r + 1) input) B target = independentMajorityMass M a (input.map some) T r target) ∧
        (∀ target : Bool, (2 / 3 : ℝ) ≤ fairTapeSuccess M a (input.map some) T target →
          1 - (8 / 9 : ℝ) ^ r ≤
            fairTapeSuccess (nativeRoundsTable (2 * r + 1) Q M a) (nativeRoundsAccept (2 * r + 1) Q)
              (tracksInput (2 * r + 1) input) B target) := by
  let N := 2 * r + 1
  refine ⟨N * (4 * c + 10) + 1, by omega, nativeRounds_commonHalt N Q M a, ?_⟩
  intro input
  let T := c * input.length ^ k + c
  let B := (N * (4 * c + 10) + 1) * input.length ^ (2 * (k + 1)) + (N * (4 * c + 10) + 1)
  have hb : N * (3 * input.length + 2 * T + 6) ≤ B := rounds_poly_bound N c k input.length
  have hrun (w : Fin B → Bool) := nativeRounds_total N Q M a hc input T (htotal input)
    (List.ofFn w) (by simpa using! hb)
  refine ⟨fun w => (hrun w).1, ?_, ?_, ?_⟩
  · intro w
    have hw := hrun w
    exact hw.2.2.le.trans (hw.2.1.trans hb)
  · intro target
    exact nativeRounds_fair_mass r Q M a hc input T (htotal input) B hb target
  · intro target hp
    exact nativeRounds_amplification r Q M a hc input T (htotal input) B hb target hp

theorem bitBlock_length (N : ℕ) (s : TrackCell N) : (bitBlock N s).length = N + 3 := by
  simp [bitBlock]

theorem bitBlock_default (N : ℕ) : bitBlock N default = List.replicate (N + 3) none := by
  change none :: (List.ofFn (fun _ : Fin N => (none : Option Bool)) ++ List.replicate 2 none) =
    none :: List.replicate (N + 2) none
  rw [List.ofFn_const, ← List.replicate_add]

theorem expandedInput_length (N : ℕ) (input : List Bool) :
    (expandedInput N input).length = input.length * (N + 3) := by
  simp [expandedInput]

theorem expandWindow_push (N : ℕ) (raw : List Bool) (k : ℕ) :
    expandQueuePush (expandWindow N raw k) ((raw.map some).getD (N + 2 + k) none) =
      expandWindow N raw (k + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [expandQueuePush, Fin.snoc_last]
    simp only [expandWindow, Fin.val_last]
    congr 1
    omega
  · rw [expandQueuePush, Fin.snoc_castSucc]
    change (raw.map some).getD (k + (j.val + 1)) none = (raw.map some).getD (k + 1 + j.val) none
    congr 1
    omega

theorem expandWindow_zero (N : ℕ) (raw : List Bool) (k : ℕ) (hk : k < raw.length) :
    expandWindow N raw k 0 = some raw[k] := by
  unfold expandWindow
  simp only [Fin.val_zero, Nat.add_zero]
  rw [List.getD_eq_getElem _ _ (by simpa using! hk)]
  simp

theorem expandWindow_end (N : ℕ) (raw : List Bool) :
    ∀ i, expandWindow N raw raw.length i = none := by
  intro i
  unfold expandWindow
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
  rfl

theorem expandShiftTape_head (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) (k : ℕ) :
    (expandShiftTape N pre raw k).head = (raw.map some).getD (N + 2 + k) none := by
  change (((raw.map some).drop (N + 2 + k)).headI) = _
  have h (l : List (Option Bool)) : l.headI = l.headD none := by cases l <;> rfl
  rw [h, List.headD_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero,
    List.getD_eq_getElem?_getD]

theorem tape_write_move_right {Γ : Type*} [Inhabited Γ] (b : Γ) (L R : Turing.ListBlank Γ) :
    ((Turing.Tape.mk' L R).write b).move .right = Turing.Tape.mk' (L.cons b) R.tail := rfl

theorem expandShiftTape_write_move (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) (k : ℕ)
    (hk : k < raw.length) :
    ((expandShiftTape N pre raw k).write (expandWindow N raw k 0)).move .right =
      expandShiftTape N pre raw (k + 1) := by
  unfold expandShiftTape
  rw [tape_write_move_right, Turing.ListBlank.cons_mk, Turing.ListBlank.tail_mk, List.tail_drop]
  rw [List.take_succ_eq_append_getElem (by simpa using! hk)]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
    expandWindow_zero N raw k hk, List.getElem_map]
  congr 2

theorem expandShift_two_steps (N : ℕ) (first : Bool) (pre : List (Option Bool))
    (raw : List Bool) (k : ℕ) (hk : k < raw.length) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) 2 (expandShiftCfg N first pre raw k) =
      some (expandShiftCfg N first pre raw (k + 1)) := by
  have hn : ¬ (∀ i, expandWindow N raw k i = none) := by
    intro hn
    have h := hn 0
    rw [expandWindow_zero N raw k hk] at h
    cases h
  have hs : Turing.TM0.step (expandInputTable N) (expandShiftCfg N first pre raw k) =
      some ⟨(4, first, 0, expandQueuePush (expandWindow N raw k) (expandShiftTape N pre raw k).head),
        (expandShiftTape N pre raw k).write (expandWindow N raw k 0)⟩ := by
    simp [TM0_step_apply, expandInputTable, expandShiftCfg, hn, TM0StmtApply]
  change Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (1 + 1)
      (expandShiftCfg N first pre raw k) = _
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
  simp only [Option.bind_some, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one]
  have hm : Turing.TM0.step (expandInputTable N)
      ⟨(4, first, 0, expandQueuePush (expandWindow N raw k) (expandShiftTape N pre raw k).head),
        (expandShiftTape N pre raw k).write (expandWindow N raw k 0)⟩ =
      some (expandShiftCfg N first pre raw (k + 1)) := by
    simp only [TM0_step_apply, expandInputTable]
    change some (⟨(3, first, 0, expandQueuePush (expandWindow N raw k) (expandShiftTape N pre raw k).head),
      ((expandShiftTape N pre raw k).write (expandWindow N raw k 0)).move .right⟩ :
        Turing.TM0.Cfg (Option Bool) (ExpandState N)) = _
    rw [expandShiftTape_head, expandWindow_push, expandShiftTape_write_move N pre raw k hk]
    rfl
  exact hm

theorem expandShift_run_to_end (N : ℕ) (first : Bool) (pre : List (Option Bool))
    (raw : List Bool) (fuel k : ℕ) (hk : k + fuel = raw.length) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (2 * fuel) (expandShiftCfg N first pre raw k) =
      some (expandShiftCfg N first pre raw raw.length) := by
  induction fuel generalizing k with
  | zero =>
    have heq : k = raw.length := by omega
    subst k
    rfl
  | succ fuel ih =>
    have hlt : k < raw.length := by omega
    rw [show 2 * (fuel + 1) = 2 + 2 * fuel by omega,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, expandShift_two_steps N first pre raw k hlt]
    exact ih (k + 1) (by omega)

theorem expandShift_end_tape (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) :
    expandShiftTape N pre raw raw.length =
      Turing.Tape.mk' (Turing.ListBlank.mk ((raw.map some).reverse ++ pre.reverse))
        (Turing.ListBlank.mk []) := by
  unfold expandShiftTape
  rw [List.take_of_length_le (by simp), List.drop_eq_nil_of_le (by simp)]

theorem expandShift_stop_step (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) :
    Turing.TM0.step (expandInputTable N) (expandShiftCfg N first pre raw raw.length) =
      some ⟨(5, first, 0, expandWindow N raw raw.length),
        (expandShiftTape N pre raw raw.length).move .left⟩ := by
  have hh : (expandShiftTape N pre raw raw.length).head = none := by
    rw [expandShift_end_tape]
    rfl
  simp [TM0_step_apply, expandShiftCfg, expandInputTable, expandWindow_end, hh, TM0StmtApply]

theorem bitBlock_input (N : ℕ) (b : Bool) :
    bitBlock N (some b, fun _ => none, false) = some b :: List.replicate (N + 2) none := by
  change some b :: (List.ofFn (fun _ : Fin N => (none : Option Bool)) ++ List.replicate 2 none) = _
  rw [List.ofFn_const, ← List.replicate_add]

theorem tracksInput_bitBlocks (N : ℕ) (input : List Bool) :
    (tracksInput N input).flatMap (bitBlock N) = expandedInput N input := by
  simp [tracksInput, expandedInput, List.flatMap_map, bitBlock_input]

theorem expandBack_run (N : ℕ) (first : Bool) (fifo : ExpandQueue N)
    (leftData : List Bool) (preRev : List (Option Bool)) (R : Turing.ListBlank (Option Bool)) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (leftData.length + 1)
      ⟨(5, first, 0, fifo),
        (Turing.Tape.mk' (Turing.ListBlank.mk (leftData.map some ++ none :: preRev)) R).move .left⟩ =
      some ⟨(6, false, 0, fifo), Turing.Tape.mk' (Turing.ListBlank.mk (none :: preRev))
        (Turing.ListBlank.append (leftData.reverse.map some) R)⟩ := by
  induction leftData generalizing R with
  | nil =>
    change Turing.TM0.step (expandInputTable N)
      ⟨(5, first, 0, fifo), (Turing.Tape.mk' (Turing.ListBlank.mk (none :: preRev)) R).move .left⟩ = _
    have hh :
        ((Turing.Tape.mk' (Turing.ListBlank.mk (none :: preRev)) R).move .left).head = none := rfl
    simp [TM0_step_apply, expandInputTable, TM0StmtApply]
  | cons b bs ih =>
    have hstart : (Turing.Tape.mk' (Turing.ListBlank.mk ((b :: bs).map some ++ none :: preRev)) R).move .left =
        Turing.Tape.mk' (Turing.ListBlank.mk (bs.map some ++ none :: preRev)) (R.cons (some b)) := by
      simp [Turing.Tape.move_left_mk']
    rw [hstart]
    have hh : (Turing.Tape.mk' (Turing.ListBlank.mk (bs.map some ++ none :: preRev)) (R.cons (some b))).head =
        some b := by simp
    have hs : Turing.TM0.step (expandInputTable N)
        ⟨(5, first, 0, fifo), Turing.Tape.mk' (Turing.ListBlank.mk (bs.map some ++ none :: preRev)) (R.cons (some b))⟩ =
        some ⟨(5, first, 0, fifo),
          (Turing.Tape.mk' (Turing.ListBlank.mk (bs.map some ++ none :: preRev)) (R.cons (some b))).move .left⟩ := by
      simp [TM0_step_apply, expandInputTable, TM0StmtApply]
    rw [show (b :: bs).length + 1 = 1 + (bs.length + 1) by simp; omega,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
    simpa only [Option.bind_some, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      Turing.ListBlank.append_assoc, Turing.ListBlank.append] using! ih (R.cons (some b))

theorem insertSlots_length (N : ℕ) (first : Bool) : (insertSlots N first).length = N + 2 := by
  simp [insertSlots]

theorem insertSlots_getElem (N : ℕ) (first : Bool) (i : ℕ) (hi : i < N + 2) :
    (insertSlots N first)[i]'(by simpa only [insertSlots_length] using! hi) =
      if first && decide (i = N) then some true else none := by
  unfold insertSlots
  rw [List.getElem_ofFn]

theorem expandCapture_zero (N : ℕ) (raw : List Bool) : expandCapture N raw 0 = fun _ => none := by
  funext j
  simp [expandCapture]

theorem expandCapture_end (N : ℕ) (raw : List Bool) : expandCapture N raw (N + 2) = expandWindow N raw 0 := by
  funext j
  simp [expandCapture, expandWindow]

theorem expandCapture_update (N : ℕ) (raw : List Bool) (i : ℕ) (hi : i < N + 2) :
    Function.update (expandCapture N raw i) (⟨i, hi⟩ : Fin (N + 2)) ((raw.map some).getD i none) =
      expandCapture N raw (i + 1) := by
  funext j
  by_cases hji : j.val = i
  · have heq : j = (⟨i, hi⟩ : Fin (N + 2)) := Fin.ext hji
    subst j
    simp [expandCapture]
  · have hne : j ≠ (⟨i, hi⟩ : Fin (N + 2)) := by intro heq; exact hji (congrArg Fin.val heq)
    rw [Function.update_of_ne hne]
    have he : (j.val < i + 1) ↔ j.val < i := by omega
    simp only [expandCapture, he]

theorem expandGatherTape_head (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (i : ℕ) :
    (expandGatherTape N first pre raw i).head = (raw.map some).getD i none := by
  change (((raw.map some).drop i).headI) = _
  have h (l : List (Option Bool)) : l.headI = l.headD none := by cases l <;> rfl
  rw [h, List.headD_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_zero,
    List.getD_eq_getElem?_getD]

theorem expandGatherTape_write_move (N : ℕ) (first : Bool) (pre : List (Option Bool))
    (raw : List Bool) (i : ℕ) (hi : i < N + 2) :
    ((expandGatherTape N first pre raw i).write
      (if first && decide (i = N) then some true else none)).move .right =
      expandGatherTape N first pre raw (i + 1) := by
  unfold expandGatherTape
  rw [tape_write_move_right, Turing.ListBlank.cons_mk, Turing.ListBlank.tail_mk, List.tail_drop]
  rw [List.take_succ_eq_append_getElem (by simpa only [insertSlots_length] using! hi)]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      insertSlots_getElem N first i hi]
  rfl

theorem expandGather_two_steps (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool)
    (i : Fin (N + 3)) (hi : i.val < N + 2) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) 2 (expandGatherCfg N first pre raw i) =
      some (expandGatherCfg N first pre raw ⟨i.val + 1, by omega⟩) := by
  let T := expandGatherTape N first pre raw i.val
  let mark : Option Bool := if first && decide (i.val = N) then some true else none
  have hs : Turing.TM0.step (expandInputTable N) (expandGatherCfg N first pre raw i) =
      some ⟨(2, first, i, expandCapture N raw (i.val + 1)), T.write mark⟩ := by
    simp only [TM0_step_apply, expandGatherCfg, hi, ↓reduceIte, expandInputTable]
    change some (⟨(2, first, i, Function.update (expandCapture N raw i.val) ⟨i.val, hi⟩ T.head),
      T.write mark⟩ : Turing.TM0.Cfg (Option Bool) (ExpandState N)) = _
    rw [expandGatherTape_head, expandCapture_update]
  have hm : Turing.TM0.step (expandInputTable N)
      ⟨(2, first, i, expandCapture N raw (i.val + 1)), T.write mark⟩ =
      some (expandGatherCfg N first pre raw ⟨i.val + 1, by omega⟩) := by
    by_cases hn : i.val + 1 < N + 2
    · simp [TM0_step_apply, expandInputTable, hn, expandGatherCfg, TM0StmtApply, T, mark]
      simpa using! expandGatherTape_write_move N first pre raw i.val hi
    · simp [TM0_step_apply, expandInputTable, hn, expandGatherCfg, TM0StmtApply, T, mark]
      simpa using! expandGatherTape_write_move N first pre raw i.val hi
  change Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (1 + 1)
      (expandGatherCfg N first pre raw i) = _
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
  exact hm

theorem expandGather_end_cfg (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) :
    expandGatherCfg N first pre raw ⟨N + 2, by omega⟩ =
      expandShiftCfg N first (pre ++ insertSlots N first) raw 0 := by
  have ht : (insertSlots N first).take (N + 2) = insertSlots N first := by
    apply List.take_of_length_le
    rw [insertSlots_length]
  simp [expandGatherCfg, expandGatherTape, expandShiftCfg, expandShiftTape, expandCapture_end,
    ht, List.reverse_append]

theorem expandGather_run_to_end (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool)
    (fuel : ℕ) (i : Fin (N + 3)) (hi : i.val + fuel = N + 2) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (2 * fuel) (expandGatherCfg N first pre raw i) =
      some (expandShiftCfg N first (pre ++ insertSlots N first) raw 0) := by
  induction fuel generalizing i with
  | zero =>
    have heq : i = (⟨N + 2, by omega⟩ : Fin (N + 3)) := Fin.ext (by omega)
    change some (expandGatherCfg N first pre raw i) = _
    rw [heq]
    exact congrArg some (expandGather_end_cfg N first pre raw)
  | succ fuel ih =>
    have hlt : i.val < N + 2 := by omega
    rw [show 2 * (fuel + 1) = 2 + 2 * fuel by omega, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      expandGather_two_steps N first pre raw i hlt]
    apply ih ⟨i.val + 1, by omega⟩
    change i.val + 1 + fuel = N + 2
    omega

theorem insertSlots_separator (N : ℕ) (first : Bool) :
    insertSlots N first = (insertSlots N first).take (N + 1) ++ [none] := by
  have hlt : N + 1 < (insertSlots N first).length := by rw [insertSlots_length]; omega
  have hlast : (insertSlots N first)[N + 1] = none := by
    rw [insertSlots_getElem N first (N + 1) (by omega)]
    simp
  rw [← hlast, ← List.take_succ_eq_append_getElem hlt]
  exact (List.take_of_length_le (by rw [insertSlots_length])).symm

theorem expandShift_back_run (N : ℕ) (first : Bool) (preBody : List (Option Bool)) (raw : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (3 * raw.length + 2)
      (expandShiftCfg N first (preBody ++ [none]) raw 0) =
      some (expandCheckCfg N (preBody ++ [none]) raw) := by
  have hs := expandShift_run_to_end N first (preBody ++ [none]) raw raw.length 0 (by simp)
  have hb := expandBack_run N first (expandWindow N raw raw.length) raw.reverse preBody.reverse
    (Turing.ListBlank.mk [])
  have hentry : (Turing.Tape.mk' (Turing.ListBlank.mk (raw.reverse.map some ++ none :: preBody.reverse))
        (Turing.ListBlank.mk [])).move .left =
      (expandShiftTape N (preBody ++ [none]) raw raw.length).move .left := by
    rw [expandShift_end_tape]
    simp [List.reverse_append, List.map_reverse]
  rw [hentry] at hb
  have hend : (⟨(6, false, 0, expandWindow N raw raw.length),
      Turing.Tape.mk' (Turing.ListBlank.mk (none :: preBody.reverse))
        (Turing.ListBlank.append (raw.reverse.reverse.map some) (Turing.ListBlank.mk []))⟩ :
        Turing.TM0.Cfg (Option Bool) (ExpandState N)) = expandCheckCfg N (preBody ++ [none]) raw := by
    have hq : expandWindow N raw raw.length = fun _ => none := funext (expandWindow_end N raw)
    simp [expandCheckCfg, hq, Turing.ListBlank.append_mk, List.reverse_append]
  rw [hend] at hb
  rw [show 3 * raw.length + 2 = 2 * raw.length + (1 + (raw.length + 1)) by omega,
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hs]
  simp only [Option.bind_some]
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, expandShift_stop_step]
  simpa only [Option.bind_some, List.length_reverse] using! hb

theorem expandInsert_from_gather (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (2 * (N + 2) + (3 * raw.length + 2))
      (expandGatherCfg N first pre raw 0) = some (expandCheckCfg N (pre ++ insertSlots N first) raw) := by
  have hg := expandGather_run_to_end N first pre raw (N + 2) 0 (by simp)
  have hpre : pre ++ insertSlots N first = (pre ++ (insertSlots N first).take (N + 1)) ++ [none] := by
    calc
      _ = pre ++ ((insertSlots N first).take (N + 1) ++ [none]) :=
        congrArg (fun xs => pre ++ xs) (insertSlots_separator N first)
      _ = _ := by rw [List.append_assoc]
  have hb := expandShift_back_run N first (pre ++ (insertSlots N first).take (N + 1)) raw
  rw [← hpre] at hb
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hg]
  exact hb

theorem insertSlots_false (N : ℕ) : insertSlots N false = List.replicate (N + 2) none := by
  simp [insertSlots, List.replicate_succ]

theorem expandProcess_one (N : ℕ) (pre : List (Option Bool)) (b : Bool) (raw : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (2 * (N + 2) + 3 * raw.length + 3)
      (expandCheckCfg N pre (b :: raw)) =
      some (expandCheckCfg N (pre ++ (some b :: List.replicate (N + 2) none)) raw) := by
  have hs : Turing.TM0.step (expandInputTable N) (expandCheckCfg N pre (b :: raw)) =
      some (expandGatherCfg N false (pre ++ [some b]) raw 0) := by
    simp [TM0_step_apply, expandInputTable, expandCheckCfg, expandGatherCfg, expandGatherTape,
      expandCapture_zero, TM0StmtApply, Turing.Tape.move_right_mk', List.reverse_append]
  have hg := expandInsert_from_gather N false (pre ++ [some b]) raw
  rw [insertSlots_false] at hg
  rw [show 2 * (N + 2) + 3 * raw.length + 3 = 1 + (2 * (N + 2) + (3 * raw.length + 2)) by omega,
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
  simpa only [Option.bind_some, List.append_assoc, List.singleton_append] using! hg

theorem expandProcess_all (N : ℕ) (raw : List Bool) (pre : List (Option Bool)) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (expandProcessTime N raw.length)
      (expandCheckCfg N pre raw) = some (expandCheckCfg N (pre ++ expandedInput N raw) []) := by
  induction raw generalizing pre with
  | nil => simp [expandProcessTime, expandedInput, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom]
  | cons b bs ih =>
    change Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N)
      ((2 * (N + 2) + 3 * bs.length + 3) + expandProcessTime N bs.length)
      (expandCheckCfg N pre (b :: bs)) = _
    rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, expandProcess_one]
    simpa only [Option.bind_some, expandedInput, List.flatMap_cons, List.append_assoc] using!
      ih (pre ++ some b :: List.replicate (N + 2) none)

theorem expandProcessTime_exact (N n : ℕ) :
    2 * expandProcessTime N n = n * (4 * N + 11 + 3 * n) := by
  induction n with
  | zero => simp [expandProcessTime]
  | succ n ih =>
    simp only [expandProcessTime]
    nlinarith

theorem expandRaw_first_step (N : ℕ) (b : Bool) (raw : List Bool) :
    Turing.TM0.step (expandInputTable N) (Turing.TM0.init ((b :: raw).map some)) =
      some (expandGatherCfg N true [some b] raw 0) := by
  have hz : (default : ExpandState N).1 = 0 := rfl
  simp [TM0_step_apply, Turing.TM0.init, expandInputTable, expandGatherCfg, expandGatherTape,
    expandCapture_zero, TM0StmtApply, Turing.Tape.mk₁, Turing.Tape.mk₂, hz, Turing.Tape.move_right_mk']

theorem expandRaw_processed (N : ℕ) (b : Bool) (raw : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (expandProcessTime N (b :: raw).length)
      (Turing.TM0.init ((b :: raw).map some)) =
      some (expandCheckCfg N (markedExpandedInput N b raw) []) := by
  have hg := expandInsert_from_gather N true [some b] raw
  have hp := expandProcess_all N raw ([some b] ++ insertSlots N true)
  have hclock : expandProcessTime N (b :: raw).length =
      1 + ((2 * (N + 2) + (3 * raw.length + 2)) + expandProcessTime N raw.length) := by
    (try simp only [expandProcessTime, List.length_cons])
    omega
  rw [hclock, Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, expandRaw_first_step]
  simp only [Option.bind_some]
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hg]
  simpa only [Option.bind_some, markedExpandedInput, List.singleton_append] using! hp

theorem expandRaw_empty (N : ℕ) :
    Turing.TM0.step (expandInputTable N) (Turing.TM0.init []) = none := by
  rfl

theorem expandQueueLabels_zero (N : ℕ) : expandQueueLabels N (fun _ => none) = 0 := by
  apply Fin.ext
  simp [expandQueueLabels, optionBoolFin, symbolIndex]

theorem expandLabels_zero (N : ℕ) : expandLabels N (0, false, 0, fun _ => none) = 0 := by
  apply Fin.ext
  simp [expandLabels, expandQueueLabels_zero, finProdFinEquiv, Equiv.prodCongr, finTwoEquiv]

theorem nativeExpand_run (N : ℕ) (input : List (Option Bool)) (coins : List Bool) :
    coinTapeRun (fun _ => nativeExpandTable N) (fun _ => false) input coins =
      coinTapeRun (fun _ => expandInputTable N) (fun _ => false) input coins ∧
    coinTapeTransitionCount (fun _ => nativeExpandTable N) input coins =
      coinTapeTransitionCount (fun _ => expandInputTable N) input coins := by
  have hz : expandLabels N (default : ExpandState N) = 0 := by
    simpa only [Fin.default_eq_zero] using! expandLabels_zero N
  exact relabel_run (expandLabels N) hz (fun _ => expandInputTable N) (fun _ => false) coins input

theorem expandCode_run (N : ℕ) (input : List (Option Bool)) (coins : List Bool) :
    coinTapeRun (table (expandCode N)) (readout (expandCode N)) input coins =
      coinTapeRun (fun _ => expandInputTable N) (fun _ => false) input coins ∧
    coinTapeTransitionCount (table (expandCode N)) input coins =
      coinTapeTransitionCount (fun _ => expandInputTable N) input coins := by
  have h :=
      encodeMachine_run (expandControlMax N) (fun _ => nativeExpandTable N)
      (fun _ => false) input coins
  exact ⟨h.1.trans (nativeExpand_run N input coins).1, h.2.trans (nativeExpand_run N input coins).2⟩

theorem nativeExpand_raw_processed (N : ℕ) (b : Bool) (raw : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (nativeExpandTable N) (expandProcessTime N (b :: raw).length)
      (Turing.TM0.init ((b :: raw).map some)) =
      some (mapCfg (expandLabels N) (expandCheckCfg N (markedExpandedInput N b raw) [])) := by
  have h := runFrom_map_success (expandInputTable N) (nativeExpandTable N) (expandLabels N)
    (fun cfg cfg' hs => by
      change Turing.TM0.step (relabelTable (expandLabels N) (fun _ => expandInputTable N) false)
        (relabelCfg (expandLabels N) cfg) = some (relabelCfg (expandLabels N) cfg')
      rw [relabel_step, hs]
      rfl) (expandProcessTime N (b :: raw).length) (Turing.TM0.init ((b :: raw).map some))
    (expandCheckCfg N (markedExpandedInput N b raw) []) (expandRaw_processed N b raw)
  have hz : expandLabels N (default : ExpandState N) = 0 := by
    simpa only [Fin.default_eq_zero] using! expandLabels_zero N
  have hi : mapCfg (expandLabels N) (Turing.TM0.init ((b :: raw).map some)) =
      Turing.TM0.init ((b :: raw).map some) := by
    change (⟨expandLabels N default, Turing.Tape.mk₁ ((b :: raw).map some)⟩ :
      Turing.TM0.Cfg (Option Bool) (Fin (expandControlMax N + 1))) = _
    rw [hz]
    rfl
  rw [hi] at h
  exact h

theorem expandJump_run (N : ℕ) (n : ℕ) (hn : 0 < n) (hb : n < N + 3)
    (fifo : ExpandQueue N) (T : Turing.Tape (Option Bool)) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) n ⟨(9, false, ⟨n, hb⟩, fifo), T⟩ =
      some ⟨(8, false, 0, fifo), (Turing.Tape.move .left)^[n] T⟩ := by
  induction n generalizing T with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      change Turing.TM0.step (expandInputTable N) ⟨(9, false, ⟨1, hb⟩, fifo), T⟩ = _
      simp [TM0_step_apply, expandInputTable, TM0StmtApply]
    | succ n =>
      have hs : Turing.TM0.step (expandInputTable N) ⟨(9, false, ⟨n + 1 + 1, hb⟩, fifo), T⟩ =
          some ⟨(9, false, ⟨n + 1, by omega⟩, fifo), T.move .left⟩ := by
        simp [TM0_step_apply, expandInputTable, TM0StmtApply, show 1 < n + 1 + 1 by omega]
      have ht := ih (by omega) (by omega) (T.move .left)
      conv_lhs => arg 2; rw [show n + 1 + 1 = 1 + (n + 1) by omega]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
      simpa only [Option.bind_some, Function.iterate_succ_apply] using! ht

theorem expandOrigin_run (N : ℕ) (n : ℕ) (hn : 0 < n) (hb : n < N + 3)
    (fifo : ExpandQueue N) (T : Turing.Tape (Option Bool)) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) n ⟨(10, false, ⟨n, hb⟩, fifo), T⟩ =
      some ⟨(11, false, 0, fifo), (Turing.Tape.move .left)^[n] T⟩ := by
  induction n generalizing T with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      change Turing.TM0.step (expandInputTable N) ⟨(10, false, ⟨1, hb⟩, fifo), T⟩ = _
      simp [TM0_step_apply, expandInputTable, TM0StmtApply]
    | succ n =>
      have hs : Turing.TM0.step (expandInputTable N) ⟨(10, false, ⟨n + 1 + 1, hb⟩, fifo), T⟩ =
          some ⟨(10, false, ⟨n + 1, by omega⟩, fifo), T.move .left⟩ := by
        simp [TM0_step_apply, expandInputTable, TM0StmtApply, show 1 < n + 1 + 1 by omega]
      have ht := ih (by omega) (by omega) (T.move .left)
      conv_lhs => arg 2; rw [show n + 1 + 1 = 1 + (n + 1) by omega]
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
        Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
      simpa only [Option.bind_some, Function.iterate_succ_apply] using! ht

theorem tape_right_append {Γ : Type*} [Inhabited Γ] (l : List Γ) (L R : Turing.ListBlank Γ) :
    (Turing.Tape.move .right)^[l.length] (Turing.Tape.mk' L (Turing.ListBlank.append l R)) =
      Turing.Tape.mk' (Turing.ListBlank.append l.reverse L) R := by
  induction l generalizing L with
  | nil => rfl
  | cons b bs ih =>
    simpa only [List.length_cons, Function.iterate_succ_apply, Turing.ListBlank.append,
      Turing.Tape.move_right_mk', Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      List.reverse_cons, Turing.ListBlank.append_assoc] using! ih (L.cons b)

theorem tape_left_right_iterate {Γ : Type*} [Inhabited Γ] (n : ℕ) (T : Turing.Tape Γ) :
    (Turing.Tape.move .left)^[n] ((Turing.Tape.move .right)^[n] T) = T := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', Turing.Tape.move_right_left]
    exact ih T

theorem tapeAt_back (l : List (Option Bool)) (n d : ℕ) :
    (Turing.Tape.move .left)^[d] (tapeAt l (n + d)) = tapeAt l n := by
  unfold tapeAt
  rw [Nat.add_comm n d, Function.iterate_add_apply]
  exact tape_left_right_iterate d _

theorem tapeAt_head (l : List (Option Bool)) (n : ℕ) : (tapeAt l n).head = l.getD n none := by
  unfold tapeAt
  rw [Turing.Tape.move_right_n_head]
  change ((Turing.TM0.init l : Turing.TM0.Cfg (Option Bool) (Fin 1)).Tape.nth (n : ℤ)) = _
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.init_nth]
  rw [if_neg (by omega : ¬ (n : ℤ) < 0)]
  simp only [Int.toNat_natCast, List.getI_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem tapeAt_append (left right : List (Option Bool)) :
    tapeAt (left ++ right) left.length =
      Turing.Tape.mk' (Turing.ListBlank.mk left.reverse) (Turing.ListBlank.mk right) := by
  have h := tape_right_append left (Turing.ListBlank.mk []) (Turing.ListBlank.mk right)
  simpa only [Turing.ListBlank.append_mk, List.append_nil, Turing.Tape.mk₁, Turing.Tape.mk₂] using!
      h

theorem tapeAt_end (l : List (Option Bool)) :
    tapeAt l l.length = Turing.Tape.mk' (Turing.ListBlank.mk l.reverse) (Turing.ListBlank.mk []) := by
  simpa only [List.append_nil] using! tapeAt_append l []

theorem insertSlots_true_prefix (N : ℕ) :
    (insertSlots N true).take N = List.replicate N none := by
  apply List.ext_getElem
  · simp [List.length_take, insertSlots_length]
  · intro i hi hj
    have hin : i < N := by simpa using! hj
    rw [List.getElem_take]
    rw [insertSlots_getElem N true i (by omega)]
    simp [show i ≠ N by omega]

theorem insertSlots_true (N : ℕ) :
    insertSlots N true = List.replicate N none ++ [some true, none] := by
  have hn : N < (insertSlots N true).length := by rw [insertSlots_length]; omega
  have hp : (insertSlots N true).take (N + 1) = List.replicate N none ++ [some true] := by
    rw [List.take_succ_eq_append_getElem hn, insertSlots_true_prefix,
      insertSlots_getElem N true N (by omega)]
    simp
  have hs := insertSlots_separator N true
  rw [hp] at hs
  simpa only [List.append_assoc, List.singleton_append] using! hs

theorem expandedInput_home (N : ℕ) (raw : List Bool) (j : ℕ) :
    (expandedInput N raw).getD (j * (N + 3) + (N + 1)) none = none := by
  induction raw generalizing j with
  | nil => rfl
  | cons b bs ih =>
    change ((some b :: List.replicate (N + 2) none) ++ expandedInput N bs).getD
      (j * (N + 3) + (N + 1)) none = none
    cases j with
    | zero =>
      rw [List.getD_append _ _ _ _ (by simp)]
      simp
    | succ j =>
      rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have hn : (j + 1) * (N + 3) + (N + 1) - (some b :: List.replicate (N + 2) none).length =
          j * (N + 3) + (N + 1) := by
        simp only [List.length_cons, List.length_replicate]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [hn]
      exact ih j

theorem markedExpandedInput_home (N : ℕ) (b : Bool) (raw : List Bool) (j : ℕ) :
    (markedExpandedInput N b raw).getD (j * (N + 3) + (N + 1)) none =
      if j = 0 then some true else none := by
  unfold markedExpandedInput
  cases j with
  | zero =>
    rw [List.getD_append _ _ _ _ (by simp [insertSlots_length])]
    simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by rw [insertSlots_length]; omega),
        insertSlots_getElem N true N (by omega)]
    simp
  | succ j =>
    rw [List.getD_append_right _ _ _ _ (by simp [insertSlots_length]; nlinarith)]
    have hn : (j + 1) * (N + 3) + (N + 1) - (some b :: insertSlots N true).length =
        j * (N + 3) + (N + 1) := by
      simp only [List.length_cons, insertSlots_length]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hn, expandedInput_home]
    simp

theorem markedExpandedInput_layout (N : ℕ) (b : Bool) (raw : List Bool) :
    markedExpandedInput N b raw = (some b :: List.replicate N none) ++ some true :: none :: expandedInput N raw := by
  simp [markedExpandedInput, insertSlots_true, List.append_assoc]

theorem expandedInput_layout (N : ℕ) (b : Bool) (raw : List Bool) :
    expandedInput N (b :: raw) = (some b :: List.replicate N none) ++ none :: none :: expandedInput N raw := by
  simp [expandedInput, List.replicate_add, List.append_assoc]

theorem expandedInput_clear_marker (N : ℕ) (b : Bool) (raw : List Bool) :
    (tapeAt (markedExpandedInput N b raw) (N + 1)).write none =
      tapeAt (expandedInput N (b :: raw)) (N + 1) := by
  have hm : tapeAt (markedExpandedInput N b raw) (N + 1) =
      Turing.Tape.mk' (Turing.ListBlank.mk (some b :: List.replicate N none).reverse)
        (Turing.ListBlank.mk (some true :: none :: expandedInput N raw)) := by
    rw [markedExpandedInput_layout]
    convert! tapeAt_append (some b :: List.replicate N none) (some true :: none :: expandedInput N raw) using 1
    simp
  have hc : tapeAt (expandedInput N (b :: raw)) (N + 1) =
      Turing.Tape.mk' (Turing.ListBlank.mk (some b :: List.replicate N none).reverse)
        (Turing.ListBlank.mk (none :: none :: expandedInput N raw)) := by
    rw [expandedInput_layout]
    convert! tapeAt_append (some b :: List.replicate N none) (none :: none :: expandedInput N raw) using 1
    simp
  rw [hm, hc]
  rfl

theorem expandClear_origin_run (N : ℕ) (b : Bool) (raw : List Bool) (fifo : ExpandQueue N) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (N + 2)
      ⟨(8, false, 0, fifo), tapeAt (markedExpandedInput N b raw) (N + 1)⟩ =
      some ⟨(11, false, 0, fifo), Turing.Tape.mk₁ (expandedInput N (b :: raw))⟩ := by
  have hh : (tapeAt (markedExpandedInput N b raw) (N + 1)).head = some true := by
    rw [tapeAt_head]
    simpa using! markedExpandedInput_home N b raw 0
  have hs : Turing.TM0.step (expandInputTable N)
      ⟨(8, false, 0, fifo), tapeAt (markedExpandedInput N b raw) (N + 1)⟩ =
      some ⟨(10, false, ⟨N + 1, by omega⟩, fifo),
        (tapeAt (markedExpandedInput N b raw) (N + 1)).write none⟩ := by
    simp [TM0_step_apply, expandInputTable, hh, TM0StmtApply]
  have ho := expandOrigin_run N (N + 1) (by omega) (by omega) fifo
    ((tapeAt (markedExpandedInput N b raw) (N + 1)).write none)
  rw [expandedInput_clear_marker] at ho
  have hback : (Turing.Tape.move .left)^[N + 1] (tapeAt (expandedInput N (b :: raw)) (N + 1)) =
      Turing.Tape.mk₁ (expandedInput N (b :: raw)) := by
    simpa only [Nat.zero_add, tapeAt, Function.iterate_zero_apply] using!
        tapeAt_back (expandedInput N (b :: raw)) 0 (N + 1)
  rw [hback] at ho
  conv_lhs => arg 2; rw [show N + 2 = 1 + (N + 1) by omega]
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
  simpa only [Option.bind_some, expandedInput_clear_marker] using! ho

theorem expandHome_previous (N : ℕ) (b : Bool) (raw : List Bool) (j : ℕ) (fifo : ExpandQueue N) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (N + 3)
      ⟨(8, false, 0, fifo), tapeAt (markedExpandedInput N b raw) ((j + 1) * (N + 3) + (N + 1))⟩ =
      some ⟨(8, false, 0, fifo), tapeAt (markedExpandedInput N b raw) (j * (N + 3) + (N + 1))⟩ := by
  let T := tapeAt (markedExpandedInput N b raw) ((j + 1) * (N + 3) + (N + 1))
  have hh : T.head = none := by rw [tapeAt_head, markedExpandedInput_home]; simp
  have hs : Turing.TM0.step (expandInputTable N) ⟨(8, false, 0, fifo), T⟩ =
      some ⟨(9, false, ⟨N + 2, by omega⟩, fifo), T.move .left⟩ := by
    simp [TM0_step_apply, expandInputTable, hh, TM0StmtApply]
  have hj := expandJump_run N (N + 2) (by omega) (by omega) fifo (T.move .left)
  have hmove : (Turing.Tape.move .left)^[N + 3] T =
      tapeAt (markedExpandedInput N b raw) (j * (N + 3) + (N + 1)) := by
    have hindex : (j + 1) * (N + 3) + (N + 1) = (j * (N + 3) + (N + 1)) + (N + 3) := by ring
    dsimp [T]
    rw [hindex]
    simpa only [Function.iterate_succ_apply] using!
      tapeAt_back (markedExpandedInput N b raw) (j * (N + 3) + (N + 1)) (N + 3)
  have hmove' : (Turing.Tape.move .left)^[N + 2] (T.move .left) =
      tapeAt (markedExpandedInput N b raw) (j * (N + 3) + (N + 1)) := by
    simpa only [Function.iterate_succ_apply] using! hmove
  rw [hmove'] at hj
  conv_lhs => arg 2; rw [show N + 3 = 1 + (N + 2) by omega]
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
  exact hj

theorem expandHome_scan (N : ℕ) (b : Bool) (raw : List Bool) (j : ℕ) (fifo : ExpandQueue N) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (j * (N + 3) + (N + 2))
      ⟨(8, false, 0, fifo), tapeAt (markedExpandedInput N b raw) (j * (N + 3) + (N + 1))⟩ =
      some ⟨(11, false, 0, fifo), Turing.Tape.mk₁ (expandedInput N (b :: raw))⟩ := by
  induction j with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add] using! expandClear_origin_run N b raw fifo
  | succ j ih =>
    conv_lhs => arg 2; rw [show (j + 1) * (N + 3) + (N + 2) = (N + 3) + (j * (N + 3) + (N + 2)) by ring]
    rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, expandHome_previous]
    exact ih

theorem markedExpandedInput_length (N : ℕ) (b : Bool) (raw : List Bool) :
    (markedExpandedInput N b raw).length = (raw.length + 1) * (N + 3) := by
  simp only [markedExpandedInput, List.length_append, List.length_cons, insertSlots_length,
      expandedInput_length]
  ring

theorem expandRaw_return (N : ℕ) (b : Bool) (raw : List Bool) :
    Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) ((raw.length + 1) * (N + 3) + 1)
      (expandCheckCfg N (markedExpandedInput N b raw) []) =
      some ⟨(11, false, 0, fun _ => none), Turing.Tape.mk₁ (expandedInput N (b :: raw))⟩ := by
  let P := markedExpandedInput N b raw
  let T := (expandCheckCfg N P []).Tape
  have hh : T.head = none := rfl
  have hs : Turing.TM0.step (expandInputTable N) (expandCheckCfg N P []) =
      some ⟨(7, false, 0, fun _ => none), T.move .left⟩ := by
    change Turing.TM0.step (expandInputTable N) ⟨(6, false, 0, fun _ => none), T⟩ = _
    simp [TM0_step_apply, expandInputTable, hh, TM0StmtApply]
  have hm : Turing.TM0.step (expandInputTable N)
      ⟨(7, false, 0, fun _ => none), T.move .left⟩ =
      some ⟨(8, false, 0, fun _ => none), (T.move .left).move .left⟩ := by
    simp [TM0_step_apply, expandInputTable, TM0StmtApply]
  have ht : T = tapeAt P P.length := (tapeAt_end P).symm
  have hindex : P.length = (raw.length * (N + 3) + (N + 1)) + 2 := by
    dsimp [P]
    rw [markedExpandedInput_length]
    ring
  have hback : (T.move .left).move .left = tapeAt P (raw.length * (N + 3) + (N + 1)) := by
    change (Turing.Tape.move .left)^[2] T = _
    rw [ht, hindex]
    exact tapeAt_back _ _ _
  have hscan := expandHome_scan N b raw raw.length (fun _ => none)
  have hclock : (raw.length + 1) * (N + 3) + 1 = 1 + (1 + (raw.length * (N + 3) + (N + 2))) := by
    ring
  conv_lhs => arg 2; rw [hclock]
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hs]
  simp only [Option.bind_some]
  rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_one, hm]
  simpa only [Option.bind_some, hback] using! hscan

theorem expandRaw_run (N : ℕ) (input : List Bool) :
    ∃ q : ExpandState N,
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (expandTime N input.length)
        (Turing.TM0.init (input.map some)) = some ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ ∧
      Turing.TM0.step (expandInputTable N) ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ = none := by
  cases input with
  | nil =>
    refine ⟨default, ?_, expandRaw_empty N⟩
    rfl
  | cons b bs =>
    have hi := expandRaw_processed N b bs
    change Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N) (expandProcessTime N (bs.length + 1))
      (Turing.TM0.init ((b :: bs).map some)) = _ at hi
    have hr := expandRaw_return N b bs
    refine ⟨(11, false, 0, fun _ => none), ?_, ?_⟩
    · change Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (expandInputTable N)
        (expandProcessTime N (bs.length + 1) + ((bs.length + 1) * (N + 3) + 1)) _ = _
      rw [Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom_add, hi]
      exact hr
    · simp [TM0_step_apply, expandInputTable]

theorem expandTime_exact (N n : ℕ) :
    2 * expandTime N (n + 1) = (n + 1) * (6 * N + 17 + 3 * (n + 1)) + 2 := by
  have h := expandProcessTime_exact N (n + 1)
  simp only [expandTime]
  nlinarith

theorem expandTime_poly_bound (N n : ℕ) :
    expandTime N n ≤ (3 * N + 13) * n ^ 2 + (3 * N + 13) := by
  cases n with
  | zero => simp [expandTime]
  | succ n =>
    have ht := expandTime_exact N n
    have hn : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul_left (6 * N + 17) hn
    nlinarith [Nat.zero_le ((n + 1) ^ 2)]

theorem expandRaw_coin_run (N : ℕ) (input : List Bool) (coins : List Bool)
    (hlen : expandTime N input.length ≤ coins.length) :
    coinTapeRun (fun _ => expandInputTable N) (fun _ => false) (input.map some) coins =
      (some false, expandTime N input.length) ∧
    coinTapeTransitionCount (fun _ => expandInputTable N) (input.map some) coins =
      expandTime N input.length := by
  obtain ⟨q, hr, hh⟩ := expandRaw_run N input
  exact runFrom_coin_constant (expandInputTable N) (fun _ => false) (expandTime N input.length)
    (Turing.TM0.init (input.map some)) ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ coins hr hh hlen

theorem expandCode_coin_run (N : ℕ) (input : List Bool) (coins : List Bool)
    (hlen : expandTime N input.length ≤ coins.length) :
    coinTapeRun (table (expandCode N)) (readout (expandCode N)) (input.map some) coins =
      (some false, expandTime N input.length) ∧
    coinTapeTransitionCount (table (expandCode N)) (input.map some) coins =
      expandTime N input.length := by
  have h := expandCode_run N (input.map some) coins
  have hr := expandRaw_coin_run N input coins hlen
  exact ⟨h.1.trans hr.1, h.2.trans hr.2⟩

theorem expandCode_polynomial (N : ℕ) :
    ∃ c : ℕ, 0 < c ∧ ∀ input : List Bool,
      let B := c * input.length ^ 2 + c
      ∀ w : Fin B → Bool,
        coinTapeRun (table (expandCode N)) (readout (expandCode N)) (input.map some) (List.ofFn w) =
          (some false, expandTime N input.length) ∧
        coinTapeTransitionCount (table (expandCode N)) (input.map some) (List.ofFn w) ≤ B := by
  refine ⟨3 * N + 13, by omega, ?_⟩
  intro input
  (try dsimp only)
  intro w
  have hb := expandTime_poly_bound N input.length
  have h := expandCode_coin_run N input (List.ofFn w) (by simpa using! hb)
  exact ⟨h.1, h.2.le.trans hb⟩

theorem nativeExpand_full_run (N : ℕ) (input : List Bool) :
    ∃ q : Fin (expandControlMax N + 1),
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (nativeExpandTable N) (expandTime N input.length)
        (Turing.TM0.init (input.map some)) = some ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ ∧
      Turing.TM0.step (nativeExpandTable N) ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ = none := by
  obtain ⟨q, hr, hh⟩ := expandRaw_run N input
  have h := runFrom_map_success (expandInputTable N) (nativeExpandTable N) (expandLabels N)
    (fun cfg cfg' hs => by
      change Turing.TM0.step (relabelTable (expandLabels N) (fun _ => expandInputTable N) false)
        (relabelCfg (expandLabels N) cfg) = some (relabelCfg (expandLabels N) cfg')
      rw [relabel_step, hs]
      rfl) (expandTime N input.length) (Turing.TM0.init (input.map some))
    ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ hr
  have hz : expandLabels N (default : ExpandState N) = 0 := by
    simpa only [Fin.default_eq_zero] using! expandLabels_zero N
  have hi : mapCfg (expandLabels N) (Turing.TM0.init (input.map some)) = Turing.TM0.init (input.map some) := by
    change (⟨expandLabels N default, Turing.Tape.mk₁ (input.map some)⟩ :
      Turing.TM0.Cfg (Option Bool) (Fin (expandControlMax N + 1))) = _
    rw [hz]
    rfl
  rw [hi] at h
  have hs := relabel_step (expandLabels N) (fun _ => expandInputTable N) false
    ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩
  rw [hh] at hs
  exact ⟨expandLabels N q, h, hs⟩

theorem expandCode_full_run (N : ℕ) (input : List Bool) :
    ∃ q : Fin (controlSize (expandCode N) + 1),
      Qatlib.Concepts.ClassicalTape.TapeCompilation.runFrom (table (expandCode N) false) (expandTime N input.length)
        (Turing.TM0.init (input.map some)) = some ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ ∧
      Turing.TM0.step (table (expandCode N) false) ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ = none := by
  simpa only [expandCode, table_encode] using! nativeExpand_full_run N input

theorem expandCode_commonHalt (N : ℕ) : commonHalt (expandCode N) := by
  unfold commonHalt
  simp only [expandCode, table_encode]
  intro q s
  exact True.intro

theorem expandCode_stopped (N : ℕ) (input : List Bool) (coins : List Bool)
    (hlen : expandTime N input.length ≤ coins.length) :
    ∃ q : Fin (controlSize (expandCode N) + 1),
      let r := coinConfigRunAux (table (expandCode N)) coins (Turing.TM0.init (input.map some))
      r.stopped = some ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ ∧
      r.reads = expandTime N input.length ∧ r.transitions = expandTime N input.length := by
  obtain ⟨q, hr, hh⟩ := nativeExpand_full_run N input
  have h := coinConfigRunAux_const (nativeExpandTable N) (expandTime N input.length)
    (Turing.TM0.init (input.map some)) ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ coins hr hh hlen
  simpa only [expandCode, table_encode] using! Exists.intro q h

theorem expandCode_then_coin_source {Λ : Type*} [Inhabited Λ]
    (N : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (input : List Bool)
    (front : Fin (expandTime N input.length) → Bool) (switch : Bool) (tail : List Bool) :
    let r := coinConfigRunAux M tail ⟨default, Turing.Tape.mk₁ (expandedInput N input)⟩
    let total := coinConfigRunAux (sequenceCoinTable (table (expandCode N)) M)
      (List.ofFn front ++ switch :: tail) (mapCfg Sum.inl (Turing.TM0.init (input.map some)))
    total.stopped = r.stopped.map (mapCfg Sum.inr) ∧
      total.reads = r.reads + expandTime N input.length + 1 ∧
      total.transitions = r.transitions + expandTime N input.length + 1 := by
  obtain ⟨q, hs, hr, _⟩ := expandCode_stopped N input (List.ofFn front) (by simp)
  have h := sequence_coinConfig_left (table (expandCode N)) M (expandCode_commonHalt N)
    (List.ofFn front) tail switch (Turing.TM0.init (input.map some))
    ⟨q, Turing.Tape.mk₁ (expandedInput N input)⟩ hs (by simpa only [List.length_ofFn] using! hr)
  simpa only [List.length_ofFn] using! h

theorem expandCode_fair_value {Λ : Type*} [Inhabited Λ]
    (N : ℕ) (M : Bool → Turing.TM0.Machine (Option Bool) Λ)
    (g : Turing.TM0.Cfg (Option Bool) Λ → ℝ) (input : List Bool) (D : ℕ) :
    fairCfgValue (sequenceCoinTable (table (expandCode N)) M)
      (fun cfg => cfg.q.elim (fun _ => 0) (fun q => g ⟨q, cfg.Tape⟩))
      (expandTime N input.length + 1 + D) (mapCfg Sum.inl (Turing.TM0.init (input.map some))) =
      fairCfgValue M g D ⟨default, Turing.Tape.mk₁ (expandedInput N input)⟩ := by
  let T := expandTime N input.length
  let e : ((Fin T → Bool) × Bool × (Fin D → Bool)) ≃ (Fin (T + (D + 1)) → Bool) :=
    (Equiv.prodCongr (Equiv.refl _) (consCoinWords D)).trans (appendCoinWords T (D + 1))
  let K := sequenceCoinTable (table (expandCode N)) M
  let H : Turing.TM0.Cfg (Option Bool) (Sum (Fin (controlSize (expandCode N) + 1)) Λ) → ℝ :=
    fun cfg => cfg.q.elim (fun _ => 0) (fun q => g ⟨q, cfg.Tape⟩)
  let initial : Turing.TM0.Cfg (Option Bool) (Sum (Fin (controlSize (expandCode N) + 1)) Λ) :=
      mapCfg Sum.inl (Turing.TM0.init (input.map some))
  let next : Turing.TM0.Cfg (Option Bool) Λ := ⟨default, Turing.Tape.mk₁ (expandedInput N input)⟩
  have hp (p : (Fin T → Bool) × Bool × (Fin D → Bool)) :
      stoppedValue H (coinConfigRunAux K (List.ofFn (e p)) initial) =
        stoppedValue g (coinConfigRunAux M (List.ofFn p.2.2) next) := by
    have hw : List.ofFn (e p) = List.ofFn p.1 ++ p.2.1 :: List.ofFn p.2.2 := by
      change List.ofFn (Fin.append p.1 (consCoinWords D p.2)) = _
      rw [List.ofFn_fin_append, List.ofFn_succ]
      rfl
    have h := (expandCode_then_coin_source N M input p.1 p.2.1 (List.ofFn p.2.2)).1
    change (coinConfigRunAux K (List.ofFn p.1 ++ p.2.1 :: List.ofFn p.2.2) initial).stopped =
      (coinConfigRunAux M (List.ofFn p.2.2) next).stopped.map (mapCfg Sum.inr) at h
    unfold stoppedValue
    rw [hw, h]
    cases (coinConfigRunAux M (List.ofFn p.2.2) next).stopped <;> rfl
  have hs : (∑ w : Fin (T + (D + 1)) → Bool,
      stoppedValue H (coinConfigRunAux K (List.ofFn w) initial)) =
      (2 : ℝ) ^ T * 2 * (∑ w : Fin D → Bool,
        stoppedValue g (coinConfigRunAux M (List.ofFn w) next)) := by
    rw [← e.sum_comp]
    simp_rw [hp]
    simp [Fintype.sum_prod_type, ← two_mul, mul_assoc]
  change fairCfgValue K H (T + 1 + D) initial = fairCfgValue M g D next
  rw [show T + 1 + D = T + (D + 1) by omega]
  unfold fairCfgValue
  rw [hs, pow_add, pow_succ]
  have hT : (2 : ℝ) ^ T ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD : (2 : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hT, hD]

@[simp] theorem bitHalf_mk (N : ℕ) (rev : Bool) (l : List (TrackCell N)) :
    bitHalf N rev (Turing.ListBlank.mk l) =
      Turing.ListBlank.mk (l.flatMap fun s => if rev then (bitBlock N s).reverse else bitBlock N s) := rfl

@[simp] theorem bitHalf_cons (N : ℕ) (rev : Bool) (s : TrackCell N)
    (l : Turing.ListBlank (TrackCell N)) :
    bitHalf N rev (l.cons s) = Turing.ListBlank.append
      (if rev then (bitBlock N s).reverse else bitBlock N s) (bitHalf N rev l) := by
  induction l using Turing.ListBlank.induction_on
  simp only [Turing.ListBlank.cons_mk, bitHalf_mk, List.flatMap_cons, Turing.ListBlank.append_mk]

theorem bitTape_mk' (N : ℕ) (L R : Turing.ListBlank (TrackCell N)) :
    bitTape N (Turing.Tape.mk' L R) =
      Turing.Tape.mk' (bitHalf N true L) (bitHalf N false R) := by
  unfold bitTape
  simp only [Turing.Tape.mk'_left, Turing.Tape.mk'_head, Turing.Tape.mk'_right]
  have h := bitHalf_cons N false R.head R.tail
  change bitHalf N false (R.tail.cons R.head) =
    Turing.ListBlank.append (bitBlock N R.head) (bitHalf N false R.tail) at h
  rw [Turing.ListBlank.cons_head_tail] at h
  rw [← h]

theorem bitTape_mk₁ (N : ℕ) (input : List (TrackCell N)) :
    bitTape N (Turing.Tape.mk₁ input) = Turing.Tape.mk₁ (input.flatMap (bitBlock N)) := by
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂, bitTape_mk']

theorem bitTape_move_right (N : ℕ) (T : Turing.Tape (TrackCell N)) :
    (Turing.Tape.move .right)^[N + 3] (bitTape N T) = bitTape N (T.move .right) := by
  have h := tape_right_append (bitBlock N T.head) (bitHalf N true T.left) (bitHalf N false T.right)
  rw [bitBlock_length] at h
  rw [bitTape, h]
  simp only [bitTape, Turing.Tape.move, bitHalf_cons, ↓reduceIte]
  have hr := bitHalf_cons N false T.right.head T.right.tail
  change bitHalf N false (T.right.tail.cons T.right.head) =
    Turing.ListBlank.append (bitBlock N T.right.head) (bitHalf N false T.right.tail) at hr
  rw [Turing.ListBlank.cons_head_tail] at hr
  rw [← hr]

theorem bitTape_move_left (N : ℕ) (T : Turing.Tape (TrackCell N)) :
    (Turing.Tape.move .left)^[N + 3] (bitTape N T) = bitTape N (T.move .left) := by
  have h := congrArg ((Turing.Tape.move .left)^[N + 3]) (bitTape_move_right N (T.move .left))
  rw [tape_left_right_iterate, Turing.Tape.move_left_right] at h
  exact h.symm

theorem cellBuffer_block (N : ℕ) (s : TrackCell N) :
    List.ofFn (cellBuffer N s) ++ [none] = bitBlock N s := by
  rw [cellBuffer, List.ofFn_cons, List.ofFn_succ']
  simp [bitBlock, List.concat_eq_append]

theorem bufferCell_cellBuffer (N : ℕ) (s : TrackCell N) : bufferCell N (cellBuffer N s) = s := by
  rcases s with ⟨i, w, h⟩
  apply Prod.ext
  · simp [bufferCell, cellBuffer]
  · apply Prod.ext
    · funext j
      simp [bufferCell, cellBuffer]
    · cases h <;> simp [bufferCell, cellBuffer]

theorem bitHalf_append_nth {Γ : Type*} [Inhabited Γ] (l : List Γ) (R : Turing.ListBlank Γ)
    (i : ℕ) (hi : i < l.length) : (Turing.ListBlank.append l R).nth i = l.getI i := by
  induction R using Turing.ListBlank.induction_on
  simp only [Turing.ListBlank.append_mk, Turing.ListBlank.nth_mk, List.getI_append _ _ _ hi]

theorem tapeBuffer_bitTape (N : ℕ) (T : Turing.Tape (TrackCell N)) :
    tapeBuffer N (bitTape N T) = cellBuffer N T.head := by
  funext j
  unfold tapeBuffer bitTape
  rw [Turing.Tape.mk'_nth_nat, bitHalf_append_nth _ _ j.val (by rw [bitBlock_length]; omega)]
  rw [← cellBuffer_block]
  have hj : j.val < (List.ofFn (cellBuffer N T.head)).length := by
    simpa only [List.length_ofFn] using! j.isLt
  rw [List.getI_append _ _ _ hj, List.getI_eq_getElem _ hj]
  simp only [List.getElem_ofFn]

theorem bitTape_separator (N : ℕ) (T : Turing.Tape (TrackCell N)) :
    (bitTape N T).nth ((N + 2 : ℕ) : ℤ) = none := by
  unfold bitTape
  rw [Turing.Tape.mk'_nth_nat, bitHalf_append_nth _ _ (N + 2) (by rw [bitBlock_length]; omega)]
  rw [← cellBuffer_block]
  simp [List.getI_eq_getElem?_getD]

@[simp] theorem bitCapture_zero (N : ℕ) (T : Turing.Tape (Option Bool)) :
    bitCapture N T 0 = fun _ => none := by funext j; simp [bitCapture]

@[simp] theorem bitCapture_full (N : ℕ) (T : Turing.Tape (Option Bool)) :
    bitCapture N T (N + 2) = tapeBuffer N T := by
  funext j
  simp [bitCapture, tapeBuffer, j.isLt]

theorem bitCapture_update (N : ℕ) (T : Turing.Tape (Option Bool)) (i : Fin (N + 2)) :
    Function.update (bitCapture N T i.val) i (T.nth (i.val : ℤ)) = bitCapture N T (i.val + 1) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [bitCapture]
  · have hv : j.val ≠ i.val := fun he => h (Fin.ext he)
    rw [Function.update_of_ne h]
    simp only [bitCapture]
    split_ifs <;> first | rfl | omega

theorem bitFetch_step {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ)
    (T : Turing.Tape (Option Bool)) (c : Bool) (i : Fin (N + 3)) (hi : i.val < N + 2) :
    Turing.TM0.step (bitSimTable N M c) (bitFetchCfg N q T i) =
      some (bitFetchCfg N q T ⟨i.val + 1, by omega⟩) := by
  have hh : ((Turing.Tape.move .right)^[i.val] T).head = T.nth (i.val : ℤ) :=
    Turing.Tape.move_right_n_head T i.val
  have hu := bitCapture_update N T ⟨i.val, hi⟩
  simp only [TM0_step_apply, bitSimTable, bitFetchCfg, hi, ↓reduceIte, Fin.val_zero, hh,
    TM0StmtApply, hu]
  split_ifs <;> simp_all [Function.iterate_succ_apply', Fin.ext_iff]
  omega

theorem bitFetch_steps_to_end {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (T : Turing.Tape (Option Bool))
    (coins : List Bool) (i : Fin (N + 3)) (hk : i.val + coins.length = N + 2) :
    coinStepsAux (bitSimTable N M) coins (bitFetchCfg N q T i) =
      some (bitFetchCfg N q T ⟨N + 2, by omega⟩) := by
  induction coins generalizing i with
  | nil =>
    have he : i = ⟨N + 2, by omega⟩ := Fin.ext (by simpa using! hk)
    rw [he]
    rfl
  | cons c cs ih =>
    have hi : i.val < N + 2 := by simp only [List.length_cons] at hk; omega
    rw [coinStepsAux, bitFetch_step N M q T c i hi]
    exact ih ⟨i.val + 1,
        by omega⟩ (by simp only [List.length_cons] at hk; simpa only [Fin.val_mk] using! (by omega : i.val + 1 + cs.length = N + 2))

theorem bitFetchReturn_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (buf : BitBuffer N)
    (coins : List Bool) (hn : 0 < coins.length) (hb : coins.length < 3 * (N + 2) + 1)
    (T : Turing.Tape (Option Bool)) :
    coinStepsAux (bitSimTable N M) coins ⟨(1, q, ⟨coins.length, hb⟩, buf), T⟩ =
      some ⟨(2, q, 0, buf), (Turing.Tape.move .left)^[coins.length] T⟩ := by
  induction coins generalizing T with
  | nil => simp at hn
  | cons c cs ih =>
    cases cs with
    | nil =>
      have hm : 1 % (3 * (N + 2) + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [coinStepsAux, TM0_step_apply, bitSimTable, TM0StmtApply, hm]
    | cons d ds =>
      have hs : Turing.TM0.step (bitSimTable N M c) ⟨(1, q, ⟨(c :: d :: ds).length, hb⟩, buf), T⟩ =
          some ⟨(1, q, ⟨(d :: ds).length, by simp only [List.length_cons] at hb ⊢; omega⟩, buf), T.move .left⟩ := by
        simp [TM0_step_apply, bitSimTable, TM0StmtApply]
      rw [coinStepsAux, hs]
      simpa only [Option.bind_some, List.length_cons, Function.iterate_succ_apply] using!
        ih (by simp) (by simp only [List.length_cons] at hb ⊢; omega) (T.move .left)

theorem bitFetch_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (T : Turing.Tape (Option Bool))
    (front back : List Bool) (hf : front.length = N + 2) (hb : back.length = N + 2) :
    coinStepsAux (bitSimTable N M) (front ++ back) ⟨(0, q, 0, fun _ => none), T⟩ =
      some ⟨(2, q, 0, tapeBuffer N T), T⟩ := by
  have ha := bitFetch_steps_to_end N M q T front 0 (by simp [hf])
  have hr := bitFetchReturn_steps N M q (tapeBuffer N T) back (by rw [hb]; omega)
    (by rw [hb]; omega) ((Turing.Tape.move .right)^[N + 2] T)
  have hs : coinStepsAux (bitSimTable N M) (front ++ back) (bitFetchCfg N q T 0) =
      some ⟨(2, q, 0, tapeBuffer N T), T⟩ := by
    rw [coinStepsAux_append, ha]
    simpa only [Option.bind_some, bitFetchCfg, lt_irrefl, ↓reduceIte, bitCapture_full,
      hb, tape_left_right_iterate] using! hr
  simpa [bitFetchCfg] using! hs

theorem bitFetch_ready_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ)
    (front back : List Bool) (hf : front.length = N + 2) (hb : back.length = N + 2) :
    coinStepsAux (bitSimTable N M) (front ++ back)
      ⟨(0, cfg.q, 0, fun _ => none), bitTape N cfg.Tape⟩ = some (bitReady N cfg) := by
  simpa only [tapeBuffer_bitTape, bitReady] using!
      bitFetch_steps N M cfg.q (bitTape N cfg.Tape) front back hf hb

theorem bitSim_ready_isNone {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (i : Fin (3 * (N + 2) + 1)) (buf : BitBuffer N) (c : Bool) (s : Option Bool) :
    (bitSimTable N M c (2, q, i, buf) s).isNone = (M c q (bufferCell N buf)).isNone := by
  cases h : M c q (bufferCell N buf) with
  | none => simp [bitSimTable, h]
  | some p =>
    rcases p with ⟨next, stmt⟩
    cases stmt with
    | move d => cases d <;> simp [bitSimTable, h]
    | write v => simp [bitSimTable, h]

theorem bitReady_coinHalt {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    coinHalt (bitSimTable N M) (bitReady N cfg) = coinHalt M cfg := by
  simp only [coinHalt, bitReady, bitSim_ready_isNone, bufferCell_cellBuffer]

theorem bitSim_commonHalt {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ q s, (bitSimTable N M false q s = none) ↔ (bitSimTable N M true q s = none) := by
  rintro ⟨phase, q, i, buf⟩ s
  fin_cases phase <;> try rfl
  change (bitSimTable N M false (2, q, i, buf) s = none) ↔
    (bitSimTable N M true (2, q, i, buf) s = none)
  rw [← Option.isNone_iff_eq_none, ← Option.isNone_iff_eq_none,
    bitSim_ready_isNone N M q i buf false s, bitSim_ready_isNone N M q i buf true s]
  simpa only [Option.isNone_iff_eq_none] using! hc q (bufferCell N buf)

theorem bitSim_initial_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (input : List (TrackCell N))
    (front back : List Bool) (hf : front.length = N + 2) (hb : back.length = N + 2) :
    coinStepsAux (bitSimTable N M) (front ++ back) (Turing.TM0.init (input.flatMap (bitBlock N))) =
      some (bitReady N (Turing.TM0.init input)) := by
  have h := bitFetch_ready_steps N M (Turing.TM0.init input) front back hf hb
  simpa only [Turing.TM0.init, bitTape_mk₁, Fin.default_eq_zero] using! h

theorem bitSim_initial_stopped {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (input : List (TrackCell N))
    (hc : coinHalt M (Turing.TM0.init input) = true)
    (front back : List Bool) (hf : front.length = N + 2) (hb : back.length = N + 2) :
    let r := coinConfigRunAux (bitSimTable N M) (front ++ back)
      (Turing.TM0.init (input.flatMap (bitBlock N)))
    r.stopped = some (bitReady N (Turing.TM0.init input)) ∧
      r.reads = 2 * (N + 2) ∧ r.transitions = 2 * (N + 2) := by
  have h := coinStepsAux_stopped (bitSimTable N M) (front ++ back)
    (Turing.TM0.init (input.flatMap (bitBlock N))) (bitReady N (Turing.TM0.init input))
    (bitSim_initial_steps N M input front back hf hb) (by rw [bitReady_coinHalt]; exact hc)
  simpa only [List.length_append, hf, hb, two_mul] using! h

theorem bitWriteTape_write_move (N : ℕ) (new old : BitBuffer N)
    (L R : Turing.ListBlank (Option Bool)) (i : ℕ) (hi : i < N + 2) :
    ((bitWriteTape N new old L R i).write (new ⟨i, hi⟩)).move .right =
      bitWriteTape N new old L R (i + 1) := by
  unfold bitWriteTape
  rw [tape_write_move_right]
  have ho : i < (List.ofFn old).length := by simpa only [List.length_ofFn] using! hi
  have hn : i < (List.ofFn new).length := by simpa only [List.length_ofFn] using! hi
  rw [List.drop_eq_getElem_cons ho, Turing.ListBlank.append, Turing.ListBlank.tail_cons,
    List.take_succ_eq_append_getElem hn]
  simp only [List.reverse_append, List.reverse_singleton, List.getElem_ofFn,
    Turing.ListBlank.append_assoc, Turing.ListBlank.append]

theorem bitWrite_two_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (new old : BitBuffer N)
    (L R : Turing.ListBlank (Option Bool)) (i : Fin (N + 3)) (hi : i.val < N + 2) (c d : Bool) :
    coinStepsAux (bitSimTable N M) [c, d] (bitWriteCfg N q new old L R i) =
      some (bitWriteCfg N q new old L R ⟨i.val + 1, by omega⟩) := by
  let T := bitWriteTape N new old L R i.val
  have hs : Turing.TM0.step (bitSimTable N M c) (bitWriteCfg N q new old L R i) =
      some ⟨(7, q, ⟨i.val, by omega⟩, new), T.write (new ⟨i.val, hi⟩)⟩ := by
    simp [TM0_step_apply, bitSimTable, bitWriteCfg, hi, TM0StmtApply, T]
  have hm : Turing.TM0.step (bitSimTable N M d)
      ⟨(7, q, ⟨i.val, by omega⟩, new), T.write (new ⟨i.val, hi⟩)⟩ =
      some (bitWriteCfg N q new old L R ⟨i.val + 1, by omega⟩) := by
    by_cases hn : i.val + 1 < N + 2 <;>
      simp [TM0_step_apply, bitSimTable, bitWriteCfg, hn, TM0StmtApply, T]
    · exact bitWriteTape_write_move N new old L R i.val hi
    · exact bitWriteTape_write_move N new old L R i.val hi
  simp only [coinStepsAux, hs, Option.bind_some, hm]

theorem bitWrite_steps_to_end {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (new old : BitBuffer N)
    (L R : Turing.ListBlank (Option Bool)) (fuel : ℕ) (i : Fin (N + 3))
    (hi : i.val + fuel = N + 2) (coins : List Bool) (hlen : coins.length = 2 * fuel) :
    coinStepsAux (bitSimTable N M) coins (bitWriteCfg N q new old L R i) =
      some (bitWriteCfg N q new old L R ⟨N + 2, by omega⟩) := by
  induction fuel generalizing i coins with
  | zero =>
    have he : i = ⟨N + 2, by omega⟩ := Fin.ext (by omega)
    have hc : coins = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [he, hc]
    rfl
  | succ fuel ih =>
    cases coins with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons c cs =>
      cases cs with
      | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
      | cons d ds =>
        have hic : i.val < N + 2 := by omega
        have hl : ds.length = 2 * fuel := by simp only [List.length_cons] at hlen; omega
        change coinStepsAux (bitSimTable N M) ([c, d] ++ ds) _ = _
        rw [coinStepsAux_append, bitWrite_two_steps N M q new old L R i hic c d]
        exact ih ⟨i.val + 1, by omega⟩ (by simp; omega) ds hl

theorem bitWriteReturn_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (buf : BitBuffer N)
    (coins : List Bool) (hn : 0 < coins.length) (hb : coins.length < 3 * (N + 2) + 1)
    (T : Turing.Tape (Option Bool)) :
    coinStepsAux (bitSimTable N M) coins ⟨(8, q, ⟨coins.length, hb⟩, buf), T⟩ =
      some ⟨(0, q, 0, fun _ => none), (Turing.Tape.move .left)^[coins.length] T⟩ := by
  induction coins generalizing T with
  | nil => simp at hn
  | cons c cs ih =>
    cases cs with
    | nil =>
      have hm : 1 % (3 * (N + 2) + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [coinStepsAux, TM0_step_apply, bitSimTable, TM0StmtApply, hm]
    | cons d ds =>
      have hs : Turing.TM0.step (bitSimTable N M c) ⟨(8, q, ⟨(c :: d :: ds).length, hb⟩, buf), T⟩ =
          some ⟨(8, q, ⟨(d :: ds).length, by simp only [List.length_cons] at hb ⊢; omega⟩, buf), T.move .left⟩ := by
        simp [TM0_step_apply, bitSimTable, TM0StmtApply]
      rw [coinStepsAux, hs]
      simpa only [Option.bind_some, List.length_cons, Function.iterate_succ_apply] using!
        ih (by simp) (by simp only [List.length_cons] at hb ⊢; omega) (T.move .left)

theorem bitPad_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (buf : BitBuffer N)
    (coins : List Bool) (hn : 0 < coins.length) (hb : coins.length < 3 * (N + 2) + 1)
    (T : Turing.Tape (Option Bool)) :
    coinStepsAux (bitSimTable N M) coins ⟨(6, q, ⟨coins.length, hb⟩, buf), T⟩ =
      some ⟨(0, q, 0, fun _ => none), T⟩ := by
  induction coins with
  | nil => simp at hn
  | cons c cs ih =>
    cases cs with
    | nil =>
      have hm : 1 % (3 * (N + 2) + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      simp [coinStepsAux, TM0_step_apply, bitSimTable, TM0StmtApply, hm]
    | cons d ds =>
      have hs : Turing.TM0.step (bitSimTable N M c) ⟨(6, q, ⟨(c :: d :: ds).length, hb⟩, buf), T⟩ =
          some ⟨(6, q, ⟨(d :: ds).length, by simp only [List.length_cons] at hb ⊢; omega⟩, buf), T⟩ := by
        simp [TM0_step_apply, bitSimTable, TM0StmtApply]
      rw [coinStepsAux, hs]
      exact ih (by simp) (by simp only [List.length_cons] at hb ⊢; omega)

theorem bitMove_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (buf : BitBuffer N) (dir : Turing.Dir)
    (coins : List Bool) (hn : 0 < coins.length) (hb : coins.length < 3 * (N + 2) + 1)
    (T : Turing.Tape (Option Bool)) :
    coinStepsAux (bitSimTable N M) coins
      ⟨((if dir = .left then 3 else 4), q, ⟨coins.length, hb⟩, buf), T⟩ =
      some ⟨(6, q, ⟨2 * (N + 2) - 1, by omega⟩, buf), (Turing.Tape.move dir)^[coins.length] T⟩ := by
  induction coins generalizing T with
  | nil => simp at hn
  | cons c cs ih =>
    cases cs with
    | nil =>
      have hm : 1 % (3 * (N + 2) + 1) = 1 := Nat.mod_eq_of_lt (by omega)
      cases dir <;> simp [coinStepsAux, TM0_step_apply, bitSimTable, TM0StmtApply, hm]
    | cons d ds =>
      have hs : Turing.TM0.step (bitSimTable N M c)
          ⟨((if dir = .left then 3 else 4), q, ⟨(c :: d :: ds).length, hb⟩, buf), T⟩ =
          some ⟨((if dir = .left then 3 else 4), q,
            ⟨(d :: ds).length, by simp only [List.length_cons] at hb ⊢; omega⟩, buf), T.move dir⟩ := by
        cases dir <;> simp [TM0_step_apply, bitSimTable, TM0StmtApply]
      rw [coinStepsAux, hs]
      simpa only [Option.bind_some, List.length_cons, Function.iterate_succ_apply] using!
        ih (by simp) (by simp only [List.length_cons] at hb ⊢; omega) (T.move dir)

theorem bitWrite_block_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (T : Turing.Tape (TrackCell N))
    (v : TrackCell N) (writes back : List Bool)
    (hw : writes.length = 2 * (N + 2)) (hb : back.length = N + 2) :
    coinStepsAux (bitSimTable N M) (writes ++ back)
      ⟨(5, q, 0, cellBuffer N v), bitTape N T⟩ =
      some ⟨(0, q, 0, fun _ => none), bitTape N (T.write v)⟩ := by
  let L := bitHalf N true T.left
  let R := (bitHalf N false T.right).cons none
  let new := cellBuffer N v
  let old := cellBuffer N T.head
  have hstart : bitWriteCfg N q new old L R 0 = ⟨(5, q, 0, new), bitTape N T⟩ := by
    unfold bitTape
    rw [← cellBuffer_block]
    simp [bitWriteCfg, bitWriteTape, Turing.ListBlank.append_assoc, L, R, old]
  have hnew : bitTape N (T.write v) = Turing.Tape.mk' L (Turing.ListBlank.append (List.ofFn new) R) := by
    unfold bitTape
    change Turing.Tape.mk' L (Turing.ListBlank.append (bitBlock N v) (bitHalf N false T.right)) = _
    rw [← cellBuffer_block, Turing.ListBlank.append_assoc]
    rfl
  have hm := tape_right_append (List.ofFn new) L R
  rw [List.length_ofFn, ← hnew] at hm
  have hend : bitWriteCfg N q new old L R ⟨N + 2, by omega⟩ =
      ⟨(8, q, ⟨N + 2, by omega⟩, new), (Turing.Tape.move .right)^[N + 2] (bitTape N (T.write v))⟩ := by
    rw [hm]
    have ht : (List.ofFn new).take (N + 2) = List.ofFn new :=
        List.take_of_length_le (by simp only [List.length_ofFn]; rfl)
    have hd : (List.ofFn old).drop (N + 2) = [] :=
        List.drop_eq_nil_of_le (by simp only [List.length_ofFn]; rfl)
    simp only [bitWriteCfg, lt_irrefl, ↓reduceIte, bitWriteTape, ht, hd, Turing.ListBlank.append]
  have ha := bitWrite_steps_to_end N M q new old L R (N + 2) 0 (by simp) writes hw
  have hr := bitWriteReturn_steps N M q new back (by rw [hb]; omega) (by rw [hb]; omega)
    ((Turing.Tape.move .right)^[N + 2] (bitTape N (T.write v)))
  rw [coinStepsAux_append, ← hstart, ha, hend]
  simpa only [Option.bind_some, hb, tape_left_right_iterate] using! hr

theorem bitMove_block_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (buf : BitBuffer N)
    (T : Turing.Tape (TrackCell N)) (dir : Turing.Dir) (moves pad : List Bool)
    (hm : moves.length = N + 3) (hp : pad.length = 2 * (N + 2) - 1) :
    coinStepsAux (bitSimTable N M) (moves ++ pad)
      ⟨((if dir = .left then 3 else 4), q, ⟨N + 3, by omega⟩, buf), bitTape N T⟩ =
      some ⟨(0, q, 0, fun _ => none), bitTape N (T.move dir)⟩ := by
  have hb : (Turing.Tape.move dir)^[N + 3] (bitTape N T) = bitTape N (T.move dir) := by
    cases dir
    · exact bitTape_move_left N T
    · exact bitTape_move_right N T
  have ha := bitMove_steps N M q buf dir moves (by rw [hm]; omega) (by rw [hm]; omega) (bitTape N T)
  have hr :=
      bitPad_steps N M q buf pad (by rw [hp]; omega) (by rw [hp]; omega) (bitTape N (T.move dir))
  rw [coinStepsAux_append]
  have ha' : coinStepsAux (bitSimTable N M) moves
      ⟨((if dir = .left then 3 else 4), q, ⟨N + 3, by omega⟩, buf), bitTape N T⟩ =
      some ⟨(6, q, ⟨2 * (N + 2) - 1, by omega⟩, buf), bitTape N (T.move dir)⟩ := by
    simpa only [hm, hb] using! ha
  rw [ha']
  simpa only [Option.bind_some, hp] using! hr

theorem bitWrite_exec_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (T : Turing.Tape (TrackCell N))
    (v : TrackCell N) (coins : List Bool) (hlen : coins.length = 3 * (N + 2)) :
    coinStepsAux (bitSimTable N M) coins ⟨(5, q, 0, cellBuffer N v), bitTape N T⟩ =
      some ⟨(0, q, 0, fun _ => none), bitTape N (T.write v)⟩ := by
  have h := bitWrite_block_steps N M q T v (coins.take (2 * (N + 2))) (coins.drop (2 * (N + 2)))
    (by rw [List.length_take, hlen]; omega) (by rw [List.length_drop, hlen]; omega)
  simpa only [List.take_append_drop] using! h

theorem bitMove_exec_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (buf : BitBuffer N)
    (T : Turing.Tape (TrackCell N)) (dir : Turing.Dir) (coins : List Bool)
    (hlen : coins.length = 3 * (N + 2)) :
    coinStepsAux (bitSimTable N M) coins
      ⟨((if dir = .left then 3 else 4), q, ⟨N + 3, by omega⟩, buf), bitTape N T⟩ =
      some ⟨(0, q, 0, fun _ => none), bitTape N (T.move dir)⟩ := by
  have h := bitMove_block_steps N M q buf T dir (coins.take (N + 3)) (coins.drop (N + 3))
    (by rw [List.length_take, hlen]; omega) (by rw [List.length_drop, hlen]; omega)
  simpa only [List.take_append_drop] using! h

theorem bitSim_macro_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ)
    (q : Λ) (stmt : Turing.TM0.Stmt (TrackCell N)) (c : Bool)
    (hs : M c cfg.q cfg.Tape.head = some (q, stmt))
    (exec front back : List Bool) (he : exec.length = 3 * (N + 2))
    (hf : front.length = N + 2) (hb : back.length = N + 2) :
    coinStepsAux (bitSimTable N M) (c :: (exec ++ (front ++ back))) (bitReady N cfg) =
      some (bitReady N ⟨q, TM0StmtApply cfg.Tape stmt⟩) := by
  cases stmt with
  | move dir =>
    have hc : Turing.TM0.step (bitSimTable N M c) (bitReady N cfg) =
        some ⟨((if dir = .left then 3 else 4), q, ⟨N + 3, by omega⟩, cellBuffer N cfg.Tape.head), bitTape N cfg.Tape⟩ := by
      cases dir <;> simp [TM0_step_apply, bitSimTable, bitReady, bufferCell_cellBuffer, hs,
          TM0StmtApply]
    rw [coinStepsAux, hc, Option.bind_some, coinStepsAux_append,
      bitMove_exec_steps N M q (cellBuffer N cfg.Tape.head) cfg.Tape dir exec he]
    exact bitFetch_ready_steps N M ⟨q, cfg.Tape.move dir⟩ front back hf hb
  | write v =>
    have hc : Turing.TM0.step (bitSimTable N M c) (bitReady N cfg) =
        some ⟨(5, q, 0, cellBuffer N v), bitTape N cfg.Tape⟩ := by
      simp [TM0_step_apply, bitSimTable, bitReady, bufferCell_cellBuffer, hs, TM0StmtApply]
    rw [coinStepsAux, hc, Option.bind_some, coinStepsAux_append,
        bitWrite_exec_steps N M q cfg.Tape v exec he]
    exact bitFetch_ready_steps N M ⟨q, cfg.Tape.write v⟩ front back hf hb

theorem bitSim_macro_stopped {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ)
    (q : Λ) (stmt : Turing.TM0.Stmt (TrackCell N)) (c : Bool)
    (hs : M c cfg.q cfg.Tape.head = some (q, stmt))
    (hh : coinHalt M ⟨q, TM0StmtApply cfg.Tape stmt⟩ = true)
    (exec front back : List Bool) (he : exec.length = 3 * (N + 2))
    (hf : front.length = N + 2) (hb : back.length = N + 2) :
    let r := coinConfigRunAux (bitSimTable N M) (c :: (exec ++ (front ++ back))) (bitReady N cfg)
    r.stopped = some (bitReady N ⟨q, TM0StmtApply cfg.Tape stmt⟩) ∧
      r.reads = 5 * (N + 2) + 1 ∧ r.transitions = 5 * (N + 2) + 1 := by
  have h := coinStepsAux_stopped (bitSimTable N M) (c :: (exec ++ (front ++ back)))
    (bitReady N cfg) (bitReady N ⟨q, TM0StmtApply cfg.Tape stmt⟩)
    (bitSim_macro_steps N M cfg q stmt c hs exec front back he hf hb)
    (by rw [bitReady_coinHalt]; exact hh)
  have hl : (c :: (exec ++ (front ++ back))).length = 5 * (N + 2) + 1 := by
    simp only [List.length_cons, List.length_append, he, hf, hb]
    omega
  simpa only [hl] using! h

theorem bitSimLabels_zero (N Q : ℕ) : bitSimLabels N Q (0, 0, 0, fun _ => none) = 0 := by
  apply Fin.ext
  simp [bitSimLabels, expandQueueLabels_zero, finProdFinEquiv, Equiv.prodCongr]

theorem nativeBitSim_run (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List (Option Bool)) (coins : List Bool) :
    coinTapeRun (nativeBitSimTable N Q M) (nativeBitSimAccept N Q a) input coins =
      coinTapeRun (bitSimTable N M) (fun q => a q.2.1) input coins ∧
    coinTapeTransitionCount (nativeBitSimTable N Q M) input coins =
      coinTapeTransitionCount (bitSimTable N M) input coins := by
  have hz : bitSimLabels N Q (default : BitSimState N (Fin (Q + 1))) = 0 := by
    simpa only [Fin.default_eq_zero] using! bitSimLabels_zero N Q
  exact relabel_run (bitSimLabels N Q) hz (bitSimTable N M) (fun q => a q.2.1) coins input

theorem bitSimCode_run (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (input : List (Option Bool)) (coins : List Bool) :
    coinTapeRun (table (bitSimCode N Q M a)) (readout (bitSimCode N Q M a)) input coins =
      coinTapeRun (bitSimTable N M) (fun q => a q.2.1) input coins ∧
    coinTapeTransitionCount (table (bitSimCode N Q M a)) input coins =
      coinTapeTransitionCount (bitSimTable N M) input coins := by
  have h := encodeMachine_run (bitSimControlMax N Q) (nativeBitSimTable N Q M)
    (nativeBitSimAccept N Q a) input coins
  exact ⟨h.1.trans (nativeBitSim_run N Q M a input coins).1,
    h.2.trans (nativeBitSim_run N Q M a input coins).2⟩

theorem nativeBitSim_commonHalt (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) :
    ∀ q s, (nativeBitSimTable N Q M false q s = none) ↔ (nativeBitSimTable N Q M true q s = none) := by
  intro q s
  simpa only [nativeBitSimTable, relabelTable, Option.map_eq_none_iff] using!
    bitSim_commonHalt N M hc ((bitSimLabels N Q).symm q) s

theorem bitSimCode_commonHalt (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) : commonHalt (bitSimCode N Q M a) := by
  unfold commonHalt
  simpa only [bitSimCode, table_encode] using! nativeBitSim_commonHalt N Q M hc

theorem coinConfigRunAux_of_steps {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (front tail : List Bool)
    (cfg next : Turing.TM0.Cfg Γ Λ) (hs : coinStepsAux M front cfg = some next) :
    let r := coinConfigRunAux M tail next
    let total := coinConfigRunAux M (front ++ tail) cfg
    total.stopped = r.stopped ∧ total.reads = r.reads + front.length ∧
      total.transitions = r.transitions + front.length := by
  induction front generalizing cfg with
  | nil =>
    have he : cfg = next := Option.some.inj hs
    subst cfg
    simp
  | cons c cs ih =>
    cases hstep : Turing.TM0.step (M c) cfg with
    | none => simp [coinStepsAux, hstep] at hs
    | some mid =>
      have htail : coinStepsAux M cs mid = some next := by
        simpa only [coinStepsAux, hstep, Option.bind_some] using! hs
      have hc : coinHalt M cfg ≠ true := by
        intro hc
        rw [coinHalt_step_none M cfg hc c] at hstep
        cases hstep
      have h := ih mid htail
      dsimp only at h ⊢
      simp only [List.cons_append, coinConfigRunAux, hc, Bool.false_eq_true, ↓reduceIte, hstep,
          List.length_cons]
      exact ⟨h.1, by rw [h.2.1]; omega, by rw [h.2.2]; omega⟩

theorem coinConfigRunAux_halted {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (coins : List Bool) (cfg : Turing.TM0.Cfg Γ Λ)
    (hc : coinHalt M cfg = true) : coinConfigRunAux M coins cfg = ⟨some cfg, 0, 0⟩ := by
  cases coins <;> simp [coinConfigRunAux, hc]

theorem bitSim_macro_word {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ)
    (q : Λ) (stmt : Turing.TM0.Stmt (TrackCell N)) (w : Fin (bitMicroWidth N) → Bool)
    (hs : M (w ⟨0, by unfold bitMicroWidth; omega⟩) cfg.q cfg.Tape.head = some (q, stmt)) :
    coinStepsAux (bitSimTable N M) (List.ofFn w) (bitReady N cfg) =
      some (bitReady N ⟨q, TM0StmtApply cfg.Tape stmt⟩) := by
  let tail := List.ofFn (Fin.tail w)
  have hl : tail.length = 5 * (N + 2) := by
    dsimp only [tail]
    rw [List.length_ofFn]
  have hw : List.ofFn w = w ⟨0, by unfold bitMicroWidth; omega⟩ :: tail :=
    List.ofFn_succ (n := 5 * (N + 2)) (f := w)
  have h := bitSim_macro_steps N M cfg q stmt (w ⟨0, by unfold bitMicroWidth; omega⟩) hs
    (tail.take (3 * (N + 2))) ((tail.drop (3 * (N + 2))).take (N + 2))
    ((tail.drop (3 * (N + 2))).drop (N + 2))
    (by rw [List.length_take, hl]; omega)
    (by rw [List.length_take, List.length_drop, hl]; omega)
    (by rw [List.length_drop, List.length_drop, hl]; omega)
  rw [hw]
  simpa only [List.take_append_drop] using! h

theorem bitSim_run_blocks {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (blocks : List (Fin (bitMicroWidth N) → Bool)) (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    let src := coinConfigRunAux M (bitSourceCoins N blocks) cfg
    let sim := coinConfigRunAux (bitSimTable N M) (bitMicroCoins N blocks) (bitReady N cfg)
    sim.stopped = src.stopped.map (bitReady N) ∧
      sim.reads = bitMicroWidth N * src.reads ∧ sim.transitions = bitMicroWidth N * src.transitions := by
  induction blocks generalizing cfg with
  | nil =>
    dsimp only [bitSourceCoins, bitMicroCoins, List.map_nil, List.flatMap_nil]
    by_cases hh : coinHalt M cfg = true <;>
      simp [coinConfigRunAux, bitReady_coinHalt, hh]
  | cons w ws ih =>
    by_cases hh : coinHalt M cfg = true
    · (try dsimp only)
      rw [coinConfigRunAux_halted M _ cfg hh,
        coinConfigRunAux_halted (bitSimTable N M) _ (bitReady N cfg) (by rw [bitReady_coinHalt]; exact hh)]
      simp
    · cases hs : M (w ⟨0, by unfold bitMicroWidth; omega⟩) cfg.q cfg.Tape.head with
      | none =>
        have hn : Turing.TM0.step (M (w ⟨0, by unfold bitMicroWidth; omega⟩)) cfg = none := by
          rw [TM0_step_apply, hs]; rfl
        exact (hh (step_none_common_halt M hc _ cfg hn)).elim
      | some p =>
        rcases p with ⟨q, stmt⟩
        let next : Turing.TM0.Cfg (TrackCell N) Λ := ⟨q, TM0StmtApply cfg.Tape stmt⟩
        have hstep : Turing.TM0.step (M (w ⟨0, by unfold bitMicroWidth; omega⟩)) cfg = some next := by
          rw [TM0_step_apply, hs]; rfl
        have hp := coinConfigRunAux_of_steps (bitSimTable N M) (List.ofFn w) (bitMicroCoins N ws)
          (bitReady N cfg) (bitReady N next) (bitSim_macro_word N M cfg q stmt w hs)
        have hi := ih next
        dsimp only at hp hi ⊢
        simp only [bitMicroCoins, bitSourceCoins] at hp hi
        simp only [bitMicroCoins, List.flatMap_cons, bitSourceCoins, List.map_cons]
        rw [hp.1, hp.2.1, hp.2.2]
        simp only [coinConfigRunAux, hh, Bool.false_eq_true, ↓reduceIte, hstep]
        refine ⟨hi.1, ?_, ?_⟩
        · rw [hi.2.1, List.length_ofFn, Nat.mul_add, Nat.mul_one]
        · rw [hi.2.2, List.length_ofFn, Nat.mul_add, Nat.mul_one]

theorem bitMicroCoins_ofFn (N t : ℕ) (w : Fin t → Fin (bitMicroWidth N) → Bool) :
    bitMicroCoins N (List.ofFn w) = List.ofFn ((freshBlocks t (bitMicroWidth N)).symm w) := by
  rw [List.ofFn_mul]
  simp only [bitMicroCoins, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h := congrFun (congrFun ((freshBlocks t (bitMicroWidth N)).apply_symm_apply w) i) j
  simpa only [freshBlocks_apply, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using! h.symm

theorem bitSourceCoins_ofFn (N t : ℕ) (w : Fin t → Fin (bitMicroWidth N) → Bool) :
    bitSourceCoins N (List.ofFn w) = List.ofFn (fun j => w j ⟨0, by unfold bitMicroWidth; omega⟩) := by
  simp only [bitSourceCoins, List.map_ofFn, Function.comp_def]

theorem bitSim_fair_ready {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (cfg : Turing.TM0.Cfg (TrackCell N) Λ) (t : ℕ) (target : Bool) :
    fairCfgValue (bitSimTable N M) (fun c => if a c.q.2.1 = target then 1 else 0)
      (t * bitMicroWidth N) (bitReady N cfg) =
      fairCfgValue M (fun c => if a c.q = target then 1 else 0) t cfg := by
  let f (w : Fin t → Bool) : ℝ :=
    stoppedValue (fun c => if a c.q = target then 1 else 0) (coinConfigRunAux M (List.ofFn w) cfg)
  have hp (w : Fin t → Fin (bitMicroWidth N) → Bool) :
      stoppedValue (fun c => if a c.q.2.1 = target then 1 else 0)
        (coinConfigRunAux (bitSimTable N M) (List.ofFn ((freshBlocks t (bitMicroWidth N)).symm w)) (bitReady N cfg)) =
        f (fun j => w j ⟨0, by unfold bitMicroWidth; omega⟩) := by
    have h := (bitSim_run_blocks N M hc (List.ofFn w) cfg).1
    rw [bitMicroCoins_ofFn, bitSourceCoins_ofFn] at h
    simp only [f, stoppedValue]
    rw [h]
    cases (coinConfigRunAux M (List.ofFn fun j => w j ⟨0, by unfold bitMicroWidth; omega⟩) cfg).stopped <;> rfl
  have hs : (∑ w : Fin (t * bitMicroWidth N) → Bool,
      stoppedValue (fun c => if a c.q.2.1 = target then 1 else 0)
        (coinConfigRunAux (bitSimTable N M) (List.ofFn w) (bitReady N cfg))) =
      (2 : ℝ) ^ (5 * (N + 2) * t) * (∑ w : Fin t → Bool, f w) := by
    rw [← (freshBlocks t (bitMicroWidth N)).symm.sum_comp]
    simp_rw [hp]
    have hfirst (p : (Fin t → Bool) × (Fin t → Fin (5 * (N + 2)) → Bool)) :
        (fun j => bitSplitWords N t p j ⟨0, by unfold bitMicroWidth; omega⟩) = p.1 := by
      funext j
      rfl
    rw [← (bitSplitWords N t).sum_comp]
    simp_rw [hfirst]
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, ← pow_mul]
  change _ = (∑ w : Fin t → Bool, f w) / 2 ^ t
  unfold fairCfgValue
  rw [hs]
  have he : t * bitMicroWidth N = 5 * (N + 2) * t + t := by unfold bitMicroWidth; ring
  rw [he, pow_add]
  have hd : (2 : ℝ) ^ (5 * (N + 2) * t) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : (2 : ℝ) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hd, ht]

theorem bitSim_initial_prefix_steps {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (input : List (TrackCell N))
    (prep : List Bool) (hp : prep.length = 2 * (N + 2)) :
    coinStepsAux (bitSimTable N M) prep (Turing.TM0.init (input.flatMap (bitBlock N))) =
      some (bitReady N (Turing.TM0.init input)) := by
  have h := bitSim_initial_steps N M input (prep.take (N + 2)) (prep.drop (N + 2))
    (by rw [List.length_take, hp]; omega) (by rw [List.length_drop, hp]; omega)
  simpa only [List.take_append_drop] using! h

theorem bitSim_initial_run {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) (input : List (TrackCell N))
    (prep : List Bool) (hp : prep.length = 2 * (N + 2))
    (blocks : List (Fin (bitMicroWidth N) → Bool)) :
    let src := coinConfigRunAux M (bitSourceCoins N blocks) (Turing.TM0.init input)
    let sim := coinConfigRunAux (bitSimTable N M) (prep ++ bitMicroCoins N blocks)
      (Turing.TM0.init (input.flatMap (bitBlock N)))
    sim.stopped = src.stopped.map (bitReady N) ∧
      sim.reads = 2 * (N + 2) + bitMicroWidth N * src.reads ∧
      sim.transitions = 2 * (N + 2) + bitMicroWidth N * src.transitions := by
  have hpre := coinConfigRunAux_of_steps (bitSimTable N M) prep (bitMicroCoins N blocks)
    (Turing.TM0.init (input.flatMap (bitBlock N))) (bitReady N (Turing.TM0.init input))
    (bitSim_initial_prefix_steps N M input prep hp)
  have hrun := bitSim_run_blocks N M hc blocks (Turing.TM0.init input)
  dsimp only at hpre hrun ⊢
  rw [hpre.1, hpre.2.1, hpre.2.2]
  exact ⟨hrun.1, by rw [hrun.2.1, hp, Nat.add_comm], by rw [hrun.2.2, hp, Nat.add_comm]⟩

theorem bitInitialWords_ofFn (N t : ℕ)
    (p : (Fin (2 * (N + 2)) → Bool) × (Fin t → Fin (bitMicroWidth N) → Bool)) :
    List.ofFn (bitInitialWords N t p) = List.ofFn p.1 ++ bitMicroCoins N (List.ofFn p.2) := by
  change List.ofFn (Fin.append p.1 ((freshBlocks t (bitMicroWidth N)).symm p.2)) = _
  rw [List.ofFn_fin_append, bitMicroCoins_ofFn]

theorem fairCfgValue_of_steps {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (K : Bool → Turing.TM0.Machine Γ Λ) (g : Turing.TM0.Cfg Γ Λ → ℝ)
    (init next : Turing.TM0.Cfg Γ Λ) (P D : ℕ)
    (htrace : ∀ w : Fin P → Bool, coinStepsAux K (List.ofFn w) init = some next) :
    fairCfgValue K g (P + D) init = fairCfgValue K g D next := by
  have hp (p : (Fin P → Bool) × (Fin D → Bool)) :
      stoppedValue g (coinConfigRunAux K (List.ofFn (appendCoinWords P D p)) init) =
        stoppedValue g (coinConfigRunAux K (List.ofFn p.2) next) := by
    rw [show List.ofFn (appendCoinWords P D p) = List.ofFn p.1 ++ List.ofFn p.2 from List.ofFn_fin_append _ _]
    unfold stoppedValue
    rw [(coinConfigRunAux_of_steps K (List.ofFn p.1) (List.ofFn p.2) init next (htrace p.1)).1]
  have hs : (∑ w : Fin (P + D) → Bool, stoppedValue g (coinConfigRunAux K (List.ofFn w) init)) =
      (2 : ℝ) ^ P * (∑ w : Fin D → Bool, stoppedValue g (coinConfigRunAux K (List.ofFn w) next)) := by
    rw [← (appendCoinWords P D).sum_comp]
    simp_rw [hp]
    simp [Fintype.sum_prod_type]
  unfold fairCfgValue
  rw [hs, pow_add]
  have hP : (2 : ℝ) ^ P ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD : (2 : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hP, hD]

theorem bitSim_fair_initial {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List (TrackCell N)) (t : ℕ) (target : Bool) :
    fairTapeSuccess (bitSimTable N M) (fun q => a q.2.1) (input.flatMap (bitBlock N))
      (2 * (N + 2) + t * bitMicroWidth N) target = fairTapeSuccess M a input t target := by
  rw [← fairCfgValue_initial, ← fairCfgValue_initial]
  rw [fairCfgValue_of_steps (bitSimTable N M) _ _ (bitReady N (Turing.TM0.init input))]
  · exact bitSim_fair_ready N M a hc (Turing.TM0.init input) t target
  · intro w
    exact bitSim_initial_prefix_steps N M input (List.ofFn w) (by rw [List.length_ofFn])

theorem bitSim_initial_output {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) (input : List (TrackCell N))
    (prep : List Bool) (hp : prep.length = 2 * (N + 2))
    (blocks : List (Fin (bitMicroWidth N) → Bool)) :
    coinTapeRun (bitSimTable N M) (fun q => a q.2.1) (input.flatMap (bitBlock N))
        (prep ++ bitMicroCoins N blocks) =
      ((coinTapeRun M a input (bitSourceCoins N blocks)).1,
        2 * (N + 2) + bitMicroWidth N * (coinTapeRun M a input (bitSourceCoins N blocks)).2) ∧
    coinTapeTransitionCount (bitSimTable N M) (input.flatMap (bitBlock N)) (prep ++ bitMicroCoins N blocks) =
      2 * (N + 2) + bitMicroWidth N * coinTapeTransitionCount M input (bitSourceCoins N blocks) := by
  have hr := bitSim_initial_run N M hc input prep hp blocks
  have hsim := coinConfigRunAux_readout (bitSimTable N M) (fun q => a q.2.1)
    (prep ++ bitMicroCoins N blocks) (Turing.TM0.init (input.flatMap (bitBlock N)))
  have hsrc := coinConfigRunAux_readout M a (bitSourceCoins N blocks) (Turing.TM0.init input)
  dsimp only at hr
  constructor
  · change coinTapeRunAux _ _ _ _ = ((coinTapeRunAux _ _ _ _).1, _ + _ * (coinTapeRunAux _ _ _ _).2)
    rw [← hsim.1, ← hsrc.1, hr.1, hr.2.1]
    simp only [Option.map_map, bitReady, Function.comp_def]
  · change coinTapeTransitionCountAux _ _ _ = _ + _ * coinTapeTransitionCountAux _ _ _
    rw [← hsim.2, ← hsrc.2, hr.2.2]

theorem bitSim_total_at {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) (input : List (TrackCell N))
    (t : ℕ) (ht : ∀ w : Fin t → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none) :
    ∀ w : Fin (2 * (N + 2) + t * bitMicroWidth N) → Bool,
      (coinTapeRun (bitSimTable N M) (fun q => a q.2.1) (input.flatMap (bitBlock N)) (List.ofFn w)).1 ≠ none := by
  intro w
  let p := (bitInitialWords N t).symm w
  have hw : List.ofFn w = List.ofFn p.1 ++ bitMicroCoins N (List.ofFn p.2) := by
    rw [← (bitInitialWords N t).apply_symm_apply w]
    exact bitInitialWords_ofFn N t p
  have hr :=
      (bitSim_initial_output N M a hc input (List.ofFn p.1) (by rw [List.length_ofFn]) (List.ofFn p.2)).1
  rw [bitSourceCoins_ofFn] at hr
  rw [hw, hr]
  exact ht (fun j => p.2 j ⟨0, by unfold bitMicroWidth; omega⟩)

theorem coinTapeTransitionCount_le_budget {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none))
    (input : List Γ) (coins : List Bool) : coinTapeTransitionCount M input coins ≤ coins.length := by
  have h := (coinConfigRunAux_commonHalt M hc coins (Turing.TM0.init input)).1
  have hr := coinConfigRunAux_reads_le M coins (Turing.TM0.init input)
  have hp := (coinConfigRunAux_readout M (fun _ => false) coins (Turing.TM0.init input)).2
  change _ = coinTapeTransitionCount M input coins at hp
  exact hp.symm.le.trans (h.le.trans hr)

theorem bitSim_full_budget {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (a : Λ → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) (input : List (TrackCell N))
    (t : ℕ) (ht : ∀ w : Fin t → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hB : 2 * (N + 2) + t * bitMicroWidth N ≤ B) :
    (∀ w : Fin B → Bool,
      (coinTapeRun (bitSimTable N M) (fun q => a q.2.1) (input.flatMap (bitBlock N)) (List.ofFn w)).1 ≠ none) ∧
    (∀ w : Fin B → Bool,
      coinTapeTransitionCount (bitSimTable N M) (input.flatMap (bitBlock N)) (List.ofFn w) ≤ B) ∧
    (∀ target : Bool,
      fairTapeSuccess (bitSimTable N M) (fun q => a q.2.1) (input.flatMap (bitBlock N)) B target =
        fairTapeSuccess M a input t target) := by
  have ht' := bitSim_total_at N M a hc input t ht
  refine ⟨coinTape_totality_monotone _ _ _ _ ht' B hB, ?_, ?_⟩
  · intro w
    simpa only [List.length_ofFn] using! coinTapeTransitionCount_le_budget (bitSimTable N M)
      (bitSim_commonHalt N M hc) (input.flatMap (bitBlock N)) (List.ofFn w)
  · intro target
    exact (fairTapeSuccess_of_total _ _ _ _ ht' B hB target).trans
        (bitSim_fair_initial N M a hc input t target)

theorem bitSimCode_full_budget (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (hc : ∀ q s, (M false q s = none) ↔ (M true q s = none)) (input : List (TrackCell N))
    (t : ℕ) (ht : ∀ w : Fin t → Bool, (coinTapeRun M a input (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hB : 2 * (N + 2) + t * bitMicroWidth N ≤ B) :
    (∀ w : Fin B → Bool,
      (coinTapeRun (table (bitSimCode N Q M a)) (readout (bitSimCode N Q M a))
        (input.flatMap (bitBlock N)) (List.ofFn w)).1 ≠ none) ∧
    (∀ w : Fin B → Bool,
      coinTapeTransitionCount (table (bitSimCode N Q M a)) (input.flatMap (bitBlock N)) (List.ofFn w) ≤ B) ∧
    (∀ target : Bool,
      fairTapeSuccess (table (bitSimCode N Q M a)) (readout (bitSimCode N Q M a)) (input.flatMap (bitBlock N)) B target =
        fairTapeSuccess M a input t target) := by
  obtain ⟨ht', hb, hm⟩ := bitSim_full_budget N M a hc input t ht B hB
  refine ⟨?_, ?_, ?_⟩
  · intro w
    rw [(bitSimCode_run N Q M a _ _).1]
    exact ht' w
  · intro w
    rw [(bitSimCode_run N Q M a _ _).2]
    exact hb w
  · intro target
    have he : fairTapeSuccess (table (bitSimCode N Q M a)) (readout (bitSimCode N Q M a))
        (input.flatMap (bitBlock N)) B target =
        fairTapeSuccess (bitSimTable N M) (fun q => a q.2.1) (input.flatMap (bitBlock N)) B target := by
      unfold fairTapeSuccess
      congr 1
      apply Finset.sum_congr rfl
      intro w _
      rw [(bitSimCode_run N Q M a _ _).1]
    exact he.trans (hm target)

theorem encodedMajorityCode_commonHalt (code : Code) (r : ℕ) : commonHalt (encodedMajorityCode code r) := by
  exact bitSimCode_commonHalt (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code)) _ _
    (nativeRounds_commonHalt (2 * r + 1) (controlSize code) (table code) (readout code))

theorem encodedMajorityCode_budget (code : Code) (r : ℕ) (hc : commonHalt code)
    (input : List Bool) (t : ℕ)
    (ht : ∀ w : Fin t → Bool, (coinTapeRun (table code) (readout code) (input.map some) (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hB : 2 * ((2 * r + 1) + 2) +
      ((2 * r + 1) * (3 * input.length + 2 * t + 6)) * bitMicroWidth (2 * r + 1) ≤ B) :
    (∀ w : Fin B → Bool,
      (coinTapeRun (table (encodedMajorityCode code r)) (readout (encodedMajorityCode code r))
        (expandedInput (2 * r + 1) input) (List.ofFn w)).1 ≠ none) ∧
    (∀ w : Fin B → Bool,
      coinTapeTransitionCount (table (encodedMajorityCode code r)) (expandedInput (2 * r + 1) input) (List.ofFn w) ≤ B) ∧
    (∀ target : Bool,
      fairTapeSuccess (table (encodedMajorityCode code r)) (readout (encodedMajorityCode code r))
        (expandedInput (2 * r + 1) input) B target =
          independentMajorityMass (table code) (readout code) (input.map some) t r target) ∧
    (∀ target : Bool, (2 / 3 : ℝ) ≤ fairTapeSuccess (table code) (readout code) (input.map some) t target →
      1 - (8 / 9 : ℝ) ^ r ≤ fairTapeSuccess (table (encodedMajorityCode code r))
        (readout (encodedMajorityCode code r)) (expandedInput (2 * r + 1) input) B target) := by
  let N := 2 * r + 1
  let Q := controlSize code
  let W := N * (3 * input.length + 2 * t + 6)
  have htwide : ∀ w : Fin W → Bool,
      (coinTapeRun (nativeRoundsTable N Q (table code) (readout code)) (nativeRoundsAccept N Q)
        (tracksInput N input) (List.ofFn w)).1 ≠ none := by
    intro w
    exact (nativeRounds_total N Q (table code) (readout code) hc input t ht (List.ofFn w) (by rw [List.length_ofFn])).1
  have h := bitSimCode_full_budget N (roundsControlMax N Q)
    (nativeRoundsTable N Q (table code) (readout code)) (nativeRoundsAccept N Q)
    (nativeRounds_commonHalt N Q (table code) (readout code)) (tracksInput N input) W htwide B hB
  rw [tracksInput_bitBlocks] at h
  change _ ∧ _ ∧ (∀ target, fairTapeSuccess (table (encodedMajorityCode code r))
    (readout (encodedMajorityCode code r)) (expandedInput N input) B target = _) at h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · intro target
    exact (h.2.2 target).trans
      (nativeRounds_fair_mass r Q (table code) (readout code) hc input t ht W (by rfl) target)
  · intro target hp
    rw [h.2.2 target,
        nativeRounds_fair_mass r Q (table code) (readout code) hc input t ht W (by rfl)]
    exact independentMajorityMass_ge (table code) (readout code) (input.map some) t r target ht hp

theorem encodedMajorityCode_polynomial (code : Code) (r c k : ℕ) (hc : commonHalt code)
    (htotal : ∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
      (coinTapeRun (table code) (readout code) (input.map some) (List.ofFn w)).1 ≠ none) :
    ∃ d : ℕ, 0 < d ∧ ∀ input : List Bool,
      let T := c * input.length ^ k + c
      let B := d * input.length ^ (2 * (k + 1)) + d
      (∀ w : Fin B → Bool,
        (coinTapeRun (table (encodedMajorityCode code r)) (readout (encodedMajorityCode code r))
          (expandedInput (2 * r + 1) input) (List.ofFn w)).1 ≠ none) ∧
      (∀ w : Fin B → Bool,
        coinTapeTransitionCount (table (encodedMajorityCode code r)) (expandedInput (2 * r + 1) input) (List.ofFn w) ≤ B) ∧
      (∀ target : Bool,
        fairTapeSuccess (table (encodedMajorityCode code r)) (readout (encodedMajorityCode code r))
          (expandedInput (2 * r + 1) input) B target =
            independentMajorityMass (table code) (readout code) (input.map some) T r target) ∧
      (∀ target : Bool, (2 / 3 : ℝ) ≤ fairTapeSuccess (table code) (readout code) (input.map some) T target →
        1 - (8 / 9 : ℝ) ^ r ≤ fairTapeSuccess (table (encodedMajorityCode code r))
          (readout (encodedMajorityCode code r)) (expandedInput (2 * r + 1) input) B target) := by
  let N := 2 * r + 1
  let C := bitMicroWidth N
  let D := 2 * (N + 2) + C * (N * (4 * c + 10) + 1) + 1
  refine ⟨D, by dsimp [D]; omega, ?_⟩
  intro input
  (try dsimp only)
  apply encodedMajorityCode_budget code r hc input (c * input.length ^ k + c) (htotal input)
  have hw := rounds_poly_bound N c k input.length
  have hm := Nat.mul_le_mul_left C hw
  change 2 * (N + 2) + (N * (3 * input.length + 2 * (c * input.length ^ k + c) + 6)) * C ≤
    D * input.length ^ (2 * (k + 1)) + D
  dsimp only [D]
  nlinarith [Nat.zero_le (2 * (N + 2) * input.length ^ (2 * (k + 1)))]

theorem expandedSequenceLabels_zero (N : ℕ) (next : Code) :
    expandedSequenceLabels N next (.inl 0) = 0 := by
  apply Fin.ext
  simp [expandedSequenceLabels, finSumFinEquiv]

theorem expandedSequence_initial (N : ℕ) (next : Code) (input : List Bool) :
    relabelCfg (expandedSequenceLabels N next) (mapCfg Sum.inl (Turing.TM0.init (input.map some))) =
      Turing.TM0.init (input.map some) := by
  change (⟨expandedSequenceLabels N next (.inl 0), Turing.Tape.mk₁ (input.map some)⟩ :
    Turing.TM0.Cfg (Option Bool) (Fin (expandedSequenceMax N next + 1))) = _
  rw [expandedSequenceLabels_zero]
  rfl

theorem expandedSequence_run (N : ℕ) (next : Code) (input : List Bool)
    (front : Fin (expandTime N input.length) → Bool) (switch : Bool) (tail : List Bool) :
    coinTapeRun (expandedSequenceTable N next) (expandedSequenceAccept N next) (input.map some)
        (List.ofFn front ++ switch :: tail) =
      Prod.map id (fun n => n + expandTime N input.length + 1)
        (coinTapeRun (table next) (readout next) (expandedInput N input) tail) ∧
    coinTapeTransitionCount (expandedSequenceTable N next) (input.map some)
        (List.ofFn front ++ switch :: tail) =
      coinTapeTransitionCount (table next) (expandedInput N input) tail + expandTime N input.length + 1 := by
  let cfg : Turing.TM0.Cfg (Option Bool) (Fin (controlSize (expandCode N) + 1)) :=
      Turing.TM0.init (input.map some)
  let cfg₂ : Turing.TM0.Cfg (Option Bool) (Fin (controlSize next + 1)) :=
      ⟨default, Turing.Tape.mk₁ (expandedInput N input)⟩
  let seq := sequenceCoinTable (table (expandCode N)) (table next)
  let coins := List.ofFn front ++ switch :: tail
  have hp := expandCode_then_coin_source N (table next) input front switch tail
  have ho :=
      coinConfigRunAux_readout seq (sourcePhaseAccept (readout next)) coins (mapCfg Sum.inl cfg)
  have hs := coinConfigRunAux_readout (table next) (readout next) tail cfg₂
  have hseq : coinTapeRunAux seq (sourcePhaseAccept (readout next)) coins (mapCfg Sum.inl cfg) =
      Prod.map id (fun n => n + expandTime N input.length + 1)
        (coinTapeRunAux (table next) (readout next) tail cfg₂) := by
    rw [← ho.1, hp.1, hp.2.1]
    simp only [Option.map_map, mapCfg, sourcePhaseAccept, Function.comp_def]
    rw [← hs.1]
    rfl
  have hseqCount : coinTapeTransitionCountAux seq coins (mapCfg Sum.inl cfg) =
      coinTapeTransitionCountAux (table next) tail cfg₂ + expandTime N input.length + 1 := by
    rw [← ho.2, hp.2.2, hs.2]
  have hr :=
      relabel_runAux (expandedSequenceLabels N next) seq (sourcePhaseAccept (readout next)) coins
      (mapCfg Sum.inl cfg)
  have ht := relabel_transitionsAux (expandedSequenceLabels N next) seq coins (mapCfg Sum.inl cfg)
  rw [expandedSequence_initial] at hr ht
  change coinTapeRunAux (expandedSequenceTable N next) (expandedSequenceAccept N next) coins
      (Turing.TM0.init (input.map some)) =
    coinTapeRunAux seq (sourcePhaseAccept (readout next)) coins (mapCfg Sum.inl cfg) at hr
  change coinTapeTransitionCountAux (expandedSequenceTable N next) coins
      (Turing.TM0.init (input.map some)) =
    coinTapeTransitionCountAux seq coins (mapCfg Sum.inl cfg) at ht
  constructor
  · change coinTapeRunAux (expandedSequenceTable N next) (expandedSequenceAccept N next) coins (Turing.TM0.init (input.map some)) = _
    rw [hr, hseq]
    rfl
  · change coinTapeTransitionCountAux (expandedSequenceTable N next) coins (Turing.TM0.init (input.map some)) = _
    rw [ht, hseqCount]
    rfl

theorem expandThenCode_run (N : ℕ) (next : Code) (input : List Bool)
    (front : Fin (expandTime N input.length) → Bool) (switch : Bool) (tail : List Bool) :
    coinTapeRun (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some)
        (List.ofFn front ++ switch :: tail) =
      Prod.map id (fun n => n + expandTime N input.length + 1)
        (coinTapeRun (table next) (readout next) (expandedInput N input) tail) ∧
    coinTapeTransitionCount (table (expandThenCode N next)) (input.map some)
        (List.ofFn front ++ switch :: tail) =
      coinTapeTransitionCount (table next) (expandedInput N input) tail + expandTime N input.length + 1 := by
  have h := encodeMachine_run (expandedSequenceMax N next) (expandedSequenceTable N next)
    (expandedSequenceAccept N next) (input.map some) (List.ofFn front ++ switch :: tail)
  have hr := expandedSequence_run N next input front switch tail
  exact ⟨h.1.trans hr.1, h.2.trans hr.2⟩

theorem expandedSequence_commonHalt (N : ℕ) (next : Code) (hc : commonHalt next) :
    ∀ q s, (expandedSequenceTable N next false q s = none) ↔ (expandedSequenceTable N next true q s = none) := by
  intro q s
  simpa only [expandedSequenceTable, relabelTable, Option.map_eq_none_iff] using!
    sequenceCoinTable_commonHalt (table (expandCode N)) (table next) hc ((expandedSequenceLabels N next).symm q) s

theorem expandThenCode_commonHalt (N : ℕ) (next : Code) (hc : commonHalt next) : commonHalt (expandThenCode N next) := by
  unfold commonHalt
  simpa only [expandThenCode, table_encode] using! expandedSequence_commonHalt N next hc

theorem rawMajorityCode_commonHalt (code : Code) (r : ℕ) : commonHalt (rawMajorityCode code r) :=
  expandThenCode_commonHalt (2 * r + 1) (encodedMajorityCode code r) (encodedMajorityCode_commonHalt code r)

theorem expandThenWords_ofFn (N : ℕ) (input : List Bool) (D : ℕ)
    (p : (Fin (expandTime N input.length) → Bool) × Bool × (Fin D → Bool)) :
    List.ofFn (expandThenWords N input D p) = List.ofFn p.1 ++ p.2.1 :: List.ofFn p.2.2 := by
  change List.ofFn (Fin.append p.1 (Fin.cons p.2.1 p.2.2)) = _
  rw [List.ofFn_fin_append, List.ofFn_cons]

theorem expandThenCode_fair_mass (N : ℕ) (next : Code) (input : List Bool) (D : ℕ) (target : Bool) :
    fairTapeSuccess (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some)
      (expandTime N input.length + (D + 1)) target =
      fairTapeSuccess (table next) (readout next) (expandedInput N input) D target := by
  have hp (p : (Fin (expandTime N input.length) → Bool) × Bool × (Fin D → Bool)) :
      (coinTapeRun (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some)
        (List.ofFn (expandThenWords N input D p))).1 =
        (coinTapeRun (table next) (readout next) (expandedInput N input) (List.ofFn p.2.2)).1 := by
    rw [expandThenWords_ofFn, (expandThenCode_run N next input p.1 p.2.1 (List.ofFn p.2.2)).1]
    rfl
  have hs : (∑ w : Fin (expandTime N input.length + (D + 1)) → Bool,
      if (coinTapeRun (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some)
        (List.ofFn w)).1 = some target then (1 : ℝ) else 0) =
      (2 : ℝ) ^ expandTime N input.length * 2 *
        (∑ w : Fin D → Bool, if (coinTapeRun (table next) (readout next) (expandedInput N input)
          (List.ofFn w)).1 = some target then (1 : ℝ) else 0) := by
    rw [← (expandThenWords N input D).sum_comp]
    simp_rw [hp]
    let f (w : Fin D → Bool) : ℝ := if (coinTapeRun (table next) (readout next)
      (expandedInput N input) (List.ofFn w)).1 = some target then 1 else 0
    change (∑ p : (Fin (expandTime N input.length) → Bool) × Bool × (Fin D → Bool), f p.2.2) =
      (2 : ℝ) ^ expandTime N input.length * 2 * (∑ w : Fin D → Bool, f w)
    simp only [Fintype.sum_prod_type]
    simp [mul_assoc]

  unfold fairTapeSuccess
  rw [hs, pow_add, pow_succ]
  have he : (2 : ℝ) ^ expandTime N input.length ≠ 0 := pow_ne_zero _ (by norm_num)
  have hd : (2 : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [he, hd]

theorem expandThenCode_total_at (N : ℕ) (next : Code) (input : List Bool) (D : ℕ)
    (ht : ∀ w : Fin D → Bool, (coinTapeRun (table next) (readout next) (expandedInput N input) (List.ofFn w)).1 ≠ none) :
    ∀ w : Fin (expandTime N input.length + (D + 1)) → Bool,
      (coinTapeRun (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some) (List.ofFn w)).1 ≠ none := by
  intro w
  let p := (expandThenWords N input D).symm w
  have hw : List.ofFn w = List.ofFn p.1 ++ p.2.1 :: List.ofFn p.2.2 := by
    rw [← (expandThenWords N input D).apply_symm_apply w]
    exact expandThenWords_ofFn N input D p
  rw [hw, (expandThenCode_run N next input p.1 p.2.1 (List.ofFn p.2.2)).1]
  exact ht p.2.2

theorem expandThenCode_full_budget (N : ℕ) (next : Code) (hc : commonHalt next)
    (input : List Bool) (D : ℕ)
    (ht : ∀ w : Fin D → Bool, (coinTapeRun (table next) (readout next) (expandedInput N input) (List.ofFn w)).1 ≠ none)
    (B : ℕ) (hB : expandTime N input.length + (D + 1) ≤ B) :
    (∀ w : Fin B → Bool,
      (coinTapeRun (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some) (List.ofFn w)).1 ≠ none) ∧
    (∀ w : Fin B → Bool,
      coinTapeTransitionCount (table (expandThenCode N next)) (input.map some) (List.ofFn w) ≤ B) ∧
    (∀ target : Bool,
      fairTapeSuccess (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some) B target =
        fairTapeSuccess (table next) (readout next) (expandedInput N input) D target) := by
  have ht' := expandThenCode_total_at N next input D ht
  refine ⟨coinTape_totality_monotone _ _ _ _ ht' B hB, ?_, ?_⟩
  · intro w
    simpa only [List.length_ofFn] using! coinTapeTransitionCount_le_budget (table (expandThenCode N next))
      (expandThenCode_commonHalt N next hc) (input.map some) (List.ofFn w)
  · intro target
    exact (fairTapeSuccess_of_total _ _ _ _ ht' B hB target).trans
        (expandThenCode_fair_mass N next input D target)

theorem expandThenCode_poly_bound (N d k n : ℕ) :
    expandTime N n + ((d * n ^ (2 * (k + 1)) + d) + 1) ≤
      (d + (3 * N + 13) + 1) * n ^ (2 * (k + 1)) + (d + (3 * N + 13) + 1) := by
  have he := expandTime_poly_bound N n
  have hp : n ^ 2 ≤ n ^ (2 * (k + 1)) := by
    by_cases hn : n = 0
    · subst n
      simp
    · exact Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_left (3 * N + 13) hp
  nlinarith [Nat.zero_le (n ^ (2 * (k + 1)))]

theorem rawMajorityCode_polynomial (code : Code) (r c k : ℕ) (hc : commonHalt code)
    (htotal : ∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
      (coinTapeRun (table code) (readout code) (input.map some) (List.ofFn w)).1 ≠ none) :
    ∃ d : ℕ, 0 < d ∧ commonHalt (rawMajorityCode code r) ∧ ∀ input : List Bool,
      let T := c * input.length ^ k + c
      let B := d * input.length ^ (2 * (k + 1)) + d
      (∀ w : Fin B → Bool,
        (coinTapeRun (table (rawMajorityCode code r)) (readout (rawMajorityCode code r))
          (input.map some) (List.ofFn w)).1 ≠ none) ∧
      (∀ w : Fin B → Bool,
        coinTapeTransitionCount (table (rawMajorityCode code r)) (input.map some) (List.ofFn w) ≤ B) ∧
      (∀ target : Bool,
        fairTapeSuccess (table (rawMajorityCode code r)) (readout (rawMajorityCode code r))
          (input.map some) B target = independentMajorityMass (table code) (readout code) (input.map some) T r target) ∧
      (∀ target : Bool, (2 / 3 : ℝ) ≤ fairTapeSuccess (table code) (readout code) (input.map some) T target →
        1 - (8 / 9 : ℝ) ^ r ≤ fairTapeSuccess (table (rawMajorityCode code r))
          (readout (rawMajorityCode code r)) (input.map some) B target) := by
  obtain ⟨d, hd, h⟩ := encodedMajorityCode_polynomial code r c k hc htotal
  let N := 2 * r + 1
  let D := d + (3 * N + 13) + 1
  refine ⟨D, by dsimp [D]; omega, rawMajorityCode_commonHalt code r, ?_⟩
  intro input
  have hbit := h input
  let Bbit := d * input.length ^ (2 * (k + 1)) + d
  let Braw := D * input.length ^ (2 * (k + 1)) + D
  have hb : expandTime N input.length + (Bbit + 1) ≤ Braw :=
      expandThenCode_poly_bound N d k input.length
  have hr := expandThenCode_full_budget N (encodedMajorityCode code r) (encodedMajorityCode_commonHalt code r)
    input Bbit hbit.1 Braw hb
  refine ⟨hr.1, hr.2.1, ?_, ?_⟩
  · intro target
    exact (hr.2.2 target).trans (hbit.2.2.1 target)
  · intro target hp
    exact (hbit.2.2.2 target hp).trans (hr.2.2 target).symm.le

theorem codeTabulate_eq_ofFn (n : ℕ) (row : ℕ → ℕ) :
    codeTabulate n row = List.ofFn (fun i : Fin n => row i.val) := by
  apply List.ext_getElem
  · simp [codeTabulate]
  · intro i hi hj
    simp only [codeTabulate, List.getElem_map, List.getElem_range, List.getElem_ofFn]

theorem encodeMachine_eq_codeEnumerate (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    encodeMachine Q M a = codeEnumerate Q
      (fun q => a ⟨q % (Q + 1), Nat.mod_lt _ (by omega)⟩)
      (fun i => encodeTransition (M (decide (3 * (Q + 1) ≤ i))
        ⟨i / 3 % (Q + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (i % 3)))) := by
  unfold encodeMachine codeEnumerate
  rw [codeTabulate_eq_ofFn, codeTabulate_eq_ofFn]
  apply congrArg (List.cons Q)
  apply congrArg₂ List.append
  · apply congrArg List.ofFn
    funext q
    simp only [Nat.mod_eq_of_lt q.isLt]
  · rfl

theorem primrec_controlSize : Primrec controlSize := by
  exact (Primrec.list_getD 0).comp Primrec.id (Primrec.const 0)

theorem primrec_readoutNat : Primrec₂ (fun (code : Code) (q : ℕ) => code.getD (1 + q) 0 % 2 == 1) := by
  change Primrec (fun p : Code × ℕ => p.1.getD (1 + p.2) 0 % 2 == 1)
  have hidx : Primrec (fun p : Code × ℕ => 1 + p.2) :=
      Primrec.nat_add.comp (Primrec.const 1) Primrec.snd
  have hget : Primrec (fun p : Code × ℕ => p.1.getD (1 + p.2) 0) :=
      (Primrec.list_getD 0).comp Primrec.fst hidx
  exact Primrec.beq.comp (Primrec.nat_mod.comp hget (Primrec.const 2)) (Primrec.const 1)

theorem primrec_codeTabulate {α : Type*} [Primcodable α] {bound : α → ℕ} {row : α → ℕ → ℕ}
    (hb : Primrec bound) (hr : Primrec₂ row) : Primrec (fun p => codeTabulate (bound p) (row p)) := by
  exact Primrec.list_map (Primrec.list_range.comp hb) hr

theorem primrec_codeEnumerate {α : Type*} [Primcodable α] {bound : α → ℕ}
    {output : α → ℕ → Bool} {row : α → ℕ → ℕ}
    (hb : Primrec bound) (ho : Primrec₂ output) (hr : Primrec₂ row) :
    Primrec (fun p => codeEnumerate (bound p) (output p) (row p)) := by
  have hq := Primrec.nat_add.comp hb (Primrec.const 1)
  have hs := Primrec.nat_mul.comp (Primrec.const 6) hq
  have hbool : Primrec Bool.toNat := Primrec.dom_bool Bool.toNat
  have ha := primrec_codeTabulate hq (hbool.comp₂ ho)
  have ht := primrec_codeTabulate hs hr
  exact Primrec.list_cons.comp hb (Primrec.list_append.comp ha ht)

theorem primrec_natPow : Primrec₂ (fun n k : ℕ => n ^ k) := Primrec₂.unpaired'.mp Nat.Primrec.pow

theorem primrec_expandControlMax : Primrec expandControlMax := by
  have hp :=
      primrec_natPow.comp (Primrec.const 3) (Primrec.nat_add.comp Primrec.id (Primrec.const 2))
  have hm := Primrec.nat_mul.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 3)) hp
  exact Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 12)
    (Primrec.nat_mul.comp (Primrec.const 2) hm)) (Primrec.const 1)

theorem primrec_roundsControlMax : Primrec₂ roundsControlMax := by
  change Primrec (fun p : ℕ × ℕ => roundsControlMax p.1 p.2)
  have hn : Primrec (fun p : ℕ × ℕ => p.1 + 1) := Primrec.nat_add.comp Primrec.fst (Primrec.const 1)
  have hq : Primrec (fun p : ℕ × ℕ => 2 * p.2 + 11) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 11)
  exact Primrec.nat_sub.comp (Primrec.nat_mul.comp hn (Primrec.nat_mul.comp hn hq))
      (Primrec.const 1)

theorem primrec_bitSimControlMax : Primrec₂ bitSimControlMax := by
  change Primrec (fun p : ℕ × ℕ => bitSimControlMax p.1 p.2)
  have hn : Primrec (fun p : ℕ × ℕ => p.1 + 2) := Primrec.nat_add.comp Primrec.fst (Primrec.const 2)
  have hp := primrec_natPow.comp (Primrec.const 3) hn
  have hi := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) hn) (Primrec.const 1)
  have hq : Primrec (fun p : ℕ × ℕ => p.2 + 1) := Primrec.nat_add.comp Primrec.snd (Primrec.const 1)
  exact Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 9)
    (Primrec.nat_mul.comp hq (Primrec.nat_mul.comp hi hp))) (Primrec.const 1)

theorem expandedSequence_initial_live (N : ℕ) (next : Code) (input : List Bool) :
    coinHalt (expandedSequenceTable N next) (Turing.TM0.init (input.map some)) = false := by
  rw [← expandedSequence_initial N next input]
  exact (relabel_coinHalt (expandedSequenceLabels N next)
    (sequenceCoinTable (table (expandCode N)) (table next))
    (mapCfg Sum.inl (Turing.TM0.init (input.map some)))).trans
      (sequence_coinHalt_left (table (expandCode N)) (table next) (Turing.TM0.init (input.map some)))

theorem expandThenCode_initial_pending (N : ℕ) (next : Code) (input : List Bool) :
    coinTapeRun (table (expandThenCode N next)) (readout (expandThenCode N next)) (input.map some) [] = (none, 0) ∧
      coinTapeTransitionCount (table (expandThenCode N next)) (input.map some) [] = 0 := by
  have h := encodeMachine_run (expandedSequenceMax N next) (expandedSequenceTable N next)
    (expandedSequenceAccept N next) (input.map some) []
  refine ⟨h.1.trans ?_, h.2.trans rfl⟩
  simp only [coinTapeRun, coinTapeRunAux, expandedSequence_initial_live, Bool.false_eq_true,
      ↓reduceIte]

theorem rawMajorityCode_controlSize (code : Code) (r : ℕ) :
    controlSize (rawMajorityCode code r) =
      expandControlMax (2 * r + 1) +
        bitSimControlMax (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code)) + 1 := by
  simp only [rawMajorityCode, expandThenCode, controlSize_encode, expandedSequenceMax,
    expandCode, encodedMajorityCode, bitSimCode]

theorem primrec_rawMajorityCode_controlSize : Primrec₂ (fun (code : Code) (r : ℕ) => controlSize (rawMajorityCode code r)) := by
  change Primrec (fun p : Code × ℕ => controlSize (rawMajorityCode p.1 p.2))
  have hn : Primrec (fun p : Code × ℕ => 2 * p.2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 1)
  have hq : Primrec (fun p : Code × ℕ => controlSize p.1) := primrec_controlSize.comp Primrec.fst
  have hr := primrec_roundsControlMax.comp hn hq
  have hb := primrec_bitSimControlMax.comp hn hr
  have he := primrec_expandControlMax.comp hn
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp he hb) (Primrec.const 1)).of_eq
    (fun p => (rawMajorityCode_controlSize p.1 p.2).symm)

theorem roundsLabels_count_nat (N Q : ℕ) (q : Fin (roundsControlMax N Q + 1)) :
    ((roundsLabels N Q).symm q).2.1.val = q.val % ((N + 1) * (2 * Q + 11)) / (2 * Q + 11) := by
  rfl

theorem bitSimLabels_source_nat (N Q : ℕ) (q : Fin (bitSimControlMax N Q + 1)) :
    ((bitSimLabels N Q).symm q).2.1.val =
      q.val % ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) /
        ((3 * (N + 2) + 1) * 3 ^ (N + 2)) := by
  rfl

theorem nativeBitSimAccept_rounds_nat (N Q : ℕ)
    (q : Fin (bitSimControlMax N (roundsControlMax N Q) + 1)) :
    nativeBitSimAccept N (roundsControlMax N Q) (nativeRoundsAccept N Q) q = bitMajorityOutputNat N Q q.val := by
  unfold nativeBitSimAccept nativeRoundsAccept roundsAccept
  rw [roundsLabels_count_nat, bitSimLabels_source_nat]
  rfl

theorem encodedMajorityCode_readout_nat (code : Code) (r : ℕ)
    (q : Fin (controlSize (encodedMajorityCode code r) + 1)) :
    readout (encodedMajorityCode code r) q = bitMajorityOutputNat (2 * r + 1) (controlSize code) q.val := by
  simpa only [encodedMajorityCode, bitSimCode, readout_encode_eq] using!
    nativeBitSimAccept_rounds_nat (2 * r + 1) (controlSize code) q

theorem expandedSequenceAccept_nat (N : ℕ) (next : Code)
    (q : Fin (expandedSequenceMax N next + 1)) :
    expandedSequenceAccept N next q =
      if q.val < controlSize (expandCode N) + 1 then false else
        readout next ⟨(q.val - (controlSize (expandCode N) + 1)) % (controlSize next + 1), Nat.mod_lt _ (by omega)⟩ := by
  generalize he : (expandedSequenceLabels N next).symm q = s
  have hq : expandedSequenceLabels N next s = q := by
    rw [← he]
    exact (expandedSequenceLabels N next).apply_symm_apply q
  cases s with
  | inl a =>
    have hv : q.val = a.val := by rw [← hq]; rfl
    have hl : q.val < controlSize (expandCode N) + 1 := by rw [hv]; exact a.isLt
    simp [expandedSequenceAccept, he, sourcePhaseAccept, hl]
  | inr a =>
    have hv : q.val = (controlSize (expandCode N) + 1) + a.val := by rw [← hq]; rfl
    have hl : ¬ q.val < controlSize (expandCode N) + 1 := by omega
    simp only [expandedSequenceAccept, he, sourcePhaseAccept, hl, ↓reduceIte]
    congr 1
    apply Fin.ext
    simp only [hv, Nat.add_sub_cancel_left, Nat.mod_eq_of_lt a.isLt]

theorem rawMajorityCode_readout_nat (code : Code) (r : ℕ)
    (q : Fin (controlSize (rawMajorityCode code r) + 1)) :
    readout (rawMajorityCode code r) q = rawMajorityOutputNat code r q.val := by
  simp only [rawMajorityCode, expandThenCode, readout_encode_eq]
  rw [expandedSequenceAccept_nat]
  simp only [expandCode, encodedMajorityCode, bitSimCode, controlSize_encode,
    readout_encode_eq, nativeBitSimAccept_rounds_nat]
  have hq : q.val < expandControlMax (2 * r + 1) + 1 +
      (bitSimControlMax (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code)) + 1) := by
    have h := q.isLt
    have hs := rawMajorityCode_controlSize code r
    omega
  simp only [rawMajorityOutputNat, Nat.mod_eq_of_lt hq]

theorem primrec_bitMajorityOutputNat :
    Primrec (fun p : ℕ × ℕ × ℕ => bitMajorityOutputNat p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hQ : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlen := Primrec.nat_add.comp hn (Primrec.const 2)
  have hs := Primrec.nat_mul.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) hlen) (Primrec.const 1))
    (primrec_natPow.comp (Primrec.const 3) hlen)
  have hwideSize := Primrec.nat_add.comp (primrec_roundsControlMax.comp hn hQ) (Primrec.const 1)
  have hwide :=
      Primrec.nat_div.comp (Primrec.nat_mod.comp hq (Primrec.nat_mul.comp hwideSize hs)) hs
  have hprog := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hQ) (Primrec.const 11)
  have hcount := Primrec.nat_div.comp
    (Primrec.nat_mod.comp hwide (Primrec.nat_mul.comp (Primrec.nat_add.comp hn (Primrec.const 1)) hprog)) hprog
  exact (Primrec.nat_lt.comp (Primrec.nat_div.comp hn (Primrec.const 2)) hcount).decide

theorem primrec_rawMajorityOutputNat :
    Primrec (fun p : Code × ℕ × ℕ => rawMajorityOutputNat p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : Code × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hq : Primrec (fun p : Code × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hcode : Primrec (fun p : Code × ℕ × ℕ => p.1) := Primrec.fst
  have hn := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hr) (Primrec.const 1)
  have hQ := primrec_controlSize.comp hcode
  have he := Primrec.nat_add.comp (primrec_expandControlMax.comp hn) (Primrec.const 1)
  have hb := Primrec.nat_add.comp
    (primrec_bitSimControlMax.comp hn (primrec_roundsControlMax.comp hn hQ)) (Primrec.const 1)
  have hl := Primrec.nat_mod.comp hq (Primrec.nat_add.comp he hb)
  have hbit := Primrec.nat_mod.comp (Primrec.nat_sub.comp hl he) hb
  have ho := primrec_bitMajorityOutputNat.comp (hn.pair (hQ.pair hbit))
  exact Primrec.ite (Primrec.nat_lt.comp hl he) (Primrec.const false) ho

theorem rawMajorityOutputNat_mod (code : Code) (r q : ℕ) :
    rawMajorityOutputNat code r (q % (controlSize (rawMajorityCode code r) + 1)) =
      rawMajorityOutputNat code r q := by
  have hs : controlSize (rawMajorityCode code r) + 1 =
      (expandControlMax (2 * r + 1) + 1) +
        (bitSimControlMax (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code)) + 1) := by
    rw [rawMajorityCode_controlSize]
    omega
  rw [hs]
  simp only [rawMajorityOutputNat, Nat.mod_mod]

theorem rawMajorityCode_readout_mod (code : Code) (r q : ℕ) :
    readout (rawMajorityCode code r) ⟨q % (controlSize (rawMajorityCode code r) + 1), Nat.mod_lt _ (by omega)⟩ =
      rawMajorityOutputNat code r q := by
  rw [rawMajorityCode_readout_nat, rawMajorityOutputNat_mod]

theorem primrec_rawMajorityCode_readout :
    Primrec (fun p : Code × ℕ × ℕ =>
      readout (rawMajorityCode p.1 p.2.1)
        ⟨p.2.2 % (controlSize (rawMajorityCode p.1 p.2.1) + 1), Nat.mod_lt _ (by omega)⟩) := by
  exact primrec_rawMajorityOutputNat.of_eq
      (fun p => (rawMajorityCode_readout_mod p.1 p.2.1 p.2.2).symm)

theorem encodeMachine_header (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    (encodeMachine Q M a).take (Q + 2) = Q :: List.ofFn (fun q => (a q).toNat) := by
  simp [encodeMachine, show Q + 2 = (Q + 1) + 1 by omega]

theorem rawMajorityCode_header (code : Code) (r : ℕ) :
    (rawMajorityCode code r).take (controlSize (rawMajorityCode code r) + 2) =
      controlSize (rawMajorityCode code r) ::
        codeTabulate (controlSize (rawMajorityCode code r) + 1)
          (fun q => (rawMajorityOutputNat code r q).toNat) := by
  rw [codeTabulate_eq_ofFn]
  have he := encodeMachine_header (expandedSequenceMax (2 * r + 1) (encodedMajorityCode code r))
    (expandedSequenceTable (2 * r + 1) (encodedMajorityCode code r))
    (expandedSequenceAccept (2 * r + 1) (encodedMajorityCode code r))
  change (rawMajorityCode code r).take (controlSize (rawMajorityCode code r) + 2) =
    controlSize (rawMajorityCode code r) :: List.ofFn (fun q => (rawMajorityOutputNat code r q.val).toNat)
  change (rawMajorityCode code r).take (controlSize (rawMajorityCode code r) + 2) = _ at he
  rw [he]
  congr 1
  apply congrArg List.ofFn
  funext q
  congr 1
  simpa only [rawMajorityCode, expandThenCode, readout_encode_eq] using!
      rawMajorityCode_readout_nat code r q

theorem primrec_rawMajorityCode_header :
    Primrec₂ (fun (code : Code) (r : ℕ) =>
      (rawMajorityCode code r).take (controlSize (rawMajorityCode code r) + 2)) := by
  change Primrec (fun p : Code × ℕ =>
    (rawMajorityCode p.1 p.2).take (controlSize (rawMajorityCode p.1 p.2) + 2))
  have hb : Primrec (fun p : Code × ℕ => controlSize (rawMajorityCode p.1 p.2) + 1) :=
    Primrec.nat_add.comp primrec_rawMajorityCode_controlSize (Primrec.const 1)
  have ho : Primrec₂ (fun (p : Code × ℕ) (q : ℕ) => (rawMajorityOutputNat p.1 p.2 q).toNat) := by
    have hc : Primrec (fun p : (Code × ℕ) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
    have hr : Primrec (fun p : (Code × ℕ) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
    exact (Primrec.dom_bool Bool.toNat).comp
      (primrec_rawMajorityOutputNat.comp (hc.pair (hr.pair Primrec.snd)))
  exact (Primrec.list_cons.comp primrec_rawMajorityCode_controlSize (primrec_codeTabulate hb ho)).of_eq
    (fun p => (rawMajorityCode_header p.1 p.2).symm)

theorem expandQueueLabels_nat (N : ℕ) (q : ExpandQueue N) :
    (expandQueueLabels N q).val = ∑ i : Fin (N + 2), symbolIndex (q i) * 3 ^ i.val := by
  rfl

theorem expandQueueLabels_digit (N : ℕ) (q : Fin (3 ^ (N + 2))) (i : Fin (N + 2)) :
    symbolIndex (((expandQueueLabels N).symm q) i) = queueDigitNat q.val i.val := by
  have h := congrArg Fin.val (optionBoolFin.apply_symm_apply
    (finFunctionFinEquiv.symm q i))
  exact h

theorem expandQueueLabels_digit_encode (N : ℕ) (q : ExpandQueue N) (i : Fin (N + 2)) :
    queueDigitNat (expandQueueLabels N q).val i.val = symbolIndex (q i) := by
  rw [← expandQueueLabels_digit]
  simp only [Equiv.symm_apply_apply]

theorem expandQueueLabels_update (N : ℕ) (q : ExpandQueue N) (i : Fin (N + 2)) (s : Option Bool) :
    (expandQueueLabels N (Function.update q i s)).val =
      queueUpdateNat (expandQueueLabels N q).val i.val (symbolIndex s) := by
  unfold queueUpdateNat
  rw [expandQueueLabels_digit_encode]
  have hq : (expandQueueLabels N q).val =
      (∑ j ∈ Finset.univ.erase i, symbolIndex (q j) * 3 ^ j.val) + symbolIndex (q i) * 3 ^ i.val := by
    rw [expandQueueLabels_nat, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [hq, Nat.add_sub_cancel]
  rw [expandQueueLabels_nat, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hij : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [Function.update_of_ne hij]

theorem expandQueueLabels_tail (N : ℕ) (q : ExpandQueue N) :
    (expandQueueLabels N q).val / 3 =
      ∑ i : Fin (N + 1), symbolIndex (q i.succ) * 3 ^ i.val := by
  rw [expandQueueLabels_nat, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
  have hmul : (∑ i : Fin (N + 1), symbolIndex (q i.succ) * (3 ^ i.val * 3)) =
      (∑ i : Fin (N + 1), symbolIndex (q i.succ) * 3 ^ i.val) * 3 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact (Nat.mul_assoc _ _ _).symm
  rw [hmul, Nat.add_mul_div_right _ _ (by omega)]
  have hlt : symbolIndex (q 0) < 3 := by
    cases q 0 with
    | none => decide
    | some b => cases b <;> decide
  rw [Nat.div_eq_of_lt hlt, Nat.zero_add]

theorem expandQueueLabels_push (N : ℕ) (q : ExpandQueue N) (s : Option Bool) :
    (expandQueueLabels N (expandQueuePush q s)).val =
      queuePushNat N (expandQueueLabels N q).val (symbolIndex s) := by
  unfold queuePushNat
  rw [expandQueueLabels_tail, expandQueueLabels_nat, Fin.sum_univ_castSucc]
  simp only [expandQueuePush, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

theorem primrec_queueDigitNat : Primrec₂ queueDigitNat := by
  change Primrec (fun p : ℕ × ℕ => queueDigitNat p.1 p.2)
  exact Primrec.nat_mod.comp
    (Primrec.nat_div.comp Primrec.fst (primrec_natPow.comp (Primrec.const 3) Primrec.snd)) (Primrec.const 3)

theorem primrec_queueUpdateNat : Primrec (fun p : ℕ × ℕ × ℕ => queueUpdateNat p.1 p.2.1 p.2.2) := by
  have hl : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hi : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp := primrec_natPow.comp (Primrec.const 3) hi
  have hold := Primrec.nat_mul.comp (primrec_queueDigitNat.comp hl hi) hp
  exact Primrec.nat_add.comp (Primrec.nat_sub.comp hl hold) (Primrec.nat_mul.comp hd hp)

theorem primrec_queuePushNat : Primrec (fun p : ℕ × ℕ × ℕ => queuePushNat p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hl : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hd : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.nat_add.comp (Primrec.nat_div.comp hl (Primrec.const 3))
    (Primrec.nat_mul.comp hd (primrec_natPow.comp (Primrec.const 3)
      (Primrec.nat_add.comp hn (Primrec.const 1))))

theorem expandLabels_nat (N : ℕ) (q : ExpandState N) :
    (expandLabels N q).val = expandLabelNat N q.1.val q.2.1.toNat q.2.2.1.val
      (expandQueueLabels N q.2.2.2).val := by
  rcases q with ⟨p, b, i, fifo⟩
  cases b <;> rfl

theorem expandQueueLabels_blank_iff (N : ℕ) (q : ExpandQueue N) :
    (expandQueueLabels N q).val = 0 ↔ ∀ i, q i = none := by
  constructor
  · intro h
    have he : expandQueueLabels N q = expandQueueLabels N (fun _ => none) := by
      rw [expandQueueLabels_zero]
      exact Fin.ext h
    have hf := (expandQueueLabels N).injective he
    intro i
    exact congrFun hf i
  · intro h
    have he : q = fun _ => none := funext h
    rw [he, expandQueueLabels_zero]
    rfl

theorem actionIndex_write (s : Option Bool) : actionIndex (.write s) = 2 + symbolIndex s := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

set_option maxHeartbeats 1000000 in

theorem expandInputTable_record (N : ℕ) (q : ExpandState N) (s : Option Bool) :
    encodeTransition ((expandInputTable N q s).map
      (fun p => (expandLabels N p.1, p.2))) =
      expandStepNat N q.1.val q.2.1.toNat q.2.2.1.val
        (expandQueueLabels N q.2.2.2).val (symbolIndex s) := by
  rcases q with ⟨phase, first, i, fifo⟩
  have hb := expandQueueLabels_blank_iff N fifo
  have hslot := expandQueueLabels_digit_encode N fifo (0 : Fin (N + 2))
  fin_cases phase <;> cases first <;> cases s with
  | none =>
    dsimp [expandInputTable, expandStepNat, symbolIndex]
    all_goals try simp only [Option.map]
    all_goals try split_ifs
    all_goals
      try dsimp only [Option.map, encodeTransition]
      repeat' (first
        | rw [expandLabels_nat]
        | rw [expandQueueLabels_update]
        | rw [expandQueueLabels_push]
        | rw [expandQueueLabels_digit_encode]
        | rw [expandQueueLabels_zero]
        | rw [actionIndex_write])
    all_goals try dsimp [actionIndex, symbolIndex]
    all_goals simp_all [symbolIndex]
  | some b =>
    cases b <;> dsimp [expandInputTable, expandStepNat, symbolIndex]
    all_goals try simp only [Option.map]
    all_goals try split_ifs
    all_goals
      try dsimp only [Option.map, encodeTransition]
      repeat' (first
        | rw [expandLabels_nat]
        | rw [expandQueueLabels_update]
        | rw [expandQueueLabels_push]
        | rw [expandQueueLabels_digit_encode]
        | rw [expandQueueLabels_zero]
        | rw [actionIndex_write])
    all_goals try dsimp [actionIndex, symbolIndex]
    all_goals simp_all [symbolIndex]

theorem primrec_expandLabelNat_comp {α : Type*} [Primcodable α]
    {n phase first i fifo : α → ℕ} (hn : Primrec n) (hp : Primrec phase)
    (hf : Primrec first) (hi : Primrec i) (hq : Primrec fifo) :
    Primrec (fun x => expandLabelNat (n x) (phase x) (first x) (i x) (fifo x)) := by
  have hpow := primrec_natPow.comp (Primrec.const 3) (Primrec.nat_add.comp hn (Primrec.const 2))
  have hblock := Primrec.nat_mul.comp (Primrec.nat_add.comp hn (Primrec.const 3)) hpow
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp hq (Primrec.nat_mul.comp hpow hi)) (Primrec.nat_mul.comp hblock hf))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) hblock) hp)

theorem primrec_expandStepNat_comp {α : Type*} [Primcodable α]
    {n phase first i fifo s : α → ℕ} (hn : Primrec n) (hp : Primrec phase)
    (hf : Primrec first) (hi : Primrec i) (hq : Primrec fifo) (hs : Primrec s) :
    Primrec (fun x => expandStepNat (n x) (phase x) (first x) (i x) (fifo x) (s x)) := by
  have he {p f j q a : α → ℕ} (hP : Primrec p) (hF : Primrec f) (hI : Primrec j)
      (hQ : Primrec q) (hA : Primrec a) :
      Primrec (fun x => 5 * expandLabelNat (n x) (p x) (f x) (j x) (q x) + a x + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 5) (primrec_expandLabelNat_comp hn hP hF hI hQ)) hA)
      (Primrec.const 1)
  have hnp1 := Primrec.nat_add.comp hn (Primrec.const 1)
  have hnp2 := Primrec.nat_add.comp hn (Primrec.const 2)
  have hip1 := Primrec.nat_add.comp hi (Primrec.const 1)
  have him1 := Primrec.nat_sub.comp hi (Primrec.const 1)
  have hupdate := primrec_queueUpdateNat.comp (hq.pair (hi.pair hs))
  have hpush := primrec_queuePushNat.comp (hn.pair (hq.pair hs))
  have hwrite :=
      Primrec.nat_add.comp (Primrec.const 2) (primrec_queueDigitNat.comp hq (Primrec.const 0))
  have hmark := Primrec.nat_add.comp (Primrec.const 2)
    (Primrec.ite (PrimrecPred.and (Primrec.eq.comp hf (Primrec.const 1)) (Primrec.eq.comp hi hn))
      (Primrec.const 2) (Primrec.const 0))
  unfold expandStepNat
  exact Primrec.ite (Primrec.eq.comp hp (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hs (Primrec.const 0)) (Primrec.const 0)
      (he (Primrec.const 1) (Primrec.const 1) (Primrec.const 0) (Primrec.const 0) (Primrec.const 1)))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 1))
      (Primrec.ite (Primrec.nat_lt.comp hi hnp2)
        (he (Primrec.const 2) hf hi hupdate hmark) (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 2))
      (Primrec.ite (Primrec.nat_lt.comp hip1 hnp2)
        (he (Primrec.const 1) hf hip1 hq (Primrec.const 1))
        (he (Primrec.const 3) hf (Primrec.const 0) hq (Primrec.const 1)))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 3))
      (Primrec.ite (PrimrecPred.and (Primrec.eq.comp hq (Primrec.const 0)) (Primrec.eq.comp hs (Primrec.const 0)))
        (he (Primrec.const 5) hf (Primrec.const 0) hq (Primrec.const 0))
        (he (Primrec.const 4) hf (Primrec.const 0) hpush hwrite))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 4))
      (he (Primrec.const 3) hf (Primrec.const 0) hq (Primrec.const 1))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 5))
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const 0))
        (he (Primrec.const 6) (Primrec.const 0) (Primrec.const 0) hq (Primrec.const 1))
        (he (Primrec.const 5) hf (Primrec.const 0) hq (Primrec.const 0)))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 6))
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const 0))
        (he (Primrec.const 7) (Primrec.const 0) (Primrec.const 0) hq (Primrec.const 0))
        (he (Primrec.const 1) (Primrec.const 0) (Primrec.const 0) (Primrec.const 0) (Primrec.const 1)))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 7))
      (he (Primrec.const 8) (Primrec.const 0) (Primrec.const 0) hq (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 8))
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const 2))
        (he (Primrec.const 10) (Primrec.const 0) hnp1 hq (Primrec.const 2))
        (he (Primrec.const 9) (Primrec.const 0) hnp2 hq (Primrec.const 0)))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 9))
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 1) hi)
        (he (Primrec.const 9) (Primrec.const 0) him1 hq (Primrec.const 0))
        (he (Primrec.const 8) (Primrec.const 0) (Primrec.const 0) hq (Primrec.const 0)))
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 10))
      (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 1) hi)
        (he (Primrec.const 10) (Primrec.const 0) him1 hq (Primrec.const 0))
        (he (Primrec.const 11) (Primrec.const 0) (Primrec.const 0) hq (Primrec.const 0)))
      (Primrec.const 0)))))))))))

theorem expandLabels_phase_nat (N : ℕ) (q : Fin (expandControlMax N + 1)) :
    ((expandLabels N).symm q).1.val = q.val / (2 * ((N + 3) * 3 ^ (N + 2))) := by
  rfl

theorem expandLabels_first_nat (N : ℕ) (q : Fin (expandControlMax N + 1)) :
    ((expandLabels N).symm q).2.1.toNat =
      q.val % (2 * ((N + 3) * 3 ^ (N + 2))) / ((N + 3) * 3 ^ (N + 2)) := by
  have h (j : Fin 2) : (finTwoEquiv j).toNat = j.val := by fin_cases j <;> rfl
  exact h _

theorem expandLabels_index_nat (N : ℕ) (q : Fin (expandControlMax N + 1)) :
    ((expandLabels N).symm q).2.2.1.val =
      q.val % (2 * ((N + 3) * 3 ^ (N + 2))) % ((N + 3) * 3 ^ (N + 2)) / 3 ^ (N + 2) := by
  rfl

theorem expandLabels_queue_nat (N : ℕ) (q : Fin (expandControlMax N + 1)) :
    (expandQueueLabels N (((expandLabels N).symm q).2.2.2)).val =
      q.val % (2 * ((N + 3) * 3 ^ (N + 2))) % ((N + 3) * 3 ^ (N + 2)) % 3 ^ (N + 2) := by
  exact congrArg Fin.val ((expandQueueLabels N).apply_symm_apply _)

theorem primrec_expandRowNat : Primrec₂ expandRowNat := by
  change Primrec (fun p : ℕ × ℕ => expandRowNat p.1 p.2)
  have hn : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hr : Primrec (fun p : ℕ × ℕ => p.2) := Primrec.snd
  have hlabel := Primrec.nat_mod.comp (Primrec.nat_div.comp hr (Primrec.const 3))
    (Primrec.nat_add.comp (primrec_expandControlMax.comp hn) (Primrec.const 1))
  have hslots := primrec_natPow.comp (Primrec.const 3) (Primrec.nat_add.comp hn (Primrec.const 2))
  have hblock := Primrec.nat_mul.comp (Primrec.nat_add.comp hn (Primrec.const 3)) hslots
  have htwo := Primrec.nat_mul.comp (Primrec.const 2) hblock
  have hrest := Primrec.nat_mod.comp hlabel htwo
  have hlow := Primrec.nat_mod.comp hrest hblock
  exact primrec_expandStepNat_comp hn (Primrec.nat_div.comp hlabel htwo)
    (Primrec.nat_div.comp hrest hblock) (Primrec.nat_div.comp hlow hslots)
    (Primrec.nat_mod.comp hlow hslots) (Primrec.nat_mod.comp hr (Primrec.const 3))

theorem nativeExpandTable_row_nat (N row : ℕ) :
    encodeTransition (nativeExpandTable N
      ⟨row / 3 % (expandControlMax N + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (row % 3))) =
      expandRowNat N row := by
  have hd : symbolIndex (decodeSymbol (row % 3)) = row % 3 := by
    exact congrArg Fin.val (optionBoolFin.apply_symm_apply ⟨row % 3, Nat.mod_lt _ (by omega)⟩)
  change encodeTransition
      ((expandInputTable N ((expandLabels N).symm _) (decodeSymbol (row % 3))).map _) = _
  rw [expandInputTable_record, expandLabels_phase_nat, expandLabels_first_nat, expandLabels_index_nat,
    expandLabels_queue_nat, hd]
  rfl

theorem expandCode_eq_codeEnumerate (N : ℕ) :
    expandCode N = codeEnumerate (expandControlMax N) (fun _ => false) (expandRowNat N) := by
  rw [expandCode, encodeMachine_eq_codeEnumerate]
  congr 1
  funext row
  exact nativeExpandTable_row_nat N row

theorem primrec_expandCode : Primrec expandCode := by
  have ho : Primrec₂ (fun (_ _ : ℕ) => false) := Primrec.const false
  exact (primrec_codeEnumerate primrec_expandControlMax ho primrec_expandRowNat).of_eq
    (fun N => (expandCode_eq_codeEnumerate N).symm)

theorem actionIndex_decodeAction (n : ℕ) : actionIndex (decodeAction n) = n % 5 := by
  unfold decodeAction
  have h : n % 5 < 5 := Nat.mod_lt _ (by omega)
  interval_cases he : n % 5 <;> rfl

theorem encodeTransition_decodeTransition (Q record : ℕ) :
    encodeTransition (decodeTransition Q record) = normalizeTransitionNat Q record := by
  cases record with
  | zero => rfl
  | succ n => simp [decodeTransition, encodeTransition, normalizeTransitionNat, actionIndex_decodeAction]

theorem sourceRowNat_table (code : Code) (coin : Bool) (q s : ℕ) :
    encodeTransition (table code coin ⟨q % (controlSize code + 1), Nat.mod_lt _ (by omega)⟩
      (decodeSymbol (s % 3))) = sourceRowNat code coin q s := by
  have hs : symbolIndex (decodeSymbol (s % 3)) = s % 3 :=
    congrArg Fin.val (optionBoolFin.apply_symm_apply ⟨s % 3, Nat.mod_lt _ (by omega)⟩)
  simp only [table, rowIndex, hs, encodeTransition_decodeTransition, sourceRowNat]
  simp only [Nat.add_assoc]

theorem expandedSequenceLabels_inl_val (N : ℕ) (next : Code)
    (q : Fin (controlSize (expandCode N) + 1)) :
    (expandedSequenceLabels N next (.inl q)).val = q.val := by rfl

theorem expandedSequenceLabels_inr_val (N : ℕ) (next : Code)
    (q : Fin (controlSize next + 1)) :
    (expandedSequenceLabels N next (.inr q)).val = expandControlMax N + 1 + q.val := by rfl

theorem expandedSequenceTable_left_record (N : ℕ) (next : Code) (coin : Bool)
    (q : Fin (controlSize (expandCode N) + 1)) (s : Option Bool) :
    encodeTransition (expandedSequenceTable N next coin (expandedSequenceLabels N next (.inl q)) s) =
      if encodeTransition (nativeExpandTable N q s) = 0 then
        5 * (expandControlMax N + 1) + (2 + symbolIndex s) + 1
      else encodeTransition (nativeExpandTable N q s) := by
  simp only [expandedSequenceTable, relabelTable]
  rw [Equiv.symm_apply_apply]
  simp only [sequenceCoinTable, sequenceTable]
  have ht : table (expandCode N) coin q s = nativeExpandTable N q s := by
    simp only [expandCode, table_encode]
  rw [ht]
  simp only [Fin.default_eq_zero]
  cases h : nativeExpandTable N q s with
  | none => simp [encodeTransition, expandedSequenceLabels_inr_val, actionIndex_write]
  | some p =>
    rcases p with ⟨q', action⟩
    simp [encodeTransition, expandedSequenceLabels_inl_val]

theorem expandedSequenceTable_right_record (N : ℕ) (next : Code) (coin : Bool)
    (q : Fin (controlSize next + 1)) (s : Option Bool) :
    encodeTransition (expandedSequenceTable N next coin (expandedSequenceLabels N next (.inr q)) s) =
      if encodeTransition (table next coin q s) = 0 then 0
      else 5 * (expandControlMax N + 1) + encodeTransition (table next coin q s) := by
  simp only [expandedSequenceTable, relabelTable, Equiv.symm_apply_apply, sequenceCoinTable,
      sequenceTable]
  cases h : table next coin q s with
  | none => rfl
  | some p =>
    rcases p with ⟨q', action⟩
    simp only [Option.map_some, encodeTransition, expandedSequenceLabels_inr_val]
    have hn : 5 * q'.val + actionIndex action + 1 ≠ 0 := by omega
    rw [if_neg hn]
    omega

theorem nativeExpandTable_record_nat (N : ℕ) (q : Fin (expandControlMax N + 1)) (s : Option Bool) :
    encodeTransition (nativeExpandTable N q s) = expandRowNat N (3 * q.val + symbolIndex s) := by
  have hs : symbolIndex s < 3 := (optionBoolFin s).isLt
  have hdiv : (3 * q.val + symbolIndex s) / 3 = q.val := by omega
  have hmod : (3 * q.val + symbolIndex s) % 3 = symbolIndex s := by omega
  simpa only [hdiv, Nat.mod_eq_of_lt q.isLt, hmod, decodeSymbol_symbolIndex] using!
    nativeExpandTable_row_nat N (3 * q.val + symbolIndex s)

theorem expandedSequenceMax_size (N : ℕ) (next : Code) :
    expandedSequenceMax N next + 1 = (expandControlMax N + 1) + (controlSize next + 1) := by
  simp only [expandedSequenceMax, expandCode, controlSize_encode]
  omega

theorem expandedSequenceTable_row_nat (N : ℕ) (next : Code) (row : ℕ) :
    encodeTransition (expandedSequenceTable N next (decide (3 * (expandedSequenceMax N next + 1) ≤ row))
      ⟨row / 3 % (expandedSequenceMax N next + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (row % 3))) =
      expandThenRowNat N next row := by
  let q : Fin (expandedSequenceMax N next + 1) :=
    ⟨row / 3 % (expandedSequenceMax N next + 1), Nat.mod_lt _ (by omega)⟩
  have hs : symbolIndex (decodeSymbol (row % 3)) = row % 3 :=
    congrArg Fin.val (optionBoolFin.apply_symm_apply ⟨row % 3, Nat.mod_lt _ (by omega)⟩)
  generalize he : (expandedSequenceLabels N next).symm q = z
  have hq : expandedSequenceLabels N next z = q := by
    rw [← he]
    exact (expandedSequenceLabels N next).apply_symm_apply q
  change encodeTransition (expandedSequenceTable N next _ q _) = _
  rw [← hq]
  cases z with
  | inl a =>
    rw [expandedSequenceTable_left_record, nativeExpandTable_record_nat, hs]
    have hv : row / 3 % (expandedSequenceMax N next + 1) = a.val := by
      exact (congrArg Fin.val hq).symm
    have ha : a.val < expandControlMax N + 1 := a.isLt
    simp only [expandThenRowNat, ← expandedSequenceMax_size, hv, ha, ↓reduceIte]
  | inr a =>
    rw [expandedSequenceTable_right_record]
    have hn : encodeTransition (table next (decide (3 * (expandedSequenceMax N next + 1) ≤ row)) a
        (decodeSymbol (row % 3))) =
        sourceRowNat next (decide (3 * (expandedSequenceMax N next + 1) ≤ row)) a.val (row % 3) := by
      simpa only [Nat.mod_eq_of_lt a.isLt, Nat.mod_mod] using!
        sourceRowNat_table next (decide (3 * (expandedSequenceMax N next + 1) ≤ row)) a.val (row % 3)
    rw [hn]
    have hv : row / 3 % (expandedSequenceMax N next + 1) = expandControlMax N + 1 + a.val := by
      exact (congrArg Fin.val hq).symm
    have ha : ¬ expandControlMax N + 1 + a.val < expandControlMax N + 1 := by omega
    simp only [expandThenRowNat, ← expandedSequenceMax_size, hv, ha, ↓reduceIte,
        Nat.add_sub_cancel_left]

theorem expandedSequenceAccept_serializer_nat (N : ℕ) (next : Code) (q : ℕ) :
    expandedSequenceAccept N next
      ⟨q % (expandedSequenceMax N next + 1), Nat.mod_lt _ (by omega)⟩ = expandThenOutputNat N next q := by
  rw [expandedSequenceAccept_nat]
  simp only [expandCode, controlSize_encode, expandedSequenceMax_size, expandThenOutputNat, readout]

theorem expandThenCode_eq_codeEnumerate (N : ℕ) (next : Code) :
    expandThenCode N next = codeEnumerate (expandedSequenceMax N next)
      (expandThenOutputNat N next) (expandThenRowNat N next) := by
  rw [expandThenCode, encodeMachine_eq_codeEnumerate]
  congr 1
  · funext q
    exact expandedSequenceAccept_serializer_nat N next q
  · funext row
    exact expandedSequenceTable_row_nat N next row

theorem primrec_normalizeTransitionNat : Primrec₂ normalizeTransitionNat := by
  change Primrec (fun p : ℕ × ℕ => normalizeTransitionNat p.1 p.2)
  have hsub : Primrec (fun p : ℕ × ℕ => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hlabel := Primrec.nat_mod.comp (Primrec.nat_div.comp hsub (Primrec.const 5))
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 5) hlabel)
      (Primrec.nat_mod.comp hsub (Primrec.const 5))) (Primrec.const 1))

theorem primrec_sourceRowNat_comp {α : Type*} [Primcodable α]
    {code : α → Code} {coin : α → Bool} {q s : α → ℕ}
    (hc : Primrec code) (hb : Primrec coin) (hq : Primrec q) (hs : Primrec s) :
    Primrec (fun x => sourceRowNat (code x) (coin x) (q x) (s x)) := by
  have hQ := primrec_controlSize.comp hc
  have hsize := Primrec.nat_add.comp hQ (Primrec.const 1)
  have hcoin := (Primrec.dom_bool Bool.toNat).comp hb
  have hrow := Primrec.nat_mul.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp hcoin hsize) (Primrec.nat_mod.comp hq hsize)) (Primrec.const 3)
  have hidx := Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1) hsize) hrow)
    (Primrec.nat_mod.comp hs (Primrec.const 3))
  exact primrec_normalizeTransitionNat.comp hQ ((Primrec.list_getD 0).comp hc hidx)

theorem primrec_expandThenOutputNat_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {code : α → Code} {q : α → ℕ}
    (hn : Primrec n) (hc : Primrec code) (hq : Primrec q) :
    Primrec (fun x => expandThenOutputNat (n x) (code x) (q x)) := by
  have he := Primrec.nat_add.comp (primrec_expandControlMax.comp hn) (Primrec.const 1)
  have hsize := Primrec.nat_add.comp (primrec_controlSize.comp hc) (Primrec.const 1)
  have hlabel := Primrec.nat_mod.comp hq (Primrec.nat_add.comp he hsize)
  have hlocal := Primrec.nat_mod.comp (Primrec.nat_sub.comp hlabel he) hsize
  have hidx := Primrec.nat_add.comp (Primrec.const 1) hlocal
  have hout := Primrec.beq.comp (Primrec.nat_mod.comp ((Primrec.list_getD 0).comp hc hidx)
    (Primrec.const 2)) (Primrec.const 1)
  exact Primrec.ite (Primrec.nat_lt.comp hlabel he) (Primrec.const false) hout

theorem primrec_expandThenRowNat_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {code : α → Code} {row : α → ℕ}
    (hn : Primrec n) (hc : Primrec code) (hr : Primrec row) :
    Primrec (fun x => expandThenRowNat (n x) (code x) (row x)) := by
  have he := Primrec.nat_add.comp (primrec_expandControlMax.comp hn) (Primrec.const 1)
  have hsize := Primrec.nat_add.comp (primrec_controlSize.comp hc) (Primrec.const 1)
  have htotal := Primrec.nat_add.comp he hsize
  have hq := Primrec.nat_mod.comp (Primrec.nat_div.comp hr (Primrec.const 3)) htotal
  have hs := Primrec.nat_mod.comp hr (Primrec.const 3)
  have hcoin := (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.const 3) htotal) hr).decide
  have hleft := primrec_expandRowNat.comp hn
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) hq) hs)
  have hright := primrec_sourceRowNat_comp hc hcoin (Primrec.nat_sub.comp hq he) hs
  have hswitch := Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 5) he) (Primrec.nat_add.comp (Primrec.const 2) hs)) (Primrec.const 1)
  exact Primrec.ite (Primrec.nat_lt.comp hq he)
    (Primrec.ite (Primrec.eq.comp hleft (Primrec.const 0)) hswitch hleft)
    (Primrec.ite (Primrec.eq.comp hright (Primrec.const 0)) (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 5) he) hright))

theorem primrec_expandedSequenceMax : Primrec₂ expandedSequenceMax := by
  change Primrec (fun p : ℕ × Code => expandedSequenceMax p.1 p.2)
  have hn : Primrec (fun p : ℕ × Code => expandControlMax p.1) :=
      primrec_expandControlMax.comp Primrec.fst
  have hc : Primrec (fun p : ℕ × Code => controlSize p.2) := primrec_controlSize.comp Primrec.snd
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp hn hc) (Primrec.const 1)).of_eq (fun p => by
    simp only [expandedSequenceMax, expandCode, controlSize_encode])

theorem primrec_expandThenCode : Primrec₂ expandThenCode := by
  change Primrec (fun p : ℕ × Code => expandThenCode p.1 p.2)
  have ho : Primrec₂ (fun (p : ℕ × Code) (q : ℕ) => expandThenOutputNat p.1 p.2 q) :=
    primrec_expandThenOutputNat_comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hr : Primrec₂ (fun (p : ℕ × Code) (q : ℕ) => expandThenRowNat p.1 p.2 q) :=
    primrec_expandThenRowNat_comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact (primrec_codeEnumerate primrec_expandedSequenceMax ho hr).of_eq
    (fun p => (expandThenCode_eq_codeEnumerate p.1 p.2).symm)

theorem cellBuffer_bufferCell (N : ℕ) (f : BitBuffer N) :
    cellBuffer N (bufferCell N f) = Function.update f (Fin.last (N + 1))
      (if f (Fin.last (N + 1)) == some true then some true else none) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [cellBuffer, bufferCell]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [cellBuffer, bufferCell]
    · simp [cellBuffer, bufferCell]

theorem cellBuffer_bufferCell_nat (N : ℕ) (f : BitBuffer N) :
    (expandQueueLabels N (cellBuffer N (bufferCell N f))).val =
      canonicalBufferNat N (expandQueueLabels N f).val := by
  rw [cellBuffer_bufferCell, expandQueueLabels_update]
  unfold canonicalBufferNat
  have hd := expandQueueLabels_digit_encode N f (Fin.last (N + 1))
  simp only [Fin.val_last] at hd
  rw [hd]
  congr 1
  cases h : f (Fin.last (N + 1)) with
  | none => rfl
  | some b => cases b <;> rfl

theorem primrec_canonicalBufferNat : Primrec₂ canonicalBufferNat := by
  change Primrec (fun p : ℕ × ℕ => canonicalBufferNat p.1 p.2)
  have hlast : Primrec (fun p : ℕ × ℕ => p.1 + 1) :=
      Primrec.nat_add.comp Primrec.fst (Primrec.const 1)
  have hd := primrec_queueDigitNat.comp Primrec.snd hlast
  have hhome :=
      Primrec.ite (Primrec.eq.comp hd (Primrec.const 2)) (Primrec.const 2) (Primrec.const 0)
  exact primrec_queueUpdateNat.comp (Primrec.snd.pair (hlast.pair hhome))

theorem canonicalBufferNat_cellBuffer (N : ℕ) (s : TrackCell N) :
    canonicalBufferNat N (expandQueueLabels N (cellBuffer N s)).val =
      (expandQueueLabels N (cellBuffer N s)).val := by
  simpa only [bufferCell_cellBuffer] using! (cellBuffer_bufferCell_nat N (cellBuffer N s)).symm

theorem canonicalBufferNat_lt (N : ℕ) (q : Fin (3 ^ (N + 2))) :
    canonicalBufferNat N q.val < 3 ^ (N + 2) := by
  have h := cellBuffer_bufferCell_nat N ((expandQueueLabels N).symm q)
  rw [Equiv.apply_symm_apply] at h
  rw [← h]
  exact (expandQueueLabels N (cellBuffer N (bufferCell N ((expandQueueLabels N).symm q)))).isLt

theorem canonicalBufferNat_idempotent (N : ℕ) (f : BitBuffer N) :
    canonicalBufferNat N (canonicalBufferNat N (expandQueueLabels N f).val) =
      canonicalBufferNat N (expandQueueLabels N f).val := by
  rw [← cellBuffer_bufferCell_nat, canonicalBufferNat_cellBuffer]

theorem bufferCell_canonicalBufferNat (N : ℕ) (q : Fin (3 ^ (N + 2))) :
    bufferCell N ((expandQueueLabels N).symm
      ⟨canonicalBufferNat N q.val, canonicalBufferNat_lt N q⟩) =
      bufferCell N ((expandQueueLabels N).symm q) := by
  have h : (expandQueueLabels N).symm
      ⟨canonicalBufferNat N q.val, canonicalBufferNat_lt N q⟩ =
      cellBuffer N (bufferCell N ((expandQueueLabels N).symm q)) := by
    apply (expandQueueLabels N).injective
    apply Fin.ext
    rw [Equiv.apply_symm_apply, cellBuffer_bufferCell_nat, Equiv.apply_symm_apply]
  rw [h, bufferCell_cellBuffer]

theorem bitSim_ready_canonical_isNone {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) (q : Λ) (i : Fin (3 * (N + 2) + 1))
    (buf : Fin (3 ^ (N + 2))) (c : Bool) (s : Option Bool) :
    (bitSimTable N M c (2, q, i, (expandQueueLabels N).symm buf) s).isNone =
      (M c q (bufferCell N ((expandQueueLabels N).symm
        ⟨canonicalBufferNat N buf.val, canonicalBufferNat_lt N buf⟩))).isNone := by
  rw [bitSim_ready_isNone, bufferCell_canonicalBufferNat]

theorem bitSimLabels_nat (N Q : ℕ) (q : BitSimState N (Fin (Q + 1))) :
    (bitSimLabels N Q q).val = bitSimLabelNat N Q q.1.val q.2.1.val q.2.2.1.val
      (expandQueueLabels N q.2.2.2).val := by rfl

theorem bitSimLabels_phase_nat (N Q : ℕ) (q : Fin (bitSimControlMax N Q + 1)) :
    ((bitSimLabels N Q).symm q).1.val =
      q.val / ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) := by rfl

theorem bitSimLabels_index_nat (N Q : ℕ) (q : Fin (bitSimControlMax N Q + 1)) :
    ((bitSimLabels N Q).symm q).2.2.1.val =
      q.val % ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) %
        ((3 * (N + 2) + 1) * 3 ^ (N + 2)) / 3 ^ (N + 2) := by rfl

theorem bitSimLabels_buffer_nat (N Q : ℕ) (q : Fin (bitSimControlMax N Q + 1)) :
    (expandQueueLabels N (((bitSimLabels N Q).symm q).2.2.2)).val =
      q.val % ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) %
        ((3 * (N + 2) + 1) * 3 ^ (N + 2)) % 3 ^ (N + 2) := by
  exact congrArg Fin.val ((expandQueueLabels N).apply_symm_apply _)

theorem primrec_bitSimLabelNat_comp {α : Type*} [Primcodable α]
    {n Q phase wide i buffer : α → ℕ} (hn : Primrec n) (hQ : Primrec Q)
    (hp : Primrec phase) (hw : Primrec wide) (hi : Primrec i) (hb : Primrec buffer) :
    Primrec (fun x => bitSimLabelNat (n x) (Q x) (phase x) (wide x) (i x) (buffer x)) := by
  have hlen := Primrec.nat_add.comp hn (Primrec.const 2)
  have hpow := primrec_natPow.comp (Primrec.const 3) hlen
  have hstride := Primrec.nat_mul.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) hlen) (Primrec.const 1)) hpow
  exact Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_add.comp hb (Primrec.nat_mul.comp hpow hi)) (Primrec.nat_mul.comp hstride hw))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp hQ (Primrec.const 1)) hstride) hp)

theorem wideRecordStride_pos (N : ℕ) : 0 < wideRecordStride N := by
  have h : 0 < 3 ^ (N + 2) := pow_pos (by decide) _
  unfold wideRecordStride
  omega

theorem wideActionNat_lt (N : ℕ) (action : Turing.TM0.Stmt (TrackCell N)) :
    wideActionNat N action < wideRecordStride N := by
  have hp : 0 < 3 ^ (N + 2) := pow_pos (by decide) _
  cases action with
  | move dir => cases dir <;> simp only [wideActionNat, wideRecordStride] <;> omega
  | write v =>
    have h := (expandQueueLabels N (cellBuffer N v)).isLt
    simp only [wideActionNat, wideRecordStride]
    omega

theorem wideRecordNat_eq_zero_iff (N Q : ℕ)
    (record : Option (Fin (Q + 1) × Turing.TM0.Stmt (TrackCell N))) :
    wideRecordNat N record = 0 ↔ record = none := by
  cases record with
  | none => simp only [wideRecordNat]
  | some p => rcases p with ⟨q, action⟩; simp [wideRecordNat]

theorem wideRecordNat_source (N Q : ℕ) (q : Fin (Q + 1)) (action : Turing.TM0.Stmt (TrackCell N)) :
    (wideRecordNat N (some (q, action)) - 1) / wideRecordStride N = q.val := by
  simp only [wideRecordNat, Nat.add_sub_cancel]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (wideRecordStride_pos N),
    Nat.div_eq_of_lt (wideActionNat_lt N action), Nat.zero_add]

theorem wideRecordNat_action (N Q : ℕ) (q : Fin (Q + 1)) (action : Turing.TM0.Stmt (TrackCell N)) :
    (wideRecordNat N (some (q, action)) - 1) % wideRecordStride N = wideActionNat N action := by
  simp only [wideRecordNat, Nat.add_sub_cancel, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (wideActionNat_lt N action)]

theorem primrec_wideRecordStride : Primrec wideRecordStride := by
  exact Primrec.nat_add.comp (primrec_natPow.comp (Primrec.const 3)
    (Primrec.nat_add.comp Primrec.id (Primrec.const 2))) (Primrec.const 2)

theorem bitSimTable_ready_record_nat (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (coin : Bool) (q : Fin (Q + 1)) (i : Fin (3 * (N + 2) + 1))
    (buf : BitBuffer N) (s : Option Bool) :
    encodeTransition ((bitSimTable N M coin (2, q, i, buf) s).map
      (fun p => (bitSimLabels N Q p.1, p.2))) =
      bitSimStepNat N Q 2 q.val i.val (expandQueueLabels N buf).val (symbolIndex s)
        (wideRecordNat N (M coin q (bufferCell N buf))) := by
  simp only [bitSimTable]
  cases h : M coin q (bufferCell N buf) with
  | none => rfl
  | some p =>
    rcases p with ⟨next, action⟩
    have hn : wideRecordNat N (some (next, action)) ≠ 0 := by simp [wideRecordNat]
    have hq := wideRecordNat_source N Q next action
    have ha := wideRecordNat_action N Q next action
    dsimp only [bitSimStepNat]
    rw [if_neg hn, hq, ha]
    cases action with
    | move dir =>
      cases dir <;> simp [wideActionNat, encodeTransition, bitSimLabels_nat, actionIndex_write]
    | write v =>
      have hv1 : 2 + (expandQueueLabels N (cellBuffer N v)).val ≠ 1 := by omega
      simp [wideActionNat, hv1, encodeTransition, bitSimLabels_nat, actionIndex_write]

set_option maxHeartbeats 1600000 in

theorem bitSimTable_record_nat (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (coin : Bool) (q : BitSimState N (Fin (Q + 1))) (s : Option Bool) :
    encodeTransition ((bitSimTable N M coin q s).map (fun p => (bitSimLabels N Q p.1, p.2))) =
      bitSimStepNat N Q q.1.val q.2.1.val q.2.2.1.val
        (expandQueueLabels N q.2.2.2).val (symbolIndex s)
        (wideRecordNat N (M coin q.2.1 (bufferCell N q.2.2.2))) := by
  rcases q with ⟨phase, wide, i, buf⟩
  have hd (hi : i.val < N + 2) : queueDigitNat (expandQueueLabels N buf).val i.val =
      symbolIndex (buf ⟨i.val, hi⟩) := expandQueueLabels_digit_encode N buf ⟨i.val, hi⟩
  fin_cases phase
  all_goals first
    | exact bitSimTable_ready_record_nat N Q M coin wide i buf s
    | dsimp [bitSimTable, bitSimStepNat]
      all_goals try simp only [Option.map]
      all_goals try split_ifs
      all_goals
        try dsimp only [Option.map, encodeTransition]
        repeat' (first
          | rw [bitSimLabels_nat]
          | rw [expandQueueLabels_update]
          | rw [expandQueueLabels_zero]
          | rw [actionIndex_write])
      all_goals try dsimp [actionIndex]
      all_goals simp_all

theorem wideTableNat_actual (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (coin : Bool) (q : Fin (Q + 1)) (buf : BitBuffer N) :
    wideTableNat N Q M coin q.val (expandQueueLabels N buf).val =
      wideRecordNat N (M coin q (bufferCell N buf)) := by
  simp only [wideTableNat, Nat.mod_eq_of_lt q.isLt,
    Nat.mod_eq_of_lt (expandQueueLabels N buf).isLt]
  change wideRecordNat N
      (M coin q (bufferCell N ((expandQueueLabels N).symm (expandQueueLabels N buf)))) = _
  rw [Equiv.symm_apply_apply]

theorem nativeBitSimTable_row_nat (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (row : ℕ) :
    encodeTransition (nativeBitSimTable N Q M (decide (3 * (bitSimControlMax N Q + 1) ≤ row))
      ⟨row / 3 % (bitSimControlMax N Q + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (row % 3))) =
      bitSimRowNat N Q (wideTableNat N Q M) row := by
  let q : Fin (bitSimControlMax N Q + 1) :=
    ⟨row / 3 % (bitSimControlMax N Q + 1), Nat.mod_lt _ (by omega)⟩
  let coin := decide (3 * (bitSimControlMax N Q + 1) ≤ row)
  have hs : symbolIndex (decodeSymbol (row % 3)) = row % 3 :=
    congrArg Fin.val (optionBoolFin.apply_symm_apply ⟨row % 3, Nat.mod_lt _ (by omega)⟩)
  change encodeTransition ((bitSimTable N M coin ((bitSimLabels N Q).symm q)
    (decodeSymbol (row % 3))).map _) = _
  rw [bitSimTable_record_nat, ← wideTableNat_actual N Q M coin
    (((bitSimLabels N Q).symm q).2.1) (((bitSimLabels N Q).symm q).2.2.2)]
  rw [bitSimLabels_phase_nat, bitSimLabels_source_nat, bitSimLabels_index_nat,
      bitSimLabels_buffer_nat, hs]
  rfl

theorem bitSimCode_eq_codeEnumerate (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    bitSimCode N Q M a = codeEnumerate (bitSimControlMax N Q)
      (fun q => nativeBitSimAccept N Q a
        ⟨q % (bitSimControlMax N Q + 1), Nat.mod_lt _ (by omega)⟩)
      (bitSimRowNat N Q (wideTableNat N Q M)) := by
  rw [bitSimCode, encodeMachine_eq_codeEnumerate]
  congr 1
  funext row
  exact nativeBitSimTable_row_nat N Q M row

theorem primrec_bitSimStepNat_comp {α : Type*} [Primcodable α]
    {n Q phase wide i buffer symbol record : α → ℕ}
    (hn : Primrec n) (hQ : Primrec Q) (hp : Primrec phase) (hw : Primrec wide)
    (hi : Primrec i) (hb : Primrec buffer) (hs : Primrec symbol) (hr : Primrec record) :
    Primrec (fun x => bitSimStepNat (n x) (Q x) (phase x) (wide x) (i x) (buffer x) (symbol x) (record x)) := by
  have he {p w j b a : α → ℕ} (hP : Primrec p) (hW : Primrec w) (hI : Primrec j)
      (hB : Primrec b) (hA : Primrec a) :
      Primrec (fun x => 5 * bitSimLabelNat (n x) (Q x) (p x) (w x) (j x) (b x) + a x + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 5)
      (primrec_bitSimLabelNat_comp hn hQ hP hW hI hB)) hA) (Primrec.const 1)
  have hlen := Primrec.nat_add.comp hn (Primrec.const 2)
  have hmove := Primrec.nat_add.comp hn (Primrec.const 3)
  have hip1 := Primrec.nat_add.comp hi (Primrec.const 1)
  have him1 := Primrec.nat_sub.comp hi (Primrec.const 1)
  have hmore := Primrec.nat_lt.comp (Primrec.const 1) hi
  have hpos := Primrec.nat_lt.comp (Primrec.const 0) hi
  have hin := Primrec.nat_lt.comp hi hlen
  have hnext := Primrec.nat_lt.comp hip1 hlen
  have hpad := Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) hlen) (Primrec.const 1)
  have hstepIndex := Primrec.ite hmore him1 (Primrec.const 0)
  have hstepBuffer := Primrec.ite hmore hb (Primrec.const 0)
  have hwrite := Primrec.nat_add.comp (Primrec.const 2) hs
  have h0 := Primrec.ite hin
    (he (Primrec.ite hnext (Primrec.const 0) (Primrec.const 1)) hw
      (Primrec.ite hnext hip1 hlen) (primrec_queueUpdateNat.comp (hb.pair (hi.pair hs))) (Primrec.const 1))
    (Primrec.const 0)
  have h1 := Primrec.ite hpos
    (he (Primrec.ite hmore (Primrec.const 1) (Primrec.const 2)) hw hstepIndex hb (Primrec.const 0))
    (Primrec.const 0)
  have hstride := primrec_wideRecordStride.comp hn
  have hpayload := Primrec.nat_sub.comp hr (Primrec.const 1)
  have hsource := Primrec.nat_div.comp hpayload hstride
  have haction := Primrec.nat_mod.comp hpayload hstride
  have h2 := Primrec.ite (Primrec.eq.comp hr (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp haction (Primrec.const 0))
      (he (Primrec.const 3) hsource hmove hb hwrite)
      (Primrec.ite (Primrec.eq.comp haction (Primrec.const 1))
        (he (Primrec.const 4) hsource hmove hb hwrite)
        (he (Primrec.const 5) hsource (Primrec.const 0)
          (Primrec.nat_sub.comp haction (Primrec.const 2)) hwrite)))
  have h3 := Primrec.ite hpos
    (he (Primrec.ite hmore (Primrec.const 3) (Primrec.const 6)) hw
      (Primrec.ite hmore him1 hpad) hb (Primrec.const 0)) (Primrec.const 0)
  have h4 := Primrec.ite hpos
    (he (Primrec.ite hmore (Primrec.const 4) (Primrec.const 6)) hw
      (Primrec.ite hmore him1 hpad) hb (Primrec.const 1)) (Primrec.const 0)
  have h5 := Primrec.ite hin
    (he (Primrec.const 7) hw hi hb
      (Primrec.nat_add.comp (Primrec.const 2) (primrec_queueDigitNat.comp hb hi))) (Primrec.const 0)
  have h6 := Primrec.ite hpos
    (he (Primrec.ite hmore (Primrec.const 6) (Primrec.const 0)) hw hstepIndex hstepBuffer hwrite) (Primrec.const 0)
  have h7 := Primrec.ite hnext
    (he (Primrec.const 5) hw hip1 hb (Primrec.const 1)) (he (Primrec.const 8) hw hlen hb (Primrec.const 1))
  have h8 := Primrec.ite hpos
    (he (Primrec.ite hmore (Primrec.const 8) (Primrec.const 0)) hw hstepIndex hstepBuffer (Primrec.const 0))
    (Primrec.const 0)
  unfold bitSimStepNat
  exact Primrec.ite (Primrec.eq.comp hp (Primrec.const 0)) h0
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 1)) h1
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 2)) h2
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 3)) h3
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 4)) h4
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 5)) h5
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 6)) h6
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 7)) h7
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 8)) h8 (Primrec.const 0)))))))))

theorem primrec_bitSimRowNat_comp {α : Type*} [Primcodable α]
    {n Q row : α → ℕ} {source : α → Bool → ℕ → ℕ → ℕ}
    (hn : Primrec n) (hQ : Primrec Q) (hr : Primrec row)
    (hsource : Primrec (fun p : α × Bool × ℕ × ℕ => source p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun x => bitSimRowNat (n x) (Q x) (source x) (row x)) := by
  have hsize := Primrec.nat_add.comp (primrec_bitSimControlMax.comp hn hQ) (Primrec.const 1)
  have hlabel := Primrec.nat_mod.comp (Primrec.nat_div.comp hr (Primrec.const 3)) hsize
  have hpow := primrec_natPow.comp (Primrec.const 3) (Primrec.nat_add.comp hn (Primrec.const 2))
  have hstride := Primrec.nat_mul.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3)
      (Primrec.nat_add.comp hn (Primrec.const 2))) (Primrec.const 1)) hpow
  have hfull := Primrec.nat_mul.comp (Primrec.nat_add.comp hQ (Primrec.const 1)) hstride
  have hrest := Primrec.nat_mod.comp hlabel hfull
  have hwide := Primrec.nat_div.comp hrest hstride
  have hinner := Primrec.nat_mod.comp hrest hstride
  have hbuffer := Primrec.nat_mod.comp hinner hpow
  have hcoin := (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.const 3) hsize) hr).decide
  have hrecord := hsource.comp (Primrec.id.pair (hcoin.pair (hwide.pair hbuffer)))
  exact primrec_bitSimStepNat_comp hn hQ (Primrec.nat_div.comp hlabel hfull) hwide
    (Primrec.nat_div.comp hinner hpow) hbuffer (Primrec.nat_mod.comp hr (Primrec.const 3)) hrecord

theorem wideTableNat_canonical (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (coin : Bool) (wide : ℕ) (buffer : Fin (3 ^ (N + 2))) :
    wideTableNat N Q M coin wide (canonicalBufferNat N buffer.val) =
      wideTableNat N Q M coin wide buffer.val := by
  simp only [wideTableNat, Nat.mod_eq_of_lt (canonicalBufferNat_lt N buffer),
      Nat.mod_eq_of_lt buffer.isLt]
  change wideRecordNat N (M coin _ (bufferCell N ((expandQueueLabels N).symm
    ⟨canonicalBufferNat N buffer.val, canonicalBufferNat_lt N buffer⟩))) =
    wideRecordNat N (M coin _ (bufferCell N ((expandQueueLabels N).symm buffer)))
  rw [bufferCell_canonicalBufferNat]

theorem wideTableNat_write_back (N Q : ℕ) (coin : Bool) (wide buffer : ℕ) :
    wideTableNat N Q (fun _ q cell => some (q, .write cell)) coin wide buffer =
      wideRecordStride N * (wide % (Q + 1)) +
        (2 + canonicalBufferNat N (buffer % 3 ^ (N + 2))) + 1 := by
  simp only [wideTableNat, wideRecordNat, wideActionNat, cellBuffer_bufferCell_nat]
  rw [Equiv.apply_symm_apply]

theorem primrec_wideTableNat_write_back_comp {α : Type*} [Primcodable α]
    {n Q wide buffer : α → ℕ} {coin : α → Bool}
    (hn : Primrec n) (hQ : Primrec Q) (hw : Primrec wide) (hb : Primrec buffer) :
    Primrec (fun x => wideTableNat (n x) (Q x) (fun _ q cell => some (q, .write cell))
      (coin x) (wide x) (buffer x)) := by
  have hstride := primrec_wideRecordStride.comp hn
  have hlabel := Primrec.nat_mod.comp hw (Primrec.nat_add.comp hQ (Primrec.const 1))
  have hpow := primrec_natPow.comp (Primrec.const 3) (Primrec.nat_add.comp hn (Primrec.const 2))
  have hbuf := primrec_canonicalBufferNat.comp hn (Primrec.nat_mod.comp hb hpow)
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hstride hlabel)
    (Primrec.nat_add.comp (Primrec.const 2) hbuf)) (Primrec.const 1)).of_eq
      (fun x => (wideTableNat_write_back (n x) (Q x) (coin x) (wide x) (buffer x)).symm)

theorem cellBuffer_writeTrack (N : ℕ) (j : Fin N) (s : TrackCell N) (b : MarkerCell) :
    cellBuffer N (writeTrack j s b) =
      Function.update (Function.update (Function.update (cellBuffer N s) 0 b.1)
        j.castSucc.succ b.2.1) (Fin.last (N + 1)) (if b.2.2 then some true else none) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · have hz : (0 : Fin (N + 2)) ≠ j.castSucc.succ := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc] at hv
      omega
    simp [cellBuffer, writeTrack, Function.update_of_ne hz]
  · refine Fin.lastCases ?_ (fun k => ?_) k
    · have hj : Fin.last N ≠ j.castSucc := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      simp [cellBuffer, writeTrack, Function.update_of_ne hj]
    · simp [cellBuffer, writeTrack, Function.update_apply]

theorem cellBuffer_writeTrack_nat (N : ℕ) (j : Fin N) (s : TrackCell N) (b : MarkerCell) :
    (expandQueueLabels N (cellBuffer N (writeTrack j s b))).val =
      trackWriteBufferNat N j.val (expandQueueLabels N (cellBuffer N s)).val
        (symbolIndex b.1) (symbolIndex b.2.1) (if b.2.2 then 2 else 0) := by
  rw [cellBuffer_writeTrack, expandQueueLabels_update, expandQueueLabels_update,
      expandQueueLabels_update]
  unfold trackWriteBufferNat
  cases b.2.2 <;> rfl

theorem cellBuffer_input_digit (N : ℕ) (s : TrackCell N) :
    queueDigitNat (expandQueueLabels N (cellBuffer N s)).val 0 = symbolIndex s.1 := by
  simpa only [cellBuffer, Fin.cons_zero] using!
    expandQueueLabels_digit_encode N (cellBuffer N s) (0 : Fin (N + 2))

theorem cellBuffer_work_digit (N : ℕ) (s : TrackCell N) (j : Fin N) :
    queueDigitNat (expandQueueLabels N (cellBuffer N s)).val (j.val + 1) = symbolIndex (s.2.1 j) := by
  simpa only [cellBuffer, Fin.val_succ, Fin.val_castSucc, Fin.cons_succ, Fin.snoc_castSucc] using!
    expandQueueLabels_digit_encode N (cellBuffer N s) j.castSucc.succ

theorem cellBuffer_home_digit (N : ℕ) (s : TrackCell N) :
    queueDigitNat (expandQueueLabels N (cellBuffer N s)).val (N + 1) = if s.2.2 then 2 else 0 := by
  have h := expandQueueLabels_digit_encode N (cellBuffer N s) (Fin.last (N + 1))
  cases hb : s.2.2 <;> simpa [cellBuffer, hb, symbolIndex] using! h

theorem roundsLabels_nat (N Q : ℕ) (q : RoundsState N Q) :
    (roundsLabels N Q q).val = roundsLabelNat N Q q.1.val q.2.1.val q.2.2.val := by rfl

theorem roundsLabels_round_nat (N Q : ℕ) (q : Fin (roundsControlMax N Q + 1)) :
    ((roundsLabels N Q).symm q).1.val = q.val / ((N + 1) * (2 * Q + 11)) := by rfl

theorem roundsLabels_prog_nat (N Q : ℕ) (q : Fin (roundsControlMax N Q + 1)) :
    ((roundsLabels N Q).symm q).2.2.val = q.val % ((N + 1) * (2 * Q + 11)) % (2 * Q + 11) := by rfl

theorem writeTrack_focusTrack (N : ℕ) (j : Fin N) (s : TrackCell N) : writeTrack j s (focusTrack j s) = s := by
  rcases s with ⟨input, work, home⟩
  simp [writeTrack, focusTrack]

theorem trackWriteBufferNat_same (N : ℕ) (j : Fin N) (s : TrackCell N) :
    trackWriteBufferNat N j.val (expandQueueLabels N (cellBuffer N s)).val
      (symbolIndex s.1) (symbolIndex (s.2.1 j)) (if s.2.2 then 2 else 0) =
        (expandQueueLabels N (cellBuffer N s)).val := by
  have h := cellBuffer_writeTrack_nat N j s (focusTrack j s)
  rw [writeTrack_focusTrack] at h
  exact h.symm

theorem prepareHomingLabels_inl_val (Q : ℕ) (q : Fin 5) :
    (prepareHomingLabels Q (.inl q)).val = q.val := by rfl

theorem prepareHomingLabels_inr_val (Q : ℕ) (q : Fin (2 * Q + 6)) :
    (prepareHomingLabels Q (.inr q)).val = 5 + q.val := by rfl

theorem homingLabels_inl_val (Q : ℕ) (q : Fin (Q + 1)) (side : Bool) :
    (homingLabels Q (.inl (q, side))).val = side.toNat + 2 * q.val := by cases side <;> rfl

theorem homingLabels_inr_val (Q : ℕ) (side output : Bool) :
    (homingLabels Q (.inr (side, output))).val = 2 * (Q + 1) + (output.toNat + 2 * side.toNat) := by
  have h : (homingLabels Q (.inr (side, output))).val =
      (Q + 1) * 2 + (output.toNat + 2 * side.toNat) := by
    cases side <;> cases output <;> rfl
  rw [h]
  omega

set_option maxHeartbeats 1200000 in

theorem trackRoundTable_copy_record_nat (N : ℕ) (j : Fin N) (code : Code) (coin : Bool)
    (q : Fin 5) (s : TrackCell N) :
    wideRecordNat N (trackRoundTable j (controlSize code) (table code) (readout code) coin
      (prepareHomingLabels (controlSize code) (.inl q)) s) =
      trackRoundRowNat N j.val code coin q.val (expandQueueLabels N (cellBuffer N s)).val := by
  simp only [trackRoundTable, trackTable, prepareHomingCoinTable, relabelTable]
  rw [Equiv.symm_apply_apply]
  simp only [sequenceCoinTable, sequenceTable]
  unfold trackRoundRowNat
  simp only [canonicalBufferNat_cellBuffer, cellBuffer_input_digit, cellBuffer_work_digit,
      cellBuffer_home_digit]
  have hsame := trackWriteBufferNat_same N j s
  fin_cases q <;> cases hb : s.2.2 <;> cases hi : s.1 with
  | none =>
    dsimp [markerCopyTable, fillCell, focusTrack]
    all_goals try simp only [Option.isSome, Option.map]
    all_goals try split_ifs
    all_goals try dsimp [wideRecordNat, wideActionNat]
    all_goals
      repeat' (first
        | rw [prepareHomingLabels_inl_val]
        | rw [prepareHomingLabels_inr_val]
        | rw [cellBuffer_writeTrack_nat]
        | rw [writeTrack_focusTrack]
        | rw [Fin.default_eq_zero])
    all_goals simp_all [symbolIndex]
  | some b =>
    cases b <;> dsimp [markerCopyTable, fillCell, focusTrack]
    all_goals try simp only [Option.isSome, Option.map]
    all_goals try split_ifs
    all_goals try dsimp [wideRecordNat, wideActionNat]
    all_goals
      repeat' (first
        | rw [prepareHomingLabels_inl_val]
        | rw [prepareHomingLabels_inr_val]
        | rw [cellBuffer_writeTrack_nat]
        | rw [writeTrack_focusTrack]
        | rw [Fin.default_eq_zero])
    all_goals simp_all [symbolIndex]

set_option maxHeartbeats 1200000 in

theorem trackRoundTable_home_record_nat (N : ℕ) (j : Fin N) (code : Code) (coin : Bool)
    (side output : Bool) (s : TrackCell N) :
    wideRecordNat N (trackRoundTable j (controlSize code) (table code) (readout code) coin
      (prepareHomingLabels (controlSize code) (.inr (homingLabels (controlSize code) (.inr (side, output))))) s) =
      trackRoundRowNat N j.val code coin
        (5 + (2 * (controlSize code + 1) + (output.toNat + 2 * side.toNat)))
        (expandQueueLabels N (cellBuffer N s)).val := by
  simp only [trackRoundTable, trackTable, prepareHomingCoinTable, relabelTable]
  rw [Equiv.symm_apply_apply]
  simp only [sequenceCoinTable, sequenceTable, nativeHomingCoinTable, relabelTable]
  rw [Equiv.symm_apply_apply]
  simp only [homingCoinTable, dispatchCoinTable, dispatchTable]
  unfold trackRoundRowNat
  simp only [canonicalBufferNat_cellBuffer, cellBuffer_input_digit, cellBuffer_work_digit,
      cellBuffer_home_digit]
  cases side <;> cases output <;> cases hb : s.2.2
  all_goals dsimp [markerHomeTable, homeDirection, focusTrack]
  all_goals simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.map_none, wideRecordNat]
  all_goals
    try dsimp [wideRecordNat, wideActionNat]
    repeat' (first | rw [prepareHomingLabels_inr_val] | rw [homingLabels_inr_val])
  all_goals simp_all
  all_goals split_ifs <;> omega

theorem sourceRowNat_actual (code : Code) (coin : Bool)
    (q : Fin (controlSize code + 1)) (s : Option Bool) :
    sourceRowNat code coin q.val (symbolIndex s) = encodeTransition (table code coin q s) := by
  simpa only [Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt (symbolIndex_lt s), decodeSymbol_symbolIndex] using!
    (sourceRowNat_table code coin q.val (symbolIndex s)).symm

theorem encodeTransition_source {Q : ℕ} (q : Fin (Q + 1)) (action : Turing.TM0.Stmt (Option Bool)) :
    (encodeTransition (some (q, action)) - 1) / 5 = q.val := by
  have h := actionIndex_lt action
  simp only [encodeTransition, Nat.add_sub_cancel]
  omega

theorem encodeTransition_action {Q : ℕ} (q : Fin (Q + 1)) (action : Turing.TM0.Stmt (Option Bool)) :
    (encodeTransition (some (q, action)) - 1) % 5 = actionIndex action := by
  have h := actionIndex_lt action
  simp only [encodeTransition, Nat.add_sub_cancel]
  omega

set_option maxHeartbeats 2000000 in

theorem trackRoundTable_source_record_nat (N : ℕ) (j : Fin N) (code : Code) (coin : Bool)
    (q : Fin (controlSize code + 1)) (side : Bool) (s : TrackCell N) :
    wideRecordNat N (trackRoundTable j (controlSize code) (table code) (readout code) coin
      (prepareHomingLabels (controlSize code) (.inr (homingLabels (controlSize code) (.inl (q, side))))) s) =
      trackRoundRowNat N j.val code coin (5 + (side.toNat + 2 * q.val))
        (expandQueueLabels N (cellBuffer N s)).val := by
  have hbound : side.toNat + 2 * q.val < 2 * (controlSize code + 1) := by
    cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> have := q.isLt <;> omega
  have hdiv : (side.toNat + 2 * q.val) / 2 = q.val := by
    cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hmod : (side.toNat + 2 * q.val) % 2 = side.toNat := by
    cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hsame := trackWriteBufferNat_same N j s
  have hr := sourceRowNat_actual code coin q (s.2.1 j)
  simp only [trackRoundTable, trackTable, prepareHomingCoinTable, relabelTable]
  rw [Equiv.symm_apply_apply]
  simp only [sequenceCoinTable, sequenceTable, nativeHomingCoinTable, relabelTable]
  rw [Equiv.symm_apply_apply]
  simp only [homingCoinTable, dispatchCoinTable, dispatchTable, sideWorkTable, focusTrack]
  unfold trackRoundRowNat
  simp only [canonicalBufferNat_cellBuffer, cellBuffer_input_digit, cellBuffer_work_digit, cellBuffer_home_digit,
    Nat.add_sub_cancel_left, hdiv, hmod]
  cases h : table code coin q (s.2.1 j) with
  | none =>
    rw [h] at hr
    simp only [encodeTransition] at hr
    cases side <;> cases hb : s.2.2
    all_goals try dsimp [wideRecordNat, wideActionNat]
    all_goals
      repeat' (first
        | rw [prepareHomingLabels_inr_val]
        | rw [homingLabels_inr_val]
        | rw [cellBuffer_writeTrack_nat]
        | rw [writeTrack_focusTrack])
    all_goals simp_all [readout]
    all_goals split_ifs <;> omega
  | some p =>
    rcases p with ⟨next, action⟩
    rw [h] at hr
    have hn : encodeTransition (some (next, action)) ≠ 0 := by simp [encodeTransition]
    have hq := encodeTransition_source next action
    have ha := encodeTransition_action next action
    cases action with
    | move dir =>
      cases dir <;> cases side <;> cases hb : s.2.2
      all_goals dsimp [sideAfterMove, wideRecordNat, wideActionNat]
      all_goals
        repeat' (first
          | rw [prepareHomingLabels_inr_val]
          | rw [homingLabels_inl_val])
      all_goals simp_all [actionIndex]
      all_goals split_ifs <;> omega
    | write b =>
      cases side <;> cases hb : s.2.2
      all_goals try dsimp [wideRecordNat, wideActionNat]
      all_goals
        repeat' (first
          | rw [prepareHomingLabels_inr_val]
          | rw [homingLabels_inl_val]
          | rw [cellBuffer_writeTrack_nat])
      all_goals simp_all [actionIndex_write]
      all_goals split_ifs <;> omega

theorem canonicalBufferNat_idempotent_nat (N buffer : ℕ) (hb : buffer < 3 ^ (N + 2)) :
    canonicalBufferNat N (canonicalBufferNat N buffer) = canonicalBufferNat N buffer := by
  have h := canonicalBufferNat_idempotent N ((expandQueueLabels N).symm ⟨buffer, hb⟩)
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem trackRoundRowNat_canonical (N j : ℕ) (code : Code) (coin : Bool) (prog buffer : ℕ)
    (hb : buffer < 3 ^ (N + 2)) :
    trackRoundRowNat N j code coin prog (canonicalBufferNat N buffer) =
      trackRoundRowNat N j code coin prog buffer := by
  unfold trackRoundRowNat
  rw [canonicalBufferNat_idempotent_nat N buffer hb]

theorem roundsStepNat_canonical (N : ℕ) (code : Code) (coin : Bool) (round count prog buffer : ℕ)
    (hb : buffer < 3 ^ (N + 2)) :
    roundsStepNat N code coin round count prog (canonicalBufferNat N buffer) =
      roundsStepNat N code coin round count prog buffer := by
  unfold roundsStepNat
  rw [trackRoundRowNat_canonical N round code coin prog buffer hb,
    canonicalBufferNat_idempotent_nat N buffer hb]

theorem trackRoundTable_record_nat (N : ℕ) (j : Fin N) (code : Code) (coin : Bool)
    (q : Fin (2 * controlSize code + 11)) (s : TrackCell N) :
    wideRecordNat N (trackRoundTable j (controlSize code) (table code) (readout code) coin q s) =
      trackRoundRowNat N j.val code coin q.val (expandQueueLabels N (cellBuffer N s)).val := by
  generalize he : (prepareHomingLabels (controlSize code)).symm q = z
  have hq : prepareHomingLabels (controlSize code) z = q := by
    rw [← he]
    exact (prepareHomingLabels (controlSize code)).apply_symm_apply q
  rw [← hq]
  cases z with
  | inl copy =>
    rw [prepareHomingLabels_inl_val]
    exact trackRoundTable_copy_record_nat N j code coin copy s
  | inr h =>
    generalize hh : (homingLabels (controlSize code)).symm h = z
    have hz : homingLabels (controlSize code) z = h := by
      rw [← hh]
      exact (homingLabels (controlSize code)).apply_symm_apply h
    rw [← hz]
    cases z with
    | inl source =>
      rcases source with ⟨q, side⟩
      rw [prepareHomingLabels_inr_val, homingLabels_inl_val]
      exact trackRoundTable_source_record_nat N j code coin q side s
    | inr home =>
      rcases home with ⟨side, output⟩
      rw [prepareHomingLabels_inr_val, homingLabels_inr_val]
      exact trackRoundTable_home_record_nat N j code coin side output s

theorem prepareHomingAccept_nat (Q : ℕ) (q : Fin (2 * Q + 11)) :
    prepareHomingAccept Q q = prepareHomingOutputNat Q q.val := by
  generalize he : (prepareHomingLabels Q).symm q = z
  have hq : prepareHomingLabels Q z = q := by
    rw [← he]
    exact (prepareHomingLabels Q).apply_symm_apply q
  rw [← hq]
  cases z with
  | inl copy =>
    have hn : ¬ 5 + 2 * (Q + 1) ≤ copy.val := by have := copy.isLt; omega
    simp only [prepareHomingAccept, Equiv.symm_apply_apply, sourcePhaseAccept,
      prepareHomingLabels_inl_val, prepareHomingOutputNat, hn, decide_false, Bool.false_and]
  | inr h =>
    generalize hh : (homingLabels Q).symm h = z
    have hz : homingLabels Q z = h := by
      rw [← hh]
      exact (homingLabels Q).apply_symm_apply h
    rw [← hz]
    cases z with
    | inl source =>
      rcases source with ⟨q, side⟩
      have hn : ¬ 5 + 2 * (Q + 1) ≤ 5 + (side.toNat + 2 * q.val) := by
        cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> have := q.isLt <;> omega
      simp only [prepareHomingAccept, Equiv.symm_apply_apply, sourcePhaseAccept, nativeHomingAccept, homingAccept,
        prepareHomingLabels_inr_val, homingLabels_inl_val, prepareHomingOutputNat, hn, decide_false, Bool.false_and]
    | inr home =>
      rcases home with ⟨side, output⟩
      have hp : 5 + 2 * (Q + 1) ≤ 5 + (2 * (Q + 1) + (output.toNat + 2 * side.toNat)) := by omega
      have hs : 5 + (2 * (Q + 1) + (output.toNat + 2 * side.toNat)) - (5 + 2 * (Q + 1)) =
          output.toNat + 2 * side.toNat := by omega
      simp only [prepareHomingAccept, Equiv.symm_apply_apply, sourcePhaseAccept, nativeHomingAccept, homingAccept,
        prepareHomingLabels_inr_val, homingLabels_inr_val, prepareHomingOutputNat, hp, decide_true, Bool.true_and, hs]
      cases side <;> cases output <;> rfl

theorem roundsTable_record_nat (N : ℕ) (code : Code) (coin : Bool)
    (q : RoundsState N (controlSize code)) (s : TrackCell N) :
    wideRecordNat N ((roundsTable N (controlSize code) (table code) (readout code) coin q s).map
      (fun p => (roundsLabels N (controlSize code) p.1, p.2))) =
      roundsStepNat N code coin q.1.val q.2.1.val q.2.2.val (expandQueueLabels N (cellBuffer N s)).val := by
  rcases q with ⟨round, count, prog⟩
  by_cases hj : round.val < N
  · have hr := trackRoundTable_record_nat N ⟨round.val, hj⟩ code coin prog s
    simp only [roundsTable, hj, ↓reduceDIte, roundsStepNat, ↓reduceIte]
    cases h : trackRoundTable ⟨round.val,
        hj⟩ (controlSize code) (table code) (readout code) coin prog s with
    | none =>
      rw [h] at hr
      simp only [wideRecordNat] at hr
      rw [← hr]
      simp only [ite_true, Option.map_some, wideRecordNat, wideActionNat, roundsLabels_nat,
        roundsNext, boundedSucc, prepareHomingAccept_nat, canonicalBufferNat_cellBuffer]
      split_ifs <;> rfl
    | some p =>
      rcases p with ⟨next, action⟩
      rw [h] at hr
      rw [← hr]
      have hn : wideRecordNat N (some (next, action)) ≠ 0 := by simp [wideRecordNat]
      rw [if_neg hn, wideRecordNat_source, wideRecordNat_action]
      simp only [Option.map_some, wideRecordNat, roundsLabels_nat]
  · simp only [roundsTable, hj, ↓reduceDIte, Option.map_none, wideRecordNat, roundsStepNat,
      ↓reduceIte]

theorem nativeRoundsTable_row_nat (N : ℕ) (code : Code) (coin : Bool) (wide buffer : ℕ) :
    wideTableNat N (roundsControlMax N (controlSize code))
      (nativeRoundsTable N (controlSize code) (table code) (readout code)) coin wide buffer =
      roundsRowNat N code coin wide buffer := by
  unfold wideTableNat
  change wideRecordNat N ((roundsTable N (controlSize code) (table code) (readout code) coin
    ((roundsLabels N (controlSize code)).symm _) (bufferCell N ((expandQueueLabels N).symm _))).map _) = _
  rw [roundsTable_record_nat, roundsLabels_round_nat, roundsLabels_count_nat, roundsLabels_prog_nat,
    cellBuffer_bufferCell_nat, Equiv.apply_symm_apply]
  unfold roundsRowNat
  apply roundsStepNat_canonical
  exact Nat.mod_lt _ (pow_pos (by decide) _)

theorem primrec_trackWriteBufferNat_comp {α : Type*} [Primcodable α]
    {n j buffer input work home : α → ℕ}
    (hn : Primrec n) (hj : Primrec j) (hb : Primrec buffer) (hi : Primrec input)
    (hw : Primrec work) (hh : Primrec home) :
    Primrec (fun x => trackWriteBufferNat (n x) (j x) (buffer x) (input x) (work x) (home x)) := by
  have hin := primrec_queueUpdateNat.comp (hb.pair ((Primrec.const 0).pair hi))
  have hwork :=
      primrec_queueUpdateNat.comp (hin.pair ((Primrec.nat_add.comp hj (Primrec.const 1)).pair hw))
  exact primrec_queueUpdateNat.comp
      (hwork.pair ((Primrec.nat_add.comp hn (Primrec.const 1)).pair hh))

theorem primrec_roundsLabelNat_comp {α : Type*} [Primcodable α]
    {n Q round count prog : α → ℕ}
    (hn : Primrec n) (hQ : Primrec Q) (hr : Primrec round) (hc : Primrec count) (hp : Primrec prog) :
    Primrec (fun x => roundsLabelNat (n x) (Q x) (round x) (count x) (prog x)) := by
  have hsize := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hQ) (Primrec.const 11)
  exact Primrec.nat_add.comp (Primrec.nat_add.comp hp (Primrec.nat_mul.comp hsize hc))
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp hn (Primrec.const 1)) hsize) hr)

theorem primrec_trackRoundRowNat_comp {α : Type*} [Primcodable α]
    {n j prog buffer : α → ℕ} {code : α → Code} {coin : α → Bool}
    (hn : Primrec n) (hj : Primrec j) (hc : Primrec code) (hb : Primrec coin)
    (hp : Primrec prog) (hbuf : Primrec buffer) :
    Primrec (fun x => trackRoundRowNat (n x) (j x) (code x) (coin x) (prog x) (buffer x)) := by
  have hQ := primrec_controlSize.comp hc
  have hbuffer := primrec_canonicalBufferNat.comp hn hbuf
  have hinput := primrec_queueDigitNat.comp hbuffer (Primrec.const 0)
  have hwork := primrec_queueDigitNat.comp hbuffer (Primrec.nat_add.comp hj (Primrec.const 1))
  have hhome := primrec_queueDigitNat.comp hbuffer (Primrec.nat_add.comp hn (Primrec.const 1))
  have hstride := primrec_wideRecordStride.comp hn
  have he {target action : α → ℕ} (ht : Primrec target) (ha : Primrec action) :
      Primrec (fun x => wideRecordStride (n x) * target x + action x + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hstride ht) ha) (Primrec.const 1)
  have hw {input work home : α → ℕ} (hi : Primrec input) (hW : Primrec work) (hh : Primrec home) :
      Primrec (fun x => 2 + trackWriteBufferNat (n x) (j x) (canonicalBufferNat (n x) (buffer x))
        (input x) (work x) (home x)) :=
    Primrec.nat_add.comp (Primrec.const 2) (primrec_trackWriteBufferNat_comp hn hj hbuffer hi hW hh)
  have hsame := Primrec.nat_add.comp (Primrec.const 2) hbuffer
  have hishome := Primrec.eq.comp hhome (Primrec.const 2)
  have h0 := he (Primrec.const 1) (hw hinput hwork (Primrec.const 2))
  have h1 := Primrec.ite (Primrec.eq.comp hinput (Primrec.const 0))
    (he (Primrec.const 3) hsame) (he (Primrec.const 2) (hw hinput hinput hhome))
  have h2 := he (Primrec.const 1) (Primrec.const 1)
  have h3 :=
      Primrec.ite hishome (he (Primrec.const 4) hsame) (he (Primrec.const 3) (Primrec.const 0))
  have h4 := he (Primrec.const 5) hsame
  have hH := Primrec.nat_sub.comp hp (Primrec.const 5)
  have hbase := Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hQ (Primrec.const 1))
  have hsource := Primrec.nat_div.comp hH (Primrec.const 2)
  have hside := Primrec.nat_mod.comp hH (Primrec.const 2)
  have hrecord := primrec_sourceRowNat_comp hc hb hsource hwork
  have houtput := (Primrec.dom_bool Bool.toNat).comp (primrec_readoutNat.comp hc hsource)
  have hlatched := Primrec.nat_add.comp (Primrec.const 5)
    (Primrec.nat_add.comp hbase (Primrec.nat_add.comp houtput (Primrec.nat_mul.comp (Primrec.const 2) hside)))
  have hpayload := Primrec.nat_sub.comp hrecord (Primrec.const 1)
  have hnext := Primrec.nat_div.comp hpayload (Primrec.const 5)
  have haction := Primrec.nat_mod.comp hpayload (Primrec.const 5)
  have ht {side : α → ℕ} (hs : Primrec side) :
      Primrec (fun x => 5 + (side x + 2 * ((sourceRowNat (code x) (coin x)
        ((prog x - 5) / 2) (queueDigitNat (canonicalBufferNat (n x) (buffer x)) (j x + 1)) - 1) / 5))) :=
    Primrec.nat_add.comp (Primrec.const 5) (Primrec.nat_add.comp hs (Primrec.nat_mul.comp (Primrec.const 2) hnext))
  have hleft := he (ht (Primrec.ite hishome (Primrec.const 1) hside)) (Primrec.const 0)
  have hright := he (ht (Primrec.ite hishome (Primrec.const 0) hside)) (Primrec.const 1)
  have hwrite := he (ht hside) (hw hinput (Primrec.nat_sub.comp haction (Primrec.const 2)) hhome)
  have hsourceStep := Primrec.ite (Primrec.eq.comp hrecord (Primrec.const 0)) (he hlatched hsame)
    (Primrec.ite (Primrec.eq.comp haction (Primrec.const 0)) hleft
      (Primrec.ite (Primrec.eq.comp haction (Primrec.const 1)) hright hwrite))
  have hhomeStep := Primrec.ite hishome (Primrec.const 0)
    (he hp (Primrec.ite (Primrec.eq.comp (Primrec.nat_div.comp (Primrec.nat_sub.comp hH hbase)
      (Primrec.const 2)) (Primrec.const 1)) (Primrec.const 1) (Primrec.const 0)))
  unfold trackRoundRowNat
  exact Primrec.ite (Primrec.eq.comp hp (Primrec.const 0)) h0
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 1)) h1
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 2)) h2
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 3)) h3
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const 4)) h4
      (Primrec.ite (Primrec.nat_lt.comp hH hbase) hsourceStep hhomeStep)))))

theorem primrec_prepareHomingOutputNat_comp {α : Type*} [Primcodable α]
    {Q prog : α → ℕ} (hQ : Primrec Q) (hp : Primrec prog) :
    Primrec (fun x => prepareHomingOutputNat (Q x) (prog x)) := by
  have hbase := Primrec.nat_add.comp (Primrec.const 5)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp hQ (Primrec.const 1)))
  exact Primrec.and.comp (Primrec.nat_le.comp hbase hp).decide
    (Primrec.beq.comp (Primrec.nat_mod.comp (Primrec.nat_sub.comp hp hbase) (Primrec.const 2)) (Primrec.const 1))

theorem primrec_roundsStepNat_comp {α : Type*} [Primcodable α]
    {n round count prog buffer : α → ℕ} {code : α → Code} {coin : α → Bool}
    (hn : Primrec n) (hc : Primrec code) (hb : Primrec coin)
    (hr : Primrec round) (hcount : Primrec count) (hp : Primrec prog) (hbuf : Primrec buffer) :
    Primrec (fun x => roundsStepNat (n x) (code x) (coin x) (round x) (count x) (prog x) (buffer x)) := by
  have hQ := primrec_controlSize.comp hc
  have hstride := primrec_wideRecordStride.comp hn
  have he {target action : α → ℕ} (ht : Primrec target) (ha : Primrec action) :
      Primrec (fun x => wideRecordStride (n x) * target x + action x + 1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hstride ht) ha) (Primrec.const 1)
  have hrecord := primrec_trackRoundRowNat_comp hn hr hc hb hp hbuf
  have hnext := Primrec.nat_min.comp (Primrec.nat_add.comp hr (Primrec.const 1)) hn
  have hnextCount := Primrec.ite (Primrec.eq.comp (primrec_prepareHomingOutputNat_comp hQ hp) (Primrec.const true))
    (Primrec.nat_min.comp (Primrec.nat_add.comp hcount (Primrec.const 1)) hn) hcount
  have hdispatch := he (primrec_roundsLabelNat_comp hn hQ hnext hnextCount (Primrec.const 0))
    (Primrec.nat_add.comp (Primrec.const 2) (primrec_canonicalBufferNat.comp hn hbuf))
  have hpayload := Primrec.nat_sub.comp hrecord (Primrec.const 1)
  have hlive := he (primrec_roundsLabelNat_comp hn hQ hr hcount (Primrec.nat_div.comp hpayload hstride))
    (Primrec.nat_mod.comp hpayload hstride)
  exact Primrec.ite (Primrec.nat_lt.comp hr hn)
    (Primrec.ite (Primrec.eq.comp hrecord (Primrec.const 0)) hdispatch hlive) (Primrec.const 0)

theorem primrec_roundsRowNat_comp {α : Type*} [Primcodable α]
    {n wide buffer : α → ℕ} {code : α → Code} {coin : α → Bool}
    (hn : Primrec n) (hc : Primrec code) (hb : Primrec coin) (hw : Primrec wide) (hbuf : Primrec buffer) :
    Primrec (fun x => roundsRowNat (n x) (code x) (coin x) (wide x) (buffer x)) := by
  have hQ := primrec_controlSize.comp hc
  have hlabel := Primrec.nat_mod.comp hw
    (Primrec.nat_add.comp (primrec_roundsControlMax.comp hn hQ) (Primrec.const 1))
  have hsize := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hQ) (Primrec.const 11)
  have hblock := Primrec.nat_mul.comp (Primrec.nat_add.comp hn (Primrec.const 1)) hsize
  have hrest := Primrec.nat_mod.comp hlabel hblock
  have hbuffer := Primrec.nat_mod.comp hbuf
    (primrec_natPow.comp (Primrec.const 3) (Primrec.nat_add.comp hn (Primrec.const 2)))
  exact primrec_roundsStepNat_comp hn hc hb (Primrec.nat_div.comp hlabel hblock)
    (Primrec.nat_div.comp hrest hsize) (Primrec.nat_mod.comp hrest hsize) hbuffer

theorem encodedMajorityCode_eq_codeEnumerate (code : Code) (r : ℕ) :
    encodedMajorityCode code r = codeEnumerate
      (bitSimControlMax (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code)))
      (encodedMajorityOutputNat code r) (encodedMajorityRowNat code r) := by
  unfold encodedMajorityCode
  rw [bitSimCode_eq_codeEnumerate]
  have hs : wideTableNat (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code))
      (nativeRoundsTable (2 * r + 1) (controlSize code) (table code) (readout code)) =
      roundsRowNat (2 * r + 1) code := by
    funext coin wide buffer
    exact nativeRoundsTable_row_nat (2 * r + 1) code coin wide buffer
  rw [hs]
  rfl

theorem primrec_encodedMajorityCode : Primrec₂ encodedMajorityCode := by
  change Primrec (fun p : Code × ℕ => encodedMajorityCode p.1 p.2)
  have hn : Primrec (fun p : Code × ℕ => 2 * p.2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 1)
  have hcode : Primrec (fun p : Code × ℕ => p.1) := Primrec.fst
  have hQ := primrec_controlSize.comp hcode
  have hR := primrec_roundsControlMax.comp hn hQ
  have hb := primrec_bitSimControlMax.comp hn hR
  have ho : Primrec₂ (fun (p : Code × ℕ) (q : ℕ) => encodedMajorityOutputNat p.1 p.2 q) := by
    have hN : Primrec (fun p : (Code × ℕ) × ℕ => 2 * p.1.2 + 1) := hn.comp Primrec.fst
    have hq : Primrec (fun p : (Code × ℕ) × ℕ => controlSize p.1.1) := hQ.comp Primrec.fst
    have hsize : Primrec (fun p : (Code × ℕ) × ℕ =>
        bitSimControlMax (2 * p.1.2 + 1) (roundsControlMax (2 * p.1.2 + 1) (controlSize p.1.1)) + 1) :=
      Primrec.nat_add.comp (hb.comp Primrec.fst) (Primrec.const 1)
    exact primrec_bitMajorityOutputNat.comp
        (hN.pair (hq.pair (Primrec.nat_mod.comp Primrec.snd hsize)))
  have hr : Primrec₂ (fun (p : Code × ℕ) (row : ℕ) => encodedMajorityRowNat p.1 p.2 row) := by
    have hN : Primrec (fun p : (Code × ℕ) × ℕ => 2 * p.1.2 + 1) := hn.comp Primrec.fst
    have hwide :
        Primrec (fun p : (Code × ℕ) × ℕ => roundsControlMax (2 * p.1.2 + 1) (controlSize p.1.1)) :=
        hR.comp Primrec.fst
    have hc : Primrec (fun p : (Code × ℕ) × ℕ => p.1.1) := hcode.comp Primrec.fst
    apply primrec_bitSimRowNat_comp hN hwide Primrec.snd
    exact primrec_roundsRowNat_comp (hN.comp Primrec.fst) (hc.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (primrec_codeEnumerate hb ho hr).of_eq
      (fun p => (encodedMajorityCode_eq_codeEnumerate p.1 p.2).symm)

theorem primrec_rawMajorityCode : Primrec₂ rawMajorityCode := by
  change Primrec (fun p : Code × ℕ => rawMajorityCode p.1 p.2)
  have hn : Primrec (fun p : Code × ℕ => 2 * p.2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd) (Primrec.const 1)
  exact primrec_expandThenCode.comp hn primrec_encodedMajorityCode

theorem computable_rawMajorityCode : Computable₂ rawMajorityCode := primrec_rawMajorityCode.to_comp

theorem finite_tape_majority_compilation :
    ∃ compile : Code → ℕ → Code, Computable₂ compile ∧
      ∀ (code : Code) (r c k : ℕ), commonHalt code →
        (∀ input : List Bool, ∀ w : Fin (c * input.length ^ k + c) → Bool,
          (coinTapeRun (table code) (readout code) (input.map some) (List.ofFn w)).1 ≠ none) →
        ∃ d : ℕ, 0 < d ∧ commonHalt (compile code r) ∧ ∀ input : List Bool,
          let T := c * input.length ^ k + c
          let B := d * input.length ^ (2 * (k + 1)) + d
          (∀ w : Fin B → Bool,
            (coinTapeRun (table (compile code r)) (readout (compile code r))
              (input.map some) (List.ofFn w)).1 ≠ none) ∧
          (∀ w : Fin B → Bool,
            coinTapeTransitionCount (table (compile code r)) (input.map some) (List.ofFn w) ≤ B) ∧
          (∀ target : Bool,
            fairTapeSuccess (table (compile code r)) (readout (compile code r)) (input.map some) B target =
              independentMajorityMass (table code) (readout code) (input.map some) T r target) ∧
          (∀ target : Bool, (2 / 3 : ℝ) ≤ fairTapeSuccess (table code) (readout code) (input.map some) T target →
            1 - (8 / 9 : ℝ) ^ r ≤
              fairTapeSuccess (table (compile code r)) (readout (compile code r)) (input.map some) B target) := by
  exact ⟨rawMajorityCode, computable_rawMajorityCode, rawMajorityCode_polynomial⟩

end Qatlib.Concepts.ClassicalTape.TapeCompilation
