/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryExt
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryEffective
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetAdversary
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedFiniteExecution
import Qatlib.Concepts.ConversionCore.WitnessCompile.GeneralAdversaryDefs
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

structure OrthogonalProjectors (H Y : Type) [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] where

  proj : Y → Matrix H H ℂ

  hidem : ∀ y, proj y * proj y = proj y

  hherm : ∀ y, (proj y).IsHermitian

  horth : ∀ y y', y ≠ y' → proj y * proj y' = 0

  hsum : (∑ y, proj y) = 1

noncomputable def projectivePovm {H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y] [DecidableEq Y]
    (P : OrthogonalProjectors H Y) : Y → Matrix H H ℂ := P.proj

noncomputable def projectiveCorrect {X H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y]
    [DecidableEq Y] (P : OrthogonalProjectors H Y) (f : X → Y) (states : X → QState H)
    (x : X) : QState H := P.proj (f x) *ᵥ states x

noncomputable def projectiveError {X H Y : Type} [Fintype H] [DecidableEq H] [Fintype Y]
    [DecidableEq Y] (P : OrthogonalProjectors H Y) (f : X → Y) (states : X → QState H)
    (x : X) : QState H := states x - projectiveCorrect P f states x

theorem projectiveCorrect_add_error {X H Y : Type} [Fintype H] [DecidableEq H]
    [Fintype Y] [DecidableEq Y] (P : OrthogonalProjectors H Y) (f : X → Y)
    (states : X → QState H) (x : X) :
    projectiveCorrect P f states x + projectiveError P f states x = states x := by
  funext h
  simp only [projectiveError, projectiveCorrect, Pi.sub_apply, Pi.add_apply]
  ring

noncomputable def genCutWitness {X : Type} [Fintype X] [DecidableEq X] (x y : X) :
    Matrix X X ℂ :=
  (1 / ‖cutWitness x y‖ : ℂ) • cutWitness x y

noncomputable def adversaryQueryLedger {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : Option (O × ℕ) → ℝ≥0∞ :=
  unboundedMass next cfg

noncomputable def truncatedQueryLedger {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) : O × ℕ → ℝ≥0∞ :=
  fun p => RandomizedExecution.runFor next fuel cfg (Sum.inl p.1, p.2)

noncomputable def discardedMass {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) : ℝ≥0∞ :=
  pendingMass next cfg fuel

noncomputable def truncatedQueryCount {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) (fuel : ℕ) : ℝ≥0∞ :=
  CostedLaw.expectedCost (RandomizedExecution.runFor next fuel cfg)

noncomputable def unboundedQueryCount {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (next : S → PMF (Configuration S O))
    (cfg : Configuration S O) : ℝ≥0∞ :=
  ∑' k : ℕ, pendingMass next cfg k

def ZenoUnitCharge {S : Type} (step : S → CostedLaw S) (s : ℕ → S) : Prop :=
  ZenoRun step s ∧ ∀ k : ℕ, (1 : ℝ≥0∞) ≤ CostedLaw.expectedCost (step (s k))

noncomputable def alphabetSymbolBits (a : ℕ) : ℕ := Nat.log2 a + 1

noncomputable def interrogationResources {n a : ℕ} [NeZero a] :
    Qatlib.Concepts.ConversionCore.WitnessCompile.AdversaryResources where
  inputLen := n * alphabetSymbolBits a
  gates := 3 * n
  space := n * alphabetSymbolBits a

noncomputable def adaptiveCoordinate {n D : ℕ} (hn : 0 < n) (o : Fin D) : Fin n :=
  ⟨o.val % n, Nat.mod_lt _ hn⟩

noncomputable def adaptiveInstrumentRound {n D : ℕ} (hn : 0 < n) :
    Qatlib.Concepts.ConversionCore.WitnessCompile.AdaptiveRound (Fin D) n D where
  inst := projectiveInstrument
  coord := adaptiveCoordinate hn

noncomputable def adaptiveAlphabetExecution {n D a : ℕ} (hn : 0 < n) :
    Qatlib.Concepts.ConversionCore.WitnessCompile.AlphabetAdaptive (Fin D) n D where
  rounds := n
  round := fun _ => adaptiveInstrumentRound hn
  alpha := a

abbrev AdaptiveExecutionState (D : ℕ) := Fin D

noncomputable def adaptiveLabelStep {D : ℕ} (c : Fin D) : Fin D :=
  ⟨c.val - 1, by omega⟩

noncomputable def adaptiveAdvance {D : ℕ} (c : Fin D) : Option (Fin D) :=
  if c.val = 0 then none else some (adaptiveLabelStep c)

noncomputable def adaptiveUnboundedNext {D : ℕ} (c : Fin D) :
    PMF (Configuration (AdaptiveExecutionState D) (Fin D)) :=
  match adaptiveAdvance c with
  | none => PMF.pure (Sum.inl c)
  | some c' => PMF.pure (Sum.inr c')

noncomputable def adaptiveHaltingCost {D : ℕ} (c₀ : Fin D) : ℕ := c₀.val + 1

theorem tape_mk₁_nth {Γ : Type} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (Turing.Tape.mk₁ l).nth n = l.getI n := by
  have h := Turing.Tape.mk'_nth_nat (Γ := Γ) (Turing.ListBlank.mk ([] : List Γ))
    (Turing.ListBlank.mk l) n
  have h2 : (Turing.Tape.mk₁ l).nth (n : ℤ)
      = (Turing.Tape.mk' (Turing.ListBlank.mk ([] : List Γ))
        (Turing.ListBlank.mk l)).nth (n : ℤ) := rfl
  rw [h2, h]
  rfl

noncomputable def scanMachine {a : ℕ} : Turing.TM0.Machine (Option (Fin a)) (Fin 1) :=
  fun _ s => if s = none then none else some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩

theorem scanMachine_apply {a : ℕ} (q : Fin 1) (s : Option (Fin a)) :
    scanMachine (a := a) q s =
      if s = none then none else some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩ := rfl

theorem scan_step {a : ℕ} (cfg : Turing.TM0.Cfg (Option (Fin a)) (Fin 1)) :
    Turing.TM0.step (scanMachine (a := a)) cfg =
      if cfg.Tape.head = none then none
      else some ⟨default, cfg.Tape.move Turing.Dir.right⟩ := by
  obtain ⟨q, T⟩ := cfg
  by_cases hT : T.head = none
  · rw [if_pos hT]
    have hnone : scanMachine (a := a) q T.head = none := by
      rw [scanMachine_apply]; simp [hT]
    simp [Turing.TM0.step, hnone]
  · rw [if_neg hT]
    have happ : scanMachine (a := a) q T.head =
        some ⟨default, Turing.TM0.Stmt.move Turing.Dir.right⟩ := by
      rw [scanMachine_apply]; simp [hT]
    simp [Turing.TM0.step, happ]

theorem scan_head {a : ℕ} (w : List (Option (Fin a))) (t : ℕ) :
    ((Turing.Tape.move Turing.Dir.right)^[t] (Turing.Tape.mk₁ w)).head = w.getI t := by
  rw [Turing.Tape.move_right_n_head]
  exact tape_mk₁_nth w t

theorem scan_after_of_noBlank {a : ℕ} {w : List (Option (Fin a))} {t : ℕ}
    (hnb : ∀ j, j < t → w.getI j ≠ none) :
    BitMachineAfter (scanMachine (a := a)) w t =
      some ⟨default, (Turing.Tape.move Turing.Dir.right)^[t] (Turing.Tape.mk₁ w)⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hstep : Turing.TM0.step (scanMachine (a := a))
        (⟨default, (Turing.Tape.move Turing.Dir.right)^[t]
          (Turing.Tape.mk₁ w)⟩ : Turing.TM0.Cfg (Option (Fin a)) (Fin 1))
        = some ⟨default, (Turing.Tape.move Turing.Dir.right)^[t + 1]
          (Turing.Tape.mk₁ w)⟩ := by
      have hhead : ((Turing.Tape.move Turing.Dir.right)^[t]
          (Turing.Tape.mk₁ w)).head = w.getI t := scan_head w t
      rw [scan_step, hhead]
      have hne : w.getI t ≠ none := hnb t (by omega)
      simp only [hne, if_false]
      rw [← Function.iterate_succ_apply' (Turing.Tape.move Turing.Dir.right) t
        (Turing.Tape.mk₁ w)]
    show (BitMachineAfter (scanMachine (a := a)) w t).bind
      (Turing.TM0.step (scanMachine (a := a))) = _
    rw [ih (by intro j hj; exact hnb j (by omega))]
    exact hstep

theorem bitMachineAfter_none_of_halts {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]
    {m : Turing.TM0.Machine Γ Λ} {w : List Γ} {t t' : ℕ}
    (h : BitMachineHaltsAt m w t) (ht : t < t') :
    BitMachineAfter m w t' = none := by
  induction t' with
  | zero => omega
  | succ t' ih =>
    show BitMachineAfter m w (t' + 1) = none
    show (BitMachineAfter m w t').bind (Turing.TM0.step m) = none
    by_cases hlt : t < t'
    · rw [ih hlt]
      rfl
    · have hteq : t = t' := by omega
      subst hteq
      obtain ⟨final, hrun, hstop⟩ := h
      rw [hrun]
      exact hstop

theorem scan_halts_at_some {a : ℕ} (w : List (Option (Fin a))) :
    ∃ t : ℕ, t ≤ w.length ∧ BitMachineHaltsAt (scanMachine (a := a)) w t := by
  have hnil : w.getI w.length = (none : Option (Fin a)) :=
    List.getI_eq_default (l := w) (by omega)
  have hex : ∃ t : ℕ, w.getI t = none := ⟨w.length, hnil⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hnil, ?_⟩
  refine ⟨⟨default, (Turing.Tape.move Turing.Dir.right)^[Nat.find hex]
    (Turing.Tape.mk₁ w)⟩, ?_, ?_⟩
  · exact scan_after_of_noBlank (by
      intro j hj hne
      have hmin := Nat.find_min' hex hne
      omega)
  · rw [scan_step]
    have hhead : ((Turing.Tape.move Turing.Dir.right)^[Nat.find hex] (Turing.Tape.mk₁ w)).head
        = w.getI (Nat.find hex) := scan_head w (Nat.find hex)
    rw [hhead, Nat.find_spec hex]
    rfl

def DataWord {a : ℕ} (w : List (Option (Fin a))) : Prop :=
  ∀ (j : ℕ), j < w.length → w.getI j ≠ none

theorem dataWord_of_cons {a : ℕ} {x : Option (Fin a)} {w : List (Option (Fin a))}
    (hx : x ≠ none) (hw : DataWord w) : DataWord (x :: w) := by
  intro j hj
  cases j with
  | zero =>
      rw [List.getI_cons_zero]
      exact hx
  | succ j =>
      rw [List.getI_cons_succ]
      have hlen : (x :: w).length = w.length + 1 := rfl
      rw [hlen] at hj
      exact hw j (by omega)

theorem dataWord_replicate {a : ℕ} {x : Option (Fin a)} (hx : x ≠ none) (n : ℕ) :
    DataWord (List.replicate n x) := by
  induction n with
  | zero => intro j hj; simp at hj
  | succ n ih =>
    rw [List.replicate_succ]
    exact dataWord_of_cons hx ih

noncomputable def scanFamily {a : ℕ} :
    Qatlib.Concepts.ConversionCore.WitnessCompile.NativeTMFamily (Option (Fin a)) (Fin 1) where
  machine := fun _ => scanMachine (a := a)

def interrogationWord {a : ℕ} : (n : ℕ) → (Fin n → Fin a) → List (Option (Fin a))
  | 0, _ => []
  | n + 1, symbols =>
      some (symbols ⟨0, Nat.succ_pos n⟩) :: interrogationWord n (fun j => symbols j.succ)

theorem interrogationWord_length {a : ℕ} : ∀ (n : ℕ) (symbols : Fin n → Fin a),
    (interrogationWord n symbols).length = n := by
  intro n
  induction n with
  | zero => intro symbols; rfl
  | succ n ih =>
    intro symbols
    rw [interrogationWord]
    simp only [List.length_cons]
    exact congrArg Nat.succ (ih (fun j => symbols j.succ))

theorem interrogationWord_isData {a : ℕ} : ∀ (n : ℕ) (symbols : Fin n → Fin a),
    DataWord (interrogationWord n symbols) := by
  intro n
  induction n with
  | zero => intro symbols j hj; rw [interrogationWord] at hj; simp at hj
  | succ n ih =>
    intro symbols
    rw [interrogationWord]
    exact dataWord_of_cons (by simp) (ih (fun j => symbols j.succ))

noncomputable def nativeInputBits {n a : ℕ} : ℕ := n * alphabetSymbolBits a

noncomputable def degenerateMachine {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] :
    Turing.TM0.Machine Γ Λ := fun _ _ => none

noncomputable def gramCrossFilteredGamma2 {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] {n : ℕ} {A : Type} [DecidableEq A]
    (input : X → Fin n → A) (ρ σ : X → QState H) : ℝ≥0∞ :=
  filteredGamma2 (gramStateMatrix ρ - gramStateMatrix σ) (genFilterDelta input)

def AlphabetConversionProgram
    {X H : Type} [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H) (W ε : ℝ) : Prop :=
  ∃ (c : ℕ), 0 < c ∧ ∃ (r : ℕ) (hr : 0 < r)
      (C : Qatlib.Concepts.GramQueryCore.LowerBoundTools.SourceWord
        (Qatlib.Concepts.GramQueryCore.LowerBoundTools.SourceSpace n q H r)),
    Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceWordLegal C ∧
    Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceWordCalls C
      ≤ c * Nat.ceil (W * Real.log (2/ε) / ε^2) ∧
    ((W = 0 ∨ n = 0 ∨ q = 0) →
      Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceWordCalls C = 0) ∧
    (∀ x, (∑ p, star ((Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceWordMatrix
          (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetOracle input x) C *ᵥ
        Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceClean n q r hr false (ρ x)) p) *
        Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceClean n q r hr true (σ x) p).re
          ≥ Real.sqrt (1 - ε)) ∧
    (ε ≤ W → ∀ x, ‖toEuclidean_fromVec
        (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceWordMatrix
          (Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAlphabetOracle input x) C *ᵥ
        Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceClean n q r hr false (ρ x) -
        Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceClean n q r hr true (σ x))‖
          < 4 * ε)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
