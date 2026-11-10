/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Qatlib.Concepts.ClassicalTape.TapeCompilation.ClassicalProbabilistic
import Qatlib.Concepts.QueryComplexity.Amplification.MajorityVote
import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Data.List.GetD
import Qatlib.Concepts.ClassicalTape.TapeBoundary
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Concepts.QueryComplexity.Amplification

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.ClassicalTape.TapeCompilation

open scoped BigOperators Classical

structure CoinRunResult (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where
  stopped : Option (Turing.TM0.Cfg Γ Λ)
  reads : ℕ
  transitions : ℕ

def coinConfigRunAux {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    List Bool → Turing.TM0.Cfg Γ Λ → CoinRunResult Γ Λ
  | [], cfg => if coinHalt M cfg then ⟨some cfg, 0, 0⟩ else ⟨none, 0, 0⟩
  | c :: cs, cfg =>
    if coinHalt M cfg then ⟨some cfg, 0, 0⟩ else
      match Turing.TM0.step (M c) cfg with
      | none => ⟨some cfg, 1, 0⟩
      | some next =>
        let r := coinConfigRunAux M cs next
        ⟨r.stopped, r.reads + 1, r.transitions + 1⟩

abbrev Code := List ℕ

def controlSize (code : Code) : ℕ := code.getD 0 0

def symbolIndex : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

def decodeSymbol (n : ℕ) : Option Bool :=
  match n with
  | 0 => none
  | 1 => some false
  | _ => some true

def actionIndex : Turing.TM0.Stmt (Option Bool) → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write none => 2
  | .write (some false) => 3
  | .write (some true) => 4

def decodeAction (n : ℕ) : Turing.TM0.Stmt (Option Bool) :=
  match n % 5 with
  | 0 => .move .left
  | 1 => .move .right
  | 2 => .write none
  | 3 => .write (some false)
  | _ => .write (some true)

def encodeTransition {Q : ℕ} :
    Option (Fin (Q + 1) × Turing.TM0.Stmt (Option Bool)) → ℕ
  | none => 0
  | some (q, stmt) => 5 * q.val + actionIndex stmt + 1

def decodeTransition (Q n : ℕ) :
    Option (Fin (Q + 1) × Turing.TM0.Stmt (Option Bool)) :=
  match n with
  | 0 => none
  | n + 1 => some (⟨n / 5 % (Q + 1), Nat.mod_lt _ (by omega)⟩, decodeAction n)

def rowIndex (Q : ℕ) (c : Bool) (q : Fin (Q + 1)) (a : Option Bool) : ℕ :=
  (c.toNat * (Q + 1) + q.val) * 3 + symbolIndex a

def table (code : Code) (coin : Bool) :
    Turing.TM0.Machine (Option Bool) (Fin (controlSize code + 1)) := fun q a =>
  decodeTransition (controlSize code)
    (code.getD (1 + (controlSize code + 1) + rowIndex (controlSize code) coin q a) 0)

def readout (code : Code) (q : Fin (controlSize code + 1)) : Bool :=
  code.getD (1 + q.val) 0 % 2 == 1

def commonHalt (code : Code) : Prop :=
  ∀ q a, (table code false q a = none) ↔ (table code true q a = none)

def totalAt (code : Code) (input : List Bool) (t : ℕ) : Prop :=
  ∀ ω : Fin t → Bool,
    (coinTapeRun (table code) (readout code) (input.map some) (List.ofFn ω)).1 ≠ none

def encodeMachine (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1)))
    (a : Fin (Q + 1) → Bool) : Code :=
  Q :: (List.ofFn (fun q : Fin (Q + 1) => (a q).toNat) ++
    List.ofFn (fun i : Fin (6 * (Q + 1)) =>
      encodeTransition (M (decide (3 * (Q + 1) ≤ i.val))
        ⟨i.val / 3 % (Q + 1), Nat.mod_lt _ (by omega)⟩ (decodeSymbol (i.val % 3)))))

def relabelTable {Γ Λ Λ' : Type*} [Inhabited Λ] [Inhabited Λ'] (e : Λ ≃ Λ')
    (M : Bool → Turing.TM0.Machine Γ Λ) (c : Bool) : Turing.TM0.Machine Γ Λ' :=
  fun q a => (M c (e.symm q) a).map fun p => (e p.1, p.2)

def relabelCfg {Γ Λ Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Λ'] (e : Λ ≃ Λ')
    (cfg : Turing.TM0.Cfg Γ Λ) : Turing.TM0.Cfg Γ Λ' := ⟨e cfg.q, cfg.Tape⟩

abbrev TallyState (N : ℕ) := Fin (N + 1) × Fin (N + 1)

def tallyTable (N : ℕ) (coin : Bool) :
    Turing.TM0.Machine (Option Bool) (TallyState N) := fun q a =>
  if h : q.1.val < N then
    some ((⟨q.1.val + 1, by omega⟩,
      ⟨min N (q.2.val + coin.toNat), by omega⟩), .write a)
  else none

def tallyAccept (N : ℕ) (q : TallyState N) : Bool := decide (N / 2 < q.2.val)

def trueCount (coins : List Bool) : ℕ := (coins.map Bool.toNat).sum

@[simp] theorem trueCount_nil : trueCount [] = 0 := rfl

@[simp] theorem trueCount_cons (c : Bool) (cs : List Bool) :
    trueCount (c :: cs) = c.toNat + trueCount cs := rfl

def tallyLabels (N : ℕ) : TallyState N ≃ Fin (N * (N + 2) + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

def nativeTallyTable (N : ℕ) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (N * (N + 2) + 1)) :=
  relabelTable (tallyLabels N) (tallyTable N)

def nativeTallyAccept (N : ℕ) (q : Fin (N * (N + 2) + 1)) : Bool :=
  tallyAccept N ((tallyLabels N).symm q)

def tallyCode (N : ℕ) : Code :=
  encodeMachine (N * (N + 2)) (nativeTallyTable N) (nativeTallyAccept N)

abbrev MarkerCell := Option Bool × Option Bool × Bool

def fillCell (s : MarkerCell) : MarkerCell := (s.1, s.1, s.2.2)

def markerCopyTable : Turing.TM0.Machine MarkerCell (Fin 5) := fun q s =>
  match q.val with
  | 0 => some (1, .write (s.1, s.2.1, true))
  | 1 => if s.1.isSome then some (2, .write (fillCell s)) else some (3, .write s)
  | 2 => some (1, .move .right)
  | 3 => if s.2.2 then some (4, .write s) else some (3, .move .left)
  | _ => none

def markerCopyAccept (q : Fin 5) : Bool := q == 4

def markerInput (input : List Bool) : List MarkerCell :=
  input.map fun b => (some b, none, false)

def markerCopyResult (input : List Bool) : Turing.Tape MarkerCell :=
  let T := Turing.Tape.mk₁ (input.map fun b => (some b, some b, false))
  T.write (T.head.1, T.head.2.1, true)

def eraseCell (s : MarkerCell) : MarkerCell := (s.1, none, s.2.2)

def markerResetTable : Turing.TM0.Machine MarkerCell (Fin 5) := fun q s =>
  match q.val with
  | 0 => some (1, .write (s.1, s.2.1, true))
  | 1 => if s.1.isSome then some (2, .write (eraseCell s)) else some (3, .write s)
  | 2 => some (1, .move .right)
  | 3 => if s.2.2 then some (4, .write s) else some (3, .move .left)
  | _ => none

def markerResetAccept (q : Fin 5) : Bool := q == 4

def markerResetInput (input : List (Bool × Option Bool)) : List MarkerCell :=
  input.map fun p => (some p.1, p.2, false)

def markerResetResult (input : List (Bool × Option Bool)) : Turing.Tape MarkerCell :=
  let T := Turing.Tape.mk₁ (input.map fun p => (some p.1, none, false))
  T.write (T.head.1, T.head.2.1, true)

def mapCfg {Γ Λ Μ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Μ]
    (f : Λ → Μ) (cfg : Turing.TM0.Cfg Γ Λ) : Turing.TM0.Cfg Γ Μ := ⟨f cfg.q, cfg.Tape⟩

def sequenceTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (M₂ : Turing.TM0.Machine Γ Μ) :
    Turing.TM0.Machine Γ (Sum Λ Μ) := fun q a =>
  match q with
  | .inl q => match M₁ q a with
    | none => some (.inr default, .write a)
    | some (q', stmt) => some (.inl q', stmt)
  | .inr q => (M₂ q a).map fun p => (.inr p.1, p.2)

def sequenceCoinTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (M₂ : Bool → Turing.TM0.Machine Γ Μ) :
    Bool → Turing.TM0.Machine Γ (Sum Λ Μ) := fun c => sequenceTable (M₁ c) (M₂ c)

def markerCopyResetLabels : Sum (Fin 5) (Fin 5) ≃ Fin 10 := finSumFinEquiv

def markerCopyResetTable : Turing.TM0.Machine MarkerCell (Fin 10) :=
  relabelTable markerCopyResetLabels (fun _ => sequenceTable markerCopyTable markerResetTable) false

def markerCopyResetAccept (q : Fin 10) : Bool :=
  match markerCopyResetLabels.symm q with
  | .inl _ => false
  | .inr q => markerResetAccept q

def markerErasedResult (input : List Bool) : Turing.Tape MarkerCell :=
  markerResetResult (input.map fun b => (b, none))

def workMap : Turing.PointedMap MarkerCell (Option Bool) := ⟨fun s => s.2.1, rfl⟩

def workCfg {Λ : Type*} [Inhabited Λ] (cfg : Turing.TM0.Cfg MarkerCell Λ) :
    Turing.TM0.Cfg (Option Bool) Λ := ⟨cfg.q, cfg.Tape.map workMap⟩

def liftWorkTable {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) :
    Turing.TM0.Machine MarkerCell Λ := fun q s =>
  (M c q s.2.1).map fun p =>
    match p.2 with
    | .move d => (p.1, .move d)
    | .write b => (p.1, .write (s.1, b, s.2.2))

def prepareLabels (Q : ℕ) : Sum (Fin 5) (Fin (Q + 1)) ≃ Fin (Q + 6) :=
  finSumFinEquiv.trans (finCongr (by omega))

def prepareCoinTable (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) :
    Bool → Turing.TM0.Machine MarkerCell (Fin (Q + 6)) :=
  relabelTable (prepareLabels Q) (sequenceCoinTable (fun _ => markerCopyTable) (liftWorkTable M))

def sourcePhaseAccept {Λ Μ : Type*} (a : Μ → Bool) : Sum Λ Μ → Bool
  | .inl _ => false
  | .inr q => a q

def prepareAccept (Q : ℕ) (a : Fin (Q + 1) → Bool) (q : Fin (Q + 6)) : Bool :=
  sourcePhaseAccept a ((prepareLabels Q).symm q)

def appendCoinWords (k m : ℕ) :
    ((Fin k → Bool) × (Fin m → Bool)) ≃ (Fin (k + m) → Bool) where
  toFun p := Fin.append p.1 p.2
  invFun w := (fun i => w (i.castAdd m), fun i => w (i.natAdd k))
  left_inv p := by
    obtain ⟨u, v⟩ := p
    apply Prod.ext
    · funext i
      exact Fin.append_left' u v i
    · funext i
      exact Fin.append_right u v i
  right_inv w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left' (fun j => w (j.castAdd m)) (fun j => w (j.natAdd k)) j
    · exact Fin.append_right (fun j => w (j.castAdd m)) (fun j => w (j.natAdd k)) j

def consCoinWords (t : ℕ) : (Bool × (Fin t → Bool)) ≃ (Fin (t + 1) → Bool) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by obtain ⟨b, w⟩ := p; rfl
  right_inv w := Fin.cons_self_tail w

def prepareCoinWords (input : List Bool) (t : ℕ) :
    ((Fin (3 * input.length + 3) → Bool) × Bool × (Fin t → Bool)) ≃
      (Fin ((3 * input.length + 3) + (t + 1)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (consCoinWords t)).trans
    (appendCoinWords (3 * input.length + 3) (t + 1))

def freshBlocks (N t : ℕ) : (Fin (N * t) → Bool) ≃ (Fin N → Fin t → Bool) :=
  (Equiv.arrowCongr (finProdFinEquiv (m := N) (n := t)).symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin N) (Fin t) Bool)

noncomputable def independentMajorityMass {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (a : Λ → Bool) (input : List Γ)
    (t r : ℕ) (target : Bool) : ℝ :=
  (∑ ω : Fin (2 * r + 1) → Fin t → Bool,
    if (MajorityBit fun j =>
        (coinTapeRun M a input (List.ofFn (ω j))).1 == some true) = target
      then (1 : ℝ) else 0) / 2 ^ (t * (2 * r + 1))

abbrev HomeState := Bool × Bool

def homeDirection (left : Bool) : Turing.Dir := if left then .right else .left

def markerHomeTable : Turing.TM0.Machine MarkerCell HomeState := fun q s =>
  if s.2.2 then none else some (q, .move (homeDirection q.1))

def markerHomeAccept (q : HomeState) : Bool := q.2

def homeDistance (left : Bool) (n : ℕ) : ℤ := if left then -(n : ℤ) else n

def HomeAt (T : Turing.Tape MarkerCell) (off : ℤ) : Prop :=
  ∀ i : ℤ, (T.nth i).2.2 = decide (i + off = 0)

def SideAt (left : Bool) (off : ℤ) : Prop :=
  (off < 0 → left = true) ∧ (0 < off → left = false)

def sideAfterMove (old atHome : Bool) : Turing.Dir → Bool
  | .left => if atHome then true else old
  | .right => if atHome then false else old

def sideWorkTable {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (c : Bool) :
    Turing.TM0.Machine MarkerCell (Λ × Bool) := fun q s =>
  (M c q.1 s.2.1).map fun p => match p.2 with
    | .move d => ((p.1, sideAfterMove q.2 s.2.2 d), .move d)
    | .write b => ((p.1, q.2), .write (s.1, b, s.2.2))

def sideWorkCfg {Λ : Type*} [Inhabited Λ] (cfg : Turing.TM0.Cfg MarkerCell (Λ × Bool)) :
    Turing.TM0.Cfg (Option Bool) Λ := ⟨cfg.q.1, cfg.Tape.map workMap⟩

def dispatchTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Turing.TM0.Machine Γ Λ) (next : Λ → Μ) (M₂ : Turing.TM0.Machine Γ Μ) :
    Turing.TM0.Machine Γ (Sum Λ Μ) := fun q a =>
  match q with
  | .inl q => match M₁ q a with
    | none => some (.inr (next q), .write a)
    | some (q', stmt) => some (.inl q', stmt)
  | .inr q => (M₂ q a).map fun p => (.inr p.1, p.2)

def dispatchCoinTable {Γ Λ Μ : Type*} [Inhabited Λ] [Inhabited Μ]
    (M₁ : Bool → Turing.TM0.Machine Γ Λ) (next : Λ → Μ)
    (M₂ : Bool → Turing.TM0.Machine Γ Μ) :
    Bool → Turing.TM0.Machine Γ (Sum Λ Μ) := fun c => dispatchTable (M₁ c) next (M₂ c)

def homingCoinTable {Λ : Type*} [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine (Option Bool) Λ) (a : Λ → Bool) :
    Bool → Turing.TM0.Machine MarkerCell (Sum (Λ × Bool) HomeState) :=
  dispatchCoinTable (sideWorkTable M) (fun q => (q.2, a q.1)) (fun _ => markerHomeTable)

def homingAccept {Λ : Type*} : Sum (Λ × Bool) HomeState → Bool
  | .inl _ => false
  | .inr q => q.2

def homingLabels (Q : ℕ) :
    Sum (Fin (Q + 1) × Bool) HomeState ≃ Fin (2 * Q + 6) :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv |>.sumCongr
    ((Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm).trans finProdFinEquiv)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))

def nativeHomingCoinTable (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine MarkerCell (Fin (2 * Q + 6)) :=
  relabelTable (homingLabels Q) (homingCoinTable M a)

def nativeHomingAccept (Q : ℕ) : Fin (2 * Q + 6) → Bool :=
  fun q => homingAccept ((homingLabels Q).symm q)

def prepareHomingLabels (Q : ℕ) : Sum (Fin 5) (Fin (2 * Q + 6)) ≃ Fin (2 * Q + 11) :=
  finSumFinEquiv.trans (finCongr (by omega))

def prepareHomingCoinTable (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine MarkerCell (Fin (2 * Q + 11)) :=
  relabelTable (prepareHomingLabels Q)
    (sequenceCoinTable (fun _ => markerCopyTable) (nativeHomingCoinTable Q M a))

def prepareHomingAccept (Q : ℕ) (q : Fin (2 * Q + 11)) : Bool :=
  sourcePhaseAccept (nativeHomingAccept Q) ((prepareHomingLabels Q).symm q)

def homingCoinWords (input : List Bool) (t : ℕ) :
    ((Fin (3 * input.length + 3) → Bool) × Bool ×
      ((Fin t → Bool) × (Fin (t + 1) → Bool))) ≃
      (Fin ((3 * input.length + 3) + ((t + (t + 1)) + 1)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl Bool) (appendCoinWords t (t + 1)))).trans
    (prepareCoinWords input (t + (t + 1)))

def InputAt (initial current : Turing.Tape MarkerCell) (off : ℤ) : Prop :=
  ∀ i : ℤ, (current.nth i).1 = (initial.nth (i + off)).1

def ProtectedAt (initial current : Turing.Tape MarkerCell) (off : ℤ) : Prop :=
  HomeAt current off ∧ InputAt initial current off

abbrev TrackCell (N : ℕ) := Option Bool × (Fin N → Option Bool) × Bool

def focusTrack {N : ℕ} (j : Fin N) : Turing.PointedMap (TrackCell N) MarkerCell :=
  ⟨fun s => (s.1, s.2.1 j, s.2.2), rfl⟩

def writeTrack {N : ℕ} (j : Fin N) (s : TrackCell N) (b : MarkerCell) : TrackCell N :=
  (b.1, Function.update s.2.1 j b.2.1, b.2.2)

def trackTable {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (M : Bool → Turing.TM0.Machine MarkerCell Λ) (c : Bool) :
    Turing.TM0.Machine (TrackCell N) Λ := fun q s =>
  (M c q (focusTrack j s)).map fun p =>
    match p.2 with
    | .move d => (p.1, .move d)
    | .write b => (p.1, .write (writeTrack j s b))

def focusTrackCfg {N : ℕ} {Λ : Type*} [Inhabited Λ] (j : Fin N)
    (cfg : Turing.TM0.Cfg (TrackCell N) Λ) : Turing.TM0.Cfg MarkerCell Λ :=
  ⟨cfg.q, cfg.Tape.map (focusTrack j)⟩

def tracksInput (N : ℕ) (input : List Bool) : List (TrackCell N) :=
  input.map fun b => (some b, fun _ => none, false)

def BlankTrack {N : ℕ} (j : Fin N) (T : Turing.Tape (TrackCell N)) : Prop :=
  ∀ i : ℤ, (T.nth i).2.1 j = none

def trackRoundTable {N : ℕ} (j : Fin N) (Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (TrackCell N) (Fin (2 * Q + 11)) :=
  trackTable j (prepareHomingCoinTable Q M a)

def markedInputTape (input : List Bool) : Turing.Tape MarkerCell :=
  let T := Turing.Tape.mk₁ (markerInput input)
  T.write (T.head.1, T.head.2.1, true)

abbrev RoundsState (N Q : ℕ) := Fin (N + 1) × Fin (N + 1) × Fin (2 * Q + 11)

def boundedSucc (N : ℕ) (q : Fin (N + 1)) : Fin (N + 1) :=
  ⟨min (q.val + 1) N, Nat.lt_succ_of_le (min_le_right _ _)⟩

def roundsNext (N Q : ℕ) (q : RoundsState N Q) : RoundsState N Q :=
  (boundedSucc N q.1,
    (if prepareHomingAccept Q q.2.2 then boundedSucc N q.2.1 else q.2.1), 0)

def roundsTable (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool)
    (c : Bool) : Turing.TM0.Machine (TrackCell N) (RoundsState N Q) := fun q s =>
  if hj : q.1.val < N then
    match trackRoundTable ⟨q.1.val, hj⟩ Q M a c q.2.2 s with
    | none => some (roundsNext N Q q, .write s)
    | some (next, stmt) => some ((q.1, q.2.1, next), stmt)
  else none

def roundsAccept (N Q : ℕ) (q : RoundsState N Q) : Bool := decide (N / 2 < q.2.1.val)

def roundsControlMax (N Q : ℕ) : ℕ := (N + 1) * ((N + 1) * (2 * Q + 11)) - 1

def roundsLabels (N Q : ℕ) : RoundsState N Q ≃ Fin (roundsControlMax N Q + 1) :=
  ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by
      have h : 0 < (N + 1) * ((N + 1) * (2 * Q + 11)) :=
        Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
      unfold roundsControlMax
      omega))

def nativeRoundsTable (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (Option Bool) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) :
    Bool → Turing.TM0.Machine (TrackCell N) (Fin (roundsControlMax N Q + 1)) :=
  relabelTable (roundsLabels N Q) (roundsTable N Q M a)

def nativeRoundsAccept (N Q : ℕ) : Fin (roundsControlMax N Q + 1) → Bool :=
  fun q => roundsAccept N Q ((roundsLabels N Q).symm q)

def roundsCfg {N Q : ℕ} (j count : Fin (N + 1))
    (cfg : Turing.TM0.Cfg (TrackCell N) (Fin (2 * Q + 11))) :
    Turing.TM0.Cfg (TrackCell N) (RoundsState N Q) := ⟨(j, count, cfg.q), cfg.Tape⟩

noncomputable def stoppedValue {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (g : Turing.TM0.Cfg Γ Λ → ℝ) (r : CoinRunResult Γ Λ) : ℝ := r.stopped.elim 0 g

noncomputable def fairCfgValue {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) (g : Turing.TM0.Cfg Γ Λ → ℝ)
    (n : ℕ) (cfg : Turing.TM0.Cfg Γ Λ) : ℝ :=
  (∑ w : Fin n → Bool, stoppedValue g (coinConfigRunAux M (List.ofFn w) cfg)) / 2 ^ n

def coinStepsAux {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Bool → Turing.TM0.Machine Γ Λ) :
    List Bool → Turing.TM0.Cfg Γ Λ → Option (Turing.TM0.Cfg Γ Λ)
  | [], cfg => some cfg
  | c :: cs, cfg => (Turing.TM0.step (M c) cfg).bind (coinStepsAux M cs)

noncomputable def remainingVoteMass (N : ℕ) (pfalse ptrue : ℝ) (target : Bool) : ℕ → ℕ → ℝ
  | 0, count => if decide (N / 2 < count) = target then 1 else 0
  | fuel + 1, count =>
      pfalse * remainingVoteMass N pfalse ptrue target fuel count +
      ptrue * remainingVoteMass N pfalse ptrue target fuel (count + 1)

noncomputable def uniformVotesMass {I : Type*} [Fintype I] (N : ℕ) (vote : I → Bool)
    (target : Bool) (fuel count : ℕ) : ℝ :=
  (∑ w : Fin fuel → I,
    if decide (N / 2 < count + trueCount (List.ofFn fun j => vote (w j))) = target then (1 : ℝ) else 0) /
      (Fintype.card I : ℝ) ^ fuel

def consTrials (I : Type*) (n : ℕ) : (I × (Fin n → I)) ≃ (Fin (n + 1) → I) where
  toFun p := Fin.cons p.1 p.2
  invFun w := (w 0, Fin.tail w)
  left_inv p := by obtain ⟨x, w⟩ := p; rfl
  right_inv w := Fin.cons_self_tail w

def bitBlock (N : ℕ) (s : TrackCell N) : List (Option Bool) :=
  s.1 :: (List.ofFn s.2.1 ++ [if s.2.2 then some true else none, none])

def expandedInput (N : ℕ) (input : List Bool) : List (Option Bool) :=
  input.flatMap fun b => some b :: List.replicate (N + 2) none

abbrev ExpandQueue (N : ℕ) := Fin (N + 2) → Option Bool

def expandQueuePush {N : ℕ} (q : ExpandQueue N) (s : Option Bool) : ExpandQueue N :=
  Fin.snoc (Fin.tail q) s

abbrev ExpandState (N : ℕ) := Fin 12 × Bool × Fin (N + 3) × ExpandQueue N

def expandInputTable (N : ℕ) : Turing.TM0.Machine (Option Bool) (ExpandState N) := fun q s =>
  let phase := q.1
  let first := q.2.1
  let i := q.2.2.1
  let fifo := q.2.2.2
  match phase.val with
  | 0 => if s.isSome then some ((1, true, 0, fun _ => none), .move .right) else none
  | 1 => if hi : i.val < N + 2 then
      some ((2, first, i, Function.update fifo ⟨i.val, hi⟩ s),
        .write (if first && decide (i.val = N) then some true else none)) else none
  | 2 => if hi : i.val + 1 < N + 2 then
      some ((1, first, ⟨i.val + 1, by omega⟩, fifo), .move .right)
    else some ((3, first, 0, fifo), .move .right)
  | 3 => if (∀ k, fifo k = none) ∧ s = none then
      some ((5, first, 0, fifo), .move .left)
    else some ((4, first, 0, expandQueuePush fifo s), .write (fifo 0))
  | 4 => some ((3, first, 0, fifo), .move .right)
  | 5 => if s.isSome then some ((5, first, 0, fifo), .move .left)
    else some ((6, false, 0, fifo), .move .right)
  | 6 => if s.isSome then some ((1, false, 0, fun _ => none), .move .right)
    else some ((7, false, 0, fifo), .move .left)
  | 7 => some ((8, false, 0, fifo), .move .left)
  | 8 => if s = some true then some ((10, false, ⟨N + 1, by omega⟩, fifo), .write none)
    else some ((9, false, ⟨N + 2, by omega⟩, fifo), .move .left)
  | 9 => if 1 < i.val then some ((9, false, ⟨i.val - 1, by omega⟩, fifo), .move .left)
    else some ((8, false, 0, fifo), .move .left)
  | 10 => if 1 < i.val then some ((10, false, ⟨i.val - 1, by omega⟩, fifo), .move .left)
    else some ((11, false, 0, fifo), .move .left)
  | _ => none

def expandWindow (N : ℕ) (raw : List Bool) (k : ℕ) : ExpandQueue N :=
  fun i => (raw.map some).getD (k + i.val) none

def expandShiftTape (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) (k : ℕ) :
    Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.mk (((raw.map some).take k).reverse ++ pre.reverse))
    (Turing.ListBlank.mk ((raw.map some).drop (N + 2 + k)))

def expandShiftCfg (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (k : ℕ) :
    Turing.TM0.Cfg (Option Bool) (ExpandState N) :=
  ⟨(3, first, 0, expandWindow N raw k), expandShiftTape N pre raw k⟩

def insertSlots (N : ℕ) (first : Bool) : List (Option Bool) :=
  List.ofFn fun i : Fin (N + 2) => if first && decide (i.val = N) then some true else none

def expandCapture (N : ℕ) (raw : List Bool) (i : ℕ) : ExpandQueue N :=
  fun j => if j.val < i then (raw.map some).getD j.val none else none

def expandGatherTape (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (i : ℕ) :
    Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.mk (((insertSlots N first).take i).reverse ++ pre.reverse))
    (Turing.ListBlank.mk ((raw.map some).drop i))

def expandGatherCfg (N : ℕ) (first : Bool) (pre : List (Option Bool)) (raw : List Bool) (i : Fin (N + 3)) :
    Turing.TM0.Cfg (Option Bool) (ExpandState N) :=
  ⟨(if i.val < N + 2 then 1 else 3, first, if i.val < N + 2 then i else 0, expandCapture N raw i.val),
    expandGatherTape N first pre raw i.val⟩

def expandCheckCfg (N : ℕ) (pre : List (Option Bool)) (raw : List Bool) :
    Turing.TM0.Cfg (Option Bool) (ExpandState N) :=
  ⟨(6, false, 0, fun _ => none),
    Turing.Tape.mk' (Turing.ListBlank.mk pre.reverse) (Turing.ListBlank.mk (raw.map some))⟩

def expandProcessTime (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (N + 2) + 3 * n + 3 + expandProcessTime N n

def markedExpandedInput (N : ℕ) (b : Bool) (raw : List Bool) : List (Option Bool) :=
  (some b :: insertSlots N true) ++ expandedInput N raw

def optionBoolFin : Option Bool ≃ Fin 3 where
  toFun s := ⟨symbolIndex s, by cases s with
    | none => decide
    | some b => cases b <;> decide⟩
  invFun i := decodeSymbol i.val
  left_inv s := by cases s with
    | none => rfl
    | some b => cases b <;> rfl
  right_inv := by decide

def expandQueueLabels (N : ℕ) : ExpandQueue N ≃ Fin (3 ^ (N + 2)) :=
  (Equiv.piCongrRight fun _ => optionBoolFin).trans finFunctionFinEquiv

def expandControlMax (N : ℕ) : ℕ := 12 * (2 * ((N + 3) * 3 ^ (N + 2))) - 1

def expandLabels (N : ℕ) : ExpandState N ≃ Fin (expandControlMax N + 1) :=
  ((Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr finTwoEquiv.symm
      ((Equiv.prodCongr (Equiv.refl _) (expandQueueLabels N)).trans finProdFinEquiv)).trans finProdFinEquiv)).trans
        finProdFinEquiv).trans (finCongr (by
          have h : 0 < 12 * (2 * ((N + 3) * 3 ^ (N + 2))) :=
            Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (pow_pos (by decide) _)))
          unfold expandControlMax
          omega))

def nativeExpandTable (N : ℕ) : Turing.TM0.Machine (Option Bool) (Fin (expandControlMax N + 1)) :=
  relabelTable (expandLabels N) (fun _ => expandInputTable N) false

def expandCode (N : ℕ) : Code :=
  encodeMachine (expandControlMax N) (fun _ => nativeExpandTable N) (fun _ => false)

def tapeAt (l : List (Option Bool)) (n : ℕ) : Turing.Tape (Option Bool) :=
  (Turing.Tape.move .right)^[n] (Turing.Tape.mk₁ l)

def expandTime (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => expandProcessTime N (n + 1) + (n + 1) * (N + 3) + 1

def bitHalf (N : ℕ) (rev : Bool) (l : Turing.ListBlank (TrackCell N)) :
    Turing.ListBlank (Option Bool) := by
  apply Turing.ListBlank.flatMap l (fun s => if rev then (bitBlock N s).reverse else bitBlock N s)
  refine ⟨N + 3, ?_⟩
  have hd : bitBlock N default = List.replicate (N + 3) none := by
    change none :: (List.ofFn (fun _ : Fin N => (none : Option Bool)) ++ List.replicate 2 none) =
      none :: List.replicate (N + 2) none
    rw [List.ofFn_const, ← List.replicate_add]
  simp only [hd, List.reverse_replicate, ite_self]
  rfl

def bitTape (N : ℕ) (T : Turing.Tape (TrackCell N)) : Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (bitHalf N true T.left)
    (Turing.ListBlank.append (bitBlock N T.head) (bitHalf N false T.right))

abbrev BitBuffer (N : ℕ) := Fin (N + 2) → Option Bool

def cellBuffer (N : ℕ) (s : TrackCell N) : BitBuffer N :=
  Fin.cons s.1 (Fin.snoc s.2.1 (if s.2.2 then some true else none))

def bufferCell (N : ℕ) (f : BitBuffer N) : TrackCell N :=
  (f 0, fun j => f j.castSucc.succ, f (Fin.last (N + 1)) == some true)

abbrev BitSimState (N : ℕ) (Λ : Type*) := Fin 9 × Λ × Fin (3 * (N + 2) + 1) × BitBuffer N

def bitSimTable {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) Λ) :
    Bool → Turing.TM0.Machine (Option Bool) (BitSimState N Λ) := fun coin q s =>
  let phase := q.1
  let wide := q.2.1
  let i := q.2.2.1
  let buf := q.2.2.2
  match phase.val with
  | 0 => if hi : i.val < N + 2 then
      some ((if i.val + 1 < N + 2 then 0 else 1, wide,
        if i.val + 1 < N + 2 then ⟨i.val + 1, by omega⟩ else ⟨N + 2, by omega⟩,
        Function.update buf ⟨i.val, hi⟩ s), .move .right)
    else none
  | 1 => if 0 < i.val then
      some ((if 1 < i.val then 1 else 2, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else 0, buf), .move .left)
    else none
  | 2 => match M coin wide (bufferCell N buf) with
    | none => none
    | some (next, .move .left) => some ((3, next, ⟨N + 3, by omega⟩, buf), .write s)
    | some (next, .move .right) => some ((4, next, ⟨N + 3, by omega⟩, buf), .write s)
    | some (next, .write v) => some ((5, next, 0, cellBuffer N v), .write s)
  | 3 => if 0 < i.val then
      some ((if 1 < i.val then 3 else 6, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else ⟨2 * (N + 2) - 1, by omega⟩, buf), .move .left)
    else none
  | 4 => if 0 < i.val then
      some ((if 1 < i.val then 4 else 6, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else ⟨2 * (N + 2) - 1, by omega⟩, buf), .move .right)
    else none
  | 5 => if hi : i.val < N + 2 then some ((7, wide, i, buf), .write (buf ⟨i.val, hi⟩)) else none
  | 6 => if 0 < i.val then
      some ((if 1 < i.val then 6 else 0, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else 0,
        if 1 < i.val then buf else fun _ => none), .write s)
    else none
  | 7 => if hi : i.val + 1 < N + 2 then
      some ((5, wide, ⟨i.val + 1, by omega⟩, buf), .move .right)
    else some ((8, wide, ⟨N + 2, by omega⟩, buf), .move .right)
  | 8 => if 0 < i.val then
      some ((if 1 < i.val then 8 else 0, wide,
        if 1 < i.val then ⟨i.val - 1, by omega⟩ else 0,
        if 1 < i.val then buf else fun _ => none), .move .left)
    else none
  | _ => none

def bitReady {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ) (cfg : Turing.TM0.Cfg (TrackCell N) Λ) :
    Turing.TM0.Cfg (Option Bool) (BitSimState N Λ) :=
  ⟨(2, cfg.q, 0, cellBuffer N cfg.Tape.head), bitTape N cfg.Tape⟩

def tapeBuffer (N : ℕ) (T : Turing.Tape (Option Bool)) : BitBuffer N :=
  fun j => T.nth (j.val : ℤ)

def bitCapture (N : ℕ) (T : Turing.Tape (Option Bool)) (i : ℕ) : BitBuffer N :=
  fun j => if j.val < i then T.nth (j.val : ℤ) else none

def bitFetchCfg {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ) (q : Λ) (T : Turing.Tape (Option Bool))
    (i : Fin (N + 3)) : Turing.TM0.Cfg (Option Bool) (BitSimState N Λ) :=
  ⟨(if i.val < N + 2 then 0 else 1, q, ⟨i.val, by have := i.isLt; omega⟩, bitCapture N T i.val),
    (Turing.Tape.move .right)^[i.val] T⟩

def bitWriteTape (N : ℕ) (new old : BitBuffer N) (L R : Turing.ListBlank (Option Bool)) (i : ℕ) :
    Turing.Tape (Option Bool) :=
  Turing.Tape.mk' (Turing.ListBlank.append ((List.ofFn new).take i).reverse L)
    (Turing.ListBlank.append ((List.ofFn old).drop i) R)

def bitWriteCfg {Λ : Type*} [Fintype Λ] [Inhabited Λ] (N : ℕ) (q : Λ) (new old : BitBuffer N)
    (L R : Turing.ListBlank (Option Bool)) (i : Fin (N + 3)) :
    Turing.TM0.Cfg (Option Bool) (BitSimState N Λ) :=
  ⟨(if i.val < N + 2 then 5 else 8, q,
    if i.val < N + 2 then ⟨i.val, by have := i.isLt; omega⟩ else ⟨N + 2, by omega⟩, new),
    bitWriteTape N new old L R i.val⟩

def bitSimControlMax (N Q : ℕ) : ℕ :=
  9 * ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) - 1

def bitSimLabels (N Q : ℕ) : BitSimState N (Fin (Q + 1)) ≃ Fin (bitSimControlMax N Q + 1) :=
  ((Equiv.prodCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _)
      ((Equiv.prodCongr (Equiv.refl _) (expandQueueLabels N)).trans finProdFinEquiv)).trans
        finProdFinEquiv)).trans finProdFinEquiv).trans (finCongr (by
          have h : 0 < 9 * ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) :=
            Nat.mul_pos (by decide) (Nat.mul_pos (by omega)
              (Nat.mul_pos (by omega) (pow_pos (by decide) _)))
          unfold bitSimControlMax
          omega))

def nativeBitSimTable (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (bitSimControlMax N Q + 1)) :=
  relabelTable (bitSimLabels N Q) (bitSimTable N M)

def nativeBitSimAccept (N Q : ℕ) (a : Fin (Q + 1) → Bool)
    (q : Fin (bitSimControlMax N Q + 1)) : Bool :=
  a ((bitSimLabels N Q).symm q).2.1

def bitSimCode (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1))) (a : Fin (Q + 1) → Bool) : Code :=
  encodeMachine (bitSimControlMax N Q) (nativeBitSimTable N Q M) (nativeBitSimAccept N Q a)

def bitMicroWidth (N : ℕ) : ℕ := 5 * (N + 2) + 1

def bitMicroCoins (N : ℕ) (blocks : List (Fin (bitMicroWidth N) → Bool)) : List Bool :=
  blocks.flatMap List.ofFn

def bitSourceCoins (N : ℕ) (blocks : List (Fin (bitMicroWidth N) → Bool)) : List Bool :=
  blocks.map fun b => b ⟨0, by unfold bitMicroWidth; omega⟩

def bitSplitWords (N t : ℕ) :
    ((Fin t → Bool) × (Fin t → Fin (5 * (N + 2)) → Bool)) ≃
      (Fin t → Fin (bitMicroWidth N) → Bool) where
  toFun p j := Fin.cons (p.1 j) (p.2 j)
  invFun w := (fun j => w j ⟨0, by unfold bitMicroWidth; omega⟩, fun j => Fin.tail (w j))
  left_inv p := by
    apply Prod.ext
    · funext j
      rfl
    · funext j i
      rfl
  right_inv w := by
    funext j
    exact Fin.cons_self_tail (w j)

def bitInitialWords (N t : ℕ) :
    ((Fin (2 * (N + 2)) → Bool) × (Fin t → Fin (bitMicroWidth N) → Bool)) ≃
      (Fin (2 * (N + 2) + t * bitMicroWidth N) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (freshBlocks t (bitMicroWidth N)).symm).trans
    (appendCoinWords (2 * (N + 2)) (t * bitMicroWidth N))

def encodedMajorityCode (code : Code) (r : ℕ) : Code :=
  bitSimCode (2 * r + 1) (roundsControlMax (2 * r + 1) (controlSize code))
    (nativeRoundsTable (2 * r + 1) (controlSize code) (table code) (readout code))
    (nativeRoundsAccept (2 * r + 1) (controlSize code))

def expandedSequenceMax (N : ℕ) (next : Code) : ℕ :=
  controlSize (expandCode N) + controlSize next + 1

def expandedSequenceLabels (N : ℕ) (next : Code) :
    Sum (Fin (controlSize (expandCode N) + 1)) (Fin (controlSize next + 1)) ≃
      Fin (expandedSequenceMax N next + 1) :=
  finSumFinEquiv.trans (finCongr (by unfold expandedSequenceMax; omega))

def expandedSequenceTable (N : ℕ) (next : Code) :
    Bool → Turing.TM0.Machine (Option Bool) (Fin (expandedSequenceMax N next + 1)) :=
  relabelTable (expandedSequenceLabels N next) (sequenceCoinTable (table (expandCode N)) (table next))

def expandedSequenceAccept (N : ℕ) (next : Code) (q : Fin (expandedSequenceMax N next + 1)) : Bool :=
  sourcePhaseAccept (readout next) ((expandedSequenceLabels N next).symm q)

def expandThenCode (N : ℕ) (next : Code) : Code :=
  encodeMachine (expandedSequenceMax N next) (expandedSequenceTable N next) (expandedSequenceAccept N next)

def rawMajorityCode (code : Code) (r : ℕ) : Code :=
  expandThenCode (2 * r + 1) (encodedMajorityCode code r)

def expandThenWords (N : ℕ) (input : List Bool) (D : ℕ) :
    ((Fin (expandTime N input.length) → Bool) × Bool × (Fin D → Bool)) ≃
      (Fin (expandTime N input.length + (D + 1)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (consCoinWords D)).trans
    (appendCoinWords (expandTime N input.length) (D + 1))

def codeTabulate (n : ℕ) (row : ℕ → ℕ) : Code := (List.range n).map row

def codeEnumerate (Q : ℕ) (output : ℕ → Bool) (row : ℕ → ℕ) : Code :=
  Q :: (codeTabulate (Q + 1) (fun q => (output q).toNat) ++ codeTabulate (6 * (Q + 1)) row)

def bitMajorityOutputNat (N Q q : ℕ) : Bool :=
  let stride := (3 * (N + 2) + 1) * 3 ^ (N + 2)
  let wide := q % ((roundsControlMax N Q + 1) * stride) / stride
  decide (N / 2 < wide % ((N + 1) * (2 * Q + 11)) / (2 * Q + 11))

def rawMajorityOutputNat (code : Code) (r q : ℕ) : Bool :=
  let N := 2 * r + 1
  let Q := controlSize code
  let exp := expandControlMax N + 1
  let bit := bitSimControlMax N (roundsControlMax N Q) + 1
  let label := q % (exp + bit)
  if label < exp then false else bitMajorityOutputNat N Q ((label - exp) % bit)

def queueDigitNat (label i : ℕ) : ℕ := label / 3 ^ i % 3

def queueUpdateNat (label i digit : ℕ) : ℕ :=
  label - queueDigitNat label i * 3 ^ i + digit * 3 ^ i

def queuePushNat (N label digit : ℕ) : ℕ := label / 3 + digit * 3 ^ (N + 1)

def expandLabelNat (N phase first i fifo : ℕ) : ℕ :=
  (fifo + 3 ^ (N + 2) * i) + ((N + 3) * 3 ^ (N + 2)) * first +
    (2 * ((N + 3) * 3 ^ (N + 2))) * phase

def expandStepNat (N phase first i fifo s : ℕ) : ℕ :=
  let emit := fun phase first i fifo action => 5 * expandLabelNat N phase first i fifo + action + 1
  if phase = 0 then
    if s = 0 then 0 else emit 1 1 0 0 1
  else if phase = 1 then
    if i < N + 2 then emit 2 first i (queueUpdateNat fifo i s)
      (2 + if first = 1 ∧ i = N then 2 else 0) else 0
  else if phase = 2 then
    if i + 1 < N + 2 then emit 1 first (i + 1) fifo 1 else emit 3 first 0 fifo 1
  else if phase = 3 then
    if fifo = 0 ∧ s = 0 then emit 5 first 0 fifo 0
    else emit 4 first 0 (queuePushNat N fifo s) (2 + queueDigitNat fifo 0)
  else if phase = 4 then emit 3 first 0 fifo 1
  else if phase = 5 then
    if s = 0 then emit 6 0 0 fifo 1 else emit 5 first 0 fifo 0
  else if phase = 6 then
    if s = 0 then emit 7 0 0 fifo 0 else emit 1 0 0 0 1
  else if phase = 7 then emit 8 0 0 fifo 0
  else if phase = 8 then
    if s = 2 then emit 10 0 (N + 1) fifo 2 else emit 9 0 (N + 2) fifo 0
  else if phase = 9 then
    if 1 < i then emit 9 0 (i - 1) fifo 0 else emit 8 0 0 fifo 0
  else if phase = 10 then
    if 1 < i then emit 10 0 (i - 1) fifo 0 else emit 11 0 0 fifo 0
  else 0

def expandRowNat (N row : ℕ) : ℕ :=
  let label := row / 3 % (expandControlMax N + 1)
  let slots := 3 ^ (N + 2)
  let block := (N + 3) * slots
  let rest := label % (2 * block)
  expandStepNat N (label / (2 * block)) (rest / block)
    (rest % block / slots) (rest % block % slots) (row % 3)

def normalizeTransitionNat (Q record : ℕ) : ℕ :=
  if record = 0 then 0 else
    5 * ((record - 1) / 5 % (Q + 1)) + (record - 1) % 5 + 1

def sourceRowNat (code : Code) (coin : Bool) (q s : ℕ) : ℕ :=
  let Q := controlSize code
  normalizeTransitionNat Q
    (code.getD (1 + (Q + 1) + (coin.toNat * (Q + 1) + q % (Q + 1)) * 3 + s % 3) 0)

def expandThenOutputNat (N : ℕ) (next : Code) (q : ℕ) : Bool :=
  let exp := expandControlMax N + 1
  let sz := controlSize next + 1
  let label := q % (exp + sz)
  if label < exp then false else next.getD (1 + (label - exp) % sz) 0 % 2 == 1

def expandThenRowNat (N : ℕ) (next : Code) (row : ℕ) : ℕ :=
  let exp := expandControlMax N + 1
  let sz := controlSize next + 1
  let total := exp + sz
  let q := row / 3 % total
  let s := row % 3
  if q < exp then
    let record := expandRowNat N (3 * q + s)
    if record = 0 then 5 * exp + (2 + s) + 1 else record
  else
    let record := sourceRowNat next (decide (3 * total ≤ row)) (q - exp) s
    if record = 0 then 0 else 5 * exp + record

def canonicalBufferNat (N label : ℕ) : ℕ :=
  queueUpdateNat label (N + 1) (if queueDigitNat label (N + 1) = 2 then 2 else 0)

def bitSimLabelNat (N Q phase wide i buffer : ℕ) : ℕ :=
  buffer + 3 ^ (N + 2) * i + ((3 * (N + 2) + 1) * 3 ^ (N + 2)) * wide +
    ((Q + 1) * ((3 * (N + 2) + 1) * 3 ^ (N + 2))) * phase

def wideRecordStride (N : ℕ) : ℕ := 3 ^ (N + 2) + 2

def wideActionNat (N : ℕ) : Turing.TM0.Stmt (TrackCell N) → ℕ
  | .move .left => 0
  | .move .right => 1
  | .write v => 2 + (expandQueueLabels N (cellBuffer N v)).val

def wideRecordNat (N : ℕ) {Q : ℕ} :
    Option (Fin (Q + 1) × Turing.TM0.Stmt (TrackCell N)) → ℕ
  | none => 0
  | some (q, action) => wideRecordStride N * q.val + wideActionNat N action + 1

def bitSimStepNat (N Q phase wide i buffer symbol record : ℕ) : ℕ :=
  let L := N + 2
  let emit :=
      fun phase wide i buffer action => 5 * bitSimLabelNat N Q phase wide i buffer + action + 1
  if phase = 0 then
    if i < L then emit (if i + 1 < L then 0 else 1) wide
      (if i + 1 < L then i + 1 else L) (queueUpdateNat buffer i symbol) 1 else 0
  else if phase = 1 then
    if 0 < i then emit (if 1 < i then 1 else 2) wide (if 1 < i then i - 1 else 0) buffer 0 else 0
  else if phase = 2 then
    if record = 0 then 0 else
      let next := (record - 1) / wideRecordStride N
      let action := (record - 1) % wideRecordStride N
      if action = 0 then emit 3 next (N + 3) buffer (2 + symbol)
      else if action = 1 then emit 4 next (N + 3) buffer (2 + symbol)
      else emit 5 next 0 (action - 2) (2 + symbol)
  else if phase = 3 then
    if 0 < i then emit (if 1 < i then 3 else 6) wide
      (if 1 < i then i - 1 else 2 * L - 1) buffer 0 else 0
  else if phase = 4 then
    if 0 < i then emit (if 1 < i then 4 else 6) wide
      (if 1 < i then i - 1 else 2 * L - 1) buffer 1 else 0
  else if phase = 5 then
    if i < L then emit 7 wide i buffer (2 + queueDigitNat buffer i) else 0
  else if phase = 6 then
    if 0 < i then emit (if 1 < i then 6 else 0) wide
      (if 1 < i then i - 1 else 0) (if 1 < i then buffer else 0) (2 + symbol) else 0
  else if phase = 7 then
    if i + 1 < L then emit 5 wide (i + 1) buffer 1 else emit 8 wide L buffer 1
  else if phase = 8 then
    if 0 < i then emit (if 1 < i then 8 else 0) wide
      (if 1 < i then i - 1 else 0) (if 1 < i then buffer else 0) 0 else 0
  else 0

def wideTableNat (N Q : ℕ)
    (M : Bool → Turing.TM0.Machine (TrackCell N) (Fin (Q + 1)))
    (coin : Bool) (wide buffer : ℕ) : ℕ :=
  wideRecordNat N (M coin ⟨wide % (Q + 1), Nat.mod_lt _ (by omega)⟩
    (bufferCell N ((expandQueueLabels N).symm
      ⟨buffer % 3 ^ (N + 2), Nat.mod_lt _ (pow_pos (by decide) _)⟩)))

def bitSimRowNat (N Q : ℕ) (source : Bool → ℕ → ℕ → ℕ) (row : ℕ) : ℕ :=
  let label := row / 3 % (bitSimControlMax N Q + 1)
  let P := 3 ^ (N + 2)
  let stride := (3 * (N + 2) + 1) * P
  let full := (Q + 1) * stride
  let rest := label % full
  let wide := rest / stride
  let index := rest % stride / P
  let buffer := rest % stride % P
  bitSimStepNat N Q (label / full) wide index buffer (row % 3)
    (source (decide (3 * (bitSimControlMax N Q + 1) ≤ row)) wide buffer)

def trackWriteBufferNat (N j buffer input work home : ℕ) : ℕ :=
  queueUpdateNat (queueUpdateNat (queueUpdateNat buffer 0 input) (j + 1) work)
    (N + 1) home

def roundsLabelNat (N Q round count prog : ℕ) : ℕ :=
  prog + (2 * Q + 11) * count + ((N + 1) * (2 * Q + 11)) * round

def trackRoundRowNat (N j : ℕ) (code : Code) (coin : Bool) (prog buffer : ℕ) : ℕ :=
  let Q := controlSize code
  let buf := canonicalBufferNat N buffer
  let input := queueDigitNat buf 0
  let work := queueDigitNat buf (j + 1)
  let home := queueDigitNat buf (N + 1)
  let emit := fun target action => wideRecordStride N * target + action + 1
  let write := fun input work home => 2 + trackWriteBufferNat N j buf input work home
  let same := 2 + buf
  if prog = 0 then emit 1 (write input work 2)
  else if prog = 1 then if input = 0 then emit 3 same else emit 2 (write input input home)
  else if prog = 2 then emit 1 1
  else if prog = 3 then if home = 2 then emit 4 same else emit 3 0
  else if prog = 4 then emit 5 same
  else
    let h := prog - 5
    let base := 2 * (Q + 1)
    if h < base then
      let source := h / 2
      let side := h % 2
      let record := sourceRowNat code coin source work
      if record = 0 then
        let output := (code.getD (1 + source) 0 % 2 == 1).toNat
        emit (5 + (base + (output + 2 * side))) same
      else
        let next := (record - 1) / 5
        let action := (record - 1) % 5
        if action = 0 then emit (5 + ((if home = 2 then 1 else side) + 2 * next)) 0
        else if action = 1 then emit (5 + ((if home = 2 then 0 else side) + 2 * next)) 1
        else emit (5 + (side + 2 * next)) (write input (action - 2) home)
    else if home = 2 then 0
    else emit prog (if (h - base) / 2 = 1 then 1 else 0)

def prepareHomingOutputNat (Q prog : ℕ) : Bool :=
  decide (5 + 2 * (Q + 1) ≤ prog) && ((prog - (5 + 2 * (Q + 1))) % 2 == 1)

def roundsStepNat (N : ℕ) (code : Code) (coin : Bool) (round count prog buffer : ℕ) : ℕ :=
  let Q := controlSize code
  let emit := fun target action => wideRecordStride N * target + action + 1
  if round < N then
    let record := trackRoundRowNat N round code coin prog buffer
    if record = 0 then
      let nextCount := if prepareHomingOutputNat Q prog then min (count + 1) N else count
      emit (roundsLabelNat N Q (min (round + 1) N) nextCount 0) (2 + canonicalBufferNat N buffer)
    else
      emit (roundsLabelNat N Q round count ((record - 1) / wideRecordStride N))
        ((record - 1) % wideRecordStride N)
  else 0

def roundsRowNat (N : ℕ) (code : Code) (coin : Bool) (wide buffer : ℕ) : ℕ :=
  let Q := controlSize code
  let label := wide % (roundsControlMax N Q + 1)
  let size := 2 * Q + 11
  let rest := label % ((N + 1) * size)
  roundsStepNat N code coin (label / ((N + 1) * size)) (rest / size) (rest % size)
    (buffer % 3 ^ (N + 2))

def encodedMajorityOutputNat (code : Code) (r q : ℕ) : Bool :=
  let N := 2 * r + 1
  let Q := controlSize code
  bitMajorityOutputNat N Q (q % (bitSimControlMax N (roundsControlMax N Q) + 1))

def encodedMajorityRowNat (code : Code) (r row : ℕ) : ℕ :=
  let N := 2 * r + 1
  bitSimRowNat N (roundsControlMax N (controlSize code)) (roundsRowNat N code) row

end Qatlib.Concepts.ClassicalTape.TapeCompilation
