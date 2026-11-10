/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachine
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ClassicalTape.FairCoinTape
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.UniformBqp.Phi3Compile

open Matrix
open Qatlib
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.UniformBqp.Phi3Compile.StandardMachine

def selfCodeCell (b : Bool) : List Bool := [false, b]

def selfCodeWord (bs : List Bool) : List Bool :=
  bs.flatMap selfCodeCell ++ [true]

def natSelfCode (n : ℕ) : List Bool := selfCodeWord n.bits

def pairSelfCode (n t : ℕ) : List Bool := natSelfCode n ++ natSelfCode t

def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * bitsToNat bs + b.toNat

def parseSelfCodeWord : List Bool → Option (List Bool × List Bool)
  | true :: rest => some ([], rest)
  | false :: b :: rest => (parseSelfCodeWord rest).map fun p => (b :: p.1, p.2)
  | _ => none

theorem parseSelfCodeWord_selfCodeWord (bs : List Bool) (rest : List Bool) :
    parseSelfCodeWord (selfCodeWord bs ++ rest) = some (bs, rest) := by
  induction bs generalizing rest with
  | nil => rfl
  | cons b bs ih =>
      have hsplit : selfCodeWord (b :: bs) ++ rest
          = false :: b :: (selfCodeWord bs ++ rest) := by
        simp [selfCodeWord, selfCodeCell, List.flatMap_cons]
      rw [hsplit]
      simp only [parseSelfCodeWord, ih]
      rfl

theorem selfCodeWord_injective {bs bs' : List Bool}
    (h : selfCodeWord bs = selfCodeWord bs') : bs = bs' := by
  have e : parseSelfCodeWord (selfCodeWord bs ++ [])
      = parseSelfCodeWord (selfCodeWord bs' ++ []) := by rw [h]
  rw [parseSelfCodeWord_selfCodeWord bs [], parseSelfCodeWord_selfCodeWord bs' []] at e
  exact congrArg Prod.fst (Option.some.inj e)

theorem bitsToNat_bits_aux : ∀ (k n : ℕ), n < k → bitsToNat n.bits = n := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
      intro n h
      rcases n with _ | m
      · rfl
      · rcases Nat.even_or_odd (m + 1) with he | ho
        · obtain ⟨r, hr⟩ := he
          have hr0 : r ≠ 0 := by omega
          rw [show m + 1 = 2 * r from by omega, Nat.bit0_bits r hr0, bitsToNat,
            ih r (by omega)]
          rfl
        · obtain ⟨r, hr⟩ := ho
          rw [show m + 1 = 2 * r + 1 from by omega, Nat.bit1_bits r, bitsToNat,
            ih r (by omega)]
          rfl

theorem bitsToNat_bits (n : ℕ) : bitsToNat n.bits = n :=
  bitsToNat_bits_aux (n + 1) n (Nat.lt_succ_self n)

theorem natSelfCode_injective {n n' : ℕ} (h : natSelfCode n = natSelfCode n') : n = n' := by
  have e : parseSelfCodeWord (natSelfCode n ++ [])
      = parseSelfCodeWord (natSelfCode n' ++ []) := by rw [h]
  simp only [natSelfCode] at e
  rw [parseSelfCodeWord_selfCodeWord n.bits [], parseSelfCodeWord_selfCodeWord n'.bits []] at e
  have hb : n.bits = n'.bits := congrArg Prod.fst (Option.some.inj e)
  have h2 := congrArg bitsToNat hb
  rwa [bitsToNat_bits, bitsToNat_bits] at h2

def pairParse (e : List Bool) : Option ((List Bool × List Bool) × List Bool) :=
  (parseSelfCodeWord e).bind fun p =>
    (parseSelfCodeWord p.2).map fun p' => ((p.1, p'.1), p'.2)

def natSelfParse (e : List Bool) : Option (ℕ × List Bool) :=
  (parseSelfCodeWord e).map fun p => (bitsToNat p.1, p.2)

theorem natSelfParse_natSelfCode (n : ℕ) (rest : List Bool) :
    natSelfParse (natSelfCode n ++ rest) = some (n, rest) := by
  have h := parseSelfCodeWord_selfCodeWord n.bits rest
  simp only [natSelfParse, natSelfCode, h, Option.map_some, bitsToNat_bits]

def natSelfCodesParse : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, e => some ([], e)
  | k + 1, e =>
      (natSelfParse e).bind fun p =>
        (natSelfCodesParse k p.2).map fun q => (p.1 :: q.1, q.2)

def natSelfCodesCode (ns : List ℕ) : List Bool :=
  natSelfCode ns.length ++ ns.flatMap natSelfCode

theorem natSelfCodesParse_flatMap (ns : List ℕ) (rest : List Bool) :
    natSelfCodesParse ns.length ((ns.flatMap natSelfCode) ++ rest) = some (ns, rest) := by
  induction ns generalizing rest with
  | nil => rfl
  | cons n ns ih =>
      have hsplit : (n :: ns).flatMap natSelfCode ++ rest
          = natSelfCode n ++ ((ns.flatMap natSelfCode) ++ rest) := by
        rw [List.flatMap_cons, List.append_assoc]
      have hseed : (n :: ns).length = ns.length + 1 := by simp
      rw [hseed, hsplit]
      simp only [natSelfCodesParse, natSelfParse_natSelfCode n _, ih, Option.bind_some,
        Option.map_some]

def natListSelfParse (e : List Bool) : Option (List ℕ × List Bool) :=
  (natSelfParse e).bind fun p => (natSelfCodesParse p.1 p.2).map fun q => (q.1, q.2)

theorem natListSelfParse_natSelfCodesCode (ns : List ℕ) (rest : List Bool) :
    natListSelfParse (natSelfCodesCode ns ++ rest) = some (ns, rest) := by
  simp only [natListSelfParse, natSelfCodesCode, List.append_assoc,
    natSelfParse_natSelfCode, natSelfCodesParse_flatMap ns, Option.bind_some,
    Option.map_some]

theorem natSelfCodesCode_injective {ns ns' : List ℕ}
    (h : natSelfCodesCode ns = natSelfCodesCode ns') : ns = ns' := by
  have e : natListSelfParse (natSelfCodesCode ns ++ [])
      = natListSelfParse (natSelfCodesCode ns' ++ []) := by rw [h]
  rw [natListSelfParse_natSelfCodesCode ns [], natListSelfParse_natSelfCodesCode ns' []] at e
  exact congrArg Prod.fst (Option.some.inj e)

theorem pairParse_pairSelfCode (n t : ℕ) :
    pairParse (pairSelfCode n t) = some ((n.bits, t.bits), []) := by
  have h1 : parseSelfCodeWord (natSelfCode n ++ natSelfCode t)
      = some (n.bits, natSelfCode t) :=
    parseSelfCodeWord_selfCodeWord n.bits (natSelfCode t)
  have h2 : parseSelfCodeWord (natSelfCode t ++ [])
      = some (t.bits, []) :=
    parseSelfCodeWord_selfCodeWord t.bits []
  simp only [List.append_nil] at h2
  simp only [pairParse, pairSelfCode, h1, Option.bind_some, h2, Option.map_some]

theorem pairSelfCode_injective {n t n' t' : ℕ}
    (h : pairSelfCode n t = pairSelfCode n' t') : n = n' ∧ t = t' := by
  have hp : pairParse (pairSelfCode n t) = pairParse (pairSelfCode n' t') := by rw [h]
  rw [pairParse_pairSelfCode n t, pairParse_pairSelfCode n' t'] at hp
  have hp1 : (n.bits, t.bits) = (n'.bits, t'.bits) := congrArg Prod.fst (Option.some.inj hp)
  have hb1 : n.bits = n'.bits := congrArg Prod.fst hp1
  have hb2 : t.bits = t'.bits := congrArg Prod.snd hp1
  have e1 := congrArg bitsToNat hb1
  have e2 := congrArg bitsToNat hb2
  rw [bitsToNat_bits, bitsToNat_bits] at e1
  rw [bitsToNat_bits, bitsToNat_bits] at e2
  exact ⟨e1, e2⟩

theorem frozenCollisionPair_separated : pairSelfCode 1 21 ≠ pairSelfCode 5 5 := by
  intro h
  obtain ⟨e, -⟩ := pairSelfCode_injective h
  omega

def selfCodeParserMachine : Turing.TM0.Machine (Option Bool) (Fin 2) :=
  fun l γ =>
    if l = 0 then
      match γ with
      | some false => some (1, Turing.TM0.Stmt.move Turing.Dir.right)
      | _ => none
    else
      match γ with
      | some _ => some (0, Turing.TM0.Stmt.move Turing.Dir.right)
      | none => none

@[simp] theorem parserMachine_zero_false :
    selfCodeParserMachine 0 (some false)
      = some (1, Turing.TM0.Stmt.move Turing.Dir.right) := rfl

@[simp] theorem parserMachine_zero_true : selfCodeParserMachine 0 (some true) = none := rfl

@[simp] theorem parserMachine_one_some (b : Bool) :
    selfCodeParserMachine 1 (some b)
      = some (0, Turing.TM0.Stmt.move Turing.Dir.right) := rfl

theorem haltRun_step_live {q : ℕ} (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1)))
    {s : ℕ} {c c' : Turing.TM0.Cfg (Option Bool) (Fin (q + 1))}
    (h : Turing.TM0.step M c = some c') :
    TM0HaltRun M (s + 1) c = TM0HaltRun M s c' := by
  have heq : TM0HaltRun M (s + 1) c
      = match Turing.TM0.step M c with
        | none => some c
        | some c'' => TM0HaltRun M s c'' := rfl
  rw [heq, h]

theorem tape_mk₂_move_right_pair {Γ : Type} [Inhabited Γ]
    (L : List Γ) (a₀ a₁ : Γ) (r : List Γ) :
    ((Turing.Tape.mk₂ L (a₀ :: a₁ :: r)).move Turing.Dir.right).move Turing.Dir.right
      = Turing.Tape.mk₂ (a₁ :: a₀ :: L) r := by
  simp [Turing.Tape.mk₂, Turing.Tape.mk', Turing.Tape.move, Turing.ListBlank.cons_mk]

theorem tape_move_right_right₀_nth_succ {Γ : Type} [Inhabited Γ]
    (T : Turing.Tape Γ) (m : ℕ) :
    (T.move Turing.Dir.right).right₀.nth m = T.right₀.nth (m + 1) := by
  rw [Turing.Tape.right₀_nth, Turing.Tape.right₀_nth, Turing.Tape.move_right_nth]
  push_cast
  rfl

theorem tape_iterate_move_right_right₀ : ∀ {Γ : Type} [Inhabited Γ]
    (T : Turing.Tape Γ) (j i : ℕ),
    ((Turing.Tape.move Turing.Dir.right)^[j] T).right₀.nth i
      = T.right₀.nth (j + i) := by
  intro Γ _ T j
  induction j generalizing T with
  | zero => intro i; simp
  | succ j ih =>
      intro i
      rw [Function.iterate_succ_apply, ih (T.move Turing.Dir.right) i,
        tape_move_right_right₀_nth_succ]
      have hidx : j + i + 1 = j + 1 + i := by omega
      rw [hidx]

theorem tape_mk₁_right₀_nth {Γ : Type} [Inhabited Γ] (l : List Γ) (n : ℕ) :
    (Turing.Tape.mk₁ l).right₀.nth n = l.getI n := by
  simp [Turing.Tape.mk₁, Turing.Tape.mk₂]

theorem parser_run (bs : List Bool) :
    ∀ (L : List (Option Bool)) (rest : List Bool),
      TM0HaltRun selfCodeParserMachine (2 * bs.length)
          ⟨0, Turing.Tape.mk₂ L ((selfCodeWord bs ++ rest).map some)⟩ =
        some ⟨0, (Turing.Tape.move Turing.Dir.right)^[2 * bs.length]
          (Turing.Tape.mk₂ L ((selfCodeWord bs ++ rest).map some))⟩ := by
  induction bs with
  | nil =>
      intro L rest
      have hhead : (Turing.Tape.mk₂ L ((selfCodeWord [] ++ rest).map some)).head
          = some true := by
        simp [selfCodeWord, Turing.Tape.mk₂, Turing.Tape.mk']
      have hnone : Turing.TM0.step selfCodeParserMachine
          ⟨0, Turing.Tape.mk₂ L ((selfCodeWord [] ++ rest).map some)⟩ = none := by
        rw [TM0_step_eq_none]
        show selfCodeParserMachine 0
          (Turing.Tape.mk₂ L ((selfCodeWord [] ++ rest).map some)).head = none
        rw [hhead]
        rfl
      have hfuel : TM0HaltRun selfCodeParserMachine (2 * ([] : List Bool).length)
          ⟨0, Turing.Tape.mk₂ L ((selfCodeWord [] ++ rest).map some)⟩ =
          some ⟨0, Turing.Tape.mk₂ L ((selfCodeWord [] ++ rest).map some)⟩ := by
        show TM0HaltRun selfCodeParserMachine 0
            ⟨0, Turing.Tape.mk₂ L ((selfCodeWord [] ++ rest).map some)⟩ = _
        rw [TM0HaltRun, hnone]
        simp
      rw [hfuel]
      simp
  | cons b bs ih =>
      intro L rest
      have hsplit : (selfCodeWord (b :: bs) ++ rest).map some
          = some false :: some b :: ((selfCodeWord bs ++ rest).map some) := by
        simp [selfCodeWord, selfCodeCell, List.flatMap_cons]
      have htab1 : selfCodeParserMachine 0
          (Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).head
            = some (1, Turing.TM0.Stmt.move Turing.Dir.right) := by
        show selfCodeParserMachine 0 (some false) = _
        rfl
      have hs1 : Turing.TM0.step selfCodeParserMachine
          ⟨0, Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)⟩ =
          some ⟨1, (Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).move
            Turing.Dir.right⟩ := by
        rw [TM0_step_eq_some selfCodeParserMachine _
          1 (Turing.TM0.Stmt.move Turing.Dir.right) htab1]
        try rfl
      have htab2 : selfCodeParserMachine 1
          ((Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).move
            Turing.Dir.right).head
            = some (0, Turing.TM0.Stmt.move Turing.Dir.right) := by
        show selfCodeParserMachine 1 (some b) = _
        rfl
      have hs2 : Turing.TM0.step selfCodeParserMachine
          ⟨1, (Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).move
            Turing.Dir.right⟩ =
          some ⟨0, ((Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).move
            Turing.Dir.right).move Turing.Dir.right⟩ := by
        rw [TM0_step_eq_some selfCodeParserMachine _
          0 (Turing.TM0.Stmt.move Turing.Dir.right) htab2]
        try rfl
      have hfuel : TM0HaltRun selfCodeParserMachine (2 * (b :: bs).length)
          ⟨0, Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)⟩ =
          TM0HaltRun selfCodeParserMachine (2 * bs.length)
            ⟨0, ((Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).move
              Turing.Dir.right).move Turing.Dir.right⟩ := by
        have h2 : 2 * (b :: bs).length = 2 * bs.length + 1 + 1 := by
          simp only [List.length_cons, Nat.mul_succ]
          try omega
        rw [h2, haltRun_step_live _ hs1, haltRun_step_live _ hs2]
      rw [hfuel]
      have htape : ((Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)).move
            Turing.Dir.right).move Turing.Dir.right =
          Turing.Tape.mk₂ (some b :: some false :: L)
            ((selfCodeWord bs ++ rest).map some) := by
        rw [hsplit]
        exact tape_mk₂_move_right_pair L (some false) (some b) _
      rw [htape]
      have hiter : (Turing.Tape.move Turing.Dir.right)^[2 * (b :: bs).length]
          (Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)) =
          (Turing.Tape.move Turing.Dir.right)^[2 * bs.length]
            (Turing.Tape.mk₂ (some b :: some false :: L)
              ((selfCodeWord bs ++ rest).map some)) := by
        have h2 : 2 * (b :: bs).length = 2 * bs.length + 2 := by
          simp only [List.length_cons, Nat.mul_succ]
          try omega
        have hpair : (Turing.Tape.move Turing.Dir.right)^[2]
            (Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)) =
            Turing.Tape.mk₂ (some b :: some false :: L)
              ((selfCodeWord bs ++ rest).map some) := by
          show (Turing.Tape.move Turing.Dir.right
              (Turing.Tape.move Turing.Dir.right
                (Turing.Tape.mk₂ L ((selfCodeWord (b :: bs) ++ rest).map some)))) = _
          rw [hsplit]
          exact tape_mk₂_move_right_pair L (some false) (some b) _
        rw [h2, Function.iterate_add_apply, hpair]
      rw [hiter]
      exact ih (some b :: some false :: L) rest

theorem selfCodeCell_flatMap_length (bs : List Bool) :
    (bs.flatMap selfCodeCell).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs h =>
      have h2 : (selfCodeCell b).length = 2 := rfl
      rw [List.flatMap_cons, List.length_append, h, h2]
      simp only [List.length_cons]
      omega

theorem selfCodeWord_length (bs : List Bool) :
    (selfCodeWord bs).length = 2 * bs.length + 1 := by
  rw [selfCodeWord, List.length_append, selfCodeCell_flatMap_length]
  have h1 : (List.length [true] : ℕ) = 1 := rfl
  omega

theorem getI_map_some_append : ∀ (A B : List Bool) (i : ℕ),
    ((A ++ B).map some).getI (A.length + i) = (B.map some).getI i := by
  intro A
  induction A with
  | nil => intro B i; simp
  | cons a A ih =>
      intro B i
      have hidx : (a :: A).length + i = (A.length + i) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hidx]
      show ((some a) :: ((A ++ B).map some)).getD ((A.length + i) + 1) default
          = (B.map some).getI i
      rw [List.getD_cons_succ]
      exact ih B i

theorem selfCodeWord_append (bs : List Bool) (rest : List Bool) :
    selfCodeWord bs ++ rest
      = (bs.flatMap selfCodeCell) ++ (true :: rest) := by
  simp [selfCodeWord]

theorem parser_emits (bs rest : List Bool) :
    TM0EmitsPoly selfCodeParserMachine 2 1 (selfCodeWord bs ++ rest)
      (true :: rest) := by
  refine ⟨2 * bs.length, ⟨0, (Turing.Tape.move Turing.Dir.right)^[2 * bs.length]
      (Turing.Tape.mk₁ ((selfCodeWord bs ++ rest).map some))⟩, ?_,
    parser_run bs [] rest, ?_, ?_⟩
  · have hlen : (selfCodeWord bs ++ rest).length
        = 2 * bs.length + 1 + rest.length := by
      rw [List.length_append, selfCodeWord_length]
    simp only [Nat.pow_one]
    omega
  · rw [TM0_step_eq_none]
    have hhead : ((Turing.Tape.move Turing.Dir.right)^[2 * bs.length]
        (Turing.Tape.mk₁ ((selfCodeWord bs ++ rest).map some))).head = some true := by
      rw [Turing.Tape.move_right_n_head]
      have hmk : (Turing.Tape.mk₁ ((selfCodeWord bs ++ rest).map some)).nth
          ((2 * bs.length : ℕ) : ℤ)
          = ((selfCodeWord bs ++ rest).map some).getI (2 * bs.length) := by
        rw [← Turing.Tape.right₀_nth]
        exact tape_mk₁_right₀_nth _ _
      have happ := getI_map_some_append (bs.flatMap selfCodeCell) (true :: rest) 0
      rw [selfCodeCell_flatMap_length, Nat.add_zero] at happ
      rw [hmk, selfCodeWord_append, happ]
      rfl
    show selfCodeParserMachine 0
        ((Turing.Tape.move Turing.Dir.right)^[2 * bs.length]
          (Turing.Tape.mk₁ ((selfCodeWord bs ++ rest).map some))).head = none
    rw [hhead]
    rfl
  · intro i
    have hnth : ((Turing.Tape.move Turing.Dir.right)^[2 * bs.length]
        (Turing.Tape.mk₁ ((selfCodeWord bs ++ rest).map some))).right₀.nth i =
        ((selfCodeWord bs ++ rest).map some).getI (2 * bs.length + i) := by
      rw [tape_iterate_move_right_right₀, tape_mk₁_right₀_nth]
    have happ := getI_map_some_append (bs.flatMap selfCodeCell) (true :: rest) i
    rw [selfCodeCell_flatMap_length] at happ
    rw [hnth, selfCodeWord_append, happ]
    rfl

theorem parser_emits_pair (n t : ℕ) :
    TM0EmitsPoly selfCodeParserMachine 2 1 (pairSelfCode n t)
      (true :: natSelfCode t) := by
  have h : pairSelfCode n t = selfCodeWord n.bits ++ natSelfCode t := rfl
  rw [h]
  exact parser_emits n.bits (natSelfCode t)

def gateDescWord {w : ℕ} (gs : List (Phi3Gate w)) : List Bool :=
  natSelfCode (GateCount (phi3Compile gs))

def phi3WireSkeleton {w : ℕ} (gs : List (Phi3Gate w)) : List ℕ :=
  gs.flatMap fun g => [(g.wires 0).val, (g.wires 1).val, (g.wires 2).val]

def phi3SkeletonCode {w : ℕ} (gs : List (Phi3Gate w)) : List Bool :=
  natSelfCodesCode (phi3WireSkeleton gs)

theorem natListSelfParse_phi3SkeletonCode {w : ℕ} (gs : List (Phi3Gate w))
    (rest : List Bool) :
    natListSelfParse (phi3SkeletonCode gs ++ rest)
      = some (phi3WireSkeleton gs, rest) :=
  natListSelfParse_natSelfCodesCode _ rest

theorem phi3WireSkeleton_length {w : ℕ} (gs : List (Phi3Gate w)) :
    (phi3WireSkeleton gs).length = 3 * gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      show ([(g.wires 0).val, (g.wires 1).val, (g.wires 2).val] ++ phi3WireSkeleton gs).length
          = 3 * (gs.length + 1)
      have h3len : ([(g.wires 0).val, (g.wires 1).val, (g.wires 2).val] : List ℕ).length = 3 :=
        rfl
      rw [List.length_append, h3len, ih]
      omega

theorem phi3SkeletonCode_determined {w : ℕ} {gs gs' : List (Phi3Gate w)}
    (h : phi3SkeletonCode gs = phi3SkeletonCode gs') :
    gs.length = gs'.length ∧ phi3WireSkeleton gs = phi3WireSkeleton gs' := by
  have hs : natSelfCodesCode (phi3WireSkeleton gs)
      = natSelfCodesCode (phi3WireSkeleton gs') := h
  have hsk := natSelfCodesCode_injective hs
  have hlen := phi3WireSkeleton_length gs
  have hlen' := phi3WireSkeleton_length gs'
  rw [hsk] at hlen
  have h3 : 3 * gs.length = 3 * gs'.length := by omega
  exact ⟨Nat.mul_left_cancel (by omega) h3, hsk⟩

theorem desc_determined_by_code (desc : ℕ → ℕ → List Bool)
    (n t n' t' : ℕ) (h : pairSelfCode n t = pairSelfCode n' t') :
    desc n t = desc n' t' := by
  obtain ⟨e1, e2⟩ := pairSelfCode_injective h
  subst e1
  subst e2
  rfl

theorem generalPhi3_cellTable_gateDesc {Q A : Type} [Fintype Q] [DecidableEq Q]
    [Fintype A] [DecidableEq A] (M : GeneralNativeMachine Q A) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
      GateCount (phi3Compile gs) = gs.length ∧
      gateDescWord gs = natSelfCode gs.length ∧
      gs.length ≤ generalWindowSize n t *
        ((2 * generalWindowSize n t - 1) * phi3PaddingBudget (3 * cellBasisWidth Q A) +
          (2 * generalWindowSize n t + 1) * phi3PaddingBudget (cellBasisWidth Q A)) ∧
      (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
        (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
            (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
          (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
          (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A) (generalBasisCode Q A)
            (windowEncode c)) =
        ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
          Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c) := by
  obtain ⟨gs, -, -, hcount, hlen, hsim⟩ := generalPhi3_cellTable M n t hn ht
  refine ⟨gs, hcount, ?_, hlen, ?_⟩
  · rw [gateDescWord, hcount]
  · intro x c
    rw [(hsim x c).2.2.1]
    exact (qtmPhi3State_apply_basis (generalWindowSize n t) (cellBasisWidth Q A)
      (generalBasisCode Q A) (generalBasisCode_injective Q A) _ (windowEncode c)).trans
      (qtmPhi3_windowEmbed_image _ c)

theorem frontier1 {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (M : GeneralNativeMachine Q A) :
    (∀ n t n' t' : ℕ, pairSelfCode n t = pairSelfCode n' t' → n = n' ∧ t = t') ∧
    (∀ n t : ℕ, pairParse (pairSelfCode n t) = some ((n.bits, t.bits), [])) ∧
    (∀ n t : ℕ,
      TM0EmitsPoly selfCodeParserMachine 2 1 (pairSelfCode n t)
        (true :: natSelfCode t)) ∧
    (∀ (desc : ℕ → ℕ → List Bool) (n t n' t' : ℕ),
      pairSelfCode n t = pairSelfCode n' t' → desc n t = desc n' t') ∧
    (∀ (w : ℕ) (gs gs' : List (Phi3Gate w)),
      phi3SkeletonCode gs = phi3SkeletonCode gs' →
        gs.length = gs'.length ∧ phi3WireSkeleton gs = phi3WireSkeleton gs') ∧
    (∀ n t : ℕ, 0 < n → 0 < t →
      ∃ gs : List (Phi3Gate (generalRegisterWidth Q A n t)),
        GateCount (phi3Compile gs) = gs.length ∧
        gateDescWord gs = natSelfCode gs.length ∧
        gs.length ≤ generalWindowSize n t *
          ((2 * generalWindowSize n t - 1) * phi3PaddingBudget (3 * cellBasisWidth Q A) +
            (2 * generalWindowSize n t + 1) * phi3PaddingBudget (cellBasisWidth Q A)) ∧
        (∀ (x : Fin n → A) (c : WindowCfg (generalWindowSize n t) Q A),
          (Run (1 : Matrix (Reg (generalRegisterWidth Q A n t))
              (Reg (generalRegisterWidth Q A n t)) ℂ) (phi3Compile gs)
            (qtmPhi3State (generalWindowSize n t) (cellBasisWidth Q A)
              (generalBasisCode Q A)
              (Qatlib.Foundations.PureStateMath.Ket (windowEncode (initWindowCfg M.localQTM n x)))))
            (qtmPhi3Basis (generalWindowSize n t) (cellBasisWidth Q A)
              (generalBasisCode Q A) (windowEncode c)) =
          ((windowStep M.localQTM) ^ generalWindowSize n t *ᵥ
            Qatlib.Foundations.PureStateMath.Ket (initWindowCfg M.localQTM n x)) c)) := by
  exact ⟨fun n t n' t' h => pairSelfCode_injective h, pairParse_pairSelfCode, parser_emits_pair,
    desc_determined_by_code, fun _w _gs _gs' h => phi3SkeletonCode_determined h,
    generalPhi3_cellTable_gateDesc M⟩

end Qatlib.Concepts.UniformBqp.Phi3Compile
