/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs

set_option autoImplicit false

noncomputable section

open Turing

def natBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def intBits (n : ℤ) : List Bool :=
  decide (n < 0) :: natBits n.natAbs

def ratBits (q : ℚ) : List Bool :=
  intBits q.num ++ natBits q.den

def tapeAt (l : List Bool) (i : ℕ) : Option Bool :=
  (l.map some).getD i none

def RatOnTape {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ) (q : ℚ) : Prop :=
  ∀ i : ℕ, cfg.Tape.right₀.nth i = tapeAt (ratBits q) i

def RatsOnTape {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ)
    (qs : List ℚ) : Prop :=
  ∀ i : ℕ, cfg.Tape.right₀.nth i = tapeAt (qs.flatMap ratBits) i

def NatsOnTape {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ)
    (ns : List ℕ) : Prop :=
  ∀ i : ℕ, cfg.Tape.right₀.nth i = tapeAt (ns.flatMap natBits) i

def blankCells (xs : List (Option Bool)) : ℕ :=
  (xs.filter (fun x => x ≠ none)).length

theorem filter_ne_none_replicate (n : ℕ) :
    (List.replicate n (default : Option Bool)).filter (fun x => x ≠ none) = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx
  obtain ⟨_, rfl⟩ := List.mem_replicate.1 hx
  show ¬(decide ((default : Option Bool) ≠ none) = true)
  decide

def blankUsedCells (l : Turing.ListBlank (Option Bool)) : ℕ :=
  Turing.ListBlank.liftOn l blankCells (fun l₁ l₂ h => by
    obtain ⟨n, rfl⟩ := h
    show blankCells l₁ = blankCells (l₁ ++ List.replicate n default)
    unfold blankCells
    rw [List.filter_append, filter_ne_none_replicate, List.append_nil])

def tapeSpace (T : Turing.Tape (Option Bool)) : ℕ :=
  blankUsedCells T.left + 1 + blankUsedCells T.right

def cfgSpace {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ) : ℕ :=
  tapeSpace cfg.Tape

def peakSpaceAfter {Λ : Type} [Inhabited Λ] (M : Turing.TM0.Machine (Option Bool) Λ)
    (input : List (Option Bool)) (t : ℕ) : ℕ :=
  (List.range (t + 1)).foldl
    (fun acc s => max acc ((BitMachineAfter M input s).elim 0 cfgSpace)) 0

def dyadicVal (k : ℕ) (m : ℤ) : ℝ :=
  (m : ℝ) / (2 ^ k : ℝ)

def RoundedDyadic (k : ℕ) (m : ℤ) (x : ℝ) : Prop :=
  |dyadicVal k m - x| ≤ ((2 : ℝ)⁻¹) ^ k

def IntervalCert (k : ℕ) (lo hi : ℚ) (x : ℝ) : Prop :=
  (lo : ℝ) ≤ x ∧ x ≤ hi ∧ (hi - lo : ℝ) ≤ 2 * ((2 : ℝ)⁻¹) ^ k

structure FiniteRealInput where

  states : ℕ

  approx : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

  size : ℕ

def CertifiesApproximation (d : FiniteRealInput) (x : ℝ) : Prop :=
  ∀ k : ℕ, ∃ t q cfg,
    BitMachineAfter d.approx ((natBits k).map some) t = some cfg ∧
    Turing.TM0.step d.approx cfg = none ∧
    RatOnTape cfg q ∧
    |(q : ℝ) - x| ≤ ((2 : ℝ)⁻¹) ^ k

def ComputablyApproximable (x : ℝ) : Prop :=
  ∃ d : FiniteRealInput, CertifiesApproximation d x

def IsFiniteReal (x : ℝ) : Prop :=
  ComputablyApproximable x

structure FiniteComplexInput where
  re : FiniteRealInput
  im : FiniteRealInput

def CertifiesComplexApproximation (d : FiniteComplexInput) (z : ℂ) : Prop :=
  CertifiesApproximation d.re z.re ∧ CertifiesApproximation d.im z.im

def IsFiniteComplex (z : ℂ) : Prop :=
  ComputablyApproximable z.re ∧ ComputablyApproximable z.im

def FiniteInputBoundary : Prop :=
  (∀ x : ℝ, IsFiniteReal x ↔ ComputablyApproximable x) ∧
  (∀ z : ℂ, IsFiniteComplex z ↔ (ComputablyApproximable z.re ∧ ComputablyApproximable z.im)) ∧
  (∀ x : ℝ, ¬ ComputablyApproximable x → ¬ IsFiniteReal x)

inductive ArithOp where
  | add
  | mul
  | div
  | sqrt
  | sin
  | cos
  | arctan
  | log
  deriving DecidableEq, Repr

def ArithOp.code : ArithOp → ℕ
  | .add => 0
  | .mul => 1
  | .div => 2
  | .sqrt => 3
  | .sin => 4
  | .cos => 5
  | .arctan => 6
  | .log => 7

noncomputable def ArithOpValue (op : ArithOp) (x y : ℝ) : ℝ :=
  match op with
  | .add => x + y
  | .mul => x * y
  | .div => x / y
  | .sqrt => Real.sqrt x
  | .sin => Real.sin x
  | .cos => Real.cos x
  | .arctan => Real.arctan x
  | .log => Real.log x

def OpPremise (op : ArithOp) (x y : ℝ) (gap : ℕ) : Prop :=
  match op with
  | .add | .mul | .sin | .cos | .arctan => True
  | .div => ((2 : ℝ)⁻¹) ^ gap ≤ |y|
  | .sqrt => 0 ≤ x
  | .log => ((2 : ℝ)⁻¹) ^ gap ≤ x

def PremisesExplicit : Prop :=
  ∀ (op : ArithOp) (x y : ℝ) (gap : ℕ),
    OpPremise op x y gap ↔
      match op with
      | .add | .mul | .sin | .cos | .arctan => True
      | .div => ((2 : ℝ)⁻¹) ^ gap ≤ |y|
      | .sqrt => 0 ≤ x
      | .log => ((2 : ℝ)⁻¹) ^ gap ≤ x

def ArithOpInput (op : ArithOp) (k gap : ℕ) (r1 r2 : ℚ) : List (Option Bool) :=
  ((natBits op.code ++ natBits k ++ natBits gap ++ ratBits r1 ++ ratBits r2).map some)

structure ArithBackend where
  states : ℕ
  run : ArithOp → Turing.TM0.Machine (Option Bool) (Fin (states + 1))

def BackendSound (be : ArithBackend) (C D : ℕ) : Prop :=
  ∀ (op : ArithOp) (x y : ℝ) (gap k : ℕ) (r1 r2 : ℚ),
    OpPremise op x y gap →
    |(r1 : ℝ) - x| ≤ ((2 : ℝ)⁻¹) ^ (k + 1) →
    |(r2 : ℝ) - y| ≤ ((2 : ℝ)⁻¹) ^ (k + 1) →
    let input := ArithOpInput op k gap r1 r2
    ∃ (t : ℕ) (m : ℤ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (be.states + 1))),
      BitMachineAfter (be.run op) input t = some cfg ∧
      Turing.TM0.step (be.run op) cfg = none ∧
      RatOnTape cfg ((m : ℚ) / (2 ^ k : ℚ)) ∧
      RoundedDyadic k m (ArithOpValue op x y) ∧
      IntervalCert k ((m : ℚ) / (2 ^ k : ℚ) - (2 ^ k : ℚ)⁻¹)
        ((m : ℚ) / (2 ^ k : ℚ) + (2 ^ k : ℚ)⁻¹) (ArithOpValue op x y) ∧
      t ≤ C * (1 + input.length + gap + k) ^ D + C ∧
      peakSpaceAfter (be.run op) input t ≤ C * (1 + input.length + gap + k) ^ D + C

inductive NumericalKind where
  | phase
  | rotation
  | prepareCoeff
  | spectralGap
  deriving DecidableEq, Repr

def NumericalKind.code : NumericalKind → ℕ
  | .phase => 0
  | .rotation => 1
  | .prepareCoeff => 2
  | .spectralGap => 3

structure NumericalParam where
  kind : NumericalKind
  name : FiniteRealInput
  gap : ℕ

def NumericalKindsComplete : Prop :=
  ∀ p : NumericalParam,
    p.kind = NumericalKind.phase ∨ p.kind = NumericalKind.rotation ∨
    p.kind = NumericalKind.prepareCoeff ∨ p.kind = NumericalKind.spectralGap

structure SameWordInstance where
  L : ℕ
  amplification : Fin L → ℝ
  params : Fin L → List NumericalParam
  ε : ℝ

def inputReadCost (inst : SameWordInstance) : ℕ :=
  (Finset.univ.sum fun i : Fin inst.L =>
    (inst.params i).foldl (fun acc p => acc + p.name.size + p.gap) 0)

def accumulatedWordError (amps : List ℝ) (deltas : List ℝ) : ℝ :=
  (amps.zipWith (· * ·) deltas).sum

def amplifiedWordError (inst : SameWordInstance) (k : ℕ) : ℝ :=
  accumulatedWordError (List.ofFn inst.amplification)
    (List.replicate inst.L (((2 : ℝ)⁻¹) ^ k))

structure BackendParams where
  totalBits : ℕ
  length : ℕ
  ampSum : ℝ
  gap : ℕ
  ε : ℝ

noncomputable def paramsOf (inst : SameWordInstance) : BackendParams where
  totalBits := inputReadCost inst
  length := inst.L
  ampSum := (Finset.univ.sum fun i : Fin inst.L => inst.amplification i)
  gap := (Finset.univ.sup fun i : Fin inst.L =>
    ((inst.params i).foldl (fun acc p => max acc p.gap) 0))
  ε := inst.ε

def PrecisionChoice : Type := BackendParams → ℕ

structure BackendRun where
  states : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

def paramBits (k : ℕ) (p : NumericalParam) : List Bool :=
  natBits p.kind.code ++ natBits p.name.size ++ natBits p.gap ++ natBits k

def backendInput (inst : SameWordInstance) (k : ℕ) : List (Option Bool) :=
  let paramWord := (List.ofFn fun i : Fin inst.L => (inst.params i).flatMap (paramBits k)).flatten
  ((natBits inst.L ++ natBits k ++ paramWord).map some)

def RunRealizes (r : BackendRun) (inst : SameWordInstance) (k : ℕ) : Prop :=
  ∀ (val : NumericalParam → ℝ),
    (∀ (i : Fin inst.L) (p : NumericalParam), p ∈ inst.params i →
      CertifiesApproximation p.name (val p)) →
    ∃ (t : ℕ) (qs : List ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine (backendInput inst k) t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatsOnTape cfg qs ∧
      List.Forall₂ (fun (q : ℚ) (p : NumericalParam) =>
        |(q : ℝ) - val p| ≤ ((2 : ℝ)⁻¹) ^ k)
        qs ((List.ofFn fun i : Fin inst.L => inst.params i).flatten)

def BackendCostOk (inst : SameWordInstance) (k t : ℕ) (C D : ℕ) : Prop :=
  inputReadCost inst ≤ t ∧
  t ≤ C * (1 + inputReadCost inst + inst.L + (paramsOf inst).gap + k) ^ D + C

def InputReadCostCharged : Prop :=
  ∀ (inst : SameWordInstance) (k t C D : ℕ),
    BackendCostOk inst k t C D → inputReadCost inst ≤ t

def NoExactRealOracle : Prop :=
  ∀ (inst : SameWordInstance) (i : Fin inst.L) (p : NumericalParam) (x : ℝ),
    p ∈ inst.params i → CertifiesApproximation p.name x → ComputablyApproximable x

def OffGridQPEConsumer (r : BackendRun) : Prop :=
  ∀ (M : ℕ) (_hM : 0 < M) (name : FiniteRealInput) (θ : ℝ) (k : ℕ) (amp : ℚ),
    CertifiesApproximation name θ →
    0 ≤ amp →
    ∃ (t : ℕ) (q : ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine
        ((natBits M ++ natBits k ++ ratBits amp ++ natBits name.size).map some) t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatOnTape cfg q ∧
      |(q : ℝ) - θ| ≤ 2 * Real.pi / (M : ℝ) + (amp : ℝ) * ((2 : ℝ)⁻¹) ^ k ∧
      name.size ≤ t ∧
      t ≤ 1 + name.size + M + k

def RationalHHLConsumer (r : BackendRun) : Prop :=
  ∀ (n gap k : ℕ) (entries : Fin n → ℚ) (prep : Fin n → ℚ) (κ : ℝ) (Δ : ℝ) (ε : ℝ),
    ((2 : ℝ)⁻¹) ^ gap ≤ Δ →
    κ = (2 : ℝ) ^ gap →
    0 < ε →
    ∃ (t : ℕ) (q : ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine
        ((natBits n ++ natBits gap ++ natBits k ++
          ((List.ofFn fun i : Fin n => ratBits (entries i) ++ ratBits (prep i))).flatten).map some)
          t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatOnTape cfg q ∧
      |(q : ℝ) - (∑ i : Fin n, (entries i : ℝ) * (prep i : ℝ))| ≤
        κ * (n * ((2 : ℝ)⁻¹) ^ k) + ε ∧
      (∑ i : Fin n, (ratBits (entries i) ++ ratBits (prep i)).length) ≤ t ∧
      t ≤ 1 + n * (k + gap) + gap + k

def RationalLCUConsumer (r : BackendRun) : Prop :=
  ∀ (m k : ℕ) (coef : Fin m → ℚ) (Λ : ℚ) (ε : ℝ),
    0 < (Λ : ℝ) →
    0 < ε →
    (∑ i : Fin m, |(coef i : ℝ)|) ≤ Λ →
    ∃ (t : ℕ) (q : ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine
        ((natBits m ++ natBits k ++ ratBits Λ ++
          ((List.ofFn fun i : Fin m => ratBits (coef i))).flatten).map some) t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatOnTape cfg q ∧
      |(q : ℝ) - (∑ i : Fin m, (coef i : ℝ))| ≤ (Λ : ℝ) * ((2 : ℝ)⁻¹) ^ k + ε ∧
      (∑ i : Fin m, (ratBits (coef i)).length) ≤ t ∧
      t ≤ 1 + m * k + k

inductive AccessForm where
  | forward
  | inverse
  | controlled
  deriving DecidableEq, Repr

def AccessForm.code : AccessForm → ℕ
  | .forward => 0
  | .inverse => 1
  | .controlled => 2

structure AccessContract (L : ℕ) where
  supplied : Fin L → AccessForm → Bool
  impl : Fin L → AccessForm → Option (ℕ → ℕ)

def AccessContract.WellFormed {L : ℕ} (c : AccessContract L) : Prop :=
  ∀ (s : Fin L) (f : AccessForm), (c.impl s f).isSome = c.supplied s f

inductive ArithCode where
  | add
  | mul
  | gcd
  | modexp
  deriving DecidableEq, Repr

def ArithCode.code : ArithCode → ℕ
  | .add => 0
  | .mul => 1
  | .gcd => 2
  | .modexp => 3

def arithSem (code : ArithCode) (ws : List ℕ) : List ℕ :=
  match code, ws with
  | .add, [a, b] => [a, a + b]
  | .mul, [a, b] => [a, a * b]
  | .gcd, [a, b, _] => [a, b, Nat.gcd a b]
  | .modexp, [a, e, m, _] => [a, e, m, a ^ e % m]
  | _, ws => ws

inductive ProbInstr (w L : ℕ) where
  | fairCoin (dst : Fin w)
  | oracle (slot : Fin L) (form : AccessForm) (addr : Fin w) (val : Fin w)
  | arith (code : ArithCode) (ws : List (Fin w))
  | emit (src : Fin w)

structure ProbProgram (w L : ℕ) where
  steps : List (ProbInstr w L)

def ProbProgram.coins {w L : ℕ} (p : ProbProgram w L) : ℕ :=
  (p.steps.filter (fun s => match s with | .fairCoin _ => true | _ => false)).length

def ProbProgram.LegalFor {w L : ℕ} (p : ProbProgram w L) (c : AccessContract L) : Prop :=
  ∀ s ∈ p.steps, match s with
    | ProbInstr.oracle slot form _ _ => c.supplied slot form = true
    | _ => True

structure ProbState (w : ℕ) where
  regs : Fin w → ℕ
  coins : List Bool
  out : List ℕ

def writeWindow {w : ℕ} (regs : Fin w → ℕ) (ws : List (Fin w)) (outs : List ℕ) : Fin w → ℕ :=
  (ws.zip outs).foldl (fun m iv => Function.update m iv.1 iv.2) regs

def probStep {w L : ℕ} (c : AccessContract L) (s : ProbState w) :
    ProbInstr w L → ProbState w
  | .fairCoin dst =>
    match s.coins with
    | b :: rest => { s with regs := Function.update s.regs dst (if b then 1 else 0),
                            coins := rest }
    | [] => s
  | .oracle slot form addr val =>
    match c.impl slot form with
    | some g => { s with regs := Function.update s.regs val (g (s.regs addr)) }
    | none => s
  | .arith code ws =>
    let vals := ws.map (fun i => s.regs i)
    let outs := arithSem code vals
    { s with regs := writeWindow s.regs ws outs }
  | .emit src => { s with out := s.out ++ [s.regs src] }

def runProb {w L : ℕ} (c : AccessContract L) (p : ProbProgram w L)
    (record : List Bool) : ProbState w :=
  p.steps.foldl (probStep c) { regs := fun _ => 0, coins := record, out := [] }

def ProbLaw {w L : ℕ} (c : AccessContract L) (p : ProbProgram w L) (ω : List ℕ) : ℝ :=
  ((Finset.univ.filter fun r : Fin p.coins → Bool =>
      (runProb c p (List.ofFn r)).out = ω).card : ℝ) / (2 ^ p.coins : ℝ)

def probInstrFields {w L : ℕ} : ProbInstr w L → List ℕ
  | .fairCoin dst => [0, dst.val]
  | .oracle slot form addr val => [1, slot.val, form.code, addr.val, val.val]
  | .arith code ws => [2, code.code, ws.length] ++ ws.map (fun i => i.val)
  | .emit src => [3, src.val]

def probProgramBits {w L : ℕ} (p : ProbProgram w L) : List Bool :=
  ([w, L, p.steps.length, p.coins] ++ p.steps.flatMap probInstrFields).flatMap natBits

structure ProbTM0Compiler where
  states : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

def tm0Final (comp : ProbTM0Compiler) (input : List (Option Bool)) (clock : ℕ) :
    Option (Turing.TM0.Cfg (Option Bool) (Fin (comp.states + 1))) :=
  ((List.range (clock + 1)).filterMap (fun s => BitMachineAfter comp.machine input s)).getLast?

def TM0Compiled {w L : ℕ} (comp : ProbTM0Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock space : ℕ) : Prop :=
  ∀ (record : List Bool) (_hlen : record.length = p.coins),
    let input := (probProgramBits p ++ record).map some
    ∃ (t : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (comp.states + 1))),
      BitMachineAfter comp.machine input t = some cfg ∧
      Turing.TM0.step comp.machine cfg = none ∧
      t ≤ clock ∧
      peakSpaceAfter comp.machine input t ≤ space ∧
      NatsOnTape cfg (runProb c p record).out

open scoped Classical in

def TM0LawPreserved {w L : ℕ} (comp : ProbTM0Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock : ℕ) : Prop :=
  ∀ ω : List ℕ,
    ((Finset.univ.filter fun r : Fin p.coins → Bool =>
        match tm0Final comp ((probProgramBits p ++ List.ofFn r).map some) clock with
        | some cfg => NatsOnTape cfg ω
        | none => False).card : ℝ) / (2 ^ p.coins : ℝ) = ProbLaw c p ω

structure ProbTM2Compiler where
  V : ℕ
  S : ℕ
  machine : Fin (V + 1) →
    Turing.TM2.Stmt (fun _ : Fin 3 => Option Bool) (Fin (V + 1)) (Fin (S + 1))

def tm2After (comp : ProbTM2Compiler) (input : List (Option Bool)) :
    ℕ → Option (Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (comp.V + 1)) (Fin (comp.S + 1)))
  | 0 => some (Turing.TM2.init (0 : Fin 3) input)
  | t + 1 =>
    match tm2After comp input t with
    | none => none
    | some cfg => Turing.TM2.step comp.machine cfg

def tm2Space {V S : ℕ}
    (cfg : Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (V + 1)) (Fin (S + 1))) : ℕ :=
  ∑ k : Fin 3, (cfg.stk k).length

def tm2Final (comp : ProbTM2Compiler) (input : List (Option Bool)) (clock : ℕ) :
    Option (Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (comp.V + 1)) (Fin (comp.S + 1))) :=
  ((List.range (clock + 1)).filterMap (fun s => tm2After comp input s)).getLast?

def TM2Compiled {w L : ℕ} (comp : ProbTM2Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock space : ℕ) : Prop :=
  ∀ (record : List Bool) (_hlen : record.length = p.coins),
    let input := (probProgramBits p ++ record).map some
    ∃ (t : ℕ) (cfg : Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (comp.V + 1)) (Fin (comp.S + 1))),
      tm2After comp input t = some cfg ∧
      cfg.l = none ∧
      t ≤ clock ∧
      (∀ s ≤ t, match tm2After comp input s with
        | some c' => tm2Space c' ≤ space
        | none => True) ∧
      ∀ i : ℕ, (cfg.stk (0 : Fin 3)).getD i none =
        tapeAt ((runProb c p record).out.flatMap natBits) i

open scoped Classical in

def TM2LawPreserved {w L : ℕ} (comp : ProbTM2Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock : ℕ) : Prop :=
  ∀ ω : List ℕ,
    ((Finset.univ.filter fun r : Fin p.coins → Bool =>
        match tm2Final comp ((probProgramBits p ++ List.ofFn r).map some) clock with
        | some cfg => ∀ i : ℕ, (cfg.stk (0 : Fin 3)).getD i none =
            tapeAt (ω.flatMap natBits) i
        | none => False).card : ℝ) / (2 ^ p.coins : ℝ) = ProbLaw c p ω

def AccessRestrictionPreserved : Prop :=
  ∀ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L),
    c.WellFormed →
    p.LegalFor c →
    ∀ s ∈ p.steps, match s with
      | ProbInstr.oracle slot form _ _ => c.supplied slot form = true ∧ (c.impl slot form).isSome
      | _ => True

def ShorPostprocessConsumer (comp0 : ProbTM0Compiler) : Prop :=
  (∀ (a e m : ℕ), ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      p.coins = 0 ∧ c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins → (runProb c p record).out = [a ^ e % m]) ∧
      clock ≤ 1 + (natBits a).length + (natBits e).length + (natBits m).length ∧
      space ≤ 1 + (natBits a).length + (natBits e).length + (natBits m).length) ∧
  (∀ (x y : ℕ), ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      p.coins = 0 ∧ c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins → (runProb c p record).out = [Nat.gcd x y]) ∧
      clock ≤ 1 + (natBits x).length + (natBits y).length ∧
      space ≤ 1 + (natBits x).length + (natBits y).length)

def SimonPostprocessConsumer (comp0 : ProbTM0Compiler) : Prop :=
  ∀ (n m : ℕ) (A : Fin m → Fin n → Bool) (b : Fin m → Bool),
    ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins →
        match (runProb c p record).out with
        | [code] =>
            code = 0 ∨
            ∃ x : Fin n → Bool,
              code = 1 ∧
              (∀ i : Fin m,
                (List.ofFn fun j : Fin n => if A i j && x j then (1 : ℕ) else 0).sum % 2
                  = if b i then 1 else 0)
        | _ => False) ∧
      clock ≤ 1 + n * m + n + m ∧
      space ≤ 1 + n * m + n + m

def QFTPostprocessConsumer (comp0 : ProbTM0Compiler) : Prop :=
  ∀ (n : ℕ) (bits : Fin n → Bool),
    ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins →
        (runProb c p record).out
          = [(List.ofFn fun j : Fin n => if bits j then 2 ^ j.val else 0).sum]) ∧
      clock ≤ 1 + n ∧
      space ≤ 1 + n

end

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
