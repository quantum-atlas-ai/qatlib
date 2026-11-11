/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.FairRandomBits.RationalReject.RationalRejectionSampling
import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Mathlib.Data.Nat.Sqrt

/-!
# Finite coin-code and rejection-sampler definitions

`CoinCode` describes finite binary decision trees with explicit returns and bit requests. Its
interpreter records a residual code and read count; its costed law, fresh-tape law, and native
control table provide probabilistic and tape-machine interpretations. This is a concrete
classical component of the computational models described in [KitaevShenVyalyi2002].

`weightedSampler` builds a bounded rejection loop with separate bit, comparison, and trial
counters. `sqrtSampler` applies it to integer approximations of square-root weights at a chosen
precision.

## Main statements

* `CoinCode`: Finite programs that return values or branch on a supplied bit.
* `CoinCode.run`: A finite-tape interpreter with residual code and read count.
* `weightedSampler`: Bounded weighted rejection sampling with counters.
* `sqrtSampler`: Weighted sampling using precision-scaled integer square roots.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- A finite binary decision tree whose leaves return values and whose internal nodes request a
Boolean bit. -/
inductive CoinCode (α : Type)
  | ret : α → CoinCode α
  | bit : CoinCode α → CoinCode α → CoinCode α

namespace CoinCode

variable {α β : Type}

/-- Replaces each return leaf by its continuation code while preserving bit-branching nodes. -/
def bind (p : CoinCode α) (f : α → CoinCode β) : CoinCode β :=
  match p with
  | .ret a => f a
  | .bit p q => .bit (p.bind f) (q.bind f)

/-- The maximum number of bit requests on a root-to-leaf path. -/
def depth : CoinCode α → ℕ
  | .ret _ => 0
  | .bit p q => 1 + max p.depth q.depth

/-- Extracts the return value at a return node and gives `none` at a bit request. -/
def output : CoinCode α → Option α
  | .ret a => some a
  | .bit _ _ => none

/-- Interprets a finite bit list, returning the residual code and the number of bits consumed. -/
def run : List Bool → CoinCode α → CoinCode α × ℕ
  | [], p => (p, 0)
  | _ :: _, .ret a => (.ret a, 0)
  | b :: bs, .bit p q =>
      let z := run bs (if b then q else p)
      (z.1, 1 + z.2)

/-- The output and read-cost law obtained by using an independent fair bit at each branching
node. -/
noncomputable def law : CoinCode α → CostedLaw α
  | .ret a => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret a
  | .bit p q => (PMF.uniformOfFintype' Bool).bind fun b =>
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (if b then law q else law p)

/-- The probability law of a list of `n` independent fair Boolean bits. -/
noncomputable def freshTape : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | n + 1 => (PMF.uniformOfFintype' Bool).bind fun b =>
      (freshTape n).map (b :: ·)

/-- The optional-output and read-cost law obtained by running a code on a fresh tape of length
`n`. -/
noncomputable def tapeLaw (n : ℕ) (p : CoinCode α) : CostedLaw (Option α) :=
  (freshTape n).map fun bs => ((p.run bs).1.output, (p.run bs).2)

/-- A finite coin code that requests `n` bits and returns them as a register in `Reg n`. -/
def block : (n : ℕ) → CoinCode (Reg n)
  | 0 => .ret (ZeroStr 0)
  | n + 1 => (block n).bind fun ω =>
      .bit (.ret ((regSuccEquiv n).symm (ω, false)))
        (.ret ((regSuccEquiv n).symm (ω, true)))

/-- The type of node positions in a finite coin code, including its root and the positions of
both branches. -/
def Positions : CoinCode α → Type
  | .ret _ => Unit
  | .bit p q => Unit ⊕ (p.Positions ⊕ q.Positions)

/-- The recursively constructed finite enumeration of the positions in a coin code. -/
@[reducible] def positionFintype : (p : CoinCode α) → Fintype p.Positions
  | .ret _ => inferInstanceAs (Fintype Unit)
  | .bit p q =>
      letI := positionFintype p
      letI := positionFintype q
      inferInstanceAs (Fintype (Unit ⊕ (p.Positions ⊕ q.Positions)))

instance (p : CoinCode α) : Fintype p.Positions := positionFintype p

/-- The root position of a finite coin code. -/
def root : (p : CoinCode α) → p.Positions
  | .ret _ => ()
  | .bit _ _ => .inl ()

instance (p : CoinCode α) : Inhabited p.Positions := ⟨p.root⟩

/-- The subtree of a finite coin code at the given position. -/
def atPosition : (p : CoinCode α) → p.Positions → CoinCode α
  | .ret a, _ => .ret a
  | .bit p q, .inl _ => .bit p q
  | .bit p _, .inr (.inl i) => p.atPosition i
  | .bit _ q, .inr (.inr i) => q.atPosition i

/-- The successor position selected by a Boolean bit, with `none` at return leaves. -/
def nextPosition (b : Bool) : (p : CoinCode α) → p.Positions → Option p.Positions
  | .ret _, _ => none
  | .bit p q, .inl _ =>
      some (if b then .inr (.inr q.root) else .inr (.inl p.root))
  | .bit p _, .inr (.inl i) => (p.nextPosition b i).map (.inr ∘ .inl)
  | .bit _ q, .inr (.inr i) => (q.nextPosition b i).map (.inr ∘ .inr)

/-- The native machine table that follows the selected code edge and rewrites the current tape
symbol unchanged. -/
def nativeTable (p : CoinCode α) (b : Bool) :
    Turing.TM0.Machine (Option Bool) p.Positions :=
  fun i γ => (p.nextPosition b i).map fun j => (j, .write γ)

/-- Applies the Boolean result map at return positions and gives `false` at positions with no
output. -/
def nativeAccept (p : CoinCode α) (f : α → Bool) (i : p.Positions) : Bool :=
  ((p.atPosition i).output.map f).getD false

/-- The total number of return and branching nodes in a finite coin code. -/
def nodes : CoinCode α → ℕ
  | .ret _ => 1
  | .bit p q => 1 + p.nodes + q.nodes

end CoinCode

/-- Draws a `b`-bit block and applies the counted weight decoder, returning an optional index
and comparison count. -/
def weightedTrial {N : ℕ} (w : Fin N → ℕ) (b : ℕ) :
    CoinCode (Option (Fin N) × ℕ) :=
  (CoinCode.block b).bind fun ω =>
    .ret (weightDecodeCounted w (bitVecEquiv b ω).val)

/-- Performs a weighted trial, updates the state on acceptance, and returns the unchanged
environment together with the decoded outcome and comparison count. -/
def feedbackTrial {S E : Type} {N : ℕ} (weights : S → Fin N → ℕ)
    (update : S → Fin N → S) (b : ℕ) (s : S) (env : E) :
    CoinCode (S × E × Option (Fin N) × ℕ) :=
  (weightedTrial (weights s) b).bind fun z =>
    .ret (z.1.elim s (update s), env, z.1, z.2)

/-- Decodes one bit block and updates the cumulative bit and comparison counters, producing
either an accepted index or a pending configuration. -/
def countedTrialResult {N : ℕ} (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) (ω : Reg b) :
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) :=
  let d := weightDecodeCounted w (bitVecEquiv b ω).val
  match d.1 with
  | some j => .inl (j, BD.1 + b, BD.2 + d.2)
  | none => .inr (BD.1 + b, BD.2 + d.2)

/-- Executes at most the given number of weighted trials, stopping at acceptance and recording
the number of trials performed. -/
def countedLoop {N : ℕ} (w : Fin N → ℕ) (b : ℕ) : ℕ →
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) →
    CoinCode (RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ)
  | 0, cfg => .ret (cfg, 0)
  | _ + 1, .inl out => .ret (.inl out, 0)
  | fuel + 1, .inr BD => (CoinCode.block b).bind fun ω =>
      (countedLoop w b fuel (countedTrialResult w b BD ω)).bind fun y =>
        .ret (y.1, 1 + y.2)

/-- Starts the counted rejection loop with zero bit and comparison counters and the given fuel
budget. -/
def weightedSampler {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ) :=
  countedLoop w b fuel (.inr (0, 0))

/-- The integer square root of `a * s ^ 2`, used as an integer approximation to `s` times the
real square root of `a`. -/
def sqrtWeight (s a : ℕ) : ℕ := Nat.sqrt (a * s ^ 2)

/-- The scale `(N + 1) * 2 ^ k` for approximating a family of `N` square-root weights. -/
def sqrtPrecisionScale (N k : ℕ) : ℕ := (N + 1) * 2 ^ k

/-- The integer square-root weights obtained by applying `sqrtWeight` at scale
`sqrtPrecisionScale N k`. -/
def sqrtWeights {N : ℕ} (a : Fin N → ℕ) (k : ℕ) (i : Fin N) : ℕ :=
  sqrtWeight (sqrtPrecisionScale N k) (a i)

/-- The weighted rejection sampler for precision-scaled square-root weights, using a bit width
determined by their total weight. -/
def sqrtSampler {N : ℕ} (a : Fin N → ℕ) (k fuel : ℕ) :=
  weightedSampler (sqrtWeights a k) (Nat.clog 2 (weightTotal (sqrtWeights a k))) fuel

/-- The event that a completed rejection configuration contains an accepted index in `F`. -/
def acceptedIn {N : ℕ} (F : Finset (Fin N)) :
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) → Prop
  | .inl out => out.1 ∈ F
  | .inr _ => False

end Qatlib.Concepts.AdversaryBounds.AdvDuality
