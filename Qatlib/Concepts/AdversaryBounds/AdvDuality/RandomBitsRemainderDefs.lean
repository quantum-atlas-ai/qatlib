/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.FairRandomBits.RationalReject.RationalRejectionSampling
import Qatlib.Concepts.ClassicalTape.FairCoinTape
import Mathlib.Data.Nat.Sqrt
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

inductive CoinCode (α : Type)
  | ret : α → CoinCode α
  | bit : CoinCode α → CoinCode α → CoinCode α

namespace CoinCode

variable {α β : Type}

def bind (p : CoinCode α) (f : α → CoinCode β) : CoinCode β :=
  match p with
  | .ret a => f a
  | .bit p q => .bit (p.bind f) (q.bind f)

def depth : CoinCode α → ℕ
  | .ret _ => 0
  | .bit p q => 1 + max p.depth q.depth

def output : CoinCode α → Option α
  | .ret a => some a
  | .bit _ _ => none

def run : List Bool → CoinCode α → CoinCode α × ℕ
  | [], p => (p, 0)
  | _ :: _, .ret a => (.ret a, 0)
  | b :: bs, .bit p q =>
      let z := run bs (if b then q else p)
      (z.1, 1 + z.2)

noncomputable def law : CoinCode α → CostedLaw α
  | .ret a => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret a
  | .bit p q => (PMF.uniformOfFintype' Bool).bind fun b =>
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1 (if b then law q else law p)

noncomputable def freshTape : ℕ → PMF (List Bool)
  | 0 => PMF.pure []
  | n + 1 => (PMF.uniformOfFintype' Bool).bind fun b =>
      (freshTape n).map (b :: ·)

noncomputable def tapeLaw (n : ℕ) (p : CoinCode α) : CostedLaw (Option α) :=
  (freshTape n).map fun bs => ((p.run bs).1.output, (p.run bs).2)

def block : (n : ℕ) → CoinCode (Reg n)
  | 0 => .ret (ZeroStr 0)
  | n + 1 => (block n).bind fun ω =>
      .bit (.ret ((regSuccEquiv n).symm (ω, false)))
        (.ret ((regSuccEquiv n).symm (ω, true)))

def Positions : CoinCode α → Type
  | .ret _ => Unit
  | .bit p q => Unit ⊕ (p.Positions ⊕ q.Positions)

@[reducible] def positionFintype : (p : CoinCode α) → Fintype p.Positions
  | .ret _ => inferInstanceAs (Fintype Unit)
  | .bit p q =>
      letI := positionFintype p
      letI := positionFintype q
      inferInstanceAs (Fintype (Unit ⊕ (p.Positions ⊕ q.Positions)))

instance (p : CoinCode α) : Fintype p.Positions := positionFintype p

def root : (p : CoinCode α) → p.Positions
  | .ret _ => ()
  | .bit _ _ => .inl ()

instance (p : CoinCode α) : Inhabited p.Positions := ⟨p.root⟩

def atPosition : (p : CoinCode α) → p.Positions → CoinCode α
  | .ret a, _ => .ret a
  | .bit p q, .inl _ => .bit p q
  | .bit p _, .inr (.inl i) => p.atPosition i
  | .bit _ q, .inr (.inr i) => q.atPosition i

def nextPosition (b : Bool) : (p : CoinCode α) → p.Positions → Option p.Positions
  | .ret _, _ => none
  | .bit p q, .inl _ =>
      some (if b then .inr (.inr q.root) else .inr (.inl p.root))
  | .bit p _, .inr (.inl i) => (p.nextPosition b i).map (.inr ∘ .inl)
  | .bit _ q, .inr (.inr i) => (q.nextPosition b i).map (.inr ∘ .inr)

def nativeTable (p : CoinCode α) (b : Bool) :
    Turing.TM0.Machine (Option Bool) p.Positions :=
  fun i γ => (p.nextPosition b i).map fun j => (j, .write γ)

def nativeAccept (p : CoinCode α) (f : α → Bool) (i : p.Positions) : Bool :=
  ((p.atPosition i).output.map f).getD false

def nodes : CoinCode α → ℕ
  | .ret _ => 1
  | .bit p q => 1 + p.nodes + q.nodes

end CoinCode

def weightedTrial {N : ℕ} (w : Fin N → ℕ) (b : ℕ) :
    CoinCode (Option (Fin N) × ℕ) :=
  (CoinCode.block b).bind fun ω =>
    .ret (weightDecodeCounted w (bitVecEquiv b ω).val)

def feedbackTrial {S E : Type} {N : ℕ} (weights : S → Fin N → ℕ)
    (update : S → Fin N → S) (b : ℕ) (s : S) (env : E) :
    CoinCode (S × E × Option (Fin N) × ℕ) :=
  (weightedTrial (weights s) b).bind fun z =>
    .ret (z.1.elim s (update s), env, z.1, z.2)

def countedTrialResult {N : ℕ} (w : Fin N → ℕ) (b : ℕ) (BD : ℕ × ℕ) (ω : Reg b) :
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) :=
  let d := weightDecodeCounted w (bitVecEquiv b ω).val
  match d.1 with
  | some j => .inl (j, BD.1 + b, BD.2 + d.2)
  | none => .inr (BD.1 + b, BD.2 + d.2)

def countedLoop {N : ℕ} (w : Fin N → ℕ) (b : ℕ) : ℕ →
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) →
    CoinCode (RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ)
  | 0, cfg => .ret (cfg, 0)
  | _ + 1, .inl out => .ret (.inl out, 0)
  | fuel + 1, .inr BD => (CoinCode.block b).bind fun ω =>
      (countedLoop w b fuel (countedTrialResult w b BD ω)).bind fun y =>
        .ret (y.1, 1 + y.2)

def weightedSampler {N : ℕ} (w : Fin N → ℕ) (b fuel : ℕ) :=
  countedLoop w b fuel (.inr (0, 0))

def sqrtWeight (s a : ℕ) : ℕ := Nat.sqrt (a * s ^ 2)

def sqrtPrecisionScale (N k : ℕ) : ℕ := (N + 1) * 2 ^ k

def sqrtWeights {N : ℕ} (a : Fin N → ℕ) (k : ℕ) (i : Fin N) : ℕ :=
  sqrtWeight (sqrtPrecisionScale N k) (a i)

def sqrtSampler {N : ℕ} (a : Fin N → ℕ) (k fuel : ℕ) :=
  weightedSampler (sqrtWeights a k) (Nat.clog 2 (weightTotal (sqrtWeights a k))) fuel

def acceptedIn {N : ℕ} (F : Finset (Fin N)) :
    RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) → Prop
  | .inl out => out.1 ∈ F
  | .inr _ => False

end Qatlib.Concepts.AdversaryBounds.AdvDuality
