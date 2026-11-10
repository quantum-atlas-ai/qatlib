/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
import Qatlib.Concepts.WalshMoment.Forrelation.StrongYesInstancePropertyStat
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Theorem62CumulativeSamplerStat
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.FreshFallback.BitScanLedger

open Qatlib
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

def samplerPrefixes {I : Type} (historyGate : Matrix I I ℂ) :
    TOCircuit I → List (TOCircuit I)
  | [] => []
  | TOStep.gate G :: C => (samplerPrefixes historyGate C).map (TOStep.gate G :: ·)
  | TOStep.queryU :: C => (samplerPrefixes historyGate C).map (TOStep.queryU :: ·)
  | TOStep.queryS :: C => [] ::
      (samplerPrefixes historyGate C).map (TOStep.gate historyGate :: ·)

def binaryAlphabet : (n : ℕ) → List (Reg n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (binaryAlphabet n).map (Fin.cons false) ++
      (binaryAlphabet n).map (Fin.cons true)

def firstFresh (n : ℕ) (hist : List (Reg n)) : Option (Reg n) :=
  (binaryAlphabet n).find? (fun x => decide (x ∉ hist))

def samplerFallback (n : ℕ) (hist : List (Reg n)) (x : Reg n) : Option (Reg n) :=
  if x ∈ hist then firstFresh n hist else some x

def paddedPrefix {I : Type} (t : ℕ) (P : TOCircuit I) : TOCircuit I :=
  P ++ List.replicate (t - TOQueryCountU P) TOStep.queryU

def binaryPrefixCounted : (n k : ℕ) → List (Reg n) × ℕ
  | _, 0 => ([], 1)
  | 0, _ + 1 => ([fun i => Fin.elim0 i], 1)
  | n + 1, k + 1 =>
      let lo := binaryPrefixCounted n (min (k + 1) (2 ^ n))
      let hi := binaryPrefixCounted n ((k + 1) - 2 ^ n)
      (lo.1.map (Fin.cons false) ++ hi.1.map (Fin.cons true), 1 + lo.2 + hi.2)

def firstFreshBounded (n : ℕ) (hist : List (Reg n)) : Option (Reg n) :=
  (binaryPrefixCounted n (hist.length + 1)).1.find? (fun x => decide (x ∉ hist))

noncomputable def strongAverage (n ℓ : ℕ) (κ : ℝ)
    (f : (Fin ℓ → Reg n) → (Reg n → Bool) → ℝ) : ℝ :=
  1 / (Fintype.card (Fin ℓ → Reg n) : ℝ) *
    ∑ s : Fin ℓ → Reg n, ∑ U : Reg n → Bool, strongBernoulliWeight n ℓ κ s U * f s U

def packedOracle (S U : ∀ n, Reg n → Bool) : ∀ n, Reg n → Bool
  | 0, _ => false
  | n + 1, x => if x 0 then U n (fun i => x i.succ) else S n (fun i => x i.succ)

def diagonalLengths (threshold : ℕ → ℕ) (queryWindow : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => threshold 0 + 1
  | k + 1 => 1 + max (diagonalLengths threshold queryWindow k)
      (max (threshold (k+1)) (queryWindow k (diagonalLengths threshold queryWindow k)))

noncomputable def condensateTensor {I : Type} (ℓ : ℕ) (φ : QState I) :
    QState (Fin ℓ → I) := fun s => ∏ j, φ (s j)

def occupationCount {I : Type} [DecidableEq I] {ℓ : ℕ} (x : I) (s : Fin ℓ → I) : ℕ :=
  (Finset.univ.filter fun j => s j = x).card

def allOccupied {I : Type} {ℓ v : ℕ} (guesses : Fin v → I) (s : Fin ℓ → I) : Prop :=
  ∀ a, ∃ j, s j = guesses a

instance allOccupied_decidable {I : Type} [DecidableEq I] {ℓ v : ℕ}
    (guesses : Fin v → I) (s : Fin ℓ → I) : Decidable (allOccupied guesses s) :=
  inferInstanceAs (Decidable (∀ a, ∃ j, s j = guesses a))

def occupationMoment {I : Type} [DecidableEq I] {ℓ v : ℕ}
    (guesses : Fin v → I) (s : Fin ℓ → I) : ℕ := ∏ a, occupationCount (guesses a) s

end Qatlib.Concepts.FreshFallback.BitScanLedger
