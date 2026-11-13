/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
import Qatlib.Concepts.WalshMoment.Forrelation.StrongYesInstancePropertyStat
import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Theorem62CumulativeSamplerStat

/-!
# Oracle sampler and fresh-search definitions

`samplerPrefixes` extracts circuit prefixes preceding sampler queries, and `samplerFallback`
chooses an unused binary string when the proposed sample has already appeared. The module
defines a counted binary-prefix generator, phase-query padding, packed oracles, and protected
diagonal lengths for finite query constructions as in [KitaevShenVyalyi2002].

The remaining definitions provide strong weighted averages and occupation statistics for
tensor-product states, connecting classical histories to quantum sampling estimates.

## Main statements

* `binaryPrefixCounted`: generates a binary-alphabet prefix together with a recursive visit
  count.
* `firstFreshBounded`: searches only the first `hist.length + 1` candidate strings.
* `occupationMoment`: multiplies the occupation counts of the guessed values.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

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

/-- Lists the prefixes preceding `S` queries, replacing earlier `S` queries by the supplied
history gate. -/
def samplerPrefixes {I : Type} (historyGate : Matrix I I ℂ) :
    TOCircuit I → List (TOCircuit I)
  | [] => []
  | TOStep.gate G :: C => (samplerPrefixes historyGate C).map (TOStep.gate G :: ·)
  | TOStep.queryU :: C => (samplerPrefixes historyGate C).map (TOStep.queryU :: ·)
  | TOStep.queryS :: C => [] ::
      (samplerPrefixes historyGate C).map (TOStep.gate historyGate :: ·)

/-- Recursively enumerates all `n`-bit strings, listing false-leading strings before
true-leading strings. -/
def binaryAlphabet : (n : ℕ) → List (Reg n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (binaryAlphabet n).map (Fin.cons false) ++
      (binaryAlphabet n).map (Fin.cons true)

/-- The first binary-alphabet string absent from the history, or `none` if no such string
exists. -/
def firstFresh (n : ℕ) (hist : List (Reg n)) : Option (Reg n) :=
  (binaryAlphabet n).find? (fun x => decide (x ∉ hist))

/-- Returns the proposed string if it is fresh, and otherwise searches the binary alphabet for a
fresh string. -/
def samplerFallback (n : ℕ) (hist : List (Reg n)) (x : Reg n) : Option (Reg n) :=
  if x ∈ hist then firstFresh n hist else some x

/-- Appends `t - TOQueryCountU P` additional `U` queries to a prefix. -/
def paddedPrefix {I : Type} (t : ℕ) (P : TOCircuit I) : TOCircuit I :=
  P ++ List.replicate (t - TOQueryCountU P) TOStep.queryU

/-- Generates up to the first `k` binary-alphabet entries together with the number of recursive
generator visits. -/
def binaryPrefixCounted : (n k : ℕ) → List (Reg n) × ℕ
  | _, 0 => ([], 1)
  | 0, _ + 1 => ([fun i => Fin.elim0 i], 1)
  | n + 1, k + 1 =>
      let lo := binaryPrefixCounted n (min (k + 1) (2 ^ n))
      let hi := binaryPrefixCounted n ((k + 1) - 2 ^ n)
      (lo.1.map (Fin.cons false) ++ hi.1.map (Fin.cons true), 1 + lo.2 + hi.2)

/-- Searches the first `hist.length + 1` binary-alphabet entries for a string absent from the
history. -/
def firstFreshBounded (n : ℕ) (hist : List (Reg n)) : Option (Reg n) :=
  (binaryPrefixCounted n (hist.length + 1)).1.find? (fun x => decide (x ∉ hist))

/-- The uniform average over sample tuples of the oracle-weighted sum defined by
`strongBernoulliWeight`. -/
noncomputable def strongAverage (n ℓ : ℕ) (κ : ℝ)
    (f : (Fin ℓ → Reg n) → (Reg n → Bool) → ℝ) : ℝ :=
  1 / (Fintype.card (Fin ℓ → Reg n) : ℝ) *
    ∑ s : Fin ℓ → Reg n, ∑ U : Reg n → Bool, strongBernoulliWeight n ℓ κ s U * f s U

/-- Combines two oracle families into one by using the leading bit as an `S`/`U` selector; the
zero-bit oracle is constantly false. -/
def packedOracle (S U : ∀ n, Reg n → Bool) : ∀ n, Reg n → Bool
  | 0, _ => false
  | n + 1, x => if x 0 then U n (fun i => x i.succ) else S n (fun i => x i.succ)

/-- A recursive sequence exceeding each stage threshold and the preceding stage's query window. -/
def diagonalLengths (threshold : ℕ → ℕ) (queryWindow : ℕ → ℕ → ℕ) : ℕ → ℕ
  | 0 => threshold 0 + 1
  | k + 1 => 1 + max (diagonalLengths threshold queryWindow k)
      (max (threshold (k+1)) (queryWindow k (diagonalLengths threshold queryWindow k)))

/-- The `ℓ`-fold tensor power of a state, with amplitude equal to the product of the coordinate
amplitudes. -/
noncomputable def condensateTensor {I : Type} (ℓ : ℕ) (φ : QState I) :
    QState (Fin ℓ → I) := fun s => ∏ j, φ (s j)

/-- The number of coordinates of the sample tuple equal to `x`. -/
def occupationCount {I : Type} [DecidableEq I] {ℓ : ℕ} (x : I) (s : Fin ℓ → I) : ℕ :=
  (Finset.univ.filter fun j => s j = x).card

/-- The proposition that every guessed value occurs in at least one sample coordinate. -/
def allOccupied {I : Type} {ℓ v : ℕ} (guesses : Fin v → I) (s : Fin ℓ → I) : Prop :=
  ∀ a, ∃ j, s j = guesses a

instance allOccupied_decidable {I : Type} [DecidableEq I] {ℓ v : ℕ}
    (guesses : Fin v → I) (s : Fin ℓ → I) : Decidable (allOccupied guesses s) :=
  inferInstanceAs (Decidable (∀ a, ∃ j, s j = guesses a))

/-- The product, over the guesses, of their occupation counts in the sample tuple. -/
def occupationMoment {I : Type} [DecidableEq I] {ℓ v : ℕ}
    (guesses : Fin v → I) (s : Fin ℓ → I) : ℕ := ∏ a, occupationCount (guesses a) s

end Qatlib.Concepts.FreshFallback.BitScanLedger
