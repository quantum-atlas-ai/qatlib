/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.Basic

@[expose] public section


/-! # Genuine recursive source word

Fixed arXiv:1005.1318v3 Eq.(3) and its many-term analogue. Level k-1 of the
actual shared recursion is S_(2k), with negative-i Hamiltonian generators.
We preserve the complete coefficient cancellation through degree2k and the
honest unmerged length/mass bounds. The sharper merged primitive count and
second-largest-norm tail are separate, unproved source obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceRecursive

/-- The actual skew generators of the Hamiltonian summands. -/
def signed {I : Type} (H : List (Matrix I I ℂ)) :=
  H.map (fun A => (-Complex.I) • A)

/-- Positive paper order k corresponds exactly to shared recursion level k-1. -/
def sourceWord {I : Type} [Fintype I] [DecidableEq I]
    (H : List (Matrix I I ℂ)) (k : ℕ) := recursiveSuzukiGenerators (signed H) (k-1)

/-- The signed generators sum to the actual negative-i total Hamiltonian generator. -/
theorem signedSum {I : Type} (H : List (Matrix I I ℂ)) :
    (signed H).sum = (-Complex.I) • H.sum := by
  induction H with
  | nil => simp [signed]
  | cons A H ih => simpa [signed, smul_add] using congrArg (fun M => (-Complex.I) • A + M) ih

/-- All actual recursive word coefficients match the total exponential through the complete source order. -/
theorem coefficients {I : Type} [Fintype I] [DecidableEq I]
    (H : List (Matrix I I ℂ)) {k n : ℕ} (hk : 0 < k) (hn : n ≤ 2*k) :
    suzukiSeries (sourceWord H k) n =
      ((n.factorial : ℝ)⁻¹) • ((-Complex.I) • H.sum)^n := by
  have horder : n ≤ 2*((k-1)+1) := by omega
  simpa only [sourceWord, signedSum] using
    recursive_suzuki_all_even_order_coefficients I (signed H) (k-1) n horder

/-- The actual unmerged source list has its true length and a valid shared mass bound. -/
theorem lengthAndMass {I : Type} [Fintype I] [DecidableEq I]
    (H : List (Matrix I I ℂ)) (k : ℕ) :
    (sourceWord H k).length = 2 * H.length * 5^(k-1) ∧
      suzukiMass (sourceWord H k) ≤ (3 : ℝ)^(k-1) * suzukiMass (signed H) := by
  simpa only [sourceWord, signed, List.length_map] using
    recursive_suzuki_length_and_mass I (signed H) (k-1)

end Qatlib.Papers.HamEfficiency10.SuzukiWord.SourceRecursive
