/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiConsumers
import Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedSegments
import Qatlib.Concepts.InteractionEvo.DysonGrid.DysonTruncationGrid
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

namespace Qatlib.Papers.OrderedOpExp08.MainResults

def orderedGenerator {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (u : ℝ) : Matrix I I ℂ :=
  ∑ j, H j u

def LambdaSmooth {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (Λ : ℝ) (a b : ℝ) (P : ℕ) : Prop :=
  ∀ (p : ℕ), p ≤ P → ∀ u ∈ Set.Icc a b,
    (∑ j : Fin m, ‖iteratedDeriv p (H j) u‖) ≤ Λ ^ (p + 1)

def ltsGenerators {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam : ℝ) (k : ℕ) : List (Matrix I I ℂ) :=
  Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiGenerators
    (List.ofFn (fun j : Fin m => H j (μ + dlam / 2))) k

def ltsWord {I : Type} [Fintype I] [DecidableEq I] {m : ℕ}
    (H : Fin m → ℝ → Matrix I I ℂ) (μ dlam : ℝ) (k : ℕ) : Matrix I I ℂ :=
  Qatlib.Concepts.TrotterFormula.SuzukiFourth.suzukiExponentialWord
    (ltsGenerators H μ dlam (k - 1)) dlam

def segmentProduct {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (t : ℝ) (r : ℕ) : Matrix I I ℂ :=
  (Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs.segmentWord xs t r).prod

def suzukiQ (k : ℕ) : ℝ :=
  if k = 1 then 1 / 2
  else ∏ i ∈ Finset.range (k - 1), |1 - 4 * Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.recursiveSuzukiScale i|

def theorem1Count (Λ ε dlam : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil (5 * (k : ℝ) * Λ * dlam * ((5 : ℝ) / 3) ^ k * (Λ * dlam / ε) ^ ((2 * k : ℝ)⁻¹))

theorem list_prod_norm_le_one {I : Type} [Fintype I] [DecidableEq I]
    (V : List (Matrix I I ℂ)) (hV : ∀ X ∈ V, ‖X‖ ≤ 1) : ‖V.prod‖ ≤ 1 := by
  induction V with
  | nil => simpa using! Qatlib.Foundations.OperatorErrors.OperatorError.l2_norm_one_le (I := I)
  | cons X xs ih =>
    rw [List.prod_cons]
    calc
      ‖X * xs.prod‖ ≤ ‖X‖ * ‖xs.prod‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by
        exact mul_le_mul (hV X (by simp)) (ih (fun Y hY => hV Y (by simp [hY])))
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

end Qatlib.Papers.OrderedOpExp08.MainResults
