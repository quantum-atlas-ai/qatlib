/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs

set_option autoImplicit false
set_option maxHeartbeats 400000

open Matrix Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorCoreDefs
open scoped Classical BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open scoped ComplexOrder
open Set
variable {I : Type} [Fintype I] [DecidableEq I]
variable {I : Type} [Fintype I]
variable {S ι : Type} [Fintype S] [Fintype ι]

theorem clause54_outputError_budget_impossible :
    ¬(∀ (S : Type) [Fintype S] (dist : S → S → ℝ) (d : ℕ) (C κ α : ℝ) (τ : ℕ),
      0 < C →
      0 ≤ κ →
      2 * (d : ℝ) < α →
      IsPolynomialGrowth dist C d →
      ∀ (D m : ℕ) (H : Fin m → Operator D)
        (supp : Fin m → Finset S)
        (suppO : Finset S) (O : Operator D),
        suppO.Nonempty →
        (∀ i : Fin m, (supp i).Nonempty) →
        IsTermPacking supp τ →
        IsObservableDecay (distToSupport dist suppO) supp H O κ α →
        ∀ (T ε : ℝ), 0 < T → 0 < ε →
          ∃ (ℓ : ℝ) (r Γ υ : ℕ) (ledger : LocalObservableLedger),
            0 < ℓ ∧
            0 < r ∧
            0 < Γ ∧
            (∀ i : Fin m, i ∈ lightConeTerms (distToSupport dist suppO) supp ℓ →
              termDistToObs (distToSupport dist suppO) supp i < (Γ : ℝ) * ℓ) ∧
            (∀ ρin : Operator D, IsDensityOperator ρin →
              ‖Matrix.trace (O *
                  ((shellOrderedWord (distToSupport dist suppO) ℓ T r H supp Γ υ).prod * ρin *
                    (shellOrderedWord (distToSupport dist suppO) ℓ T r H supp Γ υ).prodᴴ)) -
                Matrix.trace (O *
                  (NormedSpace.exp (T • (∑ i : Fin m, H i)) * ρin *
                    (NormedSpace.exp (T • (∑ i : Fin m, H i)))ᴴ))‖ ≤ ε) ∧
            ledger.lightConeRadius = ℓ ∧
            ledger.outputError = ε ∧
            ledger.outputError ≤
              (T ^ 2 / (2 * (r : ℝ))) *
                pfCommutatorSum (truncatedFamily (distToSupport dist suppO) supp ℓ H) +
              T * observableTailMass (distToSupport dist suppO) ℓ H supp O ∧
            ledger.reducedLength =
              r * (lightConeTerms (distToSupport dist suppO) supp ℓ).card ∧
            ledger.gates =
              r * (lightConeTerms (distToSupport dist suppO) supp ℓ).card ∧
            ledger.gates ≤
              r * τ * suppO.card * Nat.ceil (C * (1 + 2 * ℓ) ^ (d : ℝ))) := by
  intro h

  have hgen := h (Fin 1) (fun _ _ => 0) 0 (1 : ℝ) (0 : ℝ) (1 : ℝ) 0
    (by norm_num) (by norm_num) (by norm_num)
    (by
      refine ⟨by norm_num, fun o r hr => ?_⟩
      have hfilter :
          (Finset.univ : Finset (Fin 1)).filter (fun x => ((fun _ _ => (0 : ℝ)) o x) ≤ r) =
            Finset.univ :=
        Finset.filter_true_of_mem fun x _ => hr
      rw [hfilter, Finset.card_univ, Fintype.card_fin]
      simp)
    (1 : ℕ) 0
    (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ => (∅ : Finset (Fin 1)))
    (Finset.univ : Finset (Fin 1))
    (0 : Matrix (Fin 1) (Fin 1) ℂ)
    (Finset.univ_nonempty)
    (fun i => nomatch i)
    (fun x => by simp)
    (fun i => nomatch i)
  obtain hgen := hgen 1 1 (by norm_num) (by norm_num)
  obtain ⟨ℓ, r, Γ, υ, ledger, _, _, _, _, _, _, hEq, hLe, _, _, _⟩ := hgen

  have hzero : (1 ^ 2 / (2 * (r : ℝ))) *
        pfCommutatorSum (truncatedFamily
          (distToSupport (fun _ _ => (0 : ℝ)) (Finset.univ : Finset (Fin 1)))
          (fun _ : Fin 0 => (∅ : Finset (Fin 1))) ℓ
          (fun _ : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℂ))) +
      (1 : ℝ) * observableTailMass
        (distToSupport (fun _ _ => (0 : ℝ)) (Finset.univ : Finset (Fin 1)))
        ℓ (fun _ : Fin 0 => (0 : Matrix (Fin 1) (Fin 1) ℂ))
        (fun _ : Fin 0 => (∅ : Finset (Fin 1)))
        (0 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
    simp [pfCommutatorSum, observableTailMass]
  rw [hzero] at hLe
  linarith

theorem clause53_truncationTail_budget_false :
    ¬(∀ (d : ℕ) (S : Type) [Fintype S] (dist : S → S → ℝ) (C α : ℝ),
      0 < C →
      2 * (d : ℝ) < α →
      IsPolynomialGrowth dist C d →
      ∀ (w : S → S → ℝ), IsPowerLawWeight dist w α →
        ∀ (ℓ : ℝ), 0 < ℓ →
          truncationTail dist w ℓ ≤
            (Fintype.card S) * powerLawTailBound C d α ℓ ∧
          ∀ (D m : ℕ) (H : Fin m → Operator D) (supp : Fin m → Finset S)
            (xs : List (Operator D)) (lab : Fin xs.length → Fin m)
            (c : Fin xs.length → ℝ) (Htot Hcut : Operator D) (p : ℕ) (R τ : ℕ),
            1 ≤ p →
            (∀ i : Fin m, (supp i).Nonempty) →
            (∀ i : Fin m, ∀ x ∈ supp i, ∀ y ∈ supp i, dist x y ≤ (R : ℝ)) →
            IsTermPacking supp τ →
            IsFamilyWord H xs lab c →
            IsMatchedOrder xs Hcut p →
            ‖Htot - Hcut‖ ≤ truncationTail dist w ℓ →
            ∀ (T ε : ℝ), 0 < ε →
              let r := familyOrderedSegments H lab c p T ε
              ‖(segmentWord xs T r).prod - NormedSpace.exp (T • Htot)‖ ≤
                ε + |T| * truncationTail dist w ℓ ∧
              cutoffPairCount dist supp ℓ ≤
                m * τ * Nat.ceil (C * (1 + R + ℓ) ^ (d : ℝ)) ∧
              ∃ ledger : LongRangeLedger,
                ledger.segments = r ∧
                ledger.cutoff = ℓ ∧
                ledger.gatesPerStep = xs.length ∧
                ledger.tailCost = truncationTail dist w ℓ) := by
  intro h

  have hgen := h 0 (Fin 1) (fun _ _ => (2 : ℝ)) 1 1
    (by norm_num) (by norm_num)
    (by
      refine ⟨by norm_num, fun o r hr => ?_⟩
      by_cases h2 : (2 : ℝ) ≤ r
      · have hfilter :
            (Finset.univ : Finset (Fin 1)).filter (fun x => (2 : ℝ) ≤ r) = Finset.univ :=
          Finset.filter_true_of_mem fun x _ => h2
        rw [hfilter, Finset.card_univ, Fintype.card_fin]
        simp
      · have hfilter :
            (Finset.univ : Finset (Fin 1)).filter (fun x => (2 : ℝ) ≤ r) = ∅ :=
          Finset.filter_false_of_mem fun x _ => h2
        rw [hfilter, Finset.card_empty]
        simp)
    (fun _ _ => (1 : ℝ))
    (by
      intro i j hij
      constructor
      · norm_num
      · intro hne
        exact absurd hij hne)
    1
    (by norm_num)
  obtain htail := hgen.1

  have hL : truncationTail (fun _ _ => (2 : ℝ) : Fin 1 → Fin 1 → ℝ)
      (fun _ _ => (1 : ℝ) : Fin 1 → Fin 1 → ℝ) 1 = 1 := by
    simp [truncationTail]
  have hR : (Fintype.card (Fin 1)) *
      powerLawTailBound (1 : ℝ) (((0 : ℕ) : ℝ)) (1 : ℝ) (1 : ℝ) = 1 / 2 := by
    have hexp : (((0 : ℕ) : ℝ) - (1 : ℝ)) = (-(1 : ℝ)) := by norm_num
    have hden : ((1 : ℝ) - ((0 : ℕ) : ℝ)) = 1 := by norm_num
    simp only [Fintype.card_fin, powerLawTailBound, hexp, hden]
    norm_num
  rw [hL, hR] at htail
  norm_num at htail
end Qatlib.Concepts.TrotterFormula.GeneralOrder
