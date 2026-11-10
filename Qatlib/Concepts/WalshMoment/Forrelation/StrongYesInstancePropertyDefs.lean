/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.StrongDistributionAuxiliary
import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder
set_option warningAsError false

open Qatlib
open scoped BigOperators
open Classical

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

namespace Qatlib.Concepts.WalshMoment.Forrelation

def multisetInd {n ℓ : ℕ} (s : Fin ℓ → Reg n) : Reg n → Bool :=
  fun x => decide (∃ i : Fin ℓ, s i = x)

def supportCard {n : ℕ} (Δ : Reg n → Bool) : ℕ :=
  (Finset.univ.filter fun x : Reg n => Δ x).card

def IsStrongYes {n : ℕ} (t1 t2 : ℝ) (v : ℕ) (S U : Reg n → Bool) : Prop :=
  t2 ≤ spectralForrelation n S U ∧
    ∀ Δ : Reg n → Bool, (∀ x, Δ x → S x) → supportCard Δ ≤ v →
      spectralForrelation n Δ U ≤ t1

noncomputable def strongFailProb (n ℓ : ℕ) (κ t1 t2 : ℝ) (v : ℕ) : ℝ :=
  (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
    ∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
      strongBernoulliWeight n ℓ κ s u *
        (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)
end Qatlib.Concepts.WalshMoment.Forrelation
