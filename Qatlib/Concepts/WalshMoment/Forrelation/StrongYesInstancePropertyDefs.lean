/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.StrongDistributionAuxiliary
import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder

/-!
# Strong spectral yes instances and failure weights

`multisetInd` and `supportCard` describe the support of Boolean functions on registers.
`IsStrongYes` requires a large spectral forrelation value for the full support and a small value
for every sub-support of bounded size. `strongFailProb` averages the weighted failure indicator
over indexed samples and Boolean functions using `strongBernoulliWeight`.

The Boolean Fourier and quantum information background is discussed in [Roetteler,
2008][Roetteler2008] and [NielsenChuang2010].

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010].
-/

open Qatlib
open scoped BigOperators
open Classical

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

namespace Qatlib.Concepts.WalshMoment.Forrelation

/-- The Boolean indicator of the image of an indexed sample, ignoring repeated entries. -/
def multisetInd {n ℓ : ℕ} (s : Fin ℓ → Reg n) : Reg n → Bool :=
  fun x => decide (∃ i : Fin ℓ, s i = x)

/-- The number of registers on which the Boolean function `Δ` is true. -/
def supportCard {n : ℕ} (Δ : Reg n → Bool) : ℕ :=
  (Finset.univ.filter fun x : Reg n => Δ x).card

/-- The full pair `S, U` has spectral forrelation at least `t2`, while every Boolean sub-support
of `S` of size at most `v` has spectral forrelation with `U` at most `t1`. -/
def IsStrongYes {n : ℕ} (t1 t2 : ℝ) (v : ℕ) (S U : Reg n → Bool) : Prop :=
  t2 ≤ spectralForrelation n S U ∧
    ∀ Δ : Reg n → Bool, (∀ x, Δ x → S x) → supportCard Δ ≤ v →
      spectralForrelation n Δ U ≤ t1

/-- The average over indexed samples of the total strong Bernoulli weight of Boolean functions
that fail `IsStrongYes` for the sample support. -/
noncomputable def strongFailProb (n ℓ : ℕ) (κ t1 t2 : ℝ) (v : ℕ) : ℝ :=
  (1 / (Fintype.card (Fin ℓ → Reg n) : ℝ)) *
    ∑ s : Fin ℓ → Reg n, ∑ u : Reg n → Bool,
      strongBernoulliWeight n ℓ κ s u *
        (if IsStrongYes t1 t2 v (multisetInd s) u then 0 else 1)
end Qatlib.Concepts.WalshMoment.Forrelation
