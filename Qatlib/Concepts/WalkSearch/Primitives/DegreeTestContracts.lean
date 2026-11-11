/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleSearchCorrectedDefinitions

/-!
# Contracts for corrected degree tests

Defines finite counting contracts for the corrected repeated degree test with logarithmic round
count and sample size `Nat.ceil ((n : ℝ) ^ δ)`. Both high- and low-degree errors are required to
occupy at most a `1 / n ^ 3` fraction of tapes, with separate versions for positive `n` and for
`n ≥ 64`; see [Ambainis2005].

## Main statements

* `fact2DegreeTestCorrected`: For `n ≥ 64` and `0 < δ < 1`, the prescribed repeated degree test
  has high-to-low and low-to-high error-event counts whose products with `n ^ 3` do not exceed
  the total tape count.
* `fact2DegreeTestAllPositive`: The corrected degree-test error-count contract for every `n > 0`
  and `0 < δ < 1`, using the prescribed logarithmic number of rounds and sample size.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- For `n ≥ 64` and `0 < δ < 1`, the prescribed repeated degree test has high-to-low and
low-to-high error-event counts whose products with `n ^ 3` do not exceed the total tape
count. -/
def fact2DegreeTestCorrected : Prop :=
  ∀ (n : ℕ) (δ : ℝ),64≤n→0<δ→δ<1→
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    0<c→∀ (G : UGraph n) (v : Fin n),
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n) ∧
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n)

/-- The corrected degree-test error-count contract for every `n > 0` and `0 < δ < 1`, using the
prescribed logarithmic number of rounds and sample size. -/
def fact2DegreeTestAllPositive : Prop :=
  ∀ (n : ℕ) (δ : ℝ),0<n→0<δ→δ<1→
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    0<c→∀ (G : UGraph n) (v : Fin n),
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n) ∧
      ((Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
        degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)).card:ℕ)*n^3≤Fintype.card (Fin K→Fin c→Fin n)

end Qatlib.Concepts.WalkSearch.Primitives
