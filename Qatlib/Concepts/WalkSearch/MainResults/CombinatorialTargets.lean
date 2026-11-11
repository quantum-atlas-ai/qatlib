/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialCallScopes

/-!
# Corrected combinatorial triangle search targets

`sourceFourTermBudget` records the four real power terms in the combinatorial query estimate.
`theorem1SourceCorrected` and its dense specialization specify soundness, a finite rejection
count bound, and an explicit query budget, conditional on the search capabilities and positive
rounded thresholds. For background on quantum search and amplitude amplification, see
[BrassardEtAl2002].

## Main statements

* `sourceFourTermBudget`: The sum `n^(1 + ε) + n^(1 + δ + ε') + n^((3 - ε') / 2) + n^((3 - min δ
  (ε - δ - ε')) / 2)` of the four query budget terms.
* `theorem1DenseSourceCorrected`: The specialization with exponents `ε = 3 / 7` and `δ = ε' = 1
  / 7`, retaining soundness and the rejection bound and replacing the four term factor by `4 *
  n^(10 / 7)`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical

/-- The sum `n^(1 + ε) + n^(1 + δ + ε') + n^((3 - ε') / 2) + n^((3 - min δ (ε - δ - ε')) / 2)`
of the four query budget terms. -/
def sourceFourTermBudget (n : ℕ) (ε δ ε' : ℝ) : ℝ :=
  (n:ℝ)^(1+ε)+(n:ℝ)^(1+δ+ε')+(n:ℝ)^((3-ε')/2)+(n:ℝ)^((3-min δ (ε-δ-ε'))/2)

/-- The capability conditional triangle search statement with soundness, rejection count at most
`2 / n` of all tapes, and a four term query budget including explicit fee and logarithmic
factors. -/
def theorem1SourceCorrected : Prop :=
  ∀ (n : ℕ) (ε δ ε' : ℝ),0< n → 0<ε → ε<1 → 0<δ → 0<ε' → δ+ε'≤ε →
    ∀ (G : UGraph n) (family : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily),
    3≤ family.cExp → 3≤ ets.cExp →
    let k:=Nat.ceil (4*(n:ℝ)^ε*(Nat.log 2 n+1))
    let K:=64*(Nat.log 2 n+2)
    let c:=Nat.ceil ((n:ℝ)^δ)
    let dHi:=10*Nat.ceil ((n:ℝ)^(1-δ))
    let dLo:=Nat.floor ((n:ℝ)^(1-δ)/10)
    let τ:=Nat.ceil ((n:ℝ)^(1-ε'))
    let tThin:=Nat.floor ((n:ℝ)^(1-ε))
    let sgs:=sourceSearchExecution family n τ
    0< k → 0< c → 1≤ dLo →
    sourceCombSound G sgs ets k K c dHi dLo τ tThin ∧
    (letI:=sgs.seedFin
     letI:=ets.seedFin n
     1≤ triCount G.edges →
       (Finset.univ.filter (sourceCombRejects G sgs ets k K c dHi dLo τ tThin)).card*n≤
         2*Fintype.card (sourceCombTape n k K c sgs ets)) ∧
    (∀ t : sourceCombTape n k K c sgs ets,
      ((Qatlib.Concepts.WalkSearch.MainResults.CombOut.queries (sourceCombAlg G sgs ets k K c dHi dLo τ tThin t)):ℝ)≤
        ((2^24:ℕ)*sourceCapabilityFeeFactor family ets*(Nat.log 2 n+2)^4:ℕ)*sourceFourTermBudget n ε δ ε')

/-- The specialization with exponents `ε = 3 / 7` and `δ = ε' = 1 / 7`, retaining soundness and
the rejection bound and replacing the four term factor by `4 * n^(10 / 7)`. -/
def theorem1DenseSourceCorrected : Prop :=
  ∀ (n : ℕ),0< n → ∀ (G : UGraph n) (family : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily),
    3≤ family.cExp → 3≤ ets.cExp →
    let k:=Nat.ceil (4*(n:ℝ)^(3/7:ℝ)*(Nat.log 2 n+1))
    let K:=64*(Nat.log 2 n+2)
    let c:=Nat.ceil ((n:ℝ)^(1/7:ℝ))
    let dHi:=10*Nat.ceil ((n:ℝ)^(6/7:ℝ))
    let dLo:=Nat.floor ((n:ℝ)^(6/7:ℝ)/10)
    let τ:=Nat.ceil ((n:ℝ)^(6/7:ℝ))
    let tThin:=Nat.floor ((n:ℝ)^(4/7:ℝ))
    let sgs:=sourceSearchExecution family n τ
    0< k → 0< c → 1≤ dLo →
    sourceCombSound G sgs ets k K c dHi dLo τ tThin ∧
    (letI:=sgs.seedFin
     letI:=ets.seedFin n
     1≤ triCount G.edges →
       (Finset.univ.filter (sourceCombRejects G sgs ets k K c dHi dLo τ tThin)).card*n≤
         2*Fintype.card (sourceCombTape n k K c sgs ets)) ∧
    (∀ t : sourceCombTape n k K c sgs ets,
      ((Qatlib.Concepts.WalkSearch.MainResults.CombOut.queries (sourceCombAlg G sgs ets k K c dHi dLo τ tThin t)):ℝ)≤
        ((2^24:ℕ)*sourceCapabilityFeeFactor family ets*(Nat.log 2 n+2)^4:ℕ)*(4*(n:ℝ)^(10/7:ℝ)))
end Qatlib.Concepts.WalkSearch.MainResults
