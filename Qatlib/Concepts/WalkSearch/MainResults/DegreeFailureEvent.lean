/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.DegreeConcentration

/-!
# Finite failure counts for degree tests

`degreeTest_failure_card_positive` expresses the corrected degree test error guarantee as an
integer cardinality inequality. It uses the prescribed logarithmic repetition count and rounded
sample size; `degreeTest_failure_card` supplies the same statement under `64 ≤ n`. For
background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `degreeTest_failure_card_positive`: For positive `n`, `0 < δ < 1`, and the prescribed positive
  sample size, the number of incorrect degree test tapes times `n^3` is at most twice the total
  tape count.
* `degreeTest_failure_card`: For `64 ≤ n`, `0 < δ < 1`, and the prescribed positive sample size,
  the number of incorrect degree test tapes times `n^3` is at most twice the total tape count.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

/-- For positive `n`, `0 < δ < 1`, and the prescribed positive sample size, the number of
incorrect degree test tapes times `n^3` is at most twice the total tape count. -/
theorem degreeTest_failure_card_positive (n : ℕ) (δ : ℝ) (hn : 0<n) (hδ : 0<δ) (hδ1 : δ<1) :
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    0<c→∀ (G : UGraph n) (v : Fin n),
      (Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>¬testCorrectCorrected G v
        (10*Nat.ceil ((n:ℝ)^(1-δ))) (Nat.floor ((n:ℝ)^(1-δ)/10)) K c tape)).card*n^3≤
        2*Fintype.card (Fin K→Fin c→Fin n) := by
  intro K c hc G v
  let H:=Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
    10*Nat.ceil ((n:ℝ)^(1-δ))<degOf G.edges v ∧ degreeTestLowCorrected G v K c tape)
  let L:=Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>
    degOf G.edges v<Nat.floor ((n:ℝ)^(1-δ)/10) ∧ ¬degreeTestLowCorrected G v K c tape)
  have he : Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>¬testCorrectCorrected G v
        (10*Nat.ceil ((n:ℝ)^(1-δ))) (Nat.floor ((n:ℝ)^(1-δ)/10)) K c tape)=H∪L := by
    ext tape
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,H,L,testCorrectCorrected]
    cases degreeTestLowCorrected G v K c tape <;> simp
  have hh:=fact2DegreeTest_concentration_allPositive n δ hn hδ hδ1 hc G v
  rw [he]
  have hsum:=Nat.mul_le_mul_right (n^3) (Finset.card_union_le H L)
  change H.card*n^3≤Fintype.card (Fin K→Fin c→Fin n) ∧
      L.card*n^3≤Fintype.card (Fin K→Fin c→Fin n) at hh
  nlinarith [hh.1,hh.2]

/-- For `64 ≤ n`, `0 < δ < 1`, and the prescribed positive sample size, the number of incorrect
degree test tapes times `n^3` is at most twice the total tape count. -/
theorem degreeTest_failure_card (n : ℕ) (δ : ℝ) (hn : 64≤n) (hδ : 0<δ) (hδ1 : δ<1) :
    let K : ℕ :=64*(Nat.log 2 n+2)
    let c : ℕ :=Nat.ceil ((n:ℝ)^δ)
    0<c→∀ (G : UGraph n) (v : Fin n),
      (Finset.univ.filter (fun tape : Fin K→Fin c→Fin n=>¬testCorrectCorrected G v
        (10*Nat.ceil ((n:ℝ)^(1-δ))) (Nat.floor ((n:ℝ)^(1-δ)/10)) K c tape)).card*n^3≤
        2*Fintype.card (Fin K→Fin c→Fin n) := by
  exact degreeTest_failure_card_positive n δ (by omega) hδ hδ1
end Qatlib.Concepts.WalkSearch.MainResults
