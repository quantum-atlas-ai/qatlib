/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3
import Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel.CostLedger

set_option backward.isDefEq.respectTransparency false

/-!
# The walk-search framework of Section 3 (Theorems 3.1 and 3.3)

Fixed source: arXiv:1302.7316v1 (2013-02-28), Childs--Jeffery--Kothari--
Magniez, *A Time-Efficient Quantum Walk for 3-Distinctness Using Nested
Updates*.

Theorem 3.1 of the paper is the MNRS walk-search theorem (MNRS 2006,
Theorem 3), specialised to a coin-dependent data structure `D`; Theorem 3.3
is its nested-update variant.  Both are proved here as bridges onto the frozen
abstract assembly

* `QuantumAlgorithm.Concepts.WalkSearch.MnrsAmplify.mnrs_search_theorem_three_abstract`
  (the MNRS Theorem 3 detection/find assembly: zero-mass exactness, success
  `≥ 1/24` on nonzero marked mass, and the order-form attempt-cost bound
  `99 · (1/√ε)((1/√δ)U + C)`),

combined with the cost ledger of `SourceModel.CostLedger`:
`walkSearchCost` for Theorem 3.1 and `nestedUpdateCost` for Theorem 3.3.

The statements keep every hypothesis of the frozen interface visible (the
reflection family `R`, the reachable slice `Rs`, the `β`-closeness bounds),
so that no physical assumption is hidden; the paper's `O(·)` becomes the
explicit constant factors `99` and `198`, which are absorbable.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalk3Dist13.MainResults.SearchFramework

open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open scoped Real BigOperators
open Qatlib.Papers.QWalk3Dist13.MainResults.SourceModel

/-- **Theorem 3.1** (fixed arXiv:1302.7316v1, p.7, statement on p.6).
With `S` the setup cost, `U` the update cost and `C` the checking cost of a
coin-dependent data structure for the chain, and marked mass at least `ε`,
the quantised walk finds a marked element with bounded error (success at least
`1/24`) and total cost at most `99 (S + ε^{-1/2}(δ^{-1/2}U + C))`, i.e.
`99 · walkSearchCost S U C δ ε`.

The algorithm and its success analysis are exactly the MNRS Theorem 3
assembly `mnrs_search_theorem_three_abstract`; the new content proved here is
the combination with the `S` setup term and the paper's cost expression. -/
theorem theorem_3_1
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmass : markedMass Mr x₀ ≠ 0 → ε ≤ markedMass Mr x₀)
    (tMax : ℕ) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (c₁ c₂ : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (costR : ℕ → ℝ) (costMark : ℝ) (Rs : Submodule ℂ W)
    (hxRs : x₀ ∈ Rs)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt (1 / 72) i * ‖ψ‖)
    (hcost : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      costR i ≤ c₁ * Real.log (1 / betaAt (1 / 72) i))
    (hmark : costMark ≤ c₂)
    (hwin : 3 ^ tMax * Real.arcsin (Real.sqrt ε) ∈ Set.Icc (π / 4) (3 * π / 4))
    (hmin : ∀ j, j < tMax →
      3 ^ j * Real.arcsin (Real.sqrt ε) ∉ Set.Icc (π / 4) (3 * π / 4))
    (S U C δ : ℝ) (hS : 0 ≤ S) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hU : 0 ≤ U)
    (hcU : c₁ ≤ 2 * U / Real.sqrt δ) (hcc : c₂ ≤ C) :
    (markedMass Mr x₀ = 0 →
        tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1) = 0) ∧
      (markedMass Mr x₀ ≠ 0 →
        (1 : ℝ) / 24 ≤
          tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1)) ∧
      S + (∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i) ≤
        99 * walkSearchCost S U C δ ε := by
  have h := mnrs_search_theorem_three_abstract W Mr unmarkRefl hMneg hMid x₀ hx₀
    ε hε hε1 hmass tMax R c₁ c₂ hc₁ hc₂ costR costMark Rs hxRs hclose hRRs hfix
    hbound hcost hmark hwin hmin
  refine ⟨h.1, h.2.1, ?_⟩
  have hcost99 := h.2.2.2 U C δ hδ hδ1 hC hcU hcc
  have hK : 0 ≤ (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C) := by
    have hεs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hδs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
    positivity
  unfold walkSearchCost
  linarith only [hcost99, hS, hK]

/-- **Theorem 3.3** (fixed arXiv:1302.7316v1, p.8, statement on p.7).
Nested updates: if the data structure for the outer walk is itself maintained by
an inner walk-search whose setup cost is `S'`, whose update cost is `T` and whose
inner walk cost is `innerWalkCost U' C' ε' δ' = ε'^{-1/2}(δ'^{-1/2}U' + C')`,
then the composed algorithm succeeds with bounded error and its cost is at most
`198 · nestedUpdateCost SC S' T CC U' C' δ ε ε' δ'`.

Note on the transcription: the metadata statement of this claim renders the
outer factor as `1/√ε` twice; the PDF (p.8) displays
`S_C + S' + (1/√ε)((1/√δ)((1/√ε')((1/√δ')U' + C') + T) + C_C)`, which is the
expression formalised in `nestedUpdateCost`.  The proof is the paper's: apply
Theorem 3.1 to the data-augmented walk, whose setup cost is
`SC + S' + inner`, whose update cost is `T + inner` and whose checking cost is
`CC` (p.9), and evaluate `walkSearchCost` (this is `nested_cost_eq` and
`theorem_3_3_cost` from `SourceModel.CostLedger`). -/
theorem theorem_3_3
    (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W)
    (hMneg : ∀ z ∈ Mr, unmarkRefl z = -z)
    (hMid : ∀ z ∈ Mrᗮ, unmarkRefl z = z)
    (x₀ : W) (hx₀ : ‖x₀‖ = 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmass : markedMass Mr x₀ ≠ 0 → ε ≤ markedMass Mr x₀)
    (tMax : ℕ) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (c₁ c₂ : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (costR : ℕ → ℝ) (costMark : ℝ) (Rs : Submodule ℂ W)
    (hxRs : x₀ ∈ Rs)
    (hclose : ∀ z ∈ Rs, markProj Mr z ∈ Rs)
    (hRRs : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ z ∈ Rs, R i z ∈ Rs)
    (hfix : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1))
    (hbound : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt (1 / 72) i * ‖ψ‖)
    (hcost : ∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      costR i ≤ c₁ * Real.log (1 / betaAt (1 / 72) i))
    (hmark : costMark ≤ c₂)
    (hwin : 3 ^ tMax * Real.arcsin (Real.sqrt ε) ∈ Set.Icc (π / 4) (3 * π / 4))
    (hmin : ∀ j, j < tMax →
      3 ^ j * Real.arcsin (Real.sqrt ε) ∉ Set.Icc (π / 4) (3 * π / 4))
    (SC S' T CC U' C' δ ε' δ' : ℝ)
    (hSC : 0 ≤ SC) (hS' : 0 ≤ S') (hT : 0 ≤ T) (hCC : 0 ≤ CC)
    (hU' : 0 ≤ U') (hC' : 0 ≤ C') (hε' : 0 < ε') (hδ' : 0 < δ')
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcU : c₁ ≤ 2 * (T + innerWalkCost U' C' ε' δ') / Real.sqrt δ)
    (hcc : c₂ ≤ CC) :
    (markedMass Mr x₀ = 0 →
        tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1) = 0) ∧
      (markedMass Mr x₀ ≠ 0 →
        (1 : ℝ) / 24 ≤
          tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1)) ∧
      (SC + S' + innerWalkCost U' C' ε' δ') +
          (∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i) ≤
        198 * nestedUpdateCost SC S' T CC U' C' δ ε ε' δ' := by
  have hI : 0 ≤ innerWalkCost U' C' ε' δ' :=
    innerWalkCost_nonneg hU' hC' hε' hδ'
  have hU : 0 ≤ T + innerWalkCost U' C' ε' δ' := by linarith
  have hmass' : markedMass Mr x₀ ≠ 0 → ε ≤ markedMass Mr x₀ := hmass
  have h := theorem_3_1 W Mr unmarkRefl hMneg hMid x₀ hx₀ ε hε hε1 hmass'
    tMax R c₁ c₂ hc₁ hc₂ costR costMark Rs hxRs hclose hRRs hfix hbound hcost
    hmark hwin hmin (SC + S' + innerWalkCost U' C' ε' δ')
    (T + innerWalkCost U' C' ε' δ') CC δ
    (by linarith) hδ hδ1 hCC hU hcU hcc
  refine ⟨h.1, h.2.1, ?_⟩
  have hbridge := h.2.2
  have hstep : walkSearchCost (SC + S' + innerWalkCost U' C' ε' δ')
      (T + innerWalkCost U' C' ε' δ') CC δ ε ≤
      2 * nestedUpdateCost SC S' T CC U' C' δ ε ε' δ' :=
    theorem_3_3_cost SC S' T CC U' C' δ ε ε' δ' hSC hS' hT hCC hU' hC'
      hε hε1 hδ hδ1 hε' hδ'
  linarith only [hbridge, hstep]

end Qatlib.Papers.QWalk3Dist13.MainResults.SearchFramework
