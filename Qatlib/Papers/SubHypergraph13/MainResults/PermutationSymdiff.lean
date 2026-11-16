/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# SubHypergraph13 — permutation and symmetric difference (Lemma 6)

Fixed source: Guerreschi--Magniez--Santha, "Quantum Algorithms for Finding
Constant-sized Sub-hypergraphs", arXiv:1310.4127 (2013), **Lemma 6, page 6**.

For `Γ, Γ' ⊆ V×V×V` and `1 ≤ r ≤ p ≤ |V|³` there is a permutation `π` of
`{1,…,p}` such that, for a uniformly random `r`-subset `R ⊆ {1,…,p}`,

  `Pr_R[ |Υ(R,Γ) ∆ Υ(π(R),Γ')| ≤ 22 r |Γ∆Γ'|/p + 100 log n ]`
    `≥ 1 - 2 (1/2)^(11 r |Γ∆Γ'|/p + 50 log n)`.

`Υ` is `upsilon` (`SourceModel.lean`).  The paper's proof uses Claim 7
(`|Λ₁ ∆ Λ'₁| ≤ 2|Γ∆Γ'|`) and Lemma 2(3) (the hypergeometric far tail).
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel

@[expose] public section


set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators symmDiff
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults.PermutationSymdiff
open Qatlib.Papers.SubHypergraph13.MainResults

/-! ## Elementary structural facts about `Υ` -/

/-- `Υ` is monotone in its index set `R`. -/
theorem upsilon_mono {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}
    (Γ : Finset (V × V × V)) {R₁ R₂ : Finset (Fin p)} (h : R₁ ⊆ R₂) :
    upsilon Γ R₁ ⊆ upsilon Γ R₂ := by
  intro x hx
  simp only [upsilon, Finset.mem_filter] at hx ⊢
  obtain ⟨hxΓ, a, ha, hget⟩ := hx
  exact ⟨hxΓ, a, h ha, hget⟩

/-- The induced triple set is empty when its index set is empty. `Υ(∅, Γ) = ∅`. -/
theorem upsilon_empty {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}
    (Γ : Finset (V × V × V)) : upsilon Γ (∅ : Finset (Fin p)) = ∅ := by
  ext x
  simp [upsilon]

/-- `Υ(R, Γ) ⊆ Γ` (re-exported from the source model for local use). -/
theorem upsilon_subset' {V : Type*} [Fintype V] [DecidableEq V] {p : ℕ}
    (Γ : Finset (V × V × V)) (R : Finset (Fin p)) : upsilon Γ R ⊆ Γ :=
  upsilon_subset Γ R

/-! ## Lemma 6 (p.6) -/

/-! The remaining paper theorem requires unformalized probabilistic/circuit machinery and is intentionally omitted from this verified leaf. -/

end Qatlib.Papers.SubHypergraph13.MainResults.PermutationSymdiff
