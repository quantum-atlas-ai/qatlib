/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SubHypergraph13.MainResults.SourceModel
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

@[expose] public section


/-! Closed local facts from Le Gall, Nishimura and Tani, arXiv:1310.4127v2.
These facts certify finite probabilities, oracle unitarity and arithmetic;
they do not construct the nested quantum walk. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators symmDiff
open Qatlib.Papers.SubHypergraph13.MainResults

namespace Qatlib.Papers.SubHypergraph13.MainResults

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


/-- Each hypergeometric mass is nonnegative. -/
theorem hypergeomMass_nonneg (N K r j : ℕ) : 0 ≤ hypergeomMass N K r j := by
  unfold hypergeomMass
  positivity

/-- **Vandermonde normalisation.** For `K ≤ N` and `r ≤ N` the hypergeometric
masses over `j ∈ {0,…,r}` sum to one:
`∑_j C(K,j) C(N-K,r-j)/C(N,r) = 1`.
This is the paper's `Pr`-mass being a genuine probability (p.4). -/
theorem hypergeomMass_sum_eq_one (N K r : ℕ) (hK : K ≤ N) (hr : r ≤ N) :
    ∑ j ∈ Finset.range (r + 1), hypergeomMass N K r j = 1 := by
  have hNat : ∑ j ∈ Finset.range (r + 1),
      Nat.choose K j * Nat.choose (N - K) (r - j) = Nat.choose N r := by
    have h := Nat.add_choose_eq K (N - K) r
    rw [Nat.add_sub_of_le hK] at h
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => Nat.choose K a * Nat.choose (N - K) b) r] at h
    exact h.symm
  have hA : ∑ j ∈ Finset.range (r + 1),
      (Nat.choose K j : ℝ) * (Nat.choose (N - K) (r - j) : ℝ) = (Nat.choose N r : ℝ) := by
    exact_mod_cast hNat
  have hpos : (Nat.choose N r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hr).ne'
  unfold hypergeomMass
  rw [← Finset.sum_div, hA]
  exact div_self hpos


/-- Condition (d) plus `|Fⱼₖ| = fⱼₖ` bounds the inner set:
`|Γᵢⱼₖ| ≤ fⱼₖ · 11 fᵢⱼ fᵢₖ/(rᵢrⱼrₖ)`.  This is the deterministic `Mᵢⱼₖ`
consequence used in §4.4 (re-exported from `SourceModel.gammaSet_card_le`). -/
theorem pairTripleBound_gammaSet_card_le {ri rj rk fij fik fjk : ℕ}
    {Fij : Finset (Fin ri × Fin rj)} {Fik : Finset (Fin ri × Fin rk)}
    {Fjk : Finset (Fin rj × Fin rk)}
    (hFjk : Fjk.card = fjk) (hd : pairTripleBound fij fik Fij Fik Fjk) :
    (gammaSet ri rj rk Fij Fik Fjk).card ≤
      (fjk : ℝ) * (11 * (fij : ℝ) * (fik : ℝ) / ((ri : ℝ) * (rj : ℝ) * (rk : ℝ))) :=
  gammaSet_card_le hFjk hd

/-- Each left degree is bounded by the total number of pairs. -/
theorem leftDegree_le_card {ri rj : ℕ} (Fij : Finset (Fin ri × Fin rj)) (u : Fin ri) :
    leftDegree Fij u ≤ Fij.card :=
  Finset.card_filter_le _ _


/-- The 4-clique exponent is strictly below `1.883`: `241/128 < 1.883`. -/
theorem four_clique_exponent_lt : (241 : ℝ) / 128 < 1.883 := by norm_num

/-- The 4-clique exponent equals `1.8828125`. -/
theorem four_clique_exponent_value : (241 : ℝ) / 128 = 1.8828125 := by norm_num


/-- The associativity exponent is exactly `2.1125`: `169/80 = 2.1125`. -/
theorem assoc_exponent_eq : (169 : ℝ) / 80 = 2.1125 := by norm_num

/-- The associativity exponent is below `2.113`. -/
theorem assoc_exponent_lt : (169 : ℝ) / 80 < 2.113 := by norm_num


/-- The hypergraph oracle `|{u,v,w},b⟩ ↦ |{u,v,w}, b ⊕ χ_G({u,v,w})⟩` is a
unitary permutation matrix on the algorithm register.  This is the
well-definedness obligation for every query step of the Theorem 5 algorithm. -/
theorem hypergraphOracleMatrix_mem_unitaryGroup {n κ : ℕ} (G : Hypergraph3 n) :
    hypergraphOracleMatrix (n := n) (κ := κ) G ∈
      Matrix.unitaryGroup (HypergraphState n κ) ℂ := by
  unfold hypergraphOracleMatrix
  exact boolOracleMatrix_mem_unitaryGroup _


/-- The family of triples `(Fᵢⱼ, Fᵢₖ, Fⱼₖ)` with the prescribed cardinalities:
the sample space of the random loading states `R_{t₁}, R_{t₂}, R_{t₆}`. -/
def tripleSample (ri rj rk fij fik fjk : ℕ) :
    Finset ((Finset (Fin ri × Fin rj) × Finset (Fin ri × Fin rk) ×
      Finset (Fin rj × Fin rk))) :=
  ((Finset.univ : Finset (Fin ri × Fin rj)).powersetCard fij).product
    (((Finset.univ : Finset (Fin ri × Fin rk)).powersetCard fik).product
      ((Finset.univ : Finset (Fin rj × Fin rk)).powersetCard fjk))

/-- The family of pairs `(Fᵢₖ, Fⱼₖ)` with the prescribed cardinalities:
the sample space of the random loading states `R_{t₅}, R_{t₆}`. -/
def pairSample (ri rj rk fik fjk : ℕ) :
    Finset (Finset (Fin ri × Fin rk) × Finset (Fin rj × Fin rk)) :=
  ((Finset.univ : Finset (Fin ri × Fin rk)).powersetCard fik).product
    ((Finset.univ : Finset (Fin rj × Fin rk)).powersetCard fjk)



/-- A uniform counting probability is nonnegative, including the empty sample. -/
theorem uniform_nonneg {α : Type*} (S : Finset α) (P : α → Prop) :
    0 ≤ uniformEventProb S P := by
  classical
  unfold uniformEventProb
  positivity

/-- A uniform counting probability is at most one, including the empty sample. -/
theorem uniform_le_one {α : Type*} (S : Finset α) (P : α → Prop) :
    uniformEventProb S P ≤ 1 := by
  classical
  unfold uniformEventProb
  by_cases h : S.card = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).2
    exact_mod_cast Finset.card_filter_le S P

/-- A constant chosen after n makes an inverse-power bound hold for every probability.
This diagnoses the quantifier order in the old Lemmas 9 and 10. -/
theorem pointwise_bound {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : p ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ p ≤ C / (n : ℝ) ^ 100 := by
  have h : 0 < (n : ℝ) ^ 100 := pow_pos (by exact_mod_cast hn) _
  refine ⟨(n : ℝ) ^ 100, h, ?_⟩
  simpa [div_self h.ne'] using hp

end Qatlib.Papers.SubHypergraph13.MainResults
