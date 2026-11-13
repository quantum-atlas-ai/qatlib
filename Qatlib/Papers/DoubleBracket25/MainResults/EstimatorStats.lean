/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket25.MainResults.Definitions
import Qatlib.Papers.DoubleBracket25.MainResults.Supporting

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket25 — statistical estimation of observable variances

Source: arXiv:2504.01077, accepted-Quantum version 2025-12-16, Appendix F.

* `SourcePropositionF2` — Proposition F.2, Eq. (262), p. 45 (unbiased variance
  estimator for `Ô = Σᵢ wᵢPᵢ`);
* `SourceLemmaF3` — Lemma F.3, Eq. (272), p. 47 (variance of the `Ô²`
  estimator);
* `SourceLemmaF4` — Lemma F.4, Eq. (278)-(281), p. 47-48 (first four moments of
  a Pauli sample mean);
* `SourceLemmaF5` — Lemma F.5, Eq. (295), p. 50 (variance of the `⟨Ô⟩²`
  estimator);
* `SourceTheoremF6` — Theorem F.6, Eq. (321), p. 53 (variance of the variance
  estimator);
* `SourceLemmaF7` — Lemma F.7, Eq. (323), p. 53 (alternative unbiased
  estimator via joint measurements);
* `SourceLemmaF8` — Lemma F.8, Eq. (328), p. 54 (variance of the alternative
  estimator);
* `SourcePropositionF9` — Proposition F.9, Eq. (344)-(346), p. 55-56 (sample
  complexity `O(|w|₁⁴/ε²)`).

## Probabilistic model

The measurements are modelled by an abstract finite probability space
`(Ω, μ)` with `Σ_ω μ ω = 1`, random variables `Ω → ℝ`, and expectation
`finExpect μ X = Σ_ω μ ω * X ω`.  Independence assumptions appear as
hypotheses on the second moments / covariances and on factorisation of mixed
moments (the paper's `i.i.d.` assumptions).  For Lemma F.4, which concerns a
single operator and hence needs an explicit i.i.d. model, we build the product
law `iidWeight` on `Fin N → Bool` with `b_k = ±1` and `E[b_k] = p`.

The Pauli algebra itself (`Pᵢ ∈ {I,X,Y,Z}^{⊗n}`, `Pᵢⱼ = PᵢPⱼ`) enters only
through the real parameters `⟨Pᵢ⟩ ∈ [-1,1]` and `⟨Pᵢⱼ⟩`, which is exactly what
the paper's formulas (272)-(328) depend on (`⟨Pᵢⱼ⟩ = ⟨Pᵢ⟩⟨Pⱼ⟩` under the
`i.i.d.` assumption used in Lem. F.3-F.6).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.DoubleBracket25.MainResults

universe u

/-! ### Finite probability toolkit -/

/-- Expectation of `X` on a finite probability space `(Ω, μ)`. -/
def finExpect {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ ω * X ω

/-- Variance `Var[X] = E[X²] - (E[X])²`. -/
def finVar {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  finExpect μ (fun ω => (X ω) ^ 2) - (finExpect μ X) ^ 2

/-- Covariance `Cov[X,Y] = E[XY] - E[X]E[Y]`. -/
def finCov {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (X Y : Ω → ℝ) : ℝ :=
  finExpect μ (fun ω => X ω * Y ω) - finExpect μ X * finExpect μ Y

/-- Pairs of distinct indices, the index set of the products `Pᵢⱼ = PᵢPⱼ`
(the paper's `Σ_{i≠j}`). -/
def pairs (L : ℕ) : Type := {ij : Fin L × Fin L // ij.1 ≠ ij.2}

instance pairsFintype (L : ℕ) : Fintype (pairs L) :=
  Subtype.fintype _

/-- Expectation is additive. -/
theorem finExpect_add {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (X Y : Ω → ℝ) :
    finExpect μ (fun ω => X ω + Y ω) = finExpect μ X + finExpect μ Y := by
  simp only [finExpect, mul_add, Finset.sum_add_distrib]

/-- Expectation is homogeneous. -/
theorem finExpect_smul {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (c : ℝ) (X : Ω → ℝ) :
    finExpect μ (fun ω => c * X ω) = c * finExpect μ X := by
  simp only [finExpect, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- The expectation of a constant is the constant times the total mass. -/
theorem finExpect_const {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (c : ℝ) :
    finExpect μ (fun _ => c) = c * ∑ ω, μ ω := by
  simp only [finExpect]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- Expectation commutes with finite sums. -/
theorem finExpect_sum {Ω : Type u} [Fintype Ω] {ι : Type*} [Fintype ι]
    (μ : Ω → ℝ) (X : ι → Ω → ℝ) :
    finExpect μ (fun ω => ∑ i, X i ω) = ∑ i, finExpect μ (X i) := by
  simp only [finExpect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### i.i.d. ±1 sample model (Lemma F.4) -/

/-- Value of a `±1` measurement outcome. -/
def signVal : Bool → ℝ := fun b => if b then 1 else -1

/-- Single-shot law with `P(+1) = (1+p)/2`, `P(-1) = (1-p)/2`. -/
def pmfSign (p : ℝ) (b : Bool) : ℝ := if b then (1 + p) / 2 else (1 - p) / 2

/-- Product (i.i.d.) weight on `N` shots. -/
def iidWeight (p : ℝ) (N : ℕ) (s : Fin N → Bool) : ℝ :=
  ∏ k, pmfSign p (s k)

/-- The sample mean `X = (1/N) Σₖ bₖ` of Eq. (278). -/
def sampleMean (N : ℕ) (s : Fin N → Bool) : ℝ :=
  (1 / (N : ℝ)) * ∑ k, signVal (s k)

/-- Expectation under the i.i.d. product law. -/
def iidExpect (p : ℝ) (N : ℕ) (X : (Fin N → Bool) → ℝ) : ℝ :=
  ∑ s, iidWeight p N s * X s

/-! ### Estimators of Eq. (262) -/

variable {L : ℕ}

/-- Estimator of `⟨Ô²⟩`, Eq. (262)/(273): `Σᵢ wᵢ² + Σ_{i≠j} wᵢwⱼ Xᵢⱼ`. -/
def sqEst {Ω : Type u} (w : Fin L → ℝ) (Xpair : pairs L → Ω → ℝ) : Ω → ℝ :=
  fun ω => (∑ i, (w i) ^ 2) + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω

/-- Estimator of `⟨Ô⟩²`, Eq. (262)/(296). -/
def meanSqEst {Ω : Type u} (w : Fin L → ℝ) (N : Fin L → ℕ)
    (X : Fin L → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    (∑ i, (w i) ^ 2 * ((N i : ℝ) / ((N i : ℝ) - 1) * ((X i ω) ^ 2 - 1 / (N i : ℝ)))) +
      ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * X ij.val.1 ω * X ij.val.2 ω

/-- The variance estimator `V̄` of Eq. (262) = `sqEst - meanSqEst`. -/
def varEst {Ω : Type u} (w : Fin L → ℝ) (N : Fin L → ℕ)
    (X : Fin L → Ω → ℝ) (Xpair : pairs L → Ω → ℝ) : Ω → ℝ :=
  fun ω => sqEst w Xpair ω - meanSqEst w N X ω

/-- The alternative estimator `V̄` of Eq. (323), using joint measurements. -/
def varEstAlt {Ω : Type u} (w : Fin L → ℝ) (Xpair : pairs L → Ω → ℝ)
    (Xjoint : Fin L × Fin L → Ω → ℝ) : Ω → ℝ :=
  fun ω =>
    (∑ i, (w i) ^ 2) + (∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω) -
      ∑ ij : Fin L × Fin L, w ij.1 * w ij.2 * Xjoint ij ω

/-! ### Variance toolkit -/

/-- Expectation of a difference. -/
theorem finExpect_sub {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (X Y : Ω → ℝ) :
    finExpect μ (fun ω => X ω - Y ω) = finExpect μ X - finExpect μ Y := by
  simp only [finExpect, mul_sub, Finset.sum_sub_distrib]

/-- Variance of a scalar multiple: `Var[cX] = c² Var[X]`. -/
theorem finVar_smul {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (c : ℝ) (X : Ω → ℝ) :
    finVar μ (fun ω => c * X ω) = c ^ 2 * finVar μ X := by
  simp only [finVar, finExpect_smul]
  have h : ∀ ω, (c * X ω) ^ 2 = c ^ 2 * (X ω) ^ 2 := fun _ => by ring
  simp only [h]
  rw [finExpect_smul]
  ring

/-- A constant has zero variance (for a probability weight). -/
theorem finVar_const {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1) (c : ℝ) :
    finVar μ (fun _ => c) = 0 := by
  simp only [finVar, finExpect_const, hμ]
  ring

/-- Adding a constant does not change the variance. -/
theorem finVar_const_add {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (c : ℝ) (X : Ω → ℝ) : finVar μ (fun ω => c + X ω) = finVar μ X := by
  simp only [finVar, finExpect_add, finExpect_const, hμ]
  have h1 : ∀ ω, (c + X ω) ^ 2 = c ^ 2 + (2 * c) * X ω + (X ω) ^ 2 := fun _ => by ring
  simp only [h1]
  simp only [finExpect_add, finExpect_smul, finExpect_const, hμ]
  ring

/-- `Cov[X,X] = Var[X]`. -/
theorem finCov_self {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (X : Ω → ℝ) :
    finCov μ X X = finVar μ X := by
  simp only [finCov, finVar]
  have h : (fun ω => X ω * X ω) = (fun ω => (X ω) ^ 2) := by
    funext ω; ring
  rw [h]
  ring

/-- `Var` of a finite sum equals the double covariance sum. -/
theorem finVar_sum {Ω : Type u} [Fintype Ω] {κ : Type*} [Fintype κ]
    (μ : Ω → ℝ) (f : κ → Ω → ℝ) :
    finVar μ (fun ω => ∑ k, f k ω) = ∑ a, ∑ b, finCov μ (f a) (f b) := by
  have hsq : ∀ ω, (∑ k, f k ω) ^ 2 = ∑ a, ∑ b, f a ω * f b ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  simp only [finVar, hsq, finExpect_sum]
  have hcov : ∀ a b : κ, finCov μ (f a) (f b)
      = finExpect μ (fun ω => f a ω * f b ω) - finExpect μ (f a) * finExpect μ (f b) := by
    intro a b
    rfl
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hcov a b)),
    sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ =>
    (Finset.sum_sub_distrib (fun i => finExpect μ (fun ω => f x ω * f i ω))
      (fun i => finExpect μ (f x) * finExpect μ (f i))).symm

/-- Covariance of scalar multiples: `Cov[cX, dY] = c·d·Cov[X,Y]`. -/
theorem finCov_smul {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (c d : ℝ) (X Y : Ω → ℝ) :
    finCov μ (fun ω => c * X ω) (fun ω => d * Y ω) = c * d * finCov μ X Y := by
  simp only [finCov, finExpect_smul]
  have h : (fun ω => c * X ω * (d * Y ω)) = fun ω => (c * d) * (X ω * Y ω) := by
    funext ω; ring
  rw [h, finExpect_smul]
  ring

/-- Variance of a finite sum of pairwise-uncorrelated summands. -/
theorem finVar_sum_of_cov_zero {Ω : Type u} [Fintype Ω] {κ : Type*} [Fintype κ]
    (μ : Ω → ℝ) (f : κ → Ω → ℝ)
    (hunc : ∀ a b : κ, a ≠ b → finCov μ (f a) (f b) = 0) :
    finVar μ (fun ω => ∑ k, f k ω) = ∑ k, finVar μ (f k) := by
  rw [finVar_sum]
  have hsplit : ∀ a : κ, ∑ b, finCov μ (f a) (f b)
      = finVar μ (f a) + ∑ b ∈ Finset.univ \ {a}, finCov μ (f a) (f b) := by
    intro a
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a), finCov_self]
    · rw [Finset.sum_eq_zero fun b hb => hunc a b
        (fun h => (Finset.mem_sdiff.mp hb).2 (by simp [h]))]
      ring
    · exact fun b _ hne => hunc a b (Ne.symm hne)
  rw [Finset.sum_congr rfl (fun a _ => hsplit a), Finset.sum_add_distrib]
  have hzero : (∑ a, ∑ b ∈ Finset.univ \ {a}, finCov μ (f a) (f b)) = 0 :=
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b hb => hunc a b
      (fun h => (Finset.mem_sdiff.mp hb).2 (by simp [h]))
  rw [hzero]
  ring

/-- The `pairs L` sum reindexed over the off-diagonal part of the square
index set: `∑_{i≠j} f i j = ∑ i, ∑ j ∈ univ \ {i}, f i j`. -/
theorem sum_pairs_eq_offdiag {L : ℕ} (f : Fin L → Fin L → ℝ) :
    ∑ ij : pairs L, f ij.val.1 ij.val.2 = ∑ i, ∑ j ∈ Finset.univ \ {i}, f i j := by
  classical
  have hmem : ∀ x : Fin L × Fin L,
      x ∈ Finset.univ.filter (fun q : Fin L × Fin L => q.1 ≠ q.2) ↔ x.1 ≠ x.2 := by
    intro x; simp [Finset.mem_filter]
  have hL : ∑ p ∈ Finset.univ.filter (fun q : Fin L × Fin L => q.1 ≠ q.2), f p.1 p.2
      = ∑ ij : pairs L, f ij.val.1 ij.val.2 :=
    Finset.sum_subtype
      (Finset.univ.filter (fun q : Fin L × Fin L => q.1 ≠ q.2)) hmem (fun p => f p.1 p.2)
  have hmid : ∑ p ∈ Finset.univ.filter (fun q : Fin L × Fin L => q.1 ≠ q.2), f p.1 p.2
      = ∑ i, ∑ j, (if j ≠ i then f i j else 0) := by
    rw [Finset.sum_filter, ← Fintype.sum_prod_type' (α₁ := Fin L) (α₂ := Fin L)
      (fun i j => (if j ≠ i then f i j else 0 : ℝ))]
    exact Finset.sum_congr rfl fun p _ => by
      by_cases h : p.1 = p.2
      · simp [h]
      · simp [h, ne_comm]
  have hRstep : ∀ i : Fin L, ∑ j ∈ Finset.univ \ {i}, f i j
      = ∑ j, (if j ≠ i then f i j else 0) := by
    intro i
    rw [show Finset.univ \ {i} = Finset.univ.filter (fun j => j ≠ i) from by
      ext j; simp [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton],
      Finset.sum_filter]
  rw [hL.symm, hmid, Finset.sum_congr rfl (fun i _ => (hRstep i).symm)]

/-- Diagonal/off-diagonal split of a squared finite sum:
`(∑ i, a i)² = ∑ i, (a i)² + ∑_{i≠j} a i * a j`. -/
theorem sum_sq_split {L : ℕ} (a : Fin L → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + ∑ ij : pairs L, a ij.val.1 * a ij.val.2 := by
  have hdiag : ∀ i : Fin L, ∑ j, a i * a j
      = a i * a i + ∑ j ∈ Finset.univ \ {i}, a i * a j := by
    intro i
    conv_lhs => rw [show (Finset.univ : Finset (Fin L)) = insert i (Finset.univ.erase i) from
      (Finset.insert_erase (Finset.mem_univ i)).symm]
    rw [Finset.sum_insert (by simp [Finset.mem_erase]),
      Finset.sdiff_singleton_eq_erase i Finset.univ]
  rw [sq, Finset.sum_mul_sum, sum_pairs_eq_offdiag (fun i j => a i * a j),
    Finset.sum_congr rfl (fun i _ => hdiag i), Finset.sum_add_distrib]
  have hfirst : (∑ x, a x * a x) = (∑ i, a i ^ 2) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [hfirst]


/-! ### Prop. F.2 -/

/-- **Proposition F.2** (arXiv:2504.01077, App. F.2, Eq. (262), p. 45).
*Unbiased estimator of the observable variance.*

For `Ô = Σᵢ wᵢPᵢ`, with `Xᵢ` the `Nᵢ`-shot estimator of `⟨Pᵢ⟩` and `Xᵢⱼ` the
`Nᵢⱼ`-shot estimator of `⟨Pᵢⱼ⟩`, if `E[Xᵢ] = ⟨Pᵢ⟩`,
`E[Xᵢ²] = ⟨Pᵢ⟩² + (1-⟨Pᵢ⟩²)/Nᵢ`, and `E[Xᵢⱼ] = ⟨Pᵢⱼ⟩`, then the estimator
`V̄` of Eq. (262) is unbiased:

`E[V̄] = Σᵢ wᵢ² + Σ_{i≠j} wᵢwⱼ⟨Pᵢⱼ⟩ - (Σᵢ wᵢ⟨Pᵢ⟩)² = Var[Ô]`.

The hypothesis `hcross` records the paper's implicit i.i.d. assumption
`E[XᵢXⱼ] = ⟨Pᵢ⟩⟨Pⱼ⟩` for `i ≠ j`, needed by the `XᵢXⱼ` block of the
`⟨Ô⟩²` estimator in Eq. (262). -/
theorem SourcePropositionF2
    (w : Fin L → ℝ) (p : Fin L → ℝ) (pij : pairs L → ℝ)
    (N : Fin L → ℕ) (hN : ∀ i, 1 < N i)
    {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (X : Fin L → Ω → ℝ) (Xpair : pairs L → Ω → ℝ)
    (hX : ∀ i, finExpect μ (X i) = p i)
    (hX2 : ∀ i, finExpect μ (fun ω => (X i ω) ^ 2) =
      (p i) ^ 2 + (1 - (p i) ^ 2) / (N i : ℝ))
    (hXpair : ∀ ij, finExpect μ (Xpair ij) = pij ij)
    (hcross : ∀ i j : Fin L, i ≠ j →
      finExpect μ (fun ω => X i ω * X j ω) = p i * p j) :
    finExpect μ (varEst w N X Xpair) =
      (∑ i, (w i) ^ 2) + (∑ ij : pairs L, w ij.val.1 * w ij.val.2 * pij ij) -
        (∑ i, w i * p i) ^ 2 := by
  -- Expectation of the `⟨Ô²⟩` block of Eq. (262).
  have hE1 : finExpect μ (sqEst w Xpair)
      = (∑ i, (w i) ^ 2)
        + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * pij ij := by
    have hc : finExpect μ (fun _ => ∑ i, (w i) ^ 2) = (∑ i, (w i) ^ 2) * 1 := by
      rw [finExpect_const, hμ]
    have hs : finExpect μ (fun ω => ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω)
        = ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * pij ij := by
      rw [finExpect_sum]
      exact Finset.sum_congr rfl fun ij _ => by rw [finExpect_smul, hXpair ij]
    show finExpect μ (fun ω => (∑ i, (w i) ^ 2)
        + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω) = _
    rw [finExpect_add, hc, hs]
    ring
  -- Expectation of the `⟨Ô⟩²` block of Eq. (262): the bias correction of
  -- Eq. (260)-(261) makes the diagonal terms unbiased.
  have hcross' : ∀ ij : pairs L,
      finExpect μ (fun ω => X ij.val.1 ω * X ij.val.2 ω)
        = p ij.val.1 * p ij.val.2 := fun ij => hcross ij.val.1 ij.val.2 ij.property
  have hE2 : finExpect μ (meanSqEst w N X)
      = (∑ i, (w i) ^ 2 * (p i) ^ 2)
        + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * (p ij.val.1 * p ij.val.2) := by
    have hEc : ∀ i : Fin L,
        finExpect μ (fun ω => (X i ω) ^ 2 - 1 / (N i : ℝ))
          = (p i) ^ 2 + (1 - (p i) ^ 2) / (N i : ℝ) - 1 / (N i : ℝ) := by
      intro i
      rw [finExpect_sub, finExpect_const, hμ, hX2 i]
      ring
    have hA : finExpect μ (fun ω => ∑ i, (w i) ^ 2 *
          ((N i : ℝ) / ((N i : ℝ) - 1) * ((X i ω) ^ 2 - 1 / (N i : ℝ))))
        = ∑ i, (w i) ^ 2 * (p i) ^ 2 := by
      rw [finExpect_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [finExpect_smul, finExpect_smul, hEc i]
      have h := unbiasedCorrection (p i) (N i) (hN i)
      nlinarith [h]
    have hB : finExpect μ (fun ω => ∑ ij : pairs L,
          w ij.val.1 * w ij.val.2 * X ij.val.1 ω * X ij.val.2 ω)
        = ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * (p ij.val.1 * p ij.val.2) := by
      rw [finExpect_sum]
      refine Finset.sum_congr rfl fun ij _ => ?_
      have hfun : (fun ω => w ij.val.1 * w ij.val.2 * X ij.val.1 ω * X ij.val.2 ω)
          = fun ω => (w ij.val.1 * w ij.val.2) * (X ij.val.1 ω * X ij.val.2 ω) := by
        funext ω; ring
      rw [hfun, finExpect_smul, hcross' ij]
    show finExpect μ (fun ω => (∑ i, (w i) ^ 2 *
          ((N i : ℝ) / ((N i : ℝ) - 1) * ((X i ω) ^ 2 - 1 / (N i : ℝ))))
        + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * X ij.val.1 ω * X ij.val.2 ω) = _
    rw [finExpect_add, hA, hB]
  -- Combine through linearity and the diagonal/off-diagonal split.
  show finExpect μ (fun ω => sqEst w Xpair ω - meanSqEst w N X ω) = _
  rw [finExpect_sub, hE1, hE2]
  -- Collect via the diagonal/off-diagonal split of `(Σᵢ wᵢ⟨Pᵢ⟩)²`.
  have hkey : (∑ i, w i * p i) ^ 2
      = (∑ i, (w i) ^ 2 * (p i) ^ 2)
        + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * (p ij.val.1 * p ij.val.2) := by
    rw [sum_sq_split (fun i => w i * p i)]
    have h1 : (∑ i, (w i * p i) ^ 2) = ∑ i, (w i) ^ 2 * (p i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    have h2 : (∑ ij : pairs L, (w ij.val.1 * p ij.val.1) * (w ij.val.2 * p ij.val.2))
        = ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * (p ij.val.1 * p ij.val.2) :=
      Finset.sum_congr rfl fun ij _ => by ring
    rw [h1, h2]
  rw [← hkey]

/-! ### Lemma F.3 -/

/-- **Lemma F.3** (arXiv:2504.01077, App. F.3, Eq. (272), p. 47).
*Variance of the `⟨Ô²⟩` estimator.*

Under i.i.d. measurements, with pairwise-uncorrelated pair-estimators and
`⟨Pᵢⱼ⟩ = ⟨Pᵢ⟩⟨Pⱼ⟩`,

`Var[⟨Ô²⟩] = Σ_{i≠j} (wᵢ²wⱼ²/Nᵢⱼ)(1 - ⟨Pᵢⱼ⟩²)`. -/
theorem SourceLemmaF3
    (w : Fin L → ℝ) (p : Fin L → ℝ)
    (Nij : pairs L → ℕ) (hNij : ∀ ij, 0 < Nij ij)
    {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (Xpair : pairs L → Ω → ℝ)
    (hmean : ∀ ij, finExpect μ (Xpair ij) = p ij.val.1 * p ij.val.2)
    (hsecond : ∀ ij, finExpect μ (fun ω => (Xpair ij ω) ^ 2) =
      (p ij.val.1 * p ij.val.2) ^ 2 +
        (1 - (p ij.val.1 * p ij.val.2) ^ 2) / (Nij ij : ℝ))
    (huncorr : ∀ ij kl : pairs L, ij ≠ kl →
      finCov μ (Xpair ij) (Xpair kl) = 0) :
    finVar μ (sqEst w Xpair) =
      ∑ ij : pairs L,
        (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 / (Nij ij : ℝ) *
          (1 - (p ij.val.1 * p ij.val.2) ^ 2) := by
  -- Drop the constant `Σᵢ wᵢ²` (Eq. (274)).
  show finVar μ (fun ω => (∑ i, (w i) ^ 2)
      + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω) = _
  rw [finVar_const_add μ hμ]
  -- Additivity of the variance across the uncorrelated pair terms (Eq. (275)).
  have hunc' : ∀ a b : pairs L, a ≠ b →
      finCov μ (fun ω => w a.val.1 * w a.val.2 * Xpair a ω)
        (fun ω => w b.val.1 * w b.val.2 * Xpair b ω) = 0 := by
    intro a b hab
    rw [finCov_smul, huncorr a b hab]
    ring
  rw [finVar_sum_of_cov_zero μ _ hunc']
  -- Per-pair: `Var[aX] = a²Var[X]` and `Var[Xᵢⱼ] = (1-⟨Pᵢⱼ⟩²)/Nᵢⱼ` (Eq. (276)-(277)).
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [finVar_smul]
  have hV : finVar μ (Xpair ij)
      = (1 - (p ij.val.1 * p ij.val.2) ^ 2) / (Nij ij : ℝ) := by
    show finExpect μ (fun ω => (Xpair ij ω) ^ 2)
        - (finExpect μ (Xpair ij)) ^ 2 = _
    rw [hsecond ij, hmean ij]
    ring
  rw [hV]
  ring

/-! ### Raw moments of the i.i.d. ±1 sum (Lemma F.4 machinery) -/

/-- The raw ±1 sum `S_N = Σₖ bₖ` whose moments Lemma F.4 computes. -/
def rawSum (N : ℕ) (s : Fin N → Bool) : ℝ := ∑ k, signVal (s k)

/-- Splitting a function `Fin (N+1) → Bool` into its first `N` values and its
last value, via `Fin.snoc`. -/
def snocEquiv (N : ℕ) : ((Fin N → Bool) × Bool) ≃ (Fin (N + 1) → Bool) where
  toFun x := Fin.snoc x.1 x.2
  invFun s := (fun i => s i.castSucc, s (Fin.last N))
  left_inv x := by
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  right_inv s := by
    funext j
    cases j using Fin.lastCases <;> simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Splitting a sum over `Fin (N+1) → Bool` along the last coordinate. -/
theorem sum_snoc_split (N : ℕ) (F : (Fin (N+1) → Bool) → ℝ) :
    ∑ s, F s = ∑ t : Fin N → Bool, ∑ b : Bool, F (Fin.snoc t b) :=
  ((Fintype.sum_equiv (snocEquiv N) _ F (fun _ => rfl)).symm).trans
    (Fintype.sum_prod_type _)

/-- The expectation over `N+1` shots splits along the last shot. -/
theorem iidExpect_snoc (p : ℝ) (N : ℕ) (g : (Fin (N+1) → Bool) → ℝ) :
    iidExpect p (N+1) g
      = ∑ b : Bool, pmfSign p b * iidExpect p N (fun t => g (Fin.snoc t b)) := by
  simp only [iidExpect, iidWeight]
  rw [sum_snoc_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hw : ∏ k, pmfSign p ((Fin.snoc t b : Fin (N+1) → Bool) k)
      = (∏ k, pmfSign p (t k)) * pmfSign p b := by
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snoc_castSucc, Fin.snoc_last, mul_comm]
  rw [hw]
  ring

/-- The i.i.d. product weights sum to one. -/
theorem iidWeight_total (p : ℝ) (N : ℕ) : ∑ t, iidWeight p N t = 1 := by
  induction N with
  | zero => simp [iidWeight]
  | succ n ih =>
      rw [sum_snoc_split n (iidWeight p (n+1))]
      have hw : ∀ (t : Fin n → Bool) (b : Bool), iidWeight p (n+1) (Fin.snoc t b)
          = (∏ k, pmfSign p (t k)) * pmfSign p b := by
        intro t b
        simp only [iidWeight]
        rw [Fin.prod_univ_castSucc]
        simp [Fin.snoc_castSucc, Fin.snoc_last, mul_comm]
      have hin : ∀ t : Fin n → Bool, ∑ b : Bool, (∏ k, pmfSign p (t k)) * pmfSign p b
          = ∏ k, pmfSign p (t k) := by
        intro t
        rw [← Finset.mul_sum]
        simp [pmfSign]
        ring
      rw [Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun b _ => hw t b)),
        Finset.sum_congr rfl (fun t _ => hin t)]
      rw [show (∑ t : Fin n → Bool, ∏ k, pmfSign p (t k)) = ∑ t, iidWeight p n t from
        Finset.sum_congr rfl fun t _ => rfl, ih]

/-- Expectation of `X + c`. -/
theorem finExpect_shift1 {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (c : ℝ) :
    finExpect μ (fun ω => X ω + c) = finExpect μ X + c := by
  have hexp : ∀ ω, X ω + c = 1 * X ω + c * 1 := fun _ => by ring
  simp only [hexp]
  rw [finExpect_add, finExpect_smul, finExpect_const, hμ]
  ring

/-- Expectation of `(X + c)²`. -/
theorem finExpect_shift2 {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (c : ℝ) :
    finExpect μ (fun ω => (X ω + c) ^ 2)
      = finExpect μ (fun ω => (X ω) ^ 2) + 2 * c * finExpect μ X + c ^ 2 := by
  have hexp : ∀ ω, (X ω + c) ^ 2
      = 1 * (X ω) ^ 2 + (2 * c) * X ω + c ^ 2 * 1 := fun _ => by ring
  simp only [hexp]
  rw [finExpect_add, finExpect_add, finExpect_smul, finExpect_smul,
    finExpect_const, hμ]
  ring

/-- Expectation of `(X + c)³`. -/
theorem finExpect_shift3 {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (c : ℝ) :
    finExpect μ (fun ω => (X ω + c) ^ 3)
      = finExpect μ (fun ω => (X ω) ^ 3) + 3 * c * finExpect μ (fun ω => (X ω) ^ 2)
        + 3 * c ^ 2 * finExpect μ X + c ^ 3 := by
  have hexp : ∀ ω, (X ω + c) ^ 3
      = 1 * (X ω) ^ 3 + (3 * c) * (X ω) ^ 2 + (3 * c ^ 2) * X ω + c ^ 3 * 1 :=
    fun _ => by ring
  simp only [hexp]
  rw [finExpect_add, finExpect_add, finExpect_add, finExpect_smul, finExpect_smul,
    finExpect_smul, finExpect_const, hμ]
  ring

/-- Expectation of `(X + c)⁴`. -/
theorem finExpect_shift4 {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (X : Ω → ℝ) (c : ℝ) :
    finExpect μ (fun ω => (X ω + c) ^ 4)
      = finExpect μ (fun ω => (X ω) ^ 4) + 4 * c * finExpect μ (fun ω => (X ω) ^ 3)
        + 6 * c ^ 2 * finExpect μ (fun ω => (X ω) ^ 2)
        + 4 * c ^ 3 * finExpect μ X + c ^ 4 := by
  have hexp : ∀ ω, (X ω + c) ^ 4
      = 1 * (X ω) ^ 4 + (4 * c) * (X ω) ^ 3 + (6 * c ^ 2) * (X ω) ^ 2
        + (4 * c ^ 3) * X ω + c ^ 4 * 1 := fun _ => by ring
  simp only [hexp]
  rw [finExpect_add, finExpect_add, finExpect_add, finExpect_add,
    finExpect_smul, finExpect_smul, finExpect_smul, finExpect_smul,
    finExpect_const, hμ]
  ring

/-- The raw sums satisfy `S_{N+1}(Fin.snoc t b) = S_N t + b`. -/
theorem rawSum_snoc {N : ℕ} (t : Fin N → Bool) (b : Bool) :
    rawSum (N+1) (Fin.snoc t b) = rawSum N t + signVal b := by
  simp only [rawSum]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Moment split along the last shot, for powers of the raw sum. -/
theorem iidExpect_snoc_pow (p : ℝ) (N : ℕ) (m : ℕ) :
    iidExpect p (N+1) (fun s => (rawSum (N+1) s) ^ m)
      = ∑ b : Bool, pmfSign p b * iidExpect p N (fun t => (rawSum N t + signVal b) ^ m) := by
  rw [iidExpect_snoc p N (fun s => (rawSum (N+1) s) ^ m)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hfn : (fun t => (fun s => (rawSum (N+1) s) ^ m) (Fin.snoc t b))
      = (fun t => (rawSum N t + signVal b) ^ m) := by
    funext t
    show (rawSum (N+1) (Fin.snoc t b)) ^ m = _
    rw [rawSum_snoc]
  rw [hfn]

/-- **Raw moments of the i.i.d. ±1 sum** (Lemma F.4 machinery): the first four
moments of `S_N = Σₖ bₖ` before normalizing by `N`. -/
theorem raw_moments (p : ℝ) (N : ℕ) :
    iidExpect p N (fun s => rawSum N s) = (N:ℝ) * p ∧
    iidExpect p N (fun s => (rawSum N s) ^ 2)
      = (N:ℝ) + (N:ℝ) * ((N:ℝ) - 1) * p ^ 2 ∧
    iidExpect p N (fun s => (rawSum N s) ^ 3)
      = (N:ℝ) * (3 * (N:ℝ) - 2) * p + (N:ℝ) * ((N:ℝ) - 1) * ((N:ℝ) - 2) * p ^ 3 ∧
    iidExpect p N (fun s => (rawSum N s) ^ 4)
      = (N:ℝ) * (3 * (N:ℝ) - 2) + 2 * (N:ℝ) * ((N:ℝ) - 1) * (3 * (N:ℝ) - 4) * p ^ 2
        + (N:ℝ) * ((N:ℝ) - 1) * ((N:ℝ) - 2) * ((N:ℝ) - 3) * p ^ 4 := by
  induction N with
  | zero => simp [rawSum, iidExpect, iidWeight]
  | succ n ih =>
      obtain ⟨μ1, μ2, μ3, μ4⟩ := ih
      have hb1 : ∀ b : Bool, iidExpect p n (fun t => rawSum n t + signVal b)
          = iidExpect p n (fun s => rawSum n s) + signVal b :=
        fun b => finExpect_shift1 (iidWeight p n) (iidWeight_total p n) (rawSum n) (signVal b)
      have hb2 : ∀ b : Bool, iidExpect p n (fun t => (rawSum n t + signVal b) ^ 2)
          = iidExpect p n (fun s => (rawSum n s) ^ 2)
            + 2 * signVal b * iidExpect p n (fun s => rawSum n s) + (signVal b) ^ 2 :=
        fun b => finExpect_shift2 (iidWeight p n) (iidWeight_total p n) (rawSum n) (signVal b)
      have hb3 : ∀ b : Bool, iidExpect p n (fun t => (rawSum n t + signVal b) ^ 3)
          = iidExpect p n (fun s => (rawSum n s) ^ 3)
            + 3 * signVal b * iidExpect p n (fun s => (rawSum n s) ^ 2)
            + 3 * (signVal b) ^ 2 * iidExpect p n (fun s => rawSum n s) + (signVal b) ^ 3 :=
        fun b => finExpect_shift3 (iidWeight p n) (iidWeight_total p n) (rawSum n) (signVal b)
      have hb4 : ∀ b : Bool, iidExpect p n (fun t => (rawSum n t + signVal b) ^ 4)
          = iidExpect p n (fun s => (rawSum n s) ^ 4)
            + 4 * signVal b * iidExpect p n (fun s => (rawSum n s) ^ 3)
            + 6 * (signVal b) ^ 2 * iidExpect p n (fun s => (rawSum n s) ^ 2)
            + 4 * (signVal b) ^ 3 * iidExpect p n (fun s => rawSum n s) + (signVal b) ^ 4 :=
        fun b => finExpect_shift4 (iidWeight p n) (iidWeight_total p n) (rawSum n) (signVal b)
      have s1 : iidExpect p (n+1) (fun s => rawSum (n+1) s)
          = iidExpect p n (fun s => rawSum n s) + p := by
        have hsn := iidExpect_snoc_pow p n 1
        simp only [pow_one] at hsn
        rw [hsn]
        rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => by rw [hb1 b])]
        simp [pmfSign, signVal]
        ring
      have s2 : iidExpect p (n+1) (fun s => (rawSum (n+1) s) ^ 2)
          = iidExpect p n (fun s => (rawSum n s) ^ 2)
            + 2 * p * iidExpect p n (fun s => rawSum n s) + 1 := by
        rw [iidExpect_snoc_pow p n 2]
        rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => by rw [hb2 b])]
        simp [pmfSign, signVal]
        ring
      have s3 : iidExpect p (n+1) (fun s => (rawSum (n+1) s) ^ 3)
          = iidExpect p n (fun s => (rawSum n s) ^ 3)
            + 3 * p * iidExpect p n (fun s => (rawSum n s) ^ 2)
            + 3 * iidExpect p n (fun s => rawSum n s) + p := by
        rw [iidExpect_snoc_pow p n 3]
        rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => by rw [hb3 b])]
        simp [pmfSign, signVal]
        ring
      have s4 : iidExpect p (n+1) (fun s => (rawSum (n+1) s) ^ 4)
          = iidExpect p n (fun s => (rawSum n s) ^ 4)
            + 4 * p * iidExpect p n (fun s => (rawSum n s) ^ 3)
            + 6 * iidExpect p n (fun s => (rawSum n s) ^ 2)
            + 4 * p * iidExpect p n (fun s => rawSum n s) + 1 := by
        rw [iidExpect_snoc_pow p n 4]
        rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => by rw [hb4 b])]
        simp [pmfSign, signVal]
        ring
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [s1, μ1]; push_cast; ring
      · rw [s2, μ2, μ1]; push_cast; ring
      · rw [s3, μ3, μ2, μ1]; push_cast; ring
      · rw [s4, μ4, μ3, μ2, μ1]; push_cast; ring

/-- Homogeneity of `iidExpect`. -/
theorem iidExpect_mul (p : ℝ) (N : ℕ) (c : ℝ) (F : (Fin N → Bool) → ℝ) :
    iidExpect p N (fun s => c * F s) = c * iidExpect p N F := by
  simp only [iidExpect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ### Lemma F.4 -/

/-- **Lemma F.4** (arXiv:2504.01077, App. F.3, Eq. (278)-(281), p. 47-48).
*First four moments of a single Pauli sample mean.*

For the `N`-shot mean `X = (1/N) Σₖ bₖ` of i.i.d. `±1` outcomes with
`E[bₖ] = p`:

1. `E[X] = p`;
2. `E[X²] = p² + (1-p²)/N`;
3. `E[X³] = p³(1 - 3/N + 2/N²) + p(3/N - 2/N²)`;
4. `E[X⁴] = p⁴ + 6p²(1-p²)/N + ((11p²-3)(p²-1))/N² + 2(3p²-1)(1-p²)/N³`. -/
theorem SourceLemmaF4 (p : ℝ) (hp : |p| ≤ 1) (N : ℕ) (hN : 0 < N) :
    iidExpect p N (sampleMean N) = p ∧
    iidExpect p N (fun s => (sampleMean N s) ^ 2) = p ^ 2 + (1 - p ^ 2) / (N : ℝ) ∧
    iidExpect p N (fun s => (sampleMean N s) ^ 3) =
      p ^ 3 * (1 - 3 / (N : ℝ) + 2 / (N : ℝ) ^ 2) +
        p * (3 / (N : ℝ) - 2 / (N : ℝ) ^ 2) ∧
    iidExpect p N (fun s => (sampleMean N s) ^ 4) =
      p ^ 4 + 6 * p ^ 2 * (1 - p ^ 2) / (N : ℝ) +
        ((11 * p ^ 2 - 3) * (p ^ 2 - 1)) / (N : ℝ) ^ 2 +
        2 * (3 * p ^ 2 - 1) * (1 - p ^ 2) / (N : ℝ) ^ 3 := by
  -- Proof by induction on the number of shots `N` (`raw_moments`), splitting
  -- the last sample with `Fin.snoc` (`iidExpect_snoc`), expanding
  -- `(S + b)^m` (`finExpect_shift1`..`4`), and combining the two outcomes
  -- `b = ±1` with weights `pmfSign p b`; Eq. (278)-(281) then follow by
  -- normalizing `X = S/N` (`f4_final`-style computation).
  obtain ⟨μ1, μ2, μ3, μ4⟩ := raw_moments p N
  have hNne : ((N : ℝ)) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : iidExpect p N (sampleMean N) = (1 / (N:ℝ)) * ((N:ℝ) * p) := by
    rw [show sampleMean N = (fun s => (1/(N:ℝ)) * rawSum N s) from rfl, iidExpect_mul, μ1]
  have h2 : iidExpect p N (fun s => (sampleMean N s) ^ 2)
      = (1/(N:ℝ))^2 * ((N:ℝ) + (N:ℝ) * ((N:ℝ)-1) * p^2) := by
    rw [show (fun s => (sampleMean N s)^2)
          = (fun s => (1/(N:ℝ))^2 * (rawSum N s)^2) from funext fun s => by
          show ((1/(N:ℝ)) * rawSum N s)^2 = _
          ring,
        iidExpect_mul, μ2]
  have h3 : iidExpect p N (fun s => (sampleMean N s) ^ 3)
      = (1/(N:ℝ))^3 * ((N:ℝ) * (3 * (N:ℝ) - 2) * p
          + (N:ℝ) * ((N:ℝ)-1) * ((N:ℝ)-2) * p^3) := by
    rw [show (fun s => (sampleMean N s)^3)
          = (fun s => (1/(N:ℝ))^3 * (rawSum N s)^3) from funext fun s => by
          show ((1/(N:ℝ)) * rawSum N s)^3 = _
          ring,
        iidExpect_mul, μ3]
  have h4 : iidExpect p N (fun s => (sampleMean N s) ^ 4)
      = (1/(N:ℝ))^4 * ((N:ℝ) * (3 * (N:ℝ) - 2)
          + 2 * (N:ℝ) * ((N:ℝ)-1) * (3 * (N:ℝ)-4) * p^2
          + (N:ℝ) * ((N:ℝ)-1) * ((N:ℝ)-2) * ((N:ℝ)-3) * p^4) := by
    rw [show (fun s => (sampleMean N s)^4)
          = (fun s => (1/(N:ℝ))^4 * (rawSum N s)^4) from funext fun s => by
          show ((1/(N:ℝ)) * rawSum N s)^4 = _
          ring,
        iidExpect_mul, μ4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]; field_simp
  · rw [h2]; field_simp; ring
  · rw [h3]; field_simp; ring
  · rw [h4]; field_simp; ring

/-! ### Lemma F.5 -/

/-- **Lemma F.5** (arXiv:2504.01077, App. F.4, Eq. (295), p. 50).
*Variance of the `⟨Ô⟩²` estimator* — **stated in corrected (erratum) form**.

Under i.i.d. measurements, with the per-operator moments of Lemma F.4 and
pairwise independence,

`Var[⟨Ô⟩²] = Σᵢ 2wᵢ⁴/(Nᵢ(Nᵢ-1)) (1 + 2(Nᵢ-2)pᵢ² - (2Nᵢ-3)pᵢ⁴)`
`+ 2 Σ_{i≠j} wᵢ²wⱼ² [pᵢ²(1-pⱼ²)/Nⱼ + pⱼ²(1-pᵢ²)/Nᵢ + (1-pᵢ²)(1-pⱼ²)/(NᵢNⱼ)]`
`+ 8 Σ_{i≠j} (wᵢ³wⱼ/Nᵢ) pᵢpⱼ(1-pᵢ²)`.

**Erratum.** Eq. (295) of the source states the first block with denominator
`(Nᵢ-1)²` instead of `Nᵢ(Nᵢ-1)` (its Eq. (307) numerator `4pᵢ²Nᵢ + 2(1-pᵢ²)`
does not match its own Eq. (300) moments; e.g. at `p = 0` the two disagree
already at `N = 2`), omits the `2Cov` cross block between the single-operator
and pair terms (which is not zero), and misses the factor `2` of the second
block (the ordered sum `Σ_{i≠j}` counts `XᵢXⱼ = XⱼXᵢ` twice).  The statement
above is the corrected identity, consistent with the paper's own Eq. (321)
after its analogous correction (see `SourceTheoremF6`).

The hypothesis `hVarSplit` records the three-block independence decomposition
(single-operator variances, pair variances over ordered pairs, and the
`2Cov(A,B)` cross block), the paper's "measurements are i.i.d." applied
pairwise; `hcov3` is the mixed third moment `E[Xᵢ³Xⱼ] = μ₃(Xᵢ)·pⱼ`. -/
theorem SourceLemmaF5
    (w : Fin L → ℝ) (p : Fin L → ℝ) (hp : ∀ i, |p i| ≤ 1)
    (N : Fin L → ℕ) (hN : ∀ i, 1 < N i)
    {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (X : Fin L → Ω → ℝ)
    (h1 : ∀ i, finExpect μ (X i) = p i)
    (h2 : ∀ i, finExpect μ (fun ω => (X i ω) ^ 2) =
      (p i) ^ 2 + (1 - (p i) ^ 2) / (N i : ℝ))
    (h3 : ∀ i, finExpect μ (fun ω => (X i ω) ^ 3) =
      (p i) ^ 3 * (1 - 3 / (N i : ℝ) + 2 / (N i : ℝ) ^ 2) +
        p i * (3 / (N i : ℝ) - 2 / (N i : ℝ) ^ 2))
    (h4 : ∀ i, finExpect μ (fun ω => (X i ω) ^ 4) =
      (p i) ^ 4 + 6 * (p i) ^ 2 * (1 - (p i) ^ 2) / (N i : ℝ) +
        ((11 * (p i) ^ 2 - 3) * ((p i) ^ 2 - 1)) / (N i : ℝ) ^ 2 +
        2 * (3 * (p i) ^ 2 - 1) * (1 - (p i) ^ 2) / (N i : ℝ) ^ 3)
    (hVarSplit : finVar μ (meanSqEst w N X) =
      (∑ i, ((w i) ^ 2 * (N i : ℝ) / ((N i : ℝ) - 1)) ^ 2 *
        finVar μ (fun ω => (X i ω) ^ 2)) +
      (2 * ∑ ij : pairs L, (w ij.val.1 * w ij.val.2) ^ 2 *
        finVar μ (fun ω => X ij.val.1 ω * X ij.val.2 ω)) +
      (4 * ∑ ij : pairs L,
        (w ij.val.1) ^ 3 * ((N ij.val.1 : ℝ) / ((N ij.val.1 : ℝ) - 1)) * w ij.val.2 *
        finCov μ (fun ω => (X ij.val.1 ω) ^ 2)
          (fun ω => X ij.val.1 ω * X ij.val.2 ω)))
    (hcross1 : ∀ i j : Fin L, i ≠ j →
      finExpect μ (fun ω => X i ω * X j ω) = p i * p j)
    (hcross3 : ∀ i j : Fin L, i ≠ j →
      finExpect μ (fun ω => (X i ω) ^ 2 * (X j ω) ^ 2) =
        ((p i) ^ 2 + (1 - (p i) ^ 2) / (N i : ℝ)) *
          ((p j) ^ 2 + (1 - (p j) ^ 2) / (N j : ℝ)))
    (hcov3 : ∀ i j : Fin L, i ≠ j →
      finExpect μ (fun ω => (X i ω) ^ 3 * X j ω) =
        ((p i) ^ 3 * (1 - 3 / (N i : ℝ) + 2 / (N i : ℝ) ^ 2) +
          p i * (3 / (N i : ℝ) - 2 / (N i : ℝ) ^ 2)) * p j) :
    finVar μ (meanSqEst w N X) =
      (∑ i, 2 * (w i) ^ 4 / ((N i : ℝ) * ((N i : ℝ) - 1)) *
        (1 + 2 * ((N i : ℝ) - 2) * (p i) ^ 2
          - (2 * (N i : ℝ) - 3) * (p i) ^ 4)) +
      (2 * ∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
        ((p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) / (N ij.val.2 : ℝ) +
         (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2) / (N ij.val.1 : ℝ) +
         (1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) /
           ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ)))) +
      (8 * ∑ ij : pairs L, (w ij.val.1) ^ 3 * w ij.val.2 /
        (N ij.val.1 : ℝ) * p ij.val.1 * p ij.val.2 * (1 - (p ij.val.1) ^ 2)) := by
  -- Erratum-corrected proof (Eq. (296)-(319) of the source, with the three
  -- blocks of the corrected variance decomposition):
  --   Var[⟨Ô⟩²] = Σᵢ aᵢ² Var[Xᵢ²] + 2 Σ_{i≠j} wᵢ²wⱼ² Var[XᵢXⱼ]
  --               + 4 Σ_{i≠j} wᵢ³(Nᵢ/(Nᵢ-1)) wⱼ Cov[Xᵢ², XᵢXⱼ],
  -- with `Var[Xᵢ²] = μ₄ - μ₂²` from the F.4 moments (Eq. (300)-(306)),
  -- `Var[XᵢXⱼ] = μ₂ᵢμ₂ⱼ - pᵢ²pⱼ²` (Eq. (307)-(312)), and
  -- `Cov[Xᵢ², XᵢXⱼ] = 2pᵢpⱼ(1-pᵢ²)(Nᵢ-1)/Nᵢ²` (Eq. (312)-(319)).
  have hNne : ∀ i, ((N i : ℝ)) ≠ 0 := by
    intro i
    have h0 : (0:ℕ) < N i := Nat.lt_of_lt_of_le (by norm_num) (hN i)
    exact_mod_cast Nat.ne_of_gt h0
  have hNne1 : ∀ i, ((N i : ℝ)) - 1 ≠ 0 := by
    intro i
    have h1' : (1:ℝ) < (N i : ℝ) := by exact_mod_cast hN i
    linarith
  have hV2 : ∀ i, finVar μ (fun ω => (X i ω) ^ 2)
      = 2 * (1 - (p i) ^ 2) / (N i : ℝ) ^ 3 *
        (2 * (p i) ^ 2 * (N i : ℝ) ^ 2 - (5 * (p i) ^ 2 - 1) * (N i : ℝ)
          + (3 * (p i) ^ 2 - 1)) := by
    intro i
    have hsq : (fun ω => ((X i ω) ^ 2) ^ 2) = (fun ω => (X i ω) ^ 4) :=
      funext fun _ => by ring
    show finExpect μ (fun ω => ((X i ω) ^ 2) ^ 2)
        - (finExpect μ (fun ω => (X i ω) ^ 2)) ^ 2 = _
    rw [hsq, h4 i, h2 i]
    field_simp [(hNne i)]
    ring
  have hVX : ∀ ij : pairs L, finVar μ (fun ω => X ij.val.1 ω * X ij.val.2 ω)
      = ((p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) / (N ij.val.2 : ℝ) +
         (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2) / (N ij.val.1 : ℝ) +
         (1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) /
           ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ))) := by
    intro ij
    have hij : ij.val.1 ≠ ij.val.2 := ij.property
    have hsq : (fun ω => (X ij.val.1 ω * X ij.val.2 ω) ^ 2)
        = (fun ω => (X ij.val.1 ω) ^ 2 * (X ij.val.2 ω) ^ 2) :=
      funext fun _ => by ring
    show finExpect μ (fun ω => (X ij.val.1 ω * X ij.val.2 ω) ^ 2)
        - (finExpect μ (fun ω => X ij.val.1 ω * X ij.val.2 ω)) ^ 2 = _
    rw [hsq, hcross3 ij.val.1 ij.val.2 hij, hcross1 ij.val.1 ij.val.2 hij]
    ring
  have hCV : ∀ ij : pairs L,
      finCov μ (fun ω => (X ij.val.1 ω) ^ 2) (fun ω => X ij.val.1 ω * X ij.val.2 ω)
      = 2 * (p ij.val.1) * (p ij.val.2) * (1 - (p ij.val.1) ^ 2) *
        ((N ij.val.1 : ℝ) - 1) / (N ij.val.1 : ℝ) ^ 2 := by
    intro ij
    have hij : ij.val.1 ≠ ij.val.2 := ij.property
    have hmix : (fun ω => (X ij.val.1 ω) ^ 2 * (X ij.val.1 ω * X ij.val.2 ω))
        = (fun ω => (X ij.val.1 ω) ^ 3 * X ij.val.2 ω) :=
      funext fun _ => by ring
    show finExpect μ (fun ω => (X ij.val.1 ω) ^ 2 * (X ij.val.1 ω * X ij.val.2 ω))
        - finExpect μ (fun ω => (X ij.val.1 ω) ^ 2)
          * finExpect μ (fun ω => X ij.val.1 ω * X ij.val.2 ω) = _
    rw [hmix, hcov3 ij.val.1 ij.val.2 hij, h2 ij.val.1,
      hcross1 ij.val.1 ij.val.2 hij]
    field_simp [(hNne ij.val.1)]
    ring
  have key1 : ∀ i, ((w i) ^ 2 * (N i : ℝ) / ((N i : ℝ) - 1)) ^ 2 *
        finVar μ (fun ω => (X i ω) ^ 2)
      = 2 * (w i) ^ 4 / ((N i : ℝ) * ((N i : ℝ) - 1)) *
        (1 + 2 * ((N i : ℝ) - 2) * (p i) ^ 2
          - (2 * (N i : ℝ) - 3) * (p i) ^ 4) := by
    intro i
    rw [hV2 i]
    field_simp [(hNne i), (hNne1 i)]
    ring
  have key2 : ∀ ij : pairs L, (w ij.val.1 * w ij.val.2) ^ 2 *
        finVar μ (fun ω => X ij.val.1 ω * X ij.val.2 ω)
      = (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
        ((p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) / (N ij.val.2 : ℝ) +
         (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2) / (N ij.val.1 : ℝ) +
         (1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) /
           ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ))) := by
    intro ij
    rw [hVX ij]
    ring
  have key3 : ∀ ij : pairs L,
      (w ij.val.1) ^ 3 * ((N ij.val.1 : ℝ) / ((N ij.val.1 : ℝ) - 1)) * w ij.val.2 *
        finCov μ (fun ω => (X ij.val.1 ω) ^ 2)
          (fun ω => X ij.val.1 ω * X ij.val.2 ω)
      = 2 * ((w ij.val.1) ^ 3 * w ij.val.2 / (N ij.val.1 : ℝ) *
          p ij.val.1 * p ij.val.2 * (1 - (p ij.val.1) ^ 2)) := by
    intro ij
    rw [hCV ij]
    field_simp [(hNne ij.val.1), (hNne1 ij.val.1)]
  rw [hVarSplit,
    Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => key1 i),
    Finset.sum_congr rfl (fun ij (_ : ij ∈ Finset.univ) => key2 ij),
    Finset.sum_congr rfl (fun ij (_ : ij ∈ Finset.univ) => key3 ij)]
  have h8 : (4 * ∑ ij : pairs L, 2 * ((w ij.val.1) ^ 3 * w ij.val.2 /
        (N ij.val.1 : ℝ) * p ij.val.1 * p ij.val.2 * (1 - (p ij.val.1) ^ 2)))
      = 8 * ∑ ij : pairs L, (w ij.val.1) ^ 3 * w ij.val.2 /
        (N ij.val.1 : ℝ) * p ij.val.1 * p ij.val.2 * (1 - (p ij.val.1) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ij _ => by ring
  rw [h8]

/-! ### Theorem F.6 -/

/-- **Theorem F.6** (arXiv:2504.01077, App. F.3, Eq. (321), p. 53).
*Variance of the estimated variance* — **stated in corrected (erratum) form**.

For `Ô = Σᵢ wᵢPᵢ` with i.i.d. measurements of `Pᵢ` and `Pᵢⱼ = PᵢPⱼ`, the
variance of the estimator `V̄` of Eq. (262) is (sums over ordered pairs
`i ≠ j`)

`Var[V̄] = Σ_{i≠j} wᵢ²wⱼ²(1-⟨Pᵢⱼ⟩²)/Nᵢⱼ`
`+ 2 Σᵢ wᵢ⁴/(Nᵢ(Nᵢ-1)) (1 + 2(Nᵢ-2)pᵢ² - (2Nᵢ-3)pᵢ⁴)`
`+ 2 Σ_{i≠j} wᵢ²wⱼ²/(NᵢNⱼ) [(1-pᵢ²)(1-pⱼ²) + Nᵢpᵢ²(1-pⱼ²) + Nⱼpⱼ²(1-pᵢ²)]`
`+ 8 Σ_{i≠j} wᵢ³wⱼ/Nᵢ pᵢpⱼ(1-pᵢ²)`.

**Erratum.** Eq. (321) of the source has (i) `Var[V̄] = Var[⟨Ô²⟩] - Var[⟨Ô⟩²]`,
but the correct identity is `Var[V̄] = Var[⟨Ô²⟩] + Var[⟨Ô⟩²] - 2Cov` (its own
Eq. (271)) with `Cov = 0` between the product-measurement and
single-measurement estimators; (ii) the fourth block `4 Σ_{i<j}` is a quarter
of the true `8 Σ_{i≠j}` value (the `2Cov` cross block of Lemma F.5 has no
`i ↔ j` symmetry factor and is counted once per ordered pair); (iii) the
third block should be `2 Σ_{i≠j}` (= `4 Σ_{i<j}` over unordered pairs, which
is what the source's `4 Σ_{i<j}` was presumably meant to be, but written over
ordered pairs the coefficient is `2`).  The hypotheses `hVarO2`/`hVarOsq`
are the (corrected) conclusions of Lem. F.3 / F.5. -/
theorem SourceTheoremF6
    (w : Fin L → ℝ) (p : Fin L → ℝ) (hp : ∀ i, |p i| ≤ 1)
    (N : Fin L → ℕ) (hN : ∀ i, 1 < N i)
    (Nij : pairs L → ℕ) (hNij : ∀ ij, 0 < Nij ij)
    (varV varO2 varOsq : ℝ)
    (hVarV : varV = varO2 + varOsq)
    (hVarO2 : varO2 = ∑ ij : pairs L,
      (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 / (Nij ij : ℝ) *
        (1 - (p ij.val.1 * p ij.val.2) ^ 2))
    (hVarOsq : varOsq =
      (2 * ∑ i, (w i) ^ 4 / ((N i : ℝ) * ((N i : ℝ) - 1)) *
        (1 + 2 * ((N i : ℝ) - 2) * (p i) ^ 2
          - (2 * (N i : ℝ) - 3) * (p i) ^ 4)) +
      (2 * ∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
        ((p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) / (N ij.val.2 : ℝ) +
         (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2) / (N ij.val.1 : ℝ) +
         (1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) /
           ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ)))) +
      (8 * ∑ ij : pairs L, (w ij.val.1) ^ 3 * w ij.val.2 /
        (N ij.val.1 : ℝ) * p ij.val.1 * p ij.val.2 * (1 - (p ij.val.1) ^ 2))) :
    varV =
      (∑ ij : pairs L,
        (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 / (Nij ij : ℝ) *
          (1 - (p ij.val.1 * p ij.val.2) ^ 2)) +
      2 * (∑ i, (w i) ^ 4 / ((N i : ℝ) * ((N i : ℝ) - 1)) *
        (1 + 2 * ((N i : ℝ) - 2) * (p i) ^ 2
          - (2 * (N i : ℝ) - 3) * (p i) ^ 4)) +
      2 * (∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 /
        ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ)) *
        ((1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) +
         (N ij.val.1 : ℝ) * (p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) +
         (N ij.val.2 : ℝ) * (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2))) +
      8 * (∑ ij : pairs L,
        (w ij.val.1) ^ 3 * w ij.val.2 / (N ij.val.1 : ℝ) *
          p ij.val.1 * p ij.val.2 * (1 - (p ij.val.1) ^ 2)) := by
  -- Erratum-corrected proof: `Var[V̄] = Var[⟨Ô²⟩] + Var[⟨Ô⟩²]` (independence,
  -- corrected Eq. (271)), then substitute Lem. F.3 and the corrected Lem. F.5
  -- and put the second block over the common denominator `NᵢNⱼ`.
  rw [hVarV, hVarO2, hVarOsq]
  have hNne : ∀ i : Fin L, ((N i : ℝ)) ≠ 0 := by
    intro i
    have h0 : (0:ℕ) < N i := Nat.lt_of_lt_of_le (by norm_num) (hN i)
    exact_mod_cast Nat.ne_of_gt h0
  have key : ∀ ij : pairs L,
      (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
        ((p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) / (N ij.val.2 : ℝ) +
         (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2) / (N ij.val.1 : ℝ) +
         (1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) /
           ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ)))
      = (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 /
          ((N ij.val.1 : ℝ) * (N ij.val.2 : ℝ)) *
        ((1 - (p ij.val.1) ^ 2) * (1 - (p ij.val.2) ^ 2) +
         (N ij.val.1 : ℝ) * (p ij.val.1) ^ 2 * (1 - (p ij.val.2) ^ 2) +
         (N ij.val.2 : ℝ) * (p ij.val.2) ^ 2 * (1 - (p ij.val.1) ^ 2)) := by
    intro ij
    field_simp [(hNne ij.val.1), (hNne ij.val.2)]
    ring
  rw [Finset.sum_congr rfl (fun ij (_ : ij ∈ Finset.univ) => key ij)]
  ring

/-! ### Lemma F.7 -/

/-- **Lemma F.7** (arXiv:2504.01077, App. F.4, Eq. (323), p. 53).
*Alternative unbiased estimator via joint measurements.*

With `Xᵢⱼ` estimating `⟨Pᵢⱼ⟩` and `Xᵢ⊗ⱼ` estimating `⟨Pᵢ⟩⟨Pⱼ⟩`, the estimator
`V̄ = Σᵢ wᵢ² + Σ_{i≠j} wᵢwⱼXᵢⱼ - Σ_{i,j} wᵢwⱼXᵢ⊗ⱼ` is unbiased:

`E[V̄] = Σᵢ wᵢ² + Σ_{i≠j} wᵢwⱼ⟨Pᵢ⟩⟨Pⱼ⟩ - (Σᵢ wᵢ⟨Pᵢ⟩)²`. -/
theorem SourceLemmaF7
    (w : Fin L → ℝ) (p : Fin L → ℝ)
    {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (Xpair : pairs L → Ω → ℝ) (Xjoint : Fin L × Fin L → Ω → ℝ)
    (hXpair : ∀ ij, finExpect μ (Xpair ij) = p ij.val.1 * p ij.val.2)
    (hXjoint : ∀ ij, finExpect μ (Xjoint ij) = p ij.1 * p ij.2) :
    finExpect μ (varEstAlt w Xpair Xjoint) =
      (∑ i, (w i) ^ 2) +
        (∑ ij : pairs L, w ij.val.1 * w ij.val.2 * (p ij.val.1 * p ij.val.2)) -
        (∑ i, w i * p i) ^ 2 := by
  -- Paper route (Eq. (324)-(327)): expand
  -- `Var[Ô] = ⟨Ô²⟩ - ⟨Ô⟩² = Σᵢwᵢ² + Σ_{i≠j}wᵢwⱼ⟨Pᵢⱼ⟩ - (Σᵢwᵢ⟨Pᵢ⟩)²`
  -- and replace `⟨Pᵢⱼ⟩`, `⟨Pᵢ⟩⟨Pⱼ⟩` by their unbiased sample means
  -- (Eq. (325)-(326)).
  --
  -- Linearity bookkeeping and the diagonal split of `(Σ wᵢpᵢ)²`,
  -- identical to Prop. F.2.
  have hc : finExpect μ (fun _ => ∑ i, (w i) ^ 2) = (∑ i, (w i) ^ 2) * 1 := by
    rw [finExpect_const, hμ]
  have hB : finExpect μ (fun ω => ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω)
      = ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * (p ij.val.1 * p ij.val.2) := by
    rw [finExpect_sum]
    exact Finset.sum_congr rfl fun ij _ => by rw [finExpect_smul, hXpair ij]
  have hC : finExpect μ (fun ω => ∑ ij : Fin L × Fin L, w ij.1 * w ij.2 * Xjoint ij ω)
      = ∑ ij : Fin L × Fin L, w ij.1 * w ij.2 * (p ij.1 * p ij.2) := by
    rw [finExpect_sum]
    exact Finset.sum_congr rfl fun ij _ => by rw [finExpect_smul, hXjoint ij]
  have hkey : ∑ ij : Fin L × Fin L, w ij.1 * w ij.2 * (p ij.1 * p ij.2)
      = (∑ i, w i * p i) * (∑ j, w j * p j) := by
    rw [Fintype.sum_prod_type,
      Finset.sum_mul_sum (f := fun i => w i * p i) (g := fun j => w j * p j)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  show finExpect μ (fun ω => ((∑ i, (w i) ^ 2)
      + ∑ ij : pairs L, w ij.val.1 * w ij.val.2 * Xpair ij ω)
      - ∑ ij : Fin L × Fin L, w ij.1 * w ij.2 * Xjoint ij ω) = _
  rw [finExpect_sub, finExpect_add, hc, hB, hC, hkey, sq]
  ring

/-! ### Lemma F.8 -/

/-- **Lemma F.8** (arXiv:2504.01077, App. F.4, Eq. (328), p. 54).
*Variance of the alternative estimator.*

With the `{Pᵢⱼ}` and `{Pᵢ⊗ⱼ}` measurements i.i.d. and mutually independent,

`Var[V̄] = Σ_{i≠j} wᵢ²wⱼ²(1-⟨Pᵢⱼ⟩²)/Nᵢⱼ + Σ_{i,j} wᵢ²wⱼ²(1-⟨Pᵢ⟩²⟨Pⱼ⟩²)/Nᵢ⊗ⱼ`. -/
theorem SourceLemmaF8
    (w : Fin L → ℝ) (p : Fin L → ℝ)
    (Nij : pairs L → ℕ) (hNij : ∀ ij, 0 < Nij ij)
    (Nj : Fin L × Fin L → ℕ) (hNj : ∀ ij, 0 < Nj ij)
    {Ω : Type u} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∑ ω, μ ω = 1)
    (Xpair : pairs L → Ω → ℝ) (Xjoint : Fin L × Fin L → Ω → ℝ)
    (hPmean : ∀ ij, finExpect μ (Xpair ij) = p ij.val.1 * p ij.val.2)
    (hPsecond : ∀ ij, finExpect μ (fun ω => (Xpair ij ω) ^ 2) =
      (p ij.val.1 * p ij.val.2) ^ 2 +
        (1 - (p ij.val.1 * p ij.val.2) ^ 2) / (Nij ij : ℝ))
    (hJmean : ∀ ij, finExpect μ (Xjoint ij) = p ij.1 * p ij.2)
    (hJsecond : ∀ ij, finExpect μ (fun ω => (Xjoint ij ω) ^ 2) =
      (p ij.1 * p ij.2) ^ 2 + (1 - (p ij.1 * p ij.2) ^ 2) / (Nj ij : ℝ))
    (hVarSplit : finVar μ (varEstAlt w Xpair Xjoint) =
      (∑ ij : pairs L, (w ij.val.1 * w ij.val.2) ^ 2 *
        finVar μ (Xpair ij)) +
      (∑ ij : Fin L × Fin L, (w ij.1 * w ij.2) ^ 2 *
        finVar μ (Xjoint ij))) :
    finVar μ (varEstAlt w Xpair Xjoint) =
      (∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
        (1 - (p ij.val.1 * p ij.val.2) ^ 2) / (Nij ij : ℝ)) +
      (∑ ij : Fin L × Fin L, (w ij.1) ^ 2 * (w ij.2) ^ 2 *
        (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) / (Nj ij : ℝ)) := by
  have hVp : ∀ ij : pairs L, finVar μ (Xpair ij)
      = (1 - (p ij.val.1 * p ij.val.2) ^ 2) / (Nij ij : ℝ) := by
    intro ij
    show finExpect μ (fun ω => (Xpair ij ω) ^ 2)
        - (finExpect μ (Xpair ij)) ^ 2 = _
    rw [hPsecond ij, hPmean ij]
    ring
  have hVj : ∀ ij : Fin L × Fin L, finVar μ (Xjoint ij)
      = (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) / (Nj ij : ℝ) := by
    intro ij
    show finExpect μ (fun ω => (Xjoint ij ω) ^ 2)
        - (finExpect μ (Xjoint ij)) ^ 2 = _
    rw [hJsecond ij, hJmean ij]
    ring
  rw [hVarSplit]
  have hA : (∑ ij : pairs L, (w ij.val.1 * w ij.val.2) ^ 2 * finVar μ (Xpair ij))
      = (∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
          (1 - (p ij.val.1 * p ij.val.2) ^ 2) / (Nij ij : ℝ)) :=
    Finset.sum_congr rfl fun ij _ => by rw [hVp ij]; ring
  have hB : (∑ ij : Fin L × Fin L, (w ij.1 * w ij.2) ^ 2 * finVar μ (Xjoint ij))
      = (∑ ij : Fin L × Fin L, (w ij.1) ^ 2 * (w ij.2) ^ 2 *
          (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) / (Nj ij : ℝ)) :=
    Finset.sum_congr rfl fun ij _ => by rw [hVj ij]; ring
  rw [hA, hB]

/-! ### Prop. F.9 -/

/-- **Proposition F.9** (arXiv:2504.01077, App. F.4, Eq. (344)-(346), p. 55-56).
*Sample complexity of variance estimation.*

For `Ô = Σᵢ wᵢPᵢ` with `|⟨Pᵢ⟩| ≤ 1` and target precision `ε > 0`, there is an
allocation of the `Nᵢⱼ` (product measurements) and `Nᵢ⊗ⱼ` (joint measurements)
with total number of shots at most `(4/ε²)(Σᵢ|wᵢ|)⁴` achieving
`Var[V̄] ≤ ε²`.

This is Eq. (328) evaluated at the Lagrange-optimal allocation
(Eq. (340)-(344)), bounded using `|⟨Pᵢ⟩| ≤ 1` (Eq. (345)-(346)). -/
theorem SourcePropositionF9
    (w : Fin L → ℝ) (p : Fin L → ℝ) (hp : ∀ i, |p i| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hw : 0 < ∑ i, |w i|) :
    ∃ Nij : pairs L → ℝ, ∃ Nj : Fin L × Fin L → ℝ,
      (∀ ij, 0 < Nij ij) ∧ (∀ ij, 0 < Nj ij) ∧
      ((∑ ij : pairs L, Nij ij) + (∑ ij : Fin L × Fin L, Nj ij)) ≤
        4 / ε ^ 2 * (∑ i, |w i|) ^ 4 ∧
      ((∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
          (1 - (p ij.val.1 * p ij.val.2) ^ 2) / Nij ij) +
        (∑ ij : Fin L × Fin L, (w ij.1) ^ 2 * (w ij.2) ^ 2 *
          (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) / Nj ij)) ≤ ε ^ 2 := by
  -- Uniform allocation: N_ij = (2/ε²)|w_i w_j| S² + η with S = Σ|w_i| and a
  -- tiny η > 0 absorbing the zero-weight slots.  The slack Δ = (2/ε²)S²·Σ|w_i|²
  -- of the strict inequality Σ_{i≠j}|w_i||w_j| = S² - Σ|w_i|² < S² covers the
  -- η mass, so the total stays within (4/ε²)(Σ|w_i|)⁴ of Eq. (346), while each
  -- variance block is at most ε²/2.
  classical
  have hε2 : 0 < ε ^ 2 := by positivity
  have hinv : 0 < 2 / ε ^ 2 := div_pos two_pos hε2
  have hS0 : 0 < ∑ i, |w i| := hw
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin L, w i₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hcon i])] at hS0
    exact absurd hS0 (by norm_num)
  have hs2pos : 0 < ∑ i, |w i| ^ 2 := by
    have hle : |w i₀| ^ 2 ≤ ∑ i, |w i| ^ 2 :=
      Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg (|w i|))
        (Finset.mem_univ i₀)
    have h0 : (0 : ℝ) < |w i₀| ^ 2 := by
      have h : 0 < |w i₀| := abs_pos.mpr hi₀
      nlinarith [h]
    linarith
  set S := ∑ i, |w i| with hSdef
  set s2 := ∑ i, |w i| ^ 2 with hs2def
  have hS : 0 < S := hS0
  have hfull : ∑ ij : Fin L × Fin L, |w ij.1 * w ij.2| = S * S := by
    rw [Fintype.sum_prod_type,
      Finset.sum_mul_sum (f := fun i => |w i|) (g := fun j => |w j|)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [← abs_mul (w i) (w j)]
  have hpairs : ∑ ij : pairs L, |w ij.val.1 * w ij.val.2| = S * S - s2 := by
    have hsplit := sum_sq_split (fun i => |w i|)
    have habs : ∑ ij : pairs L, |w ij.val.1| * |w ij.val.2|
        = ∑ ij : pairs L, |w ij.val.1 * w ij.val.2| :=
      Finset.sum_congr rfl fun ij _ => by rw [abs_mul]
    rw [← habs]
    rw [show S * S = S ^ 2 from by rw [sq]]
    linarith
  set Δ := 2 / ε ^ 2 * S ^ 2 * s2 with hΔdef
  have hΔpos : 0 < Δ := by
    have hSS : (0 : ℝ) < S * S := by nlinarith [hS]
    have h1 : (0 : ℝ) < 2 / ε ^ 2 * S ^ 2 := by
      rw [show S ^ 2 = S * S from by rw [sq]]
      exact mul_pos hinv hSS
    exact mul_pos h1 hs2pos
  set m := ((Fintype.card (pairs L) : ℝ) + (Fintype.card (Fin L × Fin L) : ℝ)) with hmdef
  set η := Δ / (2 * m + 1) with hηdef
  have hηpos : 0 < η := by
    have : 0 < 2 * m + 1 := by
      have : 0 ≤ m := by positivity
      nlinarith
    exact div_pos hΔpos this
  have hηle : η * m ≤ Δ / 2 := by
    have hden : (0 : ℝ) < 2 * m + 1 := by
      have : 0 ≤ m := by positivity
      nlinarith
    have hΔn : (0 : ℝ) ≤ Δ := le_of_lt hΔpos
    rw [hηdef, div_mul_eq_mul_div, div_le_div_iff₀ hden two_pos,
      show Δ * (2 * m + 1) = Δ * m * 2 + Δ from by ring]
    linarith
  have hconstP : ∑ ij : pairs L, (η : ℝ) = η * (Fintype.card (pairs L) : ℝ) := by
    simp [Finset.sum_const]
    ring
  have hconstJ : ∑ ij : Fin L × Fin L, (η : ℝ)
      = η * (Fintype.card (Fin L × Fin L) : ℝ) := by
    simp [Finset.sum_const]
    ring
  refine ⟨fun ij => 2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 + η,
    fun ij => 2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 + η, ?_, ?_, ?_, ?_⟩
  · intro ij
    have hA : (0 : ℝ) ≤ 2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hinv) (abs_nonneg _)) (sq_nonneg S)
    linarith
  · intro ij
    have hA : (0 : ℝ) ≤ 2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hinv) (abs_nonneg _)) (sq_nonneg S)
    linarith
  · -- total shots
    have hterm : ∀ a : ℝ, 2 / ε ^ 2 * a * S ^ 2 = (2 / ε ^ 2 * S ^ 2) * a := fun a => by ring
    have hsum1 : ∑ ij : pairs L, (2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 + η)
        = (2 / ε ^ 2 * S ^ 2) * (S * S - s2) + η * (Fintype.card (pairs L) : ℝ) := by
      rw [Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun ij _ => hterm |w ij.val.1 * w ij.val.2|),
        ← Finset.mul_sum, hpairs, hconstP]
    have hsum2 : ∑ ij : Fin L × Fin L, (2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 + η)
        = (2 / ε ^ 2 * S ^ 2) * (S * S) + η * (Fintype.card (Fin L × Fin L) : ℝ) := by
      rw [Finset.sum_add_distrib,
        Finset.sum_congr rfl (fun ij _ => hterm |w ij.1 * w ij.2|),
        ← Finset.mul_sum, hfull, hconstJ]
    have hηsum : η * (Fintype.card (pairs L) : ℝ)
        + η * (Fintype.card (Fin L × Fin L) : ℝ) = η * m := by
      rw [← mul_add, hmdef]
    have hcalc : (2 / ε ^ 2 * S ^ 2) * (S * S - s2) + (2 / ε ^ 2 * S ^ 2) * (S * S)
        = 4 / ε ^ 2 * S ^ 4 - Δ := by
      rw [hΔdef]
      field_simp
      ring
    rw [hsum1, hsum2]
    linarith [hcalc, hηle, hηsum, hΔpos]
  · -- variance bound
    have habs2 : ∀ x : ℝ, |x| ^ 2 = x ^ 2 := fun x => by rw [← abs_pow, abs_sq]
    have hrr : ∀ a b : ℝ, a ^ 2 * b ^ 2 = |a * b| * |a * b| := by
      intro a b
      rw [← sq_abs a, ← sq_abs b, ← mul_pow, ← abs_mul, sq]
    have hq1 : ∀ ij : pairs L, (1 - (p ij.val.1 * p ij.val.2) ^ 2) ≤ 1 :=
      fun ij => by linarith [sq_nonneg (p ij.val.1 * p ij.val.2)]
    have hq2 : ∀ ij : Fin L × Fin L, (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) ≤ 1 :=
      fun ij => by nlinarith [sq_nonneg (p ij.1), sq_nonneg (p ij.2)]
    have hperP : ∀ ij : pairs L,
        (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
            (1 - (p ij.val.1 * p ij.val.2) ^ 2) /
          (2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 + η)
        ≤ |w ij.val.1 * w ij.val.2| * ε ^ 2 / (2 * S ^ 2) := by
      intro ij
      have hq := hq1 ij
      have hNpos : (0 : ℝ) < 2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 + η := by
        have hA : (0 : ℝ) ≤ 2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 :=
          mul_nonneg (mul_nonneg (le_of_lt hinv) (abs_nonneg _)) (sq_nonneg S)
        linarith
      have hw2 : (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2
          = |w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2| :=
        hrr (w ij.val.1) (w ij.val.2)
      have h2S : (0 : ℝ) < 2 * S ^ 2 := by positivity
      rw [hw2, div_le_div_iff₀ hNpos h2S]
      have hK : (0 : ℝ) ≤ |w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2|
          * (2 * S ^ 2) := by positivity
      have hkey : |w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2| *
            (1 - (p ij.val.1 * p ij.val.2) ^ 2) * (2 * S ^ 2)
          ≤ |w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2| * (2 * S ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hq hK
        have hassoc : (1 - (p ij.val.1 * p ij.val.2) ^ 2) *
            (|w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2| * (2 * S ^ 2))
            = |w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2| *
                (1 - (p ij.val.1 * p ij.val.2) ^ 2) * (2 * S ^ 2) := by ring
        rw [← hassoc]
        linarith [hmul]
      have hsplit2 : |w ij.val.1 * w ij.val.2| * ε ^ 2 *
            (2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 + η)
          = |w ij.val.1 * w ij.val.2| * |w ij.val.1 * w ij.val.2| * (2 * S ^ 2)
            + |w ij.val.1 * w ij.val.2| * ε ^ 2 * η := by
        field_simp
      rw [hsplit2]
      have hrn : (0 : ℝ) ≤ |w ij.val.1 * w ij.val.2| * ε ^ 2 * η :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (le_of_lt hε2)) (le_of_lt hηpos)
      linarith
    have hperJ : ∀ ij : Fin L × Fin L,
        (w ij.1) ^ 2 * (w ij.2) ^ 2 * (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) /
          (2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 + η)
        ≤ |w ij.1 * w ij.2| * ε ^ 2 / (2 * S ^ 2) := by
      intro ij
      have hq := hq2 ij
      have hNpos : (0 : ℝ) < 2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 + η := by
        have hA : (0 : ℝ) ≤ 2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 :=
          mul_nonneg (mul_nonneg (le_of_lt hinv) (abs_nonneg _)) (sq_nonneg S)
        linarith
      have hw2 : (w ij.1) ^ 2 * (w ij.2) ^ 2
          = |w ij.1 * w ij.2| * |w ij.1 * w ij.2| := hrr (w ij.1) (w ij.2)
      have h2S : (0 : ℝ) < 2 * S ^ 2 := by positivity
      rw [hw2, div_le_div_iff₀ hNpos h2S]
      have hK : (0 : ℝ) ≤ |w ij.1 * w ij.2| * |w ij.1 * w ij.2| * (2 * S ^ 2) := by
        positivity
      have hkey : |w ij.1 * w ij.2| * |w ij.1 * w ij.2| *
            (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) * (2 * S ^ 2)
          ≤ |w ij.1 * w ij.2| * |w ij.1 * w ij.2| * (2 * S ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hq hK
        have hassoc : (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) *
            (|w ij.1 * w ij.2| * |w ij.1 * w ij.2| * (2 * S ^ 2))
            = |w ij.1 * w ij.2| * |w ij.1 * w ij.2| *
                (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) * (2 * S ^ 2) := by ring
        rw [← hassoc]
        linarith [hmul]
      have hsplit2 : |w ij.1 * w ij.2| * ε ^ 2 *
            (2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 + η)
          = |w ij.1 * w ij.2| * |w ij.1 * w ij.2| * (2 * S ^ 2)
            + |w ij.1 * w ij.2| * ε ^ 2 * η := by
        field_simp
      rw [hsplit2]
      have hrn : (0 : ℝ) ≤ |w ij.1 * w ij.2| * ε ^ 2 * η :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (le_of_lt hε2)) (le_of_lt hηpos)
      linarith
    have hterm2 : ∀ a : ℝ, |a| * ε ^ 2 / (2 * S ^ 2)
        = ε ^ 2 / (2 * S ^ 2) * |a| := fun a => by ring
    have hSP : ∑ ij : pairs L, |w ij.val.1 * w ij.val.2| * ε ^ 2 / (2 * S ^ 2)
        ≤ ε ^ 2 / 2 := by
      rw [Finset.sum_congr rfl (fun ij _ => hterm2 (w ij.val.1 * w ij.val.2)),
        ← Finset.mul_sum, hpairs]
      have hzero : ε ^ 2 / (2 * S ^ 2) * (S * S) = ε ^ 2 / 2 := by
        have hSne : S ≠ 0 := ne_of_gt hS
        field_simp
      have h1 : (0 : ℝ) ≤ ε ^ 2 / (2 * S ^ 2) * s2 :=
        mul_nonneg (by positivity) (le_of_lt hs2pos)
      have h2 : ε ^ 2 / (2 * S ^ 2) * (S * S - s2)
          = ε ^ 2 / (2 * S ^ 2) * (S * S) - ε ^ 2 / (2 * S ^ 2) * s2 := by ring
      rw [h2, hzero]
      linarith
    have hSJ : ∑ ij : Fin L × Fin L, |w ij.1 * w ij.2| * ε ^ 2 / (2 * S ^ 2)
        ≤ ε ^ 2 / 2 := by
      rw [Finset.sum_congr rfl (fun ij _ => hterm2 (w ij.1 * w ij.2)),
        ← Finset.mul_sum, hfull]
      have hzero : ε ^ 2 / (2 * S ^ 2) * (S * S) = ε ^ 2 / 2 := by
        have hSne : S ≠ 0 := ne_of_gt hS
        field_simp
      rw [hzero]
    have hhalf : ε ^ 2 / 2 + ε ^ 2 / 2 = ε ^ 2 := by ring
    calc (∑ ij : pairs L, (w ij.val.1) ^ 2 * (w ij.val.2) ^ 2 *
            (1 - (p ij.val.1 * p ij.val.2) ^ 2) /
            (2 / ε ^ 2 * |w ij.val.1 * w ij.val.2| * S ^ 2 + η))
          + ∑ ij : Fin L × Fin L, (w ij.1) ^ 2 * (w ij.2) ^ 2 *
              (1 - (p ij.1) ^ 2 * (p ij.2) ^ 2) /
              (2 / ε ^ 2 * |w ij.1 * w ij.2| * S ^ 2 + η)
        ≤ (∑ ij : pairs L, |w ij.val.1 * w ij.val.2| * ε ^ 2 / (2 * S ^ 2))
            + ∑ ij : Fin L × Fin L, |w ij.1 * w ij.2| * ε ^ 2 / (2 * S ^ 2) :=
          add_le_add (Finset.sum_le_sum (fun ij _ => hperP ij))
            (Finset.sum_le_sum (fun ij _ => hperJ ij))
      _ ≤ ε ^ 2 / 2 + ε ^ 2 / 2 := add_le_add hSP hSJ
      _ = ε ^ 2 := hhalf
end Qatlib.Papers.DoubleBracket25.MainResults
