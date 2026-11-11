/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Qatlib.Papers.BettiHardness26.MainResults.Reduction.BettiEstimationReduction
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The Betti-estimation problem and the planted-clique conjectures

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11).

An instance of the reduction at fixed `(n, k)` is a `Setup`: a finite type of input graphs `Γ`
carrying the balanced planted-clique mixture `D_k = ½ G(n,1/2) + ½ G(n,1/2,k)` (weights
`mu0`, `mu1`) and the Betti value `beta = β_{k-2}(skel_{k-2} X(G))`. The null value `beta = 0`
on the `mu0`-support is the content of Lemma 4.1.

`EffModel` abstracts the class of efficient algorithms (randomized polynomial time classically,
quantum polynomial time quantumly). `ClassicalPCConjecture`/`QuantumPCConjecture` are the
paper's Assumptions 1 and 2: no efficient distinguisher has advantage `≥ δ`.

`theorem_2_1` is Theorem 2.1 of the paper, proved as a genuine reduction: it takes Lemma 4.2's
planted value `β ≥ 1` as a hypothesis (proved in `PlantedValue.lean`) and refutes the existence
of an efficient estimator of the required accuracy via the probabilistic core in
`BettiEstimationReduction`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Model

open Finset
open Qatlib.Papers.BettiHardness26.MainResults.Reduction

variable {Γ : Type*} [Fintype Γ]

/-- A fixed-`(n,k)` instance of the Betti-vs-planted-clique reduction: the null weights `mu0`
(`G(n,1/2)`), planted weights `mu1` (`G(n,1/2,k)`), and Betti value `beta`. The null value
`beta = 0` is Lemma 4.1. -/
structure Setup (Γ : Type*) [Fintype Γ] where
  /-- Null-case weights `G(n,1/2)`. -/
  mu0 : Γ → ℝ
  /-- Planted-case weights `G(n,1/2,k)`. -/
  mu1 : Γ → ℝ
  /-- The Betti value `β_{k-2}(skel_{k-2} X(G))` attached to each graph. -/
  beta : Γ → ℝ
  mu0_nonneg : ∀ g, 0 ≤ mu0 g
  mu1_nonneg : ∀ g, 0 ≤ mu1 g
  mu0_sum : (∑ g, mu0 g) = 1
  mu1_sum : (∑ g, mu1 g) = 1
  /-- Lemma 4.1: the Betti value vanishes on the null support. -/
  null_zero : ∀ g, mu0 g ≠ 0 → beta g = 0

/-- An abstract computational model: predicates selecting the efficient estimators and efficient
distinguishers, together with the fact that the reduction's canonical detector is efficient
whenever the estimator is (the reduction is a polynomial-time transformation). -/
structure EffModel (Γ : Type*) where
  /-- Which estimators `Γ → ℝ` are efficient. -/
  EffEst : (Γ → ℝ) → Prop
  /-- Which distinguishers `Γ → ℝ` are efficient. -/
  EffDet : (Γ → ℝ) → Prop
  /-- The reduction's detector is efficient whenever the estimator is. -/
  det_eff : ∀ (est : Γ → ℝ) (η : ℝ), EffEst est → EffDet (detector est η)

/-- The distinguishing advantage of a detector between the planted and null cases: the
difference of its expectation under `mu1` and under `mu0`. -/
def PCAdvantage (s : Setup Γ) (det : Γ → ℝ) : ℝ :=
  (∑ g, s.mu1 g * det g) - (∑ g, s.mu0 g * det g)

/-- **Assumption 1 (classical planted-clique conjecture)**, constant-advantage form: no
efficient distinguisher has advantage `≥ δ`. (Section 4, p.9–10; the "efficient" class is the
abstract `M.EffDet`.) -/
def ClassicalPCConjecture (M : EffModel Γ) (s : Setup Γ) (δ : ℝ) : Prop :=
  ∀ det, M.EffDet det → PCAdvantage s det < δ

/-- **Assumption 2 (quantum planted-clique conjecture)**, constant-advantage form: no efficient
quantum distinguisher has advantage `≥ δ`. (Section 4, p.9–10.) -/
def QuantumPCConjecture (M : EffModel Γ) (s : Setup Γ) (δ : ℝ) : Prop :=
  ∀ det, M.EffDet det → PCAdvantage s det < δ

/-- Success probability of an additive estimator over the balanced mixture `D_k`. -/
def AdditiveSuccess (s : Setup Γ) (est : Γ → ℝ) (η : ℝ) : ℝ :=
  (prob s.mu0 (fun g => |est g - s.beta g| < η)
    + prob s.mu1 (fun g => |est g - s.beta g| < η)) / 2

/-- **General additive reduction.** If `β = 0` on the null support, `β ≥ g0 ≥ 2η` on the planted
support, and `hpc` is the (classical or quantum) planted-clique conjecture, then no efficient
estimator reaches additive error `< η` with success probability `≥ ½ + δ`. -/
theorem hardness_from_gap (M : EffModel Γ) (s : Setup Γ)
    (η g0 δ : ℝ) (hη : 0 ≤ η) (hgap : 2 * η ≤ g0) (hδ : 0 ≤ δ)
    (hPlantedG : ∀ g, s.mu1 g ≠ 0 → g0 ≤ s.beta g)
    (hpc : ClassicalPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est η ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hred : PCAdvantage s (detector est η) ≥ δ :=
    reduction_threshold s.mu0 s.mu1 s.mu0_nonneg s.mu1_nonneg s.mu0_sum s.mu1_sum
      s.beta est η g0 δ hη hgap hδ s.null_zero hPlantedG
      (by simpa only [AdditiveSuccess] using hsol)
  have hlt : PCAdvantage s (detector est η) < δ :=
    hpc (detector est η) (M.det_eff est η heff)
  linarith

/-- **Theorem 2.1 (classical).** Under Assumption 1, no efficient estimator of
`β_{k-2}(skel_{k-2} X(G))` achieves additive error `< ½` with success probability `≥ ½ + δ` over
`D_k`, provided the planted value satisfies `β ≥ 1` (Lemma 4.2). Source: Theorem 2.1, §4, p.10. -/
theorem theorem_2_1_classical (M : EffModel Γ) (s : Setup Γ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : ClassicalPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est (1/2) ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hred : PCAdvantage s (detector est (1/2)) ≥ δ :=
    reduction_threshold s.mu0 s.mu1 s.mu0_nonneg s.mu1_nonneg s.mu0_sum s.mu1_sum
      s.beta est (1/2) 1 δ (by norm_num) (by norm_num) hδ s.null_zero hPlanted
      (by simpa only [AdditiveSuccess] using hsol)
  have hlt : PCAdvantage s (detector est (1/2)) < δ :=
    hpc (detector est (1/2)) (M.det_eff est (1/2) heff)
  linarith

/-- **Theorem 2.1 (quantum).** Under Assumption 2, no efficient quantum estimator with a
classical output achieves additive error `< ½` at success probability `≥ ½ + δ` over `D_k`,
provided `β ≥ 1` in the planted case. Source: Theorem 2.1, §4, p.10. -/
theorem theorem_2_1_quantum (M : EffModel Γ) (s : Setup Γ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est (1/2) ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hred : PCAdvantage s (detector est (1/2)) ≥ δ :=
    reduction_threshold s.mu0 s.mu1 s.mu0_nonneg s.mu1_nonneg s.mu0_sum s.mu1_sum
      s.beta est (1/2) 1 δ (by norm_num) (by norm_num) hδ s.null_zero hPlanted
      (by simpa only [AdditiveSuccess] using hsol)
  have hlt : PCAdvantage s (detector est (1/2)) < δ :=
    hpc (detector est (1/2)) (M.det_eff est (1/2) heff)
  linarith

end Qatlib.Papers.BettiHardness26.MainResults.Model
