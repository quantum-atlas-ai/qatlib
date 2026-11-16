/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BettiHardness26.MainResults.Model.BettiProblem
public import Qatlib.Papers.BettiHardness26.MainResults.Reduction.BettiEstimationReduction

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Conditional approximation reductions associated with Corollaries 3, 4, 5, 8

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11). Sources: §7.1–7.2, p.15–17.

* **Corollary 3 (multiplicative and coarse additive), §7.2 p.16.** Under Assumption 2 no
  efficient algorithm gives a finite multiplicative approximation of `β_d` at success
  `≥ ½ + δ`; at `d = k−2` the additive error `< ½` is already hard; and for `d = Θ(log n)`,
  `k = n^{1/2−ε}` the additive error may be relaxed to `exp(c log²n)`.
* **Corollary 4 (normalized Betti-number estimation), §7.2 p.16.** Under PC, normalized
  `β_d(skel_d X(G)) / f_d(G)` is hard to estimate to additive `< ½`.
* **Corollary 5 (homology vanishing), §7.2 p.16.** Under Assumption 2 no efficient algorithm
  decides whether `H_d(skel_d X(G)) = 0` at success `≥ ½ + δ`.
* **Corollary 8 (low-lying spectral density), §7.2 p.17.** Under Assumption 2 no efficient
  algorithm estimates the eigenvalue count `N_{<λ}(Δ_{k−2})` to additive `< ½`.

All claims are conditional reductions. The normalized claim additionally assumes a planted
normalized value of at least one, the separation needed for the stated error threshold.
This explicit condition is not established here for the paper's normalized Betti ratio.
The supplied functions `normbeta` and `spec` are abstract targets; this module does not identify
them with a normalized Betti ratio or a Laplacian eigenvalue count. The declaration associated
with Corollary 5 is a value-gap estimation consequence, without a homology-decision interface.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Claims
open Qatlib.Papers.BettiHardness26.MainResults

open Qatlib.Papers.BettiHardness26.MainResults.Model
open Qatlib.Papers.BettiHardness26.MainResults.Reduction

variable {Γ : Type*} [Fintype Γ]

/-- `prob` respects pointwise-equivalent predicates (needed to rewrite the estimator's target
`β` against the spectral/normalized value). -/
lemma prob_congr {mu : Γ → ℝ} {P Q : Γ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ g, P g ↔ Q g) : prob mu P = prob mu Q := by
  unfold prob
  refine Finset.sum_congr rfl (fun g _ => ?_)
  congr 1
  unfold ind
  by_cases hp : P g
  · have hq : Q g := (h g).mp hp
    simp [hp, hq]
  · have hq : ¬ Q g := fun hq => hp ((h g).mpr hq)
    simp [hp, hq]

/-! ### Corollary 3 — multiplicative and coarse additive -/

/-- Success probability of a finite multiplicative estimator `β/C ≤ est ≤ C β` over the balanced
mixture `D_k`. -/
def MultSuccess (s : Setup Γ) (est : Γ → ℝ) (C : ℝ) : ℝ :=
  (prob s.mu0 (fun g => s.beta g / C ≤ est g ∧ est g ≤ C * s.beta g)
    + prob s.mu1 (fun g => s.beta g / C ≤ est g ∧ est g ≤ C * s.beta g)) / 2

/-- **General additive reduction (quantum).** If `β = 0` on the null support and `β ≥ g0 ≥ 2η`
on the planted support, then under the quantum planted-clique conjecture no efficient estimator
reaches additive error `< η` at success `≥ ½ + δ`. (Quantum analogue of `hardness_from_gap`.) -/
theorem hardness_from_gap_quantum (M : EffModel Γ) (s : Setup Γ)
    (η g0 δ : ℝ) (hη : 0 ≤ η) (hgap : 2 * η ≤ g0) (hδ : 0 ≤ δ)
    (hPlantedG : ∀ g, s.mu1 g ≠ 0 → g0 ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est η ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hred : PCAdvantage s (detector est η) ≥ δ :=
    reduction_threshold s.mu0 s.mu1 s.mu0_nonneg s.mu1_nonneg s.mu0_sum s.mu1_sum
      s.beta est η g0 δ hη hgap hδ s.null_zero hPlantedG
      (by simpa only [AdditiveSuccess] using hsol)
  have hlt : PCAdvantage s (detector est η) < δ :=
    hpc (detector est η) (M.det_eff est η heff)
  linarith

/-- **Corollary 3, multiplicative part (§7.2, p.16).** Under the quantum planted-clique
conjecture, no efficient algorithm produces a finite multiplicative `C`-approximation of
`β_{k−2}` with success `≥ ½ + δ`, for `C ≥ 1` and `δ ≥ 0`. -/
theorem corollary_3_multiplicative (M : EffModel Γ) (s : Setup Γ) (C : ℝ) (hC : 1 ≤ C)
    {δ : ℝ} (hδ : 0 ≤ δ) (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ MultSuccess s est C ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hred : PCAdvantage s (detector est (1 / (2 * C))) ≥ δ :=
    multiplicative_yields_distinguisher s.mu0 s.mu1 s.mu0_nonneg s.mu1_nonneg
      s.mu0_sum s.mu1_sum s.beta est C hC δ hδ s.null_zero hPlanted
      (by simpa only [MultSuccess] using hsol)
  have hlt : PCAdvantage s (detector est (1 / (2 * C))) < δ :=
    hpc (detector est (1 / (2 * C))) (M.det_eff est (1 / (2 * C)) heff)
  linarith

/-- **Corollary 3, coarse-additive part (§7.2, p.16).** For `d = Θ(log n)`, `k = n^{1/2−ε}`, the
additive-error requirement may be relaxed to any `K ≥ 0` (e.g. `K = exp(c log² n)`) as long as
the planted value dominates `2K`. Proved as a reduction; the planted lower bound `2K ≤ β` is the
paper's separate estimate on the planted combinatorial Laplacian and is taken as hypothesis. -/
theorem corollary_3_coarse (M : EffModel Γ) (s : Setup Γ) (K : ℝ) (hK : 0 ≤ K)
    {δ : ℝ} (hδ : 0 ≤ δ) (hPlantedBig : ∀ g, s.mu1 g ≠ 0 → 2 * K ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est K ≥ 1/2 + δ :=
  hardness_from_gap_quantum M s K (2 * K) δ hK (le_refl (2 * K)) hδ hPlantedBig hpc

/-! ### Corollary 4 — normalized Betti number -/

/-- Normalized estimation is hard under a null value of zero and a planted value at least one.
The planted separation is an explicit additional condition for additive error below one half. -/
theorem corollary_4 (M : EffModel Γ) (s : Setup Γ) (normbeta : Γ → ℝ)
    (hNullNorm : ∀ g, s.mu0 g ≠ 0 → normbeta g = 0)
    (hPlantedNorm : ∀ g, s.mu1 g ≠ 0 → 1 ≤ normbeta g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpc : ClassicalPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧
      (prob s.mu0 (fun g => |est g - normbeta g| < 1/2)
        + prob s.mu1 (fun g => |est g - normbeta g| < 1/2)) / 2 ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hred : PCAdvantage s (detector est (1/2)) ≥ δ :=
    reduction_threshold s.mu0 s.mu1 s.mu0_nonneg s.mu1_nonneg s.mu0_sum s.mu1_sum
      normbeta est (1/2) 1 δ (by norm_num) (by norm_num) hδ hNullNorm hPlantedNorm hsol
  exact (not_lt_of_ge hred) (hpc _ (M.det_eff est (1/2) heff))

/-! ### Corollary 5 — homology vanishing -/

/-- The value-gap estimation consequence associated with Corollary 5 (§7.2, p.16).
This is Theorem 2.1 applied to the abstract target `s.beta`; it does not construct a reduction
from a homology-vanishing decision algorithm to an estimator of a possibly nonbinary target. -/
theorem corollary_5 (M : EffModel Γ) (s : Setup Γ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est (1/2) ≥ 1/2 + δ :=
  Model.theorem_2_1_quantum M s hδ hPlanted hpc

/-! ### Corollary 8 — low-lying spectral density -/

/-- Rewriting the estimator's target from `β` to a pointwise-equal `spec` inside the additive
success probability. -/
lemma additive_success_spec {s : Setup Γ} {est spec : Γ → ℝ} (h : ∀ g, spec g = s.beta g) :
    AdditiveSuccess s est (1/2) =
      (prob s.mu0 (fun g => |est g - spec g| < 1/2)
        + prob s.mu1 (fun g => |est g - spec g| < 1/2)) / 2 := by
  unfold AdditiveSuccess
  have h0 : prob s.mu0 (fun g => |est g - s.beta g| < 1/2)
      = prob s.mu0 (fun g => |est g - spec g| < 1/2) := by
    apply prob_congr; intro g; rw [h g]
  have h1 : prob s.mu1 (fun g => |est g - s.beta g| < 1/2)
      = prob s.mu1 (fun g => |est g - spec g| < 1/2) := by
    apply prob_congr; intro g; rw [h g]
  rw [h0, h1]

/-- The eigenvalue count `N_{<λ}(Δ_{k−2})` is modelled by `spec : Γ → ℝ`. The paper's spectral
fact is that for `λ ∈ (0,k)` the only eigenvalues of `Δ_{k−2}` below `λ` are the zero eigenvalues,
whose multiplicity is `β_{k−2}`; this is the hypothesis `hSpec`.

**Corollary 8 (low-lying spectral density), §7.2, p.17.** Under the quantum planted-clique
conjecture no efficient algorithm estimates `N_{<λ}(Δ_{k−2})` to additive error `< ½` at success
`≥ ½ + δ`, given the spectral identification `N_{<λ}(Δ_{k−2}) = β_{k−2}` (valid for `0 < λ < k`). -/
theorem corollary_8 (M : EffModel Γ) (s : Setup Γ) (spec : Γ → ℝ)
    (hSpec : ∀ g, spec g = s.beta g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧
      (prob s.mu0 (fun g => |est g - spec g| < 1/2)
        + prob s.mu1 (fun g => |est g - spec g| < 1/2)) / 2 ≥ 1/2 + δ := by
  rintro ⟨est, heff, hsol⟩
  have hsol' : AdditiveSuccess s est (1/2) ≥ 1/2 + δ := by
    rw [additive_success_spec (fun g => hSpec g)]
    exact hsol
  exact Model.theorem_2_1_quantum M s hδ hPlanted hpc ⟨est, heff, hsol'⟩

end Qatlib.Papers.BettiHardness26.MainResults.Claims

namespace Qatlib.Papers.BettiHardness26.MainResults.Audit

open Qatlib.Papers.BettiHardness26.MainResults.Model
open Qatlib.Papers.BettiHardness26.MainResults.Reduction

/-- Equal null and planted distributions satisfy the distinguishing assumption for positive
advantage, although the identically zero target has a perfect efficient estimator. -/
private theorem normalized_counterexample :
    ∃ (M : EffModel Unit) (s : Setup Unit) (normbeta : Unit → ℝ),
      (∀ g, s.mu0 g ≠ 0 → normbeta g = 0) ∧
      ClassicalPCConjecture M s (1/4) ∧
      ∃ est : Unit → ℝ, M.EffEst est ∧
        (prob s.mu0 (fun g => |est g - normbeta g| < 1/2) +
          prob s.mu1 (fun g => |est g - normbeta g| < 1/2)) / 2 ≥ 1/2 + 1/4 := by
  let s : Setup Unit :=
    { mu0 := fun _ => 1, mu1 := fun _ => 1, beta := fun _ => 0,
      mu0_nonneg := fun _ => by norm_num, mu1_nonneg := fun _ => by norm_num,
      mu0_sum := by simp, mu1_sum := by simp, null_zero := fun _ _ => rfl }
  let M : EffModel Unit :=
    { EffEst := fun _ => True, EffDet := fun _ => True, det_eff := fun _ _ _ => trivial }
  refine ⟨M, s, fun _ => 0, (fun _ _ => rfl), ?_, fun _ => 0, trivial, ?_⟩
  · intro det _
    norm_num [PCAdvantage, s]
  · norm_num [prob, ind, s]

end Qatlib.Papers.BettiHardness26.MainResults.Audit
