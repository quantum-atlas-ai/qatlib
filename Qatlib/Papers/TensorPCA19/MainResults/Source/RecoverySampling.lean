/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorPCA19.MainResults.Model.SpectralModel

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor PCA — sampling and variational claims (Corollary 1, Lemmas 1–2)

Source: M. B. Hastings, *Classical and Quantum Algorithms for Tensor Principal
Component Analysis*, arXiv:1907.12724v2 (= Quantum **4**, 237 (2020)).

This file covers the three claims of §2–§3.2 that concern the *input* side of the
algorithms, before any spectral estimate is used:

* Lemma 2 (p.9): the variational principle `λ₁ ≥ ⟨Ψ_sig|H(T)|Ψ_sig⟩`;
* Lemma 1 (p.5, Eq. (4)): the two sampling guarantees of Algorithm 1 hold
  simultaneously with probability at least `1/2`;
* Corollary 1 (p.5): constant overlap implies strong recovery via the classical
  boosting step (Ref. [1], Prop. 2.6).
-/

namespace Qatlib.Papers.TensorPCA19.MainResults

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-! ## Lemma 2 (p.9): the variational principle -/

/-- **Lemma 2** (§3.2, p.9).  The largest eigenvalue `λ₁` of `H(T₀)` dominates the
energy `E = ⟨Ψ_sig|H(T)|Ψ_sig⟩` of any unit state.  In the spectral decomposition
model of a Hermitian operator on a unit state (`SpectralDecomposition`) the energy
is `Σᵢ wᵢ eᵢ` and the largest eigenvalue is `lamMax`, so the claim is
`energy ≤ lamMax`. -/
theorem lemma2_variational {n : ℕ} (D : SpectralDecomposition n) :
    D.energy ≤ D.lamMax := by
  unfold SpectralDecomposition.energy
  calc ∑ i, D.weight i * D.eig i ≤ ∑ i, D.weight i * D.lamMax := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_left (D.eig_le_lamMax i) (D.weight_nonneg i)
    _ = (∑ i, D.weight i) * D.lamMax := by rw [Finset.sum_mul]
    _ = D.lamMax := by rw [D.weight_sum, one_mul]

/-! ## Lemma 1 (p.5, Eq. (4)): the sampling bound of Algorithm 1 -/

/-- **Union bound behind Lemma 1** (§2, p.5).  If two events each have probability
at least `3/4`, then their intersection has probability at least `1/2`. -/
theorem lemma1_union_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmA : (3 / 4 : ℝ) ≤ (μ A).toReal) (hmB : (3 / 4 : ℝ) ≤ (μ B).toReal) :
    (1 / 2 : ℝ) ≤ (μ (A ∩ B)).toReal := by
  have hsum : (μ (A ∪ B)).toReal + (μ (A ∩ B)).toReal = (μ A).toReal + (μ B).toReal := by
    have h' := congrArg ENNReal.toReal (measure_union_add_inter (μ := μ) A hB)
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
        ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h'
    exact h'
  have hle : (μ (A ∪ B)).toReal ≤ 1 := by
    calc (μ (A ∪ B)).toReal ≤ (μ Set.univ).toReal :=
          ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  linarith

/-- **Lemma 1** (§2, p.5, Eq. (4)).  If the two sampling events of Algorithm 1
(the norm bound and the overlap bound of the random vector `u`) each hold with
probability at least `3/4` and guarantee the overlap bound on their intersection,
then with probability at least `1/2` the output `w` satisfies
`c' √⟨v_sig|ρ|v_sig⟩ ≤ |⟨w|v_sig⟩|` for some scalar `c' > 0`. -/
theorem lemma1_overlap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A B : Set Ω) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmA : (3 / 4 : ℝ) ≤ (μ A).toReal) (hmB : (3 / 4 : ℝ) ≤ (μ B).toReal)
    (overlap : Ω → ℝ) (ρoverlap c' : ℝ) (hc' : 0 < c')
    (hgood : ∀ ω ∈ A ∩ B, c' * Real.sqrt ρoverlap ≤ overlap ω) :
    0 < c' ∧ (1 / 2 : ℝ) ≤ (μ {ω | c' * Real.sqrt ρoverlap ≤ overlap ω}).toReal := by
  have hsub : A ∩ B ⊆ {ω | c' * Real.sqrt ρoverlap ≤ overlap ω} := fun ω hω => hgood ω hω
  exact ⟨hc', le_trans (lemma1_union_bound μ A B hA hB hmA hmB)
    (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))⟩

/-! ## Corollary 1 (p.5): strong recovery from a constant overlap -/

/-- The classical boosting step cited in Corollary 1 (p.5, Ref. [1], Prop. 2.6):
from a weak-recovery guarantee with constant `c > 0` it produces strong recovery
(overlap arbitrarily close to one) with a polynomial number of repetitions. -/
structure BoostingStep where
  /-- Normalized overlap produced by the boosting procedure at weak-recovery constant `c`. -/
  boost : ℝ → ℝ
  /-- The boosted overlap is strongly recovering. -/
  strong : ∀ c : ℝ, 0 < c → StrongRecovery (boost c)

/-- **Corollary 1** (§2, p.5).  Given an algorithm whose output density matrix has
`⟨v_sig|ρ₁|v_sig⟩/N = Ω(1)` (a `WeakRecovery` with a positive constant `c`), the
classical boosting step yields strong recovery.  The polynomial running time is
part of the cited classical result, recorded in `BoostingStep`. -/
theorem corollary1_strong_recovery (B : BoostingStep) {ov c : ℝ}
    (h : WeakRecovery ov c) : StrongRecovery (B.boost c) :=
  B.strong c h.1

end

end Qatlib.Papers.TensorPCA19.MainResults
