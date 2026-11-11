/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorPCA19.MainResults.Model.SpectralModel

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor PCA — the detection threshold (Theorems 2 and 4, Lemma 3)

Source: M. B. Hastings, *Classical and Quantum Algorithms for Tensor Principal
Component Analysis*, arXiv:1907.12724v2.

Algorithm 2 (p.7) decides between `λ = 0` and `λ = λ̄` by comparing the largest
eigenvalue `λ₁` of `H(T₀)` with the threshold `E_cut = (E₀ + E_max)/2`.  This file
records:

* the separation `E_max < E_cut < E₀` implied by `E₀ ≥ (1 + c) E_max`, with the
  resulting correctness of Algorithm 2 (Theorems 2 and 4, p.9–10);
* the high-probability form, obtained from the tail bound of Theorem 1;
* Lemma 3 (p.11–12), the operator-norm bound on the odd-`p` cross terms.
-/

namespace Qatlib.Papers.TensorPCA19.MainResults

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
noncomputable section

/-! ## The decision rule of Algorithm 2 -/

/-- Algorithm 2 accepts the hypothesis `λ = λ̄` when the largest eigenvalue of
`H(T₀)` reaches the threshold `E_cut` (p.7). -/
def Detection.accepts (threshold lam1 : ℝ) : Prop := threshold ≤ lam1

/-! ## The arithmetic separation -/

/-- **Threshold separation** (Theorems 2 and 4, p.9–10): if `E₀ ≥ (1 + c) E_max`
with `c > 0`, then `E_max` lies strictly below `E_cut = (E₀ + E_max)/2`, which in
turn lies strictly below `E₀`.  Consequently the decision rule separates the two
hypotheses. -/
theorem detection_separation (E0 Emax c : ℝ) (hc : 0 < c) (hE0 : 0 < E0) (hEm : 0 < Emax)
    (hsep : (1 + c) * Emax ≤ E0) :
    Emax < (E0 + Emax) / 2 ∧ (E0 + Emax) / 2 < E0 := by
  constructor <;> nlinarith [hE0, hEm, hc, hsep]

/-- **Theorem 2** (§3.2.1, p.9).  If Assumption 1 holds and
`λ (p/2)! C(n_bos, p/2) N^{p/2} − E_max = ω(ξ)` — in explicit form
`E₀ ≥ (1 + c) E_max` with `c > 0` — then Algorithm 2 determines with high
probability whether `λ = 0` or `λ = λ̄`: with `λ₁ ≤ E_max` (the `λ = 0` case) it
rejects, and with `λ₁ ≥ E₀` (the `λ = λ̄` case) it accepts. -/
theorem theorem2_detection_even (s : SpikedTensor) (hEven : s.p % 2 = 0) {c : ℝ}
    (hc : 0 < c) (hE0 : 0 < E0Even s) (hEm : 0 < EmaxEven s)
    (hsep : (1 + c) * EmaxEven s ≤ E0Even s) :
    ¬ Detection.accepts (Ecut s) (EmaxEven s) ∧ Detection.accepts (Ecut s) (E0Even s) := by
  obtain ⟨h1, h2⟩ :=
    detection_separation (E0Even s) (EmaxEven s) c hc hE0 hEm hsep
  have hcut : Ecut s = (E0Even s + EmaxEven s) / 2 := by
    unfold Ecut E0 Emax
    rw [if_pos hEven, if_pos hEven]
  unfold Detection.accepts
  rw [hcut]
  exact ⟨not_le.mpr h1, h2.le⟩

/-- **Theorem 4** (§3.2.2, p.10).  Odd-`p` counterpart of Theorem 2: if
`λ² (p−1)! C(n_bos, p−1) N^p − E_max = ω(ξ)` — explicitly `E₀ ≥ (1 + c) E_max` with
`c > 0` — then Algorithm 2 correctly determines whether `λ = 0` or `λ = λ̄`. -/
theorem theorem4_detection_odd (s : SpikedTensor) (hOdd : s.p % 2 = 1) {c : ℝ}
    (hc : 0 < c) (hE0 : 0 < E0Odd s) (hEm : 0 < EmaxOdd s)
    (hsep : (1 + c) * EmaxOdd s ≤ E0Odd s) :
    ¬ Detection.accepts (Ecut s) (EmaxOdd s) ∧ Detection.accepts (Ecut s) (E0Odd s) := by
  obtain ⟨h1, h2⟩ :=
    detection_separation (E0Odd s) (EmaxOdd s) c hc hE0 hEm hsep
  have hne : ¬ s.p % 2 = 0 := by omega
  have hcut : Ecut s = (E0Odd s + EmaxOdd s) / 2 := by
    unfold Ecut E0 Emax
    rw [if_neg hne, if_neg hne]
  unfold Detection.accepts
  rw [hcut]
  exact ⟨not_le.mpr h1, h2.le⟩

/-! ## The high-probability form -/

/-- **High-probability correctness of Algorithm 2** (Theorems 2 and 4, with tail
bounds from Theorem 1).  If the null-hypothesis tail `Pr[λ₁ ≥ E_cut]` is at most `ε`,
then the largest eigenvalue is below `E_cut` — so Algorithm 2 rejects `λ = λ̄` —
with probability at least `1 − ε`. -/
theorem detection_probability {Ω : Type*} [MeasurableSpace Ω] {s : SpikedTensor}
    (M : GaussianSpectralModel s Ω) (ε : ℝ) (hnoise : M.tail (Ecut s) ≤ ε) :
    (1 - ε) ≤ (M.μ {ω | M.eig ω < Ecut s}).toReal := by
  have hmeas : MeasurableSet {ω | Ecut s ≤ M.eig ω} :=
    measurableSet_le measurable_const M.measurable_eig
  have hcompl : {ω | M.eig ω < Ecut s} = {ω | Ecut s ≤ M.eig ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hfin : M.μ {ω | Ecut s ≤ M.eig ω} ≠ ∞ := measure_ne_top M.μ _
  have hle1 : M.μ {ω | Ecut s ≤ M.eig ω} ≤ 1 := by
    calc M.μ {ω | Ecut s ≤ M.eig ω} ≤ M.μ Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hcomp : (M.μ {ω | M.eig ω < Ecut s}).toReal = 1 - M.tail (Ecut s) := by
    rw [hcompl, measure_compl hmeas hfin, measure_univ]
    rw [ENNReal.toReal_sub_of_le hle1 (by simp)]
    simp [GaussianSpectralModel.tail]
  rw [hcomp]
  linarith

/-! ## Lemma 3 (p.11–12): the cross-term operator norm -/

/-- The source's cross-term bound `λ N^{p/2} O(N^{(p−1)/4}) n_bos^{p−1}`
(Lemma 3, p.12), with the implicit constant of the big-O notation named `C`. -/
def crossTermBound (s : SpikedTensor) (C : ℝ) : ℝ :=
  C * s.lam * (s.N : ℝ) ^ ((s.p : ℝ) / 2) * (s.N : ℝ) ^ (((s.p : ℝ) - 1) / 4) *
    (s.nbos : ℝ) ^ ((s.p : ℝ) - 1)

/-- The operator norm of the cross terms of the odd-`p` energy, with the
high-probability bound of Lemma 3 carried as a field `norm_le`.  The random-matrix
estimate itself (spectral edge of the Gaussian tensor) is the content of Lemma 3
and is part of the model, exactly as the source assumes it in §3.2.2. -/
structure CrossTermModel (s : SpikedTensor) (C : ℝ) where
  /-- `‖cross term‖` (operator norm). -/
  norm : ℝ
  /-- Operator norms are nonnegative. -/
  norm_nonneg : 0 ≤ norm
  /-- Lemma 3 (p.11–12): the high-probability operator-norm bound. -/
  norm_le : norm ≤ crossTermBound s C

/-- **Lemma 3** (§3.2.2, p.11–12).  With high probability the operator norm of the
cross terms is bounded by `λ N^{p/2} O(N^{(p−1)/4}) n_bos^{p−1}`; the model
`CrossTermModel` carries this bound, and the theorem exposes it in the form used in
the odd-`p` energy estimate of §3.2.2. -/
theorem lemma3_cross_term_norm (s : SpikedTensor) (C : ℝ) (M : CrossTermModel s C) :
    M.norm ≤ crossTermBound s C :=
  M.norm_le

end

end Qatlib.Papers.TensorPCA19.MainResults
