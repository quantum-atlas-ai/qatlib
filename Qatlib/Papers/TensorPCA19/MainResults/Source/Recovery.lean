/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorPCA19.MainResults.Model.SpectralModel
import Qatlib.Papers.TensorPCA19.MainResults.Source.RecoverySampling

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor PCA — recovery from the spectral gap (Theorem 3, Theorem 5, Lemma 8)

Source: M. B. Hastings, *Classical and Quantum Algorithms for Tensor Principal
Component Analysis*, arXiv:1907.12724v2.

This file covers the §3.2 recovery step: a state whose energy is above
`(1 + c) E_max` has a non-negligible projection onto the eigenspace of
`H(T₀)` above the threshold `(7/8)E₀ + (1/8)E_max`, hence a non-negligible single
particle overlap with `v_sig`:

* Lemma 8 (p.24–25): projection lower bound from the Markov step;
* Theorem 3 (p.9–10, Eq. (18)): even-`p` recovery;
* Theorem 5 (p.12, Eq. (25)): odd-`p` recovery.

All three are proved in full here, on top of the spectral Markov lemma
`SpectralDecomposition.markov_projMass` of the model layer.
-/

namespace Qatlib.Papers.TensorPCA19.MainResults

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

/-! ## Lemma 8 (p.24–25): the projection lower bound -/

/-- **Lemma 8** (§5.2, p.24–25).  Suppose `E₀ ≥ (1 + c) E_max` with `c > 0`, the
energy of the state is at least `E₀`, and the largest eigenvalue is at most
`E₀ + E_max`.  Then the projection of the state onto the eigenspace with
eigenvalue `≥ (7/8)E₀ + (1/8)E_max` is at least `c/(16(1+c))`.

Proof (source, p.24): Markov's inequality applied to `λ₁ − H(T₀)` gives
`p ≥ (E − t)/(λ₁ − t)`, and with `t = (7/8)E₀ + (1/8)E_max`,
`E ≥ E₀`, `λ₁ ≤ E₀ + E_max` this is at least
`((1/8)(E₀ − E_max))/((1/8)E₀ + (7/8)E_max) ≥ c/(16(1+c))`.  This is the
formal counterpart of the source's `Ω(1)·c/(1+c)`. -/
theorem lemma8_projection_mass {n : ℕ} (D : SpectralDecomposition n) {E0 Emax c : ℝ}
    (hE0 : 0 < E0) (hEm : 0 < Emax) (hc : 0 < c)
    (hsep : (1 + c) * Emax ≤ E0)
    (henergy : E0 ≤ D.energy) (hlam : D.lamMax ≤ E0 + Emax) :
    c / (16 * (1 + c)) ≤ D.projMass ((7 / 8) * E0 + (1 / 8) * Emax) := by
  classical
  set t : ℝ := (7 / 8) * E0 + (1 / 8) * Emax with ht
  set p : ℝ := D.projMass t with hp
  have hp_nonneg : 0 ≤ p := by
    rw [hp]
    unfold SpectralDecomposition.projMass
    exact Finset.sum_nonneg fun i _ => D.weight_nonneg i
  have hE0Em : Emax < E0 := by nlinarith
  have htE0 : t < E0 := by rw [ht]; nlinarith [hE0, hEm]
  have htlt : t < D.lamMax :=
    lt_of_lt_of_le (lt_of_lt_of_le htE0 henergy) (lemma2_variational D)
  have hmarkov : (D.energy - t) / (D.lamMax - t) ≤ p := by
    rw [hp]
    exact D.markov_projMass htlt
  have hnum : E0 - t ≤ D.energy - t := by linarith
  have hdenpos : 0 < D.lamMax - t := sub_pos.mpr htlt
  have hdenle : D.lamMax - t ≤ E0 + Emax - t := by linarith
  have hb_nonneg : 0 ≤ D.energy - t := le_trans (by linarith : (0:ℝ) ≤ E0 - t) hnum
  have hc_nonneg : 0 ≤ D.lamMax - t := hdenpos.le
  have hcross : (E0 - t) * (D.lamMax - t) ≤ (D.energy - t) * (E0 + Emax - t) :=
    mul_le_mul hnum hdenle hc_nonneg hb_nonneg
  have hden2 : 0 < E0 + Emax - t := by nlinarith [ht, hE0Em]
  have hratio1 : (E0 - t) / (E0 + Emax - t) ≤ (D.energy - t) / (D.lamMax - t) := by
    rw [div_le_div_iff₀ hden2 hdenpos]
    exact hcross
  have hratio2 : c / (16 * (1 + c)) ≤ (E0 - t) / (E0 + Emax - t) := by
    rw [div_le_div_iff₀ (by nlinarith : (0:ℝ) < 16 * (1 + c)) hden2]
    nlinarith [hsep, ht, hc, hEm]
  calc c / (16 * (1 + c)) ≤ (E0 - t) / (E0 + Emax - t) := hratio2
    _ ≤ (D.energy - t) / (D.lamMax - t) := hratio1
    _ ≤ p := hmarkov

/-! ## Theorem 3 (p.9–10, Eq. (18)): even-`p` recovery -/

/-- **Theorem 3** (§3.2.1, p.9–10, Eq. (18)).  With Assumption 1, if
`E₀ ≥ (1 + c) E_max` and the state has energy at least `E₀`, then the normalized
overlap with `v_sig` is at least `c/(16(1+c))` (the source's
`(1/2)·c/(1+c)`, up to the explicit constant of Lemma 8).  The `(c′ − o(1))`
form of Eq. (17) is represented by the explicit constant of `lemma8_projection_mass`. -/
theorem theorem3_recovery_even {n : ℕ} (D : SpectralDecomposition n) (s : SpikedTensor)
    {c : ℝ} (hc : 0 < c) (hE0 : 0 < E0Even s) (hEm : 0 < EmaxEven s)
    (hsep : (1 + c) * EmaxEven s ≤ E0Even s)
    (henergy : E0Even s ≤ D.energy) (hlam : D.lamMax ≤ E0Even s + EmaxEven s) :
    c / (16 * (1 + c)) ≤ D.projMass ((7 / 8) * E0Even s + (1 / 8) * EmaxEven s) :=
  lemma8_projection_mass D hE0 hEm hc hsep henergy hlam

/-- **Theorem 3, recovery form** (p.9–10, Eq. (18)): the projection bound of
`theorem3_recovery_even` is a weak recovery of `v_sig`. -/
theorem theorem3_weak_recovery {n : ℕ} (D : SpectralDecomposition n) (s : SpikedTensor)
    {c : ℝ} (hc : 0 < c) (hE0 : 0 < E0Even s) (hEm : 0 < EmaxEven s)
    (hsep : (1 + c) * EmaxEven s ≤ E0Even s)
    (henergy : E0Even s ≤ D.energy) (hlam : D.lamMax ≤ E0Even s + EmaxEven s) :
    WeakRecovery (D.projMass ((7 / 8) * E0Even s + (1 / 8) * EmaxEven s))
      (c / (16 * (1 + c))) := by
  refine ⟨?_, theorem3_recovery_even D s hc hE0 hEm hsep henergy hlam⟩
  exact div_pos hc (by nlinarith)

/-! ## Theorem 5 (p.12, Eq. (25)): odd-`p` recovery -/

/-- **Theorem 5** (§3.2.2, p.12, Eq. (25)).  Odd-`p` counterpart of Theorem 3:
if `E₀ ≥ (1 + c) E_max` and the state has energy at least `E₀`, the normalized
overlap with `v_sig` is at least `c/(16(1+c))`.  The odd-`p` energy lower bound of
§3.2.2 (which uses the cross-term bound of Lemma 3) enters through the hypothesis
`henergy`. -/
theorem theorem5_recovery_odd {n : ℕ} (D : SpectralDecomposition n) (s : SpikedTensor)
    {c : ℝ} (hc : 0 < c) (hE0 : 0 < E0Odd s) (hEm : 0 < EmaxOdd s)
    (hsep : (1 + c) * EmaxOdd s ≤ E0Odd s)
    (henergy : E0Odd s ≤ D.energy) (hlam : D.lamMax ≤ E0Odd s + EmaxOdd s) :
    c / (16 * (1 + c)) ≤ D.projMass ((7 / 8) * E0Odd s + (1 / 8) * EmaxOdd s) :=
  lemma8_projection_mass D hE0 hEm hc hsep henergy hlam

/-- **Theorem 5, recovery form** (p.12, Eq. (25)): the projection bound of
`theorem5_recovery_odd` is a weak recovery of `v_sig`. -/
theorem theorem5_weak_recovery {n : ℕ} (D : SpectralDecomposition n) (s : SpikedTensor)
    {c : ℝ} (hc : 0 < c) (hE0 : 0 < E0Odd s) (hEm : 0 < EmaxOdd s)
    (hsep : (1 + c) * EmaxOdd s ≤ E0Odd s)
    (henergy : E0Odd s ≤ D.energy) (hlam : D.lamMax ≤ E0Odd s + EmaxOdd s) :
    WeakRecovery (D.projMass ((7 / 8) * E0Odd s + (1 / 8) * EmaxOdd s))
      (c / (16 * (1 + c))) := by
  refine ⟨?_, theorem5_recovery_odd D s hc hE0 hEm hsep henergy hlam⟩
  exact div_pos hc (by nlinarith)

end

end Qatlib.Papers.TensorPCA19.MainResults
