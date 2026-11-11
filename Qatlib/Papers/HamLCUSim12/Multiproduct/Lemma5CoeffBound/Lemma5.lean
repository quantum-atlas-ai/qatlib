/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffBoundCertifiedHami
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductEtaRecordHami

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5 (Eq. (20)) — coefficient bound for the multi-product formula

Fixed source: arXiv:1202.5822v1, Lemma 5, p.6, Eq. (20):
if `e^{2 gamma (k+1)} >= 2 k^2`, then for every `1 <= q < k+1`
`|C_q| <= sqrt2 * k^{3/2} * e^{2k(1 + log(eta)/2 - gamma)}`, with `eta` as in Eq. (21).

The paper's derivation (Eqs. (22)-(28)) uses the closed form of `C_q` (our frozen
`multiproductCoeffClosedForm`), the factorial lower bound (Eq. (24), frozen
`FactorialLowerBound`) and the numerical value of `eta` in `(305/1000, 312/1000)`.
All three ingredients are already discharged in the frozen certificate
`MultiproductCoeffBoundCertified`, so the paper-layer statement is a bridge to it.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma5CoeffBound

open Qatlib.Papers.HamLCUSim12.Multiproduct

/-- Fixed arXiv:1202.5822v1, Lemma 5 Eq. (20) together with the eta record Eq. (21):
there is `eta in (305/1000, 312/1000)` such that for every `k >= 1`, `gamma > 0` with
`2 k^2 <= e^{2 gamma (k+1)}` and every `q < k` (paper index `1 <= q < k+1`),
`|C_q| <= sqrt2 * k^{3/2} * exp(2k(1 + log eta / 2 - gamma))`.

The nodes are `ell_q = q+1` (`q < k`) and `ell_{k+1} = exp(gamma(k+1))` as in
Definition 1, Eq. (16).  Reuses frozen
`MultiproductCoeffBoundCertified.multiproductCoeffBoundCertified`. -/
theorem lemma5_coeff_bound :
    ∃ η : ℝ, 305 / 1000 < η ∧ η < 312 / 1000 ∧
      ∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, 0 < γ →
        2 * (k : ℝ) ^ 2 ≤ Real.exp (2 * γ * ((k + 1 : ℕ) : ℝ)) →
        ∀ q : Fin (k + 1), (q : ℕ) < k →
          |mCoeff k (Real.exp (γ * ((k + 1 : ℕ) : ℝ))) q| ≤
            Real.sqrt 2 * (k : ℝ) ^ ((3 : ℝ) / 2) *
              Real.exp (2 * (k : ℝ) * (1 + Real.log η / 2 - γ)) := by
  obtain ⟨η, hlo, hhi, hbound⟩ := multiproductCoeffBoundCertified
  exact ⟨η, hlo, hhi, fun k hk γ hγ hcond q hq => hbound k hk γ hγ hcond q hq⟩

/-- Fixed arXiv:1202.5822v1, Eq. (21): the maximizing ratio
`eta := max_{lambda in [0,1)} lambda^2/((1+lambda)^{1+lambda}(1-lambda)^{1-lambda})`
lies in the interval `(305/1000, 312/1000)` (the paper prints the approximation
`0.3081`).  Reuses frozen `MultiproductEtaRecord.multiproductEtaRecord`. -/
theorem lemma5_eta_record :
    ∃ η : ℝ, 305 / 1000 < η ∧ η < 312 / 1000 ∧ EtaMaxProperty η :=
  multiproductEtaRecord

end Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma5CoeffBound
